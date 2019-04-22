/*********************************
 *
 *                                   Juntong Liu
 *                                           
 *                                                juntong.liu@embiron.com   
 *
 *                                                                        2006.02.08
 *
 * 
 * Copyright (C), 2006, Embiron AB.
 * This software is designed and developed by Embiron AB for the EU's SNOCER project. The  
 * SNOCER project's final copyright rule will apply to this software. Under the SNOCER 
 * software's copyright(GPL), one can change and use this software, but MUST include this
 * beginning information in the resulting software. One can obtain a copy of GPL from the 
 * following link:
 *  
 *           http://www.gnu.org/copyleft/gpl.html
 *
 * 
 * THIS PROGRAM IS DEVELOPED AS IT IS. TO USE IT IS AT YOUR OWN RISK. 
 *   
 * Code used in our test system to take care the IPtables and to block all suspected IP addresses. 
 *
 * This program is partially tested under Redhat linux 9, GCC-3.2.2. 
 *
 * This code segment is used in a test system to perform IP tables(Linux IP firewall) handling, 
 * at the same time keep track of IP addresses that have been blocked.
 *
 *  To speed up the process, a ring list and corresponding algorithms have been designed and 
 * implemented to improve the performance of the list maintain process, and:
 *
 *      1.) to keep track of all the suspected IP addresses, 
 *      2.) to make sure that the same IP address can only appear on an IPtables once,
 *      3.) to make sure that an IP address will not be blocked for ever, 
 *      4.) to make sure that the IP table will not grow wildly which might
 *          leading to degrade the whole system's performance.
 *      5.) log the intruders IP address. 
 *
 *
 * Note, this code can be used only in a Linux system where the IPtables have been compiled 
 * into the kernel. 
 *
 * Pre-conditions:
 *         1.) IPtables in kernel
 *         2.) no other program dealing with the IP tables on the same box
 *         3.) if this will be complied as a separated file, it needs the snort-xxx/src/decode.h
 *             head file.
 *
 *
 * I embedded this code into a sensor's source file to fit our situation. But, it should be easy to 
 * convert the code into a client-server style IP tables management agent.
 * Note that this program can also be used as a general purpose "safe list" in some environment, 
 * or as a base for information cache software. 
 *
 *
 *  Revision History:
 *
 *  1.1   2006.02.08, first implementation. 2006.05.08 put into CVS.
 *  1.2   2006.05.10, add some comments to make it more readable.
 *  1.3   2006.05.12, re-code the is_visitor_on_list() function.
 *  1.4   2006.05.12, fixed a small error.
 *  1.5   2006.05.16, added more comments.
 *  1.6   2006.05.23, a few small changes.
 *  1.7   2006.06.02, add more comments, some small changes. 
 *  1.8   2006.06.05, add a few lines to clean the IPtable when finished, add more comments.
 *
 *
 *
 ***********************************************************************************************/


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>
#include <sys/time.h>
#include <time.h>

#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>

#include "decode.h"


#define MAX_LIST_LEN   512            /* max list length, research shows that ipt performance drop sharply when entries > 500  */
#define TIME_ON_LIST   1800 /*7200*/  /* seconds, block an intruder/attacker's IP address half hour 
					 seems enough to frustrate the bad guy   */
#define ONLY_WE_TAKE_CARE_IPTABLES 1
char *our_net_str = "213.212.52.";    /* give our own sub-net the green light */
char *our_logfile="/home/juntong/packets-captured/snort_alert";
int ipt_cmd_flag = 0; 


/* IP table operation parameters */
struct ipt_opera{
  char *ctl_if;
  char *ipt_cmd_a;
  char *ipt_cmd;
  char *ipt_tbl;
  char *ipt_poli;
} ipt_o 
= 
{
  "eth0", 
  "/sbin/iptables", 
  "iptables", 
  "INPUT",
  "REJECT"      /* REJECT will make some "noise" to the net, one can use DROP if you do not like it */ 
};


/* define a list element */
struct w_visitor{
  char client_ip[15];                /* suspected IP address in string format */
  unsigned long ipaddr;              /* IP address in binary for fast compare  */
  long btime;                        /* time when this IP address got blocked, seconds */
  struct w_visitor  *next; 
  struct w_visitor  *prev;
};


/* define a list */
struct visitor_list{
  struct w_visitor *head;
  struct w_visitor *tail;
  struct w_visitor *current; 
  int num_elements;
};


/* declare the list header */
struct visitor_list our_visitor_list = { NULL, NULL, NULL, 0 };


/* function prototypes */
void does_ipt_cmd_exist(Packet *p, char *msg);               /* the interface function to this subsystem */
int free_visitor_list(void);                                 /* the clean up function, called when snort exit to release allocated memory  */
static void block_suspected_source_ip(Packet *p, char *msg);
static int is_visitor_on_list(struct in_addr *inaddr);
static int add_visitor_to_list(struct in_addr *in_addr, char *ip_str);
static int check_list_element_time(void);
static int delete_input_rule(int pos);
static void my_record_alert(char *ipaddr, char *msg);


/* 
 * Check to see if the IP is already blocked, using our "youngest first cache look up 
 * algorithm" in this function to improve performance.
 */
static int is_visitor_on_list(struct in_addr *inaddr)
{
  struct w_visitor *wp;
  struct in_addr this_inaddr;
  
  if(!our_visitor_list.head)
    return 0;                       /* empty list */
  
  this_inaddr.s_addr = inaddr->s_addr;

  /*
   * With the input IP table being setup to block an IP address, the same IP address should not be able
   * to pass the IP table(firewall) to reach the application layer anymore. But, for some intrusion 
   * detection software, they may get packets directly from link layer. Since this codes is designed to
   * embedded into an intrusion detection software, that means that the already blocked IP address may
   * still can reach this codes.
   * 
   * Most likely, an intruder/attacker will launch multiple attempts, this give us a chance
   * to design an algorithm to speed up the comparison after an IP address has been put 
   * onto our list.
   * 
   * Note that no matter where we start to compare, for each new IP address, we have to walk 
   * the whole list to make sure that this is a new IP address, and then put it onto the list. 
   * But, most likely, an intruder/attacker will launch multiple attempts. This means that 
   * we have to process the same IP address multiple times, even a lot of times. 
   * So, always start to compare from the youngest element on the list will save time if the 
   * IP address has already been recorded on the list.   
   * If there is only one intruder at a time, with this algorithm, no matter how long the list 
   * is, most likely we will get a hit after check only one element of the list. And do not need 
   * to walk the whole  list. 
   * If there are N intruders/attackers, then, with this algorithm, we should be able to get 
   * a hit after compare X elements of the list, where X <= N. In other word, when N intruders
   * /attackers launch attack at the same time, with this algorithm, in the wast case, we still
   * should be able to get a hit after check N elements of the list. 
   * 
   * So, for this implementation:
   * If the current!=NULL, the element before the element pointed by the current is the youngest
   * on the list. 
   * If the current=NULL, the element pointed by the tail is the youngest one.
   */ 

  if(our_visitor_list.current)
    {
      wp = our_visitor_list.current->prev;
      
      /* take care the head */
      if(!wp)                                      /* current point to the head */
	wp = our_visitor_list.tail;

      while(wp != our_visitor_list.current)
	{
	  if(wp->ipaddr == this_inaddr.s_addr)
	    return 1;                              /* return 1 - visitor already on list */

	  if((wp = wp->prev))                      /* check to see if reached head */
	    continue;
	  else
	    wp = our_visitor_list.tail;

	}; /* end of while() */

      /* take care the one left */
      if(our_visitor_list.current->ipaddr == this_inaddr.s_addr)
	return 1;
      
      return 0;
    }
  else
    {     
      /* start from tail */

      wp = our_visitor_list.tail;
      /* just walk the list */
      while(wp != our_visitor_list.head)
	{
	  if(wp->ipaddr == this_inaddr.s_addr)
	    return 1;                            /* return 1 - visitor already on list */
	  
	  wp = wp->prev;
	}; 

      if(our_visitor_list.head->ipaddr == this_inaddr.s_addr)
	return 1;

      return 0;                                 /* return 0 - visitor's IP is new */

    };

  return 0;                                     /* should not reach here */
};



/* 
 * Make sure that if we can not work, we wast other's time as less as possible
 * because that we are embedded into other people's program. 
 * Note, the only reason that we use the Packet structure as a argument for this
 * function and the block_suspected_source_ip() function is that, in our case, we 
 * get the suspected IP address from it. If the suspected IP address can be obtained 
 * directly, instead of using the Packet *p as a parameter, one can directly put the 
 * IP-address as one of these function's argument.   
 */  
void does_ipt_cmd_exist(Packet *p, char *msg)
{
  int ret;

  if(!ipt_cmd_flag)
    {
      /* should never reach here more than once */

      ret = access(ipt_o.ipt_cmd_a, R_OK | X_OK);
      if(!ret)
	{
	  ipt_cmd_flag = 1;
	   block_suspected_source_ip(p, msg);
	   return;
	}
      else
	{
	  ipt_cmd_flag = -1;
	  return; 
	};
    }
  else if (ipt_cmd_flag == 1)
    {
      block_suspected_source_ip(p, msg);
    };
  
  return;

}

 
/* 
 * Add a suspected IP onto the list so that we can keep track of it. See SNOCER
 * project Deliverable_3.2, sub-section 2.1.3.1.2 for detail description of this function.
 * Here is a summary:
 * If the list has never reached its maximum length, new element will be appended to the tail.
 * If the list had reached its maximum length, but now, under its maximum length because that
 * those aged elements have been removed from the list, new element will be inserted before 
 * the oldest element.  
 * When the list reaches its maximum length, the list will become a "ring" and will not grow
 * any more, new element will overwrite the oldest element. So, the IP table will not grow
 * wildly and degrade the whole system.
 */  
static int add_visitor_to_list(struct in_addr *in_addr, char *ip_str)
{

  struct w_visitor *tmp;
  
  struct timeval this_tv;

  gettimeofday(&this_tv, NULL);

  /* check to see if we should add a new element  */
  if(our_visitor_list.num_elements < MAX_LIST_LEN)
    {
      /* list is not at its maximum size, we can add a new element */
      
      tmp = malloc(sizeof(struct w_visitor));
      if(!tmp)
	return -1;                                  /* just return, not to disturb snort */
      
      memset(tmp, 0, sizeof(struct w_visitor));
      strncpy(tmp->client_ip, ip_str, strlen(ip_str));
      tmp->ipaddr    = in_addr->s_addr;
      tmp->btime     = this_tv.tv_sec;              /* blocked time */ 

      /* check to see if the list have ever reached its maximum size */
      if(!our_visitor_list.current)
	{  
	  /* list never reached its maximum size yet, we append it */

	  /* check to see if the list is empty */
	  if(!our_visitor_list.head)
	    {  
	      /* we are the first one */	      
	      our_visitor_list.head = tmp;          
	      tmp->next = NULL;
	      tmp->prev = NULL;
	      our_visitor_list.tail = tmp;          
	      our_visitor_list.num_elements++;
	    }
	  else
	    {  
	     /* already have element on queue */
	      tmp->prev = our_visitor_list.tail;
	      our_visitor_list.tail->next = tmp;
	      our_visitor_list.tail = tmp;         
	      our_visitor_list.tail->next = NULL;
	      our_visitor_list.num_elements++;
	    }
	}
      else 
	{  
	  /* list reached its maximum length before, but now under its maximum length */
	  
	  /* check to see if the current point to the head */
	  if(our_visitor_list.current == our_visitor_list.head)
	    {  
	      /* the current point to the head, we need to "pre-apend" the element */
	      our_visitor_list.head->prev = tmp;
	      tmp->next = our_visitor_list.head;
	      tmp->prev = NULL;
	      our_visitor_list.head = tmp;
	      our_visitor_list.num_elements++;
	    }
	  else
	    {
	      /* current not point to the head, we just insert it into the list */
	      our_visitor_list.current->prev->next = tmp;
	      tmp->prev = our_visitor_list.current->prev;
	      tmp->next = our_visitor_list.current;
	      our_visitor_list.current->prev = tmp;
	      our_visitor_list.num_elements++;
	    }
	}
    }
  else
    {     
      /* now, the list is a "ring" */

      if(our_visitor_list.current)
	{   
	  /* check to see if need rewind */
	  if(our_visitor_list.current == our_visitor_list.tail)        
	    { 
	      strncpy(our_visitor_list.current->client_ip, ip_str, strlen(ip_str));
	      our_visitor_list.current->ipaddr = in_addr->s_addr;
	      our_visitor_list.current->btime  = this_tv.tv_sec; 
	      our_visitor_list.current = our_visitor_list.head;      

	      /* we need to take care the IP table when we overwrite an old element */
#ifdef ONLY_WE_TAKE_CARE_IPTABLES
	      delete_input_rule(MAX_LIST_LEN+1);
#endif 
	    
	    }
	  else
	    {    
	      strncpy(our_visitor_list.current->client_ip, ip_str, strlen(ip_str));
	      our_visitor_list.current->ipaddr = in_addr->s_addr;
	      our_visitor_list.current->btime  = this_tv.tv_sec; 
	      our_visitor_list.current = our_visitor_list.current->next;  
	     
	      
#ifdef ONLY_WE_TAKE_CARE_IPTABLES
	      delete_input_rule(MAX_LIST_LEN+1);  
#endif 
	   
	    }
	}
      else if(!our_visitor_list.current)
	{  
	  our_visitor_list.current = our_visitor_list.head;
	  strncpy(our_visitor_list.current->client_ip, ip_str, strlen(ip_str));
	  our_visitor_list.current->ipaddr = in_addr->s_addr;
	  our_visitor_list.current->btime  = this_tv.tv_sec; 
	
	  our_visitor_list.current = our_visitor_list.current->next;  

#ifdef ONLY_WE_TAKE_CARE_IPTABLES
	      delete_input_rule(MAX_LIST_LEN+1);                 
#endif 

	}
    };

  return 0;

}


/* 
 * Remove those elements which have been on the list longer than
 * MAX_TIME_ON_LIST seconds.
 */
static int check_list_element_time(void)
{
  struct w_visitor *tmp, *tmp2;
  struct timeval this_tv;

  if(!our_visitor_list.head)
    return 0;

  gettimeofday(&this_tv, NULL);

  /* 
   * check should be started from the oldest element on the list to save time.
   * If the current!=NULL, means that the list reached its maximum length once,
   * we do not care if the list is at its maximum length or not now, but we know that
   * now the "current" always point at the oldest element.
   * If the current=NULL, means that the list never reached its maximum length,
   * the "head" points to the oldest element on the list.
   */
  if(our_visitor_list.current)            
    {
      /* current always point at the oldest element */

      tmp = our_visitor_list.current; 
      while(tmp)
	{
	  /* neglect the micro seconds, just use the seconds */
	  if((this_tv.tv_sec - tmp->btime) <  TIME_ON_LIST)       
	    {
	      return 0;                                           /* the oldest one still have time */
	    }
	  else
	    { 
	      /* we need to rewind when we reach tail */
	      if(tmp != our_visitor_list.tail)            
		{
		  tmp->prev->next = tmp->next;            
		  tmp->next->prev = tmp->prev;
		  our_visitor_list.current = tmp->next;
		  tmp2 = tmp;
		  tmp = tmp->next;                       

#ifdef ONLY_WE_TAKE_CARE_IPTABLES
		  
		  delete_input_rule(our_visitor_list.num_elements);     
#endif
		
		  free(tmp2);
		  our_visitor_list.num_elements--;
		}
	      else
		{ 
		  /* reached tail  */
		  tmp->prev->next = NULL;
		  our_visitor_list.tail = tmp->prev;
		  our_visitor_list.current = our_visitor_list.head;
		  tmp2 = tmp;
		  tmp = our_visitor_list.head;
		  free(tmp2);

#ifdef ONLY_WE_TAKE_CARE_IPTABLES
		  /* delete the corresponding input rule */
		  delete_input_rule(our_visitor_list.num_elements);     
#endif

		  our_visitor_list.num_elements--;
		  
		}
	    }
	} /* end of while() */
    }
  else 
    {  
      /* head point to the oldest element on the list */
      tmp = our_visitor_list.head;
      while(tmp)
	{
	  if((this_tv.tv_sec - tmp->btime) <  TIME_ON_LIST)
	    {
	      return 0;                        /* the oldest one still have time */
	    }
	  else
	    {              
	      /* need to delete this one and corresponding rule */		  
	      our_visitor_list.head = tmp->next;
	      tmp->next->prev = NULL;
	      tmp2 = tmp;
	      tmp = tmp->next;
	      free(tmp2);
	      
#ifdef ONLY_WE_TAKE_CARE_IPTABLES
	      /* delete the corresponding input rule */
	      delete_input_rule(our_visitor_list.num_elements);     
#endif		      
	      our_visitor_list.num_elements--;
	    }
	  
	} /* end of while() */
    }

  return 0;

}


/* 
 * This can do the job. We use it before we find a fast way to access IP table.
 * The only use of the Packet data structure here is that we get the intruder/
 * attacker's IP address from it.
 * 
 */
static void block_suspected_source_ip(Packet *p, char *msg)
{
  //unsigned long int src_ip;
  char *ipaddr;
  int statu, pid, execret;
  //char ip_str[15];
  struct in_addr i_addr;
  int if_blocked;
  
  /* check to see if the source ip address is in the packet */
  if(!p->iph->ip_src.s_addr)
    return;

  /* prepare to convert it into string-dot format */
  i_addr.s_addr = p->iph->ip_src.s_addr;

  /* convert IP address into string format */
  ipaddr = inet_ntoa(i_addr);

  /* is this from our own subnetwork? */
  if(!strncmp(our_net_str, ipaddr, 11))
    goto skip_it;
    
  /* first, we check to see if the ip is already blocked */
  if_blocked = is_visitor_on_list(&i_addr);

  if(!if_blocked)
    {
      if((pid = fork()) < 0) 
	return;                            /* just return, do not disturb the program we hooked to */
      
      if(!pid)                             /* child */
	{     
	  execret = execl(ipt_o.ipt_cmd_a, ipt_o.ipt_cmd, "-I", 
			  ipt_o.ipt_tbl, "-i", ipt_o.ctl_if, 
			  "-s", ipaddr, "-j", ipt_o.ipt_poli, NULL);
	  exit(0);    
	}
      else
	{
	  wait(&statu);
	};


      add_visitor_to_list(&i_addr, ipaddr); 

      /* so, if do not add new element to list, do not check for time-out-element */
      check_list_element_time();      
    
      my_record_alert(ipaddr, msg);       /* record the blocked IP address into log file */
      
    };
  
 skip_it:

  return;

};


/* 
 * Delete a rule from the INPUT IP table. We use this before we find a
 * faster way to access the kernel's IP table.
 */
static int delete_input_rule(int pos)
{

  int pid, statu, execret;
  char spos[8];

  if((pos < 1) || (pos > MAX_LIST_LEN+1))
    return -1;

  sprintf(spos, "%d", pos);

  if((pid = fork()) < 0) 
    return -1;
  
  if(!pid)   
    {     
      execret = execl(ipt_o.ipt_cmd_a, ipt_o.ipt_cmd, 
		      "-D", ipt_o.ipt_tbl, spos, NULL);
      exit(0);    
    }
  else
    {
      wait(&statu);
    };	  
  
  return 0;
}


/* 
 * Release the memory we used. Called by a clean up function.
 */
int free_visitor_list(void)
{

  int i;
  struct w_visitor *tmp1;

  printf("\nSimple IP table handler existing! Free allocated memory blocks.......\n\n");
  
  if(!our_visitor_list.head)
    return 0;                                                   /* nothing on list */

  for(i=0; i<our_visitor_list.num_elements; i++)                /* clean the IP table */
    {
      /* the index start from 1 */
      delete_input_rule(1);
    };

  tmp1 = our_visitor_list.head->next;

  while(our_visitor_list.head)
    {
      free(our_visitor_list.head);
      our_visitor_list.head = tmp1;
      if(tmp1)
	tmp1 = tmp1->next;
    };

  
  return 0;
}
  

/* 
 * Write the alert into our log file 
 */
static void my_record_alert(char *ipaddr, char *msg)
{

   char loginfo[2048];
   FILE *fp;
   time_t when;
   char *time_str;

   if(!ipaddr)
     return;

   fp = fopen(our_logfile, "a+");
   
   if(!fp) 
     return;                       /* just return, do not disturb other */        

   /* time when caught this IP address */
   when = time(NULL);

   time_str = ctime(&when);

   sprintf(loginfo, "Alert =>: %s%s%s%s%s", msg, " from ", ipaddr, " on ", time_str);

   fwrite(loginfo, strlen(loginfo), 1,  fp);   
 
   fclose(fp);
   
   return;

};                              
