/*********************************************
 * OPL  Model
 * Author: yilmazu
 * Creation Date: Jul 3, 2020 at 5:30:00 PM
 *********************************************/
 tuple emp {
  key string name;
  int qualification;
}

tuple shift {
   key int day;
   string dayname;
   key string time;
   int minRequirement;   
}

tuple couple {
  emp emp1;
  emp emp2;
}

int day = 28;

range days = 1..day;


{emp} Emps = ...;
{shift} Shifts = ...;
{couple} Forbidden with emp1 in Emps, emp2 in Emps = ... ;


dvar int Assignment[Emps][Shifts] in 0..1 ;
dvar int Viol_Pattern[Emps][Shifts]  in 0..1 ;
dvar int Viol_Minus[Shifts] in 0..1 ;
dexpr float Viol_Pattern_Emp[e in Emps] = sum(s in Shifts) Viol_Pattern[e][s] ;
dexpr int EmpNumPerShift[s in Shifts] = sum(e in Emps) Assignment[e][s] ;
dexpr int OverAssignment[s in Shifts] = maxl(EmpNumPerShift[s] - s.minRequirement, 0) ;
dvar int UnderAssignment[Shifts] in 0..1 ;

minimize
  sum(s in Shifts) 
  (
   OverAssignment[s]^2 +
   Viol_Minus[s]^2 + 300*UnderAssignment[s]) +
  sum(e in Emps)
    2*Viol_Pattern_Emp[e]^2
   
   ;

subject to {
	
 	
  //Successive days
  forall(e in Emps, s1, s2, s3, s4 in Shifts, d in days :
   ((d == s1.day && d == s2.day && d+1 == s3.day &&
  d+1 == s4.day) ||  (28 == s1.day && 28 == s2.day && 1 == s3.day &&
  1 == s4.day)) && s1.time != s2.time && s3.time != s4.time ) 
 Assignment[e][s1] + Assignment[e][s2] + Assignment[e][s3] 
 + Assignment[e][s4] == 1 ;    
 
  //A-B-A
  forall(e in Emps, s1, s2 in Shifts, d in days :
   ((d == s1.day && d + 2  == s2.day) || (s1.day == 28 && s2.day == 2)
    || (s1.day == 27 && s2.day == 1)) && s1.time == s2.time) 
   Assignment[e][s1] + Assignment[e][s2] <= 1 + Viol_Pattern[e][s1] ;
  

  //Requirement
  forall(s in Shifts)
   sum(e in Emps) Assignment[e][s] >= s.minRequirement - UnderAssignment[s] ;
   
  //minusplus
  forall(s in Shifts)
  sum(e in Emps) Assignment[e][s] * e.qualification  >= 0 - Viol_Minus[s];
  
  //forbidden
   forall( < e1 , e2 > in Forbidden , s in Shifts )
      Assignment[e1][s] + Assignment[e2][s] <= 1   ;
      
      
}
