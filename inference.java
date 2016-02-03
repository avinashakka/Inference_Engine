import java.util.*;
import java.io.*;

/*
 * The backward chaining algorithm has been implemented exactly the same it has been mentioned 
 * in the 2nd edition of AIMA(Page.No: 275, Section :9.4). 
 * The main calls the back_chain function with the query which is then 
 * checked for entailment and a list of substitutions is returned based on which the inference is made.
 * 
 * The algorithm solves the problem of passing the substitutions using recursion and passing around a theta object
 * which has a flag for success or failure and the resulting map of values for the variables used in the 
 * entailment proof.
 * 
 * It handles negation implicitly but only the visited predicates with same parameters have to be tracked to 
 * prevent loops, which is done by keeping a queue called Visited and adding the predicates to it every time a
 * call is made to prove a particular predicate.
 */

public class inference 
{

	public static class ThetaO
	{
		boolean success;
		HashMap<String, String> values;
		
		public ThetaO()
		{
			this.values = new HashMap<String, String>();
			this.success = true;
		}
		
		public void setflag(boolean x)
		{
			this.success = x;
		}
		
		public void clearValues()
		{
			this.values = new HashMap <String,String>();
		}
	}
	
	
	public static HashMap<String, ArrayList<ArrayList<String>>> KB;
	public static ArrayList<String> Visited;
	
	public static void addFact(String clause)
	{
		String[] parts = clause.split("\\(");
		String key = parts[0];
		String valArgs = parts[1].replace(")","");
		
		if(KB.containsKey(key))
		{
			ArrayList<String> list = new ArrayList<String>();
			list.add(valArgs);
			list.add("TRUE");
			KB.get(key).add(list);
		}
		else
		{
			ArrayList<ArrayList<String>> valueList = new ArrayList<ArrayList<String>>();
			ArrayList<String> list = new ArrayList<String>();
			list.add(valArgs);
			list.add("TRUE"); 
			valueList.add(list);
			KB.put(key, valueList);								
		}
		
	}
	
	public static void addClause(String clause)
	{
		
				String[] parts = clause.split("=>");
				String antecedent = parts[0];
				String consequent = parts[1];
				
				String[] part = consequent.split("\\(");
				String key = part[0];
				String value = part[1].replace(")","");
		
				if(KB.containsKey(key))
			{
				ArrayList<String> list = new ArrayList<String>();
				list.add(value);
				list.add(antecedent); 
				KB.get(key).add(list);
			}
			else
			{
				ArrayList<ArrayList<String>> valueList = new ArrayList<ArrayList<String>>();
				ArrayList<String> list = new ArrayList<String>();
				list.add(value);
				list.add(antecedent);
				valueList.add(list);
				KB.put(key, valueList);
			}
		
	}

	public static ArrayList<String> standardize_parameters(ArrayList<String> sentence)
	{
			if(sentence.get(1).equals("TRUE"))
			{
				return sentence;
			}
			
			ArrayList<String> std_rule = new ArrayList<String>();
			HashMap<String,String> std_map = new HashMap<String,String>();
			ArrayList<String> predicates = new ArrayList<String>(); 
			
			String[] curargs = sentence.get(0).split(",");
			for(String argument : curargs)
			{
				if((!std_map.containsKey(argument)) && (Character.isLowerCase(argument.charAt(0))) )
				{
					std_map.put(argument, argument+index);
					index += 1;
				}
			}
			String[] conjList = sentence.get(1).split("\\^");
			for(String currC : conjList)
			{
				String[] splitClause = currC.split("\\(");
				String curr = splitClause[0];
				String[] currArgsList = splitClause[1].replace(")", "").split(",");
					for(String argument : currArgsList)
					{
						if((!std_map.containsKey(argument)) && (Character.isLowerCase(argument.charAt(0))) )
						{
							std_map.put(argument, argument+index);
							index += 1;
						}
					}
					StringBuilder std_predicate = new StringBuilder(curr);
						std_predicate.append("(");
							for(String argument : currArgsList)
							{
								if(Character.isLowerCase(argument.charAt(0)))
								{
									std_predicate.append(std_map.get(argument));
									std_predicate.append(",");
								}
								else
								{
									std_predicate.append(argument);
									std_predicate.append(",");									
								}
							}
						std_predicate.deleteCharAt(std_predicate.lastIndexOf(","));
						std_predicate.append(")");
						
				 predicates.add(std_predicate.toString());
			}
	
			StringBuilder std_args = new StringBuilder();
				for(String argument : curargs)
				{
					if(Character.isLowerCase(argument.charAt(0)))
					{
						std_args.append(std_map.get(argument));
						std_args.append(",");
					}
					else
					{
						std_args.append(argument);
						std_args.append(",");						
					}
				}
			std_args.deleteCharAt(std_args.lastIndexOf(","));
			
			
			StringBuilder std_clause = new StringBuilder();
				for(String stdPredicate : predicates)
				{
					std_clause.append(stdPredicate);
					std_clause.append("^");
				}
			std_clause.deleteCharAt(std_clause.lastIndexOf("^"));
			std_rule.add(std_args.toString());
			std_rule.add(std_clause.toString());
		
		
		return std_rule;
	}
	
	public static ThetaO compose(ThetaO theta, ThetaO thetaI)
	{
		ThetaO comtheta = new ThetaO();
		comtheta.setflag(true);
	
		for(String variable : theta.values.keySet())
			{
				if(thetaI.values.containsKey(variable))
				{
					comtheta.values.put(variable, thetaI.values.get(variable));
				}
				else
				{
					comtheta.values.put(variable, theta.values.get(variable));
				}
			}
			for(String variable : thetaI.values.keySet())
			{
				if(!theta.values.containsKey(variable))
				{
						comtheta.values.put(variable, thetaI.values.get(variable));
				}
			}
				
		return comtheta;
		
	}
	
	public static int index = 0; 
	
	public static ThetaO unify(String query, String queryI)
	{
		
		String[] cArgs = query.split(",");
		String[] vArgs = queryI.split(",");
		ThetaO unifiermap = new ThetaO();
	    for(int i=0;i<(vArgs.length);i++)
	    {
	    	String item = vArgs[i];
	        if (Character.isLowerCase(item.charAt(0)) && Character.isLowerCase(cArgs[i].charAt(0)))
	        {
		        	
		        	unifiermap.setflag(true);
		        	if(!unifiermap.values.containsKey(item))
		        	{
		        		if(!unifiermap.values.containsKey(cArgs[i]))
		        		{
			        			unifiermap.values.put(item, cArgs[i]);
		        		}
		        		else
		        		{
		        			unifiermap.values.put(item,(unifiermap.values.get(cArgs[i])));
		        		}
		        	}	
		        	else
		        	{
		        			if(unifiermap.values.get(item).equals(cArgs[i]))
		        			{
		        				unifiermap.setflag(true);
		        				continue;
		        			}
		        			else
		        			{
		        				unifiermap.setflag(false);
		        				return unifiermap;
		        				
		        			}
		        	}
	        }
	        	        
	        else if (Character.isUpperCase(item.charAt(0)) && Character.isLowerCase(cArgs[i].charAt(0)))
	        {
	        	unifiermap.setflag(true);	        	
	        	if(!unifiermap.values.containsKey(cArgs[i]))
	        	{	
	        			unifiermap.values.put(cArgs[i], item);
	        	}
	        	else
	        	{
		        		if(unifiermap.values.get(cArgs[i]).equals(item))
	        			{
		        			unifiermap.setflag(true);
		        			continue;
	        			}
	        			else
	        			{
	        				unifiermap.setflag(false);
	        				return unifiermap;	        				
	        			}
	        	}
	        }
	        
	        else if (Character.isLowerCase(item.charAt(0)) && Character.isUpperCase(cArgs[i].charAt(0)))
	        {
	        	unifiermap.setflag(true);
	        	
	        	if(!unifiermap.values.containsKey(item))
	        	{
	        			unifiermap.values.put(item, cArgs[i]);
	        	}
	        	else
	        	{
		        		if(unifiermap.values.get(item).equals(cArgs[i]))
	        			{
		        			unifiermap.setflag(true);
		        			continue;
	        			}
	        			else
	        			{
	        				unifiermap.setflag(false);
	        				return unifiermap;	        				
	        			}
	        	}
	        }
	        else if (item.equals(cArgs[i]))
	        {
	        	unifiermap.setflag(true);	
	        	continue;
	        }
	        else 
	        {
	        	unifiermap.setflag(false);
		        	return unifiermap;
	        }
	        
	    }
	    return unifiermap;
		
	}
	
	public static boolean argsCheck(String query)
	{
		String[] parts = query.split(",");
		
		for(String var : parts)
		{
			if(Character.isLowerCase(var.charAt(0)))
			{
				return false;
			}
		}
		
		return true;
		
	}
	
	public static boolean CompareMaps(HashMap<String,String> newMap,HashMap<String,String> oldMap)
	{
		if(newMap.keySet().size() != oldMap.keySet().size())
		{
			return false;
		}
		
		for(String newkey : newMap.keySet())
		{
			if(!oldMap.containsKey(newkey))
			{
				return false;
			}
			if(!oldMap.get(newkey).equals(newMap.get(newkey)))
			{
				return false;
			}			
			
		}
		
		return true;		
		
	}
 

	
	public static String substitute(String thetaI, HashMap<String, String> subs)
	{
		//System.out.println("Inside substitute: "+thetaI+" values: "+subs);		
		for(String var : subs.keySet())
		{
			if(thetaI.contains(var))
			{
				thetaI = thetaI.replace(var,subs.get(var));
			}			
		}			
		return thetaI;
	}
	
	public static ArrayList<ThetaO> back_chain_list(LinkedList<String> qlist, ThetaO theta)
	{
			ArrayList<ThetaO> answers = new ArrayList<ThetaO>();
			if(qlist.isEmpty())
			{
				 ArrayList<ThetaO> sendlist = new ArrayList<ThetaO>();
				 sendlist.add(theta);
				 return sendlist;
			}
				
				String q = qlist.pollFirst();
				String[] parts = q.split("\\(");
				
				//System.out.println("Query being processed: "+q);
				String predicate = parts[0];
				//System.out.println("predicate: "+splitQuery[0]+" args: "+splitQuery[1]);
				String args = parts[1].replace(")","");
				
				String subsqstring = substitute(args, theta.values);
				
				String newquery = predicate+"("+subsqstring+")";
				if(argsCheck(subsqstring) == true)
				{
					if(!Visited.contains(newquery))
					{
						Visited.add(newquery);
					}
					else
					{
						return answers;
					}
				}
				
									
				if(KB.containsKey(predicate))
				{
					ArrayList<ArrayList<String>> getclauses = KB.get(predicate);
					 
						for(ArrayList<String>currule:getclauses)
						{
								ArrayList<String> std_rule = standardize_parameters(currule);
								ThetaO thetaI = unify(subsqstring, std_rule.get(0));
								
								LinkedList<String> duplicateList = new LinkedList<String>();
								
								Iterator<String> iterator = qlist.iterator();
								while(iterator.hasNext())
								{
									String newString = new String(iterator.next());
									duplicateList.addLast(newString);
								}								
								
								if(thetaI.success == true)
								{
										if(!std_rule.get(1).equals("TRUE"))
										{
											String[] subclausesl = std_rule.get(1).split("\\^");
											for(String subClause : subclausesl)
											{
												duplicateList.addLast(subClause);
											}
										}
										ThetaO ctheta = compose(thetaI, theta);
										ArrayList<ThetaO> thetaList = back_chain_list(duplicateList, ctheta);
										for(ThetaO retthetaO : thetaList)
										{
											answers.add(retthetaO);
										}
								}													
						}					
					return answers;					
				}
				else
				{
						return answers;								
				}
	}	

	public static ArrayList<ThetaO> back_chain(String query)
	{
		ThetaO theta = new ThetaO();
		LinkedList<String> qlist = new LinkedList<String>();
		qlist.addLast(query);
		
		ArrayList<ThetaO> answers = back_chain_list(qlist, theta);		
		return answers;
	}

	public static void main(String[] args) throws IOException
	{
				
		if(!args[0].equals("-i"))
		{
			System.out.println(" Not a valid command. The first argument should be '-i' followed by the inputFile name");
			System.exit(0);
		}
		
			Scanner s = new Scanner (new BufferedReader(new FileReader(args[1])));
			PrintWriter out = new PrintWriter(new FileWriter("output.txt"));						
				
				KB = new HashMap<String, ArrayList<ArrayList<String>>>();
			
				int N = Integer.parseInt(s.nextLine());
				String[] queries = new String[N];
				
				for(int i=0; i<N; i++)
				{
					queries[i] = s.nextLine();
				}
				
				int N1 = Integer.parseInt(s.nextLine());
				for(int i=0; i<N1; i++)
				{
					String temp = s.nextLine();	
					String clause = temp.replace(" ","");
					
					if(clause.contains("=>"))
					{
						addClause(clause);
					}
					else
					{
						addFact(clause);						
					}
					
				}
								
				Visited = new ArrayList<String>();
				index = 0;
				for(int i=0;i<queries.length;i++)
				{
					ArrayList<ThetaO> answers = back_chain(queries[i]);
					if(answers.size()>0)
					{
						out.println("TRUE");
					}
					else
					{
						out.println("FALSE");
					}
					Visited.clear();
					index = 0;					
				}
			
			s.close();
			out.close();		
		
	}

}
