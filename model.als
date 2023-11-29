/*	The system are compost by Three elements: Locks, LockUsers, SystemUser and the system itself
	At system execution there can be any number of these elements
	Alaways at system execution, will have one AdminUser
	Every Lock have it
	The components reside on a sig that is the system itself
	
*/
-- The main componnent, where all elements reside and operate on
one sig AccessSystem {
	var rooms: set Lock,
	var management: set SystemUser
}

one abstract sig Lock {
	var authorized: set LockUser,
	var logMessages: set LockMessage,
	var state: LockState
}

one abstract sig LockState {}
one sig Open extends LockState {}
one sig Closed extends LockState {}

-- A source of thuth about the validty of a LockUser, Locks will consult here
-- It will be as a property of LockUsers, that can be a Valid or Invalid
one abstract sig ExternalRegistry {}
one sig Valid extends ExternalRegistry {}
one sig Invalid extends ExternalRegistry {}

-- Users is a user that operate on Locks
sig LockUser {
	var valid: ExternalRegistry,
	var going: one Where
	

}

-- SystemUser are users that can only operate on system adding or removing LockUser
-- So its better to define in a sig apart from LockUser, because they have not in common properties
-- RegularUser can only 
abstract sig SystemUser {}
one sig AdminUser extends SystemUser {}
sig SubAdminUser extends SystemUser {}

-- A log for lock usage
one sig LockMessage {
	var user: LockUser,
	var permission: Access,
	time: Date
}
one abstract sig Access {}
one sig Granted extends Access {}
one sig Denied extends Access {}

one abstract sig Where {}
one sig Inside extends Where {}
one sig Outside extends Where {}

one sig Date {}
/*
-- added for convenience, track operations on the system
abstract sig Operation {}
-- Try_Unlock, Grant_Access, 
one sig TU, GA extends Operation {}
-- Add_Permission, Remove_Permission 
one sig AP, RP extends Operation {}
-- Check_Valid_Lock_User
one sig CVU extends Operation {}
one sig Track {
	var op: lone Operation
}*/

fact "Always have one AdminUser" {
	always one AdminUser
}

run {}

-- Initial conditions
/*pred [] init {

}*/

-----------------------
-- Transition relation
-----------------------
/*
pred trans []  {
   (some mb: Mailbox | createMailbox [mb])
   or
   (some mb: Mailbox | deleteMailbox [mb])
   or
   (some m: Message | createMessage [m])
   or
   (some m: Message | getMessage [m])
   or
   (some m: Message | sendMessage [m])
   or
   (some m: Message | deleteMessage [m])
   or
   (some m: Message | some mb: Mailbox | moveMessage [m, mb])
   or
   emptyTrash []
}


--------------------
-- System predicate
--------------------

-- Denotes all possible executions of the system from a state
-- that satisfies the initial condition
pred System {
  init
  always trans
}

run execution { System } for 8


--------------
-- Properties
--------------
check a1 for 8 // p1
pred p1 {
-- Active mailboxes contain only active messages
	all mb : Mailbox | all m : mb.messages | some (m.status & InUse) and 
								 some (mb.status & InUse)
}

--------------
-- Assertions
--------------
assert a1 { System => p1 }
*/
