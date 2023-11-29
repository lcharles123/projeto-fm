/*	The system are compost by Three elements: Locks, LockUsers, SystemUser and the system itself
	At system execution there can be any number of these elements
	Alaways at system execution, will have one AdminUser
	Every Lock have it
	The components reside on a sig that is the system itself	
*/
-- The main componnent, where all elements reside and operate on
-- The system have any number of rooms, but must have one Admin 
one sig AccessSystem {
	var rooms: set Lock,
	var management: set SystemUser
}

-- Each room have its Lock, and its logMessages indicating user entered or not
-- If a user try to enter, a message are registered
-- And each Lock have its LockUser, LockState (represent if room is empty(closed) or not)
one sig Lock {
	var authorized: set LockUser,
	var logMessages: set LockMessage,
	var state: LockState
}

one abstract sig LockState {}
one sig Open extends LockState {}
one sig Closed extends LockState {}

-- A source of thuth about the validty of a LockUser, Locks will consult here
-- It will be as a property of LockUsers, that can be a Valid or Invalid
-- And can change anytime, because this system does not have power over
one abstract sig ExternalRegistry {}
one sig Valid extends ExternalRegistry {}
one sig Invalid extends ExternalRegistry {}

-- LockUsers is a user that operate on Locks
-- The ExternalRegistry are a property 
-- and have the state about the next action
sig LockUser {
	var valid: ExternalRegistry,
	var inside: Lock,
	var state: one Where
}

-- SystemUser are users that can only operate on system adding or removing LockUser or Locks
-- AdminUser can do anything on removing or adding LockUser's, Lock's and SubAdminUser's
-- and setting permissions for LockUser's, SubAdminUser can only set permissions
abstract sig SystemUser {}
one sig AdminUser extends SystemUser {}
sig SubAdminUser extends SystemUser {}

-- A message are table that stores the historic of access of each Lock
-- It have one author, room, and one Date.
sig LockMessage {
	author: LockUser,
	room: Access,
	time: Date
}

-- If message indicate Access Granted or not
one abstract sig Access {}
one sig Granted extends Access {}
one sig Denied extends Access {}

-- If the user wants to go Inside room or Outside
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

-- Initial conditions
pred init {
	one AccessSystem
}

-----------------------
-- Transition relation
-----------------------

pred trans []  {

/*   (some mb: Mailbox | createMailbox [mb])
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
   emptyTrash []*/
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
-- Assertions
--------------
assert canEnterOnlyIfAuthorized { System => p1 }
check canEnterOnlyIfAuthorized for 8
pred p1 {
-- Can enter the room only if authorized
}

assert insideOnlyOneRoomAtTime { System => p2 }
check insideOnlyOneRoomAtTime for 8
pred p2 {
-- Can enter only one room at a time if does not are inside another

}

assert onlyAuthorizedWhenValid { System => p3 }
check onlyAuthorizedWhenValid for 8
pred p3 {
-- Can be authorized to enter Lock only if Valid in ExternalRegistry

}
