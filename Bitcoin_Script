Require Export BinNums.
Local Open Scope Z_scope.
Require Import List.
Require Import Bool.
Import ListNotations.
Require Import ZArith.
Require Import BinInt.
Delimit Scope Int_scope with I.
Local Open Scope Int_scope.
Require Import Plus.
Require Import Mult.


Module Stack.
Inductive OP_CODES : Type :=
  (* CRYPTO *)
  | OP_RIPEMD160 : OP_CODES
  | OP_SHA1 : OP_CODES
  | OP_SHA256 : OP_CODES
  | OP_HASH160 : OP_CODES
  | OP_CHECKSIG : OP_CODES
  | OP_CHECKSIGVERIFY : OP_CODES
  | OP_CHECKMULTISIG : OP_CODES
  | OP_CHECKMULTISIGVERIFY : OP_CODES
  (* BITWISE LOGIC *)
  | OP_EQUAL : OP_CODES
  | OP_EQUALVERIFY : OP_CODES
  | OP_VERIFY : OP_CODES
  | OP_RETURN : OP_CODES
  (* STACK CONTROL *)
  | OP_IFDUP : Z -> OP_CODES
  (* Puts the size of the stack into the stack *)
  | OP_DEPTH : OP_CODES
  | OP_DROP : OP_CODES
  | OP_DUP : OP_CODES
  | OP_2DUP : OP_CODES
  | OP_NIP : OP_CODES
  | OP_OVER : OP_CODES
  | OP_PICK : OP_CODES
  | OP_ROLL : OP_CODES
  | OP_ROT : OP_CODES
  | OP_SWAP : OP_CODES
  | OP_PUSH : Z -> OP_CODES
  (* To be added, if needed *)
  (* LOCKTIME *)
  | OP_CHECKLOCKTIMEVERIFY : Z -> OP_CODES
  | OP_CHECKSEQUENCEVERIFY : Z -> OP_CODES
  (* FLOW CONTROL *)
  (* If the top value is not False, statement is
    executed. The top stack element is removed. *)
  | OP_IF : OP_CODES
  | OP_NOTIF : OP_CODES
  | OP_ELSE : OP_CODES
  | OP_ENDIF : OP_CODES
  (* CONSTANTS *)
  | OP_NUM : Z -> OP_CODES
  | OP_NEGATE : nat -> OP_CODES
  | OP_0 : OP_CODES
  | OP_1 : OP_CODES
  | OP_NOP : OP_CODES
  (* ARITHMETIC *)
  | OP_1ADD : OP_CODES
  | OP_1SUB : OP_CODES
  | OP_ABS : OP_CODES
  | OP_NOT : OP_CODES
  | OP_ADD : OP_CODES
  | OP_SUB : OP_CODES
  | OP_NUMEQUAL : Z -> Z -> OP_CODES
  | OP_NUMEQUALVERIFY : Z -> Z -> OP_CODES
  | OP_NUMNOTEQUAL : Z -> Z -> OP_CODES
  | OP_LESSTHAN : Z -> Z -> OP_CODES
  | OP_GREATERTHAN : Z -> Z -> OP_CODES
  | OP_MIN : Z -> Z -> OP_CODES
  | OP_MAX : Z -> Z -> OP_CODES
  | OP_WITHIN : Z -> Z -> Z -> OP_CODES
  (* PSEUDO-WORDS *)
  | OP_PUBKEYHASH : OP_CODES
  | OP_PUB_KEY : OP_CODES
  | OP_INVALIDOPCODE : OP_CODES
  | OP_TIME_TO_ELAPSE : nat -> OP_CODES.

Definition OP_CODES_List := list OP_CODES.
Definition stack := list Z.

Compute ([1;2] ++ [3]) .

(* Some basic operations *)

(* length - returns the lenght of a given list *)
Fixpoint length (l:OP_CODES_List) : nat :=
    match l with
      | nil => 0
      | _ :: m => S (length m)
    end.

(* top - returns the top most element from the stack *)
Definition top (default:Z)(s:stack) : Z := 
  match s with
  | nil => default
  | h::t => h
  end.

(* pop - extracts the top most element from the stack *)
Definition pop (s:stack) : stack := 
  match s with
  | nil => nil
  | h :: t => t
  end.

(* push - a new item is added on the top of the stack *)
Definition push (item:Z) (s:stack) : stack := 
  match s with
  | nil => [item]
  | h :: t => item :: h :: t
  end.

(* rot - rotates the top three items to the left *)
Definition rot (s:stack) : stack :=
  match s with
  | nil => []
  | h :: t => (top 0 t) :: (top 0 (pop t)) :: h :: (pop (pop t))
  end.

(* Cryptography functions *)
Definition compute_SHA1 (s:stack) : stack :=
  match s with
  | nil => []
  | h :: t => push (top 0 s) (pop s)
  end.

Definition compute_SHA256 (s:stack) : stack :=
  match s with
  | nil => []
  | h :: t => push (top 0 s) (pop s)
  end.

Fixpoint compute_elapsed_time (time:nat) (s:stack) : stack :=
match time with
| 0 => pop s
| S k => compute_elapsed_time k s
end.

Definition verify_op (s:stack) : bool :=
  match s with
  | nil => true
  | h::t => if Z.eqb h 1%Z then true else false
  end.

Definition verify_eq (first:Z) (second:Z) : Z :=
   if Z.eqb first second then 1 else 0.

Definition verify (s:stack) : bool * stack  :=
  match s with
  | nil => (false, [])
  | h :: t => if (Z.eqb (top 0 s) 1%Z) then (true, t) else (false, t)
  end.

Fixpoint first_n_elems (n:nat) (s:stack) : stack :=
  match n with
  | O => nil
  | S m => match s with 
           | nil => nil
           | h :: t => h :: (first_n_elems m t)
           end
  end.

Fixpoint remove_n_elems (n:nat) (s:stack) : stack :=
  match n with
  | O => s
  | S m => match s with
           | nil => nil
           | h :: t => (remove_n_elems m t)
           end
  end.

Compute(remove_n_elems 1 [1%Z; 2%Z; 3%Z; 5%Z; 4%Z]).

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1, b2 with
  | true, _ => b2
  | false, _ => false
  end.

Fixpoint compare_lists (s1:stack) (s2:stack) : bool :=
  match s1, s2 with
  | nil, nil => true
  | h1::t1, h2::t2 => andb (Z.eqb h1 h2) (compare_lists t1 t2) 
  | _, _ => false
  end.

Definition compute_op (s:stack)(op:OP_CODES) : stack :=
  match op with
  | OP_NOT => if (Z.eqb (top 0 s) 0%Z) then (push 1 (pop s)) else (push 0 (pop s)) 
  | OP_DUP => push (top 0 s) s
  | OP_2DUP => push (top 0 s)(push (top 0 (pop s)) s)
  | OP_DROP => pop s
  | OP_PUSH n => push n s
  | OP_1 => push 1 s
  | OP_0 => push 0 s
  | OP_NUM n => push n s
  | OP_ADD => push (Zplus (top 0 s) (top 0 (pop s))) (pop (pop s)) 
  | OP_SUB => push (Zminus (top 0 s) (top 0 (pop s))) (pop (pop s))
  | OP_SHA1 => compute_SHA1 s
  | OP_SHA256 => compute_SHA256 s
  | OP_TIME_TO_ELAPSE n => compute_elapsed_time n s
  | OP_EQUAL => if (Z.eqb (verify_eq (top 0 s) (top 0 (pop s)))) 1%Z then (push 1 (pop (pop s))) 
                else (push 0 (pop (pop s)))
  | OP_IF => if (Z.eqb (top 0 s) 1%Z) then pop s else s
  | OP_CHECKSIG => if (Z.eqb (verify_eq (top 0 s) (top 0 (pop s)))) 1%Z then (push 1 (pop (pop s)))
                   else (push 0 (pop (pop s)))
  | _ => s
  end.


Fixpoint split_if (script:OP_CODES_List)(branch:Z) : OP_CODES_List * OP_CODES_List :=
  match script with
  | nil => (nil, nil)
  | OP_ENDIF::t1 => (t1, t1)
  | OP_ELSE::t1 => split_if t1 1
  | s::t => if(Z.eqb branch 0%Z) then let (a,b) := (split_if t branch) in (s::a, b) else let (a,b) := (split_if t branch) in (a,s::b)
  end.


Fixpoint multiSignature (s:stack) (l:stack) (m : nat): bool := 
  match m with
  | 0 => true
  | S m' => match s with
            | nil => false
            | x :: s' => match l with
                         | nil => false
                         | x' :: l' => if (Z.eqb x x')
                                       then (multiSignature s' l' m')
                                       else false
                         end
             end
  end.


Fixpoint checkElement (s:stack) (x:Z) : bool :=
  match s with
  | nil => false
  | x' :: s' => if (Z.eqb x x') 
                then true
                else (checkElement s' x)
  end.

Fixpoint multiSignatureScript (s:stack) (l:stack): bool := 
  match l with
  | nil => true
  | x :: l' => match (checkElement s x) with
               | true => (multiSignatureScript s l')
               | false => false
               end
  end.


Fixpoint evaluate_script (s:stack)(script:OP_CODES_List)(n : nat) : stack :=
match n with
| O => s
| S m => match script with
        | nil => s
        | OP_IF::t => if (Z.eqb (top 0 s) 1%Z) 
                      then let (a,b) := (split_if t 0)
                           in (evaluate_script (pop s) a m) 
                      else let (a,b) := (split_if t 0)
                           in (evaluate_script (pop s) b m)
        | OP_VERIFY::t => if (Z.eqb (top 0 s) 1%Z) 
                          then (evaluate_script (pop s) t m) 
                          else (evaluate_script s [OP_PUSH 0] m)
        | OP_CHECKLOCKTIMEVERIFY n :: t => if (Z.leb n (top 0 s)) 
                                           then (evaluate_script s t m)
                                           else (evaluate_script s [OP_PUSH 0] m)
        | OP_CHECKSEQUENCEVERIFY n :: t => if (Z.geb n (top 0 s))
                                           then (evaluate_script s t m)
                                           else (evaluate_script s [OP_PUSH 0] m)
        | OP_CHECKMULTISIG :: t => 
          if (multiSignatureScript (first_n_elems (Z.to_nat (top 0 (remove_n_elems (Z.to_nat (top 0 s)) (pop s)))) 
                                   (pop (remove_n_elems (Z.to_nat (top 0 s)) (pop s))))
                                   (first_n_elems (Z.to_nat (top 0 s)) (pop s)))
          then [1%Z] else [0%Z]
        | h::t => (evaluate_script (compute_op s h) t m)
      end
end.

Definition check_stack (s:stack) : bool :=
  match s with
  | nil => true
  | h::t => if (Z.eqb h 1%Z) then true else false
end.


Definition firstScript := [5%Z] .
Definition secondScript := [7%Z; 8%Z; 10%Z] .

Compute(multiSignatureScript secondScript firstScript) .

(* 1 - Lock with PublicKey *)
(* locking script - [OP_PUSH <publicKey>; OP_CHECKSIG] *)
(* unlocking script - <sig> *)
Definition LWPK := [OP_PUSH 3; OP_CHECKSIG] .
Compute((check_stack (evaluate_script [3%Z] LWPK (length LWPK)))).

(* 2 - Lock with Multisig *)
(* locking script - [OP_PUSH <M>; OP_PUSH <publicKeys>; OP_PUSH <N>; OP_CHECKMULTISIG] *)
(* unlocking script - <digitalSignatures> *)
Definition LWMS (l1:Z) (l2:Z) (pk:OP_CODES_List) := [OP_PUSH l1] ++ pk ++ [OP_PUSH l2] ++ [OP_CHECKMULTISIG] .
Compute(evaluate_script [1%Z; 2%Z] 
                        (LWMS 3%Z 2%Z [OP_PUSH 3; OP_PUSH 2; OP_PUSH 1] )
                        (length (LWMS 3%Z 2%Z[OP_PUSH 3; OP_PUSH 2; OP_PUSH 1]))).

(* 3 - Lock with PublicKeyHash *)
(* locking script - [OP_DUP; OP_SHA256; OP_PUSH <public_key_hash>; OP_EQUALVERIFY; OP_CHECKSIG] *)
(* unlocking script - <sig> <public_key> *)
Definition LWPKH (hash : Z) := [OP_DUP; OP_SHA256; OP_PUSH hash; OP_EQUALVERIFY; OP_CHECKSIG] .
Compute((check_stack (evaluate_script [3%Z; 3%Z] (LWPKH 3%Z) (length (LWPKH 3%Z))))).

(* 4 - Reveal Preimage *)
(* locking script - [OP_SHA256; OP_PUSH <public_key_hash>; OP_EQUAL] *)
(* unlocking script - <public_key> *)
Definition RP := [OP_SHA256; OP_PUSH 3; OP_EQUAL] .
Compute((check_stack (evaluate_script [3%Z] RP (length RP)))) .

(* 5 - Reveal Collision *)
(* locking script - [OP_2DUP; OP_EQUAL; OP_NOT; OP_VERIFY; OP_SHA1; OP_SWAP; OP_SHA1; OP_EQUAL] *)
(* unlocking script - <public_key1> <public_key2> *)
Definition RC := [OP_2DUP; OP_EQUAL; OP_NOT; OP_VERIFY; OP_SHA1; OP_SWAP; OP_SHA1; OP_EQUAL] .
Compute((check_stack (evaluate_script [3%Z; 1%Z] RC (length RC)))) .

(* 6 - Reveal FixPoint *)
(* locking script - [OP_DUP; OP_SHA256; OP_EQUAL] *)
(* unlocking script - <public_key_hash> *)
Definition RFP := [OP_DUP; OP_SHA256; OP_EQUAL] .
Compute((check_stack (evaluate_script [3%Z] RFP (length RFP)))) .

(* 7 - Lock Until *)
(* locking script - [OP_PUSH <time>; OP_CHECKLOCKTIMEVERIFY <time_limit>; OP_DROP; OP_PUSH <public_key>; OP_CHECKSIG] *)
(* unlocking script - <sig> *)
Definition LU (y : Z) (time1 : Z) (time2 : Z) := [OP_PUSH time1; OP_CHECKLOCKTIMEVERIFY time2; OP_DROP; OP_PUSH y; OP_CHECKSIG] .
Compute((check_stack (evaluate_script [3%Z] (LU 3%Z 10%Z 9%Z) (length (LU 3%Z 10%Z 9%Z))))) .


(* Proofs *)
Theorem crypto_operations : forall s:stack, compute_SHA1 s = s .
Proof.
  intros s.
  destruct s; trivial.
  simpl.
  induction s; simpl; trivial.
Qed.

Theorem exec : forall s:stack, forall x, Z.eqb (top x s) 1%Z = true -> check_stack s = true.
Proof.
  intros.
  unfold check_stack.
  unfold top in H.
  destruct s. trivial.
  rewrite H. trivial.
Qed.

Lemma LWPKH_Proof : forall s, forall x, forall y, (evaluate_script [y] (LWPKH y) (length (LWPKH y))) = s ->
  top x s = 1%Z.
Proof.
  intros.
  simpl in H.
  unfold verify_eq in H. 
  case_eq (Z.eqb y y); intros; rewrite H0 in H; simpl in *. 
  - unfold top. subst; trivial.
  - rewrite Z.eqb_refl in H0. inversion H0.
Qed.

Lemma LU_Proof :
  forall x,
  forall y,
  forall t1,
  forall t2,
    (Z.eqb
       (top x (evaluate_script [y] (LU y t1 t2) (length (LU y t1 t2))))
       1%Z
    ) = true ->
    (Z.leb t2 t1) = true .
Proof.
  intros.
  simpl in H.
  case_eq (Z.leb t2 t1); intros H'; rewrite H' in *; trivial.
Qed.


End Stack.