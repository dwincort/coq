Require Import PArith.
Require Import FSets.FSetPositive.
Require Import FSets.FMapPositive.

Module ResourceSet := PositiveSet.
Module ResourceMap := PositiveMap.
Module VariableSet := PositiveSet.
Module VariableMap := PositiveMap.

Definition resource := positive.
Definition resource_set := ResourceSet.t.

Definition resource_disjoint rs1 rs2 :=
  ResourceSet.inter rs1 rs2 = ResourceSet.empty.

Inductive op_nullary : Type :=
  op_unit | op_nil.

Inductive op_unary : Type :=
  op_fst | op_snd | op_left | op_right | op_arr | op_first.

Inductive op_binary : Type :=
  op_pair | op_cons | op_comp | op_choice | op_fork.

Inductive op_resource : Type :=
  op_rsf | op_brsf.

Definition var := positive.

Inductive expr : Type :=
  | e_var : var -> expr  (* Weak HOAS *)
  | e_builtin : op_nullary -> expr
  | e_unary : op_unary -> expr -> expr
  | e_binary : op_binary -> expr -> expr -> expr
  | e_resource : op_resource -> resource -> expr
  | e_caseS : expr -> (var -> expr)  (* case left *)
                   -> (var -> expr)  (* case right *)
                   -> expr
  | e_caseL : expr -> expr                  (* case nil *)
                   -> (var -> var -> expr)  (* case cons *)
                   -> expr
  | e_lam : (var -> expr) -> expr  (* Weak HOAS *)
  | e_ap : expr -> expr -> expr
  | e_letw : expr -> (resource -> resource -> expr) -> expr.

Definition e_unit := e_builtin op_unit.
Definition e_nil := e_builtin op_nil.

Definition e_left := e_unary op_left.
Definition e_right := e_unary op_right.
Definition e_arr := e_unary op_arr.
Definition e_first := e_unary op_first.

Definition e_pair := e_binary op_pair.
Definition e_cons := e_binary op_cons.
Definition e_comp := e_binary op_comp.
Definition e_choice := e_binary op_choice.
Definition e_fork := e_binary op_fork.

Definition e_rsf := e_resource op_rsf.
Definition e_brsf := e_resource op_brsf.

Inductive type : Type :=
  | t_unit : type
  | t_prod : type -> type -> type
  | t_sum  : type -> type -> type
  | t_list : type -> type
  | t_func : type -> type -> type
  | t_sf   : type -> type -> resource_set -> type.
Notation "a ~> b" := (t_sf a b ResourceSet.empty) (at level 0, no associativity).
Notation "a ~( r )~> b" := (t_sf a b r) (at level 0).

Definition env := VariableMap.t type.

Definition rtype := prod type type.
Definition renv := ResourceMap.t rtype.

(*** End of Syntax Definitions *)

(*** Equality Boilerplates *)
Require Import Structures.Equalities.

Module NullaryDecidable <: DecidableTypeFull.
  Definition t := op_nullary.
  Definition eq := @eq op_nullary.
  Definition eq_equiv := @eq_equivalence op_nullary.
  Definition eq_refl := @eq_refl op_nullary.
  Definition eq_sym := @eq_sym op_nullary.
  Definition eq_trans := @eq_trans op_nullary.
  Definition eq_dec (op1 op2 : op_nullary) : {op1 = op2} + {~ op1 = op2}.
    destruct op1; destruct op2;
      solve [ left; reflexivity | right; discriminate ].
  Defined.
  Definition eqb (op1 op2 : op_nullary) :=
    match eq_dec op1 op2 with
    | left _ => true
    | right _ => false
    end.
  Lemma eqb_eq (op1 op2 : op_nullary) :
    eqb op1 op2 = true <-> op1 = op2.
  Proof.
    unfold eqb; destruct (eq_dec op1 op2).
      split; auto.

      split; intros.
        discriminate H.
        contradiction.
  Qed.
End NullaryDecidable.

Module UnaryDecidable <: DecidableTypeFull.
  Definition t := op_unary.
  Definition eq := @eq op_unary.
  Definition eq_equiv := @eq_equivalence op_unary.
  Definition eq_refl := @eq_refl op_unary.
  Definition eq_sym := @eq_sym op_unary.
  Definition eq_trans := @eq_trans op_unary.
  Definition eq_dec (op1 op2 : op_unary) : {op1 = op2} + {~ op1 = op2}.
    destruct op1; destruct op2;
      solve [ left; reflexivity | right; discriminate ].
  Defined.
  Definition eqb (op1 op2 : op_unary) :=
    match eq_dec op1 op2 with
    | left _ => true
    | right _ => false
    end.
  Lemma eqb_eq (op1 op2 : op_unary) :
    eqb op1 op2 = true <-> op1 = op2.
  Proof.
    unfold eqb; destruct (eq_dec op1 op2).
      split; auto.

      split; intros.
        discriminate H.
        contradiction.
  Qed.
End UnaryDecidable.

Module BinaryDecidable <: DecidableTypeFull.
  Definition t := op_binary.
  Definition eq := @eq op_binary.
  Definition eq_equiv := @eq_equivalence op_binary.
  Definition eq_refl := @eq_refl op_binary.
  Definition eq_sym := @eq_sym op_binary.
  Definition eq_trans := @eq_trans op_binary.
  Definition eq_dec (op1 op2 : op_binary) : {op1 = op2} + {~ op1 = op2}.
    destruct op1; destruct op2;
      solve [ left; reflexivity | right; discriminate ].
  Defined.
  Definition eqb (op1 op2 : op_binary) :=
    match eq_dec op1 op2 with
    | left _ => true
    | right _ => false
    end.
  Lemma eqb_eq (op1 op2 : op_binary) :
    eqb op1 op2 = true <-> op1 = op2.
  Proof.
    unfold eqb; destruct (eq_dec op1 op2).
      split; auto.

      split; intros.
        discriminate H.
        contradiction.
  Qed.
End BinaryDecidable.

Module OpResourceDecidable <: DecidableTypeFull.
  Definition t := op_resource.
  Definition eq := @eq op_resource.
  Definition eq_equiv := @eq_equivalence op_resource.
  Definition eq_refl := @eq_refl op_resource.
  Definition eq_sym := @eq_sym op_resource.
  Definition eq_trans := @eq_trans op_resource.
  Definition eq_dec (op1 op2 : op_resource) : {op1 = op2} + {~ op1 = op2}.
    destruct op1; destruct op2;
      solve [ left; reflexivity | right; discriminate ].
  Defined.
  Definition eqb (op1 op2 : op_resource) :=
    match eq_dec op1 op2 with
    | left _ => true
    | right _ => false
    end.
  Lemma eqb_eq (op1 op2 : op_resource) :
    eqb op1 op2 = true <-> op1 = op2.
  Proof.
    unfold eqb; destruct (eq_dec op1 op2).
      split; auto.

      split; intros.
        discriminate H.
        contradiction.
  Qed.
End OpResourceDecidable.

(*
Require Import OrderedType.

Module ExprOrderedType.

  Definition t := expr.
  Fixpoint eq_p (e1 e2 : expr)(p : positive) :=
  match e1, e2 with
  | e_var m, e_var n => m = n
  | e_builtin op, e_builtin op' => op = op'
  | e_unary op x, e_unary op' x' => op = op' /\ eq x x'
  | e_binary op x y, e_binary op' x' y' =>
    op = op' /\ eq_p x x' p /\ eq_p y y' p
  | e_resource op r, e_resource op' r' => op = op' /\ r = r'
  | e_caseS x l r, e_caseS x' l' r' =>
    eq_p x x' p /\ eq_p (l p) (l' p) (p + 1) /\ eq_p (r p) (r' p) (p + 1)
  | e_caseL x n c, e_caseL x' n' c' =>
    eq_p x x' p /\ eq_p n n' p /\ eq_p (c p (Pos.succ p)) (c' p (Pos.succ p)) (p + 2)
  | e_lam f, e_lam f' =>
    eq_p (f p) (f' p) (p + 1)
  | e_ap x y, e_ap x' y' => eq_p x x' p /\ eq_p y y' p
  | e_letw x f, e_letw x' f' =>
    eq_p x x' p /\ eq_p (f p (Pos.succ p)) (f' p (Pos.succ p)) (p + 2)
  | _, _ => False
  end.
  Definition eq e1 e2 := eq_p e1 e2 1.

  Definition constr_nth (e : expr) : positive :=
  match e with
  | e_var _ => 1%positive
  | e_builtin _ => 2%positive
  | e_unary _ _ => 3%positive
  | e_binary _ _ _ => 4%positive
  | e_resource _ _ => 5%positive
  | e_caseS _ _ _ => 6%positive
  | e_caseL _ _ _ => 7%positive
  | e_lam _ => 8%positive
  | e_ap _ _ => 9%positive
  | e_letw _ _ => 10%positive
  end.

  Definition nullary_contsr_nth op :=
  match op with
  | op_unit => 1%positive
  | op_nil => 2%positive
  end.

  Definition unary_constr_nth op :=
  match op with
  | op_fst => 1%positive
  | op_snd => 2%positive
  | op_left => 3%positive
  | op_right => 4%positive
  | op_arr => 5%positive
  | op_first => 6%positive
  end.

  Definition binary_constr_nth op :=
  match op with
  | op_pair => 1%positive
  | op_cons => 2%positive
  | op_comp => 3%positive
  | op_choice => 4%positive
  | op_fork => 5%positive
  end.

  Definition resource_constr_nth op :=
  match op with
  | op_rsf => 1%positive
  | op_brsf => 2%positive
  end.

  Definition 
  Fixpoint compare_p (e1 e2 : expr)(p : positive) :=
  match expr_constr_nth e1 ?= expr_constr_nth e2 with
  | Lt => Lt
  | Gt => Gt
  | Eq =>
    match e1, e2 with
    | e_var m, e_var n => m ?= n
    | e_builtin op, e_builtin op' => op = op'
  | e_unary op x, e_unary op' x' => op = op' /\ eq x x'
  | e_binary op x y, e_binary op' x' y' =>
    op = op' /\ eq_p x x' p /\ eq_p y y' p
  | e_resource op r, e_resource op' r' => op = op' /\ r = r'
  | e_caseS x l r, e_caseS x' l' r' =>
    eq_p x x' p /\ eq_p (l p) (l' p) (p + 1) /\ eq_p (r p) (r' p) (p + 1)
  | e_caseL x n c, e_caseL x' n' c' =>
    eq_p x x' p /\ eq_p n n' p /\ eq_p (c p (Pos.succ p)) (c' p (Pos.succ p)) (p + 2)
  | e_lam f, e_lam f' =>
    eq_p (f p) (f' p) (p + 1)
  | e_ap x y, e_ap x' y' => eq_p x x' p /\ eq_p y y' p
  | e_letw x f, e_letw x' f' =>
    eq_p x x' p /\ eq_p (f p (Pos.succ p)) (f' p (Pos.succ p)) (p + 2)
  | _, _ => False
  end.
*)
