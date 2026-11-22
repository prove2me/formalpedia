-- Prove2me | Theorems.Thm_DeciSigma1_Readers_Table_runPrefix_add
-- name    : DeciSigma1.Readers.Table.runPrefix_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:42.130375+00:00
-- url     : https://prove2.me/theorems/fa2d588b-4976-4cd8-9dc9-04591ef80ef6
-- title:
--   Table: run Prefix add
-- statement:
--   The Table construction uses the run Prefix add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L146-L149
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L146-L149

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Finset.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Readers
open DeciSigma1.Automata
variable {α S : Type} {k : ℕ}
open DeciSigma1.Readers.Table
variable (T : Table α S k)
variable {T}

theorem DeciSigma1.Readers.Table.runPrefix_add (W : Fin k → List α) (i : Fin k) (a t : ℕ) :
    T.runPrefix W i (a + t) = runFrom T.step (T.runPrefix W i a) (((W i).drop a).take t) := by sorry
