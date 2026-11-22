-- Prove2me | Theorems.Thm_DeciSigma1_Readers_Table_runPrefix_of_le
-- name    : DeciSigma1.Readers.Table.runPrefix_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:17.703397+00:00
-- url     : https://prove2.me/theorems/a1b1fc20-4593-4f1d-ac75-2a5a09087d7d
-- title:
--   Table: run Prefix of le
-- statement:
--   The Table construction uses the run Prefix of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L142-L144
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L142-L144

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

theorem DeciSigma1.Readers.Table.runPrefix_of_le (W : Fin k → List α) (i : Fin k) {a : ℕ} (h : (W i).length ≤ a) :
    T.runPrefix W i a = T.endState W i := by sorry
