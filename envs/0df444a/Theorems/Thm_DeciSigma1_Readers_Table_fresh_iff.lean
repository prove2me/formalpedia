-- Prove2me | Theorems.Thm_DeciSigma1_Readers_Table_fresh_iff
-- name    : DeciSigma1.Readers.Table.fresh_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:02.614813+00:00
-- url     : https://prove2.me/theorems/bd6d3926-8f95-4367-b557-3c7adb149201
-- title:
--   Table: fresh iff
-- statement:
--   The Table construction uses the fresh iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L194-L196
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L194-L196

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

theorem DeciSigma1.Readers.Table.fresh_iff [DecidableEq S] {W : Fin k → List α} {i : Fin k} :
    T.Fresh W i ↔ ∀ a < (W i).length, T.runPrefix W i a ≠ T.endState W i := by sorry
