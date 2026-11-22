-- Prove2me | Theorems.Thm_DeciSigma1_Readers_Table_runPrefix_mem_visitedStates
-- name    : DeciSigma1.Readers.Table.runPrefix_mem_visitedStates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:24.135793+00:00
-- url     : https://prove2.me/theorems/b8a9cfd2-ffc4-4921-b28c-350de7d7cd35
-- title:
--   Table: run Prefix mem visited States
-- statement:
--   The Table construction uses the run Prefix mem visited States property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L168-L170
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L168-L170

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

theorem DeciSigma1.Readers.Table.runPrefix_mem_visitedStates [DecidableEq S] (W : Fin k → List α) (i : Fin k) {a : ℕ}
    (h : a ≤ (W i).length) : T.runPrefix W i a ∈ T.visitedStates W i := by sorry
