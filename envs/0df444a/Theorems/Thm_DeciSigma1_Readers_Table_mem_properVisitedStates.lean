-- Prove2me | Theorems.Thm_DeciSigma1_Readers_Table_mem_properVisitedStates
-- name    : DeciSigma1.Readers.Table.mem_properVisitedStates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:23.896573+00:00
-- url     : https://prove2.me/theorems/ab5ad223-b7da-47a6-a15f-f8afe77167d0
-- title:
--   Table: mem proper Visited States
-- statement:
--   The Table construction uses the mem proper Visited States property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L164-L166
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L164-L166

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

theorem DeciSigma1.Readers.Table.mem_properVisitedStates [DecidableEq S] {W : Fin k → List α} {i : Fin k} {s : S} :
    s ∈ T.properVisitedStates W i ↔ ∃ a < (W i).length, T.runPrefix W i a = s := by sorry
