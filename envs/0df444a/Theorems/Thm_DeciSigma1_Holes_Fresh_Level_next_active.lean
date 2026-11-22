-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_active
-- name    : DeciSigma1.Holes.Fresh.Level.next_active
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:58.118796+00:00
-- url     : https://prove2.me/theorems/c0331017-ce47-405a-b86f-7e8875fc1c1b
-- title:
--   Level: next active
-- statement:
--   The Level construction uses the next active property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L206-L208
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L206-L208

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Fresh.Level
variable [DecidableEq α] (L : Level α k)
variable {L}

theorem DeciSigma1.Holes.Fresh.Level.next_active {W : Fin k → List α} {l : Fin k} :
    l ∈ (L.next W).active ↔ l ∈ L.active ∧ ∃ e ∈ L.markerEndCuts (W l), e < (W l).length := by sorry
