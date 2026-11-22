-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_active_subset
-- name    : DeciSigma1.Holes.Fresh.Level.next_active_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:39.434037+00:00
-- url     : https://prove2.me/theorems/6438bd73-1395-4ca7-8f84-c9e223f5c13d
-- title:
--   Level: next active subset
-- statement:
--   The Level construction uses the next active subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L210-L210
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L210-L210

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

theorem DeciSigma1.Holes.Fresh.Level.next_active_subset (W : Fin k → List α) : (L.next W).active ⊆ L.active := by sorry
