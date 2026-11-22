-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_Level_mem_markerEndCuts
-- name    : DeciSigma1.Holes.Fresh.Level.mem_markerEndCuts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:53.273155+00:00
-- url     : https://prove2.me/theorems/250d30dd-e791-4551-8f5e-c5145717248f
-- title:
--   Level: mem marker End Cuts
-- statement:
--   The Level construction uses the mem marker End Cuts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L161-L163
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L161-L163

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

theorem DeciSigma1.Holes.Fresh.Level.mem_markerEndCuts {u : List α} {e : ℕ} :
    e ∈ L.markerEndCuts u ↔ e ≤ u.length ∧ ∃ m ∈ L.active, L.marker m <:+ u.take e := by sorry
