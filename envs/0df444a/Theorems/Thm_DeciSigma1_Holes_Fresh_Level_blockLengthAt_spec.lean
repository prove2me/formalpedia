-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_Level_blockLengthAt_spec
-- name    : DeciSigma1.Holes.Fresh.Level.blockLengthAt_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:13.245797+00:00
-- url     : https://prove2.me/theorems/28d3a4bc-5bfe-44e5-b3c2-30ca806f59dc
-- title:
--   Level: block Length At spec
-- statement:
--   The Level construction uses the block Length At spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L197-L204
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L197-L204

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

theorem DeciSigma1.Holes.Fresh.Level.blockLengthAt_spec {x : List α} {e : ℕ} (he : e ∈ L.markerEndCuts x) :
    ∃ m ∈ L.active, L.marker m <:+ x.take e ∧ L.blockLengthAt x e = (L.marker m).length := by sorry
