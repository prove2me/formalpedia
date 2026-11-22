-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_markerEndCuts_eq
-- name    : DeciSigma1.Holes.Fresh.Level.next_markerEndCuts_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:13.619725+00:00
-- url     : https://prove2.me/theorems/207c1f6c-c196-4e65-8cd6-8b8e12abbd6e
-- title:
--   Level: next marker End Cuts eq
-- statement:
--   Read as a text, a next marker has exactly two anchors: the end of the marker it starts with
--   and its own end.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L326-L378
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L326-L378

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

theorem DeciSigma1.Holes.Fresh.Level.next_markerEndCuts_eq (hA : L.FactorAntichain) {W : Fin k → List α}
    (hS : L.MarkersAreSuffixes W)
    {l : Fin k}
    (hl : l ∈ (L.next W).active) :
    ∃ m ∈ L.active, L.marker m <+: (L.next W).marker l ∧
      (L.marker m).length < ((L.next W).marker l).length ∧
      L.markerEndCuts ((L.next W).marker l) =
          {(L.marker m).length, ((L.next W).marker l).length} := by sorry
