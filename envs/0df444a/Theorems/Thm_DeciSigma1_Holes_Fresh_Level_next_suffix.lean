-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_suffix
-- name    : DeciSigma1.Holes.Fresh.Level.next_suffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:22.436943+00:00
-- url     : https://prove2.me/theorems/644253ac-884e-447b-8635-f18de9424cc3
-- title:
--   Level: next suffix
-- statement:
--   The current marker of an active word is a proper suffix of its next marker.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L255-L264
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L255-L264

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

theorem DeciSigma1.Holes.Fresh.Level.next_suffix (hA : L.FactorAntichain) {W : Fin k → List α} (hS : L.MarkersAreSuffixes W)
    {l : Fin k}
    (hl : l ∈ (L.next W).active) :
    L.marker l <:+ (L.next W).marker l ∧ (L.marker l).length < ((L.next W).marker l).length := by sorry
