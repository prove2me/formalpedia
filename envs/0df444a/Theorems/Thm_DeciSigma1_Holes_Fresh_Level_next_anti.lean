-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_anti
-- name    : DeciSigma1.Holes.Fresh.Level.next_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:09.48627+00:00
-- url     : https://prove2.me/theorems/fd8c8b1c-c78d-4329-b5f5-c0462cc6d8f7
-- title:
--   Level: next anti
-- statement:
--   The factor antichain property passes to the next level.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L267-L322
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L267-L322

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

theorem DeciSigma1.Holes.Fresh.Level.next_anti (hA : L.FactorAntichain) {W : Fin k → List α} (hS : L.MarkersAreSuffixes W) :
    (L.next W).FactorAntichain := by sorry
