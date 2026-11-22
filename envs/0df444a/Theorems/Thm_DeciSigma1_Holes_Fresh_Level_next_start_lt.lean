-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_start_lt
-- name    : DeciSigma1.Holes.Fresh.Level.next_start_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:11.133701+00:00
-- url     : https://prove2.me/theorems/9e7d51ea-315b-4f86-ad26-f2c2d0cb4e71
-- title:
--   Level: next start lt
-- statement:
--   The next marker starts strictly before the current marker of the same word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L235-L252
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L235-L252

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

theorem DeciSigma1.Holes.Fresh.Level.next_start_lt (hA : L.FactorAntichain) {W : Fin k → List α} (hS : L.MarkersAreSuffixes W)
    {l : Fin k}
    (hl : l ∈ (L.next W).active) :
    L.lastInteriorCut (W l) - L.blockLengthAt (W l) (L.lastInteriorCut (W l)) < (W l).length -
        (L.marker l).length := by sorry
