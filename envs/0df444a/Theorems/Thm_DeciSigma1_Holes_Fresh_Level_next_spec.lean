-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_spec
-- name    : DeciSigma1.Holes.Fresh.Level.next_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:44.932821+00:00
-- url     : https://prove2.me/theorems/1540e32e-e1df-4745-b469-5e0bd6b07aa5
-- title:
--   Level: next spec
-- statement:
--   The next marker is the marker ending at the last anchor before the end, followed by the rest
--   of the word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L214-L232
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L214-L232

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

theorem DeciSigma1.Holes.Fresh.Level.next_spec {W : Fin k → List α} {l : Fin k} (hl : l ∈ (L.next W).active) :
    ∃ m ∈ L.active, L.marker m <:+ (W l).take (L.lastInteriorCut (W l)) ∧
      L.blockLengthAt (W l) (L.lastInteriorCut (W l)) = (L.marker m).length ∧
      (L.marker m).length ≤ L.lastInteriorCut (W l) ∧
      (L.next W).marker l = (W l).drop (L.lastInteriorCut (W l) - (L.marker m).length) ∧
      (L.next W).marker l = L.marker m ++ (W l).drop (L.lastInteriorCut (W l)) := by sorry
