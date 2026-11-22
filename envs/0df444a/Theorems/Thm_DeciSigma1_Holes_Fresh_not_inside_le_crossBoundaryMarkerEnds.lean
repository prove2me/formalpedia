-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_not_inside_le_crossBoundaryMarkerEnds
-- name    : DeciSigma1.Holes.Fresh.not_inside_le_crossBoundaryMarkerEnds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:46.182817+00:00
-- url     : https://prove2.me/theorems/201483d7-e36a-4a20-b400-0e9de443d60f
-- title:
--   Fresh: not inside le cross Boundary Marker Ends
-- statement:
--   No anchor of `z` alone lies at or before the end of a marker that starts to the left of `z`:
--   its marker would occur strictly inside the other marker, against the factor antichain
--   property.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L618-L633
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L618-L633

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}

theorem DeciSigma1.Holes.Fresh.not_inside_le_crossBoundaryMarkerEnds {t : ℕ} (ht : 1 ≤ t) {u z : List α}
    {p q : ℕ} (hp : p ∈ crossBoundaryMarkerEnds W t u z) (hq : q ∈ contextAnchors W t z)
        (hqp : q ≤ p) : False := by sorry
