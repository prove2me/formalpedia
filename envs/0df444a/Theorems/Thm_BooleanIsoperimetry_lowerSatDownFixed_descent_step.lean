-- Prove2me | Theorems.Thm_BooleanIsoperimetry_lowerSatDownFixed_descent_step
-- name    : BooleanIsoperimetry.lowerSatDownFixed_descent_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:34.050966+00:00
-- url     : https://prove2.me/theorems/66a76940-9461-4854-a909-e5556ecf29dd
-- title:
--   Boolean Isoperimetry: lower Sat Down Fixed descent step
-- statement:
--   **Reduction step to a lower-saturated, down-fixed family** (no colex shift).
--   If `A` is not yet both coordinate-Down-fixed and lower-level saturated, one
--   coordinate Down-compression or one level-block fill gives a family of the same
--   size, no larger neighborhood, and strictly smaller potential.  Both moves are
--   sorry-free; no within-layer colex swap is used.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2129-L2149
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2129-L2149

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry

theorem BooleanIsoperimetry.lowerSatDownFixed_descent_step {N : ℕ} (A : Finset (Cube N))
    (h : ¬ (IsCoordinateDownFixed A ∧ IsLowerLevelSaturated A)) :
    ∃ A' : Finset (Cube N), A'.card = A.card ∧
      (neighborhood 1 A').card ≤ (neighborhood 1 A).card ∧
      compressionPotential A' < compressionPotential A := by sorry
