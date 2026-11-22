-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_exists_isMulticoloredSumFree_rpow_le
-- name    : ArithmeticTriangleRemovalInVectorSpaces.exists_isMulticoloredSumFree_rpow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:12.331798+00:00
-- url     : https://prove2.me/theorems/b2577801-c21e-4f59-ba8c-d6227e12f56d
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: exists is Multicolored Sum Free rpow le
-- statement:
--   **Large multicolored sum-free families** (Kleinberg, Sawin and Speyer, using Pebody's theorem;
--   the second part of Theorem 2 of Fox and Lovász). For `p ≥ 2`, `η > 0` and
--   `d ≥ n₀ p η = ⌈(2 ^ (p + 3) * p ^ 10 / η) ^ 2⌉ + p ^ 4 + 1`, there is a multicolored sum-free
--   family in `Fin d → ZMod p` with at least `p ^ ((1 - c p - η) * d)` members.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/LowerBound.lean#L409-L432
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/LowerBound.lean#L409-L432

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_Family
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Decreasing
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_LowerBound
set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open ArithmeticTriangleRemovalInVectorSpaces
variable {n N : ℕ} {ρ : ℝ}

theorem ArithmeticTriangleRemovalInVectorSpaces.exists_isMulticoloredSumFree_rpow_le {p d : ℕ} (hp : 2 ≤ p) {η : ℝ} (hη : 0 < η)
    (hd : n₀ p η ≤ d) :
    ∃ (m : ℕ) (x y z : Fin m → Fin d → ZMod p),
      IsMulticoloredSumFree x y z ∧ (p : ℝ) ^ ((1 - c p - η) * d) ≤ m := by sorry
