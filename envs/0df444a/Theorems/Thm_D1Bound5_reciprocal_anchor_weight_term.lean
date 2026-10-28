-- Prove2me | Theorems.Thm_D1Bound5_reciprocal_anchor_weight_term
-- name    : D1Bound5.reciprocal_anchor_weight_term
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:33:42.966287+00:00
-- url     : https://prove2.me/theorems/885d605d-05e0-4809-9813-01d80e3d8355
-- title:
--   Reciprocal anchor weight term
-- statement:
--   Pointwise transfer of barycentric weights from nodes `a` to reciprocal nodes `a⁻¹`, valid even if some nodes coincide.
-- source:
--   D1Bound5/ReciprocalAnchors.lean, lines 30-44, SHA-256 0eef21f646e4e303b7482f6be00f9e043fad50634704078870004bfb326da97b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.LinearAlgebra.Lagrange

section
open Polynomial Finset

namespace D1Bound5




theorem _root_.D1Bound5.reciprocal_anchor_weight_term
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F)
    (ha : ∀ j ∈ s, a j ≠ 0) (i : ι) (hi : i ∈ s) (k : ℕ) :
    ((a i)⁻¹) ^ (k + 1) /
      (∏ j ∈ s.erase i, (a i - a j)) =
      (∏ j ∈ s, a j)⁻¹ *
        ((a i)⁻¹) ^ (k + (s.erase i).card) /
        (∏ j ∈ s.erase i, ((a j)⁻¹ - (a i)⁻¹)) := by sorry









end D1Bound5
end
