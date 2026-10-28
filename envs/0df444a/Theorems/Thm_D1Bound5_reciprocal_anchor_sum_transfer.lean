-- Prove2me | Theorems.Thm_D1Bound5_reciprocal_anchor_sum_transfer
-- name    : D1Bound5.reciprocal_anchor_sum_transfer
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:27:23.309523+00:00
-- url     : https://prove2.me/theorems/d9641526-325e-4753-8d96-18bd84ebaeee
-- title:
--   Reciprocal anchor sum transfer
-- statement:
--   For every order, a negative-power barycentric sum at nonzero anchors transfers to an ordinary positive-power Lagrange moment of their reciprocals. The sign and total product are exact.
-- source:
--   D1Bound5/ReciprocalAnchors.lean, lines 86-102, SHA-256 0eef21f646e4e303b7482f6be00f9e043fad50634704078870004bfb326da97b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.LinearAlgebra.Lagrange

section
open Polynomial Finset

namespace D1Bound5










theorem _root_.D1Bound5.reciprocal_anchor_sum_transfer
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F)
    (ha : ∀ j ∈ s, a j ≠ 0) (k : ℕ) :
    (∑ i ∈ s, ((a i)⁻¹) ^ (k + 1) /
      (∏ j ∈ s.erase i, (a i - a j))) =
      ((-1 : F) ^ (s.card - 1) * (∏ j ∈ s, a j)⁻¹) *
        (∑ i ∈ s, ((a i)⁻¹) ^ (k + s.card - 1) /
          (∏ j ∈ s.erase i, ((a i)⁻¹ - (a j)⁻¹))) := by sorry



end D1Bound5
end
