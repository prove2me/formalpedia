-- Prove2me | Theorems.Thm_D1Bound5_reciprocal_anchor_weight_standard
-- name    : D1Bound5.reciprocal_anchor_weight_standard
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:30.800861+00:00
-- url     : https://prove2.me/theorems/8d053e4f-ecf7-4151-b76a-def749f344e8
-- title:
--   Reciprocal anchor weight standard
-- statement:
--   The reciprocal-node transfer with the standard Lagrange orientation. This is the precise all-order weight reduction used for negative powers of the original interpolation anchors.
-- source:
--   D1Bound5/ReciprocalAnchors.lean, lines 63-84, SHA-256 0eef21f646e4e303b7482f6be00f9e043fad50634704078870004bfb326da97b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.LinearAlgebra.Lagrange

section
open Polynomial Finset

namespace D1Bound5








theorem _root_.D1Bound5.reciprocal_anchor_weight_standard
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F)
    (ha : ∀ j ∈ s, a j ≠ 0) (i : ι) (hi : i ∈ s) (k : ℕ) :
    ((a i)⁻¹) ^ (k + 1) /
      (∏ j ∈ s.erase i, (a i - a j)) =
      (-1 : F) ^ (s.card - 1) * (∏ j ∈ s, a j)⁻¹ *
        ((a i)⁻¹) ^ (k + s.card - 1) /
        (∏ j ∈ s.erase i, ((a i)⁻¹ - (a j)⁻¹)) := by sorry





end D1Bound5
end
