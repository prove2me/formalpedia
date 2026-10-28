-- Prove2me | Theorems.Thm_D1Bound5_reciprocal_vandermonde_product
-- name    : D1Bound5.reciprocal_vandermonde_product
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:35:31.827562+00:00
-- url     : https://prove2.me/theorems/add55f86-6a2a-4d53-b3f3-09abfc971034
-- title:
--   Reciprocal vandermonde product
-- statement:
--   A product of ordinary Vandermonde differences changes to reciprocal nodes by an exact product identity. No distinctness is required.
-- source:
--   D1Bound5/ReciprocalAnchors.lean, lines 7-28, SHA-256 0eef21f646e4e303b7482f6be00f9e043fad50634704078870004bfb326da97b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.LinearAlgebra.Lagrange

section
open Polynomial Finset

namespace D1Bound5


theorem _root_.D1Bound5.reciprocal_vandermonde_product
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F)
    (ha : ∀ j ∈ s, a j ≠ 0) (i : ι) (hi : i ∈ s) :
    (∏ j ∈ s.erase i, (a i - a j)) =
      (a i) ^ (s.erase i).card *
        (∏ j ∈ s.erase i, a j) *
        (∏ j ∈ s.erase i, ((a j)⁻¹ - (a i)⁻¹)) := by sorry











end D1Bound5
end
