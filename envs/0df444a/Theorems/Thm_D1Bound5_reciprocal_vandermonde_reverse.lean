-- Prove2me | Theorems.Thm_D1Bound5_reciprocal_vandermonde_reverse
-- name    : D1Bound5.reciprocal_vandermonde_reverse
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:33:43.55424+00:00
-- url     : https://prove2.me/theorems/8a501a17-1eca-42b0-bf28-3c89bd338461
-- title:
--   Reciprocal vandermonde reverse
-- statement:
--   Reversing all reciprocal Vandermonde differences gives exactly the parity sign for a full set of anchors.
-- source:
--   D1Bound5/ReciprocalAnchors.lean, lines 46-61, SHA-256 0eef21f646e4e303b7482f6be00f9e043fad50634704078870004bfb326da97b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.LinearAlgebra.Lagrange

section
open Polynomial Finset

namespace D1Bound5






theorem _root_.D1Bound5.reciprocal_vandermonde_reverse
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F) (i : ι) (hi : i ∈ s) :
    (∏ j ∈ s.erase i, ((a j)⁻¹ - (a i)⁻¹)) =
      (-1 : F) ^ (s.card - 1) *
        (∏ j ∈ s.erase i, ((a i)⁻¹ - (a j)⁻¹)) := by sorry







end D1Bound5
end
