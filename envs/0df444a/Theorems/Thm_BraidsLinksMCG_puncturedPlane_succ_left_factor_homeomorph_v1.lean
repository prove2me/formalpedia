-- Prove2me | Theorems.Thm_BraidsLinksMCG_puncturedPlane_succ_left_factor_homeomorph_v1
-- name    : BraidsLinksMCG.puncturedPlane_succ_left_factor_homeomorph_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-24T16:31:58.528721+00:00
-- url     : https://prove2.me/theorems/30b39e5f-7f2e-4a1b-bcb3-19951e191127
-- title:
--   The fixed left half-plane factor is pointed-homeomorphic to the old punctured plane
-- statement:
--   The left member of the fixed two-half-plane cover is a punctured left half-plane containing exactly the first $n$ punctures. This child records the spatial bridge needed by the later free-group calculation: there is a pointed homeomorphism from that cover member to the $n$-punctured plane, with a point in the factor mapped to a point whose real coordinate is $n+1$ and whose imaginary coordinate is $1$. The statement is only a spatial identification; it does not assume freeness or any successor-step theorem.
--
--   The intended construction is a strictly increasing order homeomorphism on the real-coordinate interval, extended through the complex homeomorphism $\mathbb{C}\cong\mathbb{R}\times\mathbb{R}$. It fixes the old puncture coordinates and normalizes the newly added boundary puncture out of the strict left half-plane.
-- source:
--   A. Hatcher, Algebraic Topology, Section 1.2, Theorem 1.20 and the classical punctured-plane half-plane proof; the coordinate normalization is the explicit real interval homeomorphism used to identify the left factor with the old punctured plane.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

namespace BraidsLinksMCG

theorem puncturedPlane_succ_left_factor_homeomorph_v1 (n : ℕ)
    (A : Bool → Set (PuncturedPlane (n + 1)))
    (hfalse :
      A Bool.false =
        {z : PuncturedPlane (n + 1) |
          z.1.re < ((n : ℕ) + 1 : ℝ)}) :
    ∃ (c : ↥(A Bool.false))
      (h : ↥(A Bool.false) ≃ₜ PuncturedPlane n)
      (z : PuncturedPlane n),
      h c = z ∧ z.1.re = (n : ℝ) + 1 ∧ z.1.im = 1 := by sorry

end BraidsLinksMCG
