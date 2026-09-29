-- Prove2me | Theorems.Thm_BiconvexProg_BranchBound_vex_bilinear_separable
-- name    : BiconvexProg.BranchBound.vex_bilinear_separable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T17:54:57.44317+00:00
-- url     : https://prove2.me/theorems/372204e6-6837-48d4-819b-485c86aa128b
-- title:
--   Corollary (first clause) — $\mathrm{Vex}_\Omega\, x^\top y = \sum_i \mathrm{Vex}_{\Omega_i}\, x_i y_i$ on a box
-- statement:
--   Let $\Omega = \{(x,y) : l \le x \le L,\ m \le y \le M\} \subseteq \mathbb{R}^n \times \mathbb{R}^n$ be a box with coordinate rectangles $\Omega_i = \{(x_i, y_i) : l_i \le x_i \le L_i,\ m_i \le y_i \le M_i\}$. Then for every $(x, y) \in \Omega$,
--
--   $$\mathrm{Vex}_\Omega\, x^\top y = \sum_{i=1}^n \mathrm{Vex}_{\Omega_i}\, x_i y_i .$$
--
--   Together with Theorem 2, this gives the node functions of the algorithm in closed form: over a box, the envelope of the bilinear term is a sum of $n$ maxima of two affine functions.
--
--   **Formalization Note** The identity is stated at the points of $\Omega$. Degenerate boxes are allowed.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, p. 276, Corollary (first clause); also p. 275, display before Theorem 2

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_problem

namespace BiconvexProg.BranchBound

/-- Corollary, first clause (p. 276): on a box `Ω ⊂ ℝⁿ × ℝⁿ`, the convex envelope of `xᵀy` is the
sum of the convex envelopes of `x_i y_i` over the coordinate rectangles `Ω_i`. -/
theorem vex_bilinear_separable {n : ℕ} (Ω : Box n) (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hz : z ∈ Ω.toSet) :
    convexEnvelope Ω.toSet bilin z =
      ∑ i, convexEnvelope (Ω.rect i) (fun p : ℝ × ℝ => p.1 * p.2) (z.1 i, z.2 i) := by sorry

end BiconvexProg.BranchBound
