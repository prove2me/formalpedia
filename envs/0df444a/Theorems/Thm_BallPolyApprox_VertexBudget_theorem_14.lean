-- Prove2me | Theorems.Thm_BallPolyApprox_VertexBudget_theorem_14
-- name    : BallPolyApprox.VertexBudget.theorem_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:55:30.474236+00:00
-- url     : https://prove2.me/theorems/ff37616f-e242-4c8d-b375-4d0dc999ee03
-- title:
--   Theorem 14 — the $L^1$ error of a piecewise-affine $h$ against $q=|x|^2$ is at least $\beta_m$ times the interpolation error
-- statement:
--   Let $D\subset\mathbb R^m$ ($m\ge1$) be a polyhedral domain with a conforming triangulation $\mathcal T$, let $h:D\to\mathbb R$ be continuous and affine on every simplex of $\mathcal T$, and let $I_{\mathcal T}q$ be the continuous function on $D$ that agrees with $I_Tq$ on each $T\in\mathcal T$, $q(x)=|x|^2$. Then
--   $$\int_D|h(x)-q(x)|\,dx\ge\beta_m\int_D\big(I_{\mathcal T}q(x)-q(x)\big)\,dx\quad(32).$$
--   The Lean statement is for any finite family of nondegenerate $m$-simplices $T_j$ with pairwise Lebesgue-null intersections, $D=\bigcup_jT_j$, and $h$ affine on each $T_j$; the right side is $\beta_m\sum_j\int_{T_j}W_{T_j}(x)\,dx$.
--
--   Differences from the source:
--   - generalization: conforming triangulation 𝒯 of a polyhedral domain D, h continuous and affine on each simplex, right side ∫_D (I_𝒯 q − q) → finite family of affinely independent m-simplices T_j with pairwise null intersections, D = ⋃ T_j, h affine on each T_j (no continuity), right side Σ_j ∫_{T_j} W_{T_j}; reason: the proof is per simplex and sums; a conforming triangulation is such a family (distinct simplices meet in lower-dimensional faces), and there I_𝒯 q = I_T q on each T, so Σ_j ∫_{T_j} W_{T_j} = ∫_D (I_𝒯 q − q)
-- source:
--   Gorodzha, Hoehner, Kur, Approximating the Euclidean Ball by Polytopes, arXiv:2610.34651 (sha256 164dc885…), Theorem 14, p. 15 (PDF 17)

import Mathlib
import Definitions.Def_BallPolyApprox_VertexBudget_VolumeError
import Definitions.Def_BallPolyApprox_VertexBudget_SimplexLayer

set_option autoImplicit false

open MeasureTheory

namespace BallPolyApprox.VertexBudget

/-- Theorem 14 (p. 15, PDF 17), for a finite family of nondegenerate `m`-simplices
`T_j = conv(v_j) ⊂ ℝ^m` with pairwise Lebesgue-null intersections, covering
`D = ⋃_j T_j` (a conforming triangulation of a polyhedral domain is such a family): if
`h : D → ℝ` is affine on every `T_j`, then
`∫_D |h(x) − q(x)| dx ≥ β_m Σ_j ∫_{T_j} (I_{T_j} q(x) − q(x)) dx = β_m ∫_D (I_𝒯 q − q)` (32),
with `q(x) = |x|²`. -/
theorem theorem_14 (m : ℕ) (hm : 1 ≤ m) {ι : Type} [Fintype ι] (v : ι → Fin (m + 1) → Rd m)
    (hv : ∀ j, AffineIndependent ℝ (v j))
    (hdisj : ∀ j j', j ≠ j' →
      volume (convexHull ℝ (Set.range (v j)) ∩ convexHull ℝ (Set.range (v j'))) = 0)
    (h : Rd m → ℝ)
    (hh : ∀ j, ∃ a : Rd m →ᵃ[ℝ] ℝ, ∀ x ∈ convexHull ℝ (Set.range (v j)), h x = a x) :
    betaM m * ∑ j, ∫ x in convexHull ℝ (Set.range (v j)), interpGap (v j) x ≤
      ∫ x in ⋃ j, convexHull ℝ (Set.range (v j)), |h x - ‖x‖ ^ 2| := by sorry

end BallPolyApprox.VertexBudget
