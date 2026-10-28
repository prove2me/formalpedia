-- Prove2me | Theorems.Thm_FiniteEnergyPlane_norm_fderiv_le_mul_gradNorm
-- name    : FiniteEnergyPlane.norm_fderiv_le_mul_gradNorm
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-25T18:18:33.660988+00:00
-- url     : https://prove2.me/theorems/cd41f9bd-b862-46ff-8f36-6a50f99b2a94
-- title:
--   Euclidean derivative bounded by the $\mathbb{R}$-invariant gradient norm on a slab
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Write $y=e^{2a}x$ with $x=\mathrm{proj}(y)\in S$ for $y\ne0$. Then for every $A\in\mathbb R$ there is a constant $M$ such that for every map $u:\mathbb C\to\mathbb R^{2n+2}$ and every $z\in\mathbb C$ with $u$ differentiable at $z$, $u(z)\ne0$ and $|a(u(z))|\le A$,
--   $$\|Du(z)\|\ \le\ M\,\big(\|D(a\circ u)(z)\|+\|D(\mathrm{proj}\circ u)(z)\|\big).$$
--
--   So on a slab $|a|\le A$ the Euclidean derivative is controlled by the $\mathbb R$-invariant gradient norm.
--
--   **Formalization Note** The right-hand side is `M * gradNorm H u z`. The compatible structure $J$ does not enter the conclusion.
-- source:
--   H. Hofer, Invent. Math. 114 (1993), Section 3, (42)-(43); U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- On a slab of the symplectization the Euclidean size of the derivative is controlled by the
`ℝ`-invariant one. For a strictly star-shaped level and `A ∈ ℝ` there is `M` such that for every
map `u : ℂ → ℝ^{2n+2}` differentiable at `z` with `u(z) ≠ 0` and `|a(u(z))| ≤ A`,
`‖Du(z)‖ ≤ M |∇u(z)|`, where `|∇u| = ‖D(a ∘ u)‖ + ‖D(proj ∘ u)‖` is `gradNorm`. -/
theorem norm_fderiv_le_mul_gradNorm {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (A : ℝ) :
    ∃ M : ℝ, ∀ (u : ℂ → V n) (z : ℂ), DifferentiableAt ℝ u z → u z ≠ 0 →
      |aCoord H (u z)| ≤ A → ‖fderiv ℝ u z‖ ≤ M * gradNorm H u z := by
  sorry

end FiniteEnergyPlane
