-- Prove2me | Theorems.Thm_FiniteEnergyPlane_fderiv_proj_eq_zero_iff
-- name    : FiniteEnergyPlane.fderiv_proj_eq_zero_iff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-23T21:25:06.729045+00:00
-- url     : https://prove2.me/theorems/7184113b-453d-43c0-ad3f-425e4b561d30
-- title:
--   The kernel of the derivative of the radial projection to S is the radial line
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be strictly star-shaped and let $\mathrm{pr}_S:\mathbb{R}^{2n+2}\setminus\{0\}\to S$ be the radial projection. For $y\neq0$ and $v\in\mathbb{R}^{2n+2}$,
--   $$D\,\mathrm{pr}_S(y)v=0\iff v\in\mathbb{R}y.$$
--
--   It is used to pass between immersions into the symplectization and into $S$ (Hryniewicz 2012, Section 7).
--
--   **Formalization Note** $\mathrm{pr}_S$ is `proj H`, whose value at $0$ is irrelevant here.
-- source:
--   General lemma; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.3

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- For `y ≠ 0`, the kernel of the derivative of `proj H` at `y` is the line spanned by `y`. -/
theorem fderiv_proj_eq_zero_iff {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (y : V n) (hy : y ≠ 0) (v : V n) :
    fderiv ℝ (proj H) y v = 0 ↔ ∃ c : ℝ, v = c • y := by
  sorry

end FiniteEnergyPlane
