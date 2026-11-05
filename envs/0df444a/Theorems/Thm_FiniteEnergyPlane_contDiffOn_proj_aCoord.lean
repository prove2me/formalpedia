-- Prove2me | Theorems.Thm_FiniteEnergyPlane_contDiffOn_proj_aCoord
-- name    : FiniteEnergyPlane.contDiffOn_proj_aCoord
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T19:50:23.182803+00:00
-- url     : https://prove2.me/theorems/d7c1d9e4-2674-4de3-8338-8647b077083f
-- title:
--   Smoothness of the radial projection and the $a$-coordinate
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level: $H$ is smooth, every ray from the origin meets $S$ exactly once, and $dH_x(x)>0$ for $x\in S$. For $y\neq0$ let $r(y)>0$ be the unique scalar with $H(r(y)y)=1$, and put $\mathrm{proj}(y)=r(y)\,y\in S$ and $a(y)=-\tfrac12\log r(y)$, so that $y=e^{2a(y)}\mathrm{proj}(y)$. Then $\mathrm{proj}$ and $a$ are $C^\infty$ on $\mathbb{R}^{2n+2}\setminus\{0\}$.
--
--   This is the smoothness of the identification $\mathbb{R}^{2n+2}\setminus\{0\}\cong\mathbb{R}\times S$ of the symplectization.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, § 4 (supporting lemma for Lemma 4.16)

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- On a strictly star-shaped level `S = H⁻¹(1)`, the radial projection `proj H` and the
symplectization coordinate `aCoord H` are `C^∞` on `V n \ {0}`. -/
theorem contDiffOn_proj_aCoord {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) :
    ContDiffOn ℝ ∞ (proj H) {0}ᶜ ∧ ContDiffOn ℝ ∞ (aCoord H) {0}ᶜ := by
  sorry

end FiniteEnergyPlane
