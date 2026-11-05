-- Prove2me | Theorems.Thm_FiniteEnergyPlane_proj_smul_aCoord_smul
-- name    : FiniteEnergyPlane.proj_smul_aCoord_smul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T19:50:31.130143+00:00
-- url     : https://prove2.me/theorems/3b475724-2948-49f7-8a38-4811a1bb9558
-- title:
--   Positive rescaling: projection invariant, $a$ shifted
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, with radial projection $\mathrm{proj}$ and symplectization coordinate $a$ (so $y=e^{2a(y)}\mathrm{proj}(y)$ for $y\neq0$). For $y\neq0$ and $c>0$,
--   $$\mathrm{proj}(cy)=\mathrm{proj}(y),\qquad a(cy)=a(y)+\tfrac12\log c.$$
--
--   This is the statement that dilations of $\mathbb{R}^{2n+2}\setminus\{0\}$ are the $\mathbb{R}$-translations of the symplectization $\mathbb{R}\times S$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, § 4 (supporting lemma for Lemma 4.16)

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- On a strictly star-shaped level, scaling `y ≠ 0` by `c > 0` leaves the radial projection
unchanged and shifts the symplectization coordinate by `log c / 2`. -/
theorem proj_smul_aCoord_smul {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (y : V n) (hy : y ≠ 0) (c : ℝ) (hc : 0 < c) :
    proj H (c • y) = proj H y ∧ aCoord H (c • y) = aCoord H y + Real.log c / 2 := by
  sorry

end FiniteEnergyPlane
