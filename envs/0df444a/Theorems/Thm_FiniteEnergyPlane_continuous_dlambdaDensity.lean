-- Prove2me | Theorems.Thm_FiniteEnergyPlane_continuous_dlambdaDensity
-- name    : FiniteEnergyPlane.continuous_dlambdaDensity
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-23T21:35:57.918267+00:00
-- url     : https://prove2.me/theorems/f2cfa4c4-6b74-4459-ac03-d3cf278d6cf0
-- title:
--   The dlambda-density of a finite-energy plane is continuous
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be strictly star-shaped, $J$ a family of endomorphisms, and $u:\mathbb{C}\to\mathbb{R}^{2n+2}\setminus\{0\}$ a finite-energy plane with $S$-component $w$. Then the integrand $z\mapsto\omega_0(\partial_sw(z),\partial_tw(z))$ of $\int u^*d\lambda$ is continuous on $\mathbb{C}$.
--
--   It is used for estimates of the $d\lambda$-energy on discs (Hryniewicz 2012, Lemma 7.3).
--
--   **Formalization Note** The integrand is `dlambdaDensity H u`; the plane is `IsFiniteEnergyCurve H J Set.univ u`. No condition on `J` is needed.
-- source:
--   General lemma; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.3

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The integrand of the `dλ`-energy of a finite-energy plane is continuous. -/
theorem continuous_dlambdaDensity {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u) :
    Continuous (dlambdaDensity H u) := by
  sorry

end FiniteEnergyPlane
