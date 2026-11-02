-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isFastPlane_immersion_transverse
-- name    : FiniteEnergyPlane.isFastPlane_immersion_transverse
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-01T15:40:14.090705+00:00
-- url     : https://prove2.me/theorems/2168fd00-b652-4836-b57e-1470bce8eee3
-- title:
--   Fast planes project to immersions transverse to the Reeb field
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. If $u$ is a fast finite-energy plane, then $w=\mathrm{proj}\circ u:\mathbb{C}\to S$ is an immersion transverse to the Reeb field: for every $z$ and every nonzero $v\in\mathbb{C}$, $dw(z)v$ is not a real multiple of $R(w(z))$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Section 1

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), § 1: if `u` is a fast finite-energy plane, then `w = proj ∘ u :
ℂ → S` is an immersion transverse to the Reeb field: no nonzero tangent vector is mapped to a
multiple of `R`. -/
theorem isFastPlane_immersion_transverse (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hfast : IsFastPlane H J u) :
    ∀ z v : ℂ, v ≠ 0 → ∀ c : ℝ,
      fderiv ℝ (fun z => proj H (u z)) z v ≠ c • reeb H (proj H (u z)) := by
  sorry

end FiniteEnergyPlane
