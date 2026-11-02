-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isFastPlane_iff_hasWindInfAt_one
-- name    : FiniteEnergyPlane.isFastPlane_iff_hasWindInfAt_one
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-01T15:40:00.560751+00:00
-- url     : https://prove2.me/theorems/c505e592-51da-4c29-bad9-1f319d94cb08
-- title:
--   Fast planes are the planes with $\mathrm{wind}_\infty=1$
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $u$ be a finite-energy $\tilde J$-holomorphic plane whose puncture $\infty$ is nondegenerate (Hryniewicz, Definition 2.9) with a prime asymptotic limit $P$. Then $u$ is fast if and only if $\mathrm{wind}_\infty(u)=1$.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Definition 2.14; U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Section 1

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz, Definition 2.14 and Hryniewicz (Trans. AMS 2012), § 1: a finite-energy
`J̃`-holomorphic plane whose puncture `∞` is nondegenerate with a prime asymptotic limit `P` is fast
if and only if `wind_∞ = 1`. -/
theorem isFastPlane_iff_hasWindInfAt_one (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (P : ReebOrbit H) (hP : P.IsPrime)
    (hnd : IsNondegenerateEnd H u cylInf P 1) :
    IsFastPlane H J u ↔ HasWindInfAt H u cylInf 1 1 := by
  sorry

end FiniteEnergyPlane
