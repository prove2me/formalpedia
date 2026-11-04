-- Prove2me | Theorems.Thm_FiniteEnergyPlane_one_le_windInf_of_plane
-- name    : FiniteEnergyPlane.one_le_windInf_of_plane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T15:39:40.953218+00:00
-- url     : https://prove2.me/theorems/0f216c24-aaff-4a8d-898a-2a08de90b942
-- title:
--   Finite-energy planes have $\mathrm{wind}_\infty\ge1$
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $u$ be a finite-energy $\tilde J$-holomorphic plane whose puncture $\infty$ is nondegenerate (Hryniewicz, Definition 2.9) with asymptotic limit $P$. Then $\mathrm{wind}_\infty(u)$ is defined and at least $1$.
--
--   **Formalization Note** The hypothesis is `IsNondegenerateEnd H u cylInf P 1`; $P$ need not be nondegenerate.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Remark 3.20

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Remark 3.20: a finite-energy `J̃`-holomorphic plane whose puncture
`∞` is nondegenerate in the sense of Definition 2.9 has `wind_∞ ≥ 1`. -/
theorem one_le_windInf_of_plane (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (P : ReebOrbit H)
    (hnd : IsNondegenerateEnd H u cylInf P 1) :
    ∃ k : ℤ, 1 ≤ k ∧ HasWindInfAt H u cylInf 1 k := by
  sorry

end FiniteEnergyPlane
