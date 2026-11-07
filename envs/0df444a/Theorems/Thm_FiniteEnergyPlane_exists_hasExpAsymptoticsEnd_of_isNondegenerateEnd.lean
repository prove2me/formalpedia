-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_hasExpAsymptoticsEnd_of_isNondegenerateEnd
-- name    : FiniteEnergyPlane.exists_hasExpAsymptoticsEnd_of_isNondegenerateEnd
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T16:36:09.700507+00:00
-- url     : https://prove2.me/theorems/aae9b663-d14f-410d-a598-845ef634c11a
-- title:
--   Exponential convergence in all derivatives at the puncture at infinity of a plane
-- statement:
--   Let $u$ be a finite-energy $\tilde J$-holomorphic plane with a nondegenerate positive puncture at $\infty$ over a periodic Reeb orbit $P$ in the sense of Hryniewicz, Definition 2.9 (so $P$ itself is not assumed nondegenerate). Then, in the cylindrical coordinates $\mathtt{cylInf}$ at $\infty$, $u$ converges to the trivial cylinder over $P$ exponentially fast in $C^\infty$.
--
--   **Role.** Upgrades the $C^0$ hypothesis of Definition 2.9 to $C^\infty$ control on the end of a plane, for possibly degenerate orbits.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, used with Lemmas 6.10 and 6.20

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A finite-energy plane with a nondegenerate positive puncture at `∞` over a Reeb orbit `P` (not
assumed nondegenerate) converges to the trivial cylinder over `P` exponentially fast in `C^∞`. -/
theorem exists_hasExpAsymptoticsEnd_of_isNondegenerateEnd {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u)
    (P : ReebOrbit H) (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ b > 0, HasExpAsymptoticsEnd H u cylInf P 1 b := by
  sorry

end FiniteEnergyPlane
