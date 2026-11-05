-- Prove2me | Theorems.Thm_FiniteEnergyPlane_ofReal_loopAction_ccwLoop_le_energy
-- name    : FiniteEnergyPlane.ofReal_loopAction_ccwLoop_le_energy
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T17:09:29.537692+00:00
-- url     : https://prove2.me/theorems/99b65e99-6f9c-4d1a-b86d-e781ac12315b
-- title:
--   Actions of circles are bounded by the Hofer energy on the punctured plane
-- statement:
--   Let $u$ be a finite-energy $\tilde J$-holomorphic curve on $\mathbb{C}\setminus\{0\}$ with $a(u(z))\to-\infty$ as $z\to0$. Then for every $\rho>0$ the action of the counterclockwise loop $t\mapsto\mathrm{proj}(u(\rho e^{2\pi it}))$ is at most the Hofer energy of $u$ on $\mathbb{C}\setminus\{0\}$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, Lemma 4.11; H. Hofer, K. Wysocki, E. Zehnder, Finite energy cylinders of small area, Ergodic Theory Dynam. Systems 22 (2002), 1451-1486, Theorem 1.1

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Actions are bounded by the Hofer energy. Let `u` be a finite-energy `J̃`-holomorphic curve on
`ℂ \ {0}` with `a(u(z)) → -∞` as `z → 0`. Then for every `ρ > 0` the action of the counterclockwise
circle of radius `ρ` is at most the Hofer energy of `u` on `ℂ \ {0}`. -/
theorem ofReal_loopAction_ccwLoop_le_energy {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J {z | z ≠ 0} u)
    (hneg : Tendsto (fun z => aCoord H (u z)) (𝓝[≠] 0) atBot) (ρ : ℝ) (hρ : 0 < ρ) :
    ENNReal.ofReal (loopAction H u (ccwLoop ρ)) ≤ energy H {z | z ≠ 0} u := by
  sorry

end FiniteEnergyPlane
