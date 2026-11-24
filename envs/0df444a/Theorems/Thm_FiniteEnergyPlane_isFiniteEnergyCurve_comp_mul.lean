-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isFiniteEnergyCurve_comp_mul
-- name    : FiniteEnergyPlane.isFiniteEnergyCurve_comp_mul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-23T22:28:56.249142+00:00
-- url     : https://prove2.me/theorems/6651ec99-5562-4145-99b5-8632adc5cad6
-- title:
--   Complex scaling of the domain preserves finite-energy planes
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. If $u:\mathbb{C}\to\mathbb{R}^{2n+2}\setminus\{0\}$ is a finite-energy $\tilde J$-holomorphic plane and $A\in\mathbb{C}\setminus\{0\}$, then $z\mapsto u(Az)$ is a finite-energy $\tilde J$-holomorphic plane.
--
--   Used for reparametrizations of finite-energy planes by complex linear maps.
--
--   **Formalization Note** A plane is `IsFiniteEnergyCurve H J Set.univ u`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7.1

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- If `u` is a finite-energy `J̃`-holomorphic plane and `A ∈ ℂ` is nonzero, then `z ↦ u (A z)` is a
finite-energy `J̃`-holomorphic plane. -/
theorem isFiniteEnergyCurve_comp_mul {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (A : ℂ) (hA : A ≠ 0) :
    IsFiniteEnergyCurve H J Set.univ (fun z => u (A * z)) := by
  sorry

end FiniteEnergyPlane
