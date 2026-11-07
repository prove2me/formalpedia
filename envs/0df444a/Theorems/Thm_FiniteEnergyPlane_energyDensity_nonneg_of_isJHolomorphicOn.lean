-- Prove2me | Theorems.Thm_FiniteEnergyPlane_energyDensity_nonneg_of_isJHolomorphicOn
-- name    : FiniteEnergyPlane.energyDensity_nonneg_of_isJHolomorphicOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T17:14:18.767219+00:00
-- url     : https://prove2.me/theorems/cbd380de-cd50-4a9e-9ff8-9dc6c9391aeb
-- title:
--   Pointwise nonnegativity of the energy integrands of a J-holomorphic map, without an energy assumption
-- statement:
--   Let $S = H^{-1}(1)$ be a strictly star-shaped level in $V_n$, $J$ a compatible complex structure on $\xi$, and $\tilde J$ the symplectization structure on $V_n \setminus \{0\}$. Let $U \subseteq \mathbb{C}$ and let $u$ avoid $0$ and be $\tilde J$-holomorphic on $U$, with no assumption on its energy. Then for every admissible $\varphi$ (smooth, nondecreasing, values in $[0,1]$) and every $z \in U$, the integrand of $u^* d(\varphi(a)\lambda)$ and the integrand of $u^* d\lambda$ are nonnegative at $z$.
--
--   This removes the finite-energy hypothesis from the pointwise part of `energyDensity_nonneg`, so it can be used to establish that a map has finite energy.
-- source:
--   H. Hofer, Invent. Math. 114 (1993), (42); U. Hryniewicz, J. Symplectic Geom. 12 (2014), § 2.2.1

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Pointwise nonnegativity of the energy integrands of a `J̃`-holomorphic map, with no assumption
on its energy. Let `u` avoid `0` and be `J̃`-holomorphic on `U`. For every admissible `φ` and every
`z ∈ U`, the integrand of `u*d(φ(a) λ)` and the integrand of `u*dλ` are nonnegative at `z`. -/
theorem energyDensity_nonneg_of_isJHolomorphicOn {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (u : ℂ → V n) (hu0 : ∀ z ∈ U, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u) (φ : ℝ → ℝ) (hφ : Admissible φ)
    {z : ℂ} (hz : z ∈ U) :
    0 ≤ energyDensity H φ u z ∧ 0 ≤ dlambdaDensity H u z := by
  sorry

end FiniteEnergyPlane
