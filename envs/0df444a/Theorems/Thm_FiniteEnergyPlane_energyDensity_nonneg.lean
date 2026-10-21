-- Prove2me | Theorems.Thm_FiniteEnergyPlane_energyDensity_nonneg
-- name    : FiniteEnergyPlane.energyDensity_nonneg
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T23:23:07.965647+00:00
-- url     : https://prove2.me/theorems/34f14c55-b370-4ad0-905e-2b963b65b05d
-- title:
--   Nonnegativity of the energy densities of finite-energy curves
-- statement:
--   Let $S=H^{-1}(1)$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, $U\subseteq\mathbb{C}$ open and $u$ a finite-energy $\tilde J$-holomorphic curve on $U$. Then:
--   1. for every $\varphi\in\Sigma$, the integrand of $u^*d(\varphi(a)\lambda_0)$ is $\ge0$ at every point of $U$;
--   2. the integrand $\omega_0(\partial_sw,\partial_tw)$ of $u^*d\lambda_0$ is $\ge0$ on $U$;
--   3. $\int_Uu^*d\lambda_0\le E(u)$;
--   4. if $U$ is connected and $E(u)=0$, then $u$ is constant on $U$.
--
--   **Formalization Note** Connectedness is `IsPreconnected U`. Both energies are lower integrals in `ℝ≥0∞`.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2.1 and (17), p. 12; H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, (42), p. 535

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz 2014, § 2.2.1 and (17); Hofer 1993, (42). For a finite-energy `J̃`-holomorphic
curve on an open set `U ⊆ ℂ`, the integrand of `u*d(φ(a) λ)` is nonnegative for every admissible
`φ`, so is the integrand of `u*dλ`, and the `dλ`-energy is at most the Hofer energy. If `U` is
preconnected and the Hofer energy vanishes, `u` is constant on `U`. -/
theorem energyDensity_nonneg {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J U u) :
    (∀ φ : ℝ → ℝ, Admissible φ → ∀ z ∈ U, 0 ≤ energyDensity H φ u z) ∧
      (∀ z ∈ U, 0 ≤ dlambdaDensity H u z) ∧ dlambdaEnergy H U u ≤ energy H U u ∧
      (IsPreconnected U → energy H U u = 0 → ∃ c : V n, ∀ z ∈ U, u z = c) := by
  sorry

end FiniteEnergyPlane
