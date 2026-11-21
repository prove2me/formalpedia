-- Prove2me | Theorems.Thm_FiniteEnergyPlane_mul_abs_sub_le_norm_sub_of_exp_smul_eq
-- name    : FiniteEnergyPlane.mul_abs_sub_le_norm_sub_of_exp_smul_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T21:10:12.64827+00:00
-- url     : https://prove2.me/theorems/408d6ac0-7423-45fb-a32b-f790f1ad7f28
-- title:
--   Comparing two exponentially rescaled perturbations of a vector
-- statement:
--   Let $E$ be a real normed space, $\mu<0$, $m\in\mathbb{R}$, and $V_0,r_1,r_2\in E$ with $\|V_0\|\ge m$ and $\|r_1\|,\|r_2\|\le m/2$. If $s,s'\in\mathbb{R}$ satisfy
--   $$e^{\mu s}(V_0+r_1)=e^{\mu s'}(V_0+r_2),$$
--   then $-\mu\,|s-s'|\,\tfrac m2\le\|r_1-r_2\|$.
--
--   Role: a quantitative comparison of two exponentially rescaled perturbations of the same nonzero vector, for asymptotic formulas of the form $e^{\mu s}(v+r)$.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.22 / (100)

import Mathlib

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `μ < 0`, `‖V₀‖ ≥ m` and `‖r₁‖, ‖r₂‖ ≤ m / 2`. If
`e^{μs} (V₀ + r₁) = e^{μs'} (V₀ + r₂)`, then `-μ |s - s'| m / 2 ≤ ‖r₁ - r₂‖`. -/
theorem mul_abs_sub_le_norm_sub_of_exp_smul_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ m : ℝ} (hμ : μ < 0)
    {V₀ r₁ r₂ : E} (hm : m ≤ ‖V₀‖) (hr₁ : ‖r₁‖ ≤ m / 2) (hr₂ : ‖r₂‖ ≤ m / 2) :
    ∀ s s' : ℝ, Real.exp (μ * s) • (V₀ + r₁) = Real.exp (μ * s') • (V₀ + r₂) →
      (-μ) * |s - s'| * (m / 2) ≤ ‖r₁ - r₂‖ := by
  sorry

end FiniteEnergyPlane
