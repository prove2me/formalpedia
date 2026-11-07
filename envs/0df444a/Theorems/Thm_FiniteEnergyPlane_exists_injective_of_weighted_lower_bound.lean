-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_injective_of_weighted_lower_bound
-- name    : FiniteEnergyPlane.exists_injective_of_weighted_lower_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T16:36:29.366042+00:00
-- url     : https://prove2.me/theorems/eabe0277-f866-4eac-9ee4-27d29c628055
-- title:
--   Injective immersions from a weighted lower bound and weighted closeness
-- statement:
--   For every $c > 0$ there is $\varepsilon > 0$ with the following property. Let $E$ be a real normed space and let $A, B : \mathbb{C} \to E$ be differentiable. Suppose $c \|z - z'\| \le (1 + \|z\| + \|z'\|) \|B(z) - B(z')\|$ for all $z, z'$, and $\|A(z) - B(z)\| \le \varepsilon$ and $(1 + \|z\|) \|DA(z) - DB(z)\| \le \varepsilon$ for all $z$. Then $A$ is injective and $DA(z)$ is injective for every $z$.
--
--   **Role.** The weight $1 + \|z\|$ is the scale of cylindrical coordinates at $\infty$, so this compares maps on the plane uniformly up to infinity.
-- source:
--   Elementary lemma in the setting of U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076

import Mathlib

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `B : ℂ → E` satisfy `c ‖z - z'‖ ≤ (1 + ‖z‖ + ‖z'‖) ‖B z - B z'‖` for all `z, z'`. Then there
is `ε > 0` such that every differentiable `A` with `‖A z - B z‖ ≤ ε` and
`(1 + ‖z‖) ‖DA(z) - DB(z)‖ ≤ ε` for all `z` is injective with injective derivative everywhere. -/
theorem exists_injective_of_weighted_lower_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : ℝ) (hc : 0 < c) :
    ∃ ε > 0, ∀ A B : ℂ → E, Differentiable ℝ A → Differentiable ℝ B →
      (∀ z z', c * ‖z - z'‖ ≤ (1 + ‖z‖ + ‖z'‖) * ‖B z - B z'‖) →
      (∀ z, ‖A z - B z‖ ≤ ε) →
      (∀ z, (1 + ‖z‖) * ‖fderiv ℝ A z - fderiv ℝ B z‖ ≤ ε) →
      Function.Injective A ∧ ∀ z, Function.Injective (fderiv ℝ A z) := by
  sorry

end FiniteEnergyPlane
