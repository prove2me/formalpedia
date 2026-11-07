-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_mul_abs_sub_le_norm_sub_of_isPrime
-- name    : FiniteEnergyPlane.exists_mul_abs_sub_le_norm_sub_of_isPrime
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T16:39:44.22669+00:00
-- url     : https://prove2.me/theorems/c4248a53-418f-4e01-b144-3067eebeb76c
-- title:
--   Lower Lipschitz bound along a prime Reeb orbit
-- statement:
--   Let $P = (x, T)$ be a prime periodic Reeb orbit on a strictly star-shaped level. Then there is $c > 0$ with $c |\tau - \tau'| \le \|x(\tau) - x(\tau')\|$ whenever $|\tau - \tau'| \le T/2$.
--
--   **Role.** A prime orbit is a uniformly embedded circle.
-- source:
--   Elementary lemma in the setting of U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- On a prime periodic Reeb orbit, `‖x(τ) - x(τ')‖` is bounded below by a multiple of `|τ - τ'|`
whenever `|τ - τ'| ≤ T / 2`. -/
theorem exists_mul_abs_sub_le_norm_sub_of_isPrime {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (hP : P.IsPrime) :
    ∃ c > 0, ∀ τ τ' : ℝ, |τ - τ'| ≤ P.T / 2 → c * |τ - τ'| ≤ ‖P.x τ - P.x τ'‖ := by
  sorry

end FiniteEnergyPlane
