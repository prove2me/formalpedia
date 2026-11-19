-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_ennreal_discounted_cash_finite_grid_sum_toReal
-- name    : AvramDividend.Classical.avram_jump6_B_original_ennreal_discounted_cash_finite_grid_sum_toReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:39:39.031554+00:00
-- url     : https://prove2.me/theorems/3c67afb7-472d-4938-84a6-536984ad7f81
-- title:
--   Convert finite original discounted Stieltjes cash products from ENNReal sum to real signed sum
-- statement:
--   An exact finite-cell identity for the source paid cash: nonnegative discounted cell weights and nonnegative postpayment potential drops have ENNReal.ofReal products summing to a finite quantity whose toReal equals the real sum of weighted drops. It is needed to turn the genuine original paymentTimes closed-Iic ENNReal grid upper bound into a signed real source inequality; does not change reserve process, cap or compensated jump assumptions.

import Mathlib
open MeasureTheory
open scoped ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_ennreal_discounted_cash_finite_grid_sum_toReal
    {ι : Type*} (S : Finset ι) (E H : ι → ℝ)
    (hE : ∀ i ∈ S, 0 ≤ E i) (hH : ∀ i ∈ S, 0 ≤ H i) :
    (∑ i ∈ S, ENNReal.ofReal (E i) * ENNReal.ofReal (H i)).toReal =
      ∑ i ∈ S, E i * H i := by sorry
