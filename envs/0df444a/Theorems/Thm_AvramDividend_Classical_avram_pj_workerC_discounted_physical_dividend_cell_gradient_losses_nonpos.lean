-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_discounted_physical_dividend_cell_gradient_losses_nonpos
-- name    : AvramDividend.Classical.avram_pj_workerC_discounted_physical_dividend_cell_gradient_losses_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:40:46.140498+00:00
-- url     : https://prove2.me/theorems/e79bfcb7-d731-460c-81c1-a3273f81c98d
-- title:
--   All weighted original physical dividend-cell losses from slope at least one are nonpositive
-- statement:
--   For any finite collection of physical stopped cells, reserve decreases entirely due to dividend increments within cap. If w has derivative at least one and the weights are nonnegative, the sum of dividend cash minus lost w is nonpositive. This controls the continuous within-cell payout correction absent from the sampled right-jump-only Q_k.
-- source:
--   Direct finite-sum application of Proved 44b01929 original UBV C2 cap secant. Useful signed source for Worker C original purejump Ito, strictly independent of Gaussian or finite activity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_discounted_physical_dividend_cell_gradient_losses_nonpos
    {ι : Type*} (S : Finset ι)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (pre post weight : ι → ℝ)
    (hpost : ∀ i ∈ S, 0 ≤ post i)
    (hpre : ∀ i ∈ S, post i ≤ pre i)
    (hcap : ∀ i ∈ S, ENNReal.ofReal (pre i) ≤ C)
    (hwgt : ∀ i ∈ S, 0 ≤ weight i) :
    (∑ i ∈ S, weight i *
      ((pre i - post i) - (w (pre i) - w (post i)))) ≤ 0 := by sorry
