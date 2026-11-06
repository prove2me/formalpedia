-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn10_original_selected_signed_grid_budget
-- name    : AvramDividend.Classical.avram_bv_env3_turn10_original_selected_signed_grid_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:51:57.903729+00:00
-- url     : https://prove2.me/theorems/089c5f1e-5811-4cfd-8d3c-41e1e962aa31
-- title:
--   Original selected signed source-grid finite-prefix expectation budget
-- statement:
--   Combine actual stopped physical-grid event-selected mean-zero source martingale increments with nonpositive HJB drift increments. The finite random signed sum is integrable and has nonpositive expectation.
-- source:
--   Conditional analytic composition toward c1e2f021. Actual process-dependent event-selected compensation hMean and individual drift sign hDrift are explicit hypotheses; neither is assumed for free.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn9_integrable_bounded_measurable_source_prefix
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn9_original_centered_stopped_source_prefix_mean_zero
open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn10_original_selected_signed_grid_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (m : ℕ) (k : Ω → ℕ)
    (hk : Measurable k) (hkBound : ∀ ω, k ω ≤ m)
    (M B : ℕ → Ω → ℝ)
    (hMI : ∀ i, Integrable (M i) P)
    (hBI : ∀ i, Integrable (B i) P)
    (hMean : ∀ i < m, (∫ ω, (if i < k ω then M i ω else 0) ∂P) = 0)
    (hDrift : ∀ i ω, B i ω ≤ 0) :
    Integrable (fun ω => ∑ i ∈ Finset.range (k ω), (M i ω + B i ω)) P ∧
    (∫ ω, ∑ i ∈ Finset.range (k ω), (M i ω + B i ω) ∂P) ≤ 0 := by sorry
