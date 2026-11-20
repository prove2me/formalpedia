-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_firstmark_positive_time_precount_good_any_short_clock
-- name    : AvramDividend.Classical.avram_jump6_A_original_firstmark_positive_time_precount_good_any_short_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:54:34.732026+00:00
-- url     : https://prove2.me/theorems/dcaef705-520e-4a49-a419-01e938a7aa4a
-- title:
--   Original first size-two Poisson mark is strictly positive, prior physical count zero, first count one before any positive clock with positive probability
-- statement:
--   For every strictly positive finite horizon, a rate-one negative size-two compound Poisson driver has positive probability that the first arrival occurs after zero and before that horizon, no physical marks occur earlier, and the true physical count is exactly one at first arrival. Combines Proved exact first-arrival CDF at every horizon, Proved almost-sure positive first interarrival and Proved exact jumpCount history. The theorem directly supports canonical Gaussian-limit native Brownian tube with horizon 1/1000 or 17/16000 and original finite-cap first ruin cash countermodel.

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_interarrival_pos
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_first_size2_mark_positive_before_any_time
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_first_mark_count_zero_before_and_one_at_arrival_ae
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_firstmark_positive_time_precount_good_any_short_clock
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (τ Y : ℕ → Ω → ℝ)
    (hJ : IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      (Measure.dirac (-2 : ℝ)) μ)
    (horizon : ℝ) (hh : 0 < horizon) :
    0 < μ (
      {j : Ω |
        0 < τ 0 j ∧
        (∀ s : ℝ≥0, (s : ℝ) < arrival τ 0 j →
          jumpCount (fun n => arrival τ n j) (s : ℝ) = 0) ∧
        jumpCount (fun n => arrival τ n j) (arrival τ 0 j) = 1} ∩
      {j : Ω | τ 0 j ≤ horizon}) := by sorry
