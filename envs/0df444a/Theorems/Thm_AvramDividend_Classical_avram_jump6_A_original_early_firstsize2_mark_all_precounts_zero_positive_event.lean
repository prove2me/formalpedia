-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_early_firstsize2_mark_all_precounts_zero_positive_event
-- name    : AvramDividend.Classical.avram_jump6_A_original_early_firstsize2_mark_all_precounts_zero_positive_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:51:36.343213+00:00
-- url     : https://prove2.me/theorems/382e7e0b-0f6f-4297-8076-cc10347a9a3b
-- title:
--   Original strictly positive early first size-two jump event with no prior physical marks and one mark at first arrival
-- statement:
--   The original rate-one size-two compound Poisson driver has a strictly positive probability event on which its first physical arrival time lies in (0,1/500], its actual jump count is zero at every earlier time, and exactly one at first arrival. This follows directly from the already-Proved early strict-first-mark positive event and the almost-sure true jumpCount prepath/source theorem, through restricted measure AE intersection. This is the non-synthetic physical Poisson half of the original Brownian–Poisson positive first-ruin event required by aef35b4c and the strict unit-fullmark signed cash contradiction.

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_first_mark_count_zero_before_and_one_at_arrival_ae
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_rateone_size2_first_mark_strictly_positive_and_early_event
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_early_firstsize2_mark_all_precounts_zero_positive_event
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (τ Y : ℕ → Ω → ℝ)
    (hJ : IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      (Measure.dirac (-2 : ℝ)) μ) :
    0 < μ (
      {ω : Ω |
        (∀ t : ℝ≥0, (t : ℝ) < arrival τ 0 ω →
          jumpCount (fun n => arrival τ n ω) (t : ℝ) = 0) ∧
        jumpCount (fun n => arrival τ n ω) (arrival τ 0 ω) = 1} ∩
      {ω : Ω | 0 < τ 0 ω ∧ τ 0 ω ≤ (1 / 500 : ℝ)}) := by sorry
