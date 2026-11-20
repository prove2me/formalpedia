-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_rateone_size2_count_one_at_first_mark
-- name    : AvramDividend.Classical.avram_jump6_A_original_rateone_size2_count_one_at_first_mark
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:47:50.176184+00:00
-- url     : https://prove2.me/theorems/24aea451-62e8-4cf1-9f8b-d969f7704ee8
-- title:
--   Actual rate-one marked Poisson jump count equals one at its first arrival, almost surely
-- statement:
--   For the actual rate-one size-two compound Poisson driver, its physical arrival clock is strictly increasing almost surely. Because jumpCount is the infimum of indices whose arrival exceeds the observed time, its value at the first arrival τ0 is exactly one. This is the necessary original physical count identity for the ruin-causing negative two first marked jump, supplementing existing Proved negative-two compoundPoisson equals -2 times jumpCount and normal Gaussian source equality.

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_rateone_size2_count_one_at_first_mark
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (τ Y : ℕ → Ω → ℝ)
    (hJ : IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      (Measure.dirac (-2 : ℝ)) μ) :
    ∀ᵐ ω ∂μ, jumpCount (fun n => arrival τ n ω) (arrival τ 0 ω) = 1 := by sorry
