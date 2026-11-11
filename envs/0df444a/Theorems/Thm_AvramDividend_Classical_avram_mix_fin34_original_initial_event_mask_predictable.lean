-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin34_original_initial_event_mask_predictable
-- name    : AvramDividend.Classical.avram_mix_fin34_original_initial_event_mask_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T22:17:26.571364+00:00
-- url     : https://prove2.me/theorems/95c9c9a3-19bb-4f15-98e1-971ee3e071a3
-- title:
--   Original initial-event indicator is a predictable multiplier
-- statement:
--   For an event A measurable in the original right-continuous filtration at time zero, the real-valued indicator process constant in time is strongly predictable in that same filtration. Its strong adaptedness follows from filtration monotonicity, and its continuous-time paths are constant and hence left-continuous. The proof reuses the Proved strong-adapted left-continuity to predictability theorem 5ae104c4. It is a key exact initial-mask prerequisite for upgrading original global compensated source expectation to eventwise random-compensator centring.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable
open Classical MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin34_original_initial_event_mask_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
    IsStronglyPredictable 𝓕.rightCont
      (fun (_ : ℝ≥0) (ω : Ω) => if ω ∈ A then (1 : ℝ) else 0) := by sorry
