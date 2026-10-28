-- Prove2me | Theorems.Thm_AvramDividend_Classical_stoppingTime_capped_history_event_measurable
-- name    : AvramDividend.Classical.stoppingTime_capped_history_event_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:31:14.567417+00:00
-- url     : https://prove2.me/theorems/ad853cca-14cf-48e8-9fc8-3905a27e2c76
-- title:
--   Stopped-history event restricted to a finite time cap is measurable at the capped stopping time
-- statement:
--   For any stopping time and any measurable stopped-history event A, the intersection of A with the event that the original clock has occurred by a finite horizon N belongs to the stopped sigma-algebra of the capped stopping time min(T,N). This is the essential finite-horizon event localisation in the strong-Markov first-record renewal argument.
-- source:
--   Mathlib Probability Process Stopping, IsStoppingTime.measurableSet_min_const_iff and measurableSet_le'.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stoppingTime_capped_history_event_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0∞}
    (hτ : IsStoppingTime 𝓕 τ) (A : Set Ω)
    (hA : MeasurableSet[hτ.measurableSpace] A) (N : ℝ≥0) :
    MeasurableSet[(hτ.min_const N).measurableSpace]
      (A ∩ {ω : Ω | τ ω ≤ (N : ℝ≥0∞)}) := by sorry
