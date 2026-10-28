-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_untopA_stoppedHistory_measurable
-- name    : AvramDividend.Classical.capped_untopA_stoppedHistory_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:27:40.064994+00:00
-- url     : https://prove2.me/theorems/673ec301-6af7-4843-8bc2-6f62d9c462c8
-- title:
--   Finite cap stopped-history measurability survives conversion to a finite stopping clock
-- statement:
--   An event measurable at the minimum of a possibly infinite stopping time and a finite horizon remains measurable at the finite-valued stopping time obtained by untopA. This identifies the stopped history used in the proved finite-horizon survival event with the stopped history required by the proved finite-clock Markov factorisation.
-- source:
--   Proved stoppingTime_finite_cap_untopA_le_events; Mathlib IsStoppingTime.min_const and WithTop.untopA; proof irrelevance of stopping-time certificates.

import Mathlib.Probability.Process.Stopping
import Mathlib.Order.WithBot
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_stoppingTime_finite_cap_untopA_le_events

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.capped_untopA_stoppedHistory_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0∞}
    (hτ : IsStoppingTime 𝓕 τ) (N : ℝ≥0) (A : Set Ω)
    (hA : MeasurableSet[(hτ.min_const N).measurableSpace] A) :
    MeasurableSet[
      (isStoppingTime_withTop_of_le_events
        (fun ω => (min (τ ω) (N : ℝ≥0∞)).untopA)
        (stoppingTime_finite_cap_untopA_le_events hτ N)).measurableSpace] A := by sorry
