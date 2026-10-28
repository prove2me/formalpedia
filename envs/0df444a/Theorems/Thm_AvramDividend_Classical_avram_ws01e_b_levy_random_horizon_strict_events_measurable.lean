-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_random_horizon_strict_events_measurable
-- name    : AvramDividend.Classical.avram_ws01e_b_levy_random_horizon_strict_events_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T07:37:44.669714+00:00
-- url     : https://prove2.me/theorems/19746984-73d9-4626-8cad-22ff858602dd
-- title:
--   Joint measurable random-horizon Lévy terminal drawdown and running-minimum strict events
-- statement:
--   For a genuine spectrally negative Lévy process and any independently sampled measurable nonnegative observation horizon e, the events that the terminal level falls strictly below an earlier running path level by threshold a, or that some running level lies strictly below its initial level by a, are both measurable on the joint path-clock space. Apply the Proved general right-continuous strict random-horizon event measurability theorem to f(s,ω)=−X_s(ω) with random threshold a−X_e(ω), and to f(s,ω)=X_s(ω)−X_0(ω) with constant a. Source-specific joint Lévy path measurability and path right-continuity are Proved.
-- source:
--   Canonically Proved joint_random_horizon_strict_event_measurable (d4aacb50) and chat04_levy_joint_time_state_measurable (d55462c3).

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_joint_random_horizon_strict_event_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_levy_random_horizon_strict_events_measurable
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Θ]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (e : Θ → ℝ≥0) (he : Measurable e) (a : ℝ) :
    MeasurableSet {z : Ω × Θ |
      ∃ s : ℝ≥0, s ≤ e z.2 ∧
        X.X (e z.2) z.1 - X.X s z.1 < a} ∧
    MeasurableSet {z : Ω × Θ |
      ∃ s : ℝ≥0, s ≤ e z.2 ∧
        X.X s z.1 - X.X 0 z.1 < a} := by sorry
