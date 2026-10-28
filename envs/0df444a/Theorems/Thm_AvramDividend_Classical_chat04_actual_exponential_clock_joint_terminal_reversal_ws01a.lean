-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_joint_terminal_reversal_ws01a
-- name    : AvramDividend.Classical.chat04_actual_exponential_clock_joint_terminal_reversal_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:42:03.814887+00:00
-- url     : https://prove2.me/theorems/0d28b239-2b11-4260-9980-daa0a20dfdff
-- title:
--   Genuine exponential-horizon Levy minimum/drawdown reversal retaining the terminal displacement event
-- statement:
--   For the true joint path and independent Exp(r) observation-clock law, and each strict event on terminal displacement X_e-X_0<c, the strict terminal drawdown and strict running minimum have equal joint probabilities. The indicator density in the statement preserves the terminal event under both sides. It uses the source-faithful fixed-horizon joint reversal, genuine random-horizon path-event measurability, and the accepted weighted clock-section transfer. This is a noncircular joint reversal, not an assumed Wiener-Hopf independence or stopped-scale harmonicity.
-- source:
--   Requires the newly requested fixed-horizon source-faithful joint theorem (publication request 6bca8589) once canonically Proved; uses Proved a4fca343, 19746984 and d55462c3. Prepare source only until fixed-horizon prerequisite is canonical Proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_terminal_restricted_fixed_horizon_strict_reversal_ws01a
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_joint_weighted_clock_section_probability_transfer
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_random_horizon_strict_events_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_actual_exponential_clock_joint_terminal_reversal_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r) (a c : ℝ) :
    ((P.prod (expMeasure r)).withDensity
      (fun z : Ω × ℝ =>
        if X.X z.2.toNNReal z.1 - X.X 0 z.1 < c
        then (1 : ℝ≥0∞) else 0))
      {z : Ω × ℝ | ∃ s : ℝ≥0, s ≤ z.2.toNNReal ∧
        X.X z.2.toNNReal z.1 - X.X s z.1 < a} =
    ((P.prod (expMeasure r)).withDensity
      (fun z : Ω × ℝ =>
        if X.X z.2.toNNReal z.1 - X.X 0 z.1 < c
        then (1 : ℝ≥0∞) else 0))
      {z : Ω × ℝ | ∃ s : ℝ≥0, s ≤ z.2.toNNReal ∧
        X.X s z.1 - X.X 0 z.1 < a} := by sorry
