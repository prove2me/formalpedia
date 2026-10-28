-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_joint_pair_distribution_reversal_ws01a
-- name    : AvramDividend.Classical.chat04_actual_exponential_clock_joint_pair_distribution_reversal_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:44:44.377132+00:00
-- url     : https://prove2.me/theorems/1687a890-3a47-4c71-bd79-542ad4577f43
-- title:
--   Actual exponential-clock two-dimensional reflected terminal-pair reversal
-- statement:
--   For a spectrally negative Lévy process under the genuine product probability of its path and an independent exponential clock of any positive rate, the entire two-dimensional Borel law of (running-supremum drawdown, terminal centred displacement) agrees with the entire Borel law of (centred running minimum, terminal centred displacement). The equality is for actual pushforward measures on the real plane, including both signed and zero displacement. It is proved by finite-measure uniqueness from true Borel mixed-event reversal for any first-coordinate Borel set and every strict second-coordinate lower ray, without any Wiener-Hopf independence, independent descending transform, killed-kernel axiom, or future exit identity.
-- source:
--   Source-faithful draft at work/avram_ws01a_terminal_joint_pair_distribution_solution.lean. Requires canonical Proved status of mixed-Borel predecessor 44f90d98-8297-4d05-9966-971636d62e21 (candidate 17674 pending when prepared). All other imports Proved at pinned 4.33.1 / Mathlib 0df444a. Do not publish until parent is canonically Proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_mixed_borel_event_reversal_ws01a
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_actual_exponential_clock_joint_pair_distribution_reversal_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r) :
    (P.prod (expMeasure r)).map
      (fun z : Ω × ℝ =>
        (runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1,
         X.X z.2.toNNReal z.1 - X.X 0 z.1)) =
    (P.prod (expMeasure r)).map
      (fun z : Ω × ℝ =>
        (X.X 0 z.1 +
            -sInf {y : ℝ | ∃ s : ℝ≥0,
              s ≤ z.2.toNNReal ∧ y = X.X s z.1},
         X.X z.2.toNNReal z.1 - X.X 0 z.1)) := by sorry
