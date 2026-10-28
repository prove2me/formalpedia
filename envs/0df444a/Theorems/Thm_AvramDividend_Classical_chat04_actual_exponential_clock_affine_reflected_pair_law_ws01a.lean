-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_affine_reflected_pair_law_ws01a
-- name    : AvramDividend.Classical.chat04_actual_exponential_clock_affine_reflected_pair_law_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:57:45.513319+00:00
-- url     : https://prove2.me/theorems/c569cf34-8b78-477d-a123-4b6aa63cf951
-- title:
--   Actual exponential-clock centred supremum-drawdown and overshoot-infimum pair law
-- statement:
--   At a genuine independent positive-rate exponential clock, the full two-dimensional Borel pushforward law of the centred running supremum and terminal drawdown equals that of terminal reflected overshoot and the centred running infimum excursion, for any spectrally negative Lévy process. This is the affine transformation (d,z)→(d+z,d) of the genuinely proved joint reversal of (drawdown, terminal displacement) versus (downward excursion, terminal displacement). It is a full actual distribution law, a reusable bridge for applying an independently proved original-clock Wiener–Hopf independence, and does not assert independence itself.
-- source:
--   Source-faithful 91-line no-sorry Lean draft work/avram_ws01a_actual_affine_reflected_pair_solution.lean. Requires the direct two-dimensional actual-clock joint law 1687a890-3a47-4c71-bd79-542ad4577f43 to become canonically Proved; it was Open with candidate 17677 pending when this draft was prepared. Do not author or submit before that dependency is Proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_joint_pair_distribution_reversal_ws01a
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_actual_exponential_clock_affine_reflected_pair_law_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r) :
    (P.prod (expMeasure r)).map
      (fun z : Ω × ℝ =>
        (runningSup X z.2.toNNReal z.1 - X.X 0 z.1,
         runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1)) =
    (P.prod (expMeasure r)).map
      (fun z : Ω × ℝ =>
        (X.X z.2.toNNReal z.1 +
            -sInf {y : ℝ | ∃ s : ℝ≥0,
              s ≤ z.2.toNNReal ∧ y = X.X s z.1},
         X.X 0 z.1 +
            -sInf {y : ℝ | ∃ s : ℝ≥0,
              s ≤ z.2.toNNReal ∧ y = X.X s z.1})) := by sorry
