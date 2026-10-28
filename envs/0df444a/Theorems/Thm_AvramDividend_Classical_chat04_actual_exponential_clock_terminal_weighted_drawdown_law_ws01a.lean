-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_terminal_weighted_drawdown_law_ws01a
-- name    : AvramDividend.Classical.chat04_actual_exponential_clock_terminal_weighted_drawdown_law_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:08:48.270412+00:00
-- url     : https://prove2.me/theorems/1e4c8fdb-8179-4628-8eab-61c714b31dc9
-- title:
--   Actual exponential-clock terminal-conditioned drawdown and centred-minimum finite measure laws coincide
-- statement:
--   For a genuine spectrally negative Levy law observed under its independent Exp(r) path-clock probability, conditioning by any strict terminal displacement event X_e-X_0<c gives equal finite Borel measure pushforwards of the true terminal drawdown S_e-X_e and the centred running lower excursion X_0-inf_{s<=e}X_s. The equality holds for every Borel set, not just thresholds, and retains potential atoms and the clock at zero. It follows from the independently Proved true joint terminal-threshold reversal and finite real-measure extensionality, without Wiener-Hopf independence, a killed kernel, or the eventual exit identity.
-- source:
--   Source-faithful consequence of Proved genuine exponential clock joint threshold theorem 0d28b239-2b11-4260-9980-daa0a20dfdff, genuine extrema measurability 4390c2cb-aaa7-49a6-bafb-5492d3fc9555, strict runningSup crossing 2c2a5cce-5625-4740-a1c8-6126816bd4f1, strict lower infimum bridge 3e4d270c-91ab-4d60-b667-a12cdfb32a5f and pinned Mathlib Measure.ext_of_Iic.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_joint_terminal_reversal_ws01a
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_gt_level_iff_prior_strict_path_hit
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_actual_exponential_clock_terminal_weighted_drawdown_law_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r) (c : ℝ) :
    (((P.prod (expMeasure r)).withDensity
      (fun z : Ω × ℝ =>
        if X.X z.2.toNNReal z.1 - X.X 0 z.1 < c
        then (1 : ℝ≥0∞) else 0)).map
      (fun z : Ω × ℝ =>
        runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1)) =
    (((P.prod (expMeasure r)).withDensity
      (fun z : Ω × ℝ =>
        if X.X z.2.toNNReal z.1 - X.X 0 z.1 < c
        then (1 : ℝ≥0∞) else 0)).map
      (fun z : Ω × ℝ =>
        X.X 0 z.1 +
          -sInf {y : ℝ | ∃ s : ℝ≥0,
            s ≤ z.2.toNNReal ∧ y = X.X s z.1})) := by sorry
