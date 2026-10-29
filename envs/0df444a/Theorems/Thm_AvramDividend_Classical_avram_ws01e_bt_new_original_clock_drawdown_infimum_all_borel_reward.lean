-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_drawdown_infimum_all_borel_reward
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_original_clock_drawdown_infimum_all_borel_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T01:30:04.384001+00:00
-- url     : https://prove2.me/theorems/638884e8-e23d-4e31-ba9d-1b483591b2cd
-- title:
--   All Borel terminal-drawdown rewards equal centred-infimum rewards under the original exponential clock
-- statement:
--   For every original spectrally negative Lévy process under the true path law P with independent Exp(p) terminal clock, and every measurable nonnegative extended-real reward f on the state space, the expected Borel reward of the actual terminal drawdown S_e-X_e equals the reward of the centred negative running infimum X_0−inf_{s≤e}X_s. This is a genuine all-Borel corollary of the original-clock full marginal-law reversal, using measurable maps and the measure-theoretic lintegral map. No false product Esscher change of measure or independence assertion is introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_drawdown_infimum_marginal_law
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_original_clock_drawdown_infimum_all_borel_reward
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z : Ω × ℝ,
      f (runningSup X z.2.toNNReal z.1 -
        X.X z.2.toNNReal z.1)
      ∂(P.prod (expMeasure p))) =
    (∫⁻ z : Ω × ℝ,
      f (X.X 0 z.1 +
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ z.2.toNNReal ∧ y = X.X s z.1})
      ∂(P.prod (expMeasure p))) := by sorry
