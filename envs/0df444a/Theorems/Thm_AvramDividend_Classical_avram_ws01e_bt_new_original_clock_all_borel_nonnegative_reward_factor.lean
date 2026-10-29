-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_all_borel_nonnegative_reward_factor
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_original_clock_all_borel_nonnegative_reward_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:53:06.453142+00:00
-- url     : https://prove2.me/theorems/bc057840-f7f6-41d0-a997-f2e4b3da61bd
-- title:
--   Original clock arbitrary nonnegative Borel supremum-drawdown reward factorisation
-- statement:
--   For the actual original Lévy process under P×Exp(p), any nonnegative extended-real measurable tests f of the running supremum S_e and g of the terminal drawdown D_e have exactly factorised extended expectations. The result requires no integrability or boundedness and is built from genuine separately Proved original-clock IndepFun and joint measurability. It provides a source-bound probabilistic reward interface for killed-resolvent and first-passage arguments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_original_expclock_sup_drawdown_indepFun
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_original_clock_all_borel_nonnegative_reward_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (f g : ℝ → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    let S : Ω × ℝ → ℝ :=
      fun z => runningSup X (Real.toNNReal z.2) z.1
    let D : Ω × ℝ → ℝ :=
      fun z => S z - X.X (Real.toNNReal z.2) z.1
    (∫⁻ z, f (S z) * g (D z) ∂(P.prod (expMeasure p))) =
      (∫⁻ z, f (S z) ∂(P.prod (expMeasure p))) *
      (∫⁻ z, g (D z) ∂(P.prod (expMeasure p))) := by sorry
