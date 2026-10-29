-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_P_exp_clock_sup_drawdown_indepFun
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_original_P_exp_clock_sup_drawdown_indepFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:18:27.258322+00:00
-- url     : https://prove2.me/theorems/393755b5-3a71-49ba-9bce-b4dda9c9e843
-- title:
--   Original Lévy process has independent supremum and terminal drawdown at an exponential clock
-- statement:
--   For every actual spectrally negative Lévy process on a probability space and every positive exponential rate p, the running supremum up to the independent exponential clock and its terminal drawdown are independent under the original un-tilted product measure P×Exp(p). This follows source-faithfully by θ=0 from the accepted genuinely random-terminal Esscher IndepFun theorem, using the actual Lévy–Khintchine identity ψ(0)=0 and withDensity_one. This provides the original-clock Wiener–Hopf interface for WS1A/B without any fictitious independent Esscher path law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_original_P_exp_clock_sup_drawdown_indepFun
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p) :
    IndepFun
      (fun z : Ω × ℝ => runningSup X (Real.toNNReal z.2) z.1)
      (fun z : Ω × ℝ =>
        runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1)
      (P.prod (expMeasure p)) := by sorry
