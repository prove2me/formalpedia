-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_terminal_wh_laplace_factor
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_original_clock_terminal_wh_laplace_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:29:58.381267+00:00
-- url     : https://prove2.me/theorems/1b61a1a1-8717-4d62-b5ff-4823efec087f
-- title:
--   Actual original exponential-clock Lévy terminal Laplace factorisation
-- statement:
--   For every spectrally negative Lévy process under its original law P, every exponential observation rate p>0 and every real β, the extended-nonnegative expectation of exp(β X_e) under the genuine P×Exp(p) product measure equals the product of the actual running-supremum exponential moment and the actual terminal-drawdown negative-exponential moment. This follows from genuine original-clock supremum/drawdown independence, the source-measurable extrema, Tonelli and the pathwise identity X_e=S_e-D_e. The ENNReal identity is valid even when an exponential moment is infinite; it assumes no spurious moment-rate gap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_P_exp_clock_sup_drawdown_indepFun
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_original_clock_terminal_wh_laplace_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p) (β : ℝ) :
    let S : Ω × ℝ → ℝ :=
      fun z => runningSup X (Real.toNNReal z.2) z.1
    let D : Ω × ℝ → ℝ :=
      fun z => S z - X.X (Real.toNNReal z.2) z.1
    (∫⁻ z, ENNReal.ofReal
       (Real.exp (β * X.X (Real.toNNReal z.2) z.1))
       ∂(P.prod (expMeasure p))) =
      (∫⁻ z, ENNReal.ofReal (Real.exp (β * S z))
          ∂(P.prod (expMeasure p))) *
      (∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z))
          ∂(P.prod (expMeasure p))) := by sorry
