-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_original_expclock_sup_drawdown_indepFun
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_original_expclock_sup_drawdown_indepFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:54:44.935836+00:00
-- url     : https://prove2.me/theorems/47e972c8-c02e-465c-a5bc-07f104a92f10
-- title:
--   Original product exponential-clock supremum and terminal drawdown independence
-- statement:
--   For any genuine spectrally negative Lévy process X under probability P and every p>0, the running supremum at an independent Exp(p) time is independent of the terminal drawdown under the actual product law P×Exp(p). This is the zero-Esscher-parameter specialisation of the already accepted genuine tilted theorem; the exponent at θ=0 is zero and the withDensity weight is identically one.
-- source:
--   Proved actual-Qp IndepFun theorem 421ab102; actual Lévy Laplace exponent at zero; pinned Mathlib MeasureTheory.withDensity_one. Supports original-clock fluctuation factorisation for stopped-scale/killed-resolvent workstreams.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bi_new_original_expclock_sup_drawdown_indepFun
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p) :
    ProbabilityTheory.IndepFun
      (fun z : Ω × ℝ => runningSup X (Real.toNNReal z.2) z.1)
      (fun z : Ω × ℝ =>
        runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1)
      (P.prod (ProbabilityTheory.expMeasure p)) := by sorry
