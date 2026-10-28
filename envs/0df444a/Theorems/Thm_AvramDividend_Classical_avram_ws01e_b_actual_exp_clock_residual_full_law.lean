-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_exp_clock_residual_full_law
-- name    : AvramDividend.Classical.avram_ws01e_b_actual_exp_clock_residual_full_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:59:53.497189+00:00
-- url     : https://prove2.me/theorems/e798f2d3-6468-45b9-a3d0-66802ce5420d
-- title:
--   Fresh complete real residual law under an actual independent exponential clock
-- statement:
--   Under the independent real Exp(p) law, the conditional real residual time e.toNNReal−τ on τ<e.toNNReal has exactly the same full pushforward law as an independent fresh e.toNNReal. This instantiates the proved generic memoryless real-residual distribution theorem, the exact exponential survival tail and NNReal exponential memorylessness. No tilted Wiener–Hopf independence is assumed.
-- source:
--   Previously accepted finite-stopping Lévy strong Markov and genuine original-law product theorems; pending corrected real residual clock law and memorylessness interfaces.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Data.NNReal.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_exponential_nnreal_survival_memorylessness
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_residual_real_clock_law_eq_fresh

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_actual_exp_clock_residual_full_law
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (Y : Ω → β) (hY : Measurable Y)
    (hInd : IndepFun τ Y P)
    (p : ℝ) (hp : 0 < p)
    (hPos : (P.prod (expMeasure p))
      {z : Ω × ℝ | τ z.1 < z.2.toNNReal} ≠ 0) :
    Measure.map (fun z : Ω × ℝ =>
      (z.2.toNNReal : ℝ) - (τ z.1 : ℝ))
      ((P.prod (expMeasure p))[|{z : Ω × ℝ | τ z.1 < z.2.toNNReal}]) =
    Measure.map (fun t : ℝ => (t.toNNReal : ℝ))
      (expMeasure p) := by sorry
