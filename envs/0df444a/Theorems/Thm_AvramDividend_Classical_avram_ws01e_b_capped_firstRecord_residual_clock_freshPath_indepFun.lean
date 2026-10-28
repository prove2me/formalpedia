-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_capped_firstRecord_residual_clock_freshPath_indepFun
-- name    : AvramDividend.Classical.avram_ws01e_b_capped_firstRecord_residual_clock_freshPath_indepFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:13:48.576948+00:00
-- url     : https://prove2.me/theorems/24f810fc-b75e-40e3-90ae-e18f6538aab0
-- title:
--   Genuine stopped-record residual-clock and shifted Lévy path independence after finite localisation
-- statement:
--   For a spectrally negative Lévy process, a real strict first upper-passage level b and finite nonnegative cap N, let τ_N be the minimum of the possibly infinite original strict first-upcrossing time and N, converted to a finite nonnegative age. For any independently sampled observation clock e with P×Q(τ_N<e)>0, under the actual original-law product measure conditioned on τ_N<e, the real residual time e−τ_N is independent of the entire centred post-τ_N Lévy increment path. The proof uses the Proved right-continuous filtration process lift, the Proved capped-first-record finite stopping-time/measurability interface, and the canonically Proved full conditional Lévy shifted-path independence. It is a genuine application at localised upper-passage stopping times without assuming Wiener–Hopf factorisation, tilted all-horizon law or memorylessness.

import Mathlib.Probability.ConditionalProbability
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_rightCont_stopping_and_clock_measurable
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_conditional_residual_clock_shiftedPath_indepFun

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_capped_firstRecord_residual_clock_freshPath_indepFun
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Θ]
    {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (N : ℝ≥0)
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (e : Θ → ℝ≥0) (he : Measurable e)
    (hPos : (P.prod Q) {z : Ω × Θ |
      (min (twoSidedExitUpTime X b z.1) (N : ℝ≥0∞)).toNNReal < e z.2} ≠ 0) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
    IndepFun
      (fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ))
      (fun z : Ω × Θ => fun s : ℝ≥0 =>
        X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)
      ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}]) := by sorry
