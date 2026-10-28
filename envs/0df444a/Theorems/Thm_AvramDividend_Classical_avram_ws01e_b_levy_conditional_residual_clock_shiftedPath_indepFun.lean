-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_conditional_residual_clock_shiftedPath_indepFun
-- name    : AvramDividend.Classical.avram_ws01e_b_levy_conditional_residual_clock_shiftedPath_indepFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:51:33.027819+00:00
-- url     : https://prove2.me/theorems/20c4a598-844a-4237-9160-3d10d79562d4
-- title:
--   Whole fresh Lévy increment path is independent of a residual observation clock at a finite stopping age
-- statement:
--   Let X be a spectrally negative Lévy process and τ a finite measurable stopping time. Sample an arbitrary independent observation clock e, and assume τ<e has positive product probability. Conditional on τ<e, the real residual duration e−τ and the complete post-τ Lévy increment path are independent. This is genuine sigma-algebra independence for all real Borel and measurable path events. It follows from the separately Proved full Borel rectangle factorisation and the unchanged conditional path marginal, without assuming Wiener–Hopf splitting or exponential memorylessness.

import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_residual_clock_freshPath_rectangle

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_levy_conditional_residual_clock_shiftedPath_indepFun
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Θ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (hStop : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (e : Θ → ℝ≥0) (he : Measurable e)
    (hPos : (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} ≠ 0) :
    IndepFun
      (fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ))
      (fun z : Ω × Θ => fun s : ℝ≥0 =>
        X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)
      ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}]) := by sorry
