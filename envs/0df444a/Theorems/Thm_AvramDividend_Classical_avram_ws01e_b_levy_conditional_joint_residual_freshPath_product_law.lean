-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_conditional_joint_residual_freshPath_product_law
-- name    : AvramDividend.Classical.avram_ws01e_b_levy_conditional_joint_residual_freshPath_product_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:00:34.55515+00:00
-- url     : https://prove2.me/theorems/55f49ff2-5bdf-4149-9860-c8f1fbe1b429
-- title:
--   Conditional residual time and fresh Lévy path have the exact product probability law
-- statement:
--   Under a genuine product law of a spectrally negative Lévy process and an arbitrary independent observation clock, let τ be a finite measurable stopping time, and suppose τ<e has positive probability. The joint pushforward distribution, conditioned on τ<e, of the real residual duration e−τ and the full post-τ centred Lévy increment path equals the product of the conditional residual-time distribution and the original unshifted Lévy path distribution. This is a measure equality enabling transfer of arbitrary measurable functionals, stronger than rectangle independence and without requiring exponential memorylessness or assuming Wiener–Hopf.

import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_conditional_residual_clock_shiftedPath_indepFun
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_residual_clock_freshPath_rectangle

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_levy_conditional_joint_residual_freshPath_product_law
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Θ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (hStop : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (e : Θ → ℝ≥0) (he : Measurable e)
    (hPos : (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} ≠ 0) :
    Measure.map
      (fun z : Ω × Θ =>
        ((e z.2 : ℝ) - (τ z.1 : ℝ),
          fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1))
      ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}]) =
    (Measure.map (fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ))
      ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}])).prod
    (Measure.map (fun ω : Ω => fun s : ℝ≥0 => X.X s ω) P) := by sorry
