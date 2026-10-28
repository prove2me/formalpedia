-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_freshPath_joint_lintegral_regeneration
-- name    : AvramDividend.Classical.avram_ws01e_b_conditional_freshPath_joint_lintegral_regeneration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:33:54.270467+00:00
-- url     : https://prove2.me/theorems/334ecdb6-2d23-4313-878d-8748228bd4dc
-- title:
--   Full conditional residual-clock and fresh Lévy path reward regeneration
-- statement:
--   Conditioned on a genuine finite Lévy stopping time preceding an independent observation clock, the lower expectation of every measurable nonnegative reward of BOTH the real residual clock and the entire shifted Lévy future increment path equals its expectation under the product of the conditional residual-time law and the original Lévy full-path law. No exponential memoryless assumption is required, and this is a direct measurable-functional extension of the accepted complete conditional joint product law. It is the law-level regeneration interface needed for reflected drawdown functionals evaluated over a random residual time.
-- source:
--   Direct corollary of the Proved avram_ws01e_b_levy_conditional_joint_residual_freshPath_product_law (55f49ff2-5bdf-4149-9860-c8f1fbe1b429), genuine stopped future-path measurability and pinned mathlib lintegral_map.

import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_conditional_joint_residual_freshPath_product_law
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_conditional_freshPath_joint_lintegral_regeneration
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Θ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (hStop : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (e : Θ → ℝ≥0) (he : Measurable e)
    (hPos : (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} ≠ 0)
    (G : ℝ × (ℝ≥0 → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ z : Ω × Θ,
      G ((e z.2 : ℝ) - (τ z.1 : ℝ),
          fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)
        ∂((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}])) =
    (∫⁻ y : ℝ × (ℝ≥0 → ℝ), G y
      ∂(Measure.map (fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ))
         ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}])).prod
       (Measure.map (fun ω : Ω => fun s : ℝ≥0 => X.X s ω) P)) := by sorry
