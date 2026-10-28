-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_levy_conditional_residual_clock_shifted_path_indepFun
-- name    : AvramDividend.Classical.avram_ws01e_b_support_levy_conditional_residual_clock_shifted_path_indepFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:45:43.41875+00:00
-- url     : https://prove2.me/theorems/b2692508-f914-477b-90ac-c9986fe0970a
-- title:
--   Conditional independence of the true Lévy shifted path and residual independent clock
-- statement:
--   Under the original probability law of a spectrally negative Lévy process, let τ be a measurable finite stopping time for its canonical filtration, and e an independent nonnegative observation clock whose strict survival kernel has a multiplicative memoryless shift. Conditional on the positive-probability event τ<e, the real residual observation time e−τ and the entire shifted post-τ Lévy increment path are independent random variables. The proof supplies path measurability from the accepted joint-evaluation theorem, uses the proved finite-stopping strong-Markov path independence, and applies the proved genuine conditional residual-clock theorem. This is a concrete clock-regeneration interface for finite-rate Wiener–Hopf factorisation. It does not assert a coherent Esscher law, upcrossing transform or Wiener–Hopf independence.

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_clock_indep_shiftedPath
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_residual_clock_future_indepFun

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_support_levy_conditional_residual_clock_shifted_path_indepFun
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Θ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (hStop : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (e : Θ → ℝ≥0) (he : Measurable e)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (hTail : ∀ a : ℝ≥0, Q {η : Θ | a < e η} = discount a)
    (factor : ℝ≥0 → ℝ≥0∞)
    (hShift : ∀ a t : ℝ≥0, discount (a + t) = factor t * discount a)
    (hPos : (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} ≠ 0) :
    IndepFun
      (fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ))
      (fun z : Ω × Θ => fun s : ℝ≥0 =>
        X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)
      ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}]) := by sorry
