-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_residual_clock_freshPath_rectangle
-- name    : AvramDividend.Classical.avram_ws01e_b_levy_residual_clock_freshPath_rectangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:33:59.225855+00:00
-- url     : https://prove2.me/theorems/8999937e-12ee-4af0-9f15-03fa2cdaea44
-- title:
--   Genuine stopped Lévy fresh-path law conditionally factors from all residual-clock events
-- statement:
--   Let τ be any almost surely finite measurable stopping time of a spectrally negative Lévy process and e any independently sampled nonnegative measurable observation clock. Condition the genuine product probability law P×Q on the strict event τ<e. For every Borel event A concerning the real residual observation time e−τ and every measurable event B concerning the entire shifted Lévy future increment path, the conditional joint probability equals the conditional residual event probability multiplied by the original unshifted Lévy path event probability P(path∈B). This uses accepted full-path strong Markov independence, stationarity of the entire post-stopping path law and the accepted arbitrary clock-kernel conditional factor. There is no memorylessness requirement: the theorem is valid for arbitrary independent clock distributions and assumes no Wiener–Hopf identity.

import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_clock_indep_shiftedPath
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_shiftedFuturePath_sameLaw
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_clock_kernel_future_event_factor

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_levy_residual_clock_freshPath_rectangle
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Θ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (hStop : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (e : Θ → ℝ≥0) (he : Measurable e)
    (A : Set ℝ) (hA : MeasurableSet A)
    (B : Set (ℝ≥0 → ℝ)) (hB : MeasurableSet B) :
    (P.prod Q)[{z : Ω × Θ |
        ((e z.2 : ℝ) - (τ z.1 : ℝ)) ∈ A ∧
        (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1) ∈ B} |
        {z : Ω × Θ | τ z.1 < e z.2}] =
      (P.prod Q)[{z : Ω × Θ |
          ((e z.2 : ℝ) - (τ z.1 : ℝ)) ∈ A} |
          {z : Ω × Θ | τ z.1 < e z.2}] *
        P {ω : Ω | (fun s : ℝ≥0 => X.X s ω) ∈ B} := by sorry
