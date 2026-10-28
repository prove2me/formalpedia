-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_stationary_path_clock_factor
-- name    : AvramDividend.Classical.avram_ws01e_b_levy_stationary_path_clock_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:23:31.859915+00:00
-- url     : https://prove2.me/theorems/d702c6f5-795b-4443-b38e-72543fdc3965
-- title:
--   Residual-clock strong Markov factor with original full Lévy path law
-- statement:
--   At an actual finite stopping time τ for a spectrally negative Lévy process, and an independently sampled nonnegative memoryless observation clock e, the probability that e exceeds τ+t and the entire shifted post-τ increment path belongs to a measurable set B equals the memoryless factor at t times the product-law survival probability at τ times the original, unshifted Lévy path probability of B. This source-faithful theorem combines genuine stochastic strong-Markov stationarity of the whole path with the already proved random-age residual-clock factor. It assumes neither Wiener–Hopf independence nor two-sided exit identities and directly supplies the fresh-process-law factor needed after upper-record crossings.

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_shifted_path_residual_clock_factor
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_shiftedFuturePath_sameLaw

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_levy_stationary_path_clock_factor
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
    (t : ℝ≥0) (B : Set (ℝ≥0 → ℝ)) (hB : MeasurableSet B) :
    (P.prod Q) {z : Ω × Θ | τ z.1 + t < e z.2 ∧
       (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1) ∈ B} =
      factor t * (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} *
        P {ω : Ω | (fun s : ℝ≥0 => X.X s ω) ∈ B} := by sorry
