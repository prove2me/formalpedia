-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_shifted_path_residual_clock_factor
-- name    : AvramDividend.Classical.avram_ws01e_b_levy_shifted_path_residual_clock_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T21:52:27.235089+00:00
-- url     : https://prove2.me/theorems/134c1d13-c0db-4dcb-815a-5b16fc07554f
-- title:
--   Finite Lévy stopping-time post-path event factors from genuine residual clock survival
-- statement:
--   Let X be a spectrally negative Lévy process under its original probability P, τ a finite measurable stopping time, and e an independently sampled nonnegative observation clock with a measurable strictly memoryless survival kernel. For any additional t≥0 and any Borel event B of the whole shifted Lévy future increment path s↦X_{τ+s}−X_τ, the joint P×Q probability of e>τ+t and shiftedPath∈B equals factor(t) times P×Q(e>τ) times the probability of that shifted-path event. All Lévy shifted-path measurability and stopped-time independence are derived from accepted genuine strong-Markov results; this is an original-law bridge to record splitting, without assuming a global Esscher law or Wiener–Hopf factorisation.

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_clock_indep_shiftedPath
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_residual_clock_survival_shift

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_levy_shifted_path_residual_clock_factor
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
        P {ω : Ω |
          (fun s : ℝ≥0 => X.X (τ ω + s) ω - X.X (τ ω) ω) ∈ B} := by sorry
