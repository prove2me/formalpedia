-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a115_original_positive_rate_negative_Borel_count_poisson_singletons_20261114
-- name    : AvramDividend.Classical.avram_a115_original_positive_rate_negative_Borel_count_poisson_singletons_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T19:13:22.158144+00:00
-- url     : https://prove2.me/theorems/0705d58b-4bb3-4c64-b759-8435d7697bdc
-- title:
--   Strictly positive original physical negative Borel count intensity: exact Poisson singleton event probabilities
-- statement:
--   Under strictly positive physical Borel jump-count intensity, prove that the actual original-space count at a finite horizon has the exact Poisson probability for every integer count k. Source count measurability, physical count equality and rate are explicit hypotheses; the zero-rate branch is handled separately by first-moment positivity.
-- source:
--   Original stationary independent finite-activity marked jump counting process and exact original void probabilities. This is the remaining positive-intensity stochastic case after direct zero-rate proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a115_original_positive_rate_negative_Borel_count_poisson_singletons_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal)
    (r : ℝ≥0)
    (hr : (r : ℝ) = ((T : ℝ≥0∞) * X.ν B).toReal)
    (hRatePos : 0 < r) :
    ∀ k : ℕ, P {ω : Ω | K ω = k} = poissonMeasure r {k} := by sorry
