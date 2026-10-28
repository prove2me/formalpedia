-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_upperGrid_fibre_futureReward_scalar_factor
-- name    : AvramDividend.Classical.levy_upperGrid_fibre_futureReward_scalar_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:34:10.336992+00:00
-- url     : https://prove2.me/theorems/d294d6c4-525f-45f3-ace6-857bc53c965e
-- title:
--   Strong-Markov future reward factors on each adapted stopped-time grid fibre
-- statement:
--   For an adapted upper-grid approximation to a Lévy stopping time and any stopped-history event, the nonnegative future-path reward restricted to one stopped-time fibre has expectation equal to that fibre probability times the original whole-path expected reward. This directly composes the proved finite-grid joint product law with the pushforward indicator-mass and product-integral factorisation lemmas.
-- source:
--   Direct intermediate for the no-W strong-Markov barrier value split 79978d61-9d1f-4b20-b8a5-114797a8e380, composing proved finite-grid joint law f8d196c7-e8f7-4929-bc3b-b6c523c5ea5b, product scalar factor 7308e350-de7f-4e44-aff6-1f74bf3db945, pushforward indicator mass 772cefce-ada4-42ec-876d-2eb6794c34c9, and stopped fibre measurability.

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_stoppedHistory_upperGrid_futureReward_product
import Theorems.Thm_AvramDividend_Classical_stoppedEvent_upperGridFibre_measurable
import Theorems.Thm_AvramDividend_Classical_productIndicator_futureReward_lintegral_factor
import Theorems.Thm_AvramDividend_Classical_realIndicator_pushforward_one_mass

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_upperGrid_fibre_futureReward_scalar_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (τn : ℕ → Ω → ℝ≥0)
    (habove : ∀ ω n, τ ω ≤ τn n ω)
    (hfibres : ∀ n s,
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (n : ℕ) (s : ℝ≥0)
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, Set.indicator (A ∩ {ω' : Ω | τn n ω' = s})
      (fun ω' => g (fun t : ℝ≥0 =>
        X.X (s + t) ω' - X.X s ω')) ω ∂P) =
    P (A ∩ {ω : Ω | τn n ω = s}) *
      (∫⁻ y, g y ∂(Measure.map
        (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  sorry
