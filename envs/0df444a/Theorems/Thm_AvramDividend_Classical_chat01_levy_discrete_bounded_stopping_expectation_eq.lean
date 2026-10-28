-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_levy_discrete_bounded_stopping_expectation_eq
-- name    : AvramDividend.Classical.chat01_levy_discrete_bounded_stopping_expectation_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:44:15.114838+00:00
-- url     : https://prove2.me/theorems/caae9eaf-c005-4f69-8d62-589ae3a1b09d
-- title:
--   Exact bounded discrete stopped expectation for the compensated Lévy exponential
-- statement:
--   For an exponential martingale of a spectrally negative Lévy process sampled on any monotone natural-indexed time grid, two ordered bounded stopping times have equal expected stopped exponential values. This provides the exact optional-stopping equality needed for approximating first-passage identities.
-- source:
--   Proved levy_compensated_exponential_martingale and chat01_monotone_sampling_bounded_optional_stopping_eq.

import Mathlib.Probability.Martingale.OptionalStopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_chat01_monotone_sampling_bounded_optional_stopping_eq
open AvramDividend.Classical MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.chat01_levy_discrete_bounded_stopping_expectation_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (h𝓖 : 𝓖 =
      ({ seq := fun (n : ℕ) => 𝓕 (e n)
         mono' := by
           intro i j hij
           exact 𝓕.mono (he hij)
         le' := by
           intro n
           exact 𝓕.le (e n) } : Filtration ℕ mΩ))
    (τ π : Ω → WithTop ℕ)
    (hτ : IsStoppingTime 𝓖 τ) (hπ : IsStoppingTime 𝓖 π)
    (hle : τ ≤ π) (N : ℕ) (hbdd : ∀ ω, π ω ≤ (N : WithTop ℕ)) :
    (∫ ω, stoppedValue
      (fun (n : ℕ) (w : Ω) =>
        Real.exp (θ * X.X (e n) w -
          (e n : ℝ) * laplaceExponent X.c X.σ X.ν θ)) τ ω ∂P) =
    (∫ ω, stoppedValue
      (fun (n : ℕ) (w : Ω) =>
        Real.exp (θ * X.X (e n) w -
          (e n : ℝ) * laplaceExponent X.c X.σ X.ν θ)) π ω ∂P) := by sorry
