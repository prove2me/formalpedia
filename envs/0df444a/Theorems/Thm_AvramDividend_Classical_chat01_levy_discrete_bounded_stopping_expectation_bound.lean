-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_levy_discrete_bounded_stopping_expectation_bound
-- name    : AvramDividend.Classical.chat01_levy_discrete_bounded_stopping_expectation_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:14:46.925212+00:00
-- url     : https://prove2.me/theorems/5c9c3969-7db6-458a-bd76-d9b9f109cae7
-- title:
--   Bounded discrete optional stopping for the compensated Lévy exponential
-- statement:
--   Let a spectrally negative Lévy process's compensated exponential martingale be sampled at any increasing sequence of nonnegative real times. For bounded discrete stopping times τ and π with τ no later than π, the stopped expectation at τ does not exceed that at π. Assumes the sampled filtration is sigma-finite under the underlying measure.
-- source:
--   Proved chat01_levy_exponential_nat_sampled_martingale and Mathlib Submartingale.expected_stoppedValue_mono.

import Mathlib.Probability.Martingale.OptionalStopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat01_levy_exponential_nat_sampled_martingale
open AvramDividend.Classical MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.chat01_levy_discrete_bounded_stopping_expectation_bound
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
          (e n : ℝ) * laplaceExponent X.c X.σ X.ν θ)) τ ω ∂P) ≤
    (∫ ω, stoppedValue
      (fun (n : ℕ) (w : Ω) =>
        Real.exp (θ * X.X (e n) w -
          (e n : ℝ) * laplaceExponent X.c X.σ X.ν θ)) π ω ∂P) := by sorry
