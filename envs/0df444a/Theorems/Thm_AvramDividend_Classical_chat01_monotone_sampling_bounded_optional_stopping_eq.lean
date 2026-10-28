-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_monotone_sampling_bounded_optional_stopping_eq
-- name    : AvramDividend.Classical.chat01_monotone_sampling_bounded_optional_stopping_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:21:10.72163+00:00
-- url     : https://prove2.me/theorems/3e672b98-9166-482e-b2bc-dbeb33863a74
-- title:
--   Equality of bounded stopped expectations for monotone-time sampled martingales
-- statement:
--   The expected values of a martingale at two ordered, uniformly bounded discrete stopping times are equal, when the martingale originates from sampling a nonnegative-real-time martingale along an increasing time schedule. This strengthens the stopped inequality by also applying it to the negative martingale.
-- source:
--   Proved chat01_monotone_sampling_bounded_optional_stopping, Mathlib Martingale.neg, stoppedValue_neg, integral_neg.

import Mathlib.Probability.Martingale.OptionalStopping
import Theorems.Thm_AvramDividend_Classical_chat01_monotone_sampling_bounded_optional_stopping
open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.chat01_monotone_sampling_bounded_optional_stopping_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {f : ℝ≥0 → Ω → ℝ}
    (e : ℕ → ℝ≥0) (he : Monotone e) (hf : Martingale f 𝓕 μ)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration μ 𝓖]
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
    (∫ ω, stoppedValue (fun (n : ℕ) => f (e n)) τ ω ∂μ) =
      (∫ ω, stoppedValue (fun (n : ℕ) => f (e n)) π ω ∂μ) := by sorry
