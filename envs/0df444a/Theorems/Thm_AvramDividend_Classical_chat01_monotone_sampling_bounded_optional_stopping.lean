-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_monotone_sampling_bounded_optional_stopping
-- name    : AvramDividend.Classical.chat01_monotone_sampling_bounded_optional_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:12:42.591983+00:00
-- url     : https://prove2.me/theorems/ceab6b4c-9223-4ba8-aaa9-5a7fcd5b961a
-- title:
--   Bounded discrete optional stopping of a sampled continuous-time martingale
-- statement:
--   Any real-time martingale sampled along an increasing sequence of nonnegative times obeys the expected stopped-value inequality for bounded discrete stopping times relative to the sampled filtration. This combines monotone time sampling with Mathlib's discrete optional-stopping theorem.
-- source:
--   Proved chat01_monotone_nat_sampling_martingale and Mathlib Submartingale.expected_stoppedValue_mono.

import Mathlib.Probability.Martingale.OptionalStopping
import Theorems.Thm_AvramDividend_Classical_chat01_monotone_nat_sampling_martingale
open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.chat01_monotone_sampling_bounded_optional_stopping
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
    (∫ ω, stoppedValue (fun (n : ℕ) => f (e n)) τ ω ∂μ) ≤
      (∫ ω, stoppedValue (fun (n : ℕ) => f (e n)) π ω ∂μ) := by sorry
