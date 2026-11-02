-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_ae_exhaustion_measurable_monotone_clock
-- name    : AvramDividend.Classical.avram_wave5_05_original_ae_exhaustion_measurable_monotone_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:39:49.223677+00:00
-- url     : https://prove2.me/theorems/8a500239-9709-4f5b-bd6d-c9d4514f5089
-- title:
--   Almost surely exhaustive measurable stopping clocks admit an everywhere monotone clock envelope
-- statement:
--   For an arbitrary measurable random terminal clock rho and any sequence of measurable random times S_n whose lower-tail infima tend to infinity almost surely, construct measurable monotone clocks tau_n increasing to rho for every sample path and each tau_n is bounded by min(rho,S_n) almost surely. Replacing null exceptional paths by the terminal clock makes pointwise supremum equality exact while preserving the a.e. stopped budget comparison. This permits stopping times that are not monotone in n; no stochastic dynamics or finite-variation assumptions enter.
-- source:
--   Original Lévy dividend verification localization; pure measure-theoretic tail-infimum clock construction used in corrected UBV core.

import Mathlib

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave5_05_original_ae_exhaustion_measurable_monotone_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (ρ : Ω → ℝ≥0∞) (hρ : Measurable ρ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSm : ∀ n, Measurable (S n))
    (hTailAE : ∀ᵐ ω ∂P,
      (⨆ n, (⨅ m, if n ≤ m then S m ω else ⊤)) = ⊤) :
    ∃ τ : ℕ → Ω → ℝ≥0∞,
      (∀ n, Measurable (τ n)) ∧
      (∀ ω, Monotone (fun n => τ n ω)) ∧
      (∀ ω, (⨆ n, τ n ω) = ρ ω) ∧
      (∀ n, ∀ᵐ ω ∂P, τ n ω ≤ min (ρ ω) (S n ω)) := by
  sorry
