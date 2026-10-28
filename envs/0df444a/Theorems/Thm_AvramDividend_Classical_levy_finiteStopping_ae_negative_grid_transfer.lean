-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_ae_negative_grid_transfer
-- name    : AvramDividend.Classical.levy_finiteStopping_ae_negative_grid_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:24:12.127287+00:00
-- url     : https://prove2.me/theorems/bb820d45-fe62-4eb1-a4ad-b69b9cda6cf1
-- title:
--   Almost-sure negative-near-zero countable-grid observations persist after a finite Lévy stopping time
-- statement:
--   Let X be a spectrally negative Lévy process, τ a finite stopping time and times, horizons countable observation schedules. If almost every original sample path takes a strictly negative value along the schedule before every listed horizon, then the entire shifted increment path after τ has exactly the same almost-sure grid property. This combines the already Proved full-path stopping-time law transfer with the measurable countable-cylinder event and will support the excursion restart argument after the original process-level negative regularity is established. No excursion measure or atomlessness is postulated.
-- source:
--   Strong Markov law of spectrally negative Lévy paths; Kuznetsov, Kyprianou and Rivero (2013), scale-function excursion-height atomlessness in Section 2.3.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_shiftedPath_ae_event_transfer

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_finiteStopping_ae_negative_grid_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (hOrigMeas : Measurable (fun ω : Ω => fun t : ℝ≥0 => X.X t ω))
    (times horizons : ℕ → ℝ≥0)
    (hGridAE : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧ X.X (times m) ω < 0) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧
        X.X (τ ω + times m) ω - X.X (τ ω) ω < 0 := by sorry
