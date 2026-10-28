-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_ae_negative_near_zero_of_grid
-- name    : AvramDividend.Classical.levy_finiteStopping_ae_negative_near_zero_of_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:38:34.310577+00:00
-- url     : https://prove2.me/theorems/e39806bd-5f10-4cff-b3ce-6590404d1c87
-- title:
--   Downward regularity of post-stopping Lévy increments from a cofinal negative countable-grid law
-- statement:
--   When the Lévy process has a negative observation before every cofinal grid horizon almost surely, its post-stopping increment path also has an arbitrarily early negative increment almost surely for any finite stopping time. The proof composes the independent countable-grid strong Markov transfer with the proved cofinal-grid implication. This is the exact ordinary-P restart consequence needed at excursion-height hitting times after establishing the original grid event, though the excursion-measure Markov property remains distinct and unproved.
-- source:
--   Proved Prove2Me whole-path stopped-law transfer, countable-grid negativity event, and cofinal-grid reduction; related to Kuznetsov-Kyprianou-Rivero scale-function excursion-height atomlessness Section 2.3.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_ae_negative_grid_transfer
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_ae_countable_grid

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_finiteStopping_ae_negative_near_zero_of_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (hOrigMeas : Measurable (fun ω : Ω => fun t : ℝ≥0 => X.X t ω))
    (times horizons : ℕ → ℝ≥0)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, horizons n ≤ ε)
    (hGridAE : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧ X.X (times m) ω < 0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧
        X.X (τ ω + s) ω - X.X (τ ω) ω < 0 := by sorry
