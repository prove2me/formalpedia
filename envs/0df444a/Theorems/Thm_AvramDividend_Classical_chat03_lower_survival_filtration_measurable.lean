-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_lower_survival_filtration_measurable
-- name    : AvramDividend.Classical.chat03_lower_survival_filtration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T10:43:12.623684+00:00
-- url     : https://prove2.me/theorems/398891d8-81c2-4654-864c-79b2496d4c95
-- title:
--   One-sided survival through a closed horizon belongs to the current filtration
-- statement:
--   For any spectrally negative Lévy reserve process, lower barrier and finite horizon T, the event that the path has never crossed strictly below the lower barrier at any time from 0 through T is measurable with respect to the filtration at T. Reciprocal-natural-grid observations detect every strict lower crossing before T, while a separate terminal observation handles a crossing at exactly T. This one-sided result is suitable for the whole-history zero-killed discounted q-scale payoff, without imposing an artificial upper barrier.
-- source:
--   Depends on publicly Proved chat03_lower_before_horizon_countable_grid_iff (0ec8694a-90cc-4e41-9d39-37f4e80426cd), and Lévy adaptedness. Independent of scale harmonicity and the open root theorem.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_lower_survival_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower : ℝ) (T : ℝ≥0) :
    MeasurableSet[𝓕 T]
      {ω | ∀ t : ℝ≥0, t ≤ T → ¬ X.X t ω < lower} := by
  sorry
