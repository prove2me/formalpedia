-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin28_original_positive_clock_event_measure_mono
-- name    : AvramDividend.Classical.avram_mix_fin28_original_positive_clock_event_measure_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T14:59:32.522582+00:00
-- url     : https://prove2.me/theorems/0f0a0010-7856-4724-906f-7b87df16c9ba
-- title:
--   Original bounded stopped positive-clock event monotonicity under earlier localisation
-- statement:
--   For any original spectrally negative Levy law, bounded stopping clock sigma, and an earlier stopped clock rho<=sigma pathwise, the event that rho is strictly positive is contained in the event that sigma is strictly positive. Consequently every initial event intersected with the earlier positive-clock event has probability no greater than the corresponding sigma event. This deterministic-probabilistic bookkeeping is necessary when moving the physical finite-mixed local event Ito estimate to the parent 2545e563 without changing its right-hand probability event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin28_original_positive_clock_event_measure_mono
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (σ ρ : Ω → ℝ≥0) (hρle : ∀ ω, ρ ω ≤ σ ω)
    (A : Set Ω) :
    P (A ∩ {ω : Ω | ρ ω ≠ 0}) ≤
      P (A ∩ {ω : Ω | σ ω ≠ 0}) := by sorry
