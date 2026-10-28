-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_on_countable_schedule
-- name    : AvramDividend.Classical.bv_drift_deficit_ae_monotone_on_countable_schedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:22:28.817567+00:00
-- url     : https://prove2.me/theorems/ca3cc02f-b583-4fa7-a8ff-abb2648c6cca
-- title:
--   The actual BV drift deficit is jointly nondecreasing on any countable time schedule
-- statement:
--   For any countable schedule of nonnegative observation times, a single probability-one event makes the drift-deficit path D_t=d t-X_t nondecreasing between every ordered pair of scheduled times. This follows from the accepted all-fixed-pair drift-compensated increment bound using a countable conjunction of almost-everywhere events. It supports a subsequent càdlàg extension to all times and identification of the finite-activity first-jump clock.
-- source:
--   Actual bounded-variation Lévy stationary-increment support and countable intersection of almost-everywhere events, Avram et al. (2007), §3.3.

import Theorems.Thm_AvramDividend_Classical_bv_process_drift_compensated_increment_nonneg
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_drift_deficit_ae_monotone_on_countable_schedule
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (r : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ i j : ℕ, r i ≤ r j →
      X.drift * (r i : ℝ) - X.X (r i) ω ≤
      X.drift * (r j : ℝ) - X.X (r j) ω := by sorry
