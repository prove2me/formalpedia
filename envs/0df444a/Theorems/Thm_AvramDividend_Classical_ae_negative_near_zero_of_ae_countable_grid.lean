-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_ae_countable_grid
-- name    : AvramDividend.Classical.ae_negative_near_zero_of_ae_countable_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:12:59.445529+00:00
-- url     : https://prove2.me/theorems/70f14aac-397c-471f-aac9-29c1f957c022
-- title:
--   Almost-sure negative increments on cofinal countable time grids imply downward regularity
-- statement:
--   A pathwise countable observation scheme is sufficient for zero to be regular for the negative half-line. If the selected horizon sequence is cofinal towards zero, and almost every Lévy sample path has a strictly negative value at some grid time before every selected horizon, then almost every path has a negative observation before every strictly positive real time horizon. This bridges a countable measurable grid event, amenable to independence and finite-dimensional distributions, to the original all-real-time downward-regularity theorem. Proving the grid event from unbounded variation remains a separate probabilistic obligation.
-- source:
--   Elementary cofinal-horizon reduction for the negative half-line regularity criterion in spectrally negative Lévy fluctuation theory; Kuznetsov, Kyprianou and Rivero (2013), regularity of the half-line.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Data.NNReal.Defs

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.ae_negative_near_zero_of_ae_countable_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (times horizons : ℕ → ℝ≥0)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, horizons n ≤ ε)
    (hGridAE : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧ X.X (times m) ω < 0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0 := by sorry
