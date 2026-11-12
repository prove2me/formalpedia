-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger90_masked_monotone_grid_Ioc_cash_partition
-- name    : AvramDividend.Classical.avram_gledger90_masked_monotone_grid_Ioc_cash_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:09:13.640719+00:00
-- url     : https://prove2.me/theorems/b82bd6d9-2a03-4991-af2c-8a8cd25973ed
-- title:
--   Original payment-time masked nonnegative cash integrals partition exactly over a grid
-- statement:
--   Given a measurable payment-time mask and any monotone finite time grid, the restricted nonnegative cash integral on the full half-open interval equals the sum of its integrals over consecutive disjoint masked half-open cells. Applying this to the original dividend measure, original paymentTimes, original nonnegative discount and clipped grid eliminates cash overcounting in gledger81.
-- source:
--   Genuine masked measure partition needed for root-connected gledger81 16e988d7, distinct from generic unmasked gledger88 and the single-cell inclusions gledger83 and gledger85.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger90_masked_monotone_grid_Ioc_cash_partition
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (S : Set ℝ) (hS : MeasurableSet S)
    (v : ℕ → ℝ) (hv : Monotone v) (k : ℕ) :
    (∑ i ∈ Finset.range k,
      ∫⁻ s in S ∩ Ioc (v i) (v (i + 1)), f s ∂μ) =
    ∫⁻ s in S ∩ Ioc (v 0) (v k), f s ∂μ := by sorry
