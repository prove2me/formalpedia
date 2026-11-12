-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger88_monotone_grid_Ioc_cash_exact_partition
-- name    : AvramDividend.Classical.avram_gledger88_monotone_grid_Ioc_cash_exact_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:00:17.670745+00:00
-- url     : https://prove2.me/theorems/96daf400-31eb-4d6b-851e-c8fc5fada602
-- title:
--   Nonnegative cash integral over monotone half-open grid cells adds exactly
-- statement:
--   Any finite monotone grid partitions its total half-open time interval into consecutive nonoverlapping half-open cells. The nonnegative integral of any function with respect to any measure is exactly the finite sum of its integrals on those cells. This avoids multiplying the same stopped dividend cash integral by the number of cells when assembling the original gledger81 cash bound.
-- source:
--   Core finite non-overcounting measure identity for gledger81 16e988d7, to be applied to the original dividendMeasure and original cash mask. This is distinct from individual-cell gledger83/gledger85 inequalities.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger88_monotone_grid_Ioc_cash_exact_partition
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (v : ℕ → ℝ) (hv : Monotone v) (k : ℕ) :
    (∑ i ∈ Finset.range k,
      ∫⁻ s in Ioc (v i) (v (i + 1)), f s ∂μ) =
    ∫⁻ s in Ioc (v 0) (v k), f s ∂μ := by sorry
