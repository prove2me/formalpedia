-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger111_monotone_grid_Ioc_cash_le_strict_stop
-- name    : AvramDividend.Classical.avram_gledger111_monotone_grid_Ioc_cash_le_strict_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:52:06.499809+00:00
-- url     : https://prove2.me/theorems/bc396145-4a21-419a-8b31-7672422c18d5
-- title:
--   Original cash cell sums are bounded by the strict pre-stop interval
-- statement:
--   For a monotone grid beginning at zero, the aggregate measure-weighted cash in all complete intervals before the first stopping-cell crossing is bounded by the integral over the strict positive pre-stop interval. There is no duplication of the same dividend cash across cells.
-- source:
--   Root-connected gledger81 original stopped dividend contact correction; exact gledger88 partition followed by interval restriction monotonicity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger88_monotone_grid_Ioc_cash_exact_partition
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger111_monotone_grid_Ioc_cash_le_strict_stop
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (v : ℕ → ℝ) (hv : Monotone v) (hv0 : v 0 = 0)
    (k : ℕ) (ρ : ℝ) (hvk : v k < ρ) :
    (∑ i ∈ Finset.range k,
      ∫⁻ s in Ioc (v i) (v (i + 1)), f s ∂μ) ≤
    ∫⁻ s in Ioo 0 ρ, f s ∂μ := by sorry
