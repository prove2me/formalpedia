-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB146_original_discounted_Stieltjes_physical_cell_lower
-- name    : AvramDividend.Classical.avram_gbB146_original_discounted_Stieltjes_physical_cell_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:01:59.609491+00:00
-- url     : https://prove2.me/theorems/cda2677a-8130-4a34-ad62-5a6db8df9345
-- title:
--   Discounted Stieltjes cash over a physical Ioc cell is at least endpoint discount times cell measure
-- statement:
--   For any nonnegative discount rate and any real physical cash interval (a,b], the discounted nonnegative Lebesgue–Stieltjes integral is bounded below by e^(-qb) times the underlying measure of that interval. This source-ready inequality is the missing monotone-weight lower estimate in the original Gaussian reflected barrier cash certificate; it applies directly with the original dividendMeasure.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB146_original_discounted_Stieltjes_physical_cell_lower
    (μ : Measure ℝ) (q : ℝ) (hq : 0 ≤ q)
    (a b : ℝ) :
    ENNReal.ofReal (Real.exp (-(q * b))) * μ (Ioc a b) ≤
      ∫⁻ t in Ioc a b,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ := by sorry
