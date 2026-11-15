-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_unit_cash_interval_integral_gt_half
-- name    : AvramDividend.Classical.avram_bvb_obstruction_unit_cash_interval_integral_gt_half
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T00:28:15.000987+00:00
-- url     : https://prove2.me/theorems/2ec6e87a-2580-4ceb-abf7-be08f470ebd1
-- title:
--   Exact one-unit exponential discount integral exceeds half the boundary value
-- statement:
--   The real interval integral of exp(x) over [-1,0] exceeds 1/2, an exact discounted unit-drift zero-reserve cash witness after reversing time. This supports formal disproof of the spurious pathwise drift-only inequality.
-- source:
--   Pinned Mathlib integral_exp yields ∫_{-1}^0 exp x dx = 1-exp(-1). Reuse Proved 8e8693a4 strict numerical inequality. No claim on sample-path existence.

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_one_step_discounted_cash_gt_half
open MeasureTheory intervalIntegral Real

theorem AvramDividend.Classical.avram_bvb_obstruction_unit_cash_interval_integral_gt_half : (1 / 2 : ℝ) < ∫ x in (-1 : ℝ)..(0 : ℝ), Real.exp x := by sorry
