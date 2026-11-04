-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_cell_exact_discount_kernel_sandwich
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_closed_cell_exact_discount_kernel_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:29:44.072394+00:00
-- url     : https://prove2.me/theorems/aba3e90e-193b-49f3-83d9-6307c6b3d305
-- title:
--   Original Stieltjes payment discount is sandwiched by closed cell endpoint discounts
-- statement:
--   Exact original discount weight ENNReal.ofReal(exp(-qt)) on any nonnegative Stieltjes payment cell lies between its endpoint discounts, including time zero and the closed right-endpoint atom. This supplies the pointwise input to a rigorous discounted continuous/singular Stieltjes mesh approximation rather than replacing all payment times with a terminal discount.
-- source:
--   Original P4-F discounted dividendMeasure Cash; Avram Palmowski Pistorius controlled Stieltjes verification Proposition 4(i), (5.10)-(5.12)

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_closed_cell_exact_discount_kernel_sandwich
    (q : ℝ) (hq : 0 ≤ q) (a t b : ℝ≥0)
    (hat : a ≤ t) (htb : t ≤ b) :
    ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) ≤
      ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) ∧
    ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) ≤
      ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) := by sorry
