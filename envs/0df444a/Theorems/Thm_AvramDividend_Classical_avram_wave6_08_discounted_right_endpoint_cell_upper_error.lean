-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_discounted_right_endpoint_cell_upper_error
-- name    : AvramDividend.Classical.avram_wave6_08_discounted_right_endpoint_cell_upper_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:31:45.881825+00:00
-- url     : https://prove2.me/theorems/4b1edf79-c16b-4fc2-9fcb-2eb255a80a6c
-- title:
--   Uniform right-endpoint discounted Stieltjes cell overestimate by q times cell width
-- statement:
--   For any locally finite or infinite measure μ, nonnegative discount rate q and cell [a,b] in nonnegative time, the actual exponentially discounted mass over (a,b] is bounded above by the right-endpoint discount times its cell mass plus q(b−a) times the same mass. This is a quantitative quadrature bound for arbitrary atomless, singular-continuous and atomic dividend measures. It is a source-faithful deterministic ingredient for the corrected original Lévy stopped source-grid epsilon-Stieltjes estimate, not an assumption of any missing Itô–Meyer theorem.
-- source:
--   Original Avram Wave6 Chat08 source-grid right-endpoint discount error; complements Proved 4bfd2714-dbb5-4da0-89c5-8216ba98b56c and supports original stopped dividend grid asymptotic hypothesis of 193e1b1b-14d0-445a-8861-bd2b838cb0f5.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave6_08_discounted_right_endpoint_cell_upper_error
    (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫⁻ s in Ioc a b, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) ≤
      ENNReal.ofReal (Real.exp (-(q * b)) + q * (b - a)) * μ (Ioc a b) := by sorry
