-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_discounted_stieltjes_cell_two_sided_mass_squeeze
-- name    : AvramDividend.Classical.avram_wave5_04b_discounted_stieltjes_cell_two_sided_mass_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:47:39.130862+00:00
-- url     : https://prove2.me/theorems/7e8c9253-e3d0-4d62-8427-70d3260a7bff
-- title:
--   Exact two-sided cell mass squeeze for complete exponentially discounted Stieltjes measures
-- statement:
--   For every measure, q≥0 and arbitrary half-open interval (a,b], the entire actual discounted Stieltjes integral lies between exp(-q b) and exp(-q a) times the true full cell mass. This immediately applies to the dividendMeasure, including singular-continuous and right-atomic variation. It provides the two-sided Riemann envelope needed to pass from step-time weights to exact Stieltjes discounting.
-- source:
--   Combine the two Proved generic half-open-cell discount envelope inequalities 00b4947d... and the Proved right-endpoint companion.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_discounted_stieltjes_cell_le_left_endpoint_discount_mass
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_discounted_stieltjes_cell_ge_right_endpoint_discount_mass

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_discounted_stieltjes_cell_two_sided_mass_squeeze
    (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ) (a b : ℝ) :
    ENNReal.ofReal (Real.exp (-(q * b))) * μ (Ioc a b) ≤
      (∫⁻ s in Ioc a b, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) ∧
    (∫⁻ s in Ioc a b, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) ≤
      ENNReal.ofReal (Real.exp (-(q * a))) * μ (Ioc a b) := by sorry
