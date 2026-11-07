-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_infinitecap_candidate_globally_nonnegative
-- name    : AvramDividend.Classical.avram_ubv_loc6_infinitecap_candidate_globally_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:25:18.161494+00:00
-- url     : https://prove2.me/theorems/8e855eb9-8718-4573-9d3d-ef9694394cff
-- title:
--   Exact UBV infinite-cap HJB candidate is nonnegative at every reserve, including negative ruin overshoot
-- statement:
--   From the original unbounded-variation HJB candidate's C2 regularity on the entire positive half-line, gradient at least one, w(0)>=0 and zero extension to negative reserves, conclude w(y)>=0 for every real reserve. This is an independent source-exact component of the stopped nonnegative-payoff certificate, with no stochastic assumptions or extra growth hypothesis.
-- source:
--   UBV-LOC6 original top-cap stopped-payoff nonnegativity component for fa7052b1, using already proved positive-cap compact C1 gradient nonnegativity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_loc6_infinitecap_candidate_globally_nonnegative
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hCtop : C = ⊤) :
    ∀ y : ℝ, 0 ≤ w y := by sorry
