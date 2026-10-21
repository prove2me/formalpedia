-- Prove2me | Theorems.Thm_AvramDividend_Classical_stieltjes_cumulative_of_monotone_continuous_zero_left
-- name    : AvramDividend.Classical.stieltjes_cumulative_of_monotone_continuous_zero_left
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:24:16.076119+00:00
-- url     : https://prove2.me/theorems/cfb75c4e-f10e-4757-bc8b-3322d8d88c63
-- title:
--   Finite positive Stieltjes cumulative measure for a continuous monotone function vanishing on negatives
-- statement:
--   A continuous nondecreasing real function, identically zero on negative arguments and strictly positive on positive ones, is the cumulative distribution function of a Stieltjes measure with finite and strictly positive positive-axis cumulative masses. This is the analytic measure-construction step after an Esscher-tilted q-scale factor has been shown nondecreasing.
-- source:
--   Pinned Mathlib StieltjesFunction.measure_Iic and right-continuous monotone-function measure construction.

import Mathlib
open Filter MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stieltjes_cumulative_of_monotone_continuous_zero_left
    (f : ℝ → ℝ)
    (hmono : Monotone f)
    (hcont : Continuous f)
    (hleft : ∀ x : ℝ, x < 0 → f x = 0)
    (hpos : ∀ x : ℝ, 0 < x → 0 < f x) :
    ∃ β : Measure ℝ,
      (∀ x : ℝ, β (Iic x) = ENNReal.ofReal (f x)) ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → 0 < β (Iic x)) := by sorry
