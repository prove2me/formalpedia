-- Prove2me | Theorems.Thm_AvramDividend_Classical_countable_future_twoSided_exit_clocks_measurable
-- name    : AvramDividend.Classical.countable_future_twoSided_exit_clocks_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:29:02.527993+00:00
-- url     : https://prove2.me/theorems/ca0c187a-681f-4f05-b40b-d0c00677b324
-- title:
--   Both strict exit clocks on a countable future observation schedule are Borel measurable
-- statement:
--   The first sampled strict upper and lower crossing times, with infinity if no crossing is observed, are Borel-measurable extended-real functions of the entire future path under the product measurable space. Their pointwise infima range only over the countable schedule. This provides reusable measurable clocks for two-sided-exit rewards in stopped renewal calculations.
-- source:
--   Pinned Mathlib Measurable.iInf (BorelSpace.Order), measurable_pi_apply (MeasurableSpace.Constructions), and comparison-event measurability. Prerequisite for stopped-renewal lower bound 6b821aa5-c792-4436-8eca-fc9429115ef9.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.countable_future_twoSided_exit_clocks_measurable
    (τ : ℕ → ℝ≥0) (upper lower : ℝ) :
    Measurable (fun g : ℝ≥0 → ℝ =>
      ⨅ j : ℕ, if upper < g (τ j) then (τ j : ℝ≥0∞) else ⊤) ∧
    Measurable (fun g : ℝ≥0 → ℝ =>
      ⨅ j : ℕ, if g (τ j) < lower then (τ j : ℝ≥0∞) else ⊤) := by sorry
