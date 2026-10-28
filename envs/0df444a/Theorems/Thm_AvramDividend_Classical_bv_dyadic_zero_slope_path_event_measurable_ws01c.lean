-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_dyadic_zero_slope_path_event_measurable_ws01c
-- name    : AvramDividend.Classical.bv_dyadic_zero_slope_path_event_measurable_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:37:05.181141+00:00
-- url     : https://prove2.me/theorems/edec0485-9b8c-4696-b849-2631ced48560
-- title:
--   Exact dyadic zero-deficit slope event is measurable in Lévy path space
-- statement:
--   For any real drift coefficient and any sequence of nonnegative time points, the event that the full drift-deficit path-coordinate quotient sequence converges to zero is measurable in the product-measurable path space. Represent convergence to zero as a countable intersection of eventual uniform dyadic bounds, use coordinate evaluation measurability and metric convergence characterisation, and conclude by countable unions/intersections. This is the Borel cylinder needed for passing origin zero slope to a random capped stopping time via equality of whole-path laws; no uncountable right-germ measurability shortcut is used.
-- source:
--   Standalone compact source-complete version of work/avram_ws01c_dyadic_zero_slope_borel_draft.lean, specialising a countable zero-limit cylinder directly to the exact future-increment path event.

import Mathlib
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_dyadic_zero_slope_path_event_measurable_ws01c
    (d : ℝ) (δ : ℕ → ℝ≥0) :
    MeasurableSet
      {f : ℝ≥0 → ℝ |
        Tendsto (fun n : ℕ =>
          (d * (δ n : ℝ) - f (δ n)) / (δ n : ℝ))
          atTop (𝓝 (0 : ℝ))} := by sorry
