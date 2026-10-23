-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_shift_indicator_window
-- name    : AvramDividend.Classical.causal_shift_indicator_window
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:11:29.40258+00:00
-- url     : https://prove2.me/theorems/d7d50081-0897-4fc5-a5ff-fbcdc2b53a42
-- title:
--   Shifted causal indicator localises a finite integration window
-- statement:
--   For 0≤u≤x, integrating over t in (0,x] the shifted function g(t-u) cut off to (0,x] equals integrating g(t-u) directly over (u,x]. This follows from the support of the causal indicator and intersection of the two time intervals.
-- source:
--   Mathlib.MeasureTheory.Integral.Bochner.Set, setIntegral_congr_fun and setIntegral_indicator.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_shift_indicator_window
    (g : ℝ → ℝ) (u x : ℝ) (hu : 0 ≤ u) (hux : u ≤ x) :
    (∫ t in Ioc (0 : ℝ) x,
      ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume) =
    (∫ t in Ioc u x, g (t - u) ∂volume) := by sorry
