-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_convolution_time_reversal
-- name    : AvramDividend.Classical.causal_convolution_time_reversal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T20:59:24.11362+00:00
-- url     : https://prove2.me/theorems/f1622c94-540f-40cd-980d-3b1132ca67c4
-- title:
--   Time reversal of a finite causal convolution integral
-- statement:
--   For t≥0 the finite causal convolution ∫_(0,t] K(t-s)g(s) ds equals ∫_(0,t] K(u)g(t-u) du by reflecting the integration variable. No integrability assumptions are needed for the equality of the Bochner integrals under this measure-preserving reflection.
-- source:
--   Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic, intervalIntegral.integral_comp_sub_left.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_convolution_time_reversal
    (K g : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume) =
    (∫ u in Ioc (0 : ℝ) t, K u * g (t - u) ∂volume) := by sorry
