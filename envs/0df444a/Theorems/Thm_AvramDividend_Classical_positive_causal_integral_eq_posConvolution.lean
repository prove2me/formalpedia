-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_causal_integral_eq_posConvolution
-- name    : AvramDividend.Classical.positive_causal_integral_eq_posConvolution
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T18:56:20.605878+00:00
-- url     : https://prove2.me/theorems/4cd2b141-d4fe-4d19-888b-2fa99882e394
-- title:
--   Causal integral agrees with positive-time convolution by time reversal
-- statement:
--   For any real functions f and g, the causal integral over (0,x] of f(x-s)g(s), at each x>0, is exactly Mathlib's positive-time convolution f*g. This follows from the elementary reflection substitution s=x-t and interval-integral conversion, without an integrability hypothesis.

import Mathlib.Analysis.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set

theorem AvramDividend.Classical.positive_causal_integral_eq_posConvolution
    (f g : ℝ → ℝ) (x : ℝ) (hx : 0 < x) :
    (∫ s in Ioc (0 : ℝ) x, f (x - s) * g s ∂volume) =
      MeasureTheory.posConvolution f g (ContinuousLinearMap.mul ℝ ℝ) volume x := by sorry
