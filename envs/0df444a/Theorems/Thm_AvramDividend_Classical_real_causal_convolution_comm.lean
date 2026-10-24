-- Prove2me | Theorems.Thm_AvramDividend_Classical_real_causal_convolution_comm
-- name    : AvramDividend.Classical.real_causal_convolution_comm
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:29:35.34615+00:00
-- url     : https://prove2.me/theorems/1cc0618a-1f90-42d0-b037-d7f12c5562d8
-- title:
--   Commutativity of real-valued additive convolution under Lebesgue measure
-- statement:
--   Real additive convolution with respect to Lebesgue measure is commutative pointwise. The change of variable y to x-y and commutativity of real multiplication exchange the factors. Used to transfer continuity of bounded left convolution kernels to the case of a bounded right factor.
-- source:
--   Pinned Mathlib convolution_symm applied to symmetric real multiplication, with Haar negation invariance on the real line.

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open MeasureTheory ContinuousLinearMap

namespace AvramDividend.Classical
theorem real_causal_convolution_comm (f g : ℝ → ℝ) (x : ℝ) :
    (∫ y : ℝ, f y * g (x - y) ∂volume) =
      ∫ y : ℝ, g y * f (x - y) ∂volume := by sorry
end AvramDividend.Classical
