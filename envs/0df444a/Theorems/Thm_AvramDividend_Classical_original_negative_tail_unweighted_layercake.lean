-- Prove2me | Theorems.Thm_AvramDividend_Classical_original_negative_tail_unweighted_layercake
-- name    : AvramDividend.Classical.original_negative_tail_unweighted_layercake
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:08:19.257452+00:00
-- url     : https://prove2.me/theorems/6c70aa26-3e35-4f03-a02c-daef6455a172
-- title:
--   Original negative-mark unweighted tail mass equals negative-jump first moment, allowing infinity
-- statement:
--   For any real measure ν supported on strictly negative jump marks, the ENNReal integral of the jump magnitude −y equals the ENNReal Lebesgue integral over positive t of the original negative tail mass ν((−∞,−t)). Both integrals may be infinite. This is the exact unweighted original-layer-cake identity, requiring no reflected auxiliary Lévy measure and no finite first moment. It supplies the infinite-activity Esscher kernel mass for pure-jump unbounded variation.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul with f(y)=−y and g(t)=1, as in Proved original_negative_levy_tail_tonelli source 4cd8a2cf; original UBV first moment Proved 2703ea95.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.original_negative_tail_unweighted_layercake
    (ν : Measure ℝ) (hSupp : ν (Ici (0 : ℝ)) = 0) :
    (∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂ν) =
      ∫⁻ t in Ioi (0 : ℝ), ν (Iio (-t)) := by sorry
