-- Prove2me | Theorems.Thm_AvramDividend_Classical_origin_crossing_strip_norm_integral_bound
-- name    : AvramDividend.Classical.origin_crossing_strip_norm_integral_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T16:25:26.37272+00:00
-- url     : https://prove2.me/theorems/36b53f5a-b481-4f09-9f12-64bb5923c0fd
-- title:
--   Quadratic boundary-layer integral bound from a linear negative-jump estimate
-- statement:
--   For y<0, if an integrable real state error f(x) has magnitude at most C|y| for all states 0<x<|y| crossed by the jump, then its absolute integral over those states is at most C y². This is the general bound needed to convert first-order origin-crossing scale-function errors into the quadratic Lévy-moment envelope used in global Fubini.
-- source:
--   Lebesgue interval-volume identity and integral monotonicity, for the Avram Dividend compensated generator boundary layer.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem origin_crossing_strip_norm_integral_bound
    (f : ℝ → ℝ) (y C : ℝ) (hy : y < 0)
    (hf : IntegrableOn (fun x : ℝ => |f x|) (Ioo 0 (-y)))
    (hbound : ∀ x ∈ Ioo (0 : ℝ) (-y), |f x| ≤ C * (-y)) :
    (∫ x in Ioo (0 : ℝ) (-y), |f x|) ≤ C * y ^ 2 := by sorry

end AvramDividend.Classical
