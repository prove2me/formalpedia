-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_weighted_signed_jump_tail_map_identity
-- name    : AvramDividend.Classical.esscher_weighted_signed_jump_tail_map_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:49:26.728967+00:00
-- url     : https://prove2.me/theorems/33ba13f8-66f6-483e-bd05-f8ebb3de9677
-- title:
--   Signed-to-magnitude Esscher weighted jump-tail identity
-- statement:
--   For any measure on real signed jumps, positive jump-magnitude threshold r and Esscher parameter φ, the exponentially weighted strict positive tail of jump magnitudes obtained under the measurable reflection y↦max(-y,0) equals the exponentially weighted strict negative tail of the original signed measure. The equality is exact and uses no regularity or Lévy assumptions. This identifies the continuous signed BV Lévy tail already Proved with the concrete positive tail-density kernel in the Esscher renewal representation.
-- source:
--   Change of variables for set lintegrals under Measure.map, the definition of withDensity, and Real.toNNReal reflection geometry.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_weighted_signed_jump_tail_map_identity
    (ν : Measure ℝ) (φ r : ℝ) (hr : 0 < r) :
    ((ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
      (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
        {z : ℝ≥0 | r < (z : ℝ)} =
    (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
      (Iio (-r)) := by sorry
