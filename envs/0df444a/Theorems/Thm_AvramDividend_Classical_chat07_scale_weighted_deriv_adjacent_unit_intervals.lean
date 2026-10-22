-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_adjacent_unit_intervals
-- name    : AvramDividend.Classical.chat07_scale_weighted_deriv_adjacent_unit_intervals
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T21:24:59.146653+00:00
-- url     : https://prove2.me/theorems/d8df087b-6844-4bc2-a75c-a50b5394dfa7
-- title:
--   Adjacent-unit comparison of exponentially weighted scale derivative and scale mass
-- statement:
--   For a nondecreasing q-scale function W and θ≥0, on any nonnegative a with W(a)≥0, the integral of exp(-θx) W'(x) over [a,a+1] is at most exp(2θ) times the integral of exp(-θx) W(x) over the following interval [a+1,a+2]. This is a quantitative, finite-interval comparison valid with ordinary derivative kinks, avoiding global C1 and absolute continuity. It combines accepted interval derivative mass with a weighted monotonicity lower bound. It is designed to feed an interval-exhaustion proof of global weighted derivative integrability.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_scale_weighted_deriv_adjacent_unit_intervals
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ a : ℝ) (hθ : 0 ≤ θ) (ha : 0 ≤ a) (hWa : 0 ≤ W a) :
    (∫ x in a..(a + 1), Real.exp (-(θ * x)) * deriv W x) ≤
      Real.exp (2 * θ) *
        (∫ x in (a + 1)..(a + 2), Real.exp (-(θ * x)) * W x) := by sorry
