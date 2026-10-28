-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_cumulative_origin_of_finite
-- name    : AvramDividend.Classical.esscher_cumulative_origin_of_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:30:59.328559+00:00
-- url     : https://prove2.me/theorems/5374c83e-9cb5-4693-a6c1-ff33bbcff112
-- title:
--   Finite Esscher renewal cumulative determines the continuous scale value at zero
-- statement:
--   Any finite cumulative renewal measure representing the exponentially tilted positive-axis scale function determines the scale value at zero: W(0) equals the renewal measure's cumulative mass at the origin. Uses right-continuity of the finite measure CDF and right-continuity of W, allowing the bounded-variation origin normalisation to be reduced to an atom-at-zero calculation.
-- source:
--   Canonical Esscher renewal representation from Avram, Palmowski and Pistorius (2007), https://arxiv.org/pdf/math/0702893; existing Proved rightContinuous_cumulative_toReal_of_finite.

import Theorems.Thm_AvramDividend_Classical_rightContinuous_cumulative_toReal_of_finite
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FunProp
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
open Filter Set MeasureTheory Topology

namespace AvramDividend.Classical

/-- A finite Esscher renewal CDF identifies the continuous scale value at zero. -/
theorem esscher_cumulative_origin_of_finite
    (β : Measure ℝ) (φ : ℝ) (W : ℝ → ℝ)
    (hβfin : ∀ x : ℝ, β (Set.Iic x) ≠ ⊤)
    (hW : ContinuousWithinAt W (Set.Ioi (0 : ℝ)) 0)
    (hEq : ∀ x : ℝ, 0 < x →
      Real.exp (-(φ * x)) * W x = (β (Set.Iic x)).toReal) :
    W 0 = (β (Set.Iic (0 : ℝ))).toReal := by sorry

end AvramDividend.Classical
