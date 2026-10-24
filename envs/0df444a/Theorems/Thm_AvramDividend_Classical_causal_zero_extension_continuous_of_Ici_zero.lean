-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_zero_extension_continuous_of_Ici_zero
-- name    : AvramDividend.Classical.causal_zero_extension_continuous_of_Ici_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T06:53:03.391018+00:00
-- url     : https://prove2.me/theorems/09a54581-58af-4bc5-b630-148065a09f03
-- title:
--   Continuous zero extension of a nonnegative-time function vanishing at zero
-- statement:
--   If V is continuous on the nonnegative real axis and V(0)=0, then its indicator-based zero extension, equal to V for positive times and zero elsewhere, is continuous on the entire real line. Glue the restrictions to the closed half-lines using continuousOn.union_of_isClosed, observing agreement at the origin. This is the regularity bridge needed to apply positive-time convolution continuity after subtracting an input's boundary value.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Algebra.Indicator
open Set

theorem AvramDividend.Classical.causal_zero_extension_continuous_of_Ici_zero
    (V : ℝ → ℝ)
    (hV : ContinuousOn V (Ici (0 : ℝ)))
    (hV0 : V 0 = 0) :
    Continuous ((Ioi (0 : ℝ)).indicator V) := by sorry
