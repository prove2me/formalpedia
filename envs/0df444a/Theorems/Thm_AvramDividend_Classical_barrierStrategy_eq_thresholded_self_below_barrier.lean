-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_eq_thresholded_self_below_barrier
-- name    : AvramDividend.Classical.barrierStrategy_eq_thresholded_self_below_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:21:48.827648+00:00
-- url     : https://prove2.me/theorems/d1d5fd7f-7d74-43b9-b734-0c602bee2fa4
-- title:
--   Below the barrier, the barrier strategy is a thresholded transform of the strategy started at the barrier
-- statement:
--   For 0<=x<=a, the barrier dividend process started below the barrier is obtained by thresholding the barrier process started at a: D^{x,a}_t=max(0,D^{a,a}_t-(a-x)). At t=0 both sides are zero. For t>0, the running supremum contains X_0=0 and is nonnegative, so D^{a,a}_t equals that supremum and the identity is algebraic.
-- source:
--   Source-neutral consequence of the formal barrierStrategy definition and X_0=0; compatible with the constant-barrier reflection construction in Avram, Palmowski and Pistorius (2007), Section 3.3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrierStrategy_eq_thresholded_self_below_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) (hxa : x ≤ a) :
    barrierStrategy X x a =
      (fun t ω => max 0 (barrierStrategy X a a t ω - (a - x))) := by sorry

end AvramDividend.Classical
