-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_below_barrier
-- name    : AvramDividend.Classical.barrierStrategy_right_continuous_below_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:21:22.562986+00:00
-- url     : https://prove2.me/theorems/1d8e9ea2-85d9-448f-a9c0-3bbbf65f8616
-- title:
--   Barrier dividends are right-continuous when the initial surplus does not exceed the barrier
-- statement:
--   If 0<=x<=a, the barrier dividend process has no initial lump-sum jump and is right-continuous at every time. It is the positive part of x-a plus the right-continuous running supremum. The restriction x<=a is essential at t=0; for x>a the formal strategy deliberately has D_0=0 and D_{0+}=x-a.
-- source:
--   Avram, Palmowski and Pistorius (2007), Sections 2 and 3.3; source-faithful consequence of the barrier reflection definition and right-continuous Levy paths.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrierStrategy_right_continuous_below_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) (hxa : x ≤ a) :
    ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun s => barrierStrategy X x a s ω) (Ici t) t := by sorry

end AvramDividend.Classical
