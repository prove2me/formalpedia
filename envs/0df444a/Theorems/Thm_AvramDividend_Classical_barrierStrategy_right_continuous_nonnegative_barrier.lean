-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_nonnegative_barrier
-- name    : AvramDividend.Classical.barrierStrategy_right_continuous_nonnegative_barrier
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:13:25.13118+00:00
-- url     : https://prove2.me/theorems/11865c2a-6684-4cb0-bfaf-417066bf31b5
-- title:
--   The constant barrier dividend process is right-continuous
-- statement:
--   For each path, the cumulative barrier dividend process is right-continuous at every time. Since it is the positive part of x-a plus the running supremum of a right-continuous path, the right-hand running supremum converges to its current value. This supplies the no-right-dividend-jump condition used by the formal admissibility definition.
-- source:
--   Avram, Palmowski and Pistorius (2007), Sections 2 and 3.3; source-faithful consequence of the right-continuous Levy paths and barrier reflection formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrierStrategy_right_continuous_nonnegative_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) :
    ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun s => barrierStrategy X x a s ω) (Ici t) t := by sorry

end AvramDividend.Classical
