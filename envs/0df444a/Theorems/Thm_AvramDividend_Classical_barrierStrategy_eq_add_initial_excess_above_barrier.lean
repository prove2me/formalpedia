-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_eq_add_initial_excess_above_barrier
-- name    : AvramDividend.Classical.barrierStrategy_eq_add_initial_excess_above_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:21:10.935012+00:00
-- url     : https://prove2.me/theorems/ece035bb-c53e-404d-bb43-a95bdd4a6f98
-- title:
--   Above the barrier, barrierStrategy is the initial excess payment plus the barrier strategy started at the barrier
-- statement:
--   For x>a, the formal constant barrier strategy pays x-a immediately and thereafter follows the barrier strategy started from a. Pathwise, the running supremum contains time zero and X_0=0, so it is nonnegative; hence max(0,x-a+S_t)=x-a+max(0,S_t) for every t>0. At t=0 both sides are defined to be zero.
-- source:
--   Source-neutral consequence of the formal barrierStrategy definition and X_0=0; corresponds to the initial excess payment convention in Avram, Palmowski and Pistorius (2007), Section 3.3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrierStrategy_eq_add_initial_excess_above_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (ha : 0 ≤ a) (hax : a < x) :
    barrierStrategy X x a =
      (fun t ω => if t = 0 then 0 else (x - a) + barrierStrategy X a a t ω) := by sorry

end AvramDividend.Classical
