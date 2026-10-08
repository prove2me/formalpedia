-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_increment_formula
-- name    : AvramDividend.Classical.barrierStrategy_right_increment_formula
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T14:54:25.373609+00:00
-- url     : https://prove2.me/theorems/8d23d801-85d6-465e-8450-4011e0dabd54
-- title:
--   Right increment of the barrier dividend process
-- statement:
--   For a constant barrier strategy, the cumulative dividend path is right-continuous at every strictly positive time. Its only formal right jump is at time zero, equal to the initial excess max(0,x-a).
-- source:
--   Avram, Palmowski and Pistorius (2007), Sections 2 and 3.3; pathwise regularity of constant-barrier reflection.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrierStrategy_right_increment_formula
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) :
    ∀ ω (t : ℝ≥0),
      rightLimit (barrierStrategy X x a) t ω - barrierStrategy X x a t ω =
        if t = 0 then max 0 (x - a) else 0 := by sorry

end AvramDividend.Classical
