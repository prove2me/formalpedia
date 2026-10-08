-- Prove2me | Theorems.Thm_AvramDividend_Classical_levyMeasure_absolutelyContinuous_of_standing_boundedVariation
-- name    : AvramDividend.Classical.levyMeasure_absolutelyContinuous_of_standing_boundedVariation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T10:05:42.199254+00:00
-- url     : https://prove2.me/theorems/abe698db-c70f-46c7-a184-c3a004adfe28
-- title:
--   Condition 3.3 forces absolute continuity in the bounded-variation branch
-- statement:
--   Under the mission's standing assumptions, Condition 3.3 says that either sigma is positive, the small-jump first moment is infinite, or the Levy measure is absolutely continuous with respect to Lebesgue measure. Bounded variation gives sigma=0 and a finite small-jump first moment, so the first two alternatives are impossible and the absolute-continuity alternative must hold.
-- source:
--   Avram, Palmowski and Pistorius (2007), condition (3.3), combined with the definition of bounded variation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem levyMeasure_absolutelyContinuous_of_standing_boundedVariation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing)
    (hbv : X.BoundedVariation) :
    X.ν ≪ volume := by sorry

end AvramDividend.Classical
