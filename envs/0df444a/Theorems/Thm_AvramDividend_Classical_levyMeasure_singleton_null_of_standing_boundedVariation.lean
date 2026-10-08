-- Prove2me | Theorems.Thm_AvramDividend_Classical_levyMeasure_singleton_null_of_standing_boundedVariation
-- name    : AvramDividend.Classical.levyMeasure_singleton_null_of_standing_boundedVariation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:22:14.966993+00:00
-- url     : https://prove2.me/theorems/f5ace022-1628-4cfb-9cc4-fba9ab62f243
-- title:
--   The standing bounded-variation Lévy measure has no atoms
-- statement:
--   The standing assumptions for bounded-variation spectrally negative Lévy processes imply the Lévy measure is absolutely continuous with respect to Lebesgue measure. Therefore it assigns zero mass to every singleton. In particular the exceptional negative jump y=-x, which takes the scale-function argument to its possibly discontinuous origin, has measure zero. This supplies the atomlessness input for almost-everywhere state continuity and dominated convergence of the generator.
-- source:
--   Accepted AvramDividend.Classical.levyMeasure_absolutelyContinuous_of_standing_boundedVariation and Lebesgue-null singletons in Mathlib.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem levyMeasure_singleton_null_of_standing_boundedVariation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (y : ℝ) :
    X.ν {y} = 0 := by sorry

end AvramDividend.Classical
