-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation
-- name    : AvramDividend.Classical.scaleFunction_contDiffOn_one_of_boundedVariation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:13:54.343322+00:00
-- url     : https://prove2.me/theorems/d42981f3-c381-4abf-9c4e-fd654949db9e
-- title:
--   Bounded-variation q-scale functions are C1 away from zero under Condition 3.3
-- statement:
--   Regularity theorem used in the bounded-variation branch of Lemma 4. Under the standing Condition (3.3), bounded variation forces σ=0 and finite small-jump first moment, so the remaining Condition (3.3) alternative is absolute continuity of the Lévy measure. The source's scale-function regularity result then gives W∈C¹(0,∞).
-- source:
--   Avram, Palmowski and Pistorius (2007), Condition (3.3) and scale-function smoothness discussion around pp. 5 and 14.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_contDiffOn_one_of_boundedVariation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation) :
    ContDiffOn ℝ 1 W (Ioi 0) := by sorry

end AvramDividend.Classical
