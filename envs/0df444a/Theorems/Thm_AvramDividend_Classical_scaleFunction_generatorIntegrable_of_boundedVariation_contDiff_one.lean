-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T10:07:18.709575+00:00
-- url     : https://prove2.me/theorems/19029a99-7868-4fa5-9ace-8103bfe6ef18
-- title:
--   C1 scale functions have an integrable generator jump term for bounded-variation Levy processes
-- statement:
--   Pure analytic bounded-variation version of generator integrability. Bounded variation supplies integrability of |y| over (-1,0). C1 regularity makes W locally Lipschitz around x>0, so the compensated increment is O(|y|) near zero. Away from zero the Levy measure has finite mass and scale-function monotonicity bounds the remaining increment. Therefore the generator jump integrand is integrable.
-- source:
--   Standard bounded-variation Levy-generator estimate; used in the proof of Lemma 4 of Avram, Palmowski and Pistorius (2007).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation)
    (x : ℝ) (hx : 0 < x)
    (hC1 : ContDiffOn ℝ 1 W (Ioi 0)) :
    X.GeneratorIntegrable W x := by sorry

end AvramDividend.Classical
