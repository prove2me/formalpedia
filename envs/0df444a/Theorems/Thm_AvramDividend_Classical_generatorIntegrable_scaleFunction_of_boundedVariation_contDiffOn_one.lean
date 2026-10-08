-- Prove2me | Theorems.Thm_AvramDividend_Classical_generatorIntegrable_scaleFunction_of_boundedVariation_contDiffOn_one
-- name    : AvramDividend.Classical.generatorIntegrable_scaleFunction_of_boundedVariation_contDiffOn_one
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:14:19.193979+00:00
-- url     : https://prove2.me/theorems/8e9b9fb1-ecd1-4cbd-9715-3b03e5864f85
-- title:
--   C1 scale-function regularity implies generator jump-integrability in bounded variation
-- statement:
--   Generic bounded-variation Lévy-generator estimate. If W has the scale-function support/monotonicity properties and is C¹ on (0,a), then the compensated generator jump integrand is integrable at x∈(0,a) when X has bounded variation. For small negative jumps the first-order remainder is O(|y|), which is integrable because bounded variation gives ∫_{(-1,0)}|y|dν<∞; jumps away from zero again have finite Lévy mass.
-- source:
--   Standard bounded-variation Lévy-generator estimate; applied in Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generatorIntegrable_scaleFunction_of_boundedVariation_contDiffOn_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a : ℝ) (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a)) :
    ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x := by sorry

end AvramDividend.Classical
