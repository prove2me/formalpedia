-- Prove2me | Theorems.Thm_AvramDividend_Classical_generatorIntegrable_scaleFunction_of_contDiffOn_two
-- name    : AvramDividend.Classical.generatorIntegrable_scaleFunction_of_contDiffOn_two
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:13:51.551092+00:00
-- url     : https://prove2.me/theorems/196ecce3-b56c-4bf1-83a7-99f415b4705b
-- title:
--   C2 scale-function regularity implies generator jump-integrability locally
-- statement:
--   Generic analytic lemma for the Lévy generator. Let W vanish on the negative half-line, be nonnegative and monotone on [0,∞) as supplied by IsScaleFunction, and be C² on (0,a). Then for every x∈(0,a), the compensated negative-jump generator integrand is integrable. Near y=0 a second-order Taylor remainder is O(y²), controlled by the Lévy-measure condition ∫min(1,y²)dν<∞. For jumps bounded away from zero, monotonicity bounds W(x+y) and the Lévy measure has finite mass.
-- source:
--   Standard Lévy-generator estimate; applied in the proof of Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generatorIntegrable_scaleFunction_of_contDiffOn_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a : ℝ)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x := by sorry

end AvramDividend.Classical
