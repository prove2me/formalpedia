-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_vcstar_contDiff_two
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrable_of_vcstar_contDiff_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:01:42.982973+00:00
-- url     : https://prove2.me/theorems/57de9282-7200-40fc-9c86-9a28c81e625b
-- title:
--   Generator integrability from explicit C2 regularity of the barrier value candidate
-- statement:
--   If the barrier candidate vcstar W is C2 on (0,cstar) and its normalisation factor k is nonzero, then the scale function W is C2 there. The compensated negative-jump Levy generator of W is integrable at every point of this interval. This is the explicit smoothness disjunct in the generator-integrability half of Lemma 4 and requires neither the Gaussian nor the bounded-variation hypotheses.
-- source:
--   Source-faithful analytic branch of Avram, Palmowski and Pistorius (2007), Lemma 4; follows from the proved C2-transfer and C2-generator-integrability project theorems.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrable_of_vcstar_contDiff_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvc : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal, X.GeneratorIntegrable W x := by sorry

end AvramDividend.Classical
