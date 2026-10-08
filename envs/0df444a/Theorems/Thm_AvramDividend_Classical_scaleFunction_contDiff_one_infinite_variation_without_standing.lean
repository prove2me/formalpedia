-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_infinite_variation_without_standing
-- name    : AvramDividend.Classical.scaleFunction_contDiff_one_infinite_variation_without_standing
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T22:37:54.579063+00:00
-- url     : https://prove2.me/theorems/cd61d678-0150-4774-8c7e-d5f3fc16b60a
-- title:
--   Infinite small-jump variation gives C1 q-scale-function regularity without first-moment standing assumptions
-- statement:
--   When the Lévy measure of a spectrally negative process has infinite absolute first moment near zero, the process has unbounded variation. Its q-scale function is C1 on the positive axis under the canonical scale-function Laplace transform. The extra first-moment Standing integrability assumption is not required for this particular unbounded variation regularity. This common analytic property implies two current milestones: C1 regularity with Standing, and derivative continuity without Standing.
-- source:
--   Chan, Kyprianou and Savov (2011), Smoothness of scale functions for spectrally negative Lévy processes; Avram, Palmowski and Pistorius (2007) condition (3.3) and Lemma 2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem scaleFunction_contDiff_one_infinite_variation_without_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ContDiffOn ℝ 1 W (Ioi 0) := by sorry

end AvramDividend.Classical
