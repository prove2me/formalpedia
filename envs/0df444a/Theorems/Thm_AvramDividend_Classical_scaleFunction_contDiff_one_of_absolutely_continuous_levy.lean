-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_absolutely_continuous_levy
-- name    : AvramDividend.Classical.scaleFunction_contDiff_one_of_absolutely_continuous_levy
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T22:22:28.484236+00:00
-- url     : https://prove2.me/theorems/c7772f90-1aa5-47a5-b145-c8a46111611a
-- title:
--   First-order scale-function smoothness for an absolutely continuous Lévy measure
-- statement:
--   A Lévy measure absolutely continuous with respect to Lebesgue measure has no atoms; the first derivative of the scale function is continuous at every positive point. This is the third branch of the canonical Condition33.
-- source:
--   Avram, Palmowski, Pistorius, arXiv:math/0702893v1, condition (3.3); Chan, Kyprianou and Savov, arXiv:0903.1467, regularity of spectrally negative Lévy scale functions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_contDiff_one_of_absolutely_continuous_levy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hac : X.ν ≪ volume) :
    ContDiffOn ℝ 1 W (Ioi 0) := by sorry
