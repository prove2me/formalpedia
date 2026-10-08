-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_infinite_variation
-- name    : AvramDividend.Classical.scaleFunction_contDiff_one_of_infinite_variation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T22:22:23.186044+00:00
-- url     : https://prove2.me/theorems/00b5c835-6b84-43ff-99b9-115f53493356
-- title:
--   First-order scale-function smoothness from infinite small-jump variation
-- statement:
--   Infinite small-jump variation yields C1 regularity of the q scale function on the strictly positive half-line; this isolates the non-Gaussian unbounded-variation branch of Condition33.
-- source:
--   Avram, Palmowski, Pistorius, arXiv:math/0702893v1, condition (3.3); Chan, Kyprianou and Savov, arXiv:0903.1467, regularity of spectrally negative Lévy scale functions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_contDiff_one_of_infinite_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ContDiffOn ℝ 1 W (Ioi 0) := by sorry
