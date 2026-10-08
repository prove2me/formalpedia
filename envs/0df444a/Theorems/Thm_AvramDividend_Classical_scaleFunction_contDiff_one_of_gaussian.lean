-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
-- name    : AvramDividend.Classical.scaleFunction_contDiff_one_of_gaussian
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T22:22:21.41383+00:00
-- url     : https://prove2.me/theorems/14dc9d4c-844a-424f-ab1e-e90bfda93f2f
-- title:
--   First-order scale-function smoothness from a positive Gaussian coefficient
-- statement:
--   The Gaussian component yields positive-axis C1 regularity of the q scale function through the continuous potential density and Brownian smoothing; this is one source-faithful branch of Condition33.
-- source:
--   Avram, Palmowski, Pistorius, arXiv:math/0702893v1, condition (3.3); Chan, Kyprianou and Savov, arXiv:0903.1467, regularity of spectrally negative Lévy scale functions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_contDiff_one_of_gaussian
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ContDiffOn ℝ 1 W (Ioi 0) := by sorry
