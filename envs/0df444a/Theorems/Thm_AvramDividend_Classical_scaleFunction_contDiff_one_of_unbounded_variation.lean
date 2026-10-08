-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_unbounded_variation
-- name    : AvramDividend.Classical.scaleFunction_contDiff_one_of_unbounded_variation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T07:13:40.20605+00:00
-- url     : https://prove2.me/theorems/fa33a1e6-0c21-4ccf-a1ca-97118c5fb0be
-- title:
--   The q-scale function is C1 on the positive half-line for every unbounded-variation process
-- statement:
--   For a spectrally negative Lévy process of unbounded variation, every q-scale function is continuously differentiable on the strictly positive half-line. This is the standard unbounded-variation smoothness theorem and does not require the additional Condition33 alternatives. It replaces separate Gaussian and infinite-small-jump C1 leaves in the Avram mission by their natural common theorem.
-- source:
--   Chan, Kyprianou and Savov, Smoothness of scale functions for spectrally negative Lévy processes (2011); standard formulation also stated as Theorem 4.2(i) in Kyprianou-related scale-function references: unbounded variation implies W^(q) is C1 on (0,infinity).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_contDiff_one_of_unbounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ContDiffOn ℝ 1 W (Ioi 0) := by sorry
