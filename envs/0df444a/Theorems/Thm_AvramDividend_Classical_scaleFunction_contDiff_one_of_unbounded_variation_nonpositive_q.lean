-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_unbounded_variation_nonpositive_q
-- name    : AvramDividend.Classical.scaleFunction_contDiff_one_of_unbounded_variation_nonpositive_q
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T11:03:21.202965+00:00
-- url     : https://prove2.me/theorems/8b23cd38-7b0a-4469-bfb1-90feef46733d
-- title:
--   The q-scale function of a spectrally negative Levy process of unbounded variation is continuously differentiable on the positive half-line in the non-positive-discount regime
-- statement:
--   The companion of the unbounded-variation smoothness theorem in the regime of a non-positive discount parameter q. When q ≤ 0 the scale function is the inverse Laplace transform of (psi theta - q) inverse, whose poles lie in the closed negative half-line, so the scale function is a sum of exponentially decaying terms and is continuously differentiable on the strictly positive half-line. This statement carries the hypothesis q ≤ 0 explicitly, so together with the positive-discount regime it closes the unrestricted q-scale function smoothness theorem scaleFunction_contDiff_one_of_unbounded_variation, which states the same conclusion without a sign hypothesis on q.
-- source:
--   Chan, Kyprianou and Savov, Smoothness of scale functions for spectrally negative Levy processes (2011), the q ≤ 0 regime of the unbounded-variation smoothness statement, obtained from the Wiener-Hopf factorization with the negative root of the Laplace exponent. This is the non-positive-discount half of the decomposition of scaleFunction_contDiff_one_of_unbounded_variation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_contDiff_one_of_unbounded_variation_nonpositive_q
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq0 : q ≤ 0) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ContDiffOn ℝ 1 W (Ioi 0) := by sorry
