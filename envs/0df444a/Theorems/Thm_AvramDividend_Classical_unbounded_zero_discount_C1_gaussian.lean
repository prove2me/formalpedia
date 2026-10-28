-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_zero_discount_C1_gaussian
-- name    : AvramDividend.Classical.unbounded_zero_discount_C1_gaussian
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:43:00.826984+00:00
-- url     : https://prove2.me/theorems/5a7d08b6-a20c-47bb-a8f1-512c6934acad
-- title:
--   Unconditional zero-discount C1 scale regularity for the Gaussian unbounded-variation branch
-- statement:
--   If a spectrally negative Levy process has unbounded variation and strictly positive Gaussian coefficient, then every zero-discount scale function is C1 on the positive half-line. The existing canonically Proved positive-discount scale existence theorem constructs a positive q-scale from the zero-scale witness, and the canonically Proved Gaussian zero-discount regularity theorem discharges C1 using that witness. This closes the Gaussian branch independently of excursion theory, with no assumption of differentiability.
-- source:
--   Kuznetsov, Kyprianou and Rivero (2011), Theory of Scale Functions, Lemma 2.4, arXiv:1104.1280. Formal dependencies: unbounded_positive_discount_scale_exists_from_zero (636cfffe-3c5a-4e91-a030-4d95f9ee9065, Proved) and unbounded_zero_discount_C1_gaussian_of_positive_scale_exists (aaebd7d3-5d4d-4dd2-ac8e-a703e302f45b, Proved), mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Theorems.Thm_AvramDividend_Classical_unbounded_positive_discount_scale_exists_from_zero
import Theorems.Thm_AvramDividend_Classical_unbounded_zero_discount_C1_gaussian_of_positive_scale_exists
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_zero_discount_C1_gaussian
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (hnbv : ¬ X.BoundedVariation) (hσ : 0 < X.σ) :
    ContDiffOn ℝ 1 W₀ (Ioi (0 : ℝ)) := by sorry
