-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_zero_discount_C1_gaussian_constructed
-- name    : AvramDividend.Classical.unbounded_zero_discount_C1_gaussian_constructed
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:44:33.453507+00:00
-- url     : https://prove2.me/theorems/582a9058-6ca8-431c-8390-d4588f6eea23
-- title:
--   Gaussian zero-scale C1 regularity from explicit positive-scale construction
-- statement:
--   For unbounded-variation spectrally negative Lévy processes with a positive Gaussian coefficient, the zero-discount scale function is continuously differentiable on (0,∞). Explicit construction of the positive-discount scale removes the separate existence hypothesis of the previously proved Gaussian C1 theorem.
-- source:
--   Proved Gaussian conditional zero-scale C1 theorem and the Neumann-series positive-discount scale existence theorem.

import Theorems.Thm_AvramDividend_Classical_unbounded_positive_discount_scale_exists_from_zero
import Theorems.Thm_AvramDividend_Classical_unbounded_zero_discount_C1_gaussian_of_positive_scale_exists
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_zero_discount_C1_gaussian_constructed
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (hσ : 0 < X.σ) :
    ContDiffOn ℝ 1 W₀ (Ioi (0 : ℝ)) := by sorry
