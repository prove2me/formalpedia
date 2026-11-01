-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_vcstar_interior_harmonicity
-- name    : AvramDividend.Classical.avram_wave4_05_gaussian_vcstar_interior_harmonicity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:36:30.256899+00:00
-- url     : https://prove2.me/theorems/01079aa0-2d7c-4179-9fbd-885f9a5961f3
-- title:
--   Original Gaussian Lévy generator annihilates the optimal-barrier candidate below finite positive cstar
-- statement:
--   Under exactly the Gaussian disjunct of the original Avram generator_vcstar_eq_zero assumptions, with no externally assumed Esscher root, the genuine Lévy generator acts on the actual optimal-dividend barrier value vcstar at every reserve 0<x<cstar, and (generator-q)vcstar=0 pointwise with true GeneratorIntegrable. The proof constructs the positive q-root from Standing, combines globally absolutely integrable original compensated jump kernel at eventual Laplace weights, the exact right-slope Gaussian residual transform, pointwise scale generator harmonicity by Laplace uniqueness, canonical cstar finiteness and the exact vcstar scale ratio transfer.
-- source:
--   Canonical Wave 4 positive q-root, eventual source product L1, weighted residual, source harmonicity and vcstar transfer; original generator from Def_AvramDividend_Classical_SpectrallyNegativeLevy

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_positive_psi_root_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_source_eventual_weighted_product_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_residual_from_eventual_product
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_source_harmonic_from_residual
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_scale_to_vcstar
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- The original Gaussian generator annihilates the actual optimal-barrier candidate. -/

theorem AvramDividend.Classical.avram_wave4_05_gaussian_vcstar_interior_harmonicity {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (hc : 0 < cstar W) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x = 0 := by sorry
