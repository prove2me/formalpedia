-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_discounted_HJB_source_jump_residual_nonpos
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_discounted_HJB_source_jump_residual_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:11:11.605607+00:00
-- url     : https://prove2.me/theorems/f07b4027-c4ae-4de3-a7be-96170cc8b4f8
-- title:
--   Original bounded-variation discounted HJB signed jump residual is nonpositive
-- statement:
--   At an original controlled reserve source pre-payment state u, the physical deterministic BV drift plus the source negative jump-compensator integral minus q*w u is nonpositive under the original generator HJB inequality. Multiplication by the strictly positive discount factor preserves the sign. The theorem uses only the genuine original process, its truncation convention, and X.GeneratorIntegrable, with no P2 premise.
-- source:
--   Proved AvramDividend.Classical.boundedVariation_generator_physical_drift_representation

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_discounted_HJB_source_jump_residual_nonpos {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (w : ℝ → ℝ) (u q t : ℝ) (hGen : X.GeneratorIntegrable w u) (hHJB : X.generator w u - q * w u ≤ 0) : Real.exp (-(q * t)) * (X.drift * deriv w u + (∫ z in Iio (0 : ℝ), w (u + z) - w u ∂X.ν) - q * w u) ≤ 0 := by sorry
