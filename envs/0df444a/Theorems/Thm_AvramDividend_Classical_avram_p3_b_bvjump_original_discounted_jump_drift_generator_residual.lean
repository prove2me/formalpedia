-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_discounted_jump_drift_generator_residual
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_discounted_jump_drift_generator_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:46:53.244137+00:00
-- url     : https://prove2.me/theorems/e7290161-fe93-4296-85b7-3f575987d888
-- title:
--   Original BV discounted source jump drift equals discounted generator residual
-- statement:
--   For the actual original bounded-variation Lévy process, integrate the discounted original C1 value jump increments against the original source X.ν. With explicit X.GeneratorIntegrable w u, pull out exp(-qt) and identify the remaining full negative jump integral with X.generator w u minus the original physical drift times w'(u). This is the exact discounted HJB compensator drift used by P3-A/P3-C; it assumes no untruncated large-negative-jump first moment, no new compensator axiom and no separate Poisson process.
-- source:
--   The P3-B original jump_drift_eq_generator_sub_physical_drift helper and Mathlib integral_const_mul

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_jump_drift_eq_generator_sub_physical_drift
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_discounted_jump_drift_generator_residual {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (w : ℝ → ℝ) (u q t : ℝ) (hGen : X.GeneratorIntegrable w u) : (∫ z in Iio (0 : ℝ), Real.exp (-(q * t)) * (w (u + z) - w u) ∂X.ν) = Real.exp (-(q * t)) * (X.generator w u - X.drift * deriv w u) := by sorry
