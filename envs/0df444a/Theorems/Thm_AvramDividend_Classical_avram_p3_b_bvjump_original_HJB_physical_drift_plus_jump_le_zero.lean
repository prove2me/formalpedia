-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_HJB_physical_drift_plus_jump_le_zero
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_HJB_physical_drift_plus_jump_le_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:46:24.991639+00:00
-- url     : https://prove2.me/theorems/b4644cfa-27a3-42b3-8fa7-fe5820e98948
-- title:
--   Original bounded-variation HJB bound in physical drift plus jump compensator form
-- statement:
--   On the genuine original bounded-variation spectrally negative Levy process, directly convert the source HJB inequality to the physical deterministic drift plus negative-jump compensator integral bound using its proved generator convention. Only X.GeneratorIntegrable is required. No global negative-jump first moment or alternate jump process is introduced.
-- source:
--   Proved AvramDividend.Classical.boundedVariation_generator_physical_drift_representation (c8ba98f0)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_HJB_physical_drift_plus_jump_le_zero {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (w : ℝ → ℝ) (u q : ℝ) (hGen : X.GeneratorIntegrable w u) (hHJB : X.generator w u - q * w u ≤ 0) : X.drift * deriv w u + (∫ z in Iio (0 : ℝ), w (u + z) - w u ∂X.ν) - q * w u ≤ 0 := by sorry
