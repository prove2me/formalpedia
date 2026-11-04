-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_jump_drift_eq_generator_sub_physical_drift
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_jump_drift_eq_generator_sub_physical_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:39:22.471844+00:00
-- url     : https://prove2.me/theorems/f5f432d2-8953-44bf-9dc6-68a42e02cdd8
-- title:
--   Original bounded-variation Lévy jump drift equals physical generator minus deterministic drift
-- statement:
--   On the genuine original bounded-variation spectrally negative Lévy process with the source's original measure X.ν and explicit X.GeneratorIntegrable w u, identify the predictable jump-compensator drift exactly as X.generator w u minus the physical BV drift X.drift·w'(u). Use the already Proved original physical generator representation; impose no untruncated large-negative-jump first moment and no surrogate compensator process. This is a direct assembly interface for P3-A deterministic drift and P3-C controlled BV chain rule.
-- source:
--   Proved AvramDividend.Classical.boundedVariation_generator_physical_drift_representation (c8ba98f0)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_jump_drift_eq_generator_sub_physical_drift {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (w : ℝ → ℝ) (u : ℝ) (hGen : X.GeneratorIntegrable w u) : (∫ z in Iio (0 : ℝ), w (u + z) - w u ∂X.ν) = X.generator w u - X.drift * deriv w u := by sorry
