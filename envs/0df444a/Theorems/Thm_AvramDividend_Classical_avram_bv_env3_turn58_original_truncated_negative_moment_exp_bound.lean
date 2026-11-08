-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn58_original_truncated_negative_moment_exp_bound
-- name    : AvramDividend.Classical.avram_bv_env3_turn58_original_truncated_negative_moment_exp_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:34:07.750965+00:00
-- url     : https://prove2.me/theorems/539b2913-fae0-4467-b9bd-3fd7c9c54bdc
-- title:
--   Original BV negative Levy truncated moment bounded by normalized exponential deficit
-- statement:
--   For the original bounded-variation spectrally negative Levy measure, the truncated negative first-moment integral is controlled by twice its normalized exponential deficit at reciprocal cutoff. The pointwise estimate is already proved in the original BV-ENV3 helper 25ad581b. Finite truncated negative-jump integrability from 05eba094 justifies integration.
-- source:
--   Proved scalar min-versus-exponential deficit bound 25ad581b, Proved finite_truncated_negative_jump_moment 05eba094, integrability and monotonicity of the real integral restricted to the original negative Levy measure X.nu; no proxy or equality-in-law substitution.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn58_original_truncated_negative_moment_exp_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ z in Iio (0 : ℝ), min ε (-z) ∂X.ν) ≤
      2 * (∫ z in Iio (0 : ℝ),
        (1 - Real.exp (ε⁻¹ * z)) / ε⁻¹ ∂X.ν) := by sorry
