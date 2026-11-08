-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn54_original_BV_truncated_moment_small
-- name    : AvramDividend.Classical.avram_bv_env3_turn54_original_BV_truncated_moment_small
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:14:59.802564+00:00
-- url     : https://prove2.me/theorems/e1d6b0f4-fa16-4ab3-aba3-c80cb2531513
-- title:
--   Original BV Levy truncated negative-jump first moment is smaller than positive drift near zero
-- statement:
--   The actual original bounded-variation Lévy measure has finite truncated negative-jump first moment. Hence the real integral g(epsilon)=∫_{z<0}min(epsilon,-z)ν(dz) tends to zero from above. With positive drift and positive cap, choose sufficiently small positive epsilon such that g(epsilon)+q*epsilon is strictly less than the original physical drift.
-- source:
--   Proved finite_truncated_negative_jump_moment 05eba094, original X.BoundedVariation and Lévy measure integrability, dominated convergence for the integrable min(1,-z) envelope; elementary small-cap selection.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn54_original_BV_truncated_moment_small
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (C : ℝ≥0∞) (hC : 0 < C)
    (hDrift : 0 < X.drift) :
    ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε < C ∧ ε ≤ 1 ∧
      q * ε + (∫ z in Iio (0 : ℝ), min ε (-z) ∂X.ν) < X.drift := by sorry
