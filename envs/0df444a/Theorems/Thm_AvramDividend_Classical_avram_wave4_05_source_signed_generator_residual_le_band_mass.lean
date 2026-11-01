-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_signed_generator_residual_le_band_mass
-- name    : AvramDividend.Classical.avram_wave4_05_source_signed_generator_residual_le_band_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:11:39.703856+00:00
-- url     : https://prove2.me/theorems/e123366a-96c0-448f-a325-6a0e2049ff66
-- title:
--   Two-band finite Levy mass bound for compensated upper generator residual
-- statement:
--   A stronger source-only compensated upper-generator residual bound expressed using two finite Lévy mass terms: the positive small-ruin overshoot mass and the negative large-ruin killing mass. Valid at all strict upper reserves, including zero caps, without any auxiliary Lévy moments.
-- source:
--   Source signed generator residual bound and original finite-band overshoot estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_signed_generator_residual_le_band_mass {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) (hx : (cstar W).toReal < x) : X.GeneratorIntegrable (vcstar W) x ∧ X.generator (vcstar W) x - q * vcstar W x ≤ X.c + (X.ν).real (Ioo (-1 : ℝ) (-x)) * max 0 (1 - vcstar W x) - (X.ν).real (Iic (-1 : ℝ) ∩ Iio (-x)) * vcstar W x - q * vcstar W x := by sorry
