-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_signed_generator_residual_bound
-- name    : AvramDividend.Classical.avram_wave4_05_source_signed_generator_residual_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:10:48.651874+00:00
-- url     : https://prove2.me/theorems/f79f9b86-1595-456b-b94b-7ddc30bf5391
-- title:
--   Original Levy generator residual bound with finite large-ruin killing measure
-- statement:
--   For the genuine original source Lévy generator of the barrier candidate at every strict upper reserve, integrability holds and the generator residual is bounded by source drift plus positive small-ruin overshoot less the exact finite large-ruin killing intensity times current barrier value and less q times current value. This handles zero and positive optimal caps and any Lévy atom at a jump landing exactly on reserve zero.
-- source:
--   Original compensated generator, original source GeneratorIntegrable theorem, all-cap signed jump bound and source finite negative Levy mass away from zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_signed_generator_residual_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) (hx : (cstar W).toReal < x) : X.GeneratorIntegrable (vcstar W) x ∧ X.generator (vcstar W) x - q * vcstar W x ≤ X.c + (∫ y in Ioo (-1 : ℝ) (-x), max 0 (-vcstar W x - y) ∂X.ν) - (X.ν).real (Iic (-1 : ℝ) ∩ Iio (-x)) * vcstar W x - q * vcstar W x := by sorry
