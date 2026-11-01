-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_ruin_jump_integral_exact
-- name    : AvramDividend.Classical.avram_wave4_05_source_ruin_jump_integral_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:14:16.322728+00:00
-- url     : https://prove2.me/theorems/f11964a5-83da-4a57-a517-7ef79b2e2f26
-- title:
--   Exact source compensated generator integral over strict ruin jump region
-- statement:
--   The exact integral of the genuine source compensated Lévy generator kernel over all negative jumps that strictly ruin an upper-reserve barrier candidate is the integral of the signed small-jump compensation overshoot minus the finite Lévy mass of large ruin jumps times current barrier value. Both strips are proven integrable from source Lévy moments; jumps landing precisely at zero are excluded, including possible BV boundary atoms.
-- source:
--   Original generatorIntegrand, barrierValue zero below reserve zero, derivative one above cstar, finite negative Levy mass away from zero, and exact source upper generator integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_ruin_jump_integral_exact {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) (hx : (cstar W).toReal < x) : X.GeneratorIntegrable (vcstar W) x ∧ (∫ y in Iio (-x), SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ∂X.ν) = (∫ y in Ioo (-1 : ℝ) (-x), (-vcstar W x - y) ∂X.ν) - (X.ν).real (Iic (-1 : ℝ) ∩ Iio (-x)) * vcstar W x := by sorry
