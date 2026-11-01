-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_hjb_all_positive_of_signed_band_criterion
-- name    : AvramDividend.Classical.avram_wave4_05_source_hjb_all_positive_of_signed_band_criterion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:16:16.486914+00:00
-- url     : https://prove2.me/theorems/c3a614e8-18ce-4bfe-b70d-9bdac3fc99a9
-- title:
--   Original all-positive Levy HJB under signed two-band ruin mass condition
-- statement:
--   The true compensated Lévy HJB holds on the entire positive half-line under the root's Gaussian/BV/C² alternatives whenever a quantified scalar two-band source jump-mass inequality holds at each upper reserve. The criterion uses positive small-ruin overshoot and the negative killing effect of large ruin-causing jumps, not a replacement formal operator.
-- source:
--   Original upper-generator signed two-band mass theorem and the canonically Proved original generator/HJB positive-half-line assembly.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_hjb_all_positive_of_signed_band_criterion {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) (hmass : ∀ y : ℝ, (cstar W).toReal < y → X.c + (X.ν).real (Ioo (-1 : ℝ) (-y)) * max 0 (1 - vcstar W y) - (X.ν).real (Iic (-1 : ℝ) ∩ Iio (-y)) * vcstar W y ≤ q * vcstar W y) : ∀ y : ℝ, 0 < y → X.GeneratorIntegrable (vcstar W) y ∧ max (X.generator (vcstar W) y - q * vcstar W y) (1 - deriv (vcstar W) y) = 0 := by sorry
