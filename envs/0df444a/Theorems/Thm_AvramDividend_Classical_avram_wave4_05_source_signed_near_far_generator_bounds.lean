-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_signed_near_far_generator_bounds
-- name    : AvramDividend.Classical.avram_wave4_05_source_signed_near_far_generator_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:24:03.320204+00:00
-- url     : https://prove2.me/theorems/60cbfc59-8c89-4d98-9783-ba39603567cd
-- title:
--   Original compensated Levy generator sharp near and far ruin-mass bounds
-- statement:
--   Source signed upper-reserve generator residual bounds split at the true small-jump truncation threshold x=1: for x<1 a finite full large-jump ruin intensity appears, and for x≥1 the positive small-ruin overshoot vanishes while the exact negative strict ruin-tail intensity remains. Both source GeneratorIntegrable and residual inequality are proved with no new moments.
-- source:
--   The signed two-band original compensated-generator bound and elementary geometry of Levy jump support at the strict truncation threshold one.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_signed_near_far_generator_bounds {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) (hx : (cstar W).toReal < x) : X.GeneratorIntegrable (vcstar W) x ∧ (if x < 1 then X.generator (vcstar W) x - q * vcstar W x ≤ X.c + (X.ν).real (Ioo (-1 : ℝ) (-x)) * max 0 (1 - vcstar W x) - (X.ν).real (Iic (-1 : ℝ)) * vcstar W x - q * vcstar W x else X.generator (vcstar W) x - q * vcstar W x ≤ X.c - (X.ν).real (Iio (-x)) * vcstar W x - q * vcstar W x) := by sorry
