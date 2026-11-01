-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_hjb_all_positive_of_signed_ruin_criterion
-- name    : AvramDividend.Classical.avram_wave4_05_source_hjb_all_positive_of_signed_ruin_criterion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:38:02.508206+00:00
-- url     : https://prove2.me/theorems/d28befa7-9858-4391-9331-bf591b190357
-- title:
--   Full positive-reserve original Levy HJB from exact signed ruin integral and zero-landing atom criterion
-- statement:
--   Under the exact signed short-ruin integral and landing-at-zero atom scalar balance at all reserves above the optimal cap, the original source compensated Levy generator satisfies the HJB equation at every strictly positive reserve, including zero optimal cap and all three root smoothness cases. This criterion is stronger than the coarse two-band positive-mass estimate and requires neither atomlessness nor an extra first moment.
-- source:
--   Full signed upper compensated source generator bound with exact ruin integral, source positive HJB assembly, cstar finite and root's actual smoothness alternative.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_hjb_all_positive_of_signed_ruin_criterion {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) (hsigned : ∀ y : ℝ, (cstar W).toReal < y → X.c + (∫ z in Ioo (-1 : ℝ) (-y), (-vcstar W y - z) ∂X.ν) - (X.ν).real (Iic (-1 : ℝ) ∩ Iio (-y)) * vcstar W y + (X.ν).real ({-y} : Set ℝ) * (vcstar W 0 - vcstar W y + if y < 1 then y else 0) ≤ q * vcstar W y) : ∀ y : ℝ, 0 < y → X.GeneratorIntegrable (vcstar W) y ∧ max (X.generator (vcstar W) y - q * vcstar W y) (1 - deriv (vcstar W) y) = 0 := by sorry
