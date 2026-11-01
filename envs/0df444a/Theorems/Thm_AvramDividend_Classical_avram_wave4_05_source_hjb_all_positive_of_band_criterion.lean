-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_hjb_all_positive_of_band_criterion
-- name    : AvramDividend.Classical.avram_wave4_05_source_hjb_all_positive_of_band_criterion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:46:06.681314+00:00
-- url     : https://prove2.me/theorems/a1e458bc-18a8-46dd-9c7f-29d2bfbc1786
-- title:
--   Full source HJB on positive reserves from genuine Levy band compensation criterion and root smoothness
-- statement:
--   Under exactly the original source standing, scale, discount and root smoothness assumptions, plus an explicit uniform source Levy finite-band compensation inequality above the optimal cap, the original compensated generator is integrable and full max HJB=0 at all positive reserves, including below, at, and above the cap and the zero-cap case.
-- source:
--   The canonically Proved vcstar_hjb_all_positive_of_generator bridge and all-cap source Levy ruin-band HJB criterion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_hjb_all_positive_of_band_criterion {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) (hmass : ∀ y : ℝ, (cstar W).toReal < y → X.c + (X.ν).real (Ioo (-1 : ℝ) (-y)) * max 0 (1 - vcstar W y) ≤ q * vcstar W y) : ∀ y : ℝ, 0 < y → X.GeneratorIntegrable (vcstar W) y ∧ max (X.generator (vcstar W) y - q * vcstar W y) (1 - deriv (vcstar W) y) = 0 := by sorry
