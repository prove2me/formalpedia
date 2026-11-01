-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_ruin_overshoot_integrable_of_levy
-- name    : AvramDividend.Classical.avram_wave4_05_source_ruin_overshoot_integrable_of_levy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:33:54.879221+00:00
-- url     : https://prove2.me/theorems/144b582c-753e-48ea-91d0-7c7e6b266e1d
-- title:
--   Exact small-ruin overshoot integrability directly from the original source Levy measure
-- statement:
--   For the original spectrally negative Levy process X, strict positive reserve x and arbitrary candidate scale W, the positive overshoot correction on the compensation crossing strip (-1,-x) is integrable with respect to the actual Levy measure, with no extraneous quadratic or first moment hypothesis. Source finite-mass-away-from-zero theorem makes the band finite; its bounded defect is Bochner integrable.
-- source:
--   Source theorem levy_negative_mass_away_from_zero_finite and the original generator compensation convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_ruin_overshoot_integrable_of_levy {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (W : ℝ → ℝ) (x : ℝ) (hx : 0 < x) : Integrable ((Ioo (-1 : ℝ) (-x)).indicator (fun y : ℝ => max 0 (-vcstar W x - y))) X.ν := by sorry
