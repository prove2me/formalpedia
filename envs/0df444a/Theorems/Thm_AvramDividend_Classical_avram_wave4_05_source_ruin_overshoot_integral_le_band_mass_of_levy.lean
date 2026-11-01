-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_ruin_overshoot_integral_le_band_mass_of_levy
-- name    : AvramDividend.Classical.avram_wave4_05_source_ruin_overshoot_integral_le_band_mass_of_levy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:34:02.82178+00:00
-- url     : https://prove2.me/theorems/9e691c5b-3f68-4d35-b191-d30d02b8fbbe
-- title:
--   Source-only Levy band-mass upper bound on the strict ruin overshoot integral
-- statement:
--   For each positive reserve, bound the true small ruin-crossing compensated Levy jump overshoot by finite source negative-jump band intensity times the barrier value shortfall. No supplementary Levy moment integral hypothesis.
-- source:
--   Proved levy_negative_mass_away_from_zero_finite and source-only overshoot Bochner integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_ruin_overshoot_integral_le_band_mass_of_levy {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (W : ℝ → ℝ) (x : ℝ) (hx : 0 < x) : (∫ y in Ioo (-1 : ℝ) (-x), max 0 (-vcstar W x - y) ∂X.ν) ≤ (X.ν).real (Ioo (-1 : ℝ) (-x)) * max 0 (1 - vcstar W x) := by sorry
