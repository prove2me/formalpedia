-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_hjb_of_ruin_band_mass_criterion_of_levy
-- name    : AvramDividend.Classical.avram_wave4_05_source_hjb_of_ruin_band_mass_criterion_of_levy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:34:52.812994+00:00
-- url     : https://prove2.me/theorems/6cd681f0-8f51-41f6-a199-226186509beb
-- title:
--   Full upper source HJB from explicit Levy ruin band mass without extraneous moment assumption
-- statement:
--   For original spectrally negative Levy source and strict upper reserve above a positive optimal barrier, full GeneratorIntegrable and HJB max=0 follow from the explicit finite-band compensation and discount balance. No additional Levy quadratic moment premise, but the scalar inequality remains logically necessary.
-- source:
--   Source-only finite-band overshoot bound and conditional source upper HJB.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_hjb_of_ruin_band_mass_criterion_of_levy {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hpos : 0 < (cstar W).toReal) (x : ℝ) (hx : (cstar W).toReal < x) (hmass : X.c + (X.ν).real (Ioo (-1 : ℝ) (-x)) * max 0 (1 - vcstar W x) ≤ q * vcstar W x) : X.GeneratorIntegrable (vcstar W) x ∧ max (X.generator (vcstar W) x - q * vcstar W x) (1 - deriv (vcstar W) x) = 0 := by sorry
