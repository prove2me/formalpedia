-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_hjb_of_ruin_overshoot_integral_bound_of_levy
-- name    : AvramDividend.Classical.avram_wave4_05_source_hjb_of_ruin_overshoot_integral_bound_of_levy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:34:02.647269+00:00
-- url     : https://prove2.me/theorems/857b0e29-f87e-44d6-a768-616e695a0ef5
-- title:
--   Source-generator full upper HJB under exact compensated overshoot inequality, no extra moments
-- statement:
--   For the actual spectrally negative source process and strictly positive cap, original generator compensated-kernel integrability and max HJB at any strict upper reserve follow from the exact finite source ruin-overshoot integral scalar inequality. No supplementary Levy moment assumption; this is a genuine conditional HJB, not a claim that the sign follows unconditionally.
-- source:
--   Original source generator formula, positive-part identity, and levy_negative_mass_away_from_zero_finite.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_hjb_of_ruin_overshoot_integral_bound_of_levy {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hpos : 0 < (cstar W).toReal) (x : ℝ) (hx : (cstar W).toReal < x) (hbound : X.c + (∫ y in Iio (0 : ℝ), (Ioo (-1 : ℝ) (-x)).indicator (fun z : ℝ => max 0 (-vcstar W x - z)) y ∂X.ν) ≤ q * vcstar W x) : X.GeneratorIntegrable (vcstar W) x ∧ max (X.generator (vcstar W) x - q * vcstar W x) (1 - deriv (vcstar W) x) = 0 := by sorry
