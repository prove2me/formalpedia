-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_hjb_all_cap_of_ruin_overshoot_bound
-- name    : AvramDividend.Classical.avram_wave4_05_source_hjb_all_cap_of_ruin_overshoot_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:36:07.175353+00:00
-- url     : https://prove2.me/theorems/607a4fa3-c109-4b9b-980b-a45218e2da37
-- title:
--   All-cap original Levy generator HJB under exact ruin-overshoot inequality
-- statement:
--   Full original compensated generator integrability and upper-reserve HJB at any finite source optimal cap, including cstar=0, given the exact overshoot scalar bound; no extraneous Levy moment or source smoothness assumptions.
-- source:
--   Source generator formula, all-cap compensated positive part, source-only Levy finite-band integrability, and upper derivative one.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_hjb_all_cap_of_ruin_overshoot_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) (hx : (cstar W).toReal < x) (hbound : X.c + (∫ y in Iio (0 : ℝ), (Ioo (-1 : ℝ) (-x)).indicator (fun z : ℝ => max 0 (-vcstar W x - z)) y ∂X.ν) ≤ q * vcstar W x) : X.GeneratorIntegrable (vcstar W) x ∧ max (X.generator (vcstar W) x - q * vcstar W x) (1 - deriv (vcstar W) x) = 0 := by sorry
