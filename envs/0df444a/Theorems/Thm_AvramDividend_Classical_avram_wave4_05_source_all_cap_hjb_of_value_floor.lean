-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_all_cap_hjb_of_value_floor
-- name    : AvramDividend.Classical.avram_wave4_05_source_all_cap_hjb_of_value_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:57:33.637144+00:00
-- url     : https://prove2.me/theorems/5da2355a-d730-4ac9-8460-345951bb6927
-- title:
--   All-cap original upper HJB when the candidate value exceeds one and drift is discounted
-- statement:
--   At any strict upper reserve for the original source Levy dividend candidate, including zero-cap cases, if the value is at least one and source drift is at most discounted value, the original compensated-generator domain and max HJB hold. Positive ruin-overshoot compensation is zero under the value floor.
-- source:
--   Source-only all-cap finite-band mass upper HJB and exact positive jump compensation identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_all_cap_hjb_of_value_floor {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) (hx : (cstar W).toReal < x) (hfloor : 1 ≤ vcstar W x) (hdrift : X.c ≤ q * vcstar W x) : X.GeneratorIntegrable (vcstar W) x ∧ max (X.generator (vcstar W) x - q * vcstar W x) (1 - deriv (vcstar W) x) = 0 := by sorry
