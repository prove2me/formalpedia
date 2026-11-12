-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys120_original_admissible_dividend_rightLimit_measurable
-- name    : AvramDividend.Classical.avram_bvb_phys120_original_admissible_dividend_rightLimit_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:06:46.288084+00:00
-- url     : https://prove2.me/theorems/4704d1d8-ed21-4f91-a480-43474f6ef0dc
-- title:
--   Original admissible right-limit dividend paths are time-measurable
-- statement:
--   For every original admissible dividend strategy and each sample path, the time-indexed right limit appearing in the physical drift and reserve is measurable. This follows by identifying Avram's infimum-defined rightLimit with the Mathlib right limit of a monotone path, and using measurability of monotone functions.
-- source:
--   Original DividendStrategy rightLimit, Mathlib Monotone.rightLim, Monotone.measurable

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys120_original_admissible_dividend_rightLimit_measurable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (ω : Ω) : Measurable (fun t : ℝ≥0 => rightLimit D t ω) := by sorry
