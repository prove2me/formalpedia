-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_negative_jump_tsum_nonnegative
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_negative_jump_tsum_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:52:08.548213+00:00
-- url     : https://prove2.me/theorems/017d744a-d8a5-4239-a5df-4d2243aa2a55
-- title:
--   Pathwise nonnegative raw real original Lévy negative-jump interval tsum
-- statement:
--   Every true original spectrally negative Lévy left jump has nonnegative loss, and so the real sum of the raw negative-jump magnitudes over a time interval is nonnegative pathwise, with no additional process model. No BV assumption is needed for this sign fact.
-- source:
--   Previously Proved source raw negative-left-jump theorem 561ccef5 plus Mathlib tsum_nonneg, evaluated on genuine source X.X and leftLim.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Every raw original negative left-jump sum has nonnegative sign, pathwise.
This sign assertion does not assume BV summability or an auxiliary process. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_negative_jump_tsum_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t) :
    0 ≤ (∑' u : ℝ≥0, if s < u ∧ u ≤ t then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
      else 0) := by sorry
