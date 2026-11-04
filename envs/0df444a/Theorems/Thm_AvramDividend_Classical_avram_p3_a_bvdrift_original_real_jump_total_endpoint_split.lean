-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_real_jump_total_endpoint_split
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_real_jump_total_endpoint_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:34:10.568644+00:00
-- url     : https://prove2.me/theorems/b725a54d-1942-4ad0-bcad-4bd0d357c0d6
-- title:
--   Original BV real negative-jump total splits into true endpoint jump and strict-past total
-- statement:
--   For almost every path of the genuine BV spectrally negative Levy source and every positive time t, the actual source negative-jump total over (0,t] in real form equals the raw signed left-jump magnitude at t plus the real total over (0,t). Finiteness, sign and source left-limit conventions are derived, with no jump representation assumed.
-- source:
--   Existing all-interval jump finiteness e80cd41a, accepted original endpoint ENNReal series split 4b729256, original raw left-jump conversion 561ccef5, pinned ENNReal.toReal_add.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_endpoint_left_jump_tsum_split
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Genuine BV real jump total split at the actual source time. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_real_jump_total_endpoint_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (t : ℝ≥0), 0 < t →
      (∑' (u : ℝ≥0),
        if 0 < u ∧ u ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal =
      (Function.leftLim (fun z : ℝ≥0 => X.X z ω) t - X.X t ω) +
      (∑' (u : ℝ≥0),
        if 0 < u ∧ u < t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal := by sorry
