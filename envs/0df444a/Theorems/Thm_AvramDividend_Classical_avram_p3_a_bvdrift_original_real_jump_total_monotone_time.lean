-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_real_jump_total_monotone_time
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_real_jump_total_monotone_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:56:01.614363+00:00
-- url     : https://prove2.me/theorems/0759bddb-d4be-428b-8f10-2e8f94910777
-- title:
--   Actual bounded-variation negative left-jump real total is monotone in the original time
-- statement:
--   Under original BV Lévy assumptions on one almost-sure event, the cumulative actual negative-left-jump mass over (0,t], converted from its finite ENNReal sum to a real number, is nondecreasing in t. This is a source-time structural lemma usable in proving continuity after jump removal.
-- source:
--   Original BV all-interval finite jump total e80cd41a; ENNReal.tsum_le_tsum, ENNReal.toReal_mono pinned Mathlib. No independent Poisson representation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The total actual source BV negative-jump magnitude is nondecreasing
in the genuine observation time, with its exact finite real value. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_real_jump_total_monotone_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 =>
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        ENNReal.ofReal
          (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal) := by sorry
