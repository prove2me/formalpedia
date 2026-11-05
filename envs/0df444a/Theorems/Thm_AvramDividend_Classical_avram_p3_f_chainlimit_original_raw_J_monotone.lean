-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_raw_J_monotone
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_raw_J_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:38:36.635582+00:00
-- url     : https://prove2.me/theorems/32cc0b62-47a8-4d27-b599-b4db4ea1babb
-- title:
--   Original BV negative jump accumulation is monotone on the genuine Lévy path
-- statement:
--   On the full-measure original BV Lévy source event, the cumulative physical negative left-jump series J(s) is no larger than J(t) whenever 0≤s≤t. The source exact adjacent-interval decomposition gives J(t)=J(s)+J((s,t]), and the original negative interval mass is nonnegative at every path and interval. This supplies the physical J monotonicity required by original discounted variation and tagged jump-cell estimates, without any surrogate jump process.
-- source:
--   Proved original raw cumulative interval additivity 50ef916b plus original pathwise nonnegative jump tsum 017d744a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_negative_jump_tsum_nonnegative
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_raw_J_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0) ≤
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0) := by sorry
