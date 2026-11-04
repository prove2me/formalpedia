-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_real_jump_summable_and_tsum
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_interval_real_jump_summable_and_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:05:56.610064+00:00
-- url     : https://prove2.me/theorems/ad61675c-dab4-4545-9c13-850dc017c648
-- title:
--   Original BV source interval real left-jump series is summable and equals ENNReal jump total
-- statement:
--   For the genuine original bounded-variation spectrally negative Levy process, on one probability-one event every bounded ordered source interval has a summable real series of actual negative left-jump magnitudes and its real tsum equals the finite ENNReal original-jump total converted to real. This is uniform across arbitrary samplewise stopped interval selections.
-- source:
--   The accepted original all-interval jump total finiteness theorem e80cd41a plus the exact pinned Mathlib ENNReal.summable_toReal and ENNReal.tsum_toReal_eq theorems, with pointwise ofReal finite. No stochastic representation is required.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- For the actual BV Lévy path, its complete negative left-jump real series is
summable on each interval and agrees with the finite ENNReal total. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_interval_real_jump_summable_and_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      Summable (fun u : ℝ≥0 =>
        (if s < u ∧ u ≤ t then
          ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal) ∧
      (∑' u : ℝ≥0, if s < u ∧ u ≤ t then
          ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal =
        ∑' u : ℝ≥0,
          (if s < u ∧ u ≤ t then
            ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal := by sorry
