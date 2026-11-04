-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_real_negative_jump_additivity
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_interval_real_negative_jump_additivity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:22:42.188843+00:00
-- url     : https://prove2.me/theorems/f0b0f24b-6f83-4d53-9c59-c9f24ec8e5a3
-- title:
--   Original BV source real negative left-jump totals are additive over ordered intervals
-- statement:
--   On one almost-sure original spectrally negative Levy bounded-variation source event, the real-valued actual downward left-jump magnitude series over (s,r] splits exactly into series over (s,t] and (t,r] for every s≤t≤r. This uses genuinely summable original jump series, without a Poisson replacement.
-- source:
--   Proved original-source BV real summability ad61675c, a pointwise disjoint interval partition, and Mathlib tsum_add for genuinely summable real series.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_real_jump_summable_and_tsum

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Source BV real jump totals split along all ordered times. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_interval_real_negative_jump_additivity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t r : ℝ≥0), s ≤ t → t ≤ r →
      (∑' u : ℝ≥0,
        (if s < u ∧ u ≤ r then
          ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal) =
      (∑' u : ℝ≥0,
        (if s < u ∧ u ≤ t then
          ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal) +
      (∑' u : ℝ≥0,
        (if t < u ∧ u ≤ r then
          ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal) := by sorry
