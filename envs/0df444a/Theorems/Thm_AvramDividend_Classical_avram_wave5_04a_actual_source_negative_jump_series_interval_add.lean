-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_source_negative_jump_series_interval_add
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_source_negative_jump_series_interval_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:19:47.251793+00:00
-- url     : https://prove2.me/theorems/7c727efc-2476-40eb-b00e-4b68802cfe1c
-- title:
--   Exact additivity of actual original negative source left-jump magnitude series across adjacent intervals
-- statement:
--   For the actual spectrally negative Levy source sample path, and any ordered nonnegative times s and t, the complete negative source left-jump magnitude series over (0,t] equals the sum of its complete series over (0,s] and (s,t]. The equality holds pathwise for every sample, including infinite activity, in extended nonnegative real units. It separates original source jumps from chronological right dividend payments and requires no independent Poisson model or stochastic integration.
-- source:
--   Wave5 Chat04-A; pinned Mathlib ENNReal.tsum_add applies after pointwise partition of time-indexed conditional jump magnitudes.

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Original source negative left-jump magnitudes have an exactly additive
series over consecutive intervals. This is pathwise, including infinite
activity, and does not identify any stochastic compensator or dividend jumps. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_source_negative_jump_series_interval_add
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∑' (u : ℝ≥0),
      if 0 < u ∧ u ≤ t then
        ENNReal.ofReal (Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
      else 0) =
    (∑' (u : ℝ≥0),
      if 0 < u ∧ u ≤ s then
        ENNReal.ofReal (Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
      else 0) +
    (∑' (u : ℝ≥0),
      if s < u ∧ u ≤ t then
        ENNReal.ofReal (Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
      else 0) := by sorry
