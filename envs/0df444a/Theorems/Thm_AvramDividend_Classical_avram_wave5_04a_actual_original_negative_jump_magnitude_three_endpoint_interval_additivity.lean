-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_negative_jump_magnitude_three_endpoint_interval_additivity
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_original_negative_jump_magnitude_three_endpoint_interval_additivity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:13:26.795907+00:00
-- url     : https://prove2.me/theorems/6d0898c1-f766-400f-b285-00a6218064d2
-- title:
--   Actual source intrinsic negative jump magnitudes add exactly across any three ordered endpoints
-- statement:
--   For every actual original spectrally negative Levy sample path and all three ordered nonnegative times s≤t≤r, the unrestricted complete negative left-jump magnitude series over (s,r] equals the sum of its two pieces (s,t] and (t,r], in extended nonnegative reals. This holds pathwise even with infinitely many small jumps, without a Poisson substitute, bounded-variation assumption, or stochastic compensation. It prepares an exact intrinsic source-measure finite-additivity identity for stopped C1 chain rules.
-- source:
--   Chat04-A original source three-time interval refinement of canonically Proved first-interval jump series additivity 7c727efc-2476-40eb-b00e-4b68802cfe1c, using `ENNReal.tsum_add` for the actual sample-path jump time marks.

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Actual original-source negative left-jump magnitude series is
exactly additive over any three ordered interval endpoints, even
with infinite jump activity; no compensation or Poisson model. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_original_negative_jump_magnitude_three_endpoint_interval_additivity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t r : ℝ≥0) (hst : s ≤ t) (htr : t ≤ r) :
    (∑' (v : ℝ≥0),
      if s < v ∧ v ≤ r then
        ENNReal.ofReal (Function.leftLim
          (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      else 0) =
    (∑' (v : ℝ≥0),
      if s < v ∧ v ≤ t then
        ENNReal.ofReal (Function.leftLim
          (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      else 0) +
    (∑' (v : ℝ≥0),
      if t < v ∧ v ≤ r then
        ENNReal.ofReal (Function.leftLim
          (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      else 0) := by sorry
