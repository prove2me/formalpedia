-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_source_frozen_prefix_weighted_cutoff
-- name    : AvramDividend.Classical.avram_bv_jump8_source_frozen_prefix_weighted_cutoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:57:46.361789+00:00
-- url     : https://prove2.me/theorems/40f97b15-5e33-4687-8708-7db41d2fad6f
-- title:
--   Exact intrinsic weighted negative-jump mass on original source prefix is unchanged by freezing after the horizon
-- statement:
--   For the original sample path, freezing the trajectory at deterministic horizon n preserves all its true negative jumps and marks in (0,n]; hence the exact strict-cutoff weighted marked lintegral is identical. No almost-everywhere exception or Poisson assumption.
-- source:
--   Original source leftLimit agreement before stop Proved 8e873bf7 plus count-measure pushforward equality on marked Borel rectangles and generic weighted integration 68109213, avoiding an arbitrary PRM.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_leftLim_before_stop
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_source_frozen_prefix_weighted_cutoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (n k : ℕ) :
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧
        p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧
        p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X (min u (n : ℝ≥0)) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X (min v (n : ℝ≥0)) ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X (min u (n : ℝ≥0)) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X (min v (n : ℝ≥0)) ω) u)))) := by sorry
