-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_actual_source_weighted_cutoff_shift
-- name    : AvramDividend.Classical.avram_bv_jump8_actual_source_weighted_cutoff_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:35:48.512429+00:00
-- url     : https://prove2.me/theorems/56c922dc-1ac9-4c82-b640-9d9528d00297
-- title:
--   Original BV source marked negative magnitude integral commutes with integer source-path shift
-- statement:
--   Pathwise, for the same original sample and any n, the intrinsic cutoff marked-magnitude integral over the actual shifted increment path on (0,1] equals the original path marked integral over (n,n+1]. This is equality of weighted marks, stronger than merely equal counts, with strict cutoff and no zero-origin atom.
-- source:
--   Mathematical child of b879a7b0. Proved source exact marked rectangle shift ed946858 for arbitrary Borel mark set plus measure ext and nonnegative integration through marked pushforward. Do not substitute equality in distribution.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_actual_source_weighted_cutoff_shift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (n k : ℕ) :
    ((∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ (1 : ℝ≥0) ∧
        p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧
          (X.X ((n : ℝ≥0) + u) ω - X.X (n : ℝ≥0) ω) -
            Function.leftLim
              (fun v : ℝ≥0 => X.X ((n : ℝ≥0) + v) ω - X.X (n : ℝ≥0) ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          (X.X ((n : ℝ≥0) + u) ω - X.X (n : ℝ≥0) ω) -
            Function.leftLim
              (fun v : ℝ≥0 => X.X ((n : ℝ≥0) + v) ω - X.X (n : ℝ≥0) ω) u))))).toReal =
    ((∫⁻ p : ℝ≥0 × ℝ,
      if (n : ℝ≥0) < p.1 ∧ p.1 ≤ ((n + 1) : ℝ≥0) ∧
        p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))).toReal := by sorry
