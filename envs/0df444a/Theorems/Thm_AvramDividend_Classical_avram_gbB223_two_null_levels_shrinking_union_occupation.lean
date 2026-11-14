-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB223_two_null_levels_shrinking_union_occupation
-- name    : AvramDividend.Classical.avram_gbB223_two_null_levels_shrinking_union_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:47:43.038524+00:00
-- url     : https://prove2.me/theorems/a60abfd6-29b1-442f-b458-2ef0315d00bb
-- title:
--   Two null fixed levels imply shrinking union of both boundary-band occupation measures
-- statement:
--   On a finite physical-time interval before a possibly sample-dependent fixed stopping level, if a measurable real-valued path occupies each of two prescribed real levels for zero Lebesgue time, then the union of shrinking neighbourhoods of those two levels also has occupation measure tending to zero.
-- source:
--   Original Gaussian B65 exact cutoff approximation: Proved B194 at two levels plus finite union measure bound. Combine with B221 and B222 cutoff error localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB223_two_null_levels_shrinking_union_occupation
    (f : ℝ → ℝ) (hf : Measurable f) (n : ℕ) (ρ a b : ℝ)
    (ha : volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧ f t = a} = 0)
    (hb : volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧ f t = b} = 0) :
    Tendsto (fun k : ℕ =>
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧
        (abs (f t - a) < (1 : ℝ) / ((k : ℝ) + 1) ∨
         abs (f t - b) < (1 : ℝ) / ((k : ℝ) + 1))})
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
