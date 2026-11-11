-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_gated_no_upward_left_jumps
-- name    : AvramDividend.Classical.avram_a06_gated_no_upward_left_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T23:45:11.016278+00:00
-- url     : https://prove2.me/theorems/4db46a68-324b-4798-93ca-e9796a31a5a1
-- title:
--   Zero-gating a downward-jump path preserves its nonpositive left jumps
-- statement:
--   For any nonnegative-time real path on a good sample set G, replacing every path outside G by the identically zero path preserves the no-positive-left-jump property at each positive time. On the complement, left-filter uniqueness forces every possible left limit to equal zero.
-- source:
--   A06 corrected original-space modified compound-Poisson downward-jump helper.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a06_gated_no_upward_left_jumps
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (G : Set Ω)
    [DecidablePred (fun ω => ω ∈ G)]
    (hdown : ∀ ω ∈ G, ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Tendsto (fun s : ℝ≥0 => X s ω) (nhdsWithin t (Iio t)) (nhds l) →
      X t ω ≤ l) :
    ∀ (ω : Ω) (t : ℝ≥0) (l : ℝ), 0 < t →
      Tendsto (fun s : ℝ≥0 => if ω ∈ G then X s ω else 0)
        (nhdsWithin t (Iio t)) (nhds l) →
      (if ω ∈ G then X t ω else 0) ≤ l := by sorry
