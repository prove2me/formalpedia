-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b107_original_source_negative_jump_iff_some_cutoff_band
-- name    : AvramDividend.Classical.avram_b107_original_source_negative_jump_iff_some_cutoff_band
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T15:59:06.259206+00:00
-- url     : https://prove2.me/theorems/84d8874d-3ab3-462f-a0fd-d0edb3600a88
-- title:
--   Every genuine negative original source jump on a half-open interval is captured by some prescribed cofinal negative-jump cutoff
-- statement:
--   At fixed original Levy sample path and arbitrary physical half-open interval (s,t], a strictly negative jump X(u)-X(u-) occurs in the interval if and only if for some natural cutoff n the exact same original source jump is at most -1/(n+1). The proof uses the positive gap of any strictly negative real mark and the genuine cofinal reciprocal cutoff limit to zero. It is pathwise and does not assert global absence of positive jumps, use a separate original spectral-negativity event to identify all nonzero jumps. This is a source-exact bridge from finite negative Poisson cutoffs to physical all-negative marked-cell selection.
-- source:
--   Prescribed original negative Levy cutoffs and Mathlib tendsto_one_div_add_atTop_nhds_zero_nat.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original source negative marks are exactly the union over genuine cofinal negative cutoffs. -/

theorem AvramDividend.Classical.avram_b107_original_source_negative_jump_iff_some_cutoff_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) :
    (∃ u : ℝ≥0, s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0) ↔
    (∃ n : ℕ, ∃ u : ℝ≥0, s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))) := by sorry
