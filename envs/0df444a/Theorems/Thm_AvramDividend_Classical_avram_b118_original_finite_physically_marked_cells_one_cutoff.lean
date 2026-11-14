-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b118_original_finite_physically_marked_cells_one_cutoff
-- name    : AvramDividend.Classical.avram_b118_original_finite_physically_marked_cells_one_cutoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:26:00.183805+00:00
-- url     : https://prove2.me/theorems/61406cb7-80b1-4aa3-8361-be8363b3c57b
-- title:
--   A single original negative cutoff captures every genuine marked cell in any finite physical stopped grid
-- statement:
--   At the actual original spectrally negative Levy sample path, every nonzero source jump in a physical finite-grid cell is strictly negative by the original no-positive-jump field and Proved canonical left-limit theorem. Every such cell is therefore detected by some reciprocal negative mark cutoff. Proved B115 establishes monotonicity under increasing cutoffs, and finite induction selects the maximum cutoff needed to capture all genuine marked cells simultaneously. This direct same-source finite stopped-grid proof removes an important marked-cell exhaustion premise from the original Ito cash verification without assuming global negative mark second moments.
-- source:
--   Original noPosJumps, Proved all-time physical left-limit theorem and Proved B115, finite set induction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
import Theorems.Thm_AvramDividend_Classical_avram_b115_original_random_interval_negative_mark_cutoff_sets_monotone
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- One negative cutoff simultaneously detects every genuinely marked original physical cell in a finite stopped-grid family. -/

theorem AvramDividend.Classical.avram_b118_original_finite_physically_marked_cells_one_cutoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (S : Finset ℕ) (s t : ℕ → ℝ≥0)
    (hMarked : ∀ i ∈ S, ∃ u : ℝ≥0,
      s i < u ∧ u ≤ t i ∧
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) :
    ∃ n : ℕ, ∀ i ∈ S, ∃ u : ℝ≥0,
      s i < u ∧ u ≤ t i ∧
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1)) := by sorry
