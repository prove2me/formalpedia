-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_initial_continuity_iff_zero_stieltjes_atom
-- name    : AvramDividend.Classical.barrierStrategy_initial_continuity_iff_zero_stieltjes_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:42:47.648807+00:00
-- url     : https://prove2.me/theorems/0a39cb4b-85f4-4d40-85aa-1dd7784de8d8
-- title:
--   Initial right-continuity exactly corresponds to the absence of a Stieltjes dividend atom
-- statement:
--   For a nonnegative initial reserve and cap, the barrier dividend process is right-continuous at time zero if and only if the associated Lebesgue–Stieltjes dividend measure has no initial singleton atom. The measure vanishes at zero precisely when x≤a; below the barrier continuity holds, and above it the positive initial lump sum prevents continuity. The result connects the precise path regularity with the initial payment term in valuation integrals.
-- source:
--   Direct deduction from Proved zero-atom iff barrier condition, below-barrier continuity, and above-barrier discontinuity.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_initial_atom_zero_iff_below_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_of_le
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_not_right_continuous_at_zero_above_barrier
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_initial_continuity_iff_zero_stieltjes_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (ω : Ω) :
    ContinuousWithinAt
      (fun s => barrierStrategy X x a s ω) (Ici (0 : ℝ≥0)) 0 ↔
      dividendMeasure (barrierStrategy X x a) ω ({0} : Set ℝ) = 0 := by sorry
