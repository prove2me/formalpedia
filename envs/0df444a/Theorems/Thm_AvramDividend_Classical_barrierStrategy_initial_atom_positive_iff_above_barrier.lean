-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_initial_atom_positive_iff_above_barrier
-- name    : AvramDividend.Classical.barrierStrategy_initial_atom_positive_iff_above_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:58:14.200798+00:00
-- url     : https://prove2.me/theorems/76e20114-0715-4437-b9ab-ca6f4d265128
-- title:
--   A positive initial dividend atom occurs exactly above the barrier
-- statement:
--   For any nonnegative capital x and barrier a, the time-zero Stieltjes atom of barrier dividends is strictly positive precisely when x>a. This complements the proved vanishing-atom equivalence and isolates the exact condition under which the strategy pays an immediate lump sum.
-- source:
--   Consequence of Proved barrierStrategy_initial_atom_zero_iff_below_barrier (49e1d867).

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_initial_atom_zero_iff_below_barrier
import Mathlib.Topology.Instances.ENNReal.Lemmas
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_initial_atom_positive_iff_above_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (ω : Ω) :
    0 < dividendMeasure (barrierStrategy X x a) ω ({0} : Set ℝ) ↔
      a < x := by sorry
