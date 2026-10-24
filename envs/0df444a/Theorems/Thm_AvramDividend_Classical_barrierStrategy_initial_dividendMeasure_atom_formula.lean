-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_initial_dividendMeasure_atom_formula
-- name    : AvramDividend.Classical.barrierStrategy_initial_dividendMeasure_atom_formula
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:47:30.981804+00:00
-- url     : https://prove2.me/theorems/f5167fe3-64d3-445d-bd85-947f84817b2e
-- title:
--   Exact deterministic initial dividend atom for every nonnegative barrier strategy
-- statement:
--   The Stieltjes dividend measure of the constant-barrier strategy has a deterministic atom at time zero equal to the positive part of the initial surplus minus the barrier. This unifies cases x>a (a lump sum x-a) and x≤a (zero payment), for any nonnegative initial surplus and barrier. Its proof uses the exact right-increment identity and the general singleton-mass formula for dividend strategies.
-- source:
--   Combination of proved dividendMeasure_singleton_eq_rightLimit_sub, barrierStrategy_isDividendStrategy_nonnegative_barrier, barrierStrategy_right_increment_formula.

import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_increment_formula
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_initial_dividendMeasure_atom_formula
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (ω : Ω) :
    dividendMeasure (barrierStrategy X x a) ω ({0} : Set ℝ) =
      ENNReal.ofReal (max 0 (x - a)) := by sorry
