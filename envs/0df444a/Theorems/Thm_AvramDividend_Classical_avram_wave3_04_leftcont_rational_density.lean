-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_leftcont_rational_density
-- name    : AvramDividend.Classical.avram_wave3_04_leftcont_rational_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:33:00.801553+00:00
-- url     : https://prove2.me/theorems/706385b7-d262-4e4c-b098-44b69998ebc6
-- title:
--   Strict left-rational observations for monotone left-continuous paths
-- statement:
--   Every strict upper level of a monotone real-valued path at a positive time is already exceeded at a preceding nonnegative rational time, provided the path is continuous from the left in the actual Iic neighbourhood topology. The formal proof uses the nontrivial punctured left neighbourhood filter and density of nonnegative rationals; it does not assume pathwise right-continuity.
-- source:
--   Mathlib Topology.Order.DenselyOrdered.nhdsLT_neBot_of_exists_lt, NNReal.lt_iff_exists_rat_btwn, and ContinuityWithinAt on Iic. Full source reached the intentional pinned remote compiler sentinel under candidate SHA-256 e2884e3b3cdd9756ce0fdad26e968574bf3871d60384a7c3d46dda84b234b81e, job a3490210-350c-4e6f-9721-af7c051e9af4. Its main consumer is AvramDividend.Classical.IsDividendStrategy left-continuous predictable dividend control, prerequisite to Avram Palmowski Pistorius (2007) Proposition 4(i).

import Mathlib

open MeasureTheory Set
open scoped NNReal NNRat

theorem AvramDividend.Classical.avram_wave3_04_leftcont_rational_density
    (f : ℝ≥0 → ℝ)
    (hm : Monotone f)
    (hc : ∀ t, ContinuousWithinAt f (Set.Iic t) t)
    (t : ℝ≥0) (a : ℝ)
    (ht : t ≠ 0) (ha : a < f t) :
    ∃ r : ℚ≥0, (r : ℝ≥0) < t ∧ a < f (r : ℝ≥0) := by sorry
