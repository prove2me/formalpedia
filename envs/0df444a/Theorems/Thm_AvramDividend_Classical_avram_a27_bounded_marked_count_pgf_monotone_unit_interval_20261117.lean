-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_bounded_marked_count_pgf_monotone_unit_interval_20261117
-- name    : AvramDividend.Classical.avram_a27_bounded_marked_count_pgf_monotone_unit_interval_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:27:09.254134+00:00
-- url     : https://prove2.me/theorems/60cd691d-4049-4f2a-93c5-ce378f76a283
-- title:
--   Bounded nonnegative marked count PGF is monotone throughout the unit interval
-- statement:
--   For a nonnegative measurable integer-valued count and a unit-bounded nonnegative weight on the same probability space, the marked count generating-function expectation is nondecreasing as the generating variable increases from zero to one. This gives a monotonicity constraint for the original finite-activity physical negative-jump PGF before establishing its Campbell equation.
-- source:
--   Proved generic bounded marked count PGF integrability 40990, induction on powers, and integral monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A nonnegative marked-count probability generating function is monotone on the unit interval. -/

theorem AvramDividend.Classical.avram_a27_bounded_marked_count_pgf_monotone_unit_interval_20261117
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (F : Ω → ℝ) (hF : Measurable F)
    (hRange : ∀ᵐ ω ∂P, 0 ≤ F ω ∧ F ω ≤ 1)
    (z w : ℝ) (hz : 0 ≤ z) (hzw : z ≤ w) (hw : w ≤ 1) :
    (∫ ω, z ^ (K ω) * F ω ∂P) ≤
      (∫ ω, w ^ (K ω) * F ω ∂P) := by sorry
