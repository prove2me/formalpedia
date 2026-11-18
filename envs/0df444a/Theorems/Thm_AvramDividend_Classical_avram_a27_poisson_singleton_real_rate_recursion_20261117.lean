-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_poisson_singleton_real_rate_recursion_20261117
-- name    : AvramDividend.Classical.avram_a27_poisson_singleton_real_rate_recursion_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:35:23.104795+00:00
-- url     : https://prove2.me/theorems/cbd88753-270a-4e53-9ed2-2f7b461fda11
-- title:
--   Poisson singleton real probability mass satisfies the exact rate divided by count recurrence
-- statement:
--   For each nonnegative Poisson intensity and every count k, the mass at k+1 equals r/(k+1) times the mass at k. This feeds the original physical marked-Poisson count-cell Mecke recursion with exact Poisson masses.
-- source:
--   Pinned Mathlib ProbabilityTheory.poissonMeasure_singleton probability formula and the natural factorial recurrence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Ordinary real Poisson singleton probabilities obey the rate-over-count recurrence. -/

theorem AvramDividend.Classical.avram_a27_poisson_singleton_real_rate_recursion_20261117 (r : ℝ≥0) (k : ℕ) :
    (poissonMeasure r).real {k + 1} =
      ((r : ℝ) / ((k + 1 : ℕ) : ℝ)) *
        (poissonMeasure r).real {k} := by sorry
