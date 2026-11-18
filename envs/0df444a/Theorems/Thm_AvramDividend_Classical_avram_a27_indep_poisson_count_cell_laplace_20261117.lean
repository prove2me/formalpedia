-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_indep_poisson_count_cell_laplace_20261117
-- name    : AvramDividend.Classical.avram_a27_indep_poisson_count_cell_laplace_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T15:25:11.008235+00:00
-- url     : https://prove2.me/theorems/61f4a029-8e57-4270-893a-51324684afdb
-- title:
--   Poisson count-cell Laplace integral from independent original marks
-- statement:
--   For a Poisson count N independent of its measurable mark stream Y on the same probability space, with fixed-k exponential moment m^k, the source integral over N=k of the random mark-sum exponential is the Poisson mass at k multiplied by m^k.
-- source:
--   Exact count-cell factorisation from the accepted proof of chat06_laplace_random_mark_sum_of_indep_count, Prove2Me 7543b0fa.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Independence of a Poisson count and the original mark stream gives each count-cell Laplace integral. -/

theorem AvramDividend.Classical.avram_a27_indep_poisson_count_cell_laplace_20261117
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable N) (hY : ∀ n, Measurable (Y n))
    (hNY : IndepFun N (fun ω n => Y n ω) P)
    (r : ℝ≥0) (hLaw : HasLaw N (poissonMeasure r) P)
    (θ m : ℝ)
    (hMarks : ∀ k, (∫ ω,
      Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω) ∂P) = m ^ k)
    (k : ℕ) :
    (∫ ω in {ω : Ω | N ω = k},
      Real.exp (θ * ∑ j ∈ Finset.range (N ω), Y j ω) ∂P) =
      (poissonMeasure r).real {k} * m ^ k := by sorry
