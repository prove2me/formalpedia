-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_laplace_random_mark_sum_without_pgf_assumption
-- name    : AvramDividend.Classical.chat06_laplace_random_mark_sum_without_pgf_assumption
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:31:50.641912+00:00
-- url     : https://prove2.me/theorems/e905fc49-0c85-440b-857a-72689b913192
-- title:
--   Marked compound-Poisson real Laplace identity with the Poisson generating function proved
-- statement:
--   If a measurable Poisson count is independent of the whole mark sequence, the exponential of the random marked sum is integrable and each fixed-count mark-sum exponential moment factors as m^k, then its real Laplace transform equals exp(r(m-1)). This theorem combines two independently accepted exact Prove2Me results: the count-cylinder conditioning formula and the Poisson generating-function theorem, thereby discharging the latter as a separate hypothesis. Independence of the actual compound Poisson count from marks, fixed-count iid mark moment factorisation, and integrability remain explicit construction obligations.
-- source:
--   Source bv_compound_poisson_laplace_without_pgf_assumption_chat06_20261021.lean, 31 lines, 1442 bytes, SHA-256 facdd612711e4f4776b0ab1e3309f35f395fd280af87723970345c83b693951f. Private probe 749931d9-1519-4d9c-8b8d-ef2e1395b65f passed remote source elaboration to sentinel with zero candidate errors at pinned revision.

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_laplace_random_mark_sum_of_indep_count
import Theorems.Thm_AvramDividend_Classical_chat06_poisson_count_pgf_general

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat06_laplace_random_mark_sum_without_pgf_assumption
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable N) (hY : ∀ n, Measurable (Y n))
    (hNY : IndepFun N (fun ω n => Y n ω) P)
    (r : ℝ≥0) (hLaw : HasLaw N (poissonMeasure r) P)
    (θ m : ℝ)
    (hFint : Integrable (fun ω =>
      Real.exp (θ * ∑ j ∈ Finset.range (N ω), Y j ω)) P)
    (hMarks : ∀ k, (∫ ω,
      Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω) ∂P) = m ^ k) :
    (∫ ω, Real.exp (θ * ∑ j ∈ Finset.range (N ω), Y j ω) ∂P) =
      Real.exp ((r : ℝ) * (m - 1)) := by sorry
