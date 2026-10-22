-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_laplace_random_mark_sum_of_indep_count
-- name    : AvramDividend.Classical.chat06_laplace_random_mark_sum_of_indep_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T09:00:29.938473+00:00
-- url     : https://prove2.me/theorems/7543b0fa-b1e0-45cc-9033-cf39a489ccbe
-- title:
--   Real Laplace transform of random Poisson mark sum by count-cylinder disintegration
-- statement:
--   If a measurable Poisson-distributed count N is independent of the entire mark sequence Y, the random marked exponential payoff is integrable, each finite mark-sum exponential moment equals m^k, and the count's Poisson generating function is exp(r(m-1)), then the random sum's real Laplace transform equals exp(r(m-1)). The proof partitions the sample space into count cylinders, factors each cylinder integral using the independence of N and all marks, and recombines with the Poisson law. The assumptions about mark moments, integrability, and count-process independence are explicit, not consequences of this theorem. An independently probed Poisson PGF helper is being published to discharge the PGF hypothesis in a follow-on theorem.
-- source:
--   Existing source bv_compound_poisson_laplace_count_partition_chat06_20261020.lean, 147 lines, 6240 bytes, SHA-256 9f9c4453b7d9217c9e39123da5ed53ca85aad43de7db710a89d155a0908687fa. Private remote probe 7c0eccb7-2467-443b-a11e-9fd7daa7062d passed source elaboration to sentinel with zero candidate source errors at pinned revision.

import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat06_laplace_random_mark_sum_of_indep_count
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
      Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω) ∂P) = m ^ k)
    (hPGF : (∫ n : ℕ, m ^ n ∂poissonMeasure r) =
      Real.exp ((r : ℝ) * (m - 1))) :
    (∫ ω, Real.exp (θ * ∑ j ∈ Finset.range (N ω), Y j ω) ∂P) =
      Real.exp ((r : ℝ) * (m - 1)) := by sorry
