-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_iid_mark_finite_sum_mean_variance
-- name    : AvramDividend.Classical.avram_wave4_p1_iid_mark_finite_sum_mean_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:27:46.277387+00:00
-- url     : https://prove2.me/theorems/25d8bb01-c0e0-4d05-b4d6-b6367b7bc05f
-- title:
--   Finite iid marked sums have additive variance and prescribed mean
-- statement:
--   On the original probability space, each mark Y_i has law ν and the full indexed family is mutually independent; each test f is measurable, integrable and square integrable. For every finite index set s, the mark sum has mean |s| times the mark mean and variance |s| times the mark variance. The proof derives each individual law transfer using HasLaw, propagates L2 through MeasurePreserving, derives pairwise independence from iIndepFun, and invokes Mathlib's variance_sum. This is the noncircular finite-mark second-order component needed before an iid-marked compound-Poisson stochastic isometry.
-- source:
--   Pinned Mathlib ProbabilityTheory.iIndepFun.indepFun, IndepFun.variance_sum, MeasurePreserving.variance_fun_comp, MemLp.comp_measurePreserving, HasLaw.integral_comp; Applebaum finite marked Poisson moments.

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_iid_mark_finite_sum_mean_variance
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (Y : ℕ → Ω → E) (hYm : ∀ i, Measurable (Y i))
    (hYL : ∀ i, HasLaw (Y i) ν P)
    (hYi : iIndepFun Y P)
    (f : E → ℝ) (hf : Measurable f)
    (hfI : Integrable f ν) (hf2 : MemLp f 2 ν)
    (s : Finset ℕ) :
    (∫ ω, ∑ i ∈ s, f (Y i ω) ∂P) =
      (s.card : ℝ) * ∫ z, f z ∂ν ∧
    variance (fun ω => ∑ i ∈ s, f (Y i ω)) P =
      (s.card : ℝ) * variance f ν := by sorry
