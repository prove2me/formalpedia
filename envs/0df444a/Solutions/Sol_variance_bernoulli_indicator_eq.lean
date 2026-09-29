-- Prove2me | solution 1 for variance_bernoulli_indicator_eq
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-23T23:37:00.385337+00:00
-- url     : https://prove2.me/submissions/93828d6c-12ac-432f-994b-274e68736746

import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

theorem solution (p : ℝ≥0) (h : p ≤ 1) :
    variance (fun b : Bool => (cond b 1 0 : ℝ)) (PMF.bernoulli p h).toMeasure
      = (p : ℝ) * (1 - p) := by
  classical
  have hmeas : AEStronglyMeasurable (fun b : Bool => (cond b 1 0 : ℝ))
      (PMF.bernoulli p h).toMeasure :=
    (measurable_of_finite _).aestronglyMeasurable
  have hf : MemLp (fun b : Bool => (cond b 1 0 : ℝ)) 2 (PMF.bernoulli p h).toMeasure :=
    MemLp.of_bound hmeas 1 (.of_forall fun b => by cases b <;> simp)
  rw [variance_eq_sub hf]
  have hEf : (PMF.bernoulli p h).toMeasure[fun b : Bool => (cond b 1 0 : ℝ)] = (p : ℝ) := by
    simpa using PMF.bernoulli_expectation h
  have hfsq : (fun b : Bool => ((fun b : Bool => (cond b 1 0 : ℝ)) ^ 2) b)
      = (fun b : Bool => (cond b 1 0 : ℝ)) := by
    funext b; cases b <;> simp
  have hEfsq : (PMF.bernoulli p h).toMeasure[(fun b : Bool => (cond b 1 0 : ℝ)) ^ 2]
      = (p : ℝ) := by
    rw [hfsq]; exact hEf
  rw [hEfsq, hEf]
  ring
