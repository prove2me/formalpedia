-- Prove2me | solution 1 for mme_finite_second_moment_many_above_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:42:36.86507+00:00
-- url     : https://prove2.me/submissions/754faa38-cd17-4d8a-b7fe-a3a3cc621622

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open BigOperators

/-- A finite Paley--Zygmund kernel in cross-multiplied form.  If a threshold
is at most half the mean, the first moment squared is controlled by the
number of parameters above threshold times the second moment. -/
theorem solution
    {Ω : Type} [DecidableEq Ω]
    (U : Finset Ω) (f : Ω → ℝ) (h : ℝ)
    (hf : ∀ ω ∈ U, 0 ≤ f ω)
    (hh : 0 ≤ h)
    (hhalf : 2 * (U.card : ℝ) * h ≤ ∑ ω ∈ U, f ω) :
    (∑ ω ∈ U, f ω) ^ 2 ≤
      4 * ((U.filter (fun ω => h ≤ f ω)).card : ℝ) *
        (∑ ω ∈ U, (f ω) ^ 2) := by
  classical
  let Good : Finset Ω := U.filter (fun ω => h ≤ f ω)
  let Bad : Finset Ω := U.filter (fun ω => ¬ h ≤ f ω)
  have hpartition :
      (∑ ω ∈ Good, f ω) + (∑ ω ∈ Bad, f ω) =
        ∑ ω ∈ U, f ω := by
    simpa only [Good, Bad] using
      Finset.sum_filter_add_sum_filter_not U (fun ω => h ≤ f ω) f
  have hbadPoint : ∀ ω ∈ Bad, f ω ≤ h := by
    intro ω hω
    have hnle : ¬ h ≤ f ω := (Finset.mem_filter.mp hω).2
    exact le_of_lt (lt_of_not_ge hnle)
  have hbadLe : (∑ ω ∈ Bad, f ω) ≤ (U.card : ℝ) * h := by
    calc
      (∑ ω ∈ Bad, f ω) ≤ ∑ _ω ∈ Bad, h :=
        Finset.sum_le_sum hbadPoint
      _ = (Bad.card : ℝ) * h := by simp
      _ ≤ (U.card : ℝ) * h := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        · exact hh
  have hsumLeGood :
      (∑ ω ∈ U, f ω) ≤ 2 * (∑ ω ∈ Good, f ω) := by
    have hfirst' :
        2 * ((U.card : ℝ) * h) ≤ ∑ ω ∈ U, f ω := by
      simpa only [mul_assoc] using hhalf
    linarith
  have hsumNonneg : 0 ≤ ∑ ω ∈ U, f ω := Finset.sum_nonneg hf
  have hgoodNonneg : 0 ≤ ∑ ω ∈ Good, f ω := by
    apply Finset.sum_nonneg
    intro ω hω
    exact hf ω ((Finset.mem_filter.mp hω).1)
  have hsqLeGoodSq :
      (∑ ω ∈ U, f ω) ^ 2 ≤ 4 * (∑ ω ∈ Good, f ω) ^ 2 := by
    nlinarith
  have hcauchy :
      (∑ ω ∈ Good, f ω) ^ 2 ≤
        (Good.card : ℝ) * ∑ ω ∈ Good, (f ω) ^ 2 := by
    exact sq_sum_le_card_mul_sum_sq
  have hsquareSubset :
      (∑ ω ∈ Good, (f ω) ^ 2) ≤
        ∑ ω ∈ U, (f ω) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro ω _ _
      positivity
  calc
    (∑ ω ∈ U, f ω) ^ 2 ≤
        4 * (∑ ω ∈ Good, f ω) ^ 2 := hsqLeGoodSq
    _ ≤ 4 * ((Good.card : ℝ) * ∑ ω ∈ Good, (f ω) ^ 2) := by
      gcongr
    _ ≤ 4 * ((Good.card : ℝ) * ∑ ω ∈ U, (f ω) ^ 2) := by
      gcongr
    _ = 4 * ((U.filter (fun ω => h ≤ f ω)).card : ℝ) *
          (∑ ω ∈ U, (f ω) ^ 2) := by
      simp only [Good]
      ring
