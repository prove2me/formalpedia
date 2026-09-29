-- Prove2me | solution 1 for hoeffding_two_sided
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T23:18:06.064131+00:00
-- url     : https://prove2.me/submissions/142c4785-408c-4e27-9cb1-a7a499d7eb33

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {c : ι → ℝ≥0} {s : Finset ι}
    (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ s, X i ω|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ s, c i)) := by
  have hR := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun h_indep h_subG hε
  have h_indep' : iIndepFun (fun i => fun ω => -(X i ω)) μ := by
    have := h_indep.comp (g := fun _ : ι => fun x : ℝ => -x) (fun i => measurable_neg)
    exact this
  have h_subG' : ∀ i ∈ s, HasSubgaussianMGF ((fun i => fun ω => -(X i ω)) i) (c i) μ := by
    intro i hi
    exact (h_subG i hi).neg
  have hL := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun h_indep' h_subG' hε
  set S : Ω → ℝ := fun ω => ∑ i ∈ s, X i ω with hS
  have hnegsum : ∀ ω, ∑ i ∈ s, (fun i => fun ω => -(X i ω)) i ω = -(S ω) := by
    intro ω; simp [hS, Finset.sum_neg_distrib]
  have hLset : {ω | ε ≤ ∑ i ∈ s, (fun i => fun ω => -(X i ω)) i ω} = {ω | ε ≤ -(S ω)} := by
    ext ω; simp only [Set.mem_setOf_eq, hnegsum]
  rw [hLset] at hL
  have hsub : {ω | ε ≤ |S ω|} ⊆ {ω | ε ≤ S ω} ∪ {ω | ε ≤ -(S ω)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rcases abs_cases (S ω) with ⟨h1, _⟩ | ⟨h1, _⟩
    · left; rw [h1] at hω; exact hω
    · right; rw [h1] at hω; exact hω
  calc μ.real {ω | ε ≤ |S ω|}
      ≤ μ.real ({ω | ε ≤ S ω} ∪ {ω | ε ≤ -(S ω)}) := measureReal_mono hsub
    _ ≤ μ.real {ω | ε ≤ S ω} + μ.real {ω | ε ≤ -(S ω)} := measureReal_union_le _ _
    _ ≤ Real.exp (-ε ^ 2 / (2 * ∑ i ∈ s, c i))
        + Real.exp (-ε ^ 2 / (2 * ∑ i ∈ s, c i)) := add_le_add hR hL
    _ = 2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ s, c i)) := by ring
