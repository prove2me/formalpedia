-- Prove2me | solution 1 for levy_foundations_iIndepSets_piiUnionInter_pairwiseDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:58:23.154723+00:00
-- url     : https://prove2.me/submissions/1dd579cd-1c8a-4e79-9ced-9b4005267ae4

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.PiSystem

open MeasureTheory MeasurableSpace Set ProbabilityTheory

theorem solution
    {Ω ι κ : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {π : κ → Set (Set Ω)} {S : ι → Set κ}
    (h_indep : iIndepSets π μ)
    (hS : Pairwise (Function.onFun Disjoint S)) :
    iIndepSets (fun i => piiUnionInter π (S i)) μ := by
  classical
  rw [iIndepSets_iff]
  intro s A hA
  have hex : ∀ i, ∃ (t : Finset κ) (g : κ → Set Ω), i ∈ s →
      (↑t ⊆ S i ∧ (∀ k ∈ t, g k ∈ π k) ∧ A i = ⋂ k ∈ t, g k) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨t, ht, g, hg, he⟩ := hA i hi
      exact ⟨t, g, fun _ => ⟨ht, hg, he⟩⟩
    · exact ⟨∅, fun _ => ∅, fun h => absurd h hi⟩
  choose t g hg using hex
  -- pairwise disjointness of the finsets
  have hdisj : Set.PairwiseDisjoint (↑s) t := by
    intro i hi j hj hij
    rw [Function.onFun, Finset.disjoint_left]
    intro k hki hkj
    exact (Set.disjoint_left.1 (hS hij) ((hg i hi).1 hki)) ((hg j hj).1 hkj)
  let G : κ → Set Ω := fun k => ⋂ i ∈ s.filter (fun i => k ∈ t i), g i k
  have hGeq : ∀ i ∈ s, ∀ k ∈ t i, G k = g i k := by
    intro i hi k hk
    have : s.filter (fun j => k ∈ t j) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hj, hkj⟩
        by_contra hne
        exact Set.disjoint_left.1 (hS hne) ((hg j hj).1 hkj) ((hg i hi).1 hk)
      · rintro rfl
        exact ⟨hi, hk⟩
    show (⋂ j ∈ s.filter (fun j => k ∈ t j), g j k) = g i k
    rw [this]
    simp
  have h1 : (⋂ i ∈ s, A i) = ⋂ k ∈ s.biUnion t, G k := by
    rw [Finset.set_biInter_biUnion]
    apply Set.iInter₂_congr
    intro i hi
    rw [(hg i hi).2.2]
    apply Set.iInter₂_congr
    intro k hk
    exact (hGeq i hi k hk).symm
  have h2 : ∀ k ∈ s.biUnion t, G k ∈ π k := by
    intro k hk
    obtain ⟨i, hi, hki⟩ := Finset.mem_biUnion.1 hk
    rw [hGeq i hi k hki]
    exact (hg i hi).2.1 k hki
  rw [h1, h_indep.meas_biInter _ h2, Finset.prod_biUnion hdisj]
  apply Finset.prod_congr rfl
  intro i hi
  rw [(hg i hi).2.2, h_indep.meas_biInter (t i) (fun k hk => (hg i hi).2.1 k hk)]
  apply Finset.prod_congr rfl
  intro k hk
  rw [hGeq i hi k hk]
