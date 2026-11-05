-- Prove2me | solution 1 for levy_foundations_iIndepFun_setRestrict_pairwiseDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:58:22.120195+00:00
-- url     : https://prove2.me/submissions/69641a5e-cfaa-472d-a973-8b7f1ab98905

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.PiSystem

open MeasureTheory MeasurableSpace Set ProbabilityTheory

theorem Lv2Aux_iIndepSets_piiUnionInter_pairwiseDisjoint
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

theorem solution
    {Ω ι κ : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {β : κ → Type*} {mβ : ∀ k, MeasurableSpace (β k)}
    {f : ∀ k, Ω → β k} (hf : ∀ k, Measurable (f k))
    (h_indep : iIndepFun f μ) {S : ι → Set κ}
    (hS : Pairwise (Function.onFun Disjoint S)) :
    iIndepFun (fun i ω => (S i).restrict fun k => f k ω) μ := by
  have h0 := Lv2Aux_iIndepSets_piiUnionInter_pairwiseDisjoint
    (π := fun k => {s | MeasurableSet[(mβ k).comap (f k)] s}) (S := S)
    (h_indep.iIndep.iIndepSets') hS
  rw [iIndepFun_iff_iIndep (fun i => MeasurableSpace.pi) _ μ]
  have hcomap : ∀ i, MeasurableSpace.comap (fun ω => (S i).restrict fun k => f k ω)
      MeasurableSpace.pi = ⨆ k ∈ S i, (mβ k).comap (f k) := by
    intro i
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, iSup_subtype']
    apply iSup_congr
    intro k
    rw [MeasurableSpace.comap_comp]
    rfl
  refine iIndepSets.iIndep (h_le := ?_) (π := _) (h_pi := ?_) (h_generate := ?_) (h_ind := h0)
  · intro i
    have : Measurable (fun ω => (S i).restrict fun k => f k ω) :=
      measurable_pi_iff.2 fun k => hf k
    exact this.comap_le
  · intro i
    exact isPiSystem_piiUnionInter _ (fun k => @MeasurableSpace.isPiSystem_measurableSet Ω ((mβ k).comap (f k))) _
  · intro i
    rw [hcomap i]
    exact (generateFrom_piiUnionInter_measurableSet (fun k => (mβ k).comap (f k)) (S i)).symm
