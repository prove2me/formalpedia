-- Prove2me | solution 1 for vcdim_finite_imp_proper_finite_support_learner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:49.467773+00:00
-- url     : https://prove2.me/submissions/98d7b01b-4a90-41af-bd39-c21e4460b4b2

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_FiniteSupportUC
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Compression
public import Theorems.Thm_boolTestExpectation_empirical_eq_avg
public import Theorems.Thm_finite_support_vc_approx

section
@[expose] public section
open Finset
noncomputable section
universe u
attribute [local instance] Classical.propDecidable
private lemma disagreementFamily_boolVCDim_le
    {X : Type u} [DecidableEq X]
    (C : ConceptClass X Bool) (c : X → Bool) (Y : Finset X) {d : ℕ}
    (hvc : VCDim X C ≤ ↑d) :
    (disagreementFamily C c Y).boolVCDim ≤ d := by
  -- boolVCDim = shatterer.sup card. Show every shattered T has T.card ≤ d.
  simp only [Finset.boolVCDim, Finset.vcDim]
  apply Finset.sup_le
  intro T hT
  have hTs := Finset.mem_shatterer.mp hT
  -- T : Finset ↥Y shattered by boolFamilyToFinsetFamily of the disagreement family.
  -- Lift T to X and show C shatters the lifted set.
  let S := T.map ⟨Subtype.val, Subtype.val_injective⟩
  have hS_card : S.card = T.card := Finset.card_map _
  have mem_S : ∀ y : ↥Y, y ∈ T → (y : X) ∈ S :=
    fun y hy => Finset.mem_map.mpr ⟨y, hy, rfl⟩
  suffices hS_shatt : Shatters X C S by
    have h1 : (S.card : WithTop ℕ) ≤ VCDim X C := le_iSup₂_of_le S hS_shatt le_rfl
    rw [hS_card] at h1; exact WithTop.coe_le_coe.mp (le_trans h1 hvc)
  intro g
  -- Build t ⊆ T: points where g disagrees with c (using dite for membership).
  let pred : ↥Y → Bool := fun y =>
    if hy : y ∈ T then decide (g ⟨y.val, mem_S y hy⟩ ≠ c y.val) else false
  let t := T.filter (fun y => pred y = true)
  have ht_sub : t ⊆ T := Finset.filter_subset (fun y => pred y = true) T
  obtain ⟨u, hu, hTu⟩ := hTs ht_sub
  -- u ∈ boolFamilyToFinsetFamily (disagreementFamily C c Y)
  simp only [boolFamilyToFinsetFamily, Finset.mem_image] at hu
  obtain ⟨a, ha, rfl⟩ := hu
  simp only [disagreementFamily, Finset.mem_filter, Finset.mem_image,
    Finset.mem_univ, true_and] at ha
  obtain ⟨_, h_concept, hcC, ha_eq⟩ := ha
  refine ⟨h_concept, hcC, fun ⟨x, hxS⟩ => ?_⟩
  obtain ⟨y, hyT, hyx⟩ := Finset.mem_map.mp hxS
  -- hyx : y.val = x. The goal is h_concept x = g ⟨x, hxS⟩.
  subst hyx
  -- Now goal: h_concept y.val = g ⟨y.val, hxS⟩.
  -- Since hxS and mem_S y hyT are proofs of the same Prop, g applied to either is the same.
  -- Key: for y ∈ T, membership in the filter-set ↔ membership in t (from hTu)
  have h_mem_iff : y ∈ Finset.univ.filter (fun z => a z = true) ↔ y ∈ t := by
    constructor
    · intro hf; exact hTu ▸ Finset.mem_inter.mpr ⟨hyT, hf⟩
    · intro ht'; exact (Finset.mem_inter.mp (hTu ▸ ht')).2
  -- Combine: a y = true ↔ g(y.val) ≠ c(y.val)
  have h_ay_iff : a y = true ↔ g ⟨y.val, hxS⟩ ≠ c y.val := by
    rw [show (a y = true) ↔ y ∈ Finset.univ.filter (fun z => a z = true) from
      by simp [Finset.mem_filter], h_mem_iff]
    simp only [t, pred, Finset.mem_filter, hyT, dite_true, decide_eq_true_eq]
    tauto
  have ha_y := ha_eq y
  -- Bool exhaustion: (h ≠ c ↔ g ≠ c) → h = g
  -- The goal is about coercions that reduce to y.val.
  -- Normalize: ↑(⟨embed y, hxS⟩ : ↥S) = y.val = ↑y
  change h_concept (y : X) = g ⟨(y : X), hxS⟩
  by_cases heq : h_concept (y : X) = c (y : X)
  · simp_all
  · have hay : a y = true := by rw [ha_y]; simp [heq]
    have hgne := h_ay_iff.mp hay
    cases hc : c (y : X) <;> cases hh : h_concept (y : X) <;>
      cases hg : g ⟨y.val, hxS⟩ <;> simp_all
private lemma supportError_eq_boolTestExpectation
    {X : Type u} (Y : Finset X) (q : FinitePMF ↥Y)
    (h c : X → Bool) :
    supportError Y q h c =
    boolTestExpectation q (fun y : ↥Y => decide (h (y : X) ≠ c (y : X))) := by
  simp only [supportError, boolTestExpectation, trueExpectation]
  simp_all
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
universe u
attribute [local instance] Classical.propDecidable
theorem _root_.solution
    (X : Type u) (C : ConceptClass X Bool)
    (hCne : C.Nonempty) (hC : VCDim X C < ⊤) :
    ∃ _L : ProperFiniteSupportLearner X C, True := by
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hC)
  obtain ⟨c₀, hc₀⟩ := hCne
  -- ERM learner: pick a consistent hypothesis if realizable, else c₀
  let learn : {m : ℕ} → (Fin m → X × Bool) → (X → Bool) := fun {m} S =>
    if h : ∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2 then h.choose else c₀
  have learn_mem : ∀ {m : ℕ} (S : Fin m → X × Bool), learn S ∈ C := by
    intro m S; simp only [learn]
    split
    · next h => exact h.choose_spec.1
    · exact hc₀
  have learn_consistent : ∀ {m : ℕ} (S : Fin m → X × Bool),
      (∃ c ∈ C, ∀ i, c (S i).1 = (S i).2) → ∀ i, learn S (S i).1 = (S i).2 := by
    intro m S hreal i; simp only [learn, dif_pos hreal]; exact hreal.choose_spec.2 i
  -- Get the sample size from finite_support_vc_approx
  obtain ⟨T, hTpos, hApprox⟩ := finite_support_vc_approx d (1 / 3) (by norm_num)
  exact ⟨⟨T, learn, @learn_mem, fun c hc Y q => by
    classical
    have : DecidableEq X := Classical.decEq X
    -- Build the disagreement family
    let A := disagreementFamily C c Y
    have hA : A.boolVCDim ≤ d := disagreementFamily_boolVCDim_le C c Y (le_of_eq hd.symm)
    -- Apply finite_support_vc_approx to get a sample of ↥Y
    obtain ⟨hs, hhs⟩ := hApprox A hA q
    -- Convert sample to Finset X
    let Z : Finset X := Finset.univ.image (fun t => ((hs t : ↥Y) : X))
    refine ⟨Z, ?_, ?_, ?_⟩
    · -- Z ⊆ Y
      intro x hx
      simp only [Z, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨t, rfl⟩ := hx
      exact (hs t).property
    · -- Z.card ≤ T
      calc Z.card ≤ Finset.univ.card := Finset.card_image_le
        _ = T := Fintype.card_fin T
    · -- supportError ≤ 1 / 3
      -- The ERM learns on Z, so learn(labeledSampleOfFinset c Z) is consistent with c on Z.
      -- The disagreement test for learn's output is in A (since learn_mem gives membership in C).
      -- The empirical disagreement on the sample hs is 0 (consistency on sampled points).
      -- By hhs, true disagreement ≤ 1 / 3.
      --
      -- The proof: supportError = boolTestExpectation of the disagreement test.
      -- The boolTestExpectation of empiricalPMF hs = fraction of sampled points
      --   where learn disagrees with c.
      -- Since every sampled point is in Z, and learn is consistent on Z,
      --   this fraction is 0.
      -- By hhs: |boolTestExpectation q a - 0| ≤ 1 / 3, so supportError ≤ 1 / 3.

      -- The key fact: the disagreement test for the ERM's output is in A
      let h_out := learn (labeledSampleOfFinset c Z)
      have h_out_mem : h_out ∈ C := learn_mem _
      let disagree : ↥Y → Bool := fun y => decide (h_out (y : X) ≠ c (y : X))
      -- Show disagree ∈ A
      have disagree_mem : disagree ∈ A := by
        simp only [A, disagreementFamily, Finset.mem_filter, Finset.mem_image,
          Finset.mem_univ, true_and]
        exact ⟨⟨disagree, rfl⟩, h_out, h_out_mem, fun y => rfl⟩
      -- Rewrite supportError as boolTestExpectation
      rw [supportError_eq_boolTestExpectation]
      -- We need: boolTestExpectation q disagree ≤ 1 / 3
      -- From hhs: |boolTestExpectation q disagree -
      --            boolTestExpectation (empiricalPMF hTpos hs) disagree| ≤ 1 / 3
      have hclose := hhs disagree disagree_mem
      -- Show empirical expectation is 0.
      -- Key: use boolTestExpectation_empirical_eq_avg to rewrite as an average
      -- over sampled points. Since learn is consistent with c on Z, and every
      -- sampled point lands in Z, the disagreement is false for all t.
      have h_emp_zero : boolTestExpectation (empiricalPMF hTpos hs) disagree = 0 := by
        rw [boolTestExpectation_empirical_eq_avg hTpos hs disagree]
        -- Goal: (∑ t, if disagree (hs t) then 1 else 0) / T = 0
        rw [div_eq_zero_iff]
        left
        apply Finset.sum_eq_zero
        intro t _
        -- For each sampled point hs t, show disagree(hs t) = false.
        -- This means h_out((hs t : X)) = c((hs t : X)).
        -- ERM learn is consistent on Z because c ∈ C realizes the labels.
        -- (hs t : X) ∈ Z by construction.
        suffices h_agree : h_out ((hs t : ↥Y) : X) = c ((hs t : ↥Y) : X) by
          change (if disagree (hs t) then (1 : ℝ) else 0) = 0
          have : disagree (hs t) = false := by
            simp only [disagree, h_agree, ne_eq, not_true_eq_false, decide_false]
          rw [this]; simp
        -- h_out = learn(labeledSampleOfFinset c Z), which is consistent with c on Z.
        -- The realizability witness for the labeled sample from Z is c itself.
        have hreal_Z : ∃ c' ∈ C, ∀ i : Fin Z.card,
            c' ((labeledSampleOfFinset c Z) i).1 = ((labeledSampleOfFinset c Z) i).2 :=
          ⟨c, hc, fun i => by simp [labeledSampleOfFinset]⟩
        -- learn_consistent gives: learn agrees with labels on all sample indices.
        -- We need to find the index of (hs t : X) in Z.
        have ht_in_Z : ((hs t : ↥Y) : X) ∈ Z := by
          simp only [Z, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨t, rfl⟩
        -- Use Z.equivFin to get the index
        set y_sub : ↥Z := ⟨((hs t : ↥Y) : X), ht_in_Z⟩ with hy_sub_def
        set i := Z.equivFin y_sub with hi_def
        have hcons_i := learn_consistent (labeledSampleOfFinset c Z) hreal_Z i
        simp only [labeledSampleOfFinset] at hcons_i
        -- hcons_i : h_out (Z.equivFin.symm i : X) = c (Z.equivFin.symm i : X)
        -- Z.equivFin.symm i = y_sub = ⟨(hs t : X), ht_in_Z⟩
        have h_symm : Z.equivFin.symm i = y_sub := Z.equivFin.symm_apply_apply y_sub
        rwa [h_symm] at hcons_i
      -- Now combine: |true - 0| ≤ 1 / 3, and true is nonneg, so true ≤ 1 / 3
      rw [h_emp_zero, sub_zero] at hclose
      calc boolTestExpectation q disagree
          ≤ |boolTestExpectation q disagree| := le_abs_self _
        _ ≤ 1 / 3 := hclose
    ⟩, trivial⟩
