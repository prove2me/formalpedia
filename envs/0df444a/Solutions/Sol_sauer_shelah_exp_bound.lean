-- Prove2me | solution 1 for sauer_shelah_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:08.85241+00:00
-- url     : https://prove2.me/submissions/3bc737e5-faaf-488d-aae5-2873d7916bcb

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Theorems.Thm_sum_choose_le_exp_pow
section
@[expose] public section
universe u v
private theorem ncard_restrictions_le_sum_choose_set {X : Type u}
    (C : ConceptClass X Bool) (S : Finset X) (d : ℕ)
    (hvc : VCDim X C = ↑d) :
    ({ f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x } : Set (↥S → Bool)).ncard ≤
      ∑ i ∈ Finset.range (d + 1), Nat.choose S.card i := by
  classical
  -- The restriction set is finite since ↥S → Bool is Fintype
  set R := { f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x } with hR_def
  have hR_fin : R.Finite := Set.Finite.subset (Set.finite_univ) (Set.subset_univ _)
  -- Convert to Finset for counting
  rw [Set.ncard_eq_toFinset_card']
  -- Build a Finset family AA : Finset (Finset ↥S) from R
  set R_fin := R.toFinset with hR_fin_def
  set AA := R_fin.image (fun f => Finset.univ.filter (fun x => f x = true)) with hAA_def
  -- Step 1: R_fin.card ≤ AA.card (the map f ↦ filter is injective on Bool-valued functions)
  have h_inj : Function.Injective
      (fun (f : ↥S → Bool) => Finset.univ.filter (fun x => f x = true)) := by
    intro f g hfg
    funext x
    have := Finset.ext_iff.mp hfg x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    cases hf : f x <;> cases hg : g x <;> simp_all
  have h1 : R_fin.card = AA.card := by
    rw [hAA_def]; exact (Finset.card_image_of_injective _ h_inj).symm
  -- Step 2: AA.card ≤ AA.shatterer.card (Mathlib: card_le_card_shatterer)
  have h2 : AA.card ≤ AA.shatterer.card := Finset.card_le_card_shatterer AA
  -- Step 3: AA.shatterer.card ≤ ∑ k ∈ Iic AA.vcDim, C(Fintype.card ↥S, k)
  have h3 := @Finset.card_shatterer_le_sum_vcDim ↥S _ AA
  -- Step 4: vcDim(AA) ≤ d
  -- If AA shatters T, then C shatters T.map Subtype.val, so |T| ≤ d
  have h4 : AA.vcDim ≤ d := by
    simp only [Finset.vcDim]
    apply Finset.sup_le
    intro T hT
    have hTs : AA.Shatters T := Finset.mem_shatterer.mp hT
    -- If AA shatters T ⊆ ↥S, then C shatters T.map Subtype.val ⊆ X
    set Tval := T.map ⟨Subtype.val, Subtype.val_injective⟩ with hTval_def
    suffices hShats : Shatters X C Tval by
      have hCard : Tval.card = T.card := Finset.card_map _
      have : (Tval.card : WithTop ℕ) ≤ ↑d := by
        calc (Tval.card : WithTop ℕ)
            ≤ ⨆ (S : Finset X) (_ : Shatters X C S), (S.card : WithTop ℕ) :=
              le_iSup₂ (f := fun (S : Finset X) (_ : Shatters X C S) =>
                (S.card : WithTop ℕ)) _ hShats
          _ = ↑d := hvc
      linarith [WithTop.coe_le_coe.mp this, hCard]
    -- Prove Shatters X C Tval: for any labeling g : ↥Tval → Bool, find c ∈ C matching
    intro g
    -- Helper function: extend g to ↥S via dite
    let g' : ↥S → Bool := fun x =>
      if h : (↑x : X) ∈ Tval then g ⟨↑x, h⟩ else false
    -- Build t_sub ⊆ T: elements labeled true
    let t_sub : Finset ↥S := T.filter (fun x => g' x = true)
    have ht_sub : t_sub ⊆ T := Finset.filter_subset _ _
    obtain ⟨A, hA, hTA⟩ := hTs ht_sub
    simp only [hAA_def, Finset.mem_image] at hA
    obtain ⟨f, hf_mem, rfl⟩ := hA
    rw [Set.mem_toFinset] at hf_mem
    obtain ⟨c, hcC, hcf⟩ := hf_mem
    refine ⟨c, hcC, ?_⟩
    intro ⟨y, hyTval⟩
    -- c ↑(y, hyTval) = c y. Need to match this with g ⟨y, hyTval⟩.
    -- y ∈ Tval, so ∃ x ∈ T, ↑x = y
    have hyTval' := hyTval
    rw [hTval_def, Finset.mem_map] at hyTval'
    obtain ⟨⟨y', hy'S⟩, hy'T, hy'eq⟩ := hyTval'
    -- hy'eq : ↑⟨y', hy'S⟩ = y, i.e., y' = y
    simp only [Function.Embedding.coeFn_mk] at hy'eq
    subst hy'eq
    -- Now y = y', hyTval : y' ∈ Tval, hy'S : y' ∈ S, hy'T : ⟨y', hy'S⟩ ∈ T
    have hcf_y := hcf ⟨y', hy'S⟩
    -- hcf_y : c y' = f ⟨y', hy'S⟩
    -- From hTA: T ∩ filter(f · = true) = t_sub = T.filter(g' · = true)
    have h_f_iff_g' : f ⟨y', hy'S⟩ = true ↔ g' ⟨y', hy'S⟩ = true := by
      have h1 : (⟨y', hy'S⟩ : ↥S) ∈ T ∩ Finset.univ.filter (fun x => f x = true) ↔
          f ⟨y', hy'S⟩ = true := by
        simp [Finset.mem_inter, Finset.mem_filter, hy'T]
      have h2 : (⟨y', hy'S⟩ : ↥S) ∈ t_sub ↔ g' ⟨y', hy'S⟩ = true := by
        simp [t_sub, Finset.mem_filter, hy'T]
      rw [hTA] at h1
      exact h1.symm.trans h2
    -- g' ⟨y', hy'S⟩ = g ⟨y', hyTval⟩ since y' ∈ Tval
    have h_g'_eq : g' ⟨y', hy'S⟩ = g ⟨y', hyTval⟩ := by
      simp only [g', dif_pos hyTval]
    -- Combine: c y' = f ⟨y',hy'S⟩ and f = true ↔ g = true
    rw [hcf_y, ← h_g'_eq]
    exact Bool.eq_iff_iff.mpr h_f_iff_g'
  -- Step 5: Fintype.card ↥S = S.card
  have h5 : Fintype.card ↥S = S.card := Fintype.card_coe S
  -- Combine
  calc R.toFinset.card
      = AA.card := h1
    _ ≤ AA.shatterer.card := h2
    _ ≤ ∑ k ∈ Finset.Iic AA.vcDim, (Fintype.card ↥S).choose k := h3
    _ = ∑ k ∈ Finset.Iic AA.vcDim, S.card.choose k := by rw [h5]
    _ ≤ ∑ k ∈ Finset.Iic d, S.card.choose k := by
        apply Finset.sum_le_sum_of_subset
        exact Finset.Iic_subset_Iic.mpr h4
    _ = ∑ k ∈ Finset.range (d + 1), S.card.choose k := by
        rw [Nat.range_succ_eq_Iic]
private theorem growth_function_le_sum_choose_set {X : Type u}
    (C : ConceptClass X Bool) (d m : ℕ) (_hdm : d ≤ m) (hvc : VCDim X C = ↑d) :
    GrowthFunction X C m ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose m i := by
  unfold GrowthFunction
  apply csSup_le'
  intro n hn
  obtain ⟨⟨S, hSm⟩, rfl⟩ := hn
  change ({ f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x } : Set _).ncard ≤ _
  calc ({ f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x } : Set _).ncard
      ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose S.card i :=
        ncard_restrictions_le_sum_choose_set C S d hvc
    _ = ∑ i ∈ Finset.range (d + 1), Nat.choose m i := by rw [hSm]
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {X : Type u} (C : ConceptClass X Bool)
    (d m : ℕ) (hd : 0 < d) (hdm : d ≤ m) (hvc : VCDim X C = ↑d) :
    GrowthFunction X C m ≤ (Real.exp 1 * m / d) ^ d := by
  -- Decompose: GF ≤ ∑ C(m,i) ≤ (em/d)^d
  have h1 : GrowthFunction X C m ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose m i :=
    growth_function_le_sum_choose_set C d m hdm hvc
  have h2 : (∑ i ∈ Finset.range (d + 1), Nat.choose m i : ℝ) ≤ (Real.exp 1 * ↑m / ↑d) ^ d :=
    sum_choose_le_exp_pow d m hd hdm
  -- Chain: need to go from ℕ inequality to ℝ
  calc (↑(GrowthFunction X C m) : ℝ)
      ≤ ↑(∑ i ∈ Finset.range (d + 1), Nat.choose m i) := by
        exact_mod_cast h1
    _ = (∑ i ∈ Finset.range (d + 1), (Nat.choose m i : ℝ)) := by push_cast; rfl
    _ ≤ (Real.exp 1 * ↑m / ↑d) ^ d := h2
