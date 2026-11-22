-- Prove2me | solution 1 for vcdim_finite_imp_growth_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:34:08.408846+00:00
-- url     : https://prove2.me/submissions/c6c1d310-5359-4386-b8ef-bcf4136ef904

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u)
    (C : ConceptClass X Bool) (hC : VCDim X C < ⊤) :
    ∃ (d : ℕ), ∀ (m : ℕ), d ≤ m →
      GrowthFunction X C m ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose m i := by
  -- Extract v from VCDim X C = ↑v (finite).
  obtain ⟨v, hv⟩ : ∃ v : ℕ, VCDim X C = (v : WithTop ℕ) := by
    rcases (WithTop.ne_top_iff_exists.mp (ne_of_lt hC)) with ⟨n, hn⟩
    exact ⟨n, hn.symm⟩
  -- Witness: d = v. Sauer-Shelah gives GrowthFunction(m) ≤ ∑_{i≤v} C(m,i) for all m.
  have : DecidableEq X := Classical.decEq X
  use v
  intro m hm
  have hvcdim_eq : VCDim X C = (v : WithTop ℕ) := hv
  -- Sauer-Shelah: GrowthFunction X C m ≤ ∑_{i≤v} C(m,i)
  -- For each S with |S| = m, bound ncard(restrictions) using Mathlib on local family.
  unfold GrowthFunction
  apply csSup_le'
  rintro n ⟨⟨S, hSm⟩, rfl⟩
  -- Beta-reduce the goal from (fun S => ...) ⟨S, hSm⟩ to the set ncard
  change { f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x }.ncard ≤
    ∑ i ∈ Finset.range (v + 1), m.choose i
  set RS : Set (↥S → Bool) := { f | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x }
  have hRS_finite : Set.Finite RS := Set.Finite.subset Set.finite_univ (Set.subset_univ _)
  set RS_fs := hRS_finite.toFinset
  have hRS_ncard : RS.ncard = RS_fs.card :=
    Set.ncard_eq_toFinset_card RS hRS_finite
  rw [hRS_ncard]
  -- Build Finset (Finset ↥S) via f ↦ {x | f x = true}
  have : DecidableEq ↥S := Classical.typeDecidableEq _
  have : DecidableEq (Finset ↥S) := Classical.typeDecidableEq _
  let toSub : (↥S → Bool) → Finset ↥S :=
    fun f => Finset.univ.filter (fun x => f x = true)
  have h_toSub_inj : Function.Injective toSub := by
    intro f g hfg; funext x
    have := Finset.ext_iff.mp hfg x
    simp only [toSub, Finset.mem_filter, Finset.mem_univ, true_and] at this
    cases hf : f x <;> cases hg : g x <;> simp_all
  set 𝒜 := RS_fs.image toSub
  have h1 : RS_fs.card = 𝒜.card :=
    (Finset.card_image_of_injective _ h_toSub_inj).symm
  have h2 : 𝒜.card ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
  have h3 := @Finset.card_shatterer_le_sum_vcDim ↥S _ 𝒜
  -- Key: vcDim(𝒜) ≤ v — if 𝒜 shatters T then C shatters T.map val, so |T| ≤ v
  have h_vcdim_le : 𝒜.vcDim ≤ v := by
    simp only [Finset.vcDim]
    apply Finset.sup_le
    intro T hT_mem
    have hT_shat : 𝒜.Shatters T := Finset.mem_shatterer.mp hT_mem
    suffices hT_lift : Shatters X C (T.map ⟨Subtype.val, Subtype.val_injective⟩) by
      have : ((T.map ⟨Subtype.val, Subtype.val_injective⟩).card : WithTop ℕ) ≤ v := by
        calc ((T.map ⟨Subtype.val, Subtype.val_injective⟩).card : WithTop ℕ)
            ≤ VCDim X C := le_iSup₂_of_le _ hT_lift le_rfl
          _ = ↑v := hvcdim_eq
      rw [Finset.card_map] at this; exact_mod_cast this
    -- Shattering lift: 𝒜.Shatters T → Shatters X C (T.map val)
    intro f
    -- Pull f back to t ⊆ T using 𝒜.Shatters, then extract c ∈ C
    let fb : ↥S → Bool := fun y =>
      if hy : y ∈ T then
        f ⟨↑y, Finset.mem_map.mpr ⟨y, hy, rfl⟩⟩
      else false
    let t : Finset ↥S := T.filter (fun y => fb y = true)
    have ht_sub : t ⊆ T := Finset.filter_subset _ _
    obtain ⟨A, hA_mem, hTA⟩ := hT_shat ht_sub
    -- A ∈ 𝒜 = RS_fs.image toSub
    have hA_mem2 := Finset.mem_image.mp hA_mem
    obtain ⟨g, hg_fs, hg_eq⟩ := hA_mem2
    have hg_RS : g ∈ RS := hRS_finite.mem_toFinset.mp hg_fs
    obtain ⟨c, hcC, hcg⟩ := hg_RS
    refine ⟨c, hcC, ?_⟩
    intro ⟨x, hx_mem⟩
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx_mem
    obtain ⟨y, hyT, rfl⟩ := hx_mem
    -- c ↑y = g y (from hcg), and g y = fb y (from T ∩ A = t), and fb y = f ⟨↑y, ...⟩
    have hcgy : c ↑y = g y := hcg y
    have hy_in_A : y ∈ A ↔ g y = true := by
      subst hg_eq; simp [toSub, Finset.mem_filter]
    have hy_in_t : y ∈ t ↔ fb y = true := by
      simp [t, Finset.mem_filter, hyT]
    have hy_inter : y ∈ T ∩ A ↔ y ∈ t := by
      constructor <;> intro h
      · exact (Finset.ext_iff.mp hTA y).mp h
      · exact (Finset.ext_iff.mp hTA y).mpr h
    have hy_fb : fb y = f ⟨↑y, Finset.mem_map.mpr ⟨y, hyT, rfl⟩⟩ := by
      simp [fb, hyT]
    have key : g y = fb y := by
      -- From hy_inter: y ∈ T ∩ A ↔ y ∈ t
      -- g y = true ↔ y ∈ A, fb y = true ↔ y ∈ t, y ∈ T
      -- So g y = true ↔ y ∈ A ↔ (y ∈ T ∧ y ∈ A) ↔ y ∈ T ∩ A ↔ y ∈ t ↔ fb y = true
      cases hgy : g y <;> cases hfby : fb y
      · rfl
      · exfalso
        have : y ∈ t := hy_in_t.mpr hfby
        have : y ∈ T ∩ A := hy_inter.mpr this
        have := Finset.mem_inter.mp this
        simp_all
      · exfalso
        have : y ∈ A := hy_in_A.mpr hgy
        have : y ∈ T ∩ A := Finset.mem_inter.mpr ⟨hyT, this⟩
        simp_all
      · rfl
    rw [hcgy, key, hy_fb]
  -- Assembly: RS_fs.card ≤ ∑ C(m, i) for i ≤ v
  have h5 : Fintype.card ↥S = S.card := Fintype.card_coe S
  calc RS_fs.card
      = 𝒜.card := h1
    _ ≤ 𝒜.shatterer.card := h2
    _ ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, (Fintype.card ↥S).choose k := h3
    _ = ∑ k ∈ Finset.Iic 𝒜.vcDim, S.card.choose k := by rw [h5]
    _ ≤ ∑ k ∈ Finset.Iic v, S.card.choose k := by
        apply Finset.sum_le_sum_of_subset
        exact Finset.Iic_subset_Iic.mpr h_vcdim_le
    _ = ∑ k ∈ Finset.range (v + 1), S.card.choose k := by
        congr 1; ext x; simp [Finset.mem_Iic, Finset.mem_range]
    _ = ∑ k ∈ Finset.range (v + 1), m.choose k := by rw [hSm]
