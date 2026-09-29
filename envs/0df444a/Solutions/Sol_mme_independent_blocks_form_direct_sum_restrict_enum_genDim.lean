-- Prove2me | solution 1 for mme_independent_blocks_form_direct_sum_restrict_enum_genDim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-06-05T01:31:06.479516+00:00
-- url     : https://prove2.me/submissions/19796994-c5c0-4116-bf1b-a3e1bf7ab068

import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_tensor_rank

open MME

universe u

set_option maxHeartbeats 800000

namespace MMEIndepBlocksEnumGenDimHelpers

/-! ## Private helpers for the general-dimension enum-injective form. -/

open PiTensorProduct DirectSum

variable {K : Type u} [Field K]

/-- For any `T : TensorObj K d` with grading `G : T.TypeGrading t` and any
multi-type `σ : Fin d → Fin t`, the block subtensor `G.blockSubtensor σ`
is a `Restrict` of `T`, via the witness `f i = G.blockProj i (σ i)`. -/
private theorem blockSubtensor_restrict {d : ℕ} {T : TensorObj K d}
    {t : ℕ} (G : T.TypeGrading t) (σ : Fin d → Fin t) :
    TensorObj.Restrict (G.blockSubtensor σ) T :=
  ⟨fun i => G.blockProj i (σ i), rfl⟩

/-- Concrete formula for `blockProj` in terms of the underlying bijection. -/
private lemma blockProj_eq {d : ℕ} {T : TensorObj K d}
    {t : ℕ} (G : T.TypeGrading t) (i : Fin d) (α : Fin t) (x : T.V i) :
    G.blockProj i α x =
      DirectSum.component K (Fin t)
        (fun β => (G.classOf i β : Submodule K (T.V i))) α
        ((G.modeLequiv i).symm x) := rfl

/-- The `(modeLequiv).symm` is by definition the symm of `ofBijective coeLinearMap _`. -/
private lemma modeLequiv_symm_apply {d : ℕ} {T : TensorObj K d}
    {t : ℕ} (G : T.TypeGrading t) (i : Fin d) (x : T.V i) :
    (G.modeLequiv i).symm x =
      (LinearEquiv.ofBijective
        (DirectSum.coeLinearMap fun α => (G.classOf i α : Submodule K (T.V i)))
        (G.is_internal i)).symm x := rfl

/-- For `v ∈ G.classOf i α`, the `α`-component of `(modeLequiv).symm v` equals `⟨v, _⟩`. -/
private lemma component_modeLequiv_symm_of_mem
    {d : ℕ} {T : TensorObj K d} {t : ℕ} (G : T.TypeGrading t)
    (i : Fin d) (α : Fin t) (v : T.V i) (hv : v ∈ G.classOf i α) :
    (DirectSum.component K (Fin t)
        (fun β => (G.classOf i β : Submodule K (T.V i))) α
        ((G.modeLequiv i).symm v) : G.classOf i α) = ⟨v, hv⟩ := by
  rw [modeLequiv_symm_apply]
  show ((LinearEquiv.ofBijective
        (DirectSum.coeLinearMap fun β => (G.classOf i β : Submodule K (T.V i)))
        (G.is_internal i)).symm v) α = ⟨v, hv⟩
  exact DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem (G.is_internal i) hv

/-- For `v ∈ G.classOf i α` and `α' ≠ α`, the `α'`-component of `(modeLequiv).symm v` is 0. -/
private lemma component_modeLequiv_symm_of_mem_ne
    {d : ℕ} {T : TensorObj K d} {t : ℕ} (G : T.TypeGrading t)
    (i : Fin d) {α α' : Fin t} (hαα' : α ≠ α') (v : T.V i) (hv : v ∈ G.classOf i α) :
    (DirectSum.component K (Fin t)
        (fun β => (G.classOf i β : Submodule K (T.V i))) α'
        ((G.modeLequiv i).symm v) : G.classOf i α') = 0 := by
  rw [modeLequiv_symm_apply]
  show ((LinearEquiv.ofBijective
        (DirectSum.coeLinearMap fun β => (G.classOf i β : Submodule K (T.V i)))
        (G.is_internal i)).symm v) α' = 0
  exact DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem_ne (G.is_internal i) hαα' hv

/-- `subtype α ∘ G.blockProj i α` is the identity on `G.classOf i α`. -/
private lemma subtype_comp_blockProj_self_apply
    {d : ℕ} {T : TensorObj K d} {t : ℕ} (G : T.TypeGrading t)
    (i : Fin d) (α : Fin t) (v : T.V i) (hv : v ∈ G.classOf i α) :
    ((G.classOf i α).subtype : G.classOf i α →ₗ[K] T.V i) (G.blockProj i α v) = v := by
  rw [blockProj_eq]
  have h := component_modeLequiv_symm_of_mem G i α v hv
  show ((DirectSum.component K (Fin t)
        (fun β => (G.classOf i β : Submodule K (T.V i))) α
        ((G.modeLequiv i).symm v) : G.classOf i α) : T.V i) = v
  rw [h]

/-- `subtype α' ∘ G.blockProj i α'` applied to `v ∈ G.classOf i α` (`α ≠ α'`) is 0. -/
private lemma subtype_comp_blockProj_ne_apply
    {d : ℕ} {T : TensorObj K d} {t : ℕ} (G : T.TypeGrading t)
    (i : Fin d) {α α' : Fin t} (hαα' : α ≠ α') (v : T.V i) (hv : v ∈ G.classOf i α) :
    ((G.classOf i α').subtype : G.classOf i α' →ₗ[K] T.V i) (G.blockProj i α' v) = 0 := by
  rw [blockProj_eq]
  have h := component_modeLequiv_symm_of_mem_ne G i hαα' v hv
  show ((DirectSum.component K (Fin t)
        (fun β => (G.classOf i β : Submodule K (T.V i))) α'
        ((G.modeLequiv i).symm v) : G.classOf i α') : T.V i) = 0
  rw [h]
  rfl

/-- `(LinearMap.id : T.V i →ₗ[K] T.V i) = ∑ α : Fin t, (subtype α) ∘ blockProj i α`. -/
private lemma id_eq_sum_subtype_blockProj
    {d : ℕ} {T : TensorObj K d} {t : ℕ} (G : T.TypeGrading t) (i : Fin d) :
    (LinearMap.id : T.V i →ₗ[K] T.V i) =
      ∑ α : Fin t,
        ((G.classOf i α).subtype : G.classOf i α →ₗ[K] T.V i) ∘ₗ G.blockProj i α := by
  ext x
  simp only [LinearMap.id_coe, id_eq, LinearMap.coe_sum, LinearMap.coe_comp,
    Function.comp_apply, Finset.sum_apply]
  have h1 : ∀ α : Fin t,
      ((G.classOf i α).subtype : G.classOf i α →ₗ[K] T.V i) ((G.blockProj i α) x) =
        ((((G.modeLequiv i).symm x) : (⨁ α : Fin t, (G.classOf i α : Submodule K (T.V i)))) α
          : T.V i) := by
    intro α
    rfl
  simp_rw [h1]
  have hsum :
      ∑ α : Fin t,
        ((((G.modeLequiv i).symm x) :
          (⨁ α : Fin t, (G.classOf i α : Submodule K (T.V i)))) α : T.V i) =
      (G.modeLequiv i) ((G.modeLequiv i).symm x) := by
    set d : (⨁ α : Fin t, (G.classOf i α : Submodule K (T.V i))) :=
        (G.modeLequiv i).symm x with hd_def
    have hd_sum : d = ∑ α : Fin t, DirectSum.of _ α (d α) := (DirectSum.sum_univ_of d).symm
    have hcoe :
        (G.modeLequiv i) d =
          DirectSum.coeLinearMap (fun α => (G.classOf i α : Submodule K (T.V i))) d := rfl
    rw [hcoe]
    conv_rhs => rw [hd_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [DirectSum.coeLinearMap_of]
  rw [hsum]
  rw [(G.modeLequiv i).apply_symm_apply]

/-- `T.t = ∑_σ map (subtype) (G.blockTensor σ)` (block decomposition), general `d`. -/
private lemma blockDecomp_T_t
    {d : ℕ} {T : TensorObj K d} {t : ℕ} (G : T.TypeGrading t) :
    (∑ σ : Fin d → Fin t,
      PiTensorProduct.map
        (fun i => ((G.classOf i (σ i)).subtype :
          G.classOf i (σ i) →ₗ[K] T.V i))
        (G.blockTensor σ)) = T.t := by
  have hid : (LinearMap.id : PiTensorProduct K T.V →ₗ[K] PiTensorProduct K T.V) =
      ∑ σ : Fin d → Fin t,
        (PiTensorProduct.map
          (fun i => ((G.classOf i (σ i)).subtype : G.classOf i (σ i) →ₗ[K] T.V i)
            ∘ₗ G.blockProj i (σ i))) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.id_coe, id_eq,
      LinearMap.coe_sum, Finset.sum_apply]
    simp_rw [PiTensorProduct.map_tprod]
    have h_each : ∀ i,
        v i = ∑ α : Fin t,
          ((G.classOf i α).subtype : G.classOf i α →ₗ[K] T.V i) (G.blockProj i α (v i)) := by
      intro i
      have hid := id_eq_sum_subtype_blockProj G i
      have hv : v i = (LinearMap.id : T.V i →ₗ[K] T.V i) (v i) := rfl
      conv_lhs => rw [hv, hid]
      simp only [LinearMap.coe_sum, LinearMap.coe_comp, Function.comp_apply, Finset.sum_apply]
    have hv_sum :
        (fun i => v i) =
          (fun i => ∑ α : Fin t,
            ((G.classOf i α).subtype : G.classOf i α →ₗ[K] T.V i) (G.blockProj i α (v i))) := by
      funext i; exact h_each i
    conv_lhs => rw [show v = (fun i => v i) from rfl, hv_sum]
    rw [MultilinearMap.map_sum (PiTensorProduct.tprod K) _]
    simp only [LinearMap.coe_comp, Function.comp_apply]
  calc (∑ σ : Fin d → Fin t,
          PiTensorProduct.map
            (fun i => ((G.classOf i (σ i)).subtype :
              G.classOf i (σ i) →ₗ[K] T.V i))
            (G.blockTensor σ))
      = ∑ σ : Fin d → Fin t,
          PiTensorProduct.map
            (fun i => ((G.classOf i (σ i)).subtype :
              G.classOf i (σ i) →ₗ[K] T.V i) ∘ₗ G.blockProj i (σ i))
            T.t := by
        refine Finset.sum_congr rfl ?_
        intro σ _
        show PiTensorProduct.map _ (G.blockTensor σ) = _
        unfold TensorObj.TypeGrading.blockTensor
        rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    _ = (∑ σ : Fin d → Fin t,
          PiTensorProduct.map
            (fun i => ((G.classOf i (σ i)).subtype :
              G.classOf i (σ i) →ₗ[K] T.V i) ∘ₗ G.blockProj i (σ i))) T.t := by
        rw [LinearMap.sum_apply]
    _ = (LinearMap.id : PiTensorProduct K T.V →ₗ[K] PiTensorProduct K T.V) T.t := by
        rw [← hid]
    _ = T.t := rfl

/-- Recursive "slot-j" inclusion `(f j).V i →ₗ[K] (bigAdd f).V i`. Defined by induction
on `k`. -/
private noncomputable def slot {d : ℕ} :
    (k : ℕ) → (f : Fin k → TensorObj K d) → (j : Fin k) → (i : Fin d) →
      (f j).V i →ₗ[K] (TensorObj.bigAdd f).V i
  | 0,     _, j, _ => j.elim0
  | 1,     f, j, i =>
      Fin.cases
        (motive := fun j => (f j).V i →ₗ[K] (f 0).V i)
        (LinearMap.id : (f 0).V i →ₗ[K] (f 0).V i)
        (fun j' => j'.elim0)
        j
  | (n+2), f, j, i =>
      Fin.cases
        (motive := fun j => (f j).V i →ₗ[K]
          (TensorObj.add (f 0) (TensorObj.bigAdd (fun k => f k.succ))).V i)
        (LinearMap.inl K ((f 0).V i) ((TensorObj.bigAdd (fun k => f k.succ)).V i))
        (fun j' =>
          (LinearMap.inr K ((f 0).V i) ((TensorObj.bigAdd (fun k => f k.succ)).V i)).comp
            (slot (n+1) (fun k => f k.succ) j' i))
        j

/-- `slot` for `k = 1` is the identity (`bigAdd f = f 0`). -/
private lemma slot_one_zero {d : ℕ} (f : Fin 1 → TensorObj K d) (i : Fin d) :
    slot 1 f 0 i = (LinearMap.id : (f 0).V i →ₗ[K] (f 0).V i) := by
  rfl

/-- `slot` for `k = n+2` and `j = 0` is `inl`. -/
private lemma slot_succ_zero {d n : ℕ} (f : Fin (n+2) → TensorObj K d) (i : Fin d) :
    slot (n+2) f 0 i =
      LinearMap.inl K ((f 0).V i) ((TensorObj.bigAdd (fun j => f j.succ)).V i) := by
  rfl

/-- `slot` for `k = n+2` and `j = j'.succ` is `inr ∘ slot j'`. -/
private lemma slot_succ_succ {d n : ℕ} (f : Fin (n+2) → TensorObj K d) (j' : Fin (n+1))
    (i : Fin d) :
    slot (n+2) f j'.succ i =
      (LinearMap.inr K ((f 0).V i) ((TensorObj.bigAdd (fun j => f j.succ)).V i)).comp
        (slot (n+1) (fun j => f j.succ) j' i) := by
  rfl

/-- The key identity: `(bigAdd f).t = ∑_j map (slot f j) (f j).t`. -/
private lemma bigAdd_t_eq_sum_slot {d : ℕ} :
    ∀ (k : ℕ) (f : Fin k → TensorObj K d),
    (TensorObj.bigAdd f).t =
      ∑ j : Fin k, PiTensorProduct.map (fun i => slot k f j i) (f j).t
  | 0,     _ => by
      show (TensorObj.zeroObj : TensorObj K d).t = ∑ j : Fin 0, _
      simp only [Finset.univ_eq_empty]
      rfl
  | 1,     f => by
      show (f 0).t = ∑ j : Fin 1, PiTensorProduct.map (fun i => slot 1 f j i) (f j).t
      rw [Fin.sum_univ_one]
      have h : (fun i : Fin d => slot 1 f 0 i) =
          (fun i : Fin d => (LinearMap.id : (f 0).V i →ₗ[K] (f 0).V i)) := by
        funext i
        rw [slot_one_zero]
      rw [h]
      change (f 0).t = (PiTensorProduct.map fun i => (LinearMap.id : (f 0).V i →ₗ[K] (f 0).V i)) (f 0).t
      rw [PiTensorProduct.map_id]
      rfl
  | (n+2), f => by
      show (TensorObj.add (f 0) (TensorObj.bigAdd (fun j => f j.succ))).t =
        ∑ j : Fin (n+2), PiTensorProduct.map (fun i => slot (n+2) f j i) (f j).t
      show PiTensorProduct.map (fun i =>
              LinearMap.inl K ((f 0).V i)
                ((TensorObj.bigAdd (fun j => f j.succ)).V i)) (f 0).t +
          PiTensorProduct.map (fun i =>
              LinearMap.inr K ((f 0).V i)
                ((TensorObj.bigAdd (fun j => f j.succ)).V i))
            (TensorObj.bigAdd (fun j => f j.succ)).t =
        ∑ j : Fin (n+2), PiTensorProduct.map (fun i => slot (n+2) f j i) (f j).t
      rw [Fin.sum_univ_succ]
      rw [bigAdd_t_eq_sum_slot (n+1) (fun j => f j.succ)]
      have h_inl : PiTensorProduct.map (fun i =>
            LinearMap.inl K ((f 0).V i)
              ((TensorObj.bigAdd (fun j => f j.succ)).V i)) (f 0).t =
          PiTensorProduct.map (fun i => slot (n+2) f 0 i) (f 0).t := by
        congr 1
      rw [h_inl]
      congr 1
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
      congr 1

end MMEIndepBlocksEnumGenDimHelpers

open MMEIndepBlocksEnumGenDimHelpers

/-- General-dimension version: see file header. -/
theorem solution
    {K : Type u} [Field K] {d : ℕ} {T : TensorObj K d} {t : ℕ}
    (G : T.TypeGrading t)
    (C : Finset (Fin d → Fin t))
    (σs : Fin C.card → (Fin d → Fin t))
    (hσs : ∀ j, σs j ∈ C)
    (hσs_inj : Function.Injective σs)
    (hDisj : ∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' → ∀ i : Fin d, σ i ≠ σ' i)
    (hSupp : ∀ σ : Fin d → Fin t, σ ∉ C → G.blockTensor σ = 0) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j => G.blockSubtensor (σs j))) T := by
  classical
  set B : Fin C.card → TensorObj K d := fun j => G.blockSubtensor (σs j) with hB_def
  refine ⟨fun i =>
      ∑ j : Fin C.card,
        (slot C.card B j i).comp (G.blockProj i (σs j i)), ?_⟩
  rw [bigAdd_t_eq_sum_slot C.card B]
  rw [← blockDecomp_T_t G]
  rw [map_sum]
  have h_zero_outside : ∀ σ ∉ C,
      PiTensorProduct.map (fun i =>
          ∑ j : Fin C.card,
            (slot C.card B j i).comp (G.blockProj i (σs j i)))
        (PiTensorProduct.map
          (fun i => ((G.classOf i (σ i)).subtype :
            G.classOf i (σ i) →ₗ[K] T.V i))
          (G.blockTensor σ)) = 0 := by
    intro σ hσ
    rw [hSupp σ hσ, map_zero, map_zero]
  have h_inside : ∀ (j₀ : Fin C.card),
      PiTensorProduct.map (fun i =>
          ∑ j : Fin C.card,
            (slot C.card B j i).comp (G.blockProj i (σs j i)))
        (PiTensorProduct.map
          (fun i => ((G.classOf i ((σs j₀) i)).subtype :
            G.classOf i ((σs j₀) i) →ₗ[K] T.V i))
          (G.blockTensor (σs j₀))) =
      PiTensorProduct.map (fun i => slot C.card B j₀ i) (G.blockTensor (σs j₀)) := by
    intro j₀
    rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    have hmap_eq : (fun i =>
          (∑ j : Fin C.card,
            (slot C.card B j i).comp (G.blockProj i (σs j i))).comp
              ((G.classOf i (σs j₀ i)).subtype :
                G.classOf i (σs j₀ i) →ₗ[K] T.V i)) =
        (fun i => slot C.card B j₀ i) := by
      funext i
      ext v
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_sum,
        Finset.sum_apply]
      rw [Finset.sum_eq_single j₀]
      · exact congrArg (slot C.card B j₀ i)
          (Subtype.ext
            (subtype_comp_blockProj_self_apply G i (σs j₀ i) (v : T.V i) v.2))
      · intro j _ hjne
        have hσne : σs j ≠ σs j₀ := fun h => hjne (hσs_inj h)
        have hijne : σs j i ≠ σs j₀ i := hDisj (σs j) (hσs j) (σs j₀) (hσs j₀) hσne i
        have h0 : G.blockProj i (σs j i) ((G.classOf i (σs j₀ i)).subtype v) = 0 := by
          apply Subtype.ext
          exact subtype_comp_blockProj_ne_apply G i hijne.symm (v : T.V i) v.2
        calc (slot C.card B j i) ((G.blockProj i (σs j i)) ((G.classOf i (σs j₀ i)).subtype v))
            = (slot C.card B j i) 0 := by rw [h0]; rfl
          _ = 0 := LinearMap.map_zero _
      · intro h
        exact absurd (Finset.mem_univ j₀) h
    conv_lhs => rw [show (fun i => (∑ j : Fin C.card,
            (slot C.card B j i).comp (G.blockProj i (σs j i))).comp
              ((G.classOf i (σs j₀ i)).subtype :
                G.classOf i (σs j₀ i) →ₗ[K] T.V i)) =
        (fun i => slot C.card B j₀ i) from hmap_eq]
    rfl
  have h_split :
      (∑ σ : Fin d → Fin t,
        PiTensorProduct.map (fun i =>
          ∑ j : Fin C.card,
            (slot C.card B j i).comp (G.blockProj i (σs j i)))
          (PiTensorProduct.map
            (fun i => ((G.classOf i (σ i)).subtype :
              G.classOf i (σ i) →ₗ[K] T.V i))
            (G.blockTensor σ))) =
      ∑ σ ∈ C,
        PiTensorProduct.map (fun i =>
          ∑ j : Fin C.card,
            (slot C.card B j i).comp (G.blockProj i (σs j i)))
          (PiTensorProduct.map
            (fun i => ((G.classOf i (σ i)).subtype :
              G.classOf i (σ i) →ₗ[K] T.V i))
            (G.blockTensor σ)) := by
    symm
    apply Finset.sum_subset
    · intro σ _
      exact Finset.mem_univ σ
    · intro σ _ hσC
      exact h_zero_outside σ hσC
  rw [h_split]
  have hRange : ∀ j : Fin C.card, σs j ∈ C := hσs
  refine (Finset.sum_bij (fun j (_ : j ∈ (Finset.univ : Finset (Fin C.card))) => σs j)
      (fun j _ => hσs j) ?_ ?_ ?_).symm
  · intro j₁ _ j₂ _ h
    exact hσs_inj h
  · intro σ hσ
    have h_image_eq_C : C = Finset.image σs Finset.univ := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro σ hσim
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hσim
        obtain ⟨j, hjσ⟩ := hσim
        rw [← hjσ]
        exact hσs j
      · rw [Finset.card_image_of_injective _ hσs_inj]
        simp
    rw [h_image_eq_C] at hσ
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hσ
    obtain ⟨j, hj⟩ := hσ
    exact ⟨j, Finset.mem_univ j, hj⟩
  · intro j _
    exact (h_inside j).symm
