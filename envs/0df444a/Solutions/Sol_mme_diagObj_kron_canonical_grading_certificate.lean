-- Prove2me | solution 1 for mme_diagObj_kron_canonical_grading_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T16:49:33.583547+00:00
-- url     : https://prove2.me/submissions/327e89af-d409-4789-82cc-974e5c1308e2

import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_block_subtensor
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Tactic

open PiTensorProduct TensorProduct BigOperators DirectSum Module

set_option autoImplicit false

namespace MME

universe u

set_option maxHeartbeats 800000

namespace DiagKronScratch

namespace TensorObj.TypeGrading

variable {K : Type u} [Field K] {d t : ℕ} {T : TensorObj K d}

lemma blockProj_apply_mem
    (G : T.TypeGrading t) (i : Fin d) (a : Fin t)
    (x : T.V i) (hx : x ∈ G.decomp i a) :
    G.blockProj i a x = ⟨x, hx⟩ := by
  unfold TensorObj.TypeGrading.blockProj TensorObj.TypeGrading.modeLequiv
  apply Subtype.ext
  simp only [LinearMap.comp_apply]
  rw [← DirectSum.apply_eq_component]
  exact congrArg Subtype.val
    ((G.is_internal i).ofBijective_coeLinearMap_of_mem hx)

lemma blockProj_apply_mem_ne
    (G : T.TypeGrading t) (i : Fin d) (a b : Fin t) (hab : a ≠ b)
    (x : T.V i) (hx : x ∈ G.decomp i b) :
    G.blockProj i a x = 0 := by
  unfold TensorObj.TypeGrading.blockProj TensorObj.TypeGrading.modeLequiv
  simp only [LinearMap.comp_apply]
  rw [← DirectSum.apply_eq_component]
  exact (G.is_internal i).ofBijective_coeLinearMap_of_mem_ne hab.symm hx

end TensorObj.TypeGrading

section BasisGrading

variable {K : Type u} [Field K]
variable {V : Type u} [AddCommGroup V] [Module K V]
variable {ι κ : Type*} [DecidableEq κ]

def basisGrade (b : Basis ι K V) (g : ι → κ) (a : κ) : Submodule K V :=
  Submodule.span K (b '' {i | g i = a})

theorem basisGrade_isInternal (b : Basis ι K V) (g : ι → κ) :
    DirectSum.IsInternal (basisGrade b g) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro a
    simp_rw [basisGrade]
    rw [← Submodule.span_iUnion₂]
    rw [← Set.image_iUnion₂]
    apply b.linearIndependent.disjoint_span_image
    rw [Set.disjoint_left]
    intro i hi hi'
    simp only [Set.mem_setOf_eq] at hi
    rcases Set.mem_iUnion.mp hi' with ⟨c, hi'⟩
    rcases Set.mem_iUnion.mp hi' with ⟨hc, hi'⟩
    exact hc (hi'.symm.trans hi)
  · change (⨆ a, Submodule.span K (b '' {i | g i = a})) = ⊤
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact le_iSup (fun a => Submodule.span K (b '' {i | g i = a})) (g i)
      (Submodule.subset_span ⟨i, rfl, rfl⟩)

theorem basis_mem_basisGrade (b : Basis ι K V) (g : ι → κ) (i : ι) :
    b i ∈ basisGrade b g (g i) := by
  exact Submodule.subset_span ⟨i, rfl, rfl⟩

end BasisGrading

private instance diagKronScalarTower
    (K : Type u) [Field K] (ι : Type*) :
    IsScalarTower K K (ι → K) :=
  IsScalarTower.of_algebraMap_smul (by simp)

private noncomputable def diagKronBasis
    (K : Type u) [Field K] (S : TensorObj K 3) (n : ℕ) (s : Fin 3) :
    Basis (Fin n × Fin (Module.finrank K (S.V s))) K
      ((TensorObj.kron (TensorObj.diagObj K 3 n) S).V s) := by
  exact @Module.Basis.tensorProduct
    K K (Fin n → K) (S.V s)
    (Fin n) (Fin (Module.finrank K (S.V s)))
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance
    ({ smul_assoc := by
        intro a b f
        ext i
        simp [mul_assoc] } : IsScalarTower K K (Fin n → K))
    inferInstance inferInstance
    (Pi.basisFun K (Fin n))
    (Module.finBasis K (S.V s))

private noncomputable def diagKronGrading
    (K : Type u) [Field K] (S : TensorObj K 3) (n : ℕ) :
    (TensorObj.kron (TensorObj.diagObj K 3 n) S).TypeGrading n where
  decomp s := basisGrade (diagKronBasis K S n s) Prod.fst
  is_internal s := basisGrade_isInternal (diagKronBasis K S n s) Prod.fst

private theorem diagKronBasis_apply
    (K : Type u) [Field K] (S : TensorObj K 3) (n : ℕ)
    (s : Fin 3) (j : Fin n) (b : Fin (Module.finrank K (S.V s))) :
    diagKronBasis K S n s (j, b) =
      (Pi.single j 1 : Fin n → K) ⊗ₜ[K] (Module.finBasis K (S.V s)) b := by
  rw [← Pi.basisFun_apply]
  unfold diagKronBasis
  apply Module.Basis.tensorProduct_apply

private noncomputable def diagEmbed
    (K : Type u) [Field K] (S : TensorObj K 3) (n : ℕ)
    (s : Fin 3) (j : Fin n) :
    S.V s →ₗ[K] (TensorObj.kron (TensorObj.diagObj K 3 n) S).V s :=
  TensorProduct.mk K _ _ (Pi.single j 1)

private noncomputable def diagGradeLift
    (K : Type u) [Field K] (S : TensorObj K 3) (n : ℕ)
    (s : Fin 3) (j : Fin n) :
    S.V s →ₗ[K] (diagKronGrading K S n).decomp s j :=
  (Module.finBasis K (S.V s)).constr K (fun b =>
    ⟨diagKronBasis K S n s (j, b),
      basis_mem_basisGrade (diagKronBasis K S n s) Prod.fst (j, b)⟩)

private theorem diagGradeLift_val
    (K : Type u) [Field K] (S : TensorObj K 3) (n : ℕ)
    (s : Fin 3) (j : Fin n) (x : S.V s) :
    ((diagGradeLift K S n s j) x :
      (TensorObj.kron (TensorObj.diagObj K 3 n) S).V s) =
      diagEmbed K S n s j x := by
  have hmaps :
      ((diagKronGrading K S n).decomp s j).subtype.comp
          (diagGradeLift K S n s j) =
        diagEmbed K S n s j := by
    apply (Module.finBasis K (S.V s)).ext
    intro b
    simp only [LinearMap.comp_apply, Submodule.coe_subtype,
      diagGradeLift, Module.Basis.constr_basis]
    rw [diagKronBasis_apply]
    change (Pi.single j 1 : Fin n → K) ⊗ₜ[K]
        (Module.finBasis K (S.V s)) b =
      (Pi.single j 1 : Fin n → K) ⊗ₜ[K]
        (Module.finBasis K (S.V s)) b
    rfl
  exact LinearMap.congr_fun hmaps x

private theorem diagEmbed_mem
    (K : Type u) [Field K] (S : TensorObj K 3) (n : ℕ)
    (s : Fin 3) (j : Fin n) (x : S.V s) :
    diagEmbed K S n s j x ∈ (diagKronGrading K S n).decomp s j := by
  rw [← diagGradeLift_val K S n s j x]
  exact (diagGradeLift K S n s j x).property

private theorem diagBlockProj_embed_same
    (K : Type u) [Field K] (S : TensorObj K 3) (n : ℕ)
    (s : Fin 3) (j : Fin n) (x : S.V s) :
    (diagKronGrading K S n).blockProj s j
        (diagEmbed K S n s j x) =
      ⟨diagEmbed K S n s j x, diagEmbed_mem K S n s j x⟩ := by
  exact TensorObj.TypeGrading.blockProj_apply_mem
    (diagKronGrading K S n) s j _ (diagEmbed_mem K S n s j x)

private theorem diagBlockProj_embed_ne
    (K : Type u) [Field K] (S : TensorObj K 3) (n : ℕ)
    (s : Fin 3) (a j : Fin n) (h : a ≠ j) (x : S.V s) :
    (diagKronGrading K S n).blockProj s a
        (diagEmbed K S n s j x) = 0 := by
  exact TensorObj.TypeGrading.blockProj_apply_mem_ne
    (diagKronGrading K S n) s a j h _ (diagEmbed_mem K S n s j x)

private noncomputable def diagContract
    (K : Type u) [Field K] (S : TensorObj K 3) (n : ℕ)
    (s : Fin 3) (j : Fin n) :
    (TensorObj.kron (TensorObj.diagObj K 3 n) S).V s →ₗ[K] S.V s :=
  (TensorProduct.lid K (S.V s)).toLinearMap.comp
    (TensorProduct.map
      (LinearMap.proj j : (Fin n → K) →ₗ[K] K)
      (LinearMap.id : S.V s →ₗ[K] S.V s))

private theorem diagContract_embed_same
    (K : Type u) [Field K] (S : TensorObj K 3) (n : ℕ)
    (s : Fin 3) (j : Fin n) (x : S.V s) :
    diagContract K S n s j (diagEmbed K S n s j x) = x := by
  unfold diagContract diagEmbed
  change (TensorProduct.lid K (S.V s))
      ((TensorProduct.map
        (LinearMap.proj j : (Fin n → K) →ₗ[K] K)
        (LinearMap.id : S.V s →ₗ[K] S.V s))
        ((Pi.single j 1 : Fin n → K) ⊗ₜ[K] x)) = x
  rw [TensorProduct.map_tmul, TensorProduct.lid_tmul]
  simp [Pi.single_apply]

private noncomputable def diagGradeUnlift
    (K : Type u) [Field K] (S : TensorObj K 3) (n : ℕ)
    (s : Fin 3) (j : Fin n) :
    (diagKronGrading K S n).decomp s j →ₗ[K] S.V s :=
  (diagContract K S n s j).comp
    ((diagKronGrading K S n).decomp s j).subtype

private theorem diagGradeUnlift_proj_embed_same
    (K : Type u) [Field K] (S : TensorObj K 3) (n : ℕ)
    (s : Fin 3) (j : Fin n) (x : S.V s) :
    (diagGradeUnlift K S n s j ∘ₗ
      (diagKronGrading K S n).blockProj s j ∘ₗ
      diagEmbed K S n s j) x = x := by
  simp only [LinearMap.comp_apply, diagGradeUnlift,
    Submodule.coe_subtype]
  rw [diagBlockProj_embed_same]
  exact diagContract_embed_same K S n s j x

private theorem diagGradeUnlift_proj_embed_ne
    (K : Type u) [Field K] (S : TensorObj K 3) (n : ℕ)
    (s : Fin 3) (a j : Fin n) (h : a ≠ j) (x : S.V s) :
    (diagGradeUnlift K S n s a ∘ₗ
      (diagKronGrading K S n).blockProj s a ∘ₗ
      diagEmbed K S n s j) x = 0 := by
  simp only [LinearMap.comp_apply, diagGradeUnlift]
  rw [diagBlockProj_embed_ne K S n s a j h]
  rfl

private theorem interchange_tprod
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) =
      tprod K (fun i => v i ⊗ₜ[K] w i) := by
  show (interchange (tprod K v)) (tprod K w) = _
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  show (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

private theorem interchange_diag_eq_map
    (K : Type u) [Field K] (S : TensorObj K 3) (n : ℕ) (j : Fin n) :
    interchange
        (tprod K (fun _ : Fin 3 => (Pi.single j 1 : Fin n → K)))
        S.t =
      PiTensorProduct.map (fun s => diagEmbed K S n s j) S.t := by
  induction S.t using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      simp only [map_smul, LinearMap.smul_apply]
      rw [interchange_tprod, PiTensorProduct.map_tprod]
      rfl
  | add x y ihx ihy =>
      simp only [map_add]
      rw [ihx, ihy]
      rfl

private theorem map_zero_of_one_map_zero
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i) (i : Fin d) (hi : f i = 0) :
    PiTensorProduct.map f = 0 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply,
    PiTensorProduct.map_tprod, LinearMap.zero_apply]
  apply MultilinearMap.map_coord_zero (tprod K) i
  rw [hi]
  rfl

private theorem diagSelectedTerm
    (K : Type u) [Field K] (S : TensorObj K 3) (n : ℕ)
    (a j : Fin n) :
    PiTensorProduct.map
        (fun s => diagGradeUnlift K S n s a ∘ₗ
          (diagKronGrading K S n).blockProj s a)
        (interchange
          (tprod K (fun _ : Fin 3 => (Pi.single j 1 : Fin n → K)))
          S.t) =
      if a = j then S.t else 0 := by
  rw [interchange_diag_eq_map]
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  by_cases h : a = j
  · subst j
    rw [if_pos rfl]
    have hmaps :
        (fun s =>
          (diagGradeUnlift K S n s a ∘ₗ
            (diagKronGrading K S n).blockProj s a) ∘ₗ
            diagEmbed K S n s a) =
          (fun _ : Fin 3 => (LinearMap.id : S.V _ →ₗ[K] S.V _)) := by
      funext s
      apply LinearMap.ext
      intro x
      exact diagGradeUnlift_proj_embed_same K S n s a x
    rw [hmaps, PiTensorProduct.map_id]
    rfl
  · rw [if_neg h]
    have hcomponent :
        (fun s =>
          (diagGradeUnlift K S n s a ∘ₗ
            (diagKronGrading K S n).blockProj s a) ∘ₗ
            diagEmbed K S n s j) (0 : Fin 3) = 0 := by
      apply LinearMap.ext
      intro x
      exact diagGradeUnlift_proj_embed_ne K S n 0 a j h x
    rw [map_zero_of_one_map_zero
      (fun s =>
        (diagGradeUnlift K S n s a ∘ₗ
          (diagKronGrading K S n).blockProj s a) ∘ₗ
          diagEmbed K S n s j) 0 hcomponent]
    rfl

private theorem diagConstantBlock_restrict
    (K : Type u) [Field K] (S : TensorObj K 3) (n : ℕ)
    (a : Fin n) :
    TensorObj.Restrict S
      ((diagKronGrading K S n).blockSubtensor (fun _ => a)) := by
  classical
  refine ⟨fun s => diagGradeUnlift K S n s a, ?_⟩
  unfold TensorObj.TypeGrading.blockSubtensor
  unfold TensorObj.TypeGrading.blockTensor
  change PiTensorProduct.map
      (fun s => diagGradeUnlift K S n s a)
      (PiTensorProduct.map
        (fun s => (diagKronGrading K S n).blockProj s a)
        (interchange
          (∑ j : Fin n,
            tprod K (fun _ : Fin 3 => (Pi.single j 1 : Fin n → K)))
          S.t)) = S.t
  refine (congrFun (congrArg DFunLike.coe
    (PiTensorProduct.map_comp _ _)) _).symm.trans ?_
  rw [map_sum]
  simp only [LinearMap.coe_sum, Finset.sum_apply]
  let F := PiTensorProduct.map
    (fun s => diagGradeUnlift K S n s a ∘ₗ
      (diagKronGrading K S n).blockProj s a)
  let f := fun j : Fin n =>
    interchange
      (tprod K (fun _ : Fin 3 => (Pi.single j 1 : Fin n → K)))
      S.t
  change F (∑ j : Fin n, f j) = S.t
  calc
    F (∑ j : Fin n, f j) = ∑ j : Fin n, F (f j) := by
      exact map_sum F f Finset.univ
    _ = ∑ j : Fin n, if a = j then S.t else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact diagSelectedTerm K S n a j
    _ = S.t := by simp

private theorem diagBlockTensor_offDiagonal
    (K : Type u) [Field K] (S : TensorObj K 3) (n : ℕ)
    (σ : Fin 3 → Fin n)
    (hoff : ¬ ∃ j : Fin n, ∀ i : Fin 3, σ i = j) :
    (diagKronGrading K S n).blockTensor σ = 0 := by
  classical
  unfold TensorObj.TypeGrading.blockTensor
  change PiTensorProduct.map
      (fun i => (diagKronGrading K S n).blockProj i (σ i))
      (interchange
        (∑ j : Fin n,
          tprod K (fun _ : Fin 3 => (Pi.single j 1 : Fin n → K)))
        S.t) = 0
  rw [map_sum]
  simp only [LinearMap.coe_sum, Finset.sum_apply]
  let F := PiTensorProduct.map
    (fun i => (diagKronGrading K S n).blockProj i (σ i))
  let f := fun j : Fin n =>
    interchange
      (tprod K (fun _ : Fin 3 => (Pi.single j 1 : Fin n → K)))
      S.t
  change F (∑ j : Fin n, f j) = 0
  calc
    F (∑ j : Fin n, f j) = ∑ j : Fin n, F (f j) := by
      exact map_sum F f Finset.univ
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      dsimp only [F, f]
      rw [interchange_diag_eq_map]
      rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
      have hi : ∃ i : Fin 3, σ i ≠ j := by
        by_contra h
        push_neg at h
        exact hoff ⟨j, h⟩
      obtain ⟨i, hi⟩ := hi
      have hcomponent :
          (fun s =>
            (diagKronGrading K S n).blockProj s (σ s) ∘ₗ
              diagEmbed K S n s j) i = 0 := by
        apply LinearMap.ext
        intro x
        exact diagBlockProj_embed_ne K S n i (σ i) j hi x
      rw [map_zero_of_one_map_zero
        (fun s =>
          (diagKronGrading K S n).blockProj s (σ s) ∘ₗ
            diagEmbed K S n s j) i hcomponent]
      rfl

private def diagConstEmbedding (n : ℕ) :
    Fin n ↪ (Fin 3 → Fin n) where
  toFun j := fun _ => j
  inj' := by
    intro j k h
    exact congrFun h (0 : Fin 3)

theorem canonical_grading_certificate
    {K : Type u} [Field K] (S : TensorObj K 3) (n : ℕ) :
    ∃ (t : ℕ)
        (grading :
          (TensorObj.kron (TensorObj.diagObj K 3 n) S).TypeGrading t)
        (C : Finset (Fin 3 → Fin t))
        (σs : Fin C.card → (Fin 3 → Fin t)),
      (∀ j, σs j ∈ C) ∧
      Function.Injective σs ∧
      (∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' →
        ∀ i : Fin 3, σ i ≠ σ' i) ∧
      (∀ σ : Fin 3 → Fin t, σ ∉ C → grading.blockTensor σ = 0) ∧
      (∀ j, TensorObj.Restrict S
        (grading.blockSubtensor (σs j))) ∧
      C.card = n := by
  classical
  let C : Finset (Fin 3 → Fin n) :=
    Finset.univ.map (diagConstEmbedding n)
  have hcard : C.card = n := by
    simp [C]
  let σs : Fin C.card → (Fin 3 → Fin n) := fun j =>
    diagConstEmbedding n (Fin.cast hcard j)
  refine ⟨n, diagKronGrading K S n, C, σs, ?_, ?_, ?_, ?_, ?_, hcard⟩
  · intro j
    dsimp only [σs]
    simp [C]
  · exact (diagConstEmbedding n).injective.comp (Fin.cast_injective hcard)
  · intro σ hσ σ' hσ' hne i
    rw [Finset.mem_map] at hσ hσ'
    obtain ⟨a, _, ha⟩ := hσ
    obtain ⟨b, _, hb⟩ := hσ'
    subst σ
    subst σ'
    have hab : a ≠ b := by
      intro hab
      subst b
      exact hne rfl
    exact hab
  · intro σ hσ
    apply diagBlockTensor_offDiagonal K S n σ
    rintro ⟨j, hj⟩
    apply hσ
    rw [Finset.mem_map]
    refine ⟨j, Finset.mem_univ j, ?_⟩
    funext i
    exact (hj i).symm
  · intro j
    dsimp only [σs]
    exact diagConstantBlock_restrict K S n (Fin.cast hcard j)

end DiagKronScratch

end MME

open MME BigOperators

universe u

theorem solution
    {K : Type u} [Field K] (S : TensorObj K 3) (n : ℕ) :
    ∃ (t : ℕ)
        (grading :
          (TensorObj.kron (TensorObj.diagObj K 3 n) S).TypeGrading t)
        (C : Finset (Fin 3 → Fin t))
        (σs : Fin C.card → (Fin 3 → Fin t)),
      (∀ j, σs j ∈ C) ∧
      Function.Injective σs ∧
      (∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' →
        ∀ i : Fin 3, σ i ≠ σ' i) ∧
      (∀ σ : Fin 3 → Fin t, σ ∉ C → grading.blockTensor σ = 0) ∧
      (∀ j, TensorObj.Restrict S
        (grading.blockSubtensor (σs j))) ∧
      C.card = n := by
  exact MME.DiagKronScratch.canonical_grading_certificate S n
