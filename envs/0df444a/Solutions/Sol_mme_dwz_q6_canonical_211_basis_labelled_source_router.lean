-- Prove2me | solution 1 for mme_dwz_q6_canonical_211_basis_labelled_source_router
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:07:03.726484+00:00
-- url     : https://prove2.me/submissions/e46ecb74-e270-4469-bd7e-4169e0ee5bd2

import Definitions.Def_mme_CW_square_five_grade_certificate
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_permutation
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_dwz_q6_grade_one_coord_data
import Theorems.Thm_mme_dwz_coarseClassBasis_q6_val
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic

open PiTensorProduct TensorProduct BigOperators DirectSum Module

namespace MME

universe u

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

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
  · apply top_unique
    rw [← b.span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact le_iSup (basisGrade b g) (g i) <|
      Submodule.subset_span ⟨i, rfl, rfl⟩

theorem basis_mem_basisGrade (b : Basis ι K V) (g : ι → κ) (i : ι) :
    b i ∈ basisGrade b g (g i) := by
  exact Submodule.subset_span ⟨i, rfl, rfl⟩

end BasisGrading

section CWSquareCanonical

private def cwCoordGrade (q : ℕ) (a : Fin (q + 2)) : Fin 3 :=
  if a.val = 0 then 0 else if a.val = q + 1 then 2 else 1

private def cwPairGrade (q : ℕ) (ab : Fin (q + 2) × Fin (q + 2)) : Fin 5 :=
  ⟨(cwCoordGrade q ab.1).val + (cwCoordGrade q ab.2).val, by omega⟩

private noncomputable def cwSquareBasis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) :
    Basis (Fin (q + 2) × Fin (q + 2)) K
      ((TensorObj.kron (CWObj K q) (CWObj K q)).V s) := by
  letI : IsScalarTower K K (Fin (q + 2) → K) :=
    IsScalarTower.of_algebraMap_smul (by simp)
  exact match s with
    | ⟨0, _⟩ => Module.Basis.tensorProduct (R := K) (S := K)
        (Pi.basisFun K (Fin (q + 2))) (Pi.basisFun K (Fin (q + 2)))
    | ⟨1, _⟩ => Module.Basis.tensorProduct (R := K) (S := K)
        (Pi.basisFun K (Fin (q + 2))) (Pi.basisFun K (Fin (q + 2)))
    | ⟨2, _⟩ => Module.Basis.tensorProduct (R := K) (S := K)
        (Pi.basisFun K (Fin (q + 2))) (Pi.basisFun K (Fin (q + 2)))

/-- Public alias for the canonical basis used by the explicit source routers
in this file.  A separate compatibility leaf identifies it with the public
DWZ canonical basis. -/
noncomputable def cwSquareRouterBasis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) :=
  cwSquareBasis K q s

/-- Public alias for the canonical grading used by the explicit source
routers in this file. -/
noncomputable def cwSquareRouterGrading
    (K : Type u) [Field K] (q : ℕ) :=
  cwSquareCanonicalGrading K q

private theorem cwSquareCanonical_blockProj_basis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (a : Fin 5) (i j : Fin (q + 2)) :
    (cwSquareCanonicalGrading K q).blockProj s a
        (cwSquareBasis K q s (i, j)) =
      if h : cwPairGrade q (i, j) = a then
        ⟨cwSquareBasis K q s (i, j), by
          rw [← h]
          exact basis_mem_basisGrade (cwSquareBasis K q s) (cwPairGrade q) (i, j)⟩
      else 0 := by
  split_ifs with h
  · subst a
    exact TensorObj.TypeGrading.blockProj_apply_mem
      (cwSquareCanonicalGrading K q) s (cwPairGrade q (i, j)) _
      (basis_mem_basisGrade (cwSquareBasis K q s) (cwPairGrade q) (i, j))
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwSquareCanonicalGrading K q) s a (cwPairGrade q (i, j)) (Ne.symm h) _
      (basis_mem_basisGrade (cwSquareBasis K q s) (cwPairGrade q) (i, j))

private def cwVec
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (a : Fin (q + 2)) :
    CWSpace K q s :=
  match s with
  | ⟨0, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)
  | ⟨1, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)
  | ⟨2, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)

private theorem cwSquareBasis_apply
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (a b : Fin (q + 2)) :
    cwSquareBasis K q s (a, b) = cwVec K q s a ⊗ₜ[K] cwVec K q s b := by
  letI : IsScalarTower K K (Fin (q + 2) → K) :=
    IsScalarTower.of_algebraMap_smul (by simp)
  fin_cases s <;>
    change (Module.Basis.tensorProduct (R := K) (S := K)
      (Pi.basisFun K (Fin (q + 2))) (Pi.basisFun K (Fin (q + 2)))) (a, b) = _ <;>
    rw [Module.Basis.tensorProduct_apply] <;>
    simp [cwVec, Pi.basisFun_apply]

private theorem interchange_tprod
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) =
      tprod K (fun i => v i ⊗ₜ[K] w i) := by
  show (interchange (tprod K v)) (tprod K w) = _
  rw [interchange]
  change (PiTensorProduct.lift interchangeOuter
      (PiTensorProduct.tprod K v)) (PiTensorProduct.tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  change (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

private theorem interchange_add_right
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (x : PiTensorProduct K V) (y z : PiTensorProduct K W) :
    interchange x (y + z) = interchange x y + interchange x z := by
  exact (interchange x).map_add y z

private theorem interchange_sum_right
    {K : Type u} [Field K] {d : ℕ} {ι : Type*} [Fintype ι]
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (x : PiTensorProduct K V) (f : ι → PiTensorProduct K W) :
    interchange x (∑ i, f i) = ∑ i, interchange x (f i) := by
  exact map_sum (interchange x) f Finset.univ

private theorem interchange_sum_left
    {K : Type u} [Field K] {d : ℕ} {ι : Type*} [Fintype ι]
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ι → PiTensorProduct K V) (y : PiTensorProduct K W) :
    interchange (∑ i, f i) y = ∑ i, interchange (f i) y := by
  have h :
      (interchange (∑ i, f i) :
        PiTensorProduct K W →ₗ[K]
          PiTensorProduct K (fun i => V i ⊗[K] W i)) =
        ∑ i, interchange (f i) :=
    map_sum interchange f Finset.univ
  simpa using congrArg (fun g => g y) h

private def cwO (q : ℕ) : Fin (q + 2) := ⟨0, by omega⟩
private def cwM (q : ℕ) (i : Fin q) : Fin (q + 2) := ⟨i.val + 1, by omega⟩
private def cwT (q : ℕ) : Fin (q + 2) := ⟨q + 1, by omega⟩

private def cwSupportedTriple (q : ℕ)
    (a b c : Fin (q + 2)) : Prop :=
  (∃ i : Fin q, a = cwO q ∧ b = cwM q i ∧ c = cwM q i) ∨
  (∃ i : Fin q, a = cwM q i ∧ b = cwO q ∧ c = cwM q i) ∨
  (∃ i : Fin q, a = cwM q i ∧ b = cwM q i ∧ c = cwO q) ∨
  (a = cwO q ∧ b = cwO q ∧ c = cwT q) ∨
  (a = cwO q ∧ b = cwT q ∧ c = cwO q) ∨
  (a = cwT q ∧ b = cwO q ∧ c = cwO q)

private theorem cwCoordGrade_O (q : ℕ) : cwCoordGrade q (cwO q) = 0 := by
  simp [cwCoordGrade, cwO]

private theorem cwCoordGrade_M (q : ℕ) (i : Fin q) :
    cwCoordGrade q (cwM q i) = 1 := by
  simp [cwCoordGrade, cwM]
  omega

private theorem cwCoordGrade_T (q : ℕ) : cwCoordGrade q (cwT q) = 2 := by
  simp [cwCoordGrade, cwT]

private theorem cwSupportedTriple_grade_sum_two
    (q : ℕ) (a b c : Fin (q + 2))
    (h : cwSupportedTriple q a b c) :
    (cwCoordGrade q a).val + (cwCoordGrade q b).val +
      (cwCoordGrade q c).val = 2 := by
  rcases h with
    ⟨i, rfl, rfl, rfl⟩ | ⟨i, rfl, rfl, rfl⟩ |
    ⟨i, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp [cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T]

private abbrev CWTerm (q : ℕ) := (Fin q × Fin 3) ⊕ Fin 3

private def cwTermTriple (q : ℕ) : CWTerm q → Fin 3 → Fin (q + 2)
  | Sum.inl (i, ⟨0, _⟩), ⟨0, _⟩ => cwO q
  | Sum.inl (i, ⟨0, _⟩), ⟨1, _⟩ => cwM q i
  | Sum.inl (i, ⟨0, _⟩), ⟨2, _⟩ => cwM q i
  | Sum.inl (i, ⟨1, _⟩), ⟨0, _⟩ => cwM q i
  | Sum.inl (i, ⟨1, _⟩), ⟨1, _⟩ => cwO q
  | Sum.inl (i, ⟨1, _⟩), ⟨2, _⟩ => cwM q i
  | Sum.inl (i, ⟨2, _⟩), ⟨0, _⟩ => cwM q i
  | Sum.inl (i, ⟨2, _⟩), ⟨1, _⟩ => cwM q i
  | Sum.inl (i, ⟨2, _⟩), ⟨2, _⟩ => cwO q
  | Sum.inr ⟨0, _⟩, ⟨0, _⟩ => cwO q
  | Sum.inr ⟨0, _⟩, ⟨1, _⟩ => cwO q
  | Sum.inr ⟨0, _⟩, ⟨2, _⟩ => cwT q
  | Sum.inr ⟨1, _⟩, ⟨0, _⟩ => cwO q
  | Sum.inr ⟨1, _⟩, ⟨1, _⟩ => cwT q
  | Sum.inr ⟨1, _⟩, ⟨2, _⟩ => cwO q
  | Sum.inr ⟨2, _⟩, ⟨0, _⟩ => cwT q
  | Sum.inr ⟨2, _⟩, ⟨1, _⟩ => cwO q
  | Sum.inr ⟨2, _⟩, ⟨2, _⟩ => cwO q

private noncomputable def cwTermMonom
    (K : Type u) [Field K] (q : ℕ) (t : CWTerm q) :
    PiTensorProduct K (CWSpace K q) :=
  CWMonom K q (cwTermTriple q t 0) (cwTermTriple q t 1) (cwTermTriple q t 2)

private theorem cwTerm_supported (q : ℕ) (t : CWTerm q) :
    cwSupportedTriple q
      (cwTermTriple q t 0) (cwTermTriple q t 1) (cwTermTriple q t 2) := by
  rcases t with ⟨i, r⟩ | r <;> fin_cases r <;>
    simp [cwTermTriple, cwSupportedTriple]

private theorem CWTensor_eq_sum_terms
    (K : Type u) [Field K] (q : ℕ) :
    CWTensor K q = ∑ t : CWTerm q, cwTermMonom K q t := by
  have hM (i : Fin q) :
      (⟨i.val + 1, by omega⟩ : Fin (q + 2)) =
        ⟨1 + i.val, by omega⟩ := by
    apply Fin.ext
    change i.val + 1 = 1 + i.val
    omega
  have hT :
      (⟨q + 1, by omega⟩ : Fin (q + 2)) =
        ⟨1 + q, by omega⟩ := by
    apply Fin.ext
    change q + 1 = 1 + q
    omega
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  unfold CWTensor cwTermMonom
  simp [cwTermTriple, Fin.sum_univ_succ, cwO, cwM, cwT,
    hM, hT]
  abel

private theorem cwSquareCanonical_blockTensor_eq_term_pairs
    (K : Type u) [Field K] (q : ℕ) (σ : Fin 3 → Fin 5) :
    (cwSquareCanonicalGrading K q).blockTensor σ =
      ∑ t : CWTerm q, ∑ u : CWTerm q,
        PiTensorProduct.map
          (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
          (interchange (cwTermMonom K q t) (cwTermMonom K q u)) := by
  change PiTensorProduct.map
      (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
      (interchange (CWTensor K q) (CWTensor K q)) = _
  rw [CWTensor_eq_sum_terms]
  let F := PiTensorProduct.map
    (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
  have hinter :
      interchange (∑ t : CWTerm q, cwTermMonom K q t)
          (∑ u : CWTerm q, cwTermMonom K q u) =
        ∑ t : CWTerm q, ∑ u : CWTerm q,
          interchange (cwTermMonom K q t) (cwTermMonom K q u) := by
    calc
      _ = ∑ t : CWTerm q,
          interchange (cwTermMonom K q t)
            (∑ u : CWTerm q, cwTermMonom K q u) :=
        interchange_sum_left (cwTermMonom K q)
          (∑ u : CWTerm q, cwTermMonom K q u)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t ht
        exact interchange_sum_right (cwTermMonom K q t) (cwTermMonom K q)
  change F
      (interchange (∑ t : CWTerm q, cwTermMonom K q t)
        (∑ u : CWTerm q, cwTermMonom K q u)) = _
  calc
    _ = F (∑ t : CWTerm q, ∑ u : CWTerm q,
          interchange (cwTermMonom K q t) (cwTermMonom K q u)) :=
      congrArg F hinter
    _ = _ := by
      calc
        _ = ∑ t : CWTerm q,
            F (∑ u : CWTerm q,
              interchange (cwTermMonom K q t) (cwTermMonom K q u)) :=
          map_sum F
            (fun t : CWTerm q => ∑ u : CWTerm q,
              interchange (cwTermMonom K q t) (cwTermMonom K q u)) Finset.univ
        _ = _ := by
          apply Finset.sum_congr rfl
          intro t ht
          exact map_sum F
            (fun u : CWTerm q =>
              interchange (cwTermMonom K q t) (cwTermMonom K q u)) Finset.univ


private theorem cwM_injective' (q : ℕ) : Function.Injective (cwM q) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [cwM] at hv
  omega

private theorem cwM_eq_cwM_iff (q : ℕ) (i j : Fin q) :
    cwM q i = cwM q j ↔ i = j :=
  (cwM_injective' q).eq_iff

private theorem cwO_ne_cwM (q : ℕ) (i : Fin q) : cwO q ≠ cwM q i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [cwO, cwM] at hv
  omega

private theorem cwT_ne_cwM (q : ℕ) (i : Fin q) : cwT q ≠ cwM q i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [cwT, cwM] at hv
  omega

private theorem cwO_ne_cwT (q : ℕ) : cwO q ≠ cwT q := by
  intro h
  have hv := congrArg Fin.val h
  simp only [cwO, cwT] at hv
  omega

private theorem cwM_ne_cwO (q : ℕ) (i : Fin q) : cwM q i ≠ cwO q :=
  (cwO_ne_cwM q i).symm

private theorem cwM_ne_cwT (q : ℕ) (i : Fin q) : cwM q i ≠ cwT q :=
  (cwT_ne_cwM q i).symm

private noncomputable def cwSquareTargetBasisMap
    (K : Type u) [Field K] (q : ℕ)
    (W : Fin 3 → Type u)
    [∀ s, AddCommGroup (W s)] [∀ s, Module K (W s)]
    (σ : Fin 3 → Fin 5)
    (output : ∀ s : Fin 3,
      Fin (q + 2) × Fin (q + 2) → W s)
    (s : Fin 3) :
    (cwSquareCanonicalGrading K q).classOf s (σ s) →ₗ[K] W s :=
  ((cwSquareBasis K q s).constr K (output s)).comp
    ((cwSquareCanonicalGrading K q).decomp s (σ s)).subtype

private theorem cwSquareTargetBasisMap_apply_blockProj_basis
    (K : Type u) [Field K] (q : ℕ)
    (W : Fin 3 → Type u)
    [∀ s, AddCommGroup (W s)] [∀ s, Module K (W s)]
    (σ : Fin 3 → Fin 5)
    (output : ∀ s : Fin 3,
      Fin (q + 2) × Fin (q + 2) → W s)
    (s : Fin 3) (idx : Fin (q + 2) × Fin (q + 2)) :
    cwSquareTargetBasisMap K q W σ output s
        ((cwSquareCanonicalGrading K q).blockProj s (σ s)
          (cwSquareBasis K q s idx)) =
      if cwPairGrade q idx = σ s then output s idx else 0 := by
  rw [cwSquareCanonical_blockProj_basis]
  split_ifs with hgrade
  · simp [cwSquareTargetBasisMap]
  · simp [cwSquareTargetBasisMap]

private theorem cwSquareTargetBasisMap_term_pair
    (K : Type u) [Field K] (q : ℕ)
    (W : Fin 3 → Type u)
    [∀ s, AddCommGroup (W s)] [∀ s, Module K (W s)]
    (σ : Fin 3 → Fin 5)
    (output : ∀ s : Fin 3,
      Fin (q + 2) × Fin (q + 2) → W s)
    (t u : CWTerm q) :
    PiTensorProduct.map (cwSquareTargetBasisMap K q W σ output)
        (PiTensorProduct.map
          (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
          (interchange (cwTermMonom K q t) (cwTermMonom K q u))) =
      tprod K (fun s =>
        if cwPairGrade q
            (cwTermTriple q t s, cwTermTriple q u s) = σ s then
          output s (cwTermTriple q t s, cwTermTriple q u s)
        else 0) := by
  let v₁ : ∀ s, CWSpace K q s :=
    fun s => match s with
      | ⟨0, _⟩ => (Pi.single (cwTermTriple q t 0) 1 : Fin (q + 2) → K)
      | ⟨1, _⟩ => (Pi.single (cwTermTriple q t 1) 1 : Fin (q + 2) → K)
      | ⟨2, _⟩ => (Pi.single (cwTermTriple q t 2) 1 : Fin (q + 2) → K)
  let v₂ : ∀ s, CWSpace K q s :=
    fun s => match s with
      | ⟨0, _⟩ => (Pi.single (cwTermTriple q u 0) 1 : Fin (q + 2) → K)
      | ⟨1, _⟩ => (Pi.single (cwTermTriple q u 1) 1 : Fin (q + 2) → K)
      | ⟨2, _⟩ => (Pi.single (cwTermTriple q u 2) 1 : Fin (q + 2) → K)
  change PiTensorProduct.map (cwSquareTargetBasisMap K q W σ output)
      (PiTensorProduct.map
        (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
        (interchange (tprod K v₁) (tprod K v₂))) = _
  have hinter := interchange_tprod (K := K) v₁ v₂
  refine (congrArg
    (fun z => PiTensorProduct.map (cwSquareTargetBasisMap K q W σ output)
      (PiTensorProduct.map
        (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s)) z)) hinter).trans ?_
  have hinner :
      PiTensorProduct.map
          (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
          (tprod K (fun i => v₁ i ⊗ₜ[K] v₂ i)) =
        tprod K (fun s =>
          (cwSquareCanonicalGrading K q).blockProj s (σ s)
            (v₁ s ⊗ₜ[K] v₂ s)) :=
    PiTensorProduct.map_tprod _ _
  calc
    _ = PiTensorProduct.map (cwSquareTargetBasisMap K q W σ output)
        (tprod K (fun s =>
          (cwSquareCanonicalGrading K q).blockProj s (σ s)
            (v₁ s ⊗ₜ[K] v₂ s))) := congrArg _ hinner
    _ = tprod K (fun s =>
        cwSquareTargetBasisMap K q W σ output s
          ((cwSquareCanonicalGrading K q).blockProj s (σ s)
            (v₁ s ⊗ₜ[K] v₂ s))) :=
      PiTensorProduct.map_tprod _ _
    _ = _ := by
      congr 1
      funext s
      have hv₁ : v₁ s = cwVec K q s (cwTermTriple q t s) := by
        fin_cases s <;> rfl
      have hv₂ : v₂ s = cwVec K q s (cwTermTriple q u s) := by
        fin_cases s <;> rfl
      rw [hv₁, hv₂]
      have hbasis := (cwSquareBasis_apply K q s
        (cwTermTriple q t s) (cwTermTriple q u s)).symm
      refine (congrArg
        (fun z => cwSquareTargetBasisMap K q W σ output s
          ((cwSquareCanonicalGrading K q).blockProj s (σ s) z)) hbasis).trans ?_
      exact cwSquareTargetBasisMap_apply_blockProj_basis
        K q W σ output s _

private noncomputable def cwCoupledVec
    (K : Type u) [Field K] (q : ℕ)
    (x y : Fin q ⊕ Fin q) (z : Fin 2 ⊕ (Fin q × Fin q)) :
    ∀ s : Fin 3, CoupledSpace K q s
  | ⟨0, _⟩ => (Pi.single x 1 : (Fin q ⊕ Fin q) → K)
  | ⟨1, _⟩ => (Pi.single y 1 : (Fin q ⊕ Fin q) → K)
  | ⟨2, _⟩ => (Pi.single z 1 : (Fin 2 ⊕ (Fin q × Fin q)) → K)

private noncomputable def cwCoupledMonom
    (K : Type u) [Field K] (q : ℕ)
    (x y : Fin q ⊕ Fin q) (z : Fin 2 ⊕ (Fin q × Fin q)) :
    PiTensorProduct K (CoupledSpace K q) :=
  tprod K (cwCoupledVec K q x y z)


private theorem coupledTensor_eq_cwCoupledMonom_sums
    (K : Type u) [Field K] (q : ℕ) :
    coupledTensor K q =
      (∑ i : Fin q,
        cwCoupledMonom K q (Sum.inl i) (Sum.inl i) (Sum.inl 0)) +
      (∑ k : Fin q,
        cwCoupledMonom K q (Sum.inr k) (Sum.inr k) (Sum.inl 1)) +
      (∑ i : Fin q, ∑ k : Fin q,
        cwCoupledMonom K q (Sum.inl i) (Sum.inr k) (Sum.inr (i, k))) +
      (∑ i : Fin q, ∑ k : Fin q,
        cwCoupledMonom K q (Sum.inr k) (Sum.inl i) (Sum.inr (i, k))) := by
  rfl


private noncomputable def cwCoupled211Vec
    (K : Type u) [Field K] (q : ℕ)
    (x y : Fin q ⊕ Fin q) (z : Fin 2 ⊕ (Fin q × Fin q)) :
    ∀ s : Fin 3, (TensorObj.permObj cyclicPerm (coupledObj K q)).V s
  | ⟨0, _⟩ => (Pi.single z 1 : (Fin 2 ⊕ (Fin q × Fin q)) → K)
  | ⟨1, _⟩ => (Pi.single x 1 : (Fin q ⊕ Fin q) → K)
  | ⟨2, _⟩ => (Pi.single y 1 : (Fin q ⊕ Fin q) → K)

private noncomputable def cwCoupled211Monom
    (K : Type u) [Field K] (q : ℕ)
    (x y : Fin q ⊕ Fin q) (z : Fin 2 ⊕ (Fin q × Fin q)) :
    PiTensorProduct K (TensorObj.permObj cyclicPerm (coupledObj K q)).V :=
  tprod K (cwCoupled211Vec K q x y z)

private theorem reindex_cwCoupledMonom_cyclic
    (K : Type u) [Field K] (q : ℕ)
    (x y : Fin q ⊕ Fin q) (z : Fin 2 ⊕ (Fin q × Fin q)) :
    (PiTensorProduct.reindex K (CoupledSpace K q) cyclicPerm)
        (cwCoupledMonom K q x y z) = cwCoupled211Monom K q x y z := by
  unfold cwCoupledMonom cwCoupled211Monom
  rw [PiTensorProduct.reindex_tprod]
  congr 1
  funext s
  fin_cases s <;> rfl

private theorem permCoupled211Tensor_eq_cwCoupledMonom_sums
    (K : Type u) [Field K] (q : ℕ) :
    (TensorObj.permObj cyclicPerm (coupledObj K q)).t =
      (∑ i : Fin q,
        cwCoupled211Monom K q (Sum.inl i) (Sum.inl i) (Sum.inl 0)) +
      (∑ k : Fin q,
        cwCoupled211Monom K q (Sum.inr k) (Sum.inr k) (Sum.inl 1)) +
      (∑ i : Fin q, ∑ k : Fin q,
        cwCoupled211Monom K q (Sum.inl i) (Sum.inr k) (Sum.inr (i, k))) +
      (∑ i : Fin q, ∑ k : Fin q,
        cwCoupled211Monom K q (Sum.inr k) (Sum.inl i) (Sum.inr (i, k))) := by
  change (PiTensorProduct.reindex K (CoupledSpace K q) cyclicPerm)
      (coupledTensor K q) = _
  rw [coupledTensor_eq_cwCoupledMonom_sums]
  simp only [map_add, map_sum, reindex_cwCoupledMonom_cyclic]
  rfl

private noncomputable def cwCoupled211BasisOut
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (ab : Fin (q + 2) × Fin (q + 2)) :
    (TensorObj.permObj cyclicPerm (coupledObj K q)).V s :=
  match s with
  | ⟨0, _⟩ =>
      (if ab = (cwT q, cwO q) then
        (Pi.single (Sum.inl (0 : Fin 2)) 1 :
          (Fin 2 ⊕ (Fin q × Fin q)) → K)
      else 0) +
      (if ab = (cwO q, cwT q) then
        (Pi.single (Sum.inl (1 : Fin 2)) 1 :
          (Fin 2 ⊕ (Fin q × Fin q)) → K)
      else 0) +
      (∑ i : Fin q, ∑ j : Fin q,
        if ab = (cwM q i, cwM q j) then
          (Pi.single (Sum.inr (j, i)) 1 :
            (Fin 2 ⊕ (Fin q × Fin q)) → K)
        else 0)
  | ⟨1, _⟩ =>
      (∑ i : Fin q,
        if ab = (cwO q, cwM q i) then
          (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
        else 0) +
      (∑ i : Fin q,
        if ab = (cwM q i, cwO q) then
          (Pi.single (Sum.inr i) 1 : (Fin q ⊕ Fin q) → K)
        else 0)
  | ⟨2, _⟩ =>
      (∑ i : Fin q,
        if ab = (cwO q, cwM q i) then
          (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
        else 0) +
      (∑ i : Fin q,
        if ab = (cwM q i, cwO q) then
          (Pi.single (Sum.inr i) 1 : (Fin q ⊕ Fin q) → K)
        else 0)

private noncomputable def cwCoupled211ExpectedTermPair
    (K : Type u) [Field K] (q : ℕ) :
    CWTerm q → CWTerm q →
      PiTensorProduct K (TensorObj.permObj cyclicPerm (coupledObj K q)).V
  | Sum.inr ⟨2, _⟩, Sum.inl (i, ⟨0, _⟩) =>
      cwCoupled211Monom K q (Sum.inl i) (Sum.inl i) (Sum.inl 0)
  | Sum.inl (i, ⟨0, _⟩), Sum.inr ⟨2, _⟩ =>
      cwCoupled211Monom K q (Sum.inr i) (Sum.inr i) (Sum.inl 1)
  | Sum.inl (i, ⟨1, _⟩), Sum.inl (k, ⟨2, _⟩) =>
      cwCoupled211Monom K q (Sum.inl k) (Sum.inr i) (Sum.inr (k, i))
  | Sum.inl (k, ⟨2, _⟩), Sum.inl (i, ⟨1, _⟩) =>
      cwCoupled211Monom K q (Sum.inr k) (Sum.inl i) (Sum.inr (i, k))
  | _, _ => 0

private theorem cwCoupled211_special_or_grade_mismatch
    (q : ℕ) (t u : CWTerm q) :
    (∃ i : Fin q,
      t = Sum.inr (2 : Fin 3) ∧ u = Sum.inl (i, (0 : Fin 3))) ∨
    (∃ i : Fin q,
      t = Sum.inl (i, (0 : Fin 3)) ∧ u = Sum.inr (2 : Fin 3)) ∨
    (∃ i k : Fin q,
      t = Sum.inl (i, (1 : Fin 3)) ∧ u = Sum.inl (k, (2 : Fin 3))) ∨
    (∃ k i : Fin q,
      t = Sum.inl (k, (2 : Fin 3)) ∧ u = Sum.inl (i, (1 : Fin 3))) ∨
    cwPairGrade q (cwTermTriple q t 0, cwTermTriple q u 0) ≠ 2 ∨
    cwPairGrade q (cwTermTriple q t 1, cwTermTriple q u 1) ≠ 1 ∨
    cwPairGrade q (cwTermTriple q t 2, cwTermTriple q u 2) ≠ 1 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [cwTermTriple, cwPairGrade, cwCoordGrade_O,
      cwCoordGrade_M, cwCoordGrade_T]

private theorem cwCoupled211ExpectedTermPair_eq_zero_of_grade_mismatch
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) (s : Fin 3)
    (hgrade : cwPairGrade q
      (cwTermTriple q t s, cwTermTriple q u s) ≠
        cwSquareBlockType 2 1 1 s) :
    cwCoupled211ExpectedTermPair K q t u = 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;> fin_cases s <;>
    simp [cwTermTriple, cwCoupled211ExpectedTermPair, cwPairGrade,
      cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
      cwSquareBlockType] at hgrade ⊢

private theorem sum_ite_pair_eq
    {q : ℕ} {A : Type*} [AddCommMonoid A]
    (i k : Fin q) (f : Fin q → Fin q → A) :
    (∑ x : Fin q, ∑ y : Fin q,
      if i = x ∧ k = y then f x y else 0) = f i k := by
  classical
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro y _ hy
      rw [if_neg]
      intro h
      exact hy h.2.symm
    · simp
  · intro x _ hx
    apply Finset.sum_eq_zero
    intro y _
    rw [if_neg]
    intro h
    exact hx h.1.symm
  · simp

private theorem cwCoupled211_filtered_term_pair_classification
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) :
    tprod K (fun s =>
      if cwPairGrade q (cwTermTriple q t s, cwTermTriple q u s) =
          cwSquareBlockType 2 1 1 s then
        cwCoupled211BasisOut K q s
          (cwTermTriple q t s, cwTermTriple q u s)
      else 0) = cwCoupled211ExpectedTermPair K q t u := by
  rcases cwCoupled211_special_or_grade_mismatch q t u with
    ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ |
    ⟨i, k, rfl, rfl⟩ | ⟨k, i, rfl, rfl⟩ | h0 | h1 | h2
  · simp only [cwCoupled211ExpectedTermPair, cwCoupled211Monom]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwTermTriple, cwCoupled211BasisOut, cwCoupled211Vec,
        cwPairGrade, cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
        cwSquareBlockType, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT]
    all_goals
      first
        | rfl
        | exact Fintype.sum_ite_eq _ _
  · simp only [cwCoupled211ExpectedTermPair, cwCoupled211Monom]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwTermTriple, cwCoupled211BasisOut, cwCoupled211Vec,
        cwPairGrade, cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
        cwSquareBlockType, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT]
    all_goals
      first
        | rfl
        | exact Fintype.sum_ite_eq _ _
  · simp only [cwCoupled211ExpectedTermPair, cwCoupled211Monom]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwTermTriple, cwCoupled211BasisOut, cwCoupled211Vec,
        cwPairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwSquareBlockType, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT, eq_comm,
        sum_ite_pair_eq]
    all_goals
      first
        | rfl
        | exact Fintype.sum_ite_eq _ _
  · simp only [cwCoupled211ExpectedTermPair, cwCoupled211Monom]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwTermTriple, cwCoupled211BasisOut, cwCoupled211Vec,
        cwPairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwSquareBlockType, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT, eq_comm,
        sum_ite_pair_eq]
    all_goals
      first
        | rfl
        | exact Fintype.sum_ite_eq _ _
  · rw [cwCoupled211ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 0 (by simpa [cwSquareBlockType] using h0)]
    apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
    simp [h0, cwSquareBlockType]
  · rw [cwCoupled211ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 1 (by simpa [cwSquareBlockType] using h1)]
    apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
    simp [h1, cwSquareBlockType]
  · rw [cwCoupled211ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 2 (by simpa [cwSquareBlockType] using h2)]
    apply (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
    simp [h2, cwSquareBlockType]

private theorem cwCoupled211_cross_swapped
    (K : Type u) [Field K] (q : ℕ) :
    (∑ i : Fin q, ∑ k : Fin q,
      cwCoupled211Monom K q (Sum.inl k) (Sum.inr i) (Sum.inr (k, i))) =
    (∑ i : Fin q, ∑ k : Fin q,
      cwCoupled211Monom K q (Sum.inl i) (Sum.inr k) (Sum.inr (i, k))) := by
  rw [Finset.sum_comm]

private theorem cwCoupled211_fourth_swapped
    (K : Type u) [Field K] (q : ℕ) :
    (∑ k : Fin q, ∑ i : Fin q,
      cwCoupled211Monom K q (Sum.inr k) (Sum.inl i) (Sum.inr (i, k))) =
    (∑ i : Fin q, ∑ k : Fin q,
      cwCoupled211Monom K q (Sum.inr k) (Sum.inl i) (Sum.inr (i, k))) := by
  rw [Finset.sum_comm]

private theorem cwCoupled211_all_filtered_term_pairs_eq_permTensor
    (K : Type u) [Field K] (q : ℕ) :
    (∑ t : CWTerm q, ∑ u : CWTerm q,
      tprod K (fun s =>
        if cwPairGrade q (cwTermTriple q t s, cwTermTriple q u s) =
            cwSquareBlockType 2 1 1 s then
          cwCoupled211BasisOut K q s
            (cwTermTriple q t s, cwTermTriple q u s)
        else 0)) = (TensorObj.permObj cyclicPerm (coupledObj K q)).t := by
  calc
    _ = ∑ t : CWTerm q, ∑ u : CWTerm q,
        cwCoupled211ExpectedTermPair K q t u := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro u hu
      exact cwCoupled211_filtered_term_pair_classification K q t u
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp_rw [Fintype.sum_sum_type]
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      simp [cwCoupled211ExpectedTermPair, Fin.sum_univ_succ]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_add_distrib]
      show ((∑ x : Fin q,
                cwCoupled211Monom K q (Sum.inr x) (Sum.inr x) (Sum.inl 1)) +
              ((∑ x : Fin q, ∑ y : Fin q,
                  cwCoupled211Monom K q (Sum.inl y) (Sum.inr x)
                    (Sum.inr (y, x))) +
                (∑ x : Fin q, ∑ y : Fin q,
                  cwCoupled211Monom K q (Sum.inr x) (Sum.inl y)
                    (Sum.inr (y, x)))) +
              (∑ x : Fin q,
                cwCoupled211Monom K q (Sum.inl x) (Sum.inl x) (Sum.inl 0))) = _
      rw [cwCoupled211_cross_swapped K q]
      rw [cwCoupled211_fourth_swapped K q]
      change _ = (PiTensorProduct.reindex K (CoupledSpace K q) cyclicPerm)
        (coupledTensor K q)
      rw [show (PiTensorProduct.reindex K (CoupledSpace K q) cyclicPerm)
        (coupledTensor K q) = _ from
          permCoupled211Tensor_eq_cwCoupledMonom_sums K q]
      ac_rfl


open MME.DWZComponentRestriction

private theorem dwzQ6GradeOneCoord_source
    (p : LiftedCoarsePair.{u} 6 1) :
    p.down.1 =
      match dwzQ6GradeOneCoord p with
      | Sum.inl i => (cwO 6, cwM 6 i)
      | Sum.inr i => (cwM 6 i, cwO 6) := by
  rcases p with ⟨⟨⟨a, b⟩, hp⟩⟩
  change (a, b) =
    match (if a.val = 0 then
      Sum.inl (Fin.ofNat 6 (b.val - 1))
    else
      Sum.inr (Fin.ofNat 6 (a.val - 1))) with
    | Sum.inl i => (cwO 6, cwM 6 i)
    | Sum.inr i => (cwM 6 i, cwO 6)
  fin_cases a <;> fin_cases b <;>
    simp [cwSquarePairGrade, cwSquareCoordGrade, cwO, cwM] at hp ⊢

private theorem canonicalComponentZBasis14_blockProj
    (K : Type u) [Field K] (p : LiftedCoarsePair.{u} 6 1) :
    canonicalComponentZBasis K (14 : Fin 15) p =
      (cwSquareCanonicalGrading K 6).blockProj 2 1
        (cwSquareBasis K 6 2 p.down.1) := by
  apply Subtype.ext
  rw [TensorObj.TypeGrading.blockProj_apply_mem]
  · have hr :
        canonicalComponentZBasis K (14 : Fin 15) p =
          coarseClassBasis (K := K) 6 2 1 p.down := by
      exact Module.Basis.reindex_apply
        (coarseClassBasis (K := K) 6 2 1) Equiv.ulift.symm p
    rw [hr]
    exact mme_dwz_coarseClassBasis_q6_val K 2 1 p.down
  · exact Submodule.subset_span ⟨p.down.1, p.down.2, rfl⟩

theorem standalone_row211
    (K : Type u) [Field K] :
    ∃ maps : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K 6).classOf s
            (cwSquareBlockType 2 1 1 s) →ₗ[K]
          (TensorObj.permObj cyclicPerm (coupledObj K 6)).V s,
      PiTensorProduct.map maps
          ((cwSquareCanonicalGrading K 6).blockTensor
            (cwSquareBlockType 2 1 1)) =
        (TensorObj.permObj cyclicPerm (coupledObj K 6)).t ∧
      ∀ p,
        maps 2 (canonicalComponentZBasis K (14 : Fin 15) p) =
          (Pi.single (dwzQ6GradeOneCoord p) 1 :
            (Fin 6 ⊕ Fin 6) → K) := by
  let maps := cwSquareTargetBasisMap K 6
    (TensorObj.permObj cyclicPerm (coupledObj K 6)).V
    (cwSquareBlockType 2 1 1) (cwCoupled211BasisOut K 6)
  refine ⟨maps, ?_, ?_⟩
  · change PiTensorProduct.map maps
        ((cwSquareCanonicalGrading K 6).blockTensor
          (cwSquareBlockType 2 1 1)) =
      (TensorObj.permObj cyclicPerm (coupledObj K 6)).t
    rw [cwSquareCanonical_blockTensor_eq_term_pairs]
    dsimp only [maps]
    simp only [map_sum, cwSquareTargetBasisMap_term_pair]
    exact cwCoupled211_all_filtered_term_pairs_eq_permTensor K 6
  · intro p
    have hz := canonicalComponentZBasis14_blockProj K p
    rw [hz]
    dsimp only [maps]
    change cwSquareTargetBasisMap K 6
        (TensorObj.permObj cyclicPerm (coupledObj K 6)).V
        (cwSquareBlockType 2 1 1) (cwCoupled211BasisOut K 6) 2
          ((cwSquareCanonicalGrading K 6).blockProj 2
            (cwSquareBlockType 2 1 1 2)
            (cwSquareBasis K 6 2 p.down.1)) = _
    rw [cwSquareTargetBasisMap_apply_blockProj_basis]
    have hgrade : cwPairGrade 6 p.down.1 = 1 := by
      have hval := congrArg Fin.val p.down.2
      simpa [cwPairGrade, cwSquarePairGrade, cwCoordGrade,
        cwSquareCoordGrade, DWZSquare.shapeZ] using hval
    rw [if_pos (show cwPairGrade 6 p.down.1 =
      cwSquareBlockType 2 1 1 2 by exact hgrade)]
    have hp := dwzQ6GradeOneCoord_source p
    generalize hc : dwzQ6GradeOneCoord p = c at hp ⊢
    rcases c with i | i
    · rw [hp]
      simp [cwCoupled211BasisOut, cwM_eq_cwM_iff,
        cwO_ne_cwM]
      all_goals
        first
          | rfl
          | exact Fintype.sum_ite_eq _ _
    · rw [hp]
      simp [cwCoupled211BasisOut, cwM_eq_cwM_iff,
        cwO_ne_cwM]
      all_goals
        first
          | rfl
          | exact Fintype.sum_ite_eq _ _

end CWSquareCanonical
end MME

open MME PiTensorProduct
open MME.DWZComponentRestriction

universe u

theorem solution
    (K : Type u) [Field K] :
    ∃ maps : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K 6).classOf s
            (cwSquareBlockType 2 1 1 s) →ₗ[K]
          (TensorObj.permObj cyclicPerm (coupledObj K 6)).V s,
      PiTensorProduct.map maps
          ((cwSquareCanonicalGrading K 6).blockTensor
            (cwSquareBlockType 2 1 1)) =
        (TensorObj.permObj cyclicPerm (coupledObj K 6)).t ∧
      ∀ p,
        maps 2 (canonicalComponentZBasis K (14 : Fin 15) p) =
          (Pi.single (dwzQ6GradeOneCoord p) 1 :
            (Fin 6 ⊕ Fin 6) → K) :=
  MME.standalone_row211 K
