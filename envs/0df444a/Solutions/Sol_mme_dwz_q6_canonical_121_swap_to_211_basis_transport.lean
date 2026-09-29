-- Prove2me | solution 1 for mme_dwz_q6_canonical_121_swap_to_211_basis_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T12:14:04.612137+00:00
-- url     : https://prove2.me/submissions/8de25560-25ea-43e1-9b8e-3132977e0a81

import Mathlib.Tactic
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_TypeGrading_kron
import Theorems.Thm_mme_dwz_coarseClassBasis_q6_val
import Theorems.Thm_mme_kronPowModeMap_recursive_basis

open MME MME.TensorObj MME.DWZComponentRestriction
  PiTensorProduct TensorProduct Module BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace MME

private theorem piMap_map_apply_fin3
    {K : Type u} [Field K]
    {V W U : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
    (f : ∀ i, V i →ₗ[K] W i) (g : ∀ i, W i →ₗ[K] U i)
    (x : PiTensorProduct K V) :
    PiTensorProduct.map g (PiTensorProduct.map f x) =
      PiTensorProduct.map (fun i ↦ (g i).comp (f i)) x := by
  exact (LinearMap.congr_fun
    (PiTensorProduct.map_comp (f := f) (g := g)) x).symm

private noncomputable def cwSwapToBaseLocal
    (K : Type u) [Field K] (q : ℕ) :
    ∀ i : Fin 3,
      CWSpace K q (swapFirstTwoPerm.symm i) →ₗ[K] CWSpace K q i :=
  fun ⟨i, hi⟩ ↦ by
    match i, hi with
    | 0, _ =>
        change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K)
        exact LinearMap.id
    | 1, _ =>
        change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K)
        exact LinearMap.id
    | 2, _ =>
        change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K)
        exact LinearMap.id
    | i + 3, h => exact absurd h (by omega)

private theorem cwSwapToBaseLocal_monom
    (K : Type u) [Field K] (q : ℕ) (a b c : Fin (q + 2)) :
    PiTensorProduct.map (cwSwapToBaseLocal K q)
      ((PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm)
        (CWMonom K q a b c)) = CWMonom K q b a c := by
  unfold CWMonom
  rw [PiTensorProduct.reindex_tprod, PiTensorProduct.map_tprod]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem cwSwapToBaseLocal_tensor
    (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (cwSwapToBaseLocal K q)
      ((PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm)
        (CWTensor K q)) = CWTensor K q := by
  unfold CWTensor
  simp only [map_add, map_sum, cwSwapToBaseLocal_monom]
  let O : Fin (q + 2) := ⟨0, by omega⟩
  have hsum :
      (∑ i : Fin q,
        let M : Fin (q + 2) := ⟨i.val + 1, by omega⟩
        CWMonom K q M O M + CWMonom K q O M M +
          CWMonom K q M M O) =
      ∑ i : Fin q,
        let M : Fin (q + 2) := ⟨i.val + 1, by omega⟩
        CWMonom K q O M M + CWMonom K q M O M +
          CWMonom K q M M O := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp
    abel
  rw [hsum]
  abel

private noncomputable def cwSquareSwapToBaseLocal
    (K : Type u) [Field K] (q : ℕ) : ∀ i : Fin 3,
    ((TensorObj.kron (CWObj K q) (CWObj K q)).V
      (swapFirstTwoPerm.symm i)) →ₗ[K]
    ((TensorObj.kron (CWObj K q) (CWObj K q)).V i) :=
  fun i ↦ TensorProduct.map
    (cwSwapToBaseLocal K q i) (cwSwapToBaseLocal K q i)

private theorem cwSquareSwapToBaseLocal_tensor
    (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (cwSquareSwapToBaseLocal K q)
      ((PiTensorProduct.reindex K
        (TensorObj.kron (CWObj K q) (CWObj K q)).V
        swapFirstTwoPerm)
        (TensorObj.kron (CWObj K q) (CWObj K q)).t) =
      (TensorObj.kron (CWObj K q) (CWObj K q)).t := by
  change PiTensorProduct.map (cwSquareSwapToBaseLocal K q)
      ((PiTensorProduct.reindex K
        (fun i ↦ CWSpace K q i ⊗[K] CWSpace K q i)
        swapFirstTwoPerm)
        (interchange (CWTensor K q) (CWTensor K q))) =
      interchange (CWTensor K q) (CWTensor K q)
  rw [reindex_interchange]
  change PiTensorProduct.map
      (fun i ↦ TensorProduct.map
        (cwSwapToBaseLocal K q i) (cwSwapToBaseLocal K q i))
      (interchange
        ((PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm)
          (CWTensor K q))
        ((PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm)
          (CWTensor K q))) = _
  rw [TensorObj.TypeGrading.kronMap_interchange,
    cwSwapToBaseLocal_tensor]

private theorem cwSquareSwapToBaseLocal_basis
    (K : Type u) [Field K] (q : ℕ) (i : Fin 3)
    (p : Fin (q + 2) × Fin (q + 2)) :
    cwSquareSwapToBaseLocal K q i
        (cwSquareCanonicalBasis K q (swapFirstTwoPerm.symm i) p) =
      cwSquareCanonicalBasis K q i p := by
  rcases p with ⟨a, b⟩
  fin_cases i <;>
    simp [swapFirstTwoPerm, cwSquareSwapToBaseLocal,
      cwSwapToBaseLocal, cwSquareCanonicalBasis] <;>
    exact LinearMap.congr_fun
      (TensorProduct.map_id (R := K)
        (M := Fin (q + 2) → K) (N := Fin (q + 2) → K)) _

private theorem cwSquareSwapToBaseLocal_mem_grade
    (K : Type u) [Field K] (q : ℕ) (i : Fin 3) (a : Fin 5)
    (x : (TensorObj.kron (CWObj K q) (CWObj K q)).V
      (swapFirstTwoPerm.symm i))
    (hx : x ∈ (cwSquareCanonicalGrading K q).classOf
      (swapFirstTwoPerm.symm i) a) :
    cwSquareSwapToBaseLocal K q i x ∈
      (cwSquareCanonicalGrading K q).classOf i a := by
  change x ∈ cwBasisGrade
      (cwSquareCanonicalBasis K q (swapFirstTwoPerm.symm i))
      (cwSquarePairGrade q) a at hx
  change cwSquareSwapToBaseLocal K q i x ∈ cwBasisGrade
      (cwSquareCanonicalBasis K q i) (cwSquarePairGrade q) a
  unfold cwBasisGrade at hx ⊢
  refine Submodule.span_induction
    (p := fun y _ ↦ cwSquareSwapToBaseLocal K q i y ∈
      Submodule.span K
        (cwSquareCanonicalBasis K q i ''
          {p | cwSquarePairGrade q p = a}))
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    rw [cwSquareSwapToBaseLocal_basis]
    exact Submodule.subset_span ⟨p, hp, rfl⟩
  · simp
  · intro y z hy hz hy' hz'
    simpa using Submodule.add_mem _ hy' hz'
  · intro c y hy hy'
    simpa using Submodule.smul_mem _ c hy'

private noncomputable def row121SwapTo211BaseMap
    (K : Type u) [Field K] : ∀ i : Fin 3,
    (cwSquareCanonicalGrading K 6).classOf
        (swapFirstTwoPerm.symm i)
        (cwSquareBlockType 1 2 1 (swapFirstTwoPerm.symm i)) →ₗ[K]
    (cwSquareCanonicalGrading K 6).classOf i
        (cwSquareBlockType 2 1 1 i) := fun i ↦
  LinearMap.codRestrict _
    ((cwSquareSwapToBaseLocal K 6 i).comp
      ((cwSquareCanonicalGrading K 6).classOf
        (swapFirstTwoPerm.symm i)
        (cwSquareBlockType 1 2 1 (swapFirstTwoPerm.symm i))).subtype)
    (fun x ↦ by
      change cwSquareSwapToBaseLocal K 6 i x.1 ∈
        (cwSquareCanonicalGrading K 6).classOf i
          (cwSquareBlockType 2 1 1 i)
      have hx := x.2
      change x.1 ∈ (cwSquareCanonicalGrading K 6).classOf
          (swapFirstTwoPerm.symm i)
          (cwSquareBlockType 1 2 1 (swapFirstTwoPerm.symm i)) at hx
      have h := cwSquareSwapToBaseLocal_mem_grade K 6 i
        (cwSquareBlockType 1 2 1 (swapFirstTwoPerm.symm i)) x.1 hx
      have hgrade :
          cwSquareBlockType 1 2 1 (swapFirstTwoPerm.symm i) =
            cwSquareBlockType 2 1 1 i := by
        fin_cases i <;> rfl
      have hsub := congrArg
        (fun a ↦ (cwSquareCanonicalGrading K 6).classOf i a) hgrade
      exact Eq.mp (congrArg
        (fun P : Submodule K
          ((TensorObj.kron (CWObj K 6) (CWObj K 6)).V i) ↦
            cwSquareSwapToBaseLocal K 6 i x.1 ∈ P) hsub) h)

private theorem row121SwapTo211BaseMap_blockProj
    (K : Type u) [Field K] (i : Fin 3) :
    (row121SwapTo211BaseMap K i).comp
        ((cwSquareCanonicalGrading K 6).blockProj
          (swapFirstTwoPerm.symm i)
          (cwSquareBlockType 1 2 1 (swapFirstTwoPerm.symm i))) =
      ((cwSquareCanonicalGrading K 6).blockProj i
        (cwSquareBlockType 2 1 1 i)).comp
        (cwSquareSwapToBaseLocal K 6 i) := by
  let b := cwSquareCanonicalBasis K 6 (swapFirstTwoPerm.symm i)
  refine b.ext ?_
  intro p
  change row121SwapTo211BaseMap K i
        ((cwSquareCanonicalGrading K 6).blockProj
          (swapFirstTwoPerm.symm i)
          (cwSquareBlockType 1 2 1 (swapFirstTwoPerm.symm i)) (b p)) =
      (cwSquareCanonicalGrading K 6).blockProj i
        (cwSquareBlockType 2 1 1 i)
        (cwSquareSwapToBaseLocal K 6 i (b p))
  by_cases hp : cwSquarePairGrade 6 p =
      cwSquareBlockType 1 2 1 (swapFirstTwoPerm.symm i)
  · have hs : b p ∈ (cwSquareCanonicalGrading K 6).classOf
        (swapFirstTwoPerm.symm i)
        (cwSquareBlockType 1 2 1 (swapFirstTwoPerm.symm i)) :=
      Submodule.subset_span ⟨p, hp, rfl⟩
    have ht0 := cwSquareSwapToBaseLocal_mem_grade K 6 i
      (cwSquareBlockType 1 2 1 (swapFirstTwoPerm.symm i)) (b p) hs
    have hgrade :
        cwSquareBlockType 1 2 1 (swapFirstTwoPerm.symm i) =
          cwSquareBlockType 2 1 1 i := by
      fin_cases i <;> rfl
    have ht : cwSquareSwapToBaseLocal K 6 i (b p) ∈
        (cwSquareCanonicalGrading K 6).classOf i
          (cwSquareBlockType 2 1 1 i) := by
      rw [← hgrade]
      exact ht0
    rw [TensorObj.TypeGrading.blockProj_apply_mem _ _ _ _ hs,
      TensorObj.TypeGrading.blockProj_apply_mem _ _ _ _ ht]
    apply Subtype.ext
    rfl
  · have hpt : cwSquarePairGrade 6 p ≠
        cwSquareBlockType 2 1 1 i := by
      intro h
      apply hp
      fin_cases i <;> exact h
    have hs : b p ∈ (cwSquareCanonicalGrading K 6).classOf
        (swapFirstTwoPerm.symm i) (cwSquarePairGrade 6 p) :=
      Submodule.subset_span ⟨p, rfl, rfl⟩
    have ht : cwSquareSwapToBaseLocal K 6 i (b p) ∈
        (cwSquareCanonicalGrading K 6).classOf i
          (cwSquarePairGrade 6 p) :=
      cwSquareSwapToBaseLocal_mem_grade K 6 i
        (cwSquarePairGrade 6 p) (b p) hs
    rw [TensorObj.TypeGrading.blockProj_apply_mem_ne _ _ _ _
        (Ne.symm hp) _ hs,
      TensorObj.TypeGrading.blockProj_apply_mem_ne _ _ _ _
        (Ne.symm hpt) _ ht]
    exact map_zero _

theorem row121SwapTo211BaseMap_tensor
    (K : Type u) [Field K] :
    PiTensorProduct.map (row121SwapTo211BaseMap K)
        (TensorObj.permObj swapFirstTwoPerm
          (canonicalComponentBlock K (13 : Fin 15))).t =
      (canonicalComponentBlock K (14 : Fin 15)).t := by
  change PiTensorProduct.map (row121SwapTo211BaseMap K)
      ((PiTensorProduct.reindex K
        (fun i ↦ (cwSquareCanonicalGrading K 6).classOf i
          (cwSquareBlockType 1 2 1 i)) swapFirstTwoPerm)
        ((cwSquareCanonicalGrading K 6).blockTensor
          (cwSquareBlockType 1 2 1))) =
      (cwSquareCanonicalGrading K 6).blockTensor
        (cwSquareBlockType 2 1 1)
  unfold TensorObj.TypeGrading.blockTensor
  rw [← PiTensorProduct.map_reindex
    (f := fun i ↦ (cwSquareCanonicalGrading K 6).blockProj i
      (cwSquareBlockType 1 2 1 i)) swapFirstTwoPerm]
  have hcomp :
      (fun i ↦ (row121SwapTo211BaseMap K i).comp
        ((cwSquareCanonicalGrading K 6).blockProj
          (swapFirstTwoPerm.symm i)
          (cwSquareBlockType 1 2 1 (swapFirstTwoPerm.symm i)))) =
      (fun i ↦ ((cwSquareCanonicalGrading K 6).blockProj i
        (cwSquareBlockType 2 1 1 i)).comp
          (cwSquareSwapToBaseLocal K 6 i)) := by
    funext i
    exact row121SwapTo211BaseMap_blockProj K i
  rw [piMap_map_apply_fin3]
  rw [hcomp]
  rw [← piMap_map_apply_fin3]
  rw [cwSquareSwapToBaseLocal_tensor]

private theorem canonicalComponentZBasis13_val
    (K : Type u) [Field K] (p : LiftedCoarsePair.{u} 6 1) :
    (canonicalComponentZBasis K (13 : Fin 15) p).1 =
      cwSquareCanonicalBasis K 6 2 p.down.1 := by
  rw [show canonicalComponentZBasis K (13 : Fin 15) p =
    coarseClassBasis (K := K) 6 2 1 p.down by
      exact Module.Basis.reindex_apply
        (coarseClassBasis (K := K) 6 2 1) Equiv.ulift.symm p]
  exact mme_dwz_coarseClassBasis_q6_val K 2 1 p.down

private theorem canonicalComponentZBasis14_val
    (K : Type u) [Field K] (p : LiftedCoarsePair.{u} 6 1) :
    (canonicalComponentZBasis K (14 : Fin 15) p).1 =
      cwSquareCanonicalBasis K 6 2 p.down.1 := by
  rw [show canonicalComponentZBasis K (14 : Fin 15) p =
    coarseClassBasis (K := K) 6 2 1 p.down by
      exact Module.Basis.reindex_apply
        (coarseClassBasis (K := K) 6 2 1) Equiv.ulift.symm p]
  exact mme_dwz_coarseClassBasis_q6_val K 2 1 p.down

private theorem row121SwapTo211BaseMap_Z_basis
    (K : Type u) [Field K]
    (p : LiftedCoarsePair.{u} 6 1) :
    row121SwapTo211BaseMap K 2
        (canonicalComponentZBasis K (13 : Fin 15) p) =
      canonicalComponentZBasis K (14 : Fin 15) p := by
  apply Subtype.ext
  change cwSquareSwapToBaseLocal K 6 2
      (canonicalComponentZBasis K (13 : Fin 15) p).1 =
    (canonicalComponentZBasis K (14 : Fin 15) p).1
  rw [canonicalComponentZBasis13_val,
    canonicalComponentZBasis14_val]
  exact cwSquareSwapToBaseLocal_basis K 6 (2 : Fin 3) p.down.1

/-- Swapping the first two tensor modes carries the literal Table-2 `121`
component to the literal `211` component.  The witness preserves the
component tensor exactly and fixes every named third-mode coarse-pair basis
label. -/
theorem mme_dwz_q6_canonical_121_swap_to_211_basis_transport
    (K : Type u) [Field K] :
    ∃ maps : ∀ i : Fin 3,
        (TensorObj.permObj swapFirstTwoPerm
          (canonicalComponentBlock K (13 : Fin 15))).V i →ₗ[K]
        (canonicalComponentBlock K (14 : Fin 15)).V i,
      PiTensorProduct.map maps
          (TensorObj.permObj swapFirstTwoPerm
            (canonicalComponentBlock K (13 : Fin 15))).t =
        (canonicalComponentBlock K (14 : Fin 15)).t ∧
      ∀ p : LiftedCoarsePair.{u} 6 1,
        maps 2 (canonicalComponentZBasis K (13 : Fin 15) p) =
          canonicalComponentZBasis K (14 : Fin 15) p := by
  exact ⟨row121SwapTo211BaseMap K,
    row121SwapTo211BaseMap_tensor K,
    row121SwapTo211BaseMap_Z_basis K⟩

end MME

theorem solution
    (K : Type u) [Field K] :
    ∃ maps : ∀ i : Fin 3,
        (TensorObj.permObj swapFirstTwoPerm
          (canonicalComponentBlock K (13 : Fin 15))).V i →ₗ[K]
        (canonicalComponentBlock K (14 : Fin 15)).V i,
      PiTensorProduct.map maps
          (TensorObj.permObj swapFirstTwoPerm
            (canonicalComponentBlock K (13 : Fin 15))).t =
        (canonicalComponentBlock K (14 : Fin 15)).t ∧
      ∀ p : LiftedCoarsePair.{u} 6 1,
        maps 2 (canonicalComponentZBasis K (13 : Fin 15) p) =
          canonicalComponentZBasis K (14 : Fin 15) p := by
  exact MME.mme_dwz_q6_canonical_121_swap_to_211_basis_transport K
