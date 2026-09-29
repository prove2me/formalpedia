-- Prove2me | solution 1 for mme_kronFin_selected_basis_postmap_eq_zero_of_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T22:46:50.035932+00:00
-- url     : https://prove2.me/submissions/fb3b1d85-5ec9-42b0-ae27-2db070edb3b8

import Definitions.Def_mme_dwz_basis_label_projection
import Definitions.Def_mme_TypeGrading_kron
import Mathlib.LinearAlgebra.TensorProduct.Basis

open Module TensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true

/-- Projection to a singleton of a tensor-product basis is the tensor product
of the two singleton basis projections. -/
theorem mme_basisLabelProjection_tensorProduct_singleton
    {K : Type u} [Field K]
    {V W : Type u} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    {I J : Type u} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (bV : Basis I K V) (bW : Basis J K W) (x : I) (y : J) :
    MME.DWZComponentRestriction.basisLabelProjection
        (bV.tensorProduct bW) id {(x, y)} =
      TensorProduct.map
        (MME.DWZComponentRestriction.basisLabelProjection bV id {x})
        (MME.DWZComponentRestriction.basisLabelProjection bW id {y}) := by
  apply (bV.tensorProduct bW).ext
  intro z
  rcases z with ⟨a, b⟩
  unfold MME.DWZComponentRestriction.basisLabelProjection
  rw [Module.Basis.constr_basis]
  rw [Module.Basis.tensorProduct_apply, TensorProduct.map_tmul]
  by_cases ha : a = x
  · subst a
    by_cases hb : b = y
    · subst b
      simp only [id_eq, Finset.mem_singleton, if_true,
        Module.Basis.constr_basis]
    · simp only [id_eq, Finset.mem_singleton, Prod.mk.injEq, hb,
        and_false, if_false, Module.Basis.constr_basis, if_true, tmul_zero]
  · simp only [id_eq, Finset.mem_singleton, Prod.mk.injEq, ha,
      false_and, if_false, Module.Basis.constr_basis, zero_tmul]

/-- Reindexing a basis transports a singleton projection to the inverse image
of the selected label. -/
theorem mme_basisLabelProjection_reindex_singleton
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {I J : Type u} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (b : Basis I K V) (e : I ≃ J) (x : J) :
    MME.DWZComponentRestriction.basisLabelProjection
        (b.reindex e) id {x} =
      MME.DWZComponentRestriction.basisLabelProjection
        b id {e.symm x} := by
  apply (b.reindex e).ext
  intro y
  unfold MME.DWZComponentRestriction.basisLabelProjection
  rw [Module.Basis.constr_basis, Module.Basis.reindex_apply,
    Module.Basis.constr_basis]
  simp only [id_eq, Finset.mem_singleton, Equiv.symm_apply_eq,
    Equiv.apply_symm_apply]

open MME

/-- The singleton projection for the recursive word basis of a nonempty
ordered Kronecker product is the tensor product of the head and tail
singleton projections. -/
theorem mme_kronFinModePiBasis_singleton_projection_succ
    {K : Type u} [Field K] {d n : ℕ}
    (X : Fin (n + 1) → TensorObj K d) (i : Fin d)
    {Index : Fin (n + 1) → Type u}
    [∀ r, Fintype (Index r)] [∀ r, DecidableEq (Index r)]
    (b : ∀ r, Basis (Index r) K ((X r).V i))
    (word : ∀ r, Index r) :
    MME.DWZComponentRestriction.basisLabelProjection
        (TensorObj.kronFinModePiBasis (n + 1) X i b) id {word} =
      TensorProduct.map
        (MME.DWZComponentRestriction.basisLabelProjection
          (b 0) id {word 0})
        (MME.DWZComponentRestriction.basisLabelProjection
          (TensorObj.kronFinModePiBasis n
            (fun r : Fin n ↦ X r.succ) i (fun r ↦ b r.succ))
          id ({fun r : Fin n ↦ word r.succ} :
            Finset (∀ r : Fin n, Index r.succ))) := by
  let tailBasis := TensorObj.kronFinModePiBasis n
    (fun r : Fin n ↦ X r.succ) i (fun r ↦ b r.succ)
  change MME.DWZComponentRestriction.basisLabelProjection
      (((b 0).tensorProduct tailBasis).reindex (Fin.consEquiv Index))
        id {word} = _
  rw [mme_basisLabelProjection_reindex_singleton
    ((b 0).tensorProduct tailBasis) (Fin.consEquiv Index) word]
  have hcons : (Fin.consEquiv Index).symm word =
      (word 0, fun r : Fin n ↦ word r.succ) := rfl
  rw [hcons]
  exact mme_basisLabelProjection_tensorProduct_singleton
    (b 0) tailBasis (word 0) (fun r ↦ word r.succ)

/-- If the selected singleton basis tuple kills one factor tensor, then the
selected product-basis word kills the complete ordered Kronecker product. -/
theorem mme_kronFin_selected_basis_map_eq_zero_of_coordinate
    {K : Type u} [Field K] {d n : ℕ}
    (X : Fin n → TensorObj K d)
    {Index : Fin n → Fin d → Type u}
    [∀ r i, Fintype (Index r i)]
    [∀ r i, DecidableEq (Index r i)]
    (b : ∀ r i, Basis (Index r i) K ((X r).V i))
    (word : ∀ i r, Index r i)
    (r : Fin n)
    (hlocal : PiTensorProduct.map
      (fun i ↦ MME.DWZComponentRestriction.basisLabelProjection
        (b r i) id {word i r}) (X r).t = 0) :
    PiTensorProduct.map
        (fun i ↦ MME.DWZComponentRestriction.basisLabelProjection
          (TensorObj.kronFinModePiBasis n X i (fun r ↦ b r i))
          id {word i})
        (TensorObj.kronFin n X).t = 0 := by
  induction n with
  | zero => exact r.elim0
  | succ n ih =>
      let headMaps : ∀ i : Fin d, (X 0).V i →ₗ[K] (X 0).V i :=
        fun i ↦ MME.DWZComponentRestriction.basisLabelProjection
          (b 0 i) id {word i 0}
      let tailX : Fin n → TensorObj K d := fun s ↦ X s.succ
      let tailIndex : Fin n → Fin d → Type u := fun s i ↦ Index s.succ i
      let tailB : ∀ s i, Basis (tailIndex s i) K ((tailX s).V i) :=
        fun s i ↦ b s.succ i
      let tailWord : ∀ i s, tailIndex s i := fun i s ↦ word i s.succ
      let tailMaps : ∀ i : Fin d,
          (TensorObj.kronFin n tailX).V i →ₗ[K]
            (TensorObj.kronFin n tailX).V i := fun i ↦
        MME.DWZComponentRestriction.basisLabelProjection
          (TensorObj.kronFinModePiBasis n tailX i (fun s ↦ tailB s i))
          id {tailWord i}
      have hmaps :
          (fun i ↦ MME.DWZComponentRestriction.basisLabelProjection
            (TensorObj.kronFinModePiBasis (n + 1) X i
              (fun s ↦ b s i)) id {word i}) =
          (fun i ↦ TensorProduct.map (headMaps i) (tailMaps i)) := by
        funext i
        exact mme_kronFinModePiBasis_singleton_projection_succ
          X i (fun s ↦ b s i) (word i)
      rw [hmaps]
      change PiTensorProduct.map
          (fun i ↦ TensorProduct.map (headMaps i) (tailMaps i))
          (interchange (X 0).t (TensorObj.kronFin n tailX).t) = 0
      rw [TensorObj.TypeGrading.kronMap_interchange]
      cases r using Fin.cases with
      | zero =>
        have hhead : PiTensorProduct.map headMaps (X 0).t = 0 := by
          simpa only [headMaps] using hlocal
        rw [hhead]
        show interchange (0 : PiTensorProduct K fun i ↦ (X 0).V i)
            (PiTensorProduct.map tailMaps (TensorObj.kronFin n tailX).t) = 0
        rw [map_zero]
        rfl
      | succ r' =>
        have htailLocal : PiTensorProduct.map
            (fun i ↦ MME.DWZComponentRestriction.basisLabelProjection
              (tailB r' i) id {tailWord i r'})
            (tailX r').t = 0 := by
          simpa only [tailB, tailWord, tailX] using hlocal
        have htail := ih tailX tailB tailWord r' htailLocal
        have htail' : PiTensorProduct.map tailMaps
            (TensorObj.kronFin n tailX).t = 0 := by
          simpa only [tailMaps] using htail
        rw [htail']
        exact LinearMap.map_zero _

/-- The preceding zero remains zero after arbitrary mode-wise postmaps. -/
theorem solution
    {K : Type u} [Field K] {d n : ℕ}
    (X : Fin n → TensorObj K d)
    {Index : Fin n → Fin d → Type u}
    [∀ r i, Fintype (Index r i)]
    [∀ r i, DecidableEq (Index r i)]
    (b : ∀ r i, Basis (Index r i) K ((X r).V i))
    (word : ∀ i r, Index r i)
    {W : Fin d → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (post : ∀ i, (TensorObj.kronFin n X).V i →ₗ[K] W i)
    (r : Fin n)
    (hlocal : PiTensorProduct.map
      (fun i ↦ MME.DWZComponentRestriction.basisLabelProjection
        (b r i) id {word i r}) (X r).t = 0) :
    PiTensorProduct.map
        (fun i ↦ (post i).comp
          (MME.DWZComponentRestriction.basisLabelProjection
            (TensorObj.kronFinModePiBasis n X i (fun r ↦ b r i))
            id {word i}))
        (TensorObj.kronFin n X).t = 0 := by
  rw [PiTensorProduct.map_comp]
  change PiTensorProduct.map post
      (PiTensorProduct.map
        (fun i ↦ MME.DWZComponentRestriction.basisLabelProjection
          (TensorObj.kronFinModePiBasis n X i (fun r ↦ b r i))
          id {word i})
        (TensorObj.kronFin n X).t) = 0
  rw [mme_kronFin_selected_basis_map_eq_zero_of_coordinate
    X b word r hlocal]
  exact LinearMap.map_zero _
