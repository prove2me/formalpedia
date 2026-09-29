-- Prove2me | solution 1 for mme_basisZAllowed_blockSubtensor_inclusion_tensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T10:25:21.522549+00:00
-- url     : https://prove2.me/submissions/cc9df124-61e3-459d-985a-500a5e234e1b

import Definitions.Def_mme_basis_z_allowed_projection
import Definitions.Def_mme_block_subtensor
import Theorems.Thm_mme_basisZAllowedSubtensor_projection_certificate
import Mathlib.Tactic.FinCases

open MME Module DirectSum

universe u

set_option autoImplicit false
set_option warningAsError true

namespace MME.TensorObj.TypeGrading

private theorem blockProj_subtype_apply_of_mem
    {K : Type u} [Field K] {d t : ℕ}
    {T : TensorObj K d} (G : T.TypeGrading t)
    (i : Fin d) (a : Fin t) (x : T.V i)
    (hx : x ∈ G.classOf i a) :
    (G.classOf i a).subtype (G.blockProj i a x) = x := by
  change ((G.blockProj i a x : G.classOf i a) : T.V i) = x
  change (((G.modeLequiv i).symm x) a : T.V i) = x
  exact congrArg Subtype.val
    ((G.is_internal i).ofBijective_coeLinearMap_of_mem hx)

private theorem blockProj_subtype_apply_eq_zero_of_mem_ne
    {K : Type u} [Field K] {d t : ℕ}
    {T : TensorObj K d} (G : T.TypeGrading t)
    (i : Fin d) {a b : Fin t} (hab : b ≠ a) (x : T.V i)
    (hx : x ∈ G.classOf i b) :
    (G.classOf i a).subtype (G.blockProj i a x) = 0 := by
  change ((G.blockProj i a x : G.classOf i a) : T.V i) = 0
  change (((G.modeLequiv i).symm x) a : T.V i) = 0
  have hzero :=
    (G.is_internal i).ofBijective_coeLinearMap_of_mem_ne hab hx
  exact congrArg Subtype.val hzero

private theorem basisZAllowed_blockProj_subtype_basis
    {K : Type u} [Field K]
    (T : TensorObj K 3) {ι : Type u}
    (bZ : Basis ι K (T.V 2)) (allowed : ι → Prop)
    [DecidablePred allowed] (j : ι) :
    let G := T.basisZAllowedGrading bZ allowed
    (G.classOf 2 0).subtype (G.blockProj 2 0 (bZ j)) =
      if allowed j then bZ j else 0 := by
  classical
  dsimp only
  by_cases hj : allowed j
  · rw [if_pos hj]
    apply blockProj_subtype_apply_of_mem
    change bZ j ∈ cwBasisGrade bZ
      (fun k ↦ if allowed k then 0 else 1) 0
    exact Submodule.subset_span
      ⟨j, by simp only [Set.mem_ofPred_eq, if_pos hj], rfl⟩
  · rw [if_neg hj]
    apply blockProj_subtype_apply_eq_zero_of_mem_ne
      (b := (1 : Fin 2))
    · decide
    · change bZ j ∈ cwBasisGrade bZ
        (fun k ↦ if allowed k then 0 else 1) 1
      exact Submodule.subset_span
        ⟨j, by simp only [Set.mem_ofPred_eq, if_neg hj], rfl⟩

private theorem basisZAllowed_blockProj_subtype_mode_zero
    {K : Type u} [Field K]
    (T : TensorObj K 3) {ι : Type u}
    (bZ : Basis ι K (T.V 2)) (allowed : ι → Prop)
    [DecidablePred allowed] (x : T.V 0) :
    let G := T.basisZAllowedGrading bZ allowed
    (G.classOf 0 0).subtype (G.blockProj 0 0 x) = x := by
  dsimp only
  apply blockProj_subtype_apply_of_mem
  rw [(mme_basisZAllowedSubtensor_projection_certificate
    T bZ allowed).2.1]
  exact Submodule.mem_top

private theorem basisZAllowed_blockProj_subtype_mode_one
    {K : Type u} [Field K]
    (T : TensorObj K 3) {ι : Type u}
    (bZ : Basis ι K (T.V 2)) (allowed : ι → Prop)
    [DecidablePred allowed] (x : T.V 1) :
    let G := T.basisZAllowedGrading bZ allowed
    (G.classOf 1 0).subtype (G.blockProj 1 0 x) = x := by
  dsimp only
  apply blockProj_subtype_apply_of_mem
  rw [(mme_basisZAllowedSubtensor_projection_certificate
    T bZ allowed).2.2.1]
  exact Submodule.mem_top

private theorem basisZAllowed_inclusion_comp_blockProj
    {K : Type u} [Field K]
    (T : TensorObj K 3) {ι : Type u}
    (bZ : Basis ι K (T.V 2)) (allowed : ι → Prop)
    [DecidablePred allowed] :
    let G := T.basisZAllowedGrading bZ allowed
    (fun i ↦ (G.classOf i 0).subtype.comp (G.blockProj i 0)) =
      Function.update (fun _ ↦ LinearMap.id) 2
        (bZ.constr K (fun j ↦ if allowed j then bZ j else 0)) := by
  dsimp only
  funext i
  fin_cases i
  · ext x
    exact basisZAllowed_blockProj_subtype_mode_zero T bZ allowed x
  · ext x
    exact basisZAllowed_blockProj_subtype_mode_one T bZ allowed x
  · apply bZ.ext
    intro j
    change
      ((T.basisZAllowedGrading bZ allowed).classOf 2 0).subtype
          ((T.basisZAllowedGrading bZ allowed).blockProj 2 0 (bZ j)) =
        (bZ.constr K (fun j ↦ if allowed j then bZ j else 0)) (bZ j)
    rw [basisZAllowed_blockProj_subtype_basis T bZ allowed]
    simp only [Module.Basis.constr_basis]

end MME.TensorObj.TypeGrading

theorem solution
    {K : Type u} [Field K]
    (T : TensorObj K 3) {ι : Type u}
    (bZ : Basis ι K (T.V 2)) (allowed : ι → Prop)
    [DecidablePred allowed] :
    let G := T.basisZAllowedGrading bZ allowed
    PiTensorProduct.map (fun i ↦ (G.classOf i 0).subtype)
        (G.blockSubtensor (fun _ ↦ 0)).t =
      PiTensorProduct.map
        (Function.update (fun _ ↦ LinearMap.id) 2
          (bZ.constr K (fun j ↦ if allowed j then bZ j else 0)))
        T.t := by
  dsimp only [TensorObj.TypeGrading.blockSubtensor,
    TensorObj.TypeGrading.blockTensor]
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  rw [MME.TensorObj.TypeGrading.basisZAllowed_inclusion_comp_blockProj
    T bZ allowed]
