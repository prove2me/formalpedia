-- Prove2me | solution 1 for mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T18:55:51.56038+00:00
-- url     : https://prove2.me/submissions/1dd4bc71-cbbb-4183-b6dd-e5c97d72fb58

import Definitions.Def_mme_dwz_basis_label_projection
import Definitions.Def_mme_tensor

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

private theorem piTensorProduct_map_update_zero'
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i) (i : Fin d) :
    PiTensorProduct.map (Function.update f i 0) = 0 := by
  have hzero := PiTensorProduct.map_update_smul
    f i (0 : K) (0 : V i →ₗ[K] W i)
  simpa only [zero_smul] using hzero

private theorem piTensorProduct_map_update_finset_sum'
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    {J : Type u} [DecidableEq J]
    (f : ∀ i, V i →ₗ[K] W i) (i : Fin d)
    (p : J → V i →ₗ[K] W i) (s : Finset J) (x : PiTensorProduct K V) :
    PiTensorProduct.map (Function.update f i (∑ j ∈ s, p j)) x =
      ∑ j ∈ s,
        PiTensorProduct.map (Function.update f i (p j)) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact LinearMap.congr_fun (piTensorProduct_map_update_zero' f i) x
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        PiTensorProduct.map_update_add, LinearMap.add_apply, ih]

/-- A mode-2 selector which kills every unselected basis vector is the sum
of its selected singleton slices.  Hence singleton-slice vanishing implies
vanishing of the complete mapped tensor, with arbitrary other mode maps and
arbitrary selector codomain. -/
theorem solution
    {K : Type u} [Field K]
    {S U : TensorObj K 3} {Z I : Type u}
    [AddCommGroup Z] [Module K Z]
    [Fintype I] [DecidableEq I]
    (bZ : Basis I K Z) (allowed : I → Prop)
    [DecidablePred allowed]
    (preZ : S.V 2 →ₗ[K] Z) (selectZ : Z →ₗ[K] U.V 2)
    (maps : ∀ i : Fin 3, S.V i →ₗ[K] U.V i)
    (hmodeTwo : maps 2 = selectZ.comp preZ)
    (hdisallowed : ∀ j : I, ¬ allowed j → selectZ (bZ j) = 0)
    (hzero : ∀ j : I, allowed j →
      let singleton : Z →ₗ[K] Z :=
        MME.DWZComponentRestriction.basisLabelProjection bZ id {j}
      PiTensorProduct.map
        (Function.update maps 2
          ((selectZ.comp singleton).comp preZ)) S.t = 0) :
    PiTensorProduct.map maps S.t = 0 := by
  classical
  dsimp only at hzero
  let selected : Finset I := Finset.univ.filter allowed
  let singleton : I → Z →ₗ[K] Z := fun j ↦
    MME.DWZComponentRestriction.basisLabelProjection bZ id {j}
  let piece : I → S.V 2 →ₗ[K] U.V 2 := fun j ↦
    (selectZ.comp (singleton j)).comp preZ
  have hselect : selectZ = ∑ j ∈ selected, selectZ.comp (singleton j) := by
    apply bZ.ext
    intro x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    by_cases hx : allowed x
    · have hxsel : x ∈ selected := by
        simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hx
      rw [Finset.sum_eq_single x]
      · simp only [singleton,
          MME.DWZComponentRestriction.basisLabelProjection,
          Module.Basis.constr_basis, id_eq, Finset.mem_singleton, if_true]
      · intro y hy hne
        simp only [singleton,
          MME.DWZComponentRestriction.basisLabelProjection,
          Module.Basis.constr_basis, id_eq, Finset.mem_singleton,
          if_neg (Ne.symm hne), map_zero]
      · exact fun hnot ↦ (hnot hxsel).elim
    · rw [hdisallowed x hx]
      symm
      apply Finset.sum_eq_zero
      intro y hy
      have hxy : x ≠ y := by
        intro hxy
        subst y
        exact hx (by
          simpa only [selected, Finset.mem_filter, Finset.mem_univ,
            true_and] using hy)
      simp only [singleton,
        MME.DWZComponentRestriction.basisLabelProjection,
        Module.Basis.constr_basis, id_eq, Finset.mem_singleton,
        if_neg hxy, map_zero]
  have hmodeTwo' : maps 2 = ∑ j ∈ selected, piece j := by
    rw [hmodeTwo, hselect]
    apply LinearMap.ext
    intro z
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, piece]
  have hmaps : maps = Function.update maps 2 (∑ j ∈ selected, piece j) := by
    funext i
    by_cases hi : i = 2
    · subst i
      rw [Function.update_self]
      exact hmodeTwo'
    · rw [Function.update_of_ne hi]
  rw [hmaps, piTensorProduct_map_update_finset_sum']
  apply Finset.sum_eq_zero
  intro j hj
  have hjAllowed : allowed j := by
    simpa only [selected, Finset.mem_filter, Finset.mem_univ,
      true_and] using hj
  simpa only [piece, singleton] using hzero j hjAllowed
