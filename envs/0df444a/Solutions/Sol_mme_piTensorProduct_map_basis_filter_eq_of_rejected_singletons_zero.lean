-- Prove2me | solution 1 for mme_piTensorProduct_map_basis_filter_eq_of_rejected_singletons_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T22:05:26.143215+00:00
-- url     : https://prove2.me/submissions/5a9e1826-0709-47db-86bd-a937a0c589de

import Theorems.Thm_mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons_at_mode

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

/-- A finite basis filter at any tensor mode preserves a mapped tensor when
every rejected singleton slice already vanishes.  The other mode maps are
arbitrary, so filters can be inserted successively. -/
theorem solution
    {K : Type u} [Field K] {d : ℕ}
    {S U : TensorObj K d} {I : Type u}
    [Fintype I] [DecidableEq I]
    (slot : Fin d) (b : Basis I K (S.V slot))
    (allowed : I → Prop) [DecidablePred allowed]
    (maps : ∀ i : Fin d, S.V i →ₗ[K] U.V i)
    (hzero : ∀ j : I, ¬ allowed j →
      let singleton : S.V slot →ₗ[K] S.V slot :=
        MME.DWZComponentRestriction.basisLabelProjection b id {j}
      PiTensorProduct.map
        (Function.update maps slot ((maps slot).comp singleton)) S.t = 0) :
    let keep : S.V slot →ₗ[K] S.V slot :=
      MME.DWZComponentRestriction.basisLabelProjection b id
        (Finset.univ.filter allowed)
    PiTensorProduct.map
        (Function.update maps slot ((maps slot).comp keep)) S.t =
      PiTensorProduct.map maps S.t := by
  classical
  dsimp only at hzero ⊢
  let keep : S.V slot →ₗ[K] S.V slot :=
    MME.DWZComponentRestriction.basisLabelProjection b id
      (Finset.univ.filter allowed)
  let reject : S.V slot →ₗ[K] S.V slot :=
    MME.DWZComponentRestriction.basisLabelProjection b id
      (Finset.univ.filter fun j ↦ ¬ allowed j)
  let rejectedMaps : ∀ i : Fin d, S.V i →ₗ[K] U.V i :=
    Function.update maps slot ((maps slot).comp reject)
  have hrejected : PiTensorProduct.map rejectedMaps S.t = 0 := by
    refine mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons_at_mode
      (K := K) (d := d) (S := S) (U := U) (Z := S.V slot) (I := I)
      slot b (fun j ↦ ¬ allowed j) LinearMap.id
        ((maps slot).comp reject) rejectedMaps ?_ ?_ ?_
    · simp only [rejectedMaps, Function.update_self, LinearMap.comp_id]
    · intro j hj
      have hjAllowed : allowed j := not_not.mp hj
      simp only [LinearMap.comp_apply, reject,
        MME.DWZComponentRestriction.basisLabelProjection,
        Module.Basis.constr_basis, id_eq, Finset.mem_filter,
        Finset.mem_univ, true_and, hjAllowed, not_true_eq_false, if_false,
        map_zero]
    · intro j hj
      dsimp only
      have hrejsingle : reject.comp
          (MME.DWZComponentRestriction.basisLabelProjection b id {j}) =
          MME.DWZComponentRestriction.basisLabelProjection b id {j} := by
        apply b.ext
        intro x
        by_cases hx : x = j
        · subst x
          simp only [LinearMap.comp_apply, reject,
            MME.DWZComponentRestriction.basisLabelProjection,
            Module.Basis.constr_basis, id_eq, Finset.mem_singleton,
            Finset.mem_filter, Finset.mem_univ, true_and, hj,
            not_false_eq_true, if_true]
        · simp only [LinearMap.comp_apply, reject,
            MME.DWZComponentRestriction.basisLabelProjection,
            Module.Basis.constr_basis, id_eq, Finset.mem_singleton,
            if_neg hx, map_zero]
      have hupdate : Function.update rejectedMaps slot
            ((((maps slot).comp reject).comp
              (MME.DWZComponentRestriction.basisLabelProjection b id {j}))) =
          Function.update maps slot
            ((maps slot).comp
              (MME.DWZComponentRestriction.basisLabelProjection b id {j})) := by
        rw [LinearMap.comp_assoc, hrejsingle]
        funext i
        by_cases hi : i = slot
        · subst i
          simp only [Function.update_self]
        · simp only [Function.update_of_ne hi, rejectedMaps]
      simp only [LinearMap.comp_id]
      rw [hupdate]
      exact hzero j hj
  have hsplit : LinearMap.id = keep + reject := by
    apply b.ext
    intro j
    by_cases hj : allowed j
    · simp only [LinearMap.add_apply, LinearMap.id_apply, keep, reject,
        MME.DWZComponentRestriction.basisLabelProjection,
        Module.Basis.constr_basis, id_eq, Finset.mem_filter,
        Finset.mem_univ, true_and, hj, if_true, not_true_eq_false, if_false,
        add_zero]
    · simp only [LinearMap.add_apply, LinearMap.id_apply, keep, reject,
        MME.DWZComponentRestriction.basisLabelProjection,
        Module.Basis.constr_basis, id_eq, Finset.mem_filter,
        Finset.mem_univ, true_and, hj, if_false, not_false_eq_true, if_true,
        zero_add]
  have hmapsSlot : maps slot = (maps slot).comp keep +
      (maps slot).comp reject := by
    rw [← LinearMap.comp_add, ← hsplit, LinearMap.comp_id]
  have hmaps : maps = Function.update maps slot
      ((maps slot).comp keep + (maps slot).comp reject) := by
    funext i
    by_cases hi : i = slot
    · subst i
      simp only [Function.update_self]
      exact hmapsSlot
    · simp only [Function.update_of_ne hi]
  conv_rhs => rw [hmaps, PiTensorProduct.map_update_add,
    LinearMap.add_apply]
  change _ = _ + PiTensorProduct.map rejectedMaps S.t
  rw [hrejected, add_zero]
