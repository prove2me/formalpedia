-- Prove2me | solution 1 for mme_Ctensor_outer_triple_distribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:23:38.917167+00:00
-- url     : https://prove2.me/submissions/ae4ce021-8d6d-457e-a279-3ed9a0145d17

import Mathlib.Data.Fintype.Card
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_threeStarCyclicProduct
import Definitions.Def_mme_rank_bridge

open MME BigOperators

universe u

set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    {A : ℕ} (star : Fin A → TensorObj K 3) :
    let I := Fin A × Fin A × Fin A
    let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
    let block : Fin (Fintype.card I) → TensorObj K 3 := fun j =>
      let p := e.symm j
      threeStarCyclicProduct (star p.1) (star p.2.1) (star p.2.2)
    TensorObj.Restrict (TensorObj.bigAdd block)
      (cyclicSymmetrization (TensorObj.bigAdd star)) := by
  classical
  dsimp only
  let I := Fin A × Fin A × Fin A
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let block : Fin (Fintype.card I) → TensorObj K 3 := fun j =>
    let p := e.symm j
    threeStarCyclicProduct (star p.1) (star p.2.1) (star p.2.2)
  apply ((TensorQ.toQ_eq_iff).mp ?_).1
  rw [TensorQ.toQ_bigAdd, cyclicSymmetrization_eq_public_perm,
    TensorQ.toQ_kron, TensorQ.toQ_kron, TensorQ.toQ_bigAdd]
  have hperm1 :
      TensorQ.toQ (TensorObj.permObj cyclicPerm (TensorObj.bigAdd star)) =
        ∑ a, TensorQ.toQ (TensorObj.permObj cyclicPerm (star a)) := by
    calc
      TensorQ.toQ (TensorObj.permObj cyclicPerm (TensorObj.bigAdd star)) =
          TensorQ.permAut cyclicPerm
            (TensorQ.toQ (TensorObj.bigAdd star)) := by
              rw [TensorQ.permAut_toQ]
      _ = TensorQ.permAut cyclicPerm
            (∑ a, TensorQ.toQ (star a)) := by
              rw [TensorQ.toQ_bigAdd]
      _ = ∑ a, TensorQ.toQ (TensorObj.permObj cyclicPerm (star a)) := by
              simp
  have hperm2 :
      TensorQ.toQ
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (TensorObj.bigAdd star)) =
        ∑ a, TensorQ.toQ
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (star a)) := by
    calc
      TensorQ.toQ
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (TensorObj.bigAdd star)) =
          TensorQ.permAut (cyclicPerm.trans cyclicPerm)
            (TensorQ.toQ (TensorObj.bigAdd star)) := by
              rw [TensorQ.permAut_toQ]
      _ = TensorQ.permAut (cyclicPerm.trans cyclicPerm)
            (∑ a, TensorQ.toQ (star a)) := by
              rw [TensorQ.toQ_bigAdd]
      _ = ∑ a, TensorQ.toQ
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (star a)) := by
              simp
  rw [hperm1, hperm2]
  calc
    (∑ j : Fin (Fintype.card I), TensorQ.toQ (block j)) =
        ∑ p : I, TensorQ.toQ
          (threeStarCyclicProduct (star p.1) (star p.2.1) (star p.2.2)) := by
      symm
      apply Fintype.sum_equiv e
      intro p
      simp only [block, Equiv.symm_apply_apply]
    _ = ∑ a : Fin A, ∑ b : Fin A, ∑ c : Fin A,
        TensorQ.toQ (star a) *
          (TensorQ.toQ (TensorObj.permObj cyclicPerm (star b)) *
            TensorQ.toQ
              (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (star c))) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro b _hb
      apply Finset.sum_congr rfl
      intro c _hc
      simp only [threeStarCyclicProduct, TensorQ.toQ_kron]
    _ = (∑ a : Fin A, TensorQ.toQ (star a)) *
        ((∑ b : Fin A,
            TensorQ.toQ (TensorObj.permObj cyclicPerm (star b))) *
          (∑ c : Fin A,
            TensorQ.toQ
              (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (star c)))) := by
      simp_rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
