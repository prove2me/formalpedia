-- Prove2me | solution 1 for mme_bigAdd_fin_mul_isomorphic_nested
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T12:40:23.319894+00:00
-- url     : https://prove2.me/submissions/db7d7d0b-2bd0-4ab8-bc2a-fa198e1e9a72

import Definitions.Def_mme_rank_bridge

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {d k g : ℕ}
    (X : Fin k → Fin g → TensorObj K d) :
    TensorObj.Isomorphic
      (TensorObj.bigAdd (fun r : Fin (k * g) ↦
        X (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2))
      (TensorObj.bigAdd (fun a : Fin k ↦
        TensorObj.bigAdd (fun b : Fin g ↦ X a b))) := by
  apply TensorQ.toQ_eq_iff.mp
  rw [TensorQ.toQ_bigAdd, TensorQ.toQ_bigAdd]
  simp_rw [TensorQ.toQ_bigAdd]
  rw [← Finset.sum_product']
  exact Equiv.sum_comp finProdFinEquiv.symm
    (fun p : Fin k × Fin g ↦ TensorQ.toQ (X p.1 p.2))
