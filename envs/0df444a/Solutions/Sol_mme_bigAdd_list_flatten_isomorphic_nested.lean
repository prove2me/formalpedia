-- Prove2me | solution 1 for mme_bigAdd_list_flatten_isomorphic_nested
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T19:30:05.703895+00:00
-- url     : https://prove2.me/submissions/9b63910d-3902-4624-9f5d-1c80a98c5c00

import Definitions.Def_mme_rank_bridge

open MME BigOperators

universe u v

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {d : ℕ} {Item : Type v}
    (groups : List (List Item)) (X : Item → TensorObj K d) :
    TensorObj.Isomorphic
      (TensorObj.bigAdd (fun r : Fin groups.flatten.length ↦
        X (groups.flatten.get r)))
      (TensorObj.bigAdd (fun a : Fin groups.length ↦
        TensorObj.bigAdd (fun b : Fin (groups.get a).length ↦
          X ((groups.get a).get b)))) := by
  apply TensorQ.toQ_eq_iff.mp
  rw [TensorQ.toQ_bigAdd, TensorQ.toQ_bigAdd]
  simp_rw [TensorQ.toQ_bigAdd]
  simp_rw [← List.sum_ofFn]
  simp only [List.ofFn_comp', List.ofFn_get]
  rw [← List.sum_flatten, List.map_flatten]
  rw [List.map_flatten]
