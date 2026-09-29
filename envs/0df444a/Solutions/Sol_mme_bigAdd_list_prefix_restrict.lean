-- Prove2me | solution 1 for mme_bigAdd_list_prefix_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T19:35:00.748018+00:00
-- url     : https://prove2.me/submissions/1062a36a-1d2d-4413-8821-f8907273934c

import Theorems.Thm_mme_bigAdd_prefix_restrict

open MME BigOperators

universe u v

set_option autoImplicit false
set_option warningAsError true

/-- A literal list prefix of tensor summands restricts from the whole list. -/
theorem solution
    {K : Type u} [Field K] {d : ℕ} {Item : Type v}
    (hd : 1 < d) (X : Item → TensorObj K d)
    (pre remainder : List Item) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun i : Fin pre.length ↦ X (pre.get i)))
      (TensorObj.bigAdd (fun i : Fin (pre ++ remainder).length ↦
        X ((pre ++ remainder).get i))) := by
  let hlen : pre.length ≤ (pre ++ remainder).length := by simp
  have h := mme_bigAdd_prefix_restrict (K := K) (d := d)
    hd hlen (fun i : Fin (pre ++ remainder).length ↦
      X ((pre ++ remainder).get i))
  have hfun :
      (fun i : Fin pre.length ↦
        X ((pre ++ remainder).get (Fin.castLE hlen i))) =
      (fun i : Fin pre.length ↦ X (pre.get i)) := by
    funext i
    apply congrArg X
    rw [List.get_eq_getElem, List.get_eq_getElem]
    exact List.getElem_append_left i.isLt
  rw [hfun] at h
  exact h
