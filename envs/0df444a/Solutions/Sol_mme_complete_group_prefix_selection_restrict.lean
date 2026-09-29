-- Prove2me | solution 1 for mme_complete_group_prefix_selection_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T19:05:37.531224+00:00
-- url     : https://prove2.me/submissions/9de9bd2d-2212-4a02-9b09-c0ad2a277b81

import Theorems.Thm_mme_bigAdd_prefix_restrict
import Theorems.Thm_mme_nat_complete_group_floor_real_lower

open MME BigOperators

universe u v

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {d n : ℕ} {Item : Type v}
    (hd : 1 < d) (g : ℕ) (hg : 0 < g)
    (item : Fin n → Item) (Good : Item → Prop)
    (hgood : ∀ i, Good (item i))
    (X : Item → TensorObj K d) (T : TensorObj K d)
    (hsource : TensorObj.Restrict
      (TensorObj.bigAdd (fun i : Fin n ↦ X (item i))) T)
    (A : ℝ) (hlarge : 2 * (g : ℝ) ≤ A) (hlower : A ≤ (n : ℝ)) :
    ∃ (k : ℕ) (selected : Fin (k * g) → Item),
      (∀ r, Good (selected r)) ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun r : Fin (k * g) ↦ X (selected r))) T ∧
      A / (2 * (g : ℝ)) ≤ (k : ℝ) := by
  let k : ℕ := n / g
  have hprefix : k * g ≤ n := by
    exact Nat.div_mul_le_self n g
  let selected : Fin (k * g) → Item := fun r ↦
    item (Fin.castLE hprefix r)
  refine ⟨k, selected, ?_, ?_, ?_⟩
  · intro r
    exact hgood (Fin.castLE hprefix r)
  · exact TensorObj.Restrict.trans
      (mme_bigAdd_prefix_restrict hd hprefix
        (fun i : Fin n ↦ X (item i))) hsource
  · simpa only [k] using
      mme_nat_complete_group_floor_real_lower n g A hg hlarge hlower
