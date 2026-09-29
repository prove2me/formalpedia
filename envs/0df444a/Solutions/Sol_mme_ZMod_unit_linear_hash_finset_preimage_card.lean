-- Prove2me | solution 1 for mme_ZMod_unit_linear_hash_finset_preimage_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:20:33.531337+00:00
-- url     : https://prove2.me/submissions/fdc2e85d-36fd-4bc8-aa12-990578ebc6ef

import Mathlib
import Theorems.Thm_mme_ZMod_unit_linear_hash_fiber_card

open BigOperators

set_option autoImplicit false

/-- A linear hash over an arbitrary residue ring with one unit coefficient
pulls back a finite residue set with exactly the expected cardinality. -/
theorem solution {M n : ℕ} [NeZero M]
    (c : Fin (n + 1) → ZMod M) (j : Fin (n + 1))
    (hc : IsUnit (c j)) (S : Finset (ZMod M)) :
    ((Finset.univ.filter (fun w : Fin (n + 1) → ZMod M =>
      (∑ i, c i * w i) ∈ S)).card) = S.card * M ^ n := by
  let L : (Fin (n + 1) → ZMod M) → ZMod M :=
    fun w => ∑ i, c i * w i
  rw [← Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin (n + 1) → ZMod M)) S L]
  calc
    ∑ z ∈ S, ((Finset.univ.filter
        (fun w : Fin (n + 1) → ZMod M => L w = z)).card) =
        ∑ _z ∈ S, M ^ n := by
          apply Finset.sum_congr rfl
          intro z hz
          exact mme_ZMod_unit_linear_hash_fiber_card c j hc z
    _ = S.card * M ^ n := by simp
