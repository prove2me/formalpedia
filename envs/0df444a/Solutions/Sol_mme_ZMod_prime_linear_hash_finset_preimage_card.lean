-- Prove2me | solution 1 for mme_ZMod_prime_linear_hash_finset_preimage_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:47:33.104947+00:00
-- url     : https://prove2.me/submissions/1aaa5adf-dcf6-4be6-b677-fa528e947dc5

import Mathlib
import Theorems.Thm_mme_ZMod_prime_linear_hash_fiber_card

open BigOperators

set_option autoImplicit false

/-- A nonzero prime-field linear hash pulls back a finite residue set with
exactly the expected uniform cardinality. -/
theorem solution {p n : ℕ} [hp : Fact p.Prime]
    (c : Fin (n + 1) → ZMod p) (j : Fin (n + 1)) (hc : c j ≠ 0)
    (S : Finset (ZMod p)) :
    ((Finset.univ.filter (fun w : Fin (n + 1) → ZMod p =>
      (∑ i, c i * w i) ∈ S)).card) = S.card * p ^ n := by
  let L : (Fin (n + 1) → ZMod p) → ZMod p :=
    fun w => ∑ i, c i * w i
  rw [← Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin (n + 1) → ZMod p)) S L]
  calc
    ∑ z ∈ S, ((Finset.univ.filter
        (fun w : Fin (n + 1) → ZMod p => L w = z)).card) =
        ∑ _z ∈ S, p ^ n := by
          apply Finset.sum_congr rfl
          intro z hz
          exact mme_ZMod_prime_linear_hash_fiber_card c j hc z
    _ = S.card * p ^ n := by simp
