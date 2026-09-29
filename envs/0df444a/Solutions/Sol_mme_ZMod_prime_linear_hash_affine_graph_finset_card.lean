-- Prove2me | solution 1 for mme_ZMod_prime_linear_hash_affine_graph_finset_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:36:58.71362+00:00
-- url     : https://prove2.me/submissions/a3ff6acc-a18e-4831-83da-0be8b81f3213

import Theorems.Thm_mme_ZMod_prime_linear_hash_finset_preimage_card

open BigOperators

set_option autoImplicit false

/-- Adding one affine offset determined uniquely by the weight vector does
not change the exact size of a linear-hash preimage. -/
theorem solution
    {p n : ℕ} [hp : Fact p.Prime]
    (c : Fin (n + 1) → ZMod p) (j : Fin (n + 1)) (hc : c j ≠ 0)
    (S : Finset (ZMod p))
    (offset : (Fin (n + 1) → ZMod p) → ZMod p) :
    ((Finset.univ.filter
      (fun q : (Fin (n + 1) → ZMod p) × ZMod p =>
        (∑ i, c i * q.1 i) ∈ S ∧ q.2 = offset q.1)).card) =
      S.card * p ^ n := by
  classical
  let P : Finset ((Fin (n + 1) → ZMod p) × ZMod p) :=
    Finset.univ.filter (fun q =>
      (∑ i, c i * q.1 i) ∈ S ∧ q.2 = offset q.1)
  let W : Finset (Fin (n + 1) → ZMod p) :=
    Finset.univ.filter (fun w => (∑ i, c i * w i) ∈ S)
  have hPW : P.card = W.card := by
    apply Finset.card_bij (fun q _ => q.1)
    · intro q hq
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      simpa only [W, Finset.mem_filter, Finset.mem_univ, true_and]
        using hq.1
    · intro q hq q' hq' heq
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hq hq'
      apply Prod.ext heq
      rw [hq.2, hq'.2, heq]
    · intro w hw
      refine ⟨(w, offset w), ?_, rfl⟩
      simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hw, trivial⟩
  calc
    ((Finset.univ.filter
      (fun q : (Fin (n + 1) → ZMod p) × ZMod p =>
        (∑ i, c i * q.1 i) ∈ S ∧ q.2 = offset q.1)).card) =
        P.card := by rfl
    _ = W.card := hPW
    _ = S.card * p ^ n := by
      exact mme_ZMod_prime_linear_hash_finset_preimage_card c j hc S
