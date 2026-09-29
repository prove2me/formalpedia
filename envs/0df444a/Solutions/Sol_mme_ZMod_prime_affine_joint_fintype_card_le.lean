-- Prove2me | solution 1 for mme_ZMod_prime_affine_joint_fintype_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:58:45.50177+00:00
-- url     : https://prove2.me/submissions/8543d8c7-ff7c-4949-b540-e42844c1832d

import Mathlib
import Theorems.Thm_mme_ZMod_prime_linear_hash_affine_graph_fintype_card

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p n : ℕ} [Fact p.Prime]
    {I : Type*} [Fintype I] [DecidableEq I]
    (hcard : Fintype.card I = n + 1)
    (c : I → ZMod p) (j : I) (hc : c j ≠ 0)
    (offset : (I → ZMod p) → ZMod p)
    (joint : ((I → ZMod p) × ZMod p) → Prop)
    [DecidablePred joint]
    (hnormal : ∀ q, joint q →
      (∑ i, c i * q.1 i) = 0 ∧ q.2 = offset q.1) :
    ((Finset.univ.filter joint).card) ≤ p ^ n := by
  classical
  have hsubset :
      Finset.univ.filter joint ⊆
        Finset.univ.filter (fun q : (I → ZMod p) × ZMod p ↦
          (∑ i, c i * q.1 i) ∈ ({0} : Finset (ZMod p)) ∧
            q.2 = offset q.1) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    have h := hnormal q hq
    simpa using h
  have hle := Finset.card_le_card hsubset
  rw [mme_ZMod_prime_linear_hash_affine_graph_fintype_card
    hcard c j hc ({0} : Finset (ZMod p)) offset] at hle
  simpa using hle
