-- Prove2me | solution 1 for mme_type2_affine_joint_retention_fiber_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:15:43.510676+00:00
-- url     : https://prove2.me/submissions/1cd09b47-e7ff-4eb6-ad48-6edf042355b4

import Mathlib
import Theorems.Thm_mme_ZMod_prime_affine_collision_parameter_card_le

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p n : ℕ} [Fact p.Prime]
    (c : Fin (n + 1) → ZMod p) (j : Fin (n + 1)) (hc : c j ≠ 0)
    (offset : (Fin (n + 1) → ZMod p) → ZMod p)
    (joint : ((Fin (n + 1) → ZMod p) × ZMod p) → Prop)
    [DecidablePred joint]
    (hnormal : ∀ q, joint q →
      (∑ i, c i * q.1 i) = 0 ∧ q.2 = offset q.1) :
    ((Finset.univ.filter joint).card) ≤ p ^ n := by
  classical
  have hset :
      Finset.univ.filter joint =
        Finset.univ.filter (fun q :
            (Fin (n + 1) → ZMod p) × ZMod p ↦
          (∑ i, c i * q.1 i) = 0 ∧
            q.2 = offset q.1 ∧ joint q) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hq
      exact ⟨(hnormal q hq).1, (hnormal q hq).2, hq⟩
    · exact fun hq ↦ hq.2.2
  rw [hset]
  exact mme_ZMod_prime_affine_collision_parameter_card_le
    c j hc offset joint
