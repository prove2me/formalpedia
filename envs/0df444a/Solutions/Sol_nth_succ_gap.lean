-- Prove2me | solution 1 for nth_succ_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:21:57.918429+00:00
-- url     : https://prove2.me/submissions/5249746f-d2cf-41d9-bd8e-b94ca30ae910

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments

set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}
theorem _root_.solution {p : ℕ → Prop} (hf : (setOf p).Infinite) (n : ℕ) :
    ∀ k < Nat.nth p (n + 1) - Nat.nth p n, k > 0 → ¬ p (k + Nat.nth p n) := by
  intro k h_k1 h_k0 h_p_k
  let m := Nat.count p (k + Nat.nth p n)
  have h_k_ex : Nat.nth p m = k + Nat.nth p n := by simp [m, Nat.nth_count h_p_k]
  have h_n_m : n < m := by apply (Nat.nth_lt_nth hf).mp ; omega
  have h_m_n : m < n + 1 := by apply (Nat.nth_lt_nth hf).mp ; omega
  omega
