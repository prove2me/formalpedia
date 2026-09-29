-- Prove2me | solution 1 for mme_CW_q6_Zcount_quadratic_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T03:16:39.895781+00:00
-- url     : https://prove2.me/submissions/74f47a6e-7bd7-41b4-9547-c5cc31f0b5b9

import Mathlib.Data.Nat.Choose.Basic

private theorem self_le_choose_of_pos_of_lt :
    ∀ {n k : ℕ}, 0 < k → k < n → n ≤ Nat.choose n k := by
  intro n
  induction n with
  | zero =>
      intro k hk hkn
      omega
  | succ n ih =>
      intro k hk hkn
      cases k with
      | zero => simp at hk
      | succ k =>
          by_cases hk0 : k = 0
          · subst k
            simp
          · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
            have hkle : k < n := by omega
            have hchoose : n ≤ Nat.choose n k := ih hkpos hkle
            have hpositive : 0 < Nat.choose n (k + 1) :=
              Nat.choose_pos (by omega)
            have hpositive' : 1 ≤ Nat.choose n k.succ := hpositive
            rw [Nat.choose_succ_succ]
            exact (Nat.succ_le_succ hchoose).trans
              (Nat.add_le_add_left hpositive' _)

theorem solution
    {N L G : ℕ} (hL : 0 < L) (hsum : L + G = N) (hG : 0 < G) :
    2 * N * N ≤
      Nat.choose (2 * N) L * Nat.choose (2 * N - L) L := by
  have hLN : L < N := by omega
  have hL2N : L < 2 * N := by omega
  have hLrem : L < 2 * N - L := by omega
  have hfirst : 2 * N ≤ Nat.choose (2 * N) L :=
    self_le_choose_of_pos_of_lt hL hL2N
  have hsecond : 2 * N - L ≤ Nat.choose (2 * N - L) L :=
    self_le_choose_of_pos_of_lt hL hLrem
  have hNrem : N ≤ 2 * N - L := by omega
  exact Nat.mul_le_mul hfirst (hNrem.trans hsecond)
