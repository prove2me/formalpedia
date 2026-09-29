-- Prove2me | solution 1 for syracuse_two_cycle_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T19:26:36.816529+00:00
-- url     : https://prove2.me/submissions/e86a6b43-4bb3-4a9f-8e40-e092b1cb6832

import Mathlib
import Definitions.Def_syracuseStep

open Nat

theorem solution (m : ℕ) (hm : 0 < m) (hcyc : syracuseStep^[2] m = m) : m = 1 := by
  have hxdef : syracuseStep m = ordCompl[2] (3 * m + 1) := rfl
  set x := syracuseStep m with hx
  have h2 : syracuseStep x = m := by
    have : syracuseStep^[2] m = syracuseStep (syracuseStep m) := by
      simp [Function.iterate_succ_apply']
    rwa [this] at hcyc
  have hxpos : 0 < x := by rw [hxdef]; exact Nat.ordCompl_pos 2 (by omega)
  -- the two step relations
  have e1 : 2 ^ ((3 * m + 1).factorization 2) * x = 3 * m + 1 := by
    have h := Nat.ordProj_mul_ordCompl_eq_self (3 * m + 1) 2
    rwa [show ordCompl[2] (3 * m + 1) = x from (hxdef ▸ hx.symm)] at h
  have e2 : 2 ^ ((3 * x + 1).factorization 2) * m = 3 * x + 1 := by
    have h := Nat.ordProj_mul_ordCompl_eq_self (3 * x + 1) 2
    rwa [show ordCompl[2] (3 * x + 1) = m from h2] at h
  set S := (3 * m + 1).factorization 2 + (3 * x + 1).factorization 2 with hS
  have hmul : 2 ^ S * (x * m) = 9 * (m * x) + 3 * m + 3 * x + 1 := by
    rw [hS, pow_add]
    calc 2 ^ ((3 * m + 1).factorization 2) * 2 ^ ((3 * x + 1).factorization 2) * (x * m)
        = (2 ^ ((3 * m + 1).factorization 2) * x) * (2 ^ ((3 * x + 1).factorization 2) * m) := by
          ring
      _ = (3 * m + 1) * (3 * x + 1) := by rw [e1, e2]
      _ = 9 * (m * x) + 3 * m + 3 * x + 1 := by ring
  -- 2 ^ S must exceed 9, hence be at least 16
  have hgt : 9 * (x * m) < 2 ^ S * (x * m) := by
    rw [hmul, Nat.mul_comm x m]
    linarith
  have h9 : 9 < 2 ^ S := by
    by_contra h
    push Not at h
    exact absurd (Nat.mul_le_mul_right (x * m) h) (not_le.mpr hgt)
  have hS4 : 4 ≤ S := by
    by_contra h
    push Not at h
    have h8 : (2:ℕ) ^ S ≤ 8 := by
      calc (2:ℕ) ^ S ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 8 := by norm_num
    linarith
  have h16 : 16 ≤ 2 ^ S := by
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) hS4
  have hkey : 16 * (x * m) ≤ 9 * (m * x) + 3 * m + 3 * x + 1 := by
    rw [← hmul]; exact Nat.mul_le_mul_right _ h16
  -- 7 * m * x <= 3 * m + 3 * x + 1 with m, x >= 1 forces m = x = 1
  have final : ∀ p q : ℕ, 0 < p → 0 < q →
      16 * (q * p) ≤ 9 * (p * q) + 3 * p + 3 * q + 1 → p = 1 := by
    intro p q hp hq h
    obtain ⟨c, rfl⟩ : ∃ c, p = c + 1 := ⟨p - 1, by omega⟩
    obtain ⟨d, rfl⟩ : ∃ d, q = d + 1 := ⟨q - 1, by omega⟩
    have hc : c = 0 := by nlinarith
    omega
  exact final m x hm hxpos hkey
