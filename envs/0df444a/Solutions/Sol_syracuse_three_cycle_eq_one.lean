-- Prove2me | solution 1 for syracuse_three_cycle_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T19:38:56.951907+00:00
-- url     : https://prove2.me/submissions/1bccc103-ae90-435c-9002-5521e526d93c

import Mathlib
import Definitions.Def_syracuseStep

open Nat

theorem stepEq (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]

theorem stepOdd (n : ℕ) : Odd (syracuseStep n) := by
  rw [Nat.odd_iff, ← Nat.not_even_iff]
  intro he
  exact Nat.not_dvd_ordCompl Nat.prime_two (by omega : 3 * n + 1 ≠ 0) he.two_dvd

theorem stepPos {n : ℕ} : 0 < syracuseStep n := Nat.ordCompl_pos 2 (by omega)

theorem stepSplit (n : ℕ) : 2 ^ ((3 * n + 1).factorization 2) * syracuseStep n = 3 * n + 1 :=
  Nat.ordProj_mul_ordCompl_eq_self (3 * n + 1) 2

-- the three small periodic checks
theorem T1 : syracuseStep 1 = 1 := stepEq 2 (by norm_num) (by decide)
theorem T3 : syracuseStep 3 = 5 := stepEq 1 (by norm_num) (by decide)
theorem T5 : syracuseStep 5 = 1 := stepEq 4 (by norm_num) (by decide)

/-- A point of period dividing 3 that is odd, positive and below 7 must be `1`. -/
theorem small (y : ℕ) (hy : 0 < y) (hodd : Odd y) (hlt : y < 7)
    (hper : syracuseStep (syracuseStep (syracuseStep y)) = y) : y = 1 := by
  rw [Nat.odd_iff] at hodd
  interval_cases y
  · rfl
  · omega
  · rw [T3, T5, T1] at hper; omega
  · omega
  · rw [T5, T1, T1] at hper; omega
  · omega

theorem solution (m : ℕ) (hm : 0 < m) (hcyc : syracuseStep^[3] m = m) : m = 1 := by
  have hc : syracuseStep (syracuseStep (syracuseStep m)) = m := by
    have h : syracuseStep^[3] m = syracuseStep (syracuseStep (syracuseStep m)) := by
      simp [Function.iterate_succ_apply']
    rwa [h] at hcyc
  obtain ⟨x1, hx1⟩ : ∃ y, syracuseStep m = y := ⟨_, rfl⟩
  obtain ⟨x2, hx2⟩ : ∃ y, syracuseStep x1 = y := ⟨_, rfl⟩
  rw [hx1, hx2] at hc
  have hx1p : 0 < x1 := hx1 ▸ stepPos
  have hx2p : 0 < x2 := hx2 ▸ stepPos
  have hmo : Odd m := hc ▸ stepOdd x2
  have hx1o : Odd x1 := hx1 ▸ stepOdd m
  have hx2o : Odd x2 := hx2 ▸ stepOdd x1
  -- the three step relations
  obtain ⟨a0, e0⟩ : ∃ a, 2 ^ a * x1 = 3 * m + 1 := ⟨_, hx1 ▸ stepSplit m⟩
  obtain ⟨a1, e1⟩ : ∃ a, 2 ^ a * x2 = 3 * x1 + 1 := ⟨_, hx2 ▸ stepSplit x1⟩
  obtain ⟨a2, e2⟩ : ∃ a, 2 ^ a * m = 3 * x2 + 1 := ⟨_, hc ▸ stepSplit x2⟩
  have hP : 0 < m * x1 * x2 := by positivity
  have hprod : 2 ^ (a0 + a1 + a2) * (m * x1 * x2)
      = 27 * (m * x1 * x2) + 9 * (m * x1 + m * x2 + x1 * x2) + 3 * (m + x1 + x2) + 1 := by
    rw [pow_add, pow_add]
    calc 2 ^ a0 * 2 ^ a1 * 2 ^ a2 * (m * x1 * x2)
        = (2 ^ a0 * x1) * (2 ^ a1 * x2) * (2 ^ a2 * m) := by ring
      _ = (3 * m + 1) * (3 * x1 + 1) * (3 * x2 + 1) := by rw [e0, e1, e2]
      _ = 27 * (m * x1 * x2) + 9 * (m * x1 + m * x2 + x1 * x2) + 3 * (m + x1 + x2) + 1 := by
          ring
  -- 2 ^ K exceeds 27, hence is at least 32
  have h27 : 27 < 2 ^ (a0 + a1 + a2) := by
    by_contra h
    push Not at h
    have hle : 2 ^ (a0 + a1 + a2) * (m * x1 * x2) ≤ 27 * (m * x1 * x2) :=
      Nat.mul_le_mul_right _ h
    rw [hprod] at hle
    omega
  have h32 : 32 ≤ 2 ^ (a0 + a1 + a2) := by
    by_contra h
    push Not at h
    have : a0 + a1 + a2 ≤ 4 := by
      by_contra hk
      push Not at hk
      have : (32:ℕ) = 2 ^ 5 := by norm_num
      have : (2:ℕ) ^ 5 ≤ 2 ^ (a0 + a1 + a2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : (2:ℕ) ^ (a0 + a1 + a2) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) this
    norm_num at this
    omega
  have hkey : 5 * (m * x1 * x2)
      ≤ 9 * (m * x1 + m * x2 + x1 * x2) + 3 * (m + x1 + x2) + 1 := by
    have h1 : 32 * (m * x1 * x2) ≤ 2 ^ (a0 + a1 + a2) * (m * x1 * x2) :=
      Nat.mul_le_mul_right _ h32
    rw [hprod] at h1
    omega
  -- either some orbit point is below 7, or the inequality is violated
  rcases Nat.lt_or_ge m 7 with h | hm7
  · exact small m hm hmo h (by rw [hx1, hx2, hc])
  rcases Nat.lt_or_ge x1 7 with h | hx17
  · have : syracuseStep (syracuseStep (syracuseStep x1)) = x1 := by rw [hx2, hc, hx1]
    have h1 : x1 = 1 := small x1 hx1p hx1o h this
    have hx2' : x2 = 1 := by rw [← hx2, h1, T1]
    rw [hx2', T1] at hc
    omega
  rcases Nat.lt_or_ge x2 7 with h | hx27
  · have : syracuseStep (syracuseStep (syracuseStep x2)) = x2 := by rw [hc, hx1, hx2]
    have h2 : x2 = 1 := small x2 hx2p hx2o h this
    rw [h2, T1] at hc; omega
  · exfalso
    have p1 : 7 * (x1 * x2) ≤ m * x1 * x2 := by nlinarith
    have p2 : 7 * (m * x2) ≤ m * x1 * x2 := by nlinarith
    have p3 : 7 * (m * x1) ≤ m * x1 * x2 := by nlinarith
    have q1 : 49 * m ≤ m * x1 * x2 := by nlinarith
    have q2 : 49 * x1 ≤ m * x1 * x2 := by nlinarith
    have q3 : 49 * x2 ≤ m * x1 * x2 := by nlinarith
    have r : 343 ≤ m * x1 * x2 := by nlinarith
    linarith
