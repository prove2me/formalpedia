-- Prove2me | solution 1 for syracuse_small_reaches_one
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T20:50:31.410222+00:00
-- url     : https://prove2.me/submissions/87cbd61d-af4f-4367-bd18-ec1dc2c616d0

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

/-- One backward step of a convergence chain. -/
theorem reachStep {x y : ℕ} (h : syracuseStep x = y) (hy : ∃ j : ℕ, syracuseStep^[j] y = 1) :
    ∃ j : ℕ, syracuseStep^[j] x = 1 := by
  obtain ⟨j, hj⟩ := hy
  refine ⟨j + 1, ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_one, h]
  exact hj

theorem R1 : ∃ j : ℕ, syracuseStep^[j] 1 = 1 := ⟨0, rfl⟩

theorem S3 : syracuseStep 3 = 5 := stepEq 1 (by norm_num) (by decide)
theorem S5 : syracuseStep 5 = 1 := stepEq 4 (by norm_num) (by decide)
theorem S7 : syracuseStep 7 = 11 := stepEq 1 (by norm_num) (by decide)
theorem S9 : syracuseStep 9 = 7 := stepEq 2 (by norm_num) (by decide)
theorem S11 : syracuseStep 11 = 17 := stepEq 1 (by norm_num) (by decide)
theorem S13 : syracuseStep 13 = 5 := stepEq 3 (by norm_num) (by decide)
theorem S15 : syracuseStep 15 = 23 := stepEq 1 (by norm_num) (by decide)
theorem S17 : syracuseStep 17 = 13 := stepEq 2 (by norm_num) (by decide)
theorem S19 : syracuseStep 19 = 29 := stepEq 1 (by norm_num) (by decide)
theorem S21 : syracuseStep 21 = 1 := stepEq 6 (by norm_num) (by decide)
theorem S23 : syracuseStep 23 = 35 := stepEq 1 (by norm_num) (by decide)
theorem S25 : syracuseStep 25 = 19 := stepEq 2 (by norm_num) (by decide)
theorem S27 : syracuseStep 27 = 41 := stepEq 1 (by norm_num) (by decide)
theorem S29 : syracuseStep 29 = 11 := stepEq 3 (by norm_num) (by decide)
theorem S31 : syracuseStep 31 = 47 := stepEq 1 (by norm_num) (by decide)
theorem S33 : syracuseStep 33 = 25 := stepEq 2 (by norm_num) (by decide)
theorem S35 : syracuseStep 35 = 53 := stepEq 1 (by norm_num) (by decide)
theorem S41 : syracuseStep 41 = 31 := stepEq 2 (by norm_num) (by decide)
theorem S47 : syracuseStep 47 = 71 := stepEq 1 (by norm_num) (by decide)
theorem S53 : syracuseStep 53 = 5 := stepEq 5 (by norm_num) (by decide)
theorem S61 : syracuseStep 61 = 23 := stepEq 3 (by norm_num) (by decide)
theorem S71 : syracuseStep 71 = 107 := stepEq 1 (by norm_num) (by decide)
theorem S91 : syracuseStep 91 = 137 := stepEq 1 (by norm_num) (by decide)
theorem S103 : syracuseStep 103 = 155 := stepEq 1 (by norm_num) (by decide)
theorem S107 : syracuseStep 107 = 161 := stepEq 1 (by norm_num) (by decide)
theorem S121 : syracuseStep 121 = 91 := stepEq 2 (by norm_num) (by decide)
theorem S137 : syracuseStep 137 = 103 := stepEq 2 (by norm_num) (by decide)
theorem S155 : syracuseStep 155 = 233 := stepEq 1 (by norm_num) (by decide)
theorem S161 : syracuseStep 161 = 121 := stepEq 2 (by norm_num) (by decide)
theorem S167 : syracuseStep 167 = 251 := stepEq 1 (by norm_num) (by decide)
theorem S175 : syracuseStep 175 = 263 := stepEq 1 (by norm_num) (by decide)
theorem S233 : syracuseStep 233 = 175 := stepEq 2 (by norm_num) (by decide)
theorem S251 : syracuseStep 251 = 377 := stepEq 1 (by norm_num) (by decide)
theorem S263 : syracuseStep 263 = 395 := stepEq 1 (by norm_num) (by decide)
theorem S283 : syracuseStep 283 = 425 := stepEq 1 (by norm_num) (by decide)
theorem S319 : syracuseStep 319 = 479 := stepEq 1 (by norm_num) (by decide)
theorem S325 : syracuseStep 325 = 61 := stepEq 4 (by norm_num) (by decide)
theorem S377 : syracuseStep 377 = 283 := stepEq 2 (by norm_num) (by decide)
theorem S395 : syracuseStep 395 = 593 := stepEq 1 (by norm_num) (by decide)
theorem S425 : syracuseStep 425 = 319 := stepEq 2 (by norm_num) (by decide)
theorem S433 : syracuseStep 433 = 325 := stepEq 2 (by norm_num) (by decide)
theorem S445 : syracuseStep 445 = 167 := stepEq 3 (by norm_num) (by decide)
theorem S479 : syracuseStep 479 = 719 := stepEq 1 (by norm_num) (by decide)
theorem S577 : syracuseStep 577 = 433 := stepEq 2 (by norm_num) (by decide)
theorem S593 : syracuseStep 593 = 445 := stepEq 2 (by norm_num) (by decide)
theorem S719 : syracuseStep 719 = 1079 := stepEq 1 (by norm_num) (by decide)
theorem S911 : syracuseStep 911 = 1367 := stepEq 1 (by norm_num) (by decide)
theorem S1079 : syracuseStep 1079 = 1619 := stepEq 1 (by norm_num) (by decide)
theorem S1367 : syracuseStep 1367 = 2051 := stepEq 1 (by norm_num) (by decide)
theorem S1619 : syracuseStep 1619 = 2429 := stepEq 1 (by norm_num) (by decide)
theorem S2051 : syracuseStep 2051 = 3077 := stepEq 1 (by norm_num) (by decide)
theorem S2429 : syracuseStep 2429 = 911 := stepEq 3 (by norm_num) (by decide)
theorem S3077 : syracuseStep 3077 = 577 := stepEq 4 (by norm_num) (by decide)

theorem R5 : ∃ j : ℕ, syracuseStep^[j] 5 = 1 := reachStep S5 R1
theorem R21 : ∃ j : ℕ, syracuseStep^[j] 21 = 1 := reachStep S21 R1
theorem R3 : ∃ j : ℕ, syracuseStep^[j] 3 = 1 := reachStep S3 R5
theorem R13 : ∃ j : ℕ, syracuseStep^[j] 13 = 1 := reachStep S13 R5
theorem R53 : ∃ j : ℕ, syracuseStep^[j] 53 = 1 := reachStep S53 R5
theorem R17 : ∃ j : ℕ, syracuseStep^[j] 17 = 1 := reachStep S17 R13
theorem R35 : ∃ j : ℕ, syracuseStep^[j] 35 = 1 := reachStep S35 R53
theorem R11 : ∃ j : ℕ, syracuseStep^[j] 11 = 1 := reachStep S11 R17
theorem R23 : ∃ j : ℕ, syracuseStep^[j] 23 = 1 := reachStep S23 R35
theorem R7 : ∃ j : ℕ, syracuseStep^[j] 7 = 1 := reachStep S7 R11
theorem R15 : ∃ j : ℕ, syracuseStep^[j] 15 = 1 := reachStep S15 R23
theorem R29 : ∃ j : ℕ, syracuseStep^[j] 29 = 1 := reachStep S29 R11
theorem R61 : ∃ j : ℕ, syracuseStep^[j] 61 = 1 := reachStep S61 R23
theorem R9 : ∃ j : ℕ, syracuseStep^[j] 9 = 1 := reachStep S9 R7
theorem R19 : ∃ j : ℕ, syracuseStep^[j] 19 = 1 := reachStep S19 R29
theorem R325 : ∃ j : ℕ, syracuseStep^[j] 325 = 1 := reachStep S325 R61
theorem R25 : ∃ j : ℕ, syracuseStep^[j] 25 = 1 := reachStep S25 R19
theorem R433 : ∃ j : ℕ, syracuseStep^[j] 433 = 1 := reachStep S433 R325
theorem R577 : ∃ j : ℕ, syracuseStep^[j] 577 = 1 := reachStep S577 R433
theorem R33 : ∃ j : ℕ, syracuseStep^[j] 33 = 1 := reachStep S33 R25
theorem R3077 : ∃ j : ℕ, syracuseStep^[j] 3077 = 1 := reachStep S3077 R577
theorem R2051 : ∃ j : ℕ, syracuseStep^[j] 2051 = 1 := reachStep S2051 R3077
theorem R1367 : ∃ j : ℕ, syracuseStep^[j] 1367 = 1 := reachStep S1367 R2051
theorem R911 : ∃ j : ℕ, syracuseStep^[j] 911 = 1 := reachStep S911 R1367
theorem R2429 : ∃ j : ℕ, syracuseStep^[j] 2429 = 1 := reachStep S2429 R911
theorem R1619 : ∃ j : ℕ, syracuseStep^[j] 1619 = 1 := reachStep S1619 R2429
theorem R1079 : ∃ j : ℕ, syracuseStep^[j] 1079 = 1 := reachStep S1079 R1619
theorem R719 : ∃ j : ℕ, syracuseStep^[j] 719 = 1 := reachStep S719 R1079
theorem R479 : ∃ j : ℕ, syracuseStep^[j] 479 = 1 := reachStep S479 R719
theorem R319 : ∃ j : ℕ, syracuseStep^[j] 319 = 1 := reachStep S319 R479
theorem R425 : ∃ j : ℕ, syracuseStep^[j] 425 = 1 := reachStep S425 R319
theorem R283 : ∃ j : ℕ, syracuseStep^[j] 283 = 1 := reachStep S283 R425
theorem R377 : ∃ j : ℕ, syracuseStep^[j] 377 = 1 := reachStep S377 R283
theorem R251 : ∃ j : ℕ, syracuseStep^[j] 251 = 1 := reachStep S251 R377
theorem R167 : ∃ j : ℕ, syracuseStep^[j] 167 = 1 := reachStep S167 R251
theorem R445 : ∃ j : ℕ, syracuseStep^[j] 445 = 1 := reachStep S445 R167
theorem R593 : ∃ j : ℕ, syracuseStep^[j] 593 = 1 := reachStep S593 R445
theorem R395 : ∃ j : ℕ, syracuseStep^[j] 395 = 1 := reachStep S395 R593
theorem R263 : ∃ j : ℕ, syracuseStep^[j] 263 = 1 := reachStep S263 R395
theorem R175 : ∃ j : ℕ, syracuseStep^[j] 175 = 1 := reachStep S175 R263
theorem R233 : ∃ j : ℕ, syracuseStep^[j] 233 = 1 := reachStep S233 R175
theorem R155 : ∃ j : ℕ, syracuseStep^[j] 155 = 1 := reachStep S155 R233
theorem R103 : ∃ j : ℕ, syracuseStep^[j] 103 = 1 := reachStep S103 R155
theorem R137 : ∃ j : ℕ, syracuseStep^[j] 137 = 1 := reachStep S137 R103
theorem R91 : ∃ j : ℕ, syracuseStep^[j] 91 = 1 := reachStep S91 R137
theorem R121 : ∃ j : ℕ, syracuseStep^[j] 121 = 1 := reachStep S121 R91
theorem R161 : ∃ j : ℕ, syracuseStep^[j] 161 = 1 := reachStep S161 R121
theorem R107 : ∃ j : ℕ, syracuseStep^[j] 107 = 1 := reachStep S107 R161
theorem R71 : ∃ j : ℕ, syracuseStep^[j] 71 = 1 := reachStep S71 R107
theorem R47 : ∃ j : ℕ, syracuseStep^[j] 47 = 1 := reachStep S47 R71
theorem R31 : ∃ j : ℕ, syracuseStep^[j] 31 = 1 := reachStep S31 R47
theorem R41 : ∃ j : ℕ, syracuseStep^[j] 41 = 1 := reachStep S41 R31
theorem R27 : ∃ j : ℕ, syracuseStep^[j] 27 = 1 := reachStep S27 R41

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 33) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rw [Nat.odd_iff] at hodd
  interval_cases m
  · exact R1
  · omega
  · exact R3
  · omega
  · exact R5
  · omega
  · exact R7
  · omega
  · exact R9
  · omega
  · exact R11
  · omega
  · exact R13
  · omega
  · exact R15
  · omega
  · exact R17
  · omega
  · exact R19
  · omega
  · exact R21
  · omega
  · exact R23
  · omega
  · exact R25
  · omega
  · exact R27
  · omega
  · exact R29
  · omega
  · exact R31
  · omega
  · exact R33
