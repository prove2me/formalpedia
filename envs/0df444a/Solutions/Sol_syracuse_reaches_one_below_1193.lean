-- Prove2me | solution 1 for syracuse_reaches_one_below_1193
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T03:41:03.173104+00:00
-- url     : https://prove2.me/submissions/2cdefb47-4d67-49e8-a739-d3684910e500

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

theorem S5 : syracuseStep 5 = 1 := stepEq 4 (by norm_num) (by decide)
theorem R5 : ∃ j : ℕ, syracuseStep^[j] 5 = 1 := reachStep S5 R1
theorem S21 : syracuseStep 21 = 1 := stepEq 6 (by norm_num) (by decide)
theorem R21 : ∃ j : ℕ, syracuseStep^[j] 21 = 1 := reachStep S21 R1
theorem S85 : syracuseStep 85 = 1 := stepEq 8 (by norm_num) (by decide)
theorem R85 : ∃ j : ℕ, syracuseStep^[j] 85 = 1 := reachStep S85 R1
theorem S341 : syracuseStep 341 = 1 := stepEq 10 (by norm_num) (by decide)
theorem R341 : ∃ j : ℕ, syracuseStep^[j] 341 = 1 := reachStep S341 R1
theorem S3 : syracuseStep 3 = 5 := stepEq 1 (by norm_num) (by decide)
theorem R3 : ∃ j : ℕ, syracuseStep^[j] 3 = 1 := reachStep S3 R5
theorem S13 : syracuseStep 13 = 5 := stepEq 3 (by norm_num) (by decide)
theorem R13 : ∃ j : ℕ, syracuseStep^[j] 13 = 1 := reachStep S13 R5
theorem S53 : syracuseStep 53 = 5 := stepEq 5 (by norm_num) (by decide)
theorem R53 : ∃ j : ℕ, syracuseStep^[j] 53 = 1 := reachStep S53 R5
theorem S113 : syracuseStep 113 = 85 := stepEq 2 (by norm_num) (by decide)
theorem R113 : ∃ j : ℕ, syracuseStep^[j] 113 = 1 := reachStep S113 R85
theorem S213 : syracuseStep 213 = 5 := stepEq 7 (by norm_num) (by decide)
theorem R213 : ∃ j : ℕ, syracuseStep^[j] 213 = 1 := reachStep S213 R5
theorem S227 : syracuseStep 227 = 341 := stepEq 1 (by norm_num) (by decide)
theorem R227 : ∃ j : ℕ, syracuseStep^[j] 227 = 1 := reachStep S227 R341
theorem S453 : syracuseStep 453 = 85 := stepEq 4 (by norm_num) (by decide)
theorem R453 : ∃ j : ℕ, syracuseStep^[j] 453 = 1 := reachStep S453 R85
theorem S853 : syracuseStep 853 = 5 := stepEq 9 (by norm_num) (by decide)
theorem R853 : ∃ j : ℕ, syracuseStep^[j] 853 = 1 := reachStep S853 R5
theorem S909 : syracuseStep 909 = 341 := stepEq 3 (by norm_num) (by decide)
theorem R909 : ∃ j : ℕ, syracuseStep^[j] 909 = 1 := reachStep S909 R341
theorem S17 : syracuseStep 17 = 13 := stepEq 2 (by norm_num) (by decide)
theorem R17 : ∃ j : ℕ, syracuseStep^[j] 17 = 1 := reachStep S17 R13
theorem S35 : syracuseStep 35 = 53 := stepEq 1 (by norm_num) (by decide)
theorem R35 : ∃ j : ℕ, syracuseStep^[j] 35 = 1 := reachStep S35 R53
theorem S69 : syracuseStep 69 = 13 := stepEq 4 (by norm_num) (by decide)
theorem R69 : ∃ j : ℕ, syracuseStep^[j] 69 = 1 := reachStep S69 R13
theorem S75 : syracuseStep 75 = 113 := stepEq 1 (by norm_num) (by decide)
theorem R75 : ∃ j : ℕ, syracuseStep^[j] 75 = 1 := reachStep S75 R113
theorem S141 : syracuseStep 141 = 53 := stepEq 3 (by norm_num) (by decide)
theorem R141 : ∃ j : ℕ, syracuseStep^[j] 141 = 1 := reachStep S141 R53
theorem S151 : syracuseStep 151 = 227 := stepEq 1 (by norm_num) (by decide)
theorem R151 : ∃ j : ℕ, syracuseStep^[j] 151 = 1 := reachStep S151 R227
theorem S277 : syracuseStep 277 = 13 := stepEq 6 (by norm_num) (by decide)
theorem R277 : ∃ j : ℕ, syracuseStep^[j] 277 = 1 := reachStep S277 R13
theorem S301 : syracuseStep 301 = 113 := stepEq 3 (by norm_num) (by decide)
theorem R301 : ∃ j : ℕ, syracuseStep^[j] 301 = 1 := reachStep S301 R113
theorem S565 : syracuseStep 565 = 53 := stepEq 5 (by norm_num) (by decide)
theorem R565 : ∃ j : ℕ, syracuseStep^[j] 565 = 1 := reachStep S565 R53
theorem S605 : syracuseStep 605 = 227 := stepEq 3 (by norm_num) (by decide)
theorem R605 : ∃ j : ℕ, syracuseStep^[j] 605 = 1 := reachStep S605 R227
theorem S1109 : syracuseStep 1109 = 13 := stepEq 8 (by norm_num) (by decide)
theorem R1109 : ∃ j : ℕ, syracuseStep^[j] 1109 = 1 := reachStep S1109 R13
theorem S1137 : syracuseStep 1137 = 853 := stepEq 2 (by norm_num) (by decide)
theorem R1137 : ∃ j : ℕ, syracuseStep^[j] 1137 = 1 := reachStep S1137 R853
theorem S1205 : syracuseStep 1205 = 113 := stepEq 5 (by norm_num) (by decide)
theorem R1205 : ∃ j : ℕ, syracuseStep^[j] 1205 = 1 := reachStep S1205 R113
theorem S11 : syracuseStep 11 = 17 := stepEq 1 (by norm_num) (by decide)
theorem R11 : ∃ j : ℕ, syracuseStep^[j] 11 = 1 := reachStep S11 R17
theorem S23 : syracuseStep 23 = 35 := stepEq 1 (by norm_num) (by decide)
theorem R23 : ∃ j : ℕ, syracuseStep^[j] 23 = 1 := reachStep S23 R35
theorem S45 : syracuseStep 45 = 17 := stepEq 3 (by norm_num) (by decide)
theorem R45 : ∃ j : ℕ, syracuseStep^[j] 45 = 1 := reachStep S45 R17
theorem S93 : syracuseStep 93 = 35 := stepEq 3 (by norm_num) (by decide)
theorem R93 : ∃ j : ℕ, syracuseStep^[j] 93 = 1 := reachStep S93 R35
theorem S181 : syracuseStep 181 = 17 := stepEq 5 (by norm_num) (by decide)
theorem R181 : ∃ j : ℕ, syracuseStep^[j] 181 = 1 := reachStep S181 R17
theorem S201 : syracuseStep 201 = 151 := stepEq 2 (by norm_num) (by decide)
theorem R201 : ∃ j : ℕ, syracuseStep^[j] 201 = 1 := reachStep S201 R151
theorem S369 : syracuseStep 369 = 277 := stepEq 2 (by norm_num) (by decide)
theorem R369 : ∃ j : ℕ, syracuseStep^[j] 369 = 1 := reachStep S369 R277
theorem S373 : syracuseStep 373 = 35 := stepEq 5 (by norm_num) (by decide)
theorem R373 : ∃ j : ℕ, syracuseStep^[j] 373 = 1 := reachStep S373 R35
theorem S401 : syracuseStep 401 = 301 := stepEq 2 (by norm_num) (by decide)
theorem R401 : ∃ j : ℕ, syracuseStep^[j] 401 = 1 := reachStep S401 R301
theorem S403 : syracuseStep 403 = 605 := stepEq 1 (by norm_num) (by decide)
theorem R403 : ∃ j : ℕ, syracuseStep^[j] 403 = 1 := reachStep S403 R605
theorem S725 : syracuseStep 725 = 17 := stepEq 7 (by norm_num) (by decide)
theorem R725 : ∃ j : ℕ, syracuseStep^[j] 725 = 1 := reachStep S725 R17
theorem S739 : syracuseStep 739 = 1109 := stepEq 1 (by norm_num) (by decide)
theorem R739 : ∃ j : ℕ, syracuseStep^[j] 739 = 1 := reachStep S739 R1109
theorem S753 : syracuseStep 753 = 565 := stepEq 2 (by norm_num) (by decide)
theorem R753 : ∃ j : ℕ, syracuseStep^[j] 753 = 1 := reachStep S753 R565
theorem S803 : syracuseStep 803 = 1205 := stepEq 1 (by norm_num) (by decide)
theorem R803 : ∃ j : ℕ, syracuseStep^[j] 803 = 1 := reachStep S803 R1205
theorem S805 : syracuseStep 805 = 151 := stepEq 4 (by norm_num) (by decide)
theorem R805 : ∃ j : ℕ, syracuseStep^[j] 805 = 1 := reachStep S805 R151
theorem S1493 : syracuseStep 1493 = 35 := stepEq 7 (by norm_num) (by decide)
theorem R1493 : ∃ j : ℕ, syracuseStep^[j] 1493 = 1 := reachStep S1493 R35
theorem S1613 : syracuseStep 1613 = 605 := stepEq 3 (by norm_num) (by decide)
theorem R1613 : ∃ j : ℕ, syracuseStep^[j] 1613 = 1 := reachStep S1613 R605
theorem S7 : syracuseStep 7 = 11 := stepEq 1 (by norm_num) (by decide)
theorem R7 : ∃ j : ℕ, syracuseStep^[j] 7 = 1 := reachStep S7 R11
theorem S15 : syracuseStep 15 = 23 := stepEq 1 (by norm_num) (by decide)
theorem R15 : ∃ j : ℕ, syracuseStep^[j] 15 = 1 := reachStep S15 R23
theorem S29 : syracuseStep 29 = 11 := stepEq 3 (by norm_num) (by decide)
theorem R29 : ∃ j : ℕ, syracuseStep^[j] 29 = 1 := reachStep S29 R11
theorem S61 : syracuseStep 61 = 23 := stepEq 3 (by norm_num) (by decide)
theorem R61 : ∃ j : ℕ, syracuseStep^[j] 61 = 1 := reachStep S61 R23
theorem S2141 : syracuseStep 2141 = 803 := stepEq 3 (by norm_num) (by decide)
theorem R2141 : ∃ j : ℕ, syracuseStep^[j] 2141 = 1 := reachStep S2141 R803
theorem S117 : syracuseStep 117 = 11 := stepEq 5 (by norm_num) (by decide)
theorem R117 : ∃ j : ℕ, syracuseStep^[j] 117 = 1 := reachStep S117 R11
theorem S241 : syracuseStep 241 = 181 := stepEq 2 (by norm_num) (by decide)
theorem R241 : ∃ j : ℕ, syracuseStep^[j] 241 = 1 := reachStep S241 R181
theorem S245 : syracuseStep 245 = 23 := stepEq 5 (by norm_num) (by decide)
theorem R245 : ∃ j : ℕ, syracuseStep^[j] 245 = 1 := reachStep S245 R23
theorem S267 : syracuseStep 267 = 401 := stepEq 1 (by norm_num) (by decide)
theorem R267 : ∃ j : ℕ, syracuseStep^[j] 267 = 1 := reachStep S267 R401
theorem S469 : syracuseStep 469 = 11 := stepEq 7 (by norm_num) (by decide)
theorem R469 : ∃ j : ℕ, syracuseStep^[j] 469 = 1 := reachStep S469 R11
theorem S483 : syracuseStep 483 = 725 := stepEq 1 (by norm_num) (by decide)
theorem R483 : ∃ j : ℕ, syracuseStep^[j] 483 = 1 := reachStep S483 R725
theorem S497 : syracuseStep 497 = 373 := stepEq 2 (by norm_num) (by decide)
theorem R497 : ∃ j : ℕ, syracuseStep^[j] 497 = 1 := reachStep S497 R373
theorem S535 : syracuseStep 535 = 803 := stepEq 1 (by norm_num) (by decide)
theorem R535 : ∃ j : ℕ, syracuseStep^[j] 535 = 1 := reachStep S535 R803
theorem S537 : syracuseStep 537 = 403 := stepEq 2 (by norm_num) (by decide)
theorem R537 : ∃ j : ℕ, syracuseStep^[j] 537 = 1 := reachStep S537 R403
theorem S965 : syracuseStep 965 = 181 := stepEq 4 (by norm_num) (by decide)
theorem R965 : ∃ j : ℕ, syracuseStep^[j] 965 = 1 := reachStep S965 R181
theorem S981 : syracuseStep 981 = 23 := stepEq 7 (by norm_num) (by decide)
theorem R981 : ∃ j : ℕ, syracuseStep^[j] 981 = 1 := reachStep S981 R23
theorem S985 : syracuseStep 985 = 739 := stepEq 2 (by norm_num) (by decide)
theorem R985 : ∃ j : ℕ, syracuseStep^[j] 985 = 1 := reachStep S985 R739
theorem S995 : syracuseStep 995 = 1493 := stepEq 1 (by norm_num) (by decide)
theorem R995 : ∃ j : ℕ, syracuseStep^[j] 995 = 1 := reachStep S995 R1493
theorem S1069 : syracuseStep 1069 = 401 := stepEq 3 (by norm_num) (by decide)
theorem R1069 : ∃ j : ℕ, syracuseStep^[j] 1069 = 1 := reachStep S1069 R401
theorem S1073 : syracuseStep 1073 = 805 := stepEq 2 (by norm_num) (by decide)
theorem R1073 : ∃ j : ℕ, syracuseStep^[j] 1073 = 1 := reachStep S1073 R805
theorem S1075 : syracuseStep 1075 = 1613 := stepEq 1 (by norm_num) (by decide)
theorem R1075 : ∃ j : ℕ, syracuseStep^[j] 1075 = 1 := reachStep S1075 R1613
theorem S3941 : syracuseStep 3941 = 739 := stepEq 4 (by norm_num) (by decide)
theorem R3941 : ∃ j : ℕ, syracuseStep^[j] 3941 = 1 := reachStep S3941 R739
theorem S9 : syracuseStep 9 = 7 := stepEq 2 (by norm_num) (by decide)
theorem R9 : ∃ j : ℕ, syracuseStep^[j] 9 = 1 := reachStep S9 R7
theorem S19 : syracuseStep 19 = 29 := stepEq 1 (by norm_num) (by decide)
theorem R19 : ∃ j : ℕ, syracuseStep^[j] 19 = 1 := reachStep S19 R29
theorem S37 : syracuseStep 37 = 7 := stepEq 4 (by norm_num) (by decide)
theorem R37 : ∃ j : ℕ, syracuseStep^[j] 37 = 1 := reachStep S37 R7
theorem S77 : syracuseStep 77 = 29 := stepEq 3 (by norm_num) (by decide)
theorem R77 : ∃ j : ℕ, syracuseStep^[j] 77 = 1 := reachStep S77 R29
theorem S81 : syracuseStep 81 = 61 := stepEq 2 (by norm_num) (by decide)
theorem R81 : ∃ j : ℕ, syracuseStep^[j] 81 = 1 := reachStep S81 R61
theorem S149 : syracuseStep 149 = 7 := stepEq 6 (by norm_num) (by decide)
theorem R149 : ∃ j : ℕ, syracuseStep^[j] 149 = 1 := reachStep S149 R7
theorem S163 : syracuseStep 163 = 245 := stepEq 1 (by norm_num) (by decide)
theorem R163 : ∃ j : ℕ, syracuseStep^[j] 163 = 1 := reachStep S163 R245
theorem S309 : syracuseStep 309 = 29 := stepEq 5 (by norm_num) (by decide)
theorem R309 : ∃ j : ℕ, syracuseStep^[j] 309 = 1 := reachStep S309 R29
theorem S321 : syracuseStep 321 = 241 := stepEq 2 (by norm_num) (by decide)
theorem R321 : ∃ j : ℕ, syracuseStep^[j] 321 = 1 := reachStep S321 R241
theorem S325 : syracuseStep 325 = 61 := stepEq 4 (by norm_num) (by decide)
theorem R325 : ∃ j : ℕ, syracuseStep^[j] 325 = 1 := reachStep S325 R61
theorem S331 : syracuseStep 331 = 497 := stepEq 1 (by norm_num) (by decide)
theorem R331 : ∃ j : ℕ, syracuseStep^[j] 331 = 1 := reachStep S331 R497
theorem S2389 : syracuseStep 2389 = 7 := stepEq 10 (by norm_num) (by decide)
theorem R2389 : ∃ j : ℕ, syracuseStep^[j] 2389 = 1 := reachStep S2389 R7
theorem S2501 : syracuseStep 2501 = 469 := stepEq 4 (by norm_num) (by decide)
theorem R2501 : ∃ j : ℕ, syracuseStep^[j] 2501 = 1 := reachStep S2501 R469
theorem S2573 : syracuseStep 2573 = 965 := stepEq 3 (by norm_num) (by decide)
theorem R2573 : ∃ j : ℕ, syracuseStep^[j] 2573 = 1 := reachStep S2573 R965
theorem S2627 : syracuseStep 2627 = 3941 := stepEq 1 (by norm_num) (by decide)
theorem R2627 : ∃ j : ℕ, syracuseStep^[j] 2627 = 1 := reachStep S2627 R3941
theorem S597 : syracuseStep 597 = 7 := stepEq 8 (by norm_num) (by decide)
theorem R597 : ∃ j : ℕ, syracuseStep^[j] 597 = 1 := reachStep S597 R7
theorem S625 : syracuseStep 625 = 469 := stepEq 2 (by norm_num) (by decide)
theorem R625 : ∃ j : ℕ, syracuseStep^[j] 625 = 1 := reachStep S625 R469
theorem S643 : syracuseStep 643 = 965 := stepEq 1 (by norm_num) (by decide)
theorem R643 : ∃ j : ℕ, syracuseStep^[j] 643 = 1 := reachStep S643 R965
theorem S653 : syracuseStep 653 = 245 := stepEq 3 (by norm_num) (by decide)
theorem R653 : ∃ j : ℕ, syracuseStep^[j] 653 = 1 := reachStep S653 R245
theorem S663 : syracuseStep 663 = 995 := stepEq 1 (by norm_num) (by decide)
theorem R663 : ∃ j : ℕ, syracuseStep^[j] 663 = 1 := reachStep S663 R995
theorem S713 : syracuseStep 713 = 535 := stepEq 2 (by norm_num) (by decide)
theorem R713 : ∃ j : ℕ, syracuseStep^[j] 713 = 1 := reachStep S713 R535
theorem S715 : syracuseStep 715 = 1073 := stepEq 1 (by norm_num) (by decide)
theorem R715 : ∃ j : ℕ, syracuseStep^[j] 715 = 1 := reachStep S715 R1073
theorem S2861 : syracuseStep 2861 = 1073 := stepEq 3 (by norm_num) (by decide)
theorem R2861 : ∃ j : ℕ, syracuseStep^[j] 2861 = 1 := reachStep S2861 R1073
theorem S1237 : syracuseStep 1237 = 29 := stepEq 7 (by norm_num) (by decide)
theorem R1237 : ∃ j : ℕ, syracuseStep^[j] 1237 = 1 := reachStep S1237 R29
theorem S1301 : syracuseStep 1301 = 61 := stepEq 6 (by norm_num) (by decide)
theorem R1301 : ∃ j : ℕ, syracuseStep^[j] 1301 = 1 := reachStep S1301 R61
theorem S1313 : syracuseStep 1313 = 985 := stepEq 2 (by norm_num) (by decide)
theorem R1313 : ∃ j : ℕ, syracuseStep^[j] 1313 = 1 := reachStep S1313 R985
theorem S1325 : syracuseStep 1325 = 497 := stepEq 3 (by norm_num) (by decide)
theorem R1325 : ∃ j : ℕ, syracuseStep^[j] 1325 = 1 := reachStep S1325 R497
theorem S1427 : syracuseStep 1427 = 2141 := stepEq 1 (by norm_num) (by decide)
theorem R1427 : ∃ j : ℕ, syracuseStep^[j] 1427 = 1 := reachStep S1427 R2141
theorem S1433 : syracuseStep 1433 = 1075 := stepEq 2 (by norm_num) (by decide)
theorem R1433 : ∃ j : ℕ, syracuseStep^[j] 1433 = 1 := reachStep S1433 R1075
theorem S25 : syracuseStep 25 = 19 := stepEq 2 (by norm_num) (by decide)
theorem R25 : ∃ j : ℕ, syracuseStep^[j] 25 = 1 := reachStep S25 R19
theorem S49 : syracuseStep 49 = 37 := stepEq 2 (by norm_num) (by decide)
theorem R49 : ∃ j : ℕ, syracuseStep^[j] 49 = 1 := reachStep S49 R37
theorem S51 : syracuseStep 51 = 77 := stepEq 1 (by norm_num) (by decide)
theorem R51 : ∃ j : ℕ, syracuseStep^[j] 51 = 1 := reachStep S51 R77
theorem S99 : syracuseStep 99 = 149 := stepEq 1 (by norm_num) (by decide)
theorem R99 : ∃ j : ℕ, syracuseStep^[j] 99 = 1 := reachStep S99 R149
theorem S101 : syracuseStep 101 = 19 := stepEq 4 (by norm_num) (by decide)
theorem R101 : ∃ j : ℕ, syracuseStep^[j] 101 = 1 := reachStep S101 R19
theorem S197 : syracuseStep 197 = 37 := stepEq 4 (by norm_num) (by decide)
theorem R197 : ∃ j : ℕ, syracuseStep^[j] 197 = 1 := reachStep S197 R37
theorem S205 : syracuseStep 205 = 77 := stepEq 3 (by norm_num) (by decide)
theorem R205 : ∃ j : ℕ, syracuseStep^[j] 205 = 1 := reachStep S205 R77
theorem S217 : syracuseStep 217 = 163 := stepEq 2 (by norm_num) (by decide)
theorem R217 : ∃ j : ℕ, syracuseStep^[j] 217 = 1 := reachStep S217 R163
theorem S397 : syracuseStep 397 = 149 := stepEq 3 (by norm_num) (by decide)
theorem R397 : ∃ j : ℕ, syracuseStep^[j] 397 = 1 := reachStep S397 R149
theorem S405 : syracuseStep 405 = 19 := stepEq 6 (by norm_num) (by decide)
theorem R405 : ∃ j : ℕ, syracuseStep^[j] 405 = 1 := reachStep S405 R19
theorem S433 : syracuseStep 433 = 325 := stepEq 2 (by norm_num) (by decide)
theorem R433 : ∃ j : ℕ, syracuseStep^[j] 433 = 1 := reachStep S433 R325
theorem S435 : syracuseStep 435 = 653 := stepEq 1 (by norm_num) (by decide)
theorem R435 : ∃ j : ℕ, syracuseStep^[j] 435 = 1 := reachStep S435 R653
theorem S441 : syracuseStep 441 = 331 := stepEq 2 (by norm_num) (by decide)
theorem R441 : ∃ j : ℕ, syracuseStep^[j] 441 = 1 := reachStep S441 R331
theorem S475 : syracuseStep 475 = 713 := stepEq 1 (by norm_num) (by decide)
theorem R475 : ∃ j : ℕ, syracuseStep^[j] 475 = 1 := reachStep S475 R713
theorem S789 : syracuseStep 789 = 37 := stepEq 6 (by norm_num) (by decide)
theorem R789 : ∃ j : ℕ, syracuseStep^[j] 789 = 1 := reachStep S789 R37
theorem S821 : syracuseStep 821 = 77 := stepEq 5 (by norm_num) (by decide)
theorem R821 : ∃ j : ℕ, syracuseStep^[j] 821 = 1 := reachStep S821 R77
theorem S833 : syracuseStep 833 = 625 := stepEq 2 (by norm_num) (by decide)
theorem R833 : ∃ j : ℕ, syracuseStep^[j] 833 = 1 := reachStep S833 R625
theorem S857 : syracuseStep 857 = 643 := stepEq 2 (by norm_num) (by decide)
theorem R857 : ∃ j : ℕ, syracuseStep^[j] 857 = 1 := reachStep S857 R643
theorem S867 : syracuseStep 867 = 1301 := stepEq 1 (by norm_num) (by decide)
theorem R867 : ∃ j : ℕ, syracuseStep^[j] 867 = 1 := reachStep S867 R1301
theorem S869 : syracuseStep 869 = 163 := stepEq 4 (by norm_num) (by decide)
theorem R869 : ∃ j : ℕ, syracuseStep^[j] 869 = 1 := reachStep S869 R163
theorem S875 : syracuseStep 875 = 1313 := stepEq 1 (by norm_num) (by decide)
theorem R875 : ∃ j : ℕ, syracuseStep^[j] 875 = 1 := reachStep S875 R1313
theorem S883 : syracuseStep 883 = 1325 := stepEq 1 (by norm_num) (by decide)
theorem R883 : ∃ j : ℕ, syracuseStep^[j] 883 = 1 := reachStep S883 R1325
theorem S951 : syracuseStep 951 = 1427 := stepEq 1 (by norm_num) (by decide)
theorem R951 : ∃ j : ℕ, syracuseStep^[j] 951 = 1 := reachStep S951 R1427
theorem S953 : syracuseStep 953 = 715 := stepEq 2 (by norm_num) (by decide)
theorem R953 : ∃ j : ℕ, syracuseStep^[j] 953 = 1 := reachStep S953 R715
theorem S955 : syracuseStep 955 = 1433 := stepEq 1 (by norm_num) (by decide)
theorem R955 : ∃ j : ℕ, syracuseStep^[j] 955 = 1 := reachStep S955 R1433
theorem S3185 : syracuseStep 3185 = 2389 := stepEq 2 (by norm_num) (by decide)
theorem R3185 : ∃ j : ℕ, syracuseStep^[j] 3185 = 1 := reachStep S3185 R2389
theorem S1589 : syracuseStep 1589 = 149 := stepEq 5 (by norm_num) (by decide)
theorem R1589 : ∃ j : ℕ, syracuseStep^[j] 1589 = 1 := reachStep S1589 R149
theorem S1649 : syracuseStep 1649 = 1237 := stepEq 2 (by norm_num) (by decide)
theorem R1649 : ∃ j : ℕ, syracuseStep^[j] 1649 = 1 := reachStep S1649 R1237
theorem S1667 : syracuseStep 1667 = 2501 := stepEq 1 (by norm_num) (by decide)
theorem R1667 : ∃ j : ℕ, syracuseStep^[j] 1667 = 1 := reachStep S1667 R2501
theorem S1715 : syracuseStep 1715 = 2573 := stepEq 1 (by norm_num) (by decide)
theorem R1715 : ∃ j : ℕ, syracuseStep^[j] 1715 = 1 := reachStep S1715 R2573
theorem S1733 : syracuseStep 1733 = 325 := stepEq 4 (by norm_num) (by decide)
theorem R1733 : ∃ j : ℕ, syracuseStep^[j] 1733 = 1 := reachStep S1733 R325
theorem S1741 : syracuseStep 1741 = 653 := stepEq 3 (by norm_num) (by decide)
theorem R1741 : ∃ j : ℕ, syracuseStep^[j] 1741 = 1 := reachStep S1741 R653
theorem S1751 : syracuseStep 1751 = 2627 := stepEq 1 (by norm_num) (by decide)
theorem R1751 : ∃ j : ℕ, syracuseStep^[j] 1751 = 1 := reachStep S1751 R2627
theorem S1907 : syracuseStep 1907 = 2861 := stepEq 1 (by norm_num) (by decide)
theorem R1907 : ∃ j : ℕ, syracuseStep^[j] 1907 = 1 := reachStep S1907 R2861
theorem S33 : syracuseStep 33 = 25 := stepEq 2 (by norm_num) (by decide)
theorem R33 : ∃ j : ℕ, syracuseStep^[j] 33 = 1 := reachStep S33 R25
theorem S65 : syracuseStep 65 = 49 := stepEq 2 (by norm_num) (by decide)
theorem R65 : ∃ j : ℕ, syracuseStep^[j] 65 = 1 := reachStep S65 R49
theorem S67 : syracuseStep 67 = 101 := stepEq 1 (by norm_num) (by decide)
theorem R67 : ∃ j : ℕ, syracuseStep^[j] 67 = 1 := reachStep S67 R101
theorem S2123 : syracuseStep 2123 = 3185 := stepEq 1 (by norm_num) (by decide)
theorem R2123 : ∃ j : ℕ, syracuseStep^[j] 2123 = 1 := reachStep S2123 R3185
theorem S131 : syracuseStep 131 = 197 := stepEq 1 (by norm_num) (by decide)
theorem R131 : ∃ j : ℕ, syracuseStep^[j] 131 = 1 := reachStep S131 R197
theorem S133 : syracuseStep 133 = 25 := stepEq 4 (by norm_num) (by decide)
theorem R133 : ∃ j : ℕ, syracuseStep^[j] 133 = 1 := reachStep S133 R25
theorem S2285 : syracuseStep 2285 = 857 := stepEq 3 (by norm_num) (by decide)
theorem R2285 : ∃ j : ℕ, syracuseStep^[j] 2285 = 1 := reachStep S2285 R857
theorem S261 : syracuseStep 261 = 49 := stepEq 4 (by norm_num) (by decide)
theorem R261 : ∃ j : ℕ, syracuseStep^[j] 261 = 1 := reachStep S261 R49
theorem S269 : syracuseStep 269 = 101 := stepEq 3 (by norm_num) (by decide)
theorem R269 : ∃ j : ℕ, syracuseStep^[j] 269 = 1 := reachStep S269 R101
theorem S273 : syracuseStep 273 = 205 := stepEq 2 (by norm_num) (by decide)
theorem R273 : ∃ j : ℕ, syracuseStep^[j] 273 = 1 := reachStep S273 R205
theorem S2321 : syracuseStep 2321 = 1741 := stepEq 2 (by norm_num) (by decide)
theorem R2321 : ∃ j : ℕ, syracuseStep^[j] 2321 = 1 := reachStep S2321 R1741
theorem S4373 : syracuseStep 4373 = 205 := stepEq 6 (by norm_num) (by decide)
theorem R4373 : ∃ j : ℕ, syracuseStep^[j] 4373 = 1 := reachStep S4373 R205
theorem S289 : syracuseStep 289 = 217 := stepEq 2 (by norm_num) (by decide)
theorem R289 : ∃ j : ℕ, syracuseStep^[j] 289 = 1 := reachStep S289 R217
theorem S525 : syracuseStep 525 = 197 := stepEq 3 (by norm_num) (by decide)
theorem R525 : ∃ j : ℕ, syracuseStep^[j] 525 = 1 := reachStep S525 R197
theorem S529 : syracuseStep 529 = 397 := stepEq 2 (by norm_num) (by decide)
theorem R529 : ∃ j : ℕ, syracuseStep^[j] 529 = 1 := reachStep S529 R397
theorem S533 : syracuseStep 533 = 25 := stepEq 6 (by norm_num) (by decide)
theorem R533 : ∃ j : ℕ, syracuseStep^[j] 533 = 1 := reachStep S533 R25
theorem S547 : syracuseStep 547 = 821 := stepEq 1 (by norm_num) (by decide)
theorem R547 : ∃ j : ℕ, syracuseStep^[j] 547 = 1 := reachStep S547 R821
theorem S555 : syracuseStep 555 = 833 := stepEq 1 (by norm_num) (by decide)
theorem R555 : ∃ j : ℕ, syracuseStep^[j] 555 = 1 := reachStep S555 R833
theorem S571 : syracuseStep 571 = 857 := stepEq 1 (by norm_num) (by decide)
theorem R571 : ∃ j : ℕ, syracuseStep^[j] 571 = 1 := reachStep S571 R857
theorem S577 : syracuseStep 577 = 433 := stepEq 2 (by norm_num) (by decide)
theorem R577 : ∃ j : ℕ, syracuseStep^[j] 577 = 1 := reachStep S577 R433
theorem S579 : syracuseStep 579 = 869 := stepEq 1 (by norm_num) (by decide)
theorem R579 : ∃ j : ℕ, syracuseStep^[j] 579 = 1 := reachStep S579 R869
theorem S583 : syracuseStep 583 = 875 := stepEq 1 (by norm_num) (by decide)
theorem R583 : ∃ j : ℕ, syracuseStep^[j] 583 = 1 := reachStep S583 R875
theorem S633 : syracuseStep 633 = 475 := stepEq 2 (by norm_num) (by decide)
theorem R633 : ∃ j : ℕ, syracuseStep^[j] 633 = 1 := reachStep S633 R475
theorem S635 : syracuseStep 635 = 953 := stepEq 1 (by norm_num) (by decide)
theorem R635 : ∃ j : ℕ, syracuseStep^[j] 635 = 1 := reachStep S635 R953
theorem S5093 : syracuseStep 5093 = 955 := stepEq 4 (by norm_num) (by decide)
theorem R5093 : ∃ j : ℕ, syracuseStep^[j] 5093 = 1 := reachStep S5093 R955
theorem S1045 : syracuseStep 1045 = 49 := stepEq 6 (by norm_num) (by decide)
theorem R1045 : ∃ j : ℕ, syracuseStep^[j] 1045 = 1 := reachStep S1045 R49
theorem S1059 : syracuseStep 1059 = 1589 := stepEq 1 (by norm_num) (by decide)
theorem R1059 : ∃ j : ℕ, syracuseStep^[j] 1059 = 1 := reachStep S1059 R1589
theorem S1077 : syracuseStep 1077 = 101 := stepEq 5 (by norm_num) (by decide)
theorem R1077 : ∃ j : ℕ, syracuseStep^[j] 1077 = 1 := reachStep S1077 R101
theorem S1093 : syracuseStep 1093 = 205 := stepEq 4 (by norm_num) (by decide)
theorem R1093 : ∃ j : ℕ, syracuseStep^[j] 1093 = 1 := reachStep S1093 R205
theorem S1099 : syracuseStep 1099 = 1649 := stepEq 1 (by norm_num) (by decide)
theorem R1099 : ∃ j : ℕ, syracuseStep^[j] 1099 = 1 := reachStep S1099 R1649
theorem S1111 : syracuseStep 1111 = 1667 := stepEq 1 (by norm_num) (by decide)
theorem R1111 : ∃ j : ℕ, syracuseStep^[j] 1111 = 1 := reachStep S1111 R1667
theorem S1143 : syracuseStep 1143 = 1715 := stepEq 1 (by norm_num) (by decide)
theorem R1143 : ∃ j : ℕ, syracuseStep^[j] 1143 = 1 := reachStep S1143 R1715
theorem S1155 : syracuseStep 1155 = 1733 := stepEq 1 (by norm_num) (by decide)
theorem R1155 : ∃ j : ℕ, syracuseStep^[j] 1155 = 1 := reachStep S1155 R1733
theorem S1157 : syracuseStep 1157 = 217 := stepEq 4 (by norm_num) (by decide)
theorem R1157 : ∃ j : ℕ, syracuseStep^[j] 1157 = 1 := reachStep S1157 R217
theorem S1167 : syracuseStep 1167 = 1751 := stepEq 1 (by norm_num) (by decide)
theorem R1167 : ∃ j : ℕ, syracuseStep^[j] 1167 = 1 := reachStep S1167 R1751
theorem S1177 : syracuseStep 1177 = 883 := stepEq 2 (by norm_num) (by decide)
theorem R1177 : ∃ j : ℕ, syracuseStep^[j] 1177 = 1 := reachStep S1177 R883
theorem S1271 : syracuseStep 1271 = 1907 := stepEq 1 (by norm_num) (by decide)
theorem R1271 : ∃ j : ℕ, syracuseStep^[j] 1271 = 1 := reachStep S1271 R1907
theorem S1273 : syracuseStep 1273 = 955 := stepEq 2 (by norm_num) (by decide)
theorem R1273 : ∃ j : ℕ, syracuseStep^[j] 1273 = 1 := reachStep S1273 R955
theorem S43 : syracuseStep 43 = 65 := stepEq 1 (by norm_num) (by decide)
theorem R43 : ∃ j : ℕ, syracuseStep^[j] 43 = 1 := reachStep S43 R65
theorem S87 : syracuseStep 87 = 131 := stepEq 1 (by norm_num) (by decide)
theorem R87 : ∃ j : ℕ, syracuseStep^[j] 87 = 1 := reachStep S87 R131
theorem S89 : syracuseStep 89 = 67 := stepEq 2 (by norm_num) (by decide)
theorem R89 : ∃ j : ℕ, syracuseStep^[j] 89 = 1 := reachStep S89 R67
theorem S173 : syracuseStep 173 = 65 := stepEq 3 (by norm_num) (by decide)
theorem R173 : ∃ j : ℕ, syracuseStep^[j] 173 = 1 := reachStep S173 R65
theorem S177 : syracuseStep 177 = 133 := stepEq 2 (by norm_num) (by decide)
theorem R177 : ∃ j : ℕ, syracuseStep^[j] 177 = 1 := reachStep S177 R133
theorem S179 : syracuseStep 179 = 269 := stepEq 1 (by norm_num) (by decide)
theorem R179 : ∃ j : ℕ, syracuseStep^[j] 179 = 1 := reachStep S179 R269
theorem S349 : syracuseStep 349 = 131 := stepEq 3 (by norm_num) (by decide)
theorem R349 : ∃ j : ℕ, syracuseStep^[j] 349 = 1 := reachStep S349 R131
theorem S355 : syracuseStep 355 = 533 := stepEq 1 (by norm_num) (by decide)
theorem R355 : ∃ j : ℕ, syracuseStep^[j] 355 = 1 := reachStep S355 R533
theorem S357 : syracuseStep 357 = 67 := stepEq 4 (by norm_num) (by decide)
theorem R357 : ∃ j : ℕ, syracuseStep^[j] 357 = 1 := reachStep S357 R67
theorem S385 : syracuseStep 385 = 289 := stepEq 2 (by norm_num) (by decide)
theorem R385 : ∃ j : ℕ, syracuseStep^[j] 385 = 1 := reachStep S385 R289
theorem S423 : syracuseStep 423 = 635 := stepEq 1 (by norm_num) (by decide)
theorem R423 : ∃ j : ℕ, syracuseStep^[j] 423 = 1 := reachStep S423 R635
theorem S693 : syracuseStep 693 = 65 := stepEq 5 (by norm_num) (by decide)
theorem R693 : ∃ j : ℕ, syracuseStep^[j] 693 = 1 := reachStep S693 R65
theorem S705 : syracuseStep 705 = 529 := stepEq 2 (by norm_num) (by decide)
theorem R705 : ∃ j : ℕ, syracuseStep^[j] 705 = 1 := reachStep S705 R529
theorem S709 : syracuseStep 709 = 133 := stepEq 4 (by norm_num) (by decide)
theorem R709 : ∃ j : ℕ, syracuseStep^[j] 709 = 1 := reachStep S709 R133
theorem S717 : syracuseStep 717 = 269 := stepEq 3 (by norm_num) (by decide)
theorem R717 : ∃ j : ℕ, syracuseStep^[j] 717 = 1 := reachStep S717 R269
theorem S729 : syracuseStep 729 = 547 := stepEq 2 (by norm_num) (by decide)
theorem R729 : ∃ j : ℕ, syracuseStep^[j] 729 = 1 := reachStep S729 R547
theorem S761 : syracuseStep 761 = 571 := stepEq 2 (by norm_num) (by decide)
theorem R761 : ∃ j : ℕ, syracuseStep^[j] 761 = 1 := reachStep S761 R571
theorem S769 : syracuseStep 769 = 577 := stepEq 2 (by norm_num) (by decide)
theorem R769 : ∃ j : ℕ, syracuseStep^[j] 769 = 1 := reachStep S769 R577
theorem S771 : syracuseStep 771 = 1157 := stepEq 1 (by norm_num) (by decide)
theorem R771 : ∃ j : ℕ, syracuseStep^[j] 771 = 1 := reachStep S771 R1157
theorem S777 : syracuseStep 777 = 583 := stepEq 2 (by norm_num) (by decide)
theorem R777 : ∃ j : ℕ, syracuseStep^[j] 777 = 1 := reachStep S777 R583
theorem S2837 : syracuseStep 2837 = 133 := stepEq 6 (by norm_num) (by decide)
theorem R2837 : ∃ j : ℕ, syracuseStep^[j] 2837 = 1 := reachStep S2837 R133
theorem S847 : syracuseStep 847 = 1271 := stepEq 1 (by norm_num) (by decide)
theorem R847 : ∃ j : ℕ, syracuseStep^[j] 847 = 1 := reachStep S847 R1271
theorem S2915 : syracuseStep 2915 = 4373 := stepEq 1 (by norm_num) (by decide)
theorem R2915 : ∃ j : ℕ, syracuseStep^[j] 2915 = 1 := reachStep S2915 R4373
theorem S3077 : syracuseStep 3077 = 577 := stepEq 4 (by norm_num) (by decide)
theorem R3077 : ∃ j : ℕ, syracuseStep^[j] 3077 = 1 := reachStep S3077 R577
theorem S3395 : syracuseStep 3395 = 5093 := stepEq 1 (by norm_num) (by decide)
theorem R3395 : ∃ j : ℕ, syracuseStep^[j] 3395 = 1 := reachStep S3395 R5093
theorem S1397 : syracuseStep 1397 = 131 := stepEq 5 (by norm_num) (by decide)
theorem R1397 : ∃ j : ℕ, syracuseStep^[j] 1397 = 1 := reachStep S1397 R131
theorem S1415 : syracuseStep 1415 = 2123 := stepEq 1 (by norm_num) (by decide)
theorem R1415 : ∃ j : ℕ, syracuseStep^[j] 1415 = 1 := reachStep S1415 R2123
theorem S1421 : syracuseStep 1421 = 533 := stepEq 3 (by norm_num) (by decide)
theorem R1421 : ∃ j : ℕ, syracuseStep^[j] 1421 = 1 := reachStep S1421 R533
theorem S1457 : syracuseStep 1457 = 1093 := stepEq 2 (by norm_num) (by decide)
theorem R1457 : ∃ j : ℕ, syracuseStep^[j] 1457 = 1 := reachStep S1457 R1093
theorem S1481 : syracuseStep 1481 = 1111 := stepEq 2 (by norm_num) (by decide)
theorem R1481 : ∃ j : ℕ, syracuseStep^[j] 1481 = 1 := reachStep S1481 R1111
theorem S1523 : syracuseStep 1523 = 2285 := stepEq 1 (by norm_num) (by decide)
theorem R1523 : ∃ j : ℕ, syracuseStep^[j] 1523 = 1 := reachStep S1523 R2285
theorem S1541 : syracuseStep 1541 = 289 := stepEq 4 (by norm_num) (by decide)
theorem R1541 : ∃ j : ℕ, syracuseStep^[j] 1541 = 1 := reachStep S1541 R289
theorem S1547 : syracuseStep 1547 = 2321 := stepEq 1 (by norm_num) (by decide)
theorem R1547 : ∃ j : ℕ, syracuseStep^[j] 1547 = 1 := reachStep S1547 R2321
theorem S1697 : syracuseStep 1697 = 1273 := stepEq 2 (by norm_num) (by decide)
theorem R1697 : ∃ j : ℕ, syracuseStep^[j] 1697 = 1 := reachStep S1697 R1273
theorem S2051 : syracuseStep 2051 = 3077 := stepEq 1 (by norm_num) (by decide)
theorem R2051 : ∃ j : ℕ, syracuseStep^[j] 2051 = 1 := reachStep S2051 R3077
theorem S57 : syracuseStep 57 = 43 := stepEq 2 (by norm_num) (by decide)
theorem R57 : ∃ j : ℕ, syracuseStep^[j] 57 = 1 := reachStep S57 R43
theorem S59 : syracuseStep 59 = 89 := stepEq 1 (by norm_num) (by decide)
theorem R59 : ∃ j : ℕ, syracuseStep^[j] 59 = 1 := reachStep S59 R89
theorem S115 : syracuseStep 115 = 173 := stepEq 1 (by norm_num) (by decide)
theorem R115 : ∃ j : ℕ, syracuseStep^[j] 115 = 1 := reachStep S115 R173
theorem S119 : syracuseStep 119 = 179 := stepEq 1 (by norm_num) (by decide)
theorem R119 : ∃ j : ℕ, syracuseStep^[j] 119 = 1 := reachStep S119 R179
theorem S2263 : syracuseStep 2263 = 3395 := stepEq 1 (by norm_num) (by decide)
theorem R2263 : ∃ j : ℕ, syracuseStep^[j] 2263 = 1 := reachStep S2263 R3395
theorem S229 : syracuseStep 229 = 43 := stepEq 4 (by norm_num) (by decide)
theorem R229 : ∃ j : ℕ, syracuseStep^[j] 229 = 1 := reachStep S229 R43
theorem S237 : syracuseStep 237 = 89 := stepEq 3 (by norm_num) (by decide)
theorem R237 : ∃ j : ℕ, syracuseStep^[j] 237 = 1 := reachStep S237 R89
theorem S461 : syracuseStep 461 = 173 := stepEq 3 (by norm_num) (by decide)
theorem R461 : ∃ j : ℕ, syracuseStep^[j] 461 = 1 := reachStep S461 R173
theorem S465 : syracuseStep 465 = 349 := stepEq 2 (by norm_num) (by decide)
theorem R465 : ∃ j : ℕ, syracuseStep^[j] 465 = 1 := reachStep S465 R349
theorem S473 : syracuseStep 473 = 355 := stepEq 2 (by norm_num) (by decide)
theorem R473 : ∃ j : ℕ, syracuseStep^[j] 473 = 1 := reachStep S473 R355
theorem S477 : syracuseStep 477 = 179 := stepEq 3 (by norm_num) (by decide)
theorem R477 : ∃ j : ℕ, syracuseStep^[j] 477 = 1 := reachStep S477 R179
theorem S507 : syracuseStep 507 = 761 := stepEq 1 (by norm_num) (by decide)
theorem R507 : ∃ j : ℕ, syracuseStep^[j] 507 = 1 := reachStep S507 R761
theorem S513 : syracuseStep 513 = 385 := stepEq 2 (by norm_num) (by decide)
theorem R513 : ∃ j : ℕ, syracuseStep^[j] 513 = 1 := reachStep S513 R385
theorem S917 : syracuseStep 917 = 43 := stepEq 6 (by norm_num) (by decide)
theorem R917 : ∃ j : ℕ, syracuseStep^[j] 917 = 1 := reachStep S917 R43
theorem S931 : syracuseStep 931 = 1397 := stepEq 1 (by norm_num) (by decide)
theorem R931 : ∃ j : ℕ, syracuseStep^[j] 931 = 1 := reachStep S931 R1397
theorem S943 : syracuseStep 943 = 1415 := stepEq 1 (by norm_num) (by decide)
theorem R943 : ∃ j : ℕ, syracuseStep^[j] 943 = 1 := reachStep S943 R1415
theorem S945 : syracuseStep 945 = 709 := stepEq 2 (by norm_num) (by decide)
theorem R945 : ∃ j : ℕ, syracuseStep^[j] 945 = 1 := reachStep S945 R709
theorem S947 : syracuseStep 947 = 1421 := stepEq 1 (by norm_num) (by decide)
theorem R947 : ∃ j : ℕ, syracuseStep^[j] 947 = 1 := reachStep S947 R1421
theorem S949 : syracuseStep 949 = 89 := stepEq 5 (by norm_num) (by decide)
theorem R949 : ∃ j : ℕ, syracuseStep^[j] 949 = 1 := reachStep S949 R89
theorem S971 : syracuseStep 971 = 1457 := stepEq 1 (by norm_num) (by decide)
theorem R971 : ∃ j : ℕ, syracuseStep^[j] 971 = 1 := reachStep S971 R1457
theorem S987 : syracuseStep 987 = 1481 := stepEq 1 (by norm_num) (by decide)
theorem R987 : ∃ j : ℕ, syracuseStep^[j] 987 = 1 := reachStep S987 R1481
theorem S1015 : syracuseStep 1015 = 1523 := stepEq 1 (by norm_num) (by decide)
theorem R1015 : ∃ j : ℕ, syracuseStep^[j] 1015 = 1 := reachStep S1015 R1523
theorem S1025 : syracuseStep 1025 = 769 := stepEq 2 (by norm_num) (by decide)
theorem R1025 : ∃ j : ℕ, syracuseStep^[j] 1025 = 1 := reachStep S1025 R769
theorem S1027 : syracuseStep 1027 = 1541 := stepEq 1 (by norm_num) (by decide)
theorem R1027 : ∃ j : ℕ, syracuseStep^[j] 1027 = 1 := reachStep S1027 R1541
theorem S1031 : syracuseStep 1031 = 1547 := stepEq 1 (by norm_num) (by decide)
theorem R1031 : ∃ j : ℕ, syracuseStep^[j] 1031 = 1 := reachStep S1031 R1547
theorem S1129 : syracuseStep 1129 = 847 := stepEq 2 (by norm_num) (by decide)
theorem R1129 : ∃ j : ℕ, syracuseStep^[j] 1129 = 1 := reachStep S1129 R847
theorem S1131 : syracuseStep 1131 = 1697 := stepEq 1 (by norm_num) (by decide)
theorem R1131 : ∃ j : ℕ, syracuseStep^[j] 1131 = 1 := reachStep S1131 R1697
theorem S7381 : syracuseStep 7381 = 173 := stepEq 7 (by norm_num) (by decide)
theorem R7381 : ∃ j : ℕ, syracuseStep^[j] 7381 = 1 := reachStep S7381 R173
theorem S3725 : syracuseStep 3725 = 1397 := stepEq 3 (by norm_num) (by decide)
theorem R3725 : ∃ j : ℕ, syracuseStep^[j] 3725 = 1 := reachStep S3725 R1397
theorem S3797 : syracuseStep 3797 = 89 := stepEq 7 (by norm_num) (by decide)
theorem R3797 : ∃ j : ℕ, syracuseStep^[j] 3797 = 1 := reachStep S3797 R89
theorem S1891 : syracuseStep 1891 = 2837 := stepEq 1 (by norm_num) (by decide)
theorem R1891 : ∃ j : ℕ, syracuseStep^[j] 1891 = 1 := reachStep S1891 R2837
theorem S1943 : syracuseStep 1943 = 2915 := stepEq 1 (by norm_num) (by decide)
theorem R1943 : ∃ j : ℕ, syracuseStep^[j] 1943 = 1 := reachStep S1943 R2915
theorem S39 : syracuseStep 39 = 59 := stepEq 1 (by norm_num) (by decide)
theorem R39 : ∃ j : ℕ, syracuseStep^[j] 39 = 1 := reachStep S39 R59
theorem S79 : syracuseStep 79 = 119 := stepEq 1 (by norm_num) (by decide)
theorem R79 : ∃ j : ℕ, syracuseStep^[j] 79 = 1 := reachStep S79 R119
theorem S153 : syracuseStep 153 = 115 := stepEq 2 (by norm_num) (by decide)
theorem R153 : ∃ j : ℕ, syracuseStep^[j] 153 = 1 := reachStep S153 R115
theorem S157 : syracuseStep 157 = 59 := stepEq 3 (by norm_num) (by decide)
theorem R157 : ∃ j : ℕ, syracuseStep^[j] 157 = 1 := reachStep S157 R59
theorem S305 : syracuseStep 305 = 229 := stepEq 2 (by norm_num) (by decide)
theorem R305 : ∃ j : ℕ, syracuseStep^[j] 305 = 1 := reachStep S305 R229
theorem S307 : syracuseStep 307 = 461 := stepEq 1 (by norm_num) (by decide)
theorem R307 : ∃ j : ℕ, syracuseStep^[j] 307 = 1 := reachStep S307 R461
theorem S315 : syracuseStep 315 = 473 := stepEq 1 (by norm_num) (by decide)
theorem R315 : ∃ j : ℕ, syracuseStep^[j] 315 = 1 := reachStep S315 R473
theorem S317 : syracuseStep 317 = 119 := stepEq 3 (by norm_num) (by decide)
theorem R317 : ∃ j : ℕ, syracuseStep^[j] 317 = 1 := reachStep S317 R119
theorem S2483 : syracuseStep 2483 = 3725 := stepEq 1 (by norm_num) (by decide)
theorem R2483 : ∃ j : ℕ, syracuseStep^[j] 2483 = 1 := reachStep S2483 R3725
theorem S39365 : syracuseStep 39365 = 7381 := stepEq 4 (by norm_num) (by decide)
theorem R39365 : ∃ j : ℕ, syracuseStep^[j] 39365 = 1 := reachStep S39365 R7381
theorem S2521 : syracuseStep 2521 = 1891 := stepEq 2 (by norm_num) (by decide)
theorem R2521 : ∃ j : ℕ, syracuseStep^[j] 2521 = 1 := reachStep S2521 R1891
theorem S2531 : syracuseStep 2531 = 3797 := stepEq 1 (by norm_num) (by decide)
theorem R2531 : ∃ j : ℕ, syracuseStep^[j] 2531 = 1 := reachStep S2531 R3797
theorem S611 : syracuseStep 611 = 917 := stepEq 1 (by norm_num) (by decide)
theorem R611 : ∃ j : ℕ, syracuseStep^[j] 611 = 1 := reachStep S611 R917
theorem S613 : syracuseStep 613 = 115 := stepEq 4 (by norm_num) (by decide)
theorem R613 : ∃ j : ℕ, syracuseStep^[j] 613 = 1 := reachStep S613 R115
theorem S629 : syracuseStep 629 = 59 := stepEq 5 (by norm_num) (by decide)
theorem R629 : ∃ j : ℕ, syracuseStep^[j] 629 = 1 := reachStep S629 R59
theorem S631 : syracuseStep 631 = 947 := stepEq 1 (by norm_num) (by decide)
theorem R631 : ∃ j : ℕ, syracuseStep^[j] 631 = 1 := reachStep S631 R947
theorem S647 : syracuseStep 647 = 971 := stepEq 1 (by norm_num) (by decide)
theorem R647 : ∃ j : ℕ, syracuseStep^[j] 647 = 1 := reachStep S647 R971
theorem S683 : syracuseStep 683 = 1025 := stepEq 1 (by norm_num) (by decide)
theorem R683 : ∃ j : ℕ, syracuseStep^[j] 683 = 1 := reachStep S683 R1025
theorem S687 : syracuseStep 687 = 1031 := stepEq 1 (by norm_num) (by decide)
theorem R687 : ∃ j : ℕ, syracuseStep^[j] 687 = 1 := reachStep S687 R1031
theorem S3017 : syracuseStep 3017 = 2263 := stepEq 2 (by norm_num) (by decide)
theorem R3017 : ∃ j : ℕ, syracuseStep^[j] 3017 = 1 := reachStep S3017 R2263
theorem S1229 : syracuseStep 1229 = 461 := stepEq 3 (by norm_num) (by decide)
theorem R1229 : ∃ j : ℕ, syracuseStep^[j] 1229 = 1 := reachStep S1229 R461
theorem S1241 : syracuseStep 1241 = 931 := stepEq 2 (by norm_num) (by decide)
theorem R1241 : ∃ j : ℕ, syracuseStep^[j] 1241 = 1 := reachStep S1241 R931
theorem S1265 : syracuseStep 1265 = 949 := stepEq 2 (by norm_num) (by decide)
theorem R1265 : ∃ j : ℕ, syracuseStep^[j] 1265 = 1 := reachStep S1265 R949
theorem S1295 : syracuseStep 1295 = 1943 := stepEq 1 (by norm_num) (by decide)
theorem R1295 : ∃ j : ℕ, syracuseStep^[j] 1295 = 1 := reachStep S1295 R1943
theorem S1367 : syracuseStep 1367 = 2051 := stepEq 1 (by norm_num) (by decide)
theorem R1367 : ∃ j : ℕ, syracuseStep^[j] 1367 = 1 := reachStep S1367 R2051
theorem S1505 : syracuseStep 1505 = 1129 := stepEq 2 (by norm_num) (by decide)
theorem R1505 : ∃ j : ℕ, syracuseStep^[j] 1505 = 1 := reachStep S1505 R1129
theorem S9841 : syracuseStep 9841 = 7381 := stepEq 2 (by norm_num) (by decide)
theorem R9841 : ∃ j : ℕ, syracuseStep^[j] 9841 = 1 := reachStep S9841 R7381
theorem S105 : syracuseStep 105 = 79 := stepEq 2 (by norm_num) (by decide)
theorem R105 : ∃ j : ℕ, syracuseStep^[j] 105 = 1 := reachStep S105 R79
theorem S203 : syracuseStep 203 = 305 := stepEq 1 (by norm_num) (by decide)
theorem R203 : ∃ j : ℕ, syracuseStep^[j] 203 = 1 := reachStep S203 R305
theorem S209 : syracuseStep 209 = 157 := stepEq 2 (by norm_num) (by decide)
theorem R209 : ∃ j : ℕ, syracuseStep^[j] 209 = 1 := reachStep S209 R157
theorem S211 : syracuseStep 211 = 317 := stepEq 1 (by norm_num) (by decide)
theorem R211 : ∃ j : ℕ, syracuseStep^[j] 211 = 1 := reachStep S211 R317
theorem S407 : syracuseStep 407 = 611 := stepEq 1 (by norm_num) (by decide)
theorem R407 : ∃ j : ℕ, syracuseStep^[j] 407 = 1 := reachStep S407 R611
theorem S409 : syracuseStep 409 = 307 := stepEq 2 (by norm_num) (by decide)
theorem R409 : ∃ j : ℕ, syracuseStep^[j] 409 = 1 := reachStep S409 R307
theorem S419 : syracuseStep 419 = 629 := stepEq 1 (by norm_num) (by decide)
theorem R419 : ∃ j : ℕ, syracuseStep^[j] 419 = 1 := reachStep S419 R629
theorem S421 : syracuseStep 421 = 79 := stepEq 4 (by norm_num) (by decide)
theorem R421 : ∃ j : ℕ, syracuseStep^[j] 421 = 1 := reachStep S421 R79
theorem S431 : syracuseStep 431 = 647 := stepEq 1 (by norm_num) (by decide)
theorem R431 : ∃ j : ℕ, syracuseStep^[j] 431 = 1 := reachStep S431 R647
theorem S455 : syracuseStep 455 = 683 := stepEq 1 (by norm_num) (by decide)
theorem R455 : ∃ j : ℕ, syracuseStep^[j] 455 = 1 := reachStep S455 R683
theorem S813 : syracuseStep 813 = 305 := stepEq 3 (by norm_num) (by decide)
theorem R813 : ∃ j : ℕ, syracuseStep^[j] 813 = 1 := reachStep S813 R305
theorem S817 : syracuseStep 817 = 613 := stepEq 2 (by norm_num) (by decide)
theorem R817 : ∃ j : ℕ, syracuseStep^[j] 817 = 1 := reachStep S817 R613
theorem S819 : syracuseStep 819 = 1229 := stepEq 1 (by norm_num) (by decide)
theorem R819 : ∃ j : ℕ, syracuseStep^[j] 819 = 1 := reachStep S819 R1229
theorem S827 : syracuseStep 827 = 1241 := stepEq 1 (by norm_num) (by decide)
theorem R827 : ∃ j : ℕ, syracuseStep^[j] 827 = 1 := reachStep S827 R1241
theorem S13121 : syracuseStep 13121 = 9841 := stepEq 2 (by norm_num) (by decide)
theorem R13121 : ∃ j : ℕ, syracuseStep^[j] 13121 = 1 := reachStep S13121 R9841
theorem S837 : syracuseStep 837 = 157 := stepEq 4 (by norm_num) (by decide)
theorem R837 : ∃ j : ℕ, syracuseStep^[j] 837 = 1 := reachStep S837 R157
theorem S841 : syracuseStep 841 = 631 := stepEq 2 (by norm_num) (by decide)
theorem R841 : ∃ j : ℕ, syracuseStep^[j] 841 = 1 := reachStep S841 R631
theorem S843 : syracuseStep 843 = 1265 := stepEq 1 (by norm_num) (by decide)
theorem R843 : ∃ j : ℕ, syracuseStep^[j] 843 = 1 := reachStep S843 R1265
theorem S845 : syracuseStep 845 = 317 := stepEq 3 (by norm_num) (by decide)
theorem R845 : ∃ j : ℕ, syracuseStep^[j] 845 = 1 := reachStep S845 R317
theorem S863 : syracuseStep 863 = 1295 := stepEq 1 (by norm_num) (by decide)
theorem R863 : ∃ j : ℕ, syracuseStep^[j] 863 = 1 := reachStep S863 R1295
theorem S911 : syracuseStep 911 = 1367 := stepEq 1 (by norm_num) (by decide)
theorem R911 : ∃ j : ℕ, syracuseStep^[j] 911 = 1 := reachStep S911 R1367
theorem S1003 : syracuseStep 1003 = 1505 := stepEq 1 (by norm_num) (by decide)
theorem R1003 : ∃ j : ℕ, syracuseStep^[j] 1003 = 1 := reachStep S1003 R1505
theorem S3349 : syracuseStep 3349 = 157 := stepEq 6 (by norm_num) (by decide)
theorem R3349 : ∃ j : ℕ, syracuseStep^[j] 3349 = 1 := reachStep S3349 R157
theorem S3361 : syracuseStep 3361 = 2521 := stepEq 2 (by norm_num) (by decide)
theorem R3361 : ∃ j : ℕ, syracuseStep^[j] 3361 = 1 := reachStep S3361 R2521
theorem S1637 : syracuseStep 1637 = 307 := stepEq 4 (by norm_num) (by decide)
theorem R1637 : ∃ j : ℕ, syracuseStep^[j] 1637 = 1 := reachStep S1637 R307
theorem S1655 : syracuseStep 1655 = 2483 := stepEq 1 (by norm_num) (by decide)
theorem R1655 : ∃ j : ℕ, syracuseStep^[j] 1655 = 1 := reachStep S1655 R2483
theorem S26243 : syracuseStep 26243 = 39365 := stepEq 1 (by norm_num) (by decide)
theorem R26243 : ∃ j : ℕ, syracuseStep^[j] 26243 = 1 := reachStep S26243 R39365
theorem S1685 : syracuseStep 1685 = 79 := stepEq 6 (by norm_num) (by decide)
theorem R1685 : ∃ j : ℕ, syracuseStep^[j] 1685 = 1 := reachStep S1685 R79
theorem S1687 : syracuseStep 1687 = 2531 := stepEq 1 (by norm_num) (by decide)
theorem R1687 : ∃ j : ℕ, syracuseStep^[j] 1687 = 1 := reachStep S1687 R2531
theorem S2011 : syracuseStep 2011 = 3017 := stepEq 1 (by norm_num) (by decide)
theorem R2011 : ∃ j : ℕ, syracuseStep^[j] 2011 = 1 := reachStep S2011 R3017
theorem S135 : syracuseStep 135 = 203 := stepEq 1 (by norm_num) (by decide)
theorem R135 : ∃ j : ℕ, syracuseStep^[j] 135 = 1 := reachStep S135 R203
theorem S139 : syracuseStep 139 = 209 := stepEq 1 (by norm_num) (by decide)
theorem R139 : ∃ j : ℕ, syracuseStep^[j] 139 = 1 := reachStep S139 R209
theorem S2249 : syracuseStep 2249 = 1687 := stepEq 2 (by norm_num) (by decide)
theorem R2249 : ∃ j : ℕ, syracuseStep^[j] 2249 = 1 := reachStep S2249 R1687
theorem S271 : syracuseStep 271 = 407 := stepEq 1 (by norm_num) (by decide)
theorem R271 : ∃ j : ℕ, syracuseStep^[j] 271 = 1 := reachStep S271 R407
theorem S279 : syracuseStep 279 = 419 := stepEq 1 (by norm_num) (by decide)
theorem R279 : ∃ j : ℕ, syracuseStep^[j] 279 = 1 := reachStep S279 R419
theorem S281 : syracuseStep 281 = 211 := stepEq 2 (by norm_num) (by decide)
theorem R281 : ∃ j : ℕ, syracuseStep^[j] 281 = 1 := reachStep S281 R211
theorem S287 : syracuseStep 287 = 431 := stepEq 1 (by norm_num) (by decide)
theorem R287 : ∃ j : ℕ, syracuseStep^[j] 287 = 1 := reachStep S287 R431
theorem S303 : syracuseStep 303 = 455 := stepEq 1 (by norm_num) (by decide)
theorem R303 : ∃ j : ℕ, syracuseStep^[j] 303 = 1 := reachStep S303 R455
theorem S4465 : syracuseStep 4465 = 3349 := stepEq 2 (by norm_num) (by decide)
theorem R4465 : ∃ j : ℕ, syracuseStep^[j] 4465 = 1 := reachStep S4465 R3349
theorem S2429 : syracuseStep 2429 = 911 := stepEq 3 (by norm_num) (by decide)
theorem R2429 : ∃ j : ℕ, syracuseStep^[j] 2429 = 1 := reachStep S2429 R911
theorem S4481 : syracuseStep 4481 = 3361 := stepEq 2 (by norm_num) (by decide)
theorem R4481 : ∃ j : ℕ, syracuseStep^[j] 4481 = 1 := reachStep S4481 R3361
theorem S541 : syracuseStep 541 = 203 := stepEq 3 (by norm_num) (by decide)
theorem R541 : ∃ j : ℕ, syracuseStep^[j] 541 = 1 := reachStep S541 R203
theorem S545 : syracuseStep 545 = 409 := stepEq 2 (by norm_num) (by decide)
theorem R545 : ∃ j : ℕ, syracuseStep^[j] 545 = 1 := reachStep S545 R409
theorem S551 : syracuseStep 551 = 827 := stepEq 1 (by norm_num) (by decide)
theorem R551 : ∃ j : ℕ, syracuseStep^[j] 551 = 1 := reachStep S551 R827
theorem S8747 : syracuseStep 8747 = 13121 := stepEq 1 (by norm_num) (by decide)
theorem R8747 : ∃ j : ℕ, syracuseStep^[j] 8747 = 1 := reachStep S8747 R13121
theorem S557 : syracuseStep 557 = 209 := stepEq 3 (by norm_num) (by decide)
theorem R557 : ∃ j : ℕ, syracuseStep^[j] 557 = 1 := reachStep S557 R209
theorem S561 : syracuseStep 561 = 421 := stepEq 2 (by norm_num) (by decide)
theorem R561 : ∃ j : ℕ, syracuseStep^[j] 561 = 1 := reachStep S561 R421
theorem S563 : syracuseStep 563 = 845 := stepEq 1 (by norm_num) (by decide)
theorem R563 : ∃ j : ℕ, syracuseStep^[j] 563 = 1 := reachStep S563 R845
theorem S575 : syracuseStep 575 = 863 := stepEq 1 (by norm_num) (by decide)
theorem R575 : ∃ j : ℕ, syracuseStep^[j] 575 = 1 := reachStep S575 R863
theorem S607 : syracuseStep 607 = 911 := stepEq 1 (by norm_num) (by decide)
theorem R607 : ∃ j : ℕ, syracuseStep^[j] 607 = 1 := reachStep S607 R911
theorem S2681 : syracuseStep 2681 = 2011 := stepEq 2 (by norm_num) (by decide)
theorem R2681 : ∃ j : ℕ, syracuseStep^[j] 2681 = 1 := reachStep S2681 R2011
theorem S4853 : syracuseStep 4853 = 455 := stepEq 5 (by norm_num) (by decide)
theorem R4853 : ∃ j : ℕ, syracuseStep^[j] 4853 = 1 := reachStep S4853 R455
theorem S1085 : syracuseStep 1085 = 407 := stepEq 3 (by norm_num) (by decide)
theorem R1085 : ∃ j : ℕ, syracuseStep^[j] 1085 = 1 := reachStep S1085 R407
theorem S1089 : syracuseStep 1089 = 817 := stepEq 2 (by norm_num) (by decide)
theorem R1089 : ∃ j : ℕ, syracuseStep^[j] 1089 = 1 := reachStep S1089 R817
theorem S1091 : syracuseStep 1091 = 1637 := stepEq 1 (by norm_num) (by decide)
theorem R1091 : ∃ j : ℕ, syracuseStep^[j] 1091 = 1 := reachStep S1091 R1637
theorem S1103 : syracuseStep 1103 = 1655 := stepEq 1 (by norm_num) (by decide)
theorem R1103 : ∃ j : ℕ, syracuseStep^[j] 1103 = 1 := reachStep S1103 R1655
theorem S17495 : syracuseStep 17495 = 26243 := stepEq 1 (by norm_num) (by decide)
theorem R17495 : ∃ j : ℕ, syracuseStep^[j] 17495 = 1 := reachStep S17495 R26243
theorem S1117 : syracuseStep 1117 = 419 := stepEq 3 (by norm_num) (by decide)
theorem R1117 : ∃ j : ℕ, syracuseStep^[j] 1117 = 1 := reachStep S1117 R419
theorem S1121 : syracuseStep 1121 = 841 := stepEq 2 (by norm_num) (by decide)
theorem R1121 : ∃ j : ℕ, syracuseStep^[j] 1121 = 1 := reachStep S1121 R841
theorem S1123 : syracuseStep 1123 = 1685 := stepEq 1 (by norm_num) (by decide)
theorem R1123 : ∃ j : ℕ, syracuseStep^[j] 1123 = 1 := reachStep S1123 R1685
theorem S1125 : syracuseStep 1125 = 211 := stepEq 4 (by norm_num) (by decide)
theorem R1125 : ∃ j : ℕ, syracuseStep^[j] 1125 = 1 := reachStep S1125 R211
theorem S1149 : syracuseStep 1149 = 431 := stepEq 3 (by norm_num) (by decide)
theorem R1149 : ∃ j : ℕ, syracuseStep^[j] 1149 = 1 := reachStep S1149 R431
theorem S1337 : syracuseStep 1337 = 1003 := stepEq 2 (by norm_num) (by decide)
theorem R1337 : ∃ j : ℕ, syracuseStep^[j] 1337 = 1 := reachStep S1337 R1003
theorem S185 : syracuseStep 185 = 139 := stepEq 2 (by norm_num) (by decide)
theorem R185 : ∃ j : ℕ, syracuseStep^[j] 185 = 1 := reachStep S185 R139
theorem S187 : syracuseStep 187 = 281 := stepEq 1 (by norm_num) (by decide)
theorem R187 : ∃ j : ℕ, syracuseStep^[j] 187 = 1 := reachStep S187 R281
theorem S191 : syracuseStep 191 = 287 := stepEq 1 (by norm_num) (by decide)
theorem R191 : ∃ j : ℕ, syracuseStep^[j] 191 = 1 := reachStep S191 R287
theorem S361 : syracuseStep 361 = 271 := stepEq 2 (by norm_num) (by decide)
theorem R361 : ∃ j : ℕ, syracuseStep^[j] 361 = 1 := reachStep S361 R271
theorem S363 : syracuseStep 363 = 545 := stepEq 1 (by norm_num) (by decide)
theorem R363 : ∃ j : ℕ, syracuseStep^[j] 363 = 1 := reachStep S363 R545
theorem S367 : syracuseStep 367 = 551 := stepEq 1 (by norm_num) (by decide)
theorem R367 : ∃ j : ℕ, syracuseStep^[j] 367 = 1 := reachStep S367 R551
theorem S371 : syracuseStep 371 = 557 := stepEq 1 (by norm_num) (by decide)
theorem R371 : ∃ j : ℕ, syracuseStep^[j] 371 = 1 := reachStep S371 R557
theorem S375 : syracuseStep 375 = 563 := stepEq 1 (by norm_num) (by decide)
theorem R375 : ∃ j : ℕ, syracuseStep^[j] 375 = 1 := reachStep S375 R563
theorem S383 : syracuseStep 383 = 575 := stepEq 1 (by norm_num) (by decide)
theorem R383 : ∃ j : ℕ, syracuseStep^[j] 383 = 1 := reachStep S383 R575
theorem S721 : syracuseStep 721 = 541 := stepEq 2 (by norm_num) (by decide)
theorem R721 : ∃ j : ℕ, syracuseStep^[j] 721 = 1 := reachStep S721 R541
theorem S723 : syracuseStep 723 = 1085 := stepEq 1 (by norm_num) (by decide)
theorem R723 : ∃ j : ℕ, syracuseStep^[j] 723 = 1 := reachStep S723 R1085
theorem S727 : syracuseStep 727 = 1091 := stepEq 1 (by norm_num) (by decide)
theorem R727 : ∃ j : ℕ, syracuseStep^[j] 727 = 1 := reachStep S727 R1091
theorem S735 : syracuseStep 735 = 1103 := stepEq 1 (by norm_num) (by decide)
theorem R735 : ∃ j : ℕ, syracuseStep^[j] 735 = 1 := reachStep S735 R1103
theorem S741 : syracuseStep 741 = 139 := stepEq 4 (by norm_num) (by decide)
theorem R741 : ∃ j : ℕ, syracuseStep^[j] 741 = 1 := reachStep S741 R139
theorem S747 : syracuseStep 747 = 1121 := stepEq 1 (by norm_num) (by decide)
theorem R747 : ∃ j : ℕ, syracuseStep^[j] 747 = 1 := reachStep S747 R1121
theorem S749 : syracuseStep 749 = 281 := stepEq 3 (by norm_num) (by decide)
theorem R749 : ∃ j : ℕ, syracuseStep^[j] 749 = 1 := reachStep S749 R281
theorem S765 : syracuseStep 765 = 287 := stepEq 3 (by norm_num) (by decide)
theorem R765 : ∃ j : ℕ, syracuseStep^[j] 765 = 1 := reachStep S765 R287
theorem S809 : syracuseStep 809 = 607 := stepEq 2 (by norm_num) (by decide)
theorem R809 : ∃ j : ℕ, syracuseStep^[j] 809 = 1 := reachStep S809 R607
theorem S891 : syracuseStep 891 = 1337 := stepEq 1 (by norm_num) (by decide)
theorem R891 : ∃ j : ℕ, syracuseStep^[j] 891 = 1 := reachStep S891 R1337
theorem S2987 : syracuseStep 2987 = 4481 := stepEq 1 (by norm_num) (by decide)
theorem R2987 : ∃ j : ℕ, syracuseStep^[j] 2987 = 1 := reachStep S2987 R4481
theorem S3235 : syracuseStep 3235 = 4853 := stepEq 1 (by norm_num) (by decide)
theorem R3235 : ∃ j : ℕ, syracuseStep^[j] 3235 = 1 := reachStep S3235 R4853
theorem S23813 : syracuseStep 23813 = 4465 := stepEq 4 (by norm_num) (by decide)
theorem R23813 : ∃ j : ℕ, syracuseStep^[j] 23813 = 1 := reachStep S23813 R4465
theorem S11663 : syracuseStep 11663 = 17495 := stepEq 1 (by norm_num) (by decide)
theorem R11663 : ∃ j : ℕ, syracuseStep^[j] 11663 = 1 := reachStep S11663 R17495
theorem S1445 : syracuseStep 1445 = 271 := stepEq 4 (by norm_num) (by decide)
theorem R1445 : ∃ j : ℕ, syracuseStep^[j] 1445 = 1 := reachStep S1445 R271
theorem S1453 : syracuseStep 1453 = 545 := stepEq 3 (by norm_num) (by decide)
theorem R1453 : ∃ j : ℕ, syracuseStep^[j] 1453 = 1 := reachStep S1453 R545
theorem S1469 : syracuseStep 1469 = 551 := stepEq 3 (by norm_num) (by decide)
theorem R1469 : ∃ j : ℕ, syracuseStep^[j] 1469 = 1 := reachStep S1469 R551
theorem S1499 : syracuseStep 1499 = 2249 := stepEq 1 (by norm_num) (by decide)
theorem R1499 : ∃ j : ℕ, syracuseStep^[j] 1499 = 1 := reachStep S1499 R2249
theorem S1619 : syracuseStep 1619 = 2429 := stepEq 1 (by norm_num) (by decide)
theorem R1619 : ∃ j : ℕ, syracuseStep^[j] 1619 = 1 := reachStep S1619 R2429
theorem S5831 : syracuseStep 5831 = 8747 := stepEq 1 (by norm_num) (by decide)
theorem R5831 : ∃ j : ℕ, syracuseStep^[j] 5831 = 1 := reachStep S5831 R8747
theorem S1787 : syracuseStep 1787 = 2681 := stepEq 1 (by norm_num) (by decide)
theorem R1787 : ∃ j : ℕ, syracuseStep^[j] 1787 = 1 := reachStep S1787 R2681
theorem S123 : syracuseStep 123 = 185 := stepEq 1 (by norm_num) (by decide)
theorem R123 : ∃ j : ℕ, syracuseStep^[j] 123 = 1 := reachStep S123 R185
theorem S127 : syracuseStep 127 = 191 := stepEq 1 (by norm_num) (by decide)
theorem R127 : ∃ j : ℕ, syracuseStep^[j] 127 = 1 := reachStep S127 R191
theorem S4313 : syracuseStep 4313 = 3235 := stepEq 2 (by norm_num) (by decide)
theorem R4313 : ∃ j : ℕ, syracuseStep^[j] 4313 = 1 := reachStep S4313 R3235
theorem S247 : syracuseStep 247 = 371 := stepEq 1 (by norm_num) (by decide)
theorem R247 : ∃ j : ℕ, syracuseStep^[j] 247 = 1 := reachStep S247 R371
theorem S249 : syracuseStep 249 = 187 := stepEq 2 (by norm_num) (by decide)
theorem R249 : ∃ j : ℕ, syracuseStep^[j] 249 = 1 := reachStep S249 R187
theorem S255 : syracuseStep 255 = 383 := stepEq 1 (by norm_num) (by decide)
theorem R255 : ∃ j : ℕ, syracuseStep^[j] 255 = 1 := reachStep S255 R383
theorem S481 : syracuseStep 481 = 361 := stepEq 2 (by norm_num) (by decide)
theorem R481 : ∃ j : ℕ, syracuseStep^[j] 481 = 1 := reachStep S481 R361
theorem S489 : syracuseStep 489 = 367 := stepEq 2 (by norm_num) (by decide)
theorem R489 : ∃ j : ℕ, syracuseStep^[j] 489 = 1 := reachStep S489 R367
theorem S493 : syracuseStep 493 = 185 := stepEq 3 (by norm_num) (by decide)
theorem R493 : ∃ j : ℕ, syracuseStep^[j] 493 = 1 := reachStep S493 R185
theorem S499 : syracuseStep 499 = 749 := stepEq 1 (by norm_num) (by decide)
theorem R499 : ∃ j : ℕ, syracuseStep^[j] 499 = 1 := reachStep S499 R749
theorem S509 : syracuseStep 509 = 191 := stepEq 3 (by norm_num) (by decide)
theorem R509 : ∃ j : ℕ, syracuseStep^[j] 509 = 1 := reachStep S509 R191
theorem S539 : syracuseStep 539 = 809 := stepEq 1 (by norm_num) (by decide)
theorem R539 : ∃ j : ℕ, syracuseStep^[j] 539 = 1 := reachStep S539 R809
theorem S961 : syracuseStep 961 = 721 := stepEq 2 (by norm_num) (by decide)
theorem R961 : ∃ j : ℕ, syracuseStep^[j] 961 = 1 := reachStep S961 R721
theorem S963 : syracuseStep 963 = 1445 := stepEq 1 (by norm_num) (by decide)
theorem R963 : ∃ j : ℕ, syracuseStep^[j] 963 = 1 := reachStep S963 R1445
theorem S969 : syracuseStep 969 = 727 := stepEq 2 (by norm_num) (by decide)
theorem R969 : ∃ j : ℕ, syracuseStep^[j] 969 = 1 := reachStep S969 R727
theorem S979 : syracuseStep 979 = 1469 := stepEq 1 (by norm_num) (by decide)
theorem R979 : ∃ j : ℕ, syracuseStep^[j] 979 = 1 := reachStep S979 R1469
theorem S989 : syracuseStep 989 = 371 := stepEq 3 (by norm_num) (by decide)
theorem R989 : ∃ j : ℕ, syracuseStep^[j] 989 = 1 := reachStep S989 R371
theorem S997 : syracuseStep 997 = 187 := stepEq 4 (by norm_num) (by decide)
theorem R997 : ∃ j : ℕ, syracuseStep^[j] 997 = 1 := reachStep S997 R187
theorem S999 : syracuseStep 999 = 1499 := stepEq 1 (by norm_num) (by decide)
theorem R999 : ∃ j : ℕ, syracuseStep^[j] 999 = 1 := reachStep S999 R1499
theorem S1021 : syracuseStep 1021 = 383 := stepEq 3 (by norm_num) (by decide)
theorem R1021 : ∃ j : ℕ, syracuseStep^[j] 1021 = 1 := reachStep S1021 R383
theorem S1079 : syracuseStep 1079 = 1619 := stepEq 1 (by norm_num) (by decide)
theorem R1079 : ∃ j : ℕ, syracuseStep^[j] 1079 = 1 := reachStep S1079 R1619
theorem S1191 : syracuseStep 1191 = 1787 := stepEq 1 (by norm_num) (by decide)
theorem R1191 : ∃ j : ℕ, syracuseStep^[j] 1191 = 1 := reachStep S1191 R1787
theorem S15875 : syracuseStep 15875 = 23813 := stepEq 1 (by norm_num) (by decide)
theorem R15875 : ∃ j : ℕ, syracuseStep^[j] 15875 = 1 := reachStep S15875 R23813
theorem S7775 : syracuseStep 7775 = 11663 := stepEq 1 (by norm_num) (by decide)
theorem R7775 : ∃ j : ℕ, syracuseStep^[j] 7775 = 1 := reachStep S7775 R11663
theorem S3887 : syracuseStep 3887 = 5831 := stepEq 1 (by norm_num) (by decide)
theorem R3887 : ∃ j : ℕ, syracuseStep^[j] 3887 = 1 := reachStep S3887 R5831
theorem S1925 : syracuseStep 1925 = 361 := stepEq 4 (by norm_num) (by decide)
theorem R1925 : ∃ j : ℕ, syracuseStep^[j] 1925 = 1 := reachStep S1925 R361
theorem S1937 : syracuseStep 1937 = 1453 := stepEq 2 (by norm_num) (by decide)
theorem R1937 : ∃ j : ℕ, syracuseStep^[j] 1937 = 1 := reachStep S1937 R1453
theorem S1957 : syracuseStep 1957 = 367 := stepEq 4 (by norm_num) (by decide)
theorem R1957 : ∃ j : ℕ, syracuseStep^[j] 1957 = 1 := reachStep S1957 R367
theorem S1991 : syracuseStep 1991 = 2987 := stepEq 1 (by norm_num) (by decide)
theorem R1991 : ∃ j : ℕ, syracuseStep^[j] 1991 = 1 := reachStep S1991 R2987
theorem S1997 : syracuseStep 1997 = 749 := stepEq 3 (by norm_num) (by decide)
theorem R1997 : ∃ j : ℕ, syracuseStep^[j] 1997 = 1 := reachStep S1997 R749
theorem S169 : syracuseStep 169 = 127 := stepEq 2 (by norm_num) (by decide)
theorem R169 : ∃ j : ℕ, syracuseStep^[j] 169 = 1 := reachStep S169 R127
theorem S329 : syracuseStep 329 = 247 := stepEq 2 (by norm_num) (by decide)
theorem R329 : ∃ j : ℕ, syracuseStep^[j] 329 = 1 := reachStep S329 R247
theorem S339 : syracuseStep 339 = 509 := stepEq 1 (by norm_num) (by decide)
theorem R339 : ∃ j : ℕ, syracuseStep^[j] 339 = 1 := reachStep S339 R509
theorem S10583 : syracuseStep 10583 = 15875 := stepEq 1 (by norm_num) (by decide)
theorem R10583 : ∃ j : ℕ, syracuseStep^[j] 10583 = 1 := reachStep S10583 R15875
theorem S359 : syracuseStep 359 = 539 := stepEq 1 (by norm_num) (by decide)
theorem R359 : ∃ j : ℕ, syracuseStep^[j] 359 = 1 := reachStep S359 R539
theorem S2591 : syracuseStep 2591 = 3887 := stepEq 1 (by norm_num) (by decide)
theorem R2591 : ∃ j : ℕ, syracuseStep^[j] 2591 = 1 := reachStep S2591 R3887
theorem S2609 : syracuseStep 2609 = 1957 := stepEq 2 (by norm_num) (by decide)
theorem R2609 : ∃ j : ℕ, syracuseStep^[j] 2609 = 1 := reachStep S2609 R1957
theorem S641 : syracuseStep 641 = 481 := stepEq 2 (by norm_num) (by decide)
theorem R641 : ∃ j : ℕ, syracuseStep^[j] 641 = 1 := reachStep S641 R481
theorem S657 : syracuseStep 657 = 493 := stepEq 2 (by norm_num) (by decide)
theorem R657 : ∃ j : ℕ, syracuseStep^[j] 657 = 1 := reachStep S657 R493
theorem S659 : syracuseStep 659 = 989 := stepEq 1 (by norm_num) (by decide)
theorem R659 : ∃ j : ℕ, syracuseStep^[j] 659 = 1 := reachStep S659 R989
theorem S665 : syracuseStep 665 = 499 := stepEq 2 (by norm_num) (by decide)
theorem R665 : ∃ j : ℕ, syracuseStep^[j] 665 = 1 := reachStep S665 R499
theorem S677 : syracuseStep 677 = 127 := stepEq 4 (by norm_num) (by decide)
theorem R677 : ∃ j : ℕ, syracuseStep^[j] 677 = 1 := reachStep S677 R127
theorem S719 : syracuseStep 719 = 1079 := stepEq 1 (by norm_num) (by decide)
theorem R719 : ∃ j : ℕ, syracuseStep^[j] 719 = 1 := reachStep S719 R1079
theorem S2875 : syracuseStep 2875 = 4313 := stepEq 1 (by norm_num) (by decide)
theorem R2875 : ∃ j : ℕ, syracuseStep^[j] 2875 = 1 := reachStep S2875 R4313
theorem S5183 : syracuseStep 5183 = 7775 := stepEq 1 (by norm_num) (by decide)
theorem R5183 : ∃ j : ℕ, syracuseStep^[j] 5183 = 1 := reachStep S5183 R7775
theorem S1283 : syracuseStep 1283 = 1925 := stepEq 1 (by norm_num) (by decide)
theorem R1283 : ∃ j : ℕ, syracuseStep^[j] 1283 = 1 := reachStep S1283 R1925
theorem S1291 : syracuseStep 1291 = 1937 := stepEq 1 (by norm_num) (by decide)
theorem R1291 : ∃ j : ℕ, syracuseStep^[j] 1291 = 1 := reachStep S1291 R1937
theorem S1327 : syracuseStep 1327 = 1991 := stepEq 1 (by norm_num) (by decide)
theorem R1327 : ∃ j : ℕ, syracuseStep^[j] 1327 = 1 := reachStep S1327 R1991
theorem S1331 : syracuseStep 1331 = 1997 := stepEq 1 (by norm_num) (by decide)
theorem R1331 : ∃ j : ℕ, syracuseStep^[j] 1331 = 1 := reachStep S1331 R1997
theorem S1361 : syracuseStep 1361 = 1021 := stepEq 2 (by norm_num) (by decide)
theorem R1361 : ∃ j : ℕ, syracuseStep^[j] 1361 = 1 := reachStep S1361 R1021
theorem S219 : syracuseStep 219 = 329 := stepEq 1 (by norm_num) (by decide)
theorem R219 : ∃ j : ℕ, syracuseStep^[j] 219 = 1 := reachStep S219 R329
theorem S225 : syracuseStep 225 = 169 := stepEq 2 (by norm_num) (by decide)
theorem R225 : ∃ j : ℕ, syracuseStep^[j] 225 = 1 := reachStep S225 R169
theorem S239 : syracuseStep 239 = 359 := stepEq 1 (by norm_num) (by decide)
theorem R239 : ∃ j : ℕ, syracuseStep^[j] 239 = 1 := reachStep S239 R359
theorem S427 : syracuseStep 427 = 641 := stepEq 1 (by norm_num) (by decide)
theorem R427 : ∃ j : ℕ, syracuseStep^[j] 427 = 1 := reachStep S427 R641
theorem S439 : syracuseStep 439 = 659 := stepEq 1 (by norm_num) (by decide)
theorem R439 : ∃ j : ℕ, syracuseStep^[j] 439 = 1 := reachStep S439 R659
theorem S443 : syracuseStep 443 = 665 := stepEq 1 (by norm_num) (by decide)
theorem R443 : ∃ j : ℕ, syracuseStep^[j] 443 = 1 := reachStep S443 R665
theorem S451 : syracuseStep 451 = 677 := stepEq 1 (by norm_num) (by decide)
theorem R451 : ∃ j : ℕ, syracuseStep^[j] 451 = 1 := reachStep S451 R677
theorem S479 : syracuseStep 479 = 719 := stepEq 1 (by norm_num) (by decide)
theorem R479 : ∃ j : ℕ, syracuseStep^[j] 479 = 1 := reachStep S479 R719
theorem S855 : syracuseStep 855 = 1283 := stepEq 1 (by norm_num) (by decide)
theorem R855 : ∃ j : ℕ, syracuseStep^[j] 855 = 1 := reachStep S855 R1283
theorem S877 : syracuseStep 877 = 329 := stepEq 3 (by norm_num) (by decide)
theorem R877 : ∃ j : ℕ, syracuseStep^[j] 877 = 1 := reachStep S877 R329
theorem S887 : syracuseStep 887 = 1331 := stepEq 1 (by norm_num) (by decide)
theorem R887 : ∃ j : ℕ, syracuseStep^[j] 887 = 1 := reachStep S887 R1331
theorem S901 : syracuseStep 901 = 169 := stepEq 4 (by norm_num) (by decide)
theorem R901 : ∃ j : ℕ, syracuseStep^[j] 901 = 1 := reachStep S901 R169
theorem S907 : syracuseStep 907 = 1361 := stepEq 1 (by norm_num) (by decide)
theorem R907 : ∃ j : ℕ, syracuseStep^[j] 907 = 1 := reachStep S907 R1361
theorem S7055 : syracuseStep 7055 = 10583 := stepEq 1 (by norm_num) (by decide)
theorem R7055 : ∃ j : ℕ, syracuseStep^[j] 7055 = 1 := reachStep S7055 R10583
theorem S957 : syracuseStep 957 = 359 := stepEq 3 (by norm_num) (by decide)
theorem R957 : ∃ j : ℕ, syracuseStep^[j] 957 = 1 := reachStep S957 R359
theorem S3455 : syracuseStep 3455 = 5183 := stepEq 1 (by norm_num) (by decide)
theorem R3455 : ∃ j : ℕ, syracuseStep^[j] 3455 = 1 := reachStep S3455 R5183
theorem S3509 : syracuseStep 3509 = 329 := stepEq 5 (by norm_num) (by decide)
theorem R3509 : ∃ j : ℕ, syracuseStep^[j] 3509 = 1 := reachStep S3509 R329
theorem S1709 : syracuseStep 1709 = 641 := stepEq 3 (by norm_num) (by decide)
theorem R1709 : ∃ j : ℕ, syracuseStep^[j] 1709 = 1 := reachStep S1709 R641
theorem S1721 : syracuseStep 1721 = 1291 := stepEq 2 (by norm_num) (by decide)
theorem R1721 : ∃ j : ℕ, syracuseStep^[j] 1721 = 1 := reachStep S1721 R1291
theorem S1727 : syracuseStep 1727 = 2591 := stepEq 1 (by norm_num) (by decide)
theorem R1727 : ∃ j : ℕ, syracuseStep^[j] 1727 = 1 := reachStep S1727 R2591
theorem S1739 : syracuseStep 1739 = 2609 := stepEq 1 (by norm_num) (by decide)
theorem R1739 : ∃ j : ℕ, syracuseStep^[j] 1739 = 1 := reachStep S1739 R2609
theorem S1757 : syracuseStep 1757 = 659 := stepEq 3 (by norm_num) (by decide)
theorem R1757 : ∃ j : ℕ, syracuseStep^[j] 1757 = 1 := reachStep S1757 R659
theorem S1769 : syracuseStep 1769 = 1327 := stepEq 2 (by norm_num) (by decide)
theorem R1769 : ∃ j : ℕ, syracuseStep^[j] 1769 = 1 := reachStep S1769 R1327
theorem S3833 : syracuseStep 3833 = 2875 := stepEq 2 (by norm_num) (by decide)
theorem R3833 : ∃ j : ℕ, syracuseStep^[j] 3833 = 1 := reachStep S3833 R2875
theorem S159 : syracuseStep 159 = 239 := stepEq 1 (by norm_num) (by decide)
theorem R159 : ∃ j : ℕ, syracuseStep^[j] 159 = 1 := reachStep S159 R239
theorem S2303 : syracuseStep 2303 = 3455 := stepEq 1 (by norm_num) (by decide)
theorem R2303 : ∃ j : ℕ, syracuseStep^[j] 2303 = 1 := reachStep S2303 R3455
theorem S2339 : syracuseStep 2339 = 3509 := stepEq 1 (by norm_num) (by decide)
theorem R2339 : ∃ j : ℕ, syracuseStep^[j] 2339 = 1 := reachStep S2339 R3509
theorem S295 : syracuseStep 295 = 443 := stepEq 1 (by norm_num) (by decide)
theorem R295 : ∃ j : ℕ, syracuseStep^[j] 295 = 1 := reachStep S295 R443
theorem S319 : syracuseStep 319 = 479 := stepEq 1 (by norm_num) (by decide)
theorem R319 : ∃ j : ℕ, syracuseStep^[j] 319 = 1 := reachStep S319 R479
theorem S2555 : syracuseStep 2555 = 3833 := stepEq 1 (by norm_num) (by decide)
theorem R2555 : ∃ j : ℕ, syracuseStep^[j] 2555 = 1 := reachStep S2555 R3833
theorem S569 : syracuseStep 569 = 427 := stepEq 2 (by norm_num) (by decide)
theorem R569 : ∃ j : ℕ, syracuseStep^[j] 569 = 1 := reachStep S569 R427
theorem S585 : syracuseStep 585 = 439 := stepEq 2 (by norm_num) (by decide)
theorem R585 : ∃ j : ℕ, syracuseStep^[j] 585 = 1 := reachStep S585 R439
theorem S591 : syracuseStep 591 = 887 := stepEq 1 (by norm_num) (by decide)
theorem R591 : ∃ j : ℕ, syracuseStep^[j] 591 = 1 := reachStep S591 R887
theorem S601 : syracuseStep 601 = 451 := stepEq 2 (by norm_num) (by decide)
theorem R601 : ∃ j : ℕ, syracuseStep^[j] 601 = 1 := reachStep S601 R451
theorem S4703 : syracuseStep 4703 = 7055 := stepEq 1 (by norm_num) (by decide)
theorem R4703 : ∃ j : ℕ, syracuseStep^[j] 4703 = 1 := reachStep S4703 R7055
theorem S637 : syracuseStep 637 = 239 := stepEq 3 (by norm_num) (by decide)
theorem R637 : ∃ j : ℕ, syracuseStep^[j] 637 = 1 := reachStep S637 R239
theorem S1139 : syracuseStep 1139 = 1709 := stepEq 1 (by norm_num) (by decide)
theorem R1139 : ∃ j : ℕ, syracuseStep^[j] 1139 = 1 := reachStep S1139 R1709
theorem S1147 : syracuseStep 1147 = 1721 := stepEq 1 (by norm_num) (by decide)
theorem R1147 : ∃ j : ℕ, syracuseStep^[j] 1147 = 1 := reachStep S1147 R1721
theorem S1151 : syracuseStep 1151 = 1727 := stepEq 1 (by norm_num) (by decide)
theorem R1151 : ∃ j : ℕ, syracuseStep^[j] 1151 = 1 := reachStep S1151 R1727
theorem S1159 : syracuseStep 1159 = 1739 := stepEq 1 (by norm_num) (by decide)
theorem R1159 : ∃ j : ℕ, syracuseStep^[j] 1159 = 1 := reachStep S1159 R1739
theorem S1169 : syracuseStep 1169 = 877 := stepEq 2 (by norm_num) (by decide)
theorem R1169 : ∃ j : ℕ, syracuseStep^[j] 1169 = 1 := reachStep S1169 R877
theorem S1171 : syracuseStep 1171 = 1757 := stepEq 1 (by norm_num) (by decide)
theorem R1171 : ∃ j : ℕ, syracuseStep^[j] 1171 = 1 := reachStep S1171 R1757
theorem S1179 : syracuseStep 1179 = 1769 := stepEq 1 (by norm_num) (by decide)
theorem R1179 : ∃ j : ℕ, syracuseStep^[j] 1179 = 1 := reachStep S1179 R1769
theorem S1181 : syracuseStep 1181 = 443 := stepEq 3 (by norm_num) (by decide)
theorem R1181 : ∃ j : ℕ, syracuseStep^[j] 1181 = 1 := reachStep S1181 R443
theorem S1201 : syracuseStep 1201 = 901 := stepEq 2 (by norm_num) (by decide)
theorem R1201 : ∃ j : ℕ, syracuseStep^[j] 1201 = 1 := reachStep S1201 R901
theorem S1277 : syracuseStep 1277 = 479 := stepEq 3 (by norm_num) (by decide)
theorem R1277 : ∃ j : ℕ, syracuseStep^[j] 1277 = 1 := reachStep S1277 R479
theorem S379 : syracuseStep 379 = 569 := stepEq 1 (by norm_num) (by decide)
theorem R379 : ∃ j : ℕ, syracuseStep^[j] 379 = 1 := reachStep S379 R569
theorem S393 : syracuseStep 393 = 295 := stepEq 2 (by norm_num) (by decide)
theorem R393 : ∃ j : ℕ, syracuseStep^[j] 393 = 1 := reachStep S393 R295
theorem S425 : syracuseStep 425 = 319 := stepEq 2 (by norm_num) (by decide)
theorem R425 : ∃ j : ℕ, syracuseStep^[j] 425 = 1 := reachStep S425 R319
theorem S759 : syracuseStep 759 = 1139 := stepEq 1 (by norm_num) (by decide)
theorem R759 : ∃ j : ℕ, syracuseStep^[j] 759 = 1 := reachStep S759 R1139
theorem S767 : syracuseStep 767 = 1151 := stepEq 1 (by norm_num) (by decide)
theorem R767 : ∃ j : ℕ, syracuseStep^[j] 767 = 1 := reachStep S767 R1151
theorem S779 : syracuseStep 779 = 1169 := stepEq 1 (by norm_num) (by decide)
theorem R779 : ∃ j : ℕ, syracuseStep^[j] 779 = 1 := reachStep S779 R1169
theorem S787 : syracuseStep 787 = 1181 := stepEq 1 (by norm_num) (by decide)
theorem R787 : ∃ j : ℕ, syracuseStep^[j] 787 = 1 := reachStep S787 R1181
theorem S801 : syracuseStep 801 = 601 := stepEq 2 (by norm_num) (by decide)
theorem R801 : ∃ j : ℕ, syracuseStep^[j] 801 = 1 := reachStep S801 R601
theorem S849 : syracuseStep 849 = 637 := stepEq 2 (by norm_num) (by decide)
theorem R849 : ∃ j : ℕ, syracuseStep^[j] 849 = 1 := reachStep S849 R637
theorem S851 : syracuseStep 851 = 1277 := stepEq 1 (by norm_num) (by decide)
theorem R851 : ∃ j : ℕ, syracuseStep^[j] 851 = 1 := reachStep S851 R1277
theorem S3037 : syracuseStep 3037 = 1139 := stepEq 3 (by norm_num) (by decide)
theorem R3037 : ∃ j : ℕ, syracuseStep^[j] 3037 = 1 := reachStep S3037 R1139
theorem S50165 : syracuseStep 50165 = 4703 := stepEq 5 (by norm_num) (by decide)
theorem R50165 : ∃ j : ℕ, syracuseStep^[j] 50165 = 1 := reachStep S50165 R4703
theorem S3397 : syracuseStep 3397 = 637 := stepEq 4 (by norm_num) (by decide)
theorem R3397 : ∃ j : ℕ, syracuseStep^[j] 3397 = 1 := reachStep S3397 R637
theorem S1517 : syracuseStep 1517 = 569 := stepEq 3 (by norm_num) (by decide)
theorem R1517 : ∃ j : ℕ, syracuseStep^[j] 1517 = 1 := reachStep S1517 R569
theorem S1529 : syracuseStep 1529 = 1147 := stepEq 2 (by norm_num) (by decide)
theorem R1529 : ∃ j : ℕ, syracuseStep^[j] 1529 = 1 := reachStep S1529 R1147
theorem S1535 : syracuseStep 1535 = 2303 := stepEq 1 (by norm_num) (by decide)
theorem R1535 : ∃ j : ℕ, syracuseStep^[j] 1535 = 1 := reachStep S1535 R2303
theorem S1559 : syracuseStep 1559 = 2339 := stepEq 1 (by norm_num) (by decide)
theorem R1559 : ∃ j : ℕ, syracuseStep^[j] 1559 = 1 := reachStep S1559 R2339
theorem S1561 : syracuseStep 1561 = 1171 := stepEq 2 (by norm_num) (by decide)
theorem R1561 : ∃ j : ℕ, syracuseStep^[j] 1561 = 1 := reachStep S1561 R1171
theorem S1601 : syracuseStep 1601 = 1201 := stepEq 2 (by norm_num) (by decide)
theorem R1601 : ∃ j : ℕ, syracuseStep^[j] 1601 = 1 := reachStep S1601 R1201
theorem S1703 : syracuseStep 1703 = 2555 := stepEq 1 (by norm_num) (by decide)
theorem R1703 : ∃ j : ℕ, syracuseStep^[j] 1703 = 1 := reachStep S1703 R2555
theorem S2081 : syracuseStep 2081 = 1561 := stepEq 2 (by norm_num) (by decide)
theorem R2081 : ∃ j : ℕ, syracuseStep^[j] 2081 = 1 := reachStep S2081 R1561
theorem S283 : syracuseStep 283 = 425 := stepEq 1 (by norm_num) (by decide)
theorem R283 : ∃ j : ℕ, syracuseStep^[j] 283 = 1 := reachStep S283 R425
theorem S4529 : syracuseStep 4529 = 3397 := stepEq 2 (by norm_num) (by decide)
theorem R4529 : ∃ j : ℕ, syracuseStep^[j] 4529 = 1 := reachStep S4529 R3397
theorem S505 : syracuseStep 505 = 379 := stepEq 2 (by norm_num) (by decide)
theorem R505 : ∃ j : ℕ, syracuseStep^[j] 505 = 1 := reachStep S505 R379
theorem S511 : syracuseStep 511 = 767 := stepEq 1 (by norm_num) (by decide)
theorem R511 : ∃ j : ℕ, syracuseStep^[j] 511 = 1 := reachStep S511 R767
theorem S519 : syracuseStep 519 = 779 := stepEq 1 (by norm_num) (by decide)
theorem R519 : ∃ j : ℕ, syracuseStep^[j] 519 = 1 := reachStep S519 R779
theorem S567 : syracuseStep 567 = 851 := stepEq 1 (by norm_num) (by decide)
theorem R567 : ∃ j : ℕ, syracuseStep^[j] 567 = 1 := reachStep S567 R851
theorem S33443 : syracuseStep 33443 = 50165 := stepEq 1 (by norm_num) (by decide)
theorem R33443 : ∃ j : ℕ, syracuseStep^[j] 33443 = 1 := reachStep S33443 R50165
theorem S1011 : syracuseStep 1011 = 1517 := stepEq 1 (by norm_num) (by decide)
theorem R1011 : ∃ j : ℕ, syracuseStep^[j] 1011 = 1 := reachStep S1011 R1517
theorem S1019 : syracuseStep 1019 = 1529 := stepEq 1 (by norm_num) (by decide)
theorem R1019 : ∃ j : ℕ, syracuseStep^[j] 1019 = 1 := reachStep S1019 R1529
theorem S1023 : syracuseStep 1023 = 1535 := stepEq 1 (by norm_num) (by decide)
theorem R1023 : ∃ j : ℕ, syracuseStep^[j] 1023 = 1 := reachStep S1023 R1535
theorem S1039 : syracuseStep 1039 = 1559 := stepEq 1 (by norm_num) (by decide)
theorem R1039 : ∃ j : ℕ, syracuseStep^[j] 1039 = 1 := reachStep S1039 R1559
theorem S1049 : syracuseStep 1049 = 787 := stepEq 2 (by norm_num) (by decide)
theorem R1049 : ∃ j : ℕ, syracuseStep^[j] 1049 = 1 := reachStep S1049 R787
theorem S1067 : syracuseStep 1067 = 1601 := stepEq 1 (by norm_num) (by decide)
theorem R1067 : ∃ j : ℕ, syracuseStep^[j] 1067 = 1 := reachStep S1067 R1601
theorem S1133 : syracuseStep 1133 = 425 := stepEq 3 (by norm_num) (by decide)
theorem R1133 : ∃ j : ℕ, syracuseStep^[j] 1133 = 1 := reachStep S1133 R425
theorem S1135 : syracuseStep 1135 = 1703 := stepEq 1 (by norm_num) (by decide)
theorem R1135 : ∃ j : ℕ, syracuseStep^[j] 1135 = 1 := reachStep S1135 R1703
theorem S4049 : syracuseStep 4049 = 3037 := stepEq 2 (by norm_num) (by decide)
theorem R4049 : ∃ j : ℕ, syracuseStep^[j] 4049 = 1 := reachStep S4049 R3037
theorem S2045 : syracuseStep 2045 = 767 := stepEq 3 (by norm_num) (by decide)
theorem R2045 : ∃ j : ℕ, syracuseStep^[j] 2045 = 1 := reachStep S2045 R767
theorem S377 : syracuseStep 377 = 283 := stepEq 2 (by norm_num) (by decide)
theorem R377 : ∃ j : ℕ, syracuseStep^[j] 377 = 1 := reachStep S377 R283
theorem S2693 : syracuseStep 2693 = 505 := stepEq 4 (by norm_num) (by decide)
theorem R2693 : ∃ j : ℕ, syracuseStep^[j] 2693 = 1 := reachStep S2693 R505
theorem S2699 : syracuseStep 2699 = 4049 := stepEq 1 (by norm_num) (by decide)
theorem R2699 : ∃ j : ℕ, syracuseStep^[j] 2699 = 1 := reachStep S2699 R4049
theorem S673 : syracuseStep 673 = 505 := stepEq 2 (by norm_num) (by decide)
theorem R673 : ∃ j : ℕ, syracuseStep^[j] 673 = 1 := reachStep S673 R505
theorem S679 : syracuseStep 679 = 1019 := stepEq 1 (by norm_num) (by decide)
theorem R679 : ∃ j : ℕ, syracuseStep^[j] 679 = 1 := reachStep S679 R1019
theorem S681 : syracuseStep 681 = 511 := stepEq 2 (by norm_num) (by decide)
theorem R681 : ∃ j : ℕ, syracuseStep^[j] 681 = 1 := reachStep S681 R511
theorem S699 : syracuseStep 699 = 1049 := stepEq 1 (by norm_num) (by decide)
theorem R699 : ∃ j : ℕ, syracuseStep^[j] 699 = 1 := reachStep S699 R1049
theorem S711 : syracuseStep 711 = 1067 := stepEq 1 (by norm_num) (by decide)
theorem R711 : ∃ j : ℕ, syracuseStep^[j] 711 = 1 := reachStep S711 R1067
theorem S755 : syracuseStep 755 = 1133 := stepEq 1 (by norm_num) (by decide)
theorem R755 : ∃ j : ℕ, syracuseStep^[j] 755 = 1 := reachStep S755 R1133
theorem S2845 : syracuseStep 2845 = 1067 := stepEq 3 (by norm_num) (by decide)
theorem R2845 : ∃ j : ℕ, syracuseStep^[j] 2845 = 1 := reachStep S2845 R1067
theorem S3019 : syracuseStep 3019 = 4529 := stepEq 1 (by norm_num) (by decide)
theorem R3019 : ∃ j : ℕ, syracuseStep^[j] 3019 = 1 := reachStep S3019 R4529
theorem S5453 : syracuseStep 5453 = 2045 := stepEq 3 (by norm_num) (by decide)
theorem R5453 : ∃ j : ℕ, syracuseStep^[j] 5453 = 1 := reachStep S5453 R2045
theorem S1363 : syracuseStep 1363 = 2045 := stepEq 1 (by norm_num) (by decide)
theorem R1363 : ∃ j : ℕ, syracuseStep^[j] 1363 = 1 := reachStep S1363 R2045
theorem S1385 : syracuseStep 1385 = 1039 := stepEq 2 (by norm_num) (by decide)
theorem R1385 : ∃ j : ℕ, syracuseStep^[j] 1385 = 1 := reachStep S1385 R1039
theorem S1387 : syracuseStep 1387 = 2081 := stepEq 1 (by norm_num) (by decide)
theorem R1387 : ∃ j : ℕ, syracuseStep^[j] 1387 = 1 := reachStep S1387 R2081
theorem S22295 : syracuseStep 22295 = 33443 := stepEq 1 (by norm_num) (by decide)
theorem R22295 : ∃ j : ℕ, syracuseStep^[j] 22295 = 1 := reachStep S22295 R33443
theorem S251 : syracuseStep 251 = 377 := stepEq 1 (by norm_num) (by decide)
theorem R251 : ∃ j : ℕ, syracuseStep^[j] 251 = 1 := reachStep S251 R377
theorem S503 : syracuseStep 503 = 755 := stepEq 1 (by norm_num) (by decide)
theorem R503 : ∃ j : ℕ, syracuseStep^[j] 503 = 1 := reachStep S503 R755
theorem S14863 : syracuseStep 14863 = 22295 := stepEq 1 (by norm_num) (by decide)
theorem R14863 : ∃ j : ℕ, syracuseStep^[j] 14863 = 1 := reachStep S14863 R22295
theorem S15173 : syracuseStep 15173 = 2845 := stepEq 4 (by norm_num) (by decide)
theorem R15173 : ∃ j : ℕ, syracuseStep^[j] 15173 = 1 := reachStep S15173 R2845
theorem S897 : syracuseStep 897 = 673 := stepEq 2 (by norm_num) (by decide)
theorem R897 : ∃ j : ℕ, syracuseStep^[j] 897 = 1 := reachStep S897 R673
theorem S905 : syracuseStep 905 = 679 := stepEq 2 (by norm_num) (by decide)
theorem R905 : ∃ j : ℕ, syracuseStep^[j] 905 = 1 := reachStep S905 R679
theorem S923 : syracuseStep 923 = 1385 := stepEq 1 (by norm_num) (by decide)
theorem R923 : ∃ j : ℕ, syracuseStep^[j] 923 = 1 := reachStep S923 R1385
theorem S1005 : syracuseStep 1005 = 377 := stepEq 3 (by norm_num) (by decide)
theorem R1005 : ∃ j : ℕ, syracuseStep^[j] 1005 = 1 := reachStep S1005 R377
theorem S3635 : syracuseStep 3635 = 5453 := stepEq 1 (by norm_num) (by decide)
theorem R3635 : ∃ j : ℕ, syracuseStep^[j] 3635 = 1 := reachStep S3635 R5453
theorem S1795 : syracuseStep 1795 = 2693 := stepEq 1 (by norm_num) (by decide)
theorem R1795 : ∃ j : ℕ, syracuseStep^[j] 1795 = 1 := reachStep S1795 R2693
theorem S1799 : syracuseStep 1799 = 2699 := stepEq 1 (by norm_num) (by decide)
theorem R1799 : ∃ j : ℕ, syracuseStep^[j] 1799 = 1 := reachStep S1799 R2699
theorem S1817 : syracuseStep 1817 = 1363 := stepEq 2 (by norm_num) (by decide)
theorem R1817 : ∃ j : ℕ, syracuseStep^[j] 1817 = 1 := reachStep S1817 R1363
theorem S1849 : syracuseStep 1849 = 1387 := stepEq 2 (by norm_num) (by decide)
theorem R1849 : ∃ j : ℕ, syracuseStep^[j] 1849 = 1 := reachStep S1849 R1387
theorem S4025 : syracuseStep 4025 = 3019 := stepEq 2 (by norm_num) (by decide)
theorem R4025 : ∃ j : ℕ, syracuseStep^[j] 4025 = 1 := reachStep S4025 R3019
theorem S167 : syracuseStep 167 = 251 := stepEq 1 (by norm_num) (by decide)
theorem R167 : ∃ j : ℕ, syracuseStep^[j] 167 = 1 := reachStep S167 R251
theorem S335 : syracuseStep 335 = 503 := stepEq 1 (by norm_num) (by decide)
theorem R335 : ∃ j : ℕ, syracuseStep^[j] 335 = 1 := reachStep S335 R503
theorem S2393 : syracuseStep 2393 = 1795 := stepEq 2 (by norm_num) (by decide)
theorem R2393 : ∃ j : ℕ, syracuseStep^[j] 2393 = 1 := reachStep S2393 R1795
theorem S2423 : syracuseStep 2423 = 3635 := stepEq 1 (by norm_num) (by decide)
theorem R2423 : ∃ j : ℕ, syracuseStep^[j] 2423 = 1 := reachStep S2423 R3635
theorem S2465 : syracuseStep 2465 = 1849 := stepEq 2 (by norm_num) (by decide)
theorem R2465 : ∃ j : ℕ, syracuseStep^[j] 2465 = 1 := reachStep S2465 R1849
theorem S603 : syracuseStep 603 = 905 := stepEq 1 (by norm_num) (by decide)
theorem R603 : ∃ j : ℕ, syracuseStep^[j] 603 = 1 := reachStep S603 R905
theorem S615 : syracuseStep 615 = 923 := stepEq 1 (by norm_num) (by decide)
theorem R615 : ∃ j : ℕ, syracuseStep^[j] 615 = 1 := reachStep S615 R923
theorem S2683 : syracuseStep 2683 = 4025 := stepEq 1 (by norm_num) (by decide)
theorem R2683 : ∃ j : ℕ, syracuseStep^[j] 2683 = 1 := reachStep S2683 R4025
theorem S669 : syracuseStep 669 = 251 := stepEq 3 (by norm_num) (by decide)
theorem R669 : ∃ j : ℕ, syracuseStep^[j] 669 = 1 := reachStep S669 R251
theorem S1199 : syracuseStep 1199 = 1799 := stepEq 1 (by norm_num) (by decide)
theorem R1199 : ∃ j : ℕ, syracuseStep^[j] 1199 = 1 := reachStep S1199 R1799
theorem S1211 : syracuseStep 1211 = 1817 := stepEq 1 (by norm_num) (by decide)
theorem R1211 : ∃ j : ℕ, syracuseStep^[j] 1211 = 1 := reachStep S1211 R1817
theorem S19817 : syracuseStep 19817 = 14863 := stepEq 2 (by norm_num) (by decide)
theorem R19817 : ∃ j : ℕ, syracuseStep^[j] 19817 = 1 := reachStep S19817 R14863
theorem S10115 : syracuseStep 10115 = 15173 := stepEq 1 (by norm_num) (by decide)
theorem R10115 : ∃ j : ℕ, syracuseStep^[j] 10115 = 1 := reachStep S10115 R15173
theorem S111 : syracuseStep 111 = 167 := stepEq 1 (by norm_num) (by decide)
theorem R111 : ∃ j : ℕ, syracuseStep^[j] 111 = 1 := reachStep S111 R167
theorem S223 : syracuseStep 223 = 335 := stepEq 1 (by norm_num) (by decide)
theorem R223 : ∃ j : ℕ, syracuseStep^[j] 223 = 1 := reachStep S223 R335
theorem S445 : syracuseStep 445 = 167 := stepEq 3 (by norm_num) (by decide)
theorem R445 : ∃ j : ℕ, syracuseStep^[j] 445 = 1 := reachStep S445 R167
theorem S6743 : syracuseStep 6743 = 10115 := stepEq 1 (by norm_num) (by decide)
theorem R6743 : ∃ j : ℕ, syracuseStep^[j] 6743 = 1 := reachStep S6743 R10115
theorem S799 : syracuseStep 799 = 1199 := stepEq 1 (by norm_num) (by decide)
theorem R799 : ∃ j : ℕ, syracuseStep^[j] 799 = 1 := reachStep S799 R1199
theorem S807 : syracuseStep 807 = 1211 := stepEq 1 (by norm_num) (by decide)
theorem R807 : ∃ j : ℕ, syracuseStep^[j] 807 = 1 := reachStep S807 R1211
theorem S893 : syracuseStep 893 = 335 := stepEq 3 (by norm_num) (by decide)
theorem R893 : ∃ j : ℕ, syracuseStep^[j] 893 = 1 := reachStep S893 R335
theorem S13211 : syracuseStep 13211 = 19817 := stepEq 1 (by norm_num) (by decide)
theorem R13211 : ∃ j : ℕ, syracuseStep^[j] 13211 = 1 := reachStep S13211 R19817
theorem S3577 : syracuseStep 3577 = 2683 := stepEq 2 (by norm_num) (by decide)
theorem R3577 : ∃ j : ℕ, syracuseStep^[j] 3577 = 1 := reachStep S3577 R2683
theorem S1595 : syracuseStep 1595 = 2393 := stepEq 1 (by norm_num) (by decide)
theorem R1595 : ∃ j : ℕ, syracuseStep^[j] 1595 = 1 := reachStep S1595 R2393
theorem S1615 : syracuseStep 1615 = 2423 := stepEq 1 (by norm_num) (by decide)
theorem R1615 : ∃ j : ℕ, syracuseStep^[j] 1615 = 1 := reachStep S1615 R2423
theorem S1643 : syracuseStep 1643 = 2465 := stepEq 1 (by norm_num) (by decide)
theorem R1643 : ∃ j : ℕ, syracuseStep^[j] 1643 = 1 := reachStep S1643 R2465
theorem S1781 : syracuseStep 1781 = 167 := stepEq 5 (by norm_num) (by decide)
theorem R1781 : ∃ j : ℕ, syracuseStep^[j] 1781 = 1 := reachStep S1781 R167
theorem S2153 : syracuseStep 2153 = 1615 := stepEq 2 (by norm_num) (by decide)
theorem R2153 : ∃ j : ℕ, syracuseStep^[j] 2153 = 1 := reachStep S2153 R1615
theorem S297 : syracuseStep 297 = 223 := stepEq 2 (by norm_num) (by decide)
theorem R297 : ∃ j : ℕ, syracuseStep^[j] 297 = 1 := reachStep S297 R223
theorem S4495 : syracuseStep 4495 = 6743 := stepEq 1 (by norm_num) (by decide)
theorem R4495 : ∃ j : ℕ, syracuseStep^[j] 4495 = 1 := reachStep S4495 R6743
theorem S593 : syracuseStep 593 = 445 := stepEq 2 (by norm_num) (by decide)
theorem R593 : ∃ j : ℕ, syracuseStep^[j] 593 = 1 := reachStep S593 R445
theorem S595 : syracuseStep 595 = 893 := stepEq 1 (by norm_num) (by decide)
theorem R595 : ∃ j : ℕ, syracuseStep^[j] 595 = 1 := reachStep S595 R893
theorem S8807 : syracuseStep 8807 = 13211 := stepEq 1 (by norm_num) (by decide)
theorem R8807 : ∃ j : ℕ, syracuseStep^[j] 8807 = 1 := reachStep S8807 R13211
theorem S4769 : syracuseStep 4769 = 3577 := stepEq 2 (by norm_num) (by decide)
theorem R4769 : ∃ j : ℕ, syracuseStep^[j] 4769 = 1 := reachStep S4769 R3577
theorem S1063 : syracuseStep 1063 = 1595 := stepEq 1 (by norm_num) (by decide)
theorem R1063 : ∃ j : ℕ, syracuseStep^[j] 1063 = 1 := reachStep S1063 R1595
theorem S1065 : syracuseStep 1065 = 799 := stepEq 2 (by norm_num) (by decide)
theorem R1065 : ∃ j : ℕ, syracuseStep^[j] 1065 = 1 := reachStep S1065 R799
theorem S1095 : syracuseStep 1095 = 1643 := stepEq 1 (by norm_num) (by decide)
theorem R1095 : ∃ j : ℕ, syracuseStep^[j] 1095 = 1 := reachStep S1095 R1643
theorem S1187 : syracuseStep 1187 = 1781 := stepEq 1 (by norm_num) (by decide)
theorem R1187 : ∃ j : ℕ, syracuseStep^[j] 1187 = 1 := reachStep S1187 R1781
theorem S1189 : syracuseStep 1189 = 223 := stepEq 4 (by norm_num) (by decide)
theorem R1189 : ∃ j : ℕ, syracuseStep^[j] 1189 = 1 := reachStep S1189 R223
theorem S395 : syracuseStep 395 = 593 := stepEq 1 (by norm_num) (by decide)
theorem R395 : ∃ j : ℕ, syracuseStep^[j] 395 = 1 := reachStep S395 R593
theorem S791 : syracuseStep 791 = 1187 := stepEq 1 (by norm_num) (by decide)
theorem R791 : ∃ j : ℕ, syracuseStep^[j] 791 = 1 := reachStep S791 R1187
theorem S793 : syracuseStep 793 = 595 := stepEq 2 (by norm_num) (by decide)
theorem R793 : ∃ j : ℕ, syracuseStep^[j] 793 = 1 := reachStep S793 R595
theorem S23485 : syracuseStep 23485 = 8807 := stepEq 3 (by norm_num) (by decide)
theorem R23485 : ∃ j : ℕ, syracuseStep^[j] 23485 = 1 := reachStep S23485 R8807
theorem S3179 : syracuseStep 3179 = 4769 := stepEq 1 (by norm_num) (by decide)
theorem R3179 : ∃ j : ℕ, syracuseStep^[j] 3179 = 1 := reachStep S3179 R4769
theorem S1417 : syracuseStep 1417 = 1063 := stepEq 2 (by norm_num) (by decide)
theorem R1417 : ∃ j : ℕ, syracuseStep^[j] 1417 = 1 := reachStep S1417 R1063
theorem S5669 : syracuseStep 5669 = 1063 := stepEq 4 (by norm_num) (by decide)
theorem R5669 : ∃ j : ℕ, syracuseStep^[j] 5669 = 1 := reachStep S5669 R1063
theorem S5741 : syracuseStep 5741 = 2153 := stepEq 3 (by norm_num) (by decide)
theorem R5741 : ∃ j : ℕ, syracuseStep^[j] 5741 = 1 := reachStep S5741 R2153
theorem S5993 : syracuseStep 5993 = 4495 := stepEq 2 (by norm_num) (by decide)
theorem R5993 : ∃ j : ℕ, syracuseStep^[j] 5993 = 1 := reachStep S5993 R4495
theorem S2119 : syracuseStep 2119 = 3179 := stepEq 1 (by norm_num) (by decide)
theorem R2119 : ∃ j : ℕ, syracuseStep^[j] 2119 = 1 := reachStep S2119 R3179
theorem S263 : syracuseStep 263 = 395 := stepEq 1 (by norm_num) (by decide)
theorem R263 : ∃ j : ℕ, syracuseStep^[j] 263 = 1 := reachStep S263 R395
theorem S527 : syracuseStep 527 = 791 := stepEq 1 (by norm_num) (by decide)
theorem R527 : ∃ j : ℕ, syracuseStep^[j] 527 = 1 := reachStep S527 R791
theorem S31313 : syracuseStep 31313 = 23485 := stepEq 2 (by norm_num) (by decide)
theorem R31313 : ∃ j : ℕ, syracuseStep^[j] 31313 = 1 := reachStep S31313 R23485
theorem S1053 : syracuseStep 1053 = 395 := stepEq 3 (by norm_num) (by decide)
theorem R1053 : ∃ j : ℕ, syracuseStep^[j] 1053 = 1 := reachStep S1053 R395
theorem S1057 : syracuseStep 1057 = 793 := stepEq 2 (by norm_num) (by decide)
theorem R1057 : ∃ j : ℕ, syracuseStep^[j] 1057 = 1 := reachStep S1057 R793
theorem S3779 : syracuseStep 3779 = 5669 := stepEq 1 (by norm_num) (by decide)
theorem R3779 : ∃ j : ℕ, syracuseStep^[j] 3779 = 1 := reachStep S3779 R5669
theorem S3827 : syracuseStep 3827 = 5741 := stepEq 1 (by norm_num) (by decide)
theorem R3827 : ∃ j : ℕ, syracuseStep^[j] 3827 = 1 := reachStep S3827 R5741
theorem S1889 : syracuseStep 1889 = 1417 := stepEq 2 (by norm_num) (by decide)
theorem R1889 : ∃ j : ℕ, syracuseStep^[j] 1889 = 1 := reachStep S1889 R1417
theorem S3995 : syracuseStep 3995 = 5993 := stepEq 1 (by norm_num) (by decide)
theorem R3995 : ∃ j : ℕ, syracuseStep^[j] 3995 = 1 := reachStep S3995 R5993
theorem S175 : syracuseStep 175 = 263 := stepEq 1 (by norm_num) (by decide)
theorem R175 : ∃ j : ℕ, syracuseStep^[j] 175 = 1 := reachStep S175 R263
theorem S351 : syracuseStep 351 = 527 := stepEq 1 (by norm_num) (by decide)
theorem R351 : ∃ j : ℕ, syracuseStep^[j] 351 = 1 := reachStep S351 R527
theorem S2519 : syracuseStep 2519 = 3779 := stepEq 1 (by norm_num) (by decide)
theorem R2519 : ∃ j : ℕ, syracuseStep^[j] 2519 = 1 := reachStep S2519 R3779
theorem S2551 : syracuseStep 2551 = 3827 := stepEq 1 (by norm_num) (by decide)
theorem R2551 : ∃ j : ℕ, syracuseStep^[j] 2551 = 1 := reachStep S2551 R3827
theorem S2663 : syracuseStep 2663 = 3995 := stepEq 1 (by norm_num) (by decide)
theorem R2663 : ∃ j : ℕ, syracuseStep^[j] 2663 = 1 := reachStep S2663 R3995
theorem S701 : syracuseStep 701 = 263 := stepEq 3 (by norm_num) (by decide)
theorem R701 : ∃ j : ℕ, syracuseStep^[j] 701 = 1 := reachStep S701 R263
theorem S2825 : syracuseStep 2825 = 2119 := stepEq 2 (by norm_num) (by decide)
theorem R2825 : ∃ j : ℕ, syracuseStep^[j] 2825 = 1 := reachStep S2825 R2119
theorem S1259 : syracuseStep 1259 = 1889 := stepEq 1 (by norm_num) (by decide)
theorem R1259 : ∃ j : ℕ, syracuseStep^[j] 1259 = 1 := reachStep S1259 R1889
theorem S1409 : syracuseStep 1409 = 1057 := stepEq 2 (by norm_num) (by decide)
theorem R1409 : ∃ j : ℕ, syracuseStep^[j] 1409 = 1 := reachStep S1409 R1057
theorem S83501 : syracuseStep 83501 = 31313 := stepEq 3 (by norm_num) (by decide)
theorem R83501 : ∃ j : ℕ, syracuseStep^[j] 83501 = 1 := reachStep S83501 R31313
theorem S10205 : syracuseStep 10205 = 3827 := stepEq 3 (by norm_num) (by decide)
theorem R10205 : ∃ j : ℕ, syracuseStep^[j] 10205 = 1 := reachStep S10205 R3827
theorem S233 : syracuseStep 233 = 175 := stepEq 2 (by norm_num) (by decide)
theorem R233 : ∃ j : ℕ, syracuseStep^[j] 233 = 1 := reachStep S233 R175
theorem S55667 : syracuseStep 55667 = 83501 := stepEq 1 (by norm_num) (by decide)
theorem R55667 : ∃ j : ℕ, syracuseStep^[j] 55667 = 1 := reachStep S55667 R83501
theorem S467 : syracuseStep 467 = 701 := stepEq 1 (by norm_num) (by decide)
theorem R467 : ∃ j : ℕ, syracuseStep^[j] 467 = 1 := reachStep S467 R701
theorem S6803 : syracuseStep 6803 = 10205 := stepEq 1 (by norm_num) (by decide)
theorem R6803 : ∃ j : ℕ, syracuseStep^[j] 6803 = 1 := reachStep S6803 R10205
theorem S839 : syracuseStep 839 = 1259 := stepEq 1 (by norm_num) (by decide)
theorem R839 : ∃ j : ℕ, syracuseStep^[j] 839 = 1 := reachStep S839 R1259
theorem S933 : syracuseStep 933 = 175 := stepEq 4 (by norm_num) (by decide)
theorem R933 : ∃ j : ℕ, syracuseStep^[j] 933 = 1 := reachStep S933 R175
theorem S939 : syracuseStep 939 = 1409 := stepEq 1 (by norm_num) (by decide)
theorem R939 : ∃ j : ℕ, syracuseStep^[j] 939 = 1 := reachStep S939 R1409
theorem S3401 : syracuseStep 3401 = 2551 := stepEq 2 (by norm_num) (by decide)
theorem R3401 : ∃ j : ℕ, syracuseStep^[j] 3401 = 1 := reachStep S3401 R2551
theorem S1679 : syracuseStep 1679 = 2519 := stepEq 1 (by norm_num) (by decide)
theorem R1679 : ∃ j : ℕ, syracuseStep^[j] 1679 = 1 := reachStep S1679 R2519
theorem S1775 : syracuseStep 1775 = 2663 := stepEq 1 (by norm_num) (by decide)
theorem R1775 : ∃ j : ℕ, syracuseStep^[j] 1775 = 1 := reachStep S1775 R2663
theorem S1883 : syracuseStep 1883 = 2825 := stepEq 1 (by norm_num) (by decide)
theorem R1883 : ∃ j : ℕ, syracuseStep^[j] 1883 = 1 := reachStep S1883 R2825
theorem S155 : syracuseStep 155 = 233 := stepEq 1 (by norm_num) (by decide)
theorem R155 : ∃ j : ℕ, syracuseStep^[j] 155 = 1 := reachStep S155 R233
theorem S2267 : syracuseStep 2267 = 3401 := stepEq 1 (by norm_num) (by decide)
theorem R2267 : ∃ j : ℕ, syracuseStep^[j] 2267 = 1 := reachStep S2267 R3401
theorem S37111 : syracuseStep 37111 = 55667 := stepEq 1 (by norm_num) (by decide)
theorem R37111 : ∃ j : ℕ, syracuseStep^[j] 37111 = 1 := reachStep S37111 R55667
theorem S311 : syracuseStep 311 = 467 := stepEq 1 (by norm_num) (by decide)
theorem R311 : ∃ j : ℕ, syracuseStep^[j] 311 = 1 := reachStep S311 R467
theorem S4535 : syracuseStep 4535 = 6803 := stepEq 1 (by norm_num) (by decide)
theorem R4535 : ∃ j : ℕ, syracuseStep^[j] 4535 = 1 := reachStep S4535 R6803
theorem S559 : syracuseStep 559 = 839 := stepEq 1 (by norm_num) (by decide)
theorem R559 : ∃ j : ℕ, syracuseStep^[j] 559 = 1 := reachStep S559 R839
theorem S621 : syracuseStep 621 = 233 := stepEq 3 (by norm_num) (by decide)
theorem R621 : ∃ j : ℕ, syracuseStep^[j] 621 = 1 := reachStep S621 R233
theorem S5021 : syracuseStep 5021 = 1883 := stepEq 3 (by norm_num) (by decide)
theorem R5021 : ∃ j : ℕ, syracuseStep^[j] 5021 = 1 := reachStep S5021 R1883
theorem S1119 : syracuseStep 1119 = 1679 := stepEq 1 (by norm_num) (by decide)
theorem R1119 : ∃ j : ℕ, syracuseStep^[j] 1119 = 1 := reachStep S1119 R1679
theorem S1183 : syracuseStep 1183 = 1775 := stepEq 1 (by norm_num) (by decide)
theorem R1183 : ∃ j : ℕ, syracuseStep^[j] 1183 = 1 := reachStep S1183 R1775
theorem S1255 : syracuseStep 1255 = 1883 := stepEq 1 (by norm_num) (by decide)
theorem R1255 : ∃ j : ℕ, syracuseStep^[j] 1255 = 1 := reachStep S1255 R1883
theorem S103 : syracuseStep 103 = 155 := stepEq 1 (by norm_num) (by decide)
theorem R103 : ∃ j : ℕ, syracuseStep^[j] 103 = 1 := reachStep S103 R155
theorem S207 : syracuseStep 207 = 311 := stepEq 1 (by norm_num) (by decide)
theorem R207 : ∃ j : ℕ, syracuseStep^[j] 207 = 1 := reachStep S207 R311
theorem S49481 : syracuseStep 49481 = 37111 := stepEq 2 (by norm_num) (by decide)
theorem R49481 : ∃ j : ℕ, syracuseStep^[j] 49481 = 1 := reachStep S49481 R37111
theorem S413 : syracuseStep 413 = 155 := stepEq 3 (by norm_num) (by decide)
theorem R413 : ∃ j : ℕ, syracuseStep^[j] 413 = 1 := reachStep S413 R155
theorem S745 : syracuseStep 745 = 559 := stepEq 2 (by norm_num) (by decide)
theorem R745 : ∃ j : ℕ, syracuseStep^[j] 745 = 1 := reachStep S745 R559
theorem S829 : syracuseStep 829 = 311 := stepEq 3 (by norm_num) (by decide)
theorem R829 : ∃ j : ℕ, syracuseStep^[j] 829 = 1 := reachStep S829 R311
theorem S3023 : syracuseStep 3023 = 4535 := stepEq 1 (by norm_num) (by decide)
theorem R3023 : ∃ j : ℕ, syracuseStep^[j] 3023 = 1 := reachStep S3023 R4535
theorem S3347 : syracuseStep 3347 = 5021 := stepEq 1 (by norm_num) (by decide)
theorem R3347 : ∃ j : ℕ, syracuseStep^[j] 3347 = 1 := reachStep S3347 R5021
theorem S1511 : syracuseStep 1511 = 2267 := stepEq 1 (by norm_num) (by decide)
theorem R1511 : ∃ j : ℕ, syracuseStep^[j] 1511 = 1 := reachStep S1511 R2267
theorem S1577 : syracuseStep 1577 = 1183 := stepEq 2 (by norm_num) (by decide)
theorem R1577 : ∃ j : ℕ, syracuseStep^[j] 1577 = 1 := reachStep S1577 R1183
theorem S1673 : syracuseStep 1673 = 1255 := stepEq 2 (by norm_num) (by decide)
theorem R1673 : ∃ j : ℕ, syracuseStep^[j] 1673 = 1 := reachStep S1673 R1255
theorem S137 : syracuseStep 137 = 103 := stepEq 2 (by norm_num) (by decide)
theorem R137 : ∃ j : ℕ, syracuseStep^[j] 137 = 1 := reachStep S137 R103
theorem S2231 : syracuseStep 2231 = 3347 := stepEq 1 (by norm_num) (by decide)
theorem R2231 : ∃ j : ℕ, syracuseStep^[j] 2231 = 1 := reachStep S2231 R3347
theorem S32987 : syracuseStep 32987 = 49481 := stepEq 1 (by norm_num) (by decide)
theorem R32987 : ∃ j : ℕ, syracuseStep^[j] 32987 = 1 := reachStep S32987 R49481
theorem S275 : syracuseStep 275 = 413 := stepEq 1 (by norm_num) (by decide)
theorem R275 : ∃ j : ℕ, syracuseStep^[j] 275 = 1 := reachStep S275 R413
theorem S549 : syracuseStep 549 = 103 := stepEq 4 (by norm_num) (by decide)
theorem R549 : ∃ j : ℕ, syracuseStep^[j] 549 = 1 := reachStep S549 R103
theorem S993 : syracuseStep 993 = 745 := stepEq 2 (by norm_num) (by decide)
theorem R993 : ∃ j : ℕ, syracuseStep^[j] 993 = 1 := reachStep S993 R745
theorem S1007 : syracuseStep 1007 = 1511 := stepEq 1 (by norm_num) (by decide)
theorem R1007 : ∃ j : ℕ, syracuseStep^[j] 1007 = 1 := reachStep S1007 R1511
theorem S1051 : syracuseStep 1051 = 1577 := stepEq 1 (by norm_num) (by decide)
theorem R1051 : ∃ j : ℕ, syracuseStep^[j] 1051 = 1 := reachStep S1051 R1577
theorem S1101 : syracuseStep 1101 = 413 := stepEq 3 (by norm_num) (by decide)
theorem R1101 : ∃ j : ℕ, syracuseStep^[j] 1101 = 1 := reachStep S1101 R413
theorem S1105 : syracuseStep 1105 = 829 := stepEq 2 (by norm_num) (by decide)
theorem R1105 : ∃ j : ℕ, syracuseStep^[j] 1105 = 1 := reachStep S1105 R829
theorem S1115 : syracuseStep 1115 = 1673 := stepEq 1 (by norm_num) (by decide)
theorem R1115 : ∃ j : ℕ, syracuseStep^[j] 1115 = 1 := reachStep S1115 R1673
theorem S2015 : syracuseStep 2015 = 3023 := stepEq 1 (by norm_num) (by decide)
theorem R2015 : ∃ j : ℕ, syracuseStep^[j] 2015 = 1 := reachStep S2015 R3023
theorem S91 : syracuseStep 91 = 137 := stepEq 1 (by norm_num) (by decide)
theorem R91 : ∃ j : ℕ, syracuseStep^[j] 91 = 1 := reachStep S91 R137
theorem S183 : syracuseStep 183 = 275 := stepEq 1 (by norm_num) (by decide)
theorem R183 : ∃ j : ℕ, syracuseStep^[j] 183 = 1 := reachStep S183 R275
theorem S365 : syracuseStep 365 = 137 := stepEq 3 (by norm_num) (by decide)
theorem R365 : ∃ j : ℕ, syracuseStep^[j] 365 = 1 := reachStep S365 R137
theorem S671 : syracuseStep 671 = 1007 := stepEq 1 (by norm_num) (by decide)
theorem R671 : ∃ j : ℕ, syracuseStep^[j] 671 = 1 := reachStep S671 R1007
theorem S733 : syracuseStep 733 = 275 := stepEq 3 (by norm_num) (by decide)
theorem R733 : ∃ j : ℕ, syracuseStep^[j] 733 = 1 := reachStep S733 R275
theorem S743 : syracuseStep 743 = 1115 := stepEq 1 (by norm_num) (by decide)
theorem R743 : ∃ j : ℕ, syracuseStep^[j] 743 = 1 := reachStep S743 R1115
theorem S1343 : syracuseStep 1343 = 2015 := stepEq 1 (by norm_num) (by decide)
theorem R1343 : ∃ j : ℕ, syracuseStep^[j] 1343 = 1 := reachStep S1343 R2015
theorem S1487 : syracuseStep 1487 = 2231 := stepEq 1 (by norm_num) (by decide)
theorem R1487 : ∃ j : ℕ, syracuseStep^[j] 1487 = 1 := reachStep S1487 R2231
theorem S21991 : syracuseStep 21991 = 32987 := stepEq 1 (by norm_num) (by decide)
theorem R21991 : ∃ j : ℕ, syracuseStep^[j] 21991 = 1 := reachStep S21991 R32987
theorem S121 : syracuseStep 121 = 91 := stepEq 2 (by norm_num) (by decide)
theorem R121 : ∃ j : ℕ, syracuseStep^[j] 121 = 1 := reachStep S121 R91
theorem S243 : syracuseStep 243 = 365 := stepEq 1 (by norm_num) (by decide)
theorem R243 : ∃ j : ℕ, syracuseStep^[j] 243 = 1 := reachStep S243 R365
theorem S447 : syracuseStep 447 = 671 := stepEq 1 (by norm_num) (by decide)
theorem R447 : ∃ j : ℕ, syracuseStep^[j] 447 = 1 := reachStep S447 R671
theorem S485 : syracuseStep 485 = 91 := stepEq 4 (by norm_num) (by decide)
theorem R485 : ∃ j : ℕ, syracuseStep^[j] 485 = 1 := reachStep S485 R91
theorem S495 : syracuseStep 495 = 743 := stepEq 1 (by norm_num) (by decide)
theorem R495 : ∃ j : ℕ, syracuseStep^[j] 495 = 1 := reachStep S495 R743
theorem S29321 : syracuseStep 29321 = 21991 := stepEq 2 (by norm_num) (by decide)
theorem R29321 : ∃ j : ℕ, syracuseStep^[j] 29321 = 1 := reachStep S29321 R21991
theorem S895 : syracuseStep 895 = 1343 := stepEq 1 (by norm_num) (by decide)
theorem R895 : ∃ j : ℕ, syracuseStep^[j] 895 = 1 := reachStep S895 R1343
theorem S973 : syracuseStep 973 = 365 := stepEq 3 (by norm_num) (by decide)
theorem R973 : ∃ j : ℕ, syracuseStep^[j] 973 = 1 := reachStep S973 R365
theorem S977 : syracuseStep 977 = 733 := stepEq 2 (by norm_num) (by decide)
theorem R977 : ∃ j : ℕ, syracuseStep^[j] 977 = 1 := reachStep S977 R733
theorem S991 : syracuseStep 991 = 1487 := stepEq 1 (by norm_num) (by decide)
theorem R991 : ∃ j : ℕ, syracuseStep^[j] 991 = 1 := reachStep S991 R1487
theorem S3893 : syracuseStep 3893 = 365 := stepEq 5 (by norm_num) (by decide)
theorem R3893 : ∃ j : ℕ, syracuseStep^[j] 3893 = 1 := reachStep S3893 R365
theorem S10381 : syracuseStep 10381 = 3893 := stepEq 3 (by norm_num) (by decide)
theorem R10381 : ∃ j : ℕ, syracuseStep^[j] 10381 = 1 := reachStep S10381 R3893
theorem S161 : syracuseStep 161 = 121 := stepEq 2 (by norm_num) (by decide)
theorem R161 : ∃ j : ℕ, syracuseStep^[j] 161 = 1 := reachStep S161 R121
theorem S323 : syracuseStep 323 = 485 := stepEq 1 (by norm_num) (by decide)
theorem R323 : ∃ j : ℕ, syracuseStep^[j] 323 = 1 := reachStep S323 R485
theorem S645 : syracuseStep 645 = 121 := stepEq 4 (by norm_num) (by decide)
theorem R645 : ∃ j : ℕ, syracuseStep^[j] 645 = 1 := reachStep S645 R121
theorem S651 : syracuseStep 651 = 977 := stepEq 1 (by norm_num) (by decide)
theorem R651 : ∃ j : ℕ, syracuseStep^[j] 651 = 1 := reachStep S651 R977
theorem S19547 : syracuseStep 19547 = 29321 := stepEq 1 (by norm_num) (by decide)
theorem R19547 : ∃ j : ℕ, syracuseStep^[j] 19547 = 1 := reachStep S19547 R29321
theorem S5285 : syracuseStep 5285 = 991 := stepEq 4 (by norm_num) (by decide)
theorem R5285 : ∃ j : ℕ, syracuseStep^[j] 5285 = 1 := reachStep S5285 R991
theorem S1193 : syracuseStep 1193 = 895 := stepEq 2 (by norm_num) (by decide)
theorem R1193 : ∃ j : ℕ, syracuseStep^[j] 1193 = 1 := reachStep S1193 R895
theorem S107 : syracuseStep 107 = 161 := stepEq 1 (by norm_num) (by decide)
theorem R107 : ∃ j : ℕ, syracuseStep^[j] 107 = 1 := reachStep S107 R161
theorem S215 : syracuseStep 215 = 323 := stepEq 1 (by norm_num) (by decide)
theorem R215 : ∃ j : ℕ, syracuseStep^[j] 215 = 1 := reachStep S215 R323
theorem S429 : syracuseStep 429 = 161 := stepEq 3 (by norm_num) (by decide)
theorem R429 : ∃ j : ℕ, syracuseStep^[j] 429 = 1 := reachStep S429 R161
theorem S13031 : syracuseStep 13031 = 19547 := stepEq 1 (by norm_num) (by decide)
theorem R13031 : ∃ j : ℕ, syracuseStep^[j] 13031 = 1 := reachStep S13031 R19547
theorem S795 : syracuseStep 795 = 1193 := stepEq 1 (by norm_num) (by decide)
theorem R795 : ∃ j : ℕ, syracuseStep^[j] 795 = 1 := reachStep S795 R1193
theorem S861 : syracuseStep 861 = 323 := stepEq 3 (by norm_num) (by decide)
theorem R861 : ∃ j : ℕ, syracuseStep^[j] 861 = 1 := reachStep S861 R323
theorem S3523 : syracuseStep 3523 = 5285 := stepEq 1 (by norm_num) (by decide)
theorem R3523 : ∃ j : ℕ, syracuseStep^[j] 3523 = 1 := reachStep S3523 R5285
theorem S13841 : syracuseStep 13841 = 10381 := stepEq 2 (by norm_num) (by decide)
theorem R13841 : ∃ j : ℕ, syracuseStep^[j] 13841 = 1 := reachStep S13841 R10381
theorem S71 : syracuseStep 71 = 107 := stepEq 1 (by norm_num) (by decide)
theorem R71 : ∃ j : ℕ, syracuseStep^[j] 71 = 1 := reachStep S71 R107
theorem S143 : syracuseStep 143 = 215 := stepEq 1 (by norm_num) (by decide)
theorem R143 : ∃ j : ℕ, syracuseStep^[j] 143 = 1 := reachStep S143 R215
theorem S285 : syracuseStep 285 = 107 := stepEq 3 (by norm_num) (by decide)
theorem R285 : ∃ j : ℕ, syracuseStep^[j] 285 = 1 := reachStep S285 R107
theorem S8687 : syracuseStep 8687 = 13031 := stepEq 1 (by norm_num) (by decide)
theorem R8687 : ∃ j : ℕ, syracuseStep^[j] 8687 = 1 := reachStep S8687 R13031
theorem S573 : syracuseStep 573 = 215 := stepEq 3 (by norm_num) (by decide)
theorem R573 : ∃ j : ℕ, syracuseStep^[j] 573 = 1 := reachStep S573 R215
theorem S4697 : syracuseStep 4697 = 3523 := stepEq 2 (by norm_num) (by decide)
theorem R4697 : ∃ j : ℕ, syracuseStep^[j] 4697 = 1 := reachStep S4697 R3523
theorem S9227 : syracuseStep 9227 = 13841 := stepEq 1 (by norm_num) (by decide)
theorem R9227 : ∃ j : ℕ, syracuseStep^[j] 9227 = 1 := reachStep S9227 R13841
theorem S1141 : syracuseStep 1141 = 107 := stepEq 5 (by norm_num) (by decide)
theorem R1141 : ∃ j : ℕ, syracuseStep^[j] 1141 = 1 := reachStep S1141 R107
theorem S6151 : syracuseStep 6151 = 9227 := stepEq 1 (by norm_num) (by decide)
theorem R6151 : ∃ j : ℕ, syracuseStep^[j] 6151 = 1 := reachStep S6151 R9227
theorem S47 : syracuseStep 47 = 71 := stepEq 1 (by norm_num) (by decide)
theorem R47 : ∃ j : ℕ, syracuseStep^[j] 47 = 1 := reachStep S47 R71
theorem S95 : syracuseStep 95 = 143 := stepEq 1 (by norm_num) (by decide)
theorem R95 : ∃ j : ℕ, syracuseStep^[j] 95 = 1 := reachStep S95 R143
theorem S189 : syracuseStep 189 = 71 := stepEq 3 (by norm_num) (by decide)
theorem R189 : ∃ j : ℕ, syracuseStep^[j] 189 = 1 := reachStep S189 R71
theorem S381 : syracuseStep 381 = 143 := stepEq 3 (by norm_num) (by decide)
theorem R381 : ∃ j : ℕ, syracuseStep^[j] 381 = 1 := reachStep S381 R143
theorem S757 : syracuseStep 757 = 71 := stepEq 5 (by norm_num) (by decide)
theorem R757 : ∃ j : ℕ, syracuseStep^[j] 757 = 1 := reachStep S757 R71
theorem S3131 : syracuseStep 3131 = 4697 := stepEq 1 (by norm_num) (by decide)
theorem R3131 : ∃ j : ℕ, syracuseStep^[j] 3131 = 1 := reachStep S3131 R4697
theorem S1525 : syracuseStep 1525 = 143 := stepEq 5 (by norm_num) (by decide)
theorem R1525 : ∃ j : ℕ, syracuseStep^[j] 1525 = 1 := reachStep S1525 R143
theorem S5791 : syracuseStep 5791 = 8687 := stepEq 1 (by norm_num) (by decide)
theorem R5791 : ∃ j : ℕ, syracuseStep^[j] 5791 = 1 := reachStep S5791 R8687
theorem S6101 : syracuseStep 6101 = 143 := stepEq 7 (by norm_num) (by decide)
theorem R6101 : ∃ j : ℕ, syracuseStep^[j] 6101 = 1 := reachStep S6101 R143
theorem S8201 : syracuseStep 8201 = 6151 := stepEq 2 (by norm_num) (by decide)
theorem R8201 : ∃ j : ℕ, syracuseStep^[j] 8201 = 1 := reachStep S8201 R6151
theorem S31 : syracuseStep 31 = 47 := stepEq 1 (by norm_num) (by decide)
theorem R31 : ∃ j : ℕ, syracuseStep^[j] 31 = 1 := reachStep S31 R47
theorem S2087 : syracuseStep 2087 = 3131 := stepEq 1 (by norm_num) (by decide)
theorem R2087 : ∃ j : ℕ, syracuseStep^[j] 2087 = 1 := reachStep S2087 R3131
theorem S63 : syracuseStep 63 = 95 := stepEq 1 (by norm_num) (by decide)
theorem R63 : ∃ j : ℕ, syracuseStep^[j] 63 = 1 := reachStep S63 R95
theorem S125 : syracuseStep 125 = 47 := stepEq 3 (by norm_num) (by decide)
theorem R125 : ∃ j : ℕ, syracuseStep^[j] 125 = 1 := reachStep S125 R47
theorem S253 : syracuseStep 253 = 95 := stepEq 3 (by norm_num) (by decide)
theorem R253 : ∃ j : ℕ, syracuseStep^[j] 253 = 1 := reachStep S253 R95
theorem S501 : syracuseStep 501 = 47 := stepEq 5 (by norm_num) (by decide)
theorem R501 : ∃ j : ℕ, syracuseStep^[j] 501 = 1 := reachStep S501 R47
theorem S1009 : syracuseStep 1009 = 757 := stepEq 2 (by norm_num) (by decide)
theorem R1009 : ∃ j : ℕ, syracuseStep^[j] 1009 = 1 := reachStep S1009 R757
theorem S1013 : syracuseStep 1013 = 95 := stepEq 5 (by norm_num) (by decide)
theorem R1013 : ∃ j : ℕ, syracuseStep^[j] 1013 = 1 := reachStep S1013 R95
theorem S7721 : syracuseStep 7721 = 5791 := stepEq 2 (by norm_num) (by decide)
theorem R7721 : ∃ j : ℕ, syracuseStep^[j] 7721 = 1 := reachStep S7721 R5791
theorem S4067 : syracuseStep 4067 = 6101 := stepEq 1 (by norm_num) (by decide)
theorem R4067 : ∃ j : ℕ, syracuseStep^[j] 4067 = 1 := reachStep S4067 R6101
theorem S2033 : syracuseStep 2033 = 1525 := stepEq 2 (by norm_num) (by decide)
theorem R2033 : ∃ j : ℕ, syracuseStep^[j] 2033 = 1 := reachStep S2033 R1525
theorem S41 : syracuseStep 41 = 31 := stepEq 2 (by norm_num) (by decide)
theorem R41 : ∃ j : ℕ, syracuseStep^[j] 41 = 1 := reachStep S41 R31
theorem S83 : syracuseStep 83 = 125 := stepEq 1 (by norm_num) (by decide)
theorem R83 : ∃ j : ℕ, syracuseStep^[j] 83 = 1 := reachStep S83 R125
theorem S165 : syracuseStep 165 = 31 := stepEq 4 (by norm_num) (by decide)
theorem R165 : ∃ j : ℕ, syracuseStep^[j] 165 = 1 := reachStep S165 R31
theorem S333 : syracuseStep 333 = 125 := stepEq 3 (by norm_num) (by decide)
theorem R333 : ∃ j : ℕ, syracuseStep^[j] 333 = 1 := reachStep S333 R125
theorem S337 : syracuseStep 337 = 253 := stepEq 2 (by norm_num) (by decide)
theorem R337 : ∃ j : ℕ, syracuseStep^[j] 337 = 1 := reachStep S337 R253
theorem S2645 : syracuseStep 2645 = 31 := stepEq 8 (by norm_num) (by decide)
theorem R2645 : ∃ j : ℕ, syracuseStep^[j] 2645 = 1 := reachStep S2645 R31
theorem S661 : syracuseStep 661 = 31 := stepEq 6 (by norm_num) (by decide)
theorem R661 : ∃ j : ℕ, syracuseStep^[j] 661 = 1 := reachStep S661 R31
theorem S2711 : syracuseStep 2711 = 4067 := stepEq 1 (by norm_num) (by decide)
theorem R2711 : ∃ j : ℕ, syracuseStep^[j] 2711 = 1 := reachStep S2711 R4067
theorem S675 : syracuseStep 675 = 1013 := stepEq 1 (by norm_num) (by decide)
theorem R675 : ∃ j : ℕ, syracuseStep^[j] 675 = 1 := reachStep S675 R1013
theorem S5147 : syracuseStep 5147 = 7721 := stepEq 1 (by norm_num) (by decide)
theorem R5147 : ∃ j : ℕ, syracuseStep^[j] 5147 = 1 := reachStep S5147 R7721
theorem S1333 : syracuseStep 1333 = 125 := stepEq 5 (by norm_num) (by decide)
theorem R1333 : ∃ j : ℕ, syracuseStep^[j] 1333 = 1 := reachStep S1333 R125
theorem S1349 : syracuseStep 1349 = 253 := stepEq 4 (by norm_num) (by decide)
theorem R1349 : ∃ j : ℕ, syracuseStep^[j] 1349 = 1 := reachStep S1349 R253
theorem S1355 : syracuseStep 1355 = 2033 := stepEq 1 (by norm_num) (by decide)
theorem R1355 : ∃ j : ℕ, syracuseStep^[j] 1355 = 1 := reachStep S1355 R2033
theorem S5467 : syracuseStep 5467 = 8201 := stepEq 1 (by norm_num) (by decide)
theorem R5467 : ∃ j : ℕ, syracuseStep^[j] 5467 = 1 := reachStep S5467 R8201
theorem S1391 : syracuseStep 1391 = 2087 := stepEq 1 (by norm_num) (by decide)
theorem R1391 : ∃ j : ℕ, syracuseStep^[j] 1391 = 1 := reachStep S1391 R2087
theorem S27 : syracuseStep 27 = 41 := stepEq 1 (by norm_num) (by decide)
theorem R27 : ∃ j : ℕ, syracuseStep^[j] 27 = 1 := reachStep S27 R41
theorem S55 : syracuseStep 55 = 83 := stepEq 1 (by norm_num) (by decide)
theorem R55 : ∃ j : ℕ, syracuseStep^[j] 55 = 1 := reachStep S55 R83
theorem S109 : syracuseStep 109 = 41 := stepEq 3 (by norm_num) (by decide)
theorem R109 : ∃ j : ℕ, syracuseStep^[j] 109 = 1 := reachStep S109 R41
theorem S221 : syracuseStep 221 = 83 := stepEq 3 (by norm_num) (by decide)
theorem R221 : ∃ j : ℕ, syracuseStep^[j] 221 = 1 := reachStep S221 R83
theorem S437 : syracuseStep 437 = 41 := stepEq 5 (by norm_num) (by decide)
theorem R437 : ∃ j : ℕ, syracuseStep^[j] 437 = 1 := reachStep S437 R41
theorem S449 : syracuseStep 449 = 337 := stepEq 2 (by norm_num) (by decide)
theorem R449 : ∃ j : ℕ, syracuseStep^[j] 449 = 1 := reachStep S449 R337
theorem S881 : syracuseStep 881 = 661 := stepEq 2 (by norm_num) (by decide)
theorem R881 : ∃ j : ℕ, syracuseStep^[j] 881 = 1 := reachStep S881 R661
theorem S885 : syracuseStep 885 = 83 := stepEq 5 (by norm_num) (by decide)
theorem R885 : ∃ j : ℕ, syracuseStep^[j] 885 = 1 := reachStep S885 R83
theorem S899 : syracuseStep 899 = 1349 := stepEq 1 (by norm_num) (by decide)
theorem R899 : ∃ j : ℕ, syracuseStep^[j] 899 = 1 := reachStep S899 R1349
theorem S903 : syracuseStep 903 = 1355 := stepEq 1 (by norm_num) (by decide)
theorem R903 : ∃ j : ℕ, syracuseStep^[j] 903 = 1 := reachStep S903 R1355
theorem S927 : syracuseStep 927 = 1391 := stepEq 1 (by norm_num) (by decide)
theorem R927 : ∃ j : ℕ, syracuseStep^[j] 927 = 1 := reachStep S927 R1391
theorem S7229 : syracuseStep 7229 = 2711 := stepEq 3 (by norm_num) (by decide)
theorem R7229 : ∃ j : ℕ, syracuseStep^[j] 7229 = 1 := reachStep S7229 R2711
theorem S7289 : syracuseStep 7289 = 5467 := stepEq 2 (by norm_num) (by decide)
theorem R7289 : ∃ j : ℕ, syracuseStep^[j] 7289 = 1 := reachStep S7289 R5467
theorem S3431 : syracuseStep 3431 = 5147 := stepEq 1 (by norm_num) (by decide)
theorem R3431 : ∃ j : ℕ, syracuseStep^[j] 3431 = 1 := reachStep S3431 R5147
theorem S1763 : syracuseStep 1763 = 2645 := stepEq 1 (by norm_num) (by decide)
theorem R1763 : ∃ j : ℕ, syracuseStep^[j] 1763 = 1 := reachStep S1763 R2645
theorem S1777 : syracuseStep 1777 = 1333 := stepEq 2 (by norm_num) (by decide)
theorem R1777 : ∃ j : ℕ, syracuseStep^[j] 1777 = 1 := reachStep S1777 R1333
theorem S73 : syracuseStep 73 = 55 := stepEq 2 (by norm_num) (by decide)
theorem R73 : ∃ j : ℕ, syracuseStep^[j] 73 = 1 := reachStep S73 R55
theorem S145 : syracuseStep 145 = 109 := stepEq 2 (by norm_num) (by decide)
theorem R145 : ∃ j : ℕ, syracuseStep^[j] 145 = 1 := reachStep S145 R109
theorem S147 : syracuseStep 147 = 221 := stepEq 1 (by norm_num) (by decide)
theorem R147 : ∃ j : ℕ, syracuseStep^[j] 147 = 1 := reachStep S147 R221
theorem S2287 : syracuseStep 2287 = 3431 := stepEq 1 (by norm_num) (by decide)
theorem R2287 : ∃ j : ℕ, syracuseStep^[j] 2287 = 1 := reachStep S2287 R3431
theorem S291 : syracuseStep 291 = 437 := stepEq 1 (by norm_num) (by decide)
theorem R291 : ∃ j : ℕ, syracuseStep^[j] 291 = 1 := reachStep S291 R437
theorem S293 : syracuseStep 293 = 55 := stepEq 4 (by norm_num) (by decide)
theorem R293 : ∃ j : ℕ, syracuseStep^[j] 293 = 1 := reachStep S293 R55
theorem S299 : syracuseStep 299 = 449 := stepEq 1 (by norm_num) (by decide)
theorem R299 : ∃ j : ℕ, syracuseStep^[j] 299 = 1 := reachStep S299 R449
theorem S2357 : syracuseStep 2357 = 221 := stepEq 5 (by norm_num) (by decide)
theorem R2357 : ∃ j : ℕ, syracuseStep^[j] 2357 = 1 := reachStep S2357 R221
theorem S2369 : syracuseStep 2369 = 1777 := stepEq 2 (by norm_num) (by decide)
theorem R2369 : ∃ j : ℕ, syracuseStep^[j] 2369 = 1 := reachStep S2369 R1777
theorem S581 : syracuseStep 581 = 109 := stepEq 4 (by norm_num) (by decide)
theorem R581 : ∃ j : ℕ, syracuseStep^[j] 581 = 1 := reachStep S581 R109
theorem S587 : syracuseStep 587 = 881 := stepEq 1 (by norm_num) (by decide)
theorem R587 : ∃ j : ℕ, syracuseStep^[j] 587 = 1 := reachStep S587 R881
theorem S589 : syracuseStep 589 = 221 := stepEq 3 (by norm_num) (by decide)
theorem R589 : ∃ j : ℕ, syracuseStep^[j] 589 = 1 := reachStep S589 R221
theorem S599 : syracuseStep 599 = 899 := stepEq 1 (by norm_num) (by decide)
theorem R599 : ∃ j : ℕ, syracuseStep^[j] 599 = 1 := reachStep S599 R899
theorem S4819 : syracuseStep 4819 = 7229 := stepEq 1 (by norm_num) (by decide)
theorem R4819 : ∃ j : ℕ, syracuseStep^[j] 4819 = 1 := reachStep S4819 R7229
theorem S4859 : syracuseStep 4859 = 7289 := stepEq 1 (by norm_num) (by decide)
theorem R4859 : ∃ j : ℕ, syracuseStep^[j] 4859 = 1 := reachStep S4859 R7289
theorem S1165 : syracuseStep 1165 = 437 := stepEq 3 (by norm_num) (by decide)
theorem R1165 : ∃ j : ℕ, syracuseStep^[j] 1165 = 1 := reachStep S1165 R437
theorem S1173 : syracuseStep 1173 = 55 := stepEq 6 (by norm_num) (by decide)
theorem R1173 : ∃ j : ℕ, syracuseStep^[j] 1173 = 1 := reachStep S1173 R55
theorem S1175 : syracuseStep 1175 = 1763 := stepEq 1 (by norm_num) (by decide)
theorem R1175 : ∃ j : ℕ, syracuseStep^[j] 1175 = 1 := reachStep S1175 R1763
theorem S97 : syracuseStep 97 = 73 := stepEq 2 (by norm_num) (by decide)
theorem R97 : ∃ j : ℕ, syracuseStep^[j] 97 = 1 := reachStep S97 R73
theorem S6317 : syracuseStep 6317 = 2369 := stepEq 3 (by norm_num) (by decide)
theorem R6317 : ∃ j : ℕ, syracuseStep^[j] 6317 = 1 := reachStep S6317 R2369
theorem S193 : syracuseStep 193 = 145 := stepEq 2 (by norm_num) (by decide)
theorem R193 : ∃ j : ℕ, syracuseStep^[j] 193 = 1 := reachStep S193 R145
theorem S195 : syracuseStep 195 = 293 := stepEq 1 (by norm_num) (by decide)
theorem R195 : ∃ j : ℕ, syracuseStep^[j] 195 = 1 := reachStep S195 R293
theorem S199 : syracuseStep 199 = 299 := stepEq 1 (by norm_num) (by decide)
theorem R199 : ∃ j : ℕ, syracuseStep^[j] 199 = 1 := reachStep S199 R299
theorem S6425 : syracuseStep 6425 = 4819 := stepEq 2 (by norm_num) (by decide)
theorem R6425 : ∃ j : ℕ, syracuseStep^[j] 6425 = 1 := reachStep S6425 R4819
theorem S387 : syracuseStep 387 = 581 := stepEq 1 (by norm_num) (by decide)
theorem R387 : ∃ j : ℕ, syracuseStep^[j] 387 = 1 := reachStep S387 R581
theorem S389 : syracuseStep 389 = 73 := stepEq 4 (by norm_num) (by decide)
theorem R389 : ∃ j : ℕ, syracuseStep^[j] 389 = 1 := reachStep S389 R73
theorem S391 : syracuseStep 391 = 587 := stepEq 1 (by norm_num) (by decide)
theorem R391 : ∃ j : ℕ, syracuseStep^[j] 391 = 1 := reachStep S391 R587
theorem S399 : syracuseStep 399 = 599 := stepEq 1 (by norm_num) (by decide)
theorem R399 : ∃ j : ℕ, syracuseStep^[j] 399 = 1 := reachStep S399 R599
theorem S773 : syracuseStep 773 = 145 := stepEq 4 (by norm_num) (by decide)
theorem R773 : ∃ j : ℕ, syracuseStep^[j] 773 = 1 := reachStep S773 R145
theorem S781 : syracuseStep 781 = 293 := stepEq 3 (by norm_num) (by decide)
theorem R781 : ∃ j : ℕ, syracuseStep^[j] 781 = 1 := reachStep S781 R293
theorem S783 : syracuseStep 783 = 1175 := stepEq 1 (by norm_num) (by decide)
theorem R783 : ∃ j : ℕ, syracuseStep^[j] 783 = 1 := reachStep S783 R1175
theorem S785 : syracuseStep 785 = 589 := stepEq 2 (by norm_num) (by decide)
theorem R785 : ∃ j : ℕ, syracuseStep^[j] 785 = 1 := reachStep S785 R589
theorem S797 : syracuseStep 797 = 299 := stepEq 3 (by norm_num) (by decide)
theorem R797 : ∃ j : ℕ, syracuseStep^[j] 797 = 1 := reachStep S797 R299
theorem S3239 : syracuseStep 3239 = 4859 := stepEq 1 (by norm_num) (by decide)
theorem R3239 : ∃ j : ℕ, syracuseStep^[j] 3239 = 1 := reachStep S3239 R4859
theorem S1549 : syracuseStep 1549 = 581 := stepEq 3 (by norm_num) (by decide)
theorem R1549 : ∃ j : ℕ, syracuseStep^[j] 1549 = 1 := reachStep S1549 R581
theorem S1553 : syracuseStep 1553 = 1165 := stepEq 2 (by norm_num) (by decide)
theorem R1553 : ∃ j : ℕ, syracuseStep^[j] 1553 = 1 := reachStep S1553 R1165
theorem S1565 : syracuseStep 1565 = 587 := stepEq 3 (by norm_num) (by decide)
theorem R1565 : ∃ j : ℕ, syracuseStep^[j] 1565 = 1 := reachStep S1565 R587
theorem S1571 : syracuseStep 1571 = 2357 := stepEq 1 (by norm_num) (by decide)
theorem R1571 : ∃ j : ℕ, syracuseStep^[j] 1571 = 1 := reachStep S1571 R2357
theorem S1579 : syracuseStep 1579 = 2369 := stepEq 1 (by norm_num) (by decide)
theorem R1579 : ∃ j : ℕ, syracuseStep^[j] 1579 = 1 := reachStep S1579 R2369
theorem S12197 : syracuseStep 12197 = 2287 := stepEq 4 (by norm_num) (by decide)
theorem R12197 : ∃ j : ℕ, syracuseStep^[j] 12197 = 1 := reachStep S12197 R2287
theorem S2065 : syracuseStep 2065 = 1549 := stepEq 2 (by norm_num) (by decide)
theorem R2065 : ∃ j : ℕ, syracuseStep^[j] 2065 = 1 := reachStep S2065 R1549
theorem S2069 : syracuseStep 2069 = 97 := stepEq 6 (by norm_num) (by decide)
theorem R2069 : ∃ j : ℕ, syracuseStep^[j] 2069 = 1 := reachStep S2069 R97
theorem S2105 : syracuseStep 2105 = 1579 := stepEq 2 (by norm_num) (by decide)
theorem R2105 : ∃ j : ℕ, syracuseStep^[j] 2105 = 1 := reachStep S2105 R1579
theorem S8261 : syracuseStep 8261 = 1549 := stepEq 4 (by norm_num) (by decide)
theorem R8261 : ∃ j : ℕ, syracuseStep^[j] 8261 = 1 := reachStep S8261 R1549
theorem S2125 : syracuseStep 2125 = 797 := stepEq 3 (by norm_num) (by decide)
theorem R2125 : ∃ j : ℕ, syracuseStep^[j] 2125 = 1 := reachStep S2125 R797
theorem S2159 : syracuseStep 2159 = 3239 := stepEq 1 (by norm_num) (by decide)
theorem R2159 : ∃ j : ℕ, syracuseStep^[j] 2159 = 1 := reachStep S2159 R3239
theorem S4211 : syracuseStep 4211 = 6317 := stepEq 1 (by norm_num) (by decide)
theorem R4211 : ∃ j : ℕ, syracuseStep^[j] 4211 = 1 := reachStep S4211 R6317
theorem S129 : syracuseStep 129 = 97 := stepEq 2 (by norm_num) (by decide)
theorem R129 : ∃ j : ℕ, syracuseStep^[j] 129 = 1 := reachStep S129 R97
theorem S4283 : syracuseStep 4283 = 6425 := stepEq 1 (by norm_num) (by decide)
theorem R4283 : ∃ j : ℕ, syracuseStep^[j] 4283 = 1 := reachStep S4283 R6425
theorem S257 : syracuseStep 257 = 193 := stepEq 2 (by norm_num) (by decide)
theorem R257 : ∃ j : ℕ, syracuseStep^[j] 257 = 1 := reachStep S257 R193
theorem S259 : syracuseStep 259 = 389 := stepEq 1 (by norm_num) (by decide)
theorem R259 : ∃ j : ℕ, syracuseStep^[j] 259 = 1 := reachStep S259 R389
theorem S265 : syracuseStep 265 = 199 := stepEq 2 (by norm_num) (by decide)
theorem R265 : ∃ j : ℕ, syracuseStep^[j] 265 = 1 := reachStep S265 R199
theorem S515 : syracuseStep 515 = 773 := stepEq 1 (by norm_num) (by decide)
theorem R515 : ∃ j : ℕ, syracuseStep^[j] 515 = 1 := reachStep S515 R773
theorem S517 : syracuseStep 517 = 97 := stepEq 4 (by norm_num) (by decide)
theorem R517 : ∃ j : ℕ, syracuseStep^[j] 517 = 1 := reachStep S517 R97
theorem S521 : syracuseStep 521 = 391 := stepEq 2 (by norm_num) (by decide)
theorem R521 : ∃ j : ℕ, syracuseStep^[j] 521 = 1 := reachStep S521 R391
theorem S523 : syracuseStep 523 = 785 := stepEq 1 (by norm_num) (by decide)
theorem R523 : ∃ j : ℕ, syracuseStep^[j] 523 = 1 := reachStep S523 R785
theorem S531 : syracuseStep 531 = 797 := stepEq 1 (by norm_num) (by decide)
theorem R531 : ∃ j : ℕ, syracuseStep^[j] 531 = 1 := reachStep S531 R797
theorem S1029 : syracuseStep 1029 = 193 := stepEq 4 (by norm_num) (by decide)
theorem R1029 : ∃ j : ℕ, syracuseStep^[j] 1029 = 1 := reachStep S1029 R193
theorem S1035 : syracuseStep 1035 = 1553 := stepEq 1 (by norm_num) (by decide)
theorem R1035 : ∃ j : ℕ, syracuseStep^[j] 1035 = 1 := reachStep S1035 R1553
theorem S1037 : syracuseStep 1037 = 389 := stepEq 3 (by norm_num) (by decide)
theorem R1037 : ∃ j : ℕ, syracuseStep^[j] 1037 = 1 := reachStep S1037 R389
theorem S1041 : syracuseStep 1041 = 781 := stepEq 2 (by norm_num) (by decide)
theorem R1041 : ∃ j : ℕ, syracuseStep^[j] 1041 = 1 := reachStep S1041 R781
theorem S1043 : syracuseStep 1043 = 1565 := stepEq 1 (by norm_num) (by decide)
theorem R1043 : ∃ j : ℕ, syracuseStep^[j] 1043 = 1 := reachStep S1043 R1565
theorem S1047 : syracuseStep 1047 = 1571 := stepEq 1 (by norm_num) (by decide)
theorem R1047 : ∃ j : ℕ, syracuseStep^[j] 1047 = 1 := reachStep S1047 R1571
theorem S1061 : syracuseStep 1061 = 199 := stepEq 4 (by norm_num) (by decide)
theorem R1061 : ∃ j : ℕ, syracuseStep^[j] 1061 = 1 := reachStep S1061 R199
theorem S32525 : syracuseStep 32525 = 12197 := stepEq 3 (by norm_num) (by decide)
theorem R32525 : ∃ j : ℕ, syracuseStep^[j] 32525 = 1 := reachStep S32525 R12197
theorem S171 : syracuseStep 171 = 257 := stepEq 1 (by norm_num) (by decide)
theorem R171 : ∃ j : ℕ, syracuseStep^[j] 171 = 1 := reachStep S171 R257
theorem S343 : syracuseStep 343 = 515 := stepEq 1 (by norm_num) (by decide)
theorem R343 : ∃ j : ℕ, syracuseStep^[j] 343 = 1 := reachStep S343 R515
theorem S345 : syracuseStep 345 = 259 := stepEq 2 (by norm_num) (by decide)
theorem R345 : ∃ j : ℕ, syracuseStep^[j] 345 = 1 := reachStep S345 R259
theorem S347 : syracuseStep 347 = 521 := stepEq 1 (by norm_num) (by decide)
theorem R347 : ∃ j : ℕ, syracuseStep^[j] 347 = 1 := reachStep S347 R521
theorem S353 : syracuseStep 353 = 265 := stepEq 2 (by norm_num) (by decide)
theorem R353 : ∃ j : ℕ, syracuseStep^[j] 353 = 1 := reachStep S353 R265
theorem S685 : syracuseStep 685 = 257 := stepEq 3 (by norm_num) (by decide)
theorem R685 : ∃ j : ℕ, syracuseStep^[j] 685 = 1 := reachStep S685 R257
theorem S689 : syracuseStep 689 = 517 := stepEq 2 (by norm_num) (by decide)
theorem R689 : ∃ j : ℕ, syracuseStep^[j] 689 = 1 := reachStep S689 R517
theorem S691 : syracuseStep 691 = 1037 := stepEq 1 (by norm_num) (by decide)
theorem R691 : ∃ j : ℕ, syracuseStep^[j] 691 = 1 := reachStep S691 R1037
theorem S695 : syracuseStep 695 = 1043 := stepEq 1 (by norm_num) (by decide)
theorem R695 : ∃ j : ℕ, syracuseStep^[j] 695 = 1 := reachStep S695 R1043
theorem S697 : syracuseStep 697 = 523 := stepEq 2 (by norm_num) (by decide)
theorem R697 : ∃ j : ℕ, syracuseStep^[j] 697 = 1 := reachStep S697 R523
theorem S2753 : syracuseStep 2753 = 2065 := stepEq 2 (by norm_num) (by decide)
theorem R2753 : ∃ j : ℕ, syracuseStep^[j] 2753 = 1 := reachStep S2753 R2065
theorem S707 : syracuseStep 707 = 1061 := stepEq 1 (by norm_num) (by decide)
theorem R707 : ∃ j : ℕ, syracuseStep^[j] 707 = 1 := reachStep S707 R1061
theorem S2807 : syracuseStep 2807 = 4211 := stepEq 1 (by norm_num) (by decide)
theorem R2807 : ∃ j : ℕ, syracuseStep^[j] 2807 = 1 := reachStep S2807 R4211
theorem S2855 : syracuseStep 2855 = 4283 := stepEq 1 (by norm_num) (by decide)
theorem R2855 : ∃ j : ℕ, syracuseStep^[j] 2855 = 1 := reachStep S2855 R4283
theorem S11333 : syracuseStep 11333 = 2125 := stepEq 4 (by norm_num) (by decide)
theorem R11333 : ∃ j : ℕ, syracuseStep^[j] 11333 = 1 := reachStep S11333 R2125
theorem S21683 : syracuseStep 21683 = 32525 := stepEq 1 (by norm_num) (by decide)
theorem R21683 : ∃ j : ℕ, syracuseStep^[j] 21683 = 1 := reachStep S21683 R32525
theorem S1373 : syracuseStep 1373 = 515 := stepEq 3 (by norm_num) (by decide)
theorem R1373 : ∃ j : ℕ, syracuseStep^[j] 1373 = 1 := reachStep S1373 R515
theorem S1379 : syracuseStep 1379 = 2069 := stepEq 1 (by norm_num) (by decide)
theorem R1379 : ∃ j : ℕ, syracuseStep^[j] 1379 = 1 := reachStep S1379 R2069
theorem S1403 : syracuseStep 1403 = 2105 := stepEq 1 (by norm_num) (by decide)
theorem R1403 : ∃ j : ℕ, syracuseStep^[j] 1403 = 1 := reachStep S1403 R2105
theorem S5507 : syracuseStep 5507 = 8261 := stepEq 1 (by norm_num) (by decide)
theorem R5507 : ∃ j : ℕ, syracuseStep^[j] 5507 = 1 := reachStep S5507 R8261
theorem S1439 : syracuseStep 1439 = 2159 := stepEq 1 (by norm_num) (by decide)
theorem R1439 : ∃ j : ℕ, syracuseStep^[j] 1439 = 1 := reachStep S1439 R2159
theorem S14455 : syracuseStep 14455 = 21683 := stepEq 1 (by norm_num) (by decide)
theorem R14455 : ∃ j : ℕ, syracuseStep^[j] 14455 = 1 := reachStep S14455 R21683
theorem S231 : syracuseStep 231 = 347 := stepEq 1 (by norm_num) (by decide)
theorem R231 : ∃ j : ℕ, syracuseStep^[j] 231 = 1 := reachStep S231 R347
theorem S235 : syracuseStep 235 = 353 := stepEq 1 (by norm_num) (by decide)
theorem R235 : ∃ j : ℕ, syracuseStep^[j] 235 = 1 := reachStep S235 R353
theorem S457 : syracuseStep 457 = 343 := stepEq 2 (by norm_num) (by decide)
theorem R457 : ∃ j : ℕ, syracuseStep^[j] 457 = 1 := reachStep S457 R343
theorem S459 : syracuseStep 459 = 689 := stepEq 1 (by norm_num) (by decide)
theorem R459 : ∃ j : ℕ, syracuseStep^[j] 459 = 1 := reachStep S459 R689
theorem S463 : syracuseStep 463 = 695 := stepEq 1 (by norm_num) (by decide)
theorem R463 : ∃ j : ℕ, syracuseStep^[j] 463 = 1 := reachStep S463 R695
theorem S471 : syracuseStep 471 = 707 := stepEq 1 (by norm_num) (by decide)
theorem R471 : ∃ j : ℕ, syracuseStep^[j] 471 = 1 := reachStep S471 R707
theorem S913 : syracuseStep 913 = 685 := stepEq 2 (by norm_num) (by decide)
theorem R913 : ∃ j : ℕ, syracuseStep^[j] 913 = 1 := reachStep S913 R685
theorem S915 : syracuseStep 915 = 1373 := stepEq 1 (by norm_num) (by decide)
theorem R915 : ∃ j : ℕ, syracuseStep^[j] 915 = 1 := reachStep S915 R1373
theorem S919 : syracuseStep 919 = 1379 := stepEq 1 (by norm_num) (by decide)
theorem R919 : ∃ j : ℕ, syracuseStep^[j] 919 = 1 := reachStep S919 R1379
theorem S921 : syracuseStep 921 = 691 := stepEq 2 (by norm_num) (by decide)
theorem R921 : ∃ j : ℕ, syracuseStep^[j] 921 = 1 := reachStep S921 R691
theorem S925 : syracuseStep 925 = 347 := stepEq 3 (by norm_num) (by decide)
theorem R925 : ∃ j : ℕ, syracuseStep^[j] 925 = 1 := reachStep S925 R347
theorem S929 : syracuseStep 929 = 697 := stepEq 2 (by norm_num) (by decide)
theorem R929 : ∃ j : ℕ, syracuseStep^[j] 929 = 1 := reachStep S929 R697
theorem S935 : syracuseStep 935 = 1403 := stepEq 1 (by norm_num) (by decide)
theorem R935 : ∃ j : ℕ, syracuseStep^[j] 935 = 1 := reachStep S935 R1403
theorem S941 : syracuseStep 941 = 353 := stepEq 3 (by norm_num) (by decide)
theorem R941 : ∃ j : ℕ, syracuseStep^[j] 941 = 1 := reachStep S941 R353
theorem S959 : syracuseStep 959 = 1439 := stepEq 1 (by norm_num) (by decide)
theorem R959 : ∃ j : ℕ, syracuseStep^[j] 959 = 1 := reachStep S959 R1439
theorem S7555 : syracuseStep 7555 = 11333 := stepEq 1 (by norm_num) (by decide)
theorem R7555 : ∃ j : ℕ, syracuseStep^[j] 7555 = 1 := reachStep S7555 R11333
theorem S3671 : syracuseStep 3671 = 5507 := stepEq 1 (by norm_num) (by decide)
theorem R3671 : ∃ j : ℕ, syracuseStep^[j] 3671 = 1 := reachStep S3671 R5507
theorem S1829 : syracuseStep 1829 = 343 := stepEq 4 (by norm_num) (by decide)
theorem R1829 : ∃ j : ℕ, syracuseStep^[j] 1829 = 1 := reachStep S1829 R343
theorem S1835 : syracuseStep 1835 = 2753 := stepEq 1 (by norm_num) (by decide)
theorem R1835 : ∃ j : ℕ, syracuseStep^[j] 1835 = 1 := reachStep S1835 R2753
theorem S1853 : syracuseStep 1853 = 695 := stepEq 3 (by norm_num) (by decide)
theorem R1853 : ∃ j : ℕ, syracuseStep^[j] 1853 = 1 := reachStep S1853 R695
theorem S1871 : syracuseStep 1871 = 2807 := stepEq 1 (by norm_num) (by decide)
theorem R1871 : ∃ j : ℕ, syracuseStep^[j] 1871 = 1 := reachStep S1871 R2807
theorem S1903 : syracuseStep 1903 = 2855 := stepEq 1 (by norm_num) (by decide)
theorem R1903 : ∃ j : ℕ, syracuseStep^[j] 1903 = 1 := reachStep S1903 R2855
theorem S313 : syracuseStep 313 = 235 := stepEq 2 (by norm_num) (by decide)
theorem R313 : ∃ j : ℕ, syracuseStep^[j] 313 = 1 := reachStep S313 R235
theorem S2447 : syracuseStep 2447 = 3671 := stepEq 1 (by norm_num) (by decide)
theorem R2447 : ∃ j : ℕ, syracuseStep^[j] 2447 = 1 := reachStep S2447 R3671
theorem S2537 : syracuseStep 2537 = 1903 := stepEq 2 (by norm_num) (by decide)
theorem R2537 : ∃ j : ℕ, syracuseStep^[j] 2537 = 1 := reachStep S2537 R1903
theorem S609 : syracuseStep 609 = 457 := stepEq 2 (by norm_num) (by decide)
theorem R609 : ∃ j : ℕ, syracuseStep^[j] 609 = 1 := reachStep S609 R457
theorem S617 : syracuseStep 617 = 463 := stepEq 2 (by norm_num) (by decide)
theorem R617 : ∃ j : ℕ, syracuseStep^[j] 617 = 1 := reachStep S617 R463
theorem S619 : syracuseStep 619 = 929 := stepEq 1 (by norm_num) (by decide)
theorem R619 : ∃ j : ℕ, syracuseStep^[j] 619 = 1 := reachStep S619 R929
theorem S623 : syracuseStep 623 = 935 := stepEq 1 (by norm_num) (by decide)
theorem R623 : ∃ j : ℕ, syracuseStep^[j] 623 = 1 := reachStep S623 R935
theorem S627 : syracuseStep 627 = 941 := stepEq 1 (by norm_num) (by decide)
theorem R627 : ∃ j : ℕ, syracuseStep^[j] 627 = 1 := reachStep S627 R941
theorem S639 : syracuseStep 639 = 959 := stepEq 1 (by norm_num) (by decide)
theorem R639 : ∃ j : ℕ, syracuseStep^[j] 639 = 1 := reachStep S639 R959
theorem S19273 : syracuseStep 19273 = 14455 := stepEq 2 (by norm_num) (by decide)
theorem R19273 : ∃ j : ℕ, syracuseStep^[j] 19273 = 1 := reachStep S19273 R14455
theorem S1217 : syracuseStep 1217 = 913 := stepEq 2 (by norm_num) (by decide)
theorem R1217 : ∃ j : ℕ, syracuseStep^[j] 1217 = 1 := reachStep S1217 R913
theorem S1219 : syracuseStep 1219 = 1829 := stepEq 1 (by norm_num) (by decide)
theorem R1219 : ∃ j : ℕ, syracuseStep^[j] 1219 = 1 := reachStep S1219 R1829
theorem S1223 : syracuseStep 1223 = 1835 := stepEq 1 (by norm_num) (by decide)
theorem R1223 : ∃ j : ℕ, syracuseStep^[j] 1223 = 1 := reachStep S1223 R1835
theorem S1225 : syracuseStep 1225 = 919 := stepEq 2 (by norm_num) (by decide)
theorem R1225 : ∃ j : ℕ, syracuseStep^[j] 1225 = 1 := reachStep S1225 R919
theorem S1235 : syracuseStep 1235 = 1853 := stepEq 1 (by norm_num) (by decide)
theorem R1235 : ∃ j : ℕ, syracuseStep^[j] 1235 = 1 := reachStep S1235 R1853
theorem S1247 : syracuseStep 1247 = 1871 := stepEq 1 (by norm_num) (by decide)
theorem R1247 : ∃ j : ℕ, syracuseStep^[j] 1247 = 1 := reachStep S1247 R1871
theorem S1253 : syracuseStep 1253 = 235 := stepEq 4 (by norm_num) (by decide)
theorem R1253 : ∃ j : ℕ, syracuseStep^[j] 1253 = 1 := reachStep S1253 R235
theorem S10073 : syracuseStep 10073 = 7555 := stepEq 2 (by norm_num) (by decide)
theorem R10073 : ∃ j : ℕ, syracuseStep^[j] 10073 = 1 := reachStep S10073 R7555
theorem S411 : syracuseStep 411 = 617 := stepEq 1 (by norm_num) (by decide)
theorem R411 : ∃ j : ℕ, syracuseStep^[j] 411 = 1 := reachStep S411 R617
theorem S415 : syracuseStep 415 = 623 := stepEq 1 (by norm_num) (by decide)
theorem R415 : ∃ j : ℕ, syracuseStep^[j] 415 = 1 := reachStep S415 R623
theorem S417 : syracuseStep 417 = 313 := stepEq 2 (by norm_num) (by decide)
theorem R417 : ∃ j : ℕ, syracuseStep^[j] 417 = 1 := reachStep S417 R313
theorem S6715 : syracuseStep 6715 = 10073 := stepEq 1 (by norm_num) (by decide)
theorem R6715 : ∃ j : ℕ, syracuseStep^[j] 6715 = 1 := reachStep S6715 R10073
theorem S811 : syracuseStep 811 = 1217 := stepEq 1 (by norm_num) (by decide)
theorem R811 : ∃ j : ℕ, syracuseStep^[j] 811 = 1 := reachStep S811 R1217
theorem S815 : syracuseStep 815 = 1223 := stepEq 1 (by norm_num) (by decide)
theorem R815 : ∃ j : ℕ, syracuseStep^[j] 815 = 1 := reachStep S815 R1223
theorem S823 : syracuseStep 823 = 1235 := stepEq 1 (by norm_num) (by decide)
theorem R823 : ∃ j : ℕ, syracuseStep^[j] 823 = 1 := reachStep S823 R1235
theorem S825 : syracuseStep 825 = 619 := stepEq 2 (by norm_num) (by decide)
theorem R825 : ∃ j : ℕ, syracuseStep^[j] 825 = 1 := reachStep S825 R619
theorem S831 : syracuseStep 831 = 1247 := stepEq 1 (by norm_num) (by decide)
theorem R831 : ∃ j : ℕ, syracuseStep^[j] 831 = 1 := reachStep S831 R1247
theorem S835 : syracuseStep 835 = 1253 := stepEq 1 (by norm_num) (by decide)
theorem R835 : ∃ j : ℕ, syracuseStep^[j] 835 = 1 := reachStep S835 R1253
theorem S25697 : syracuseStep 25697 = 19273 := stepEq 2 (by norm_num) (by decide)
theorem R25697 : ∃ j : ℕ, syracuseStep^[j] 25697 = 1 := reachStep S25697 R19273
theorem S3293 : syracuseStep 3293 = 1235 := stepEq 3 (by norm_num) (by decide)
theorem R3293 : ∃ j : ℕ, syracuseStep^[j] 3293 = 1 := reachStep S3293 R1235
theorem S3341 : syracuseStep 3341 = 1253 := stepEq 3 (by norm_num) (by decide)
theorem R3341 : ∃ j : ℕ, syracuseStep^[j] 3341 = 1 := reachStep S3341 R1253
theorem S1625 : syracuseStep 1625 = 1219 := stepEq 2 (by norm_num) (by decide)
theorem R1625 : ∃ j : ℕ, syracuseStep^[j] 1625 = 1 := reachStep S1625 R1219
theorem S1631 : syracuseStep 1631 = 2447 := stepEq 1 (by norm_num) (by decide)
theorem R1631 : ∃ j : ℕ, syracuseStep^[j] 1631 = 1 := reachStep S1631 R2447
theorem S1633 : syracuseStep 1633 = 1225 := stepEq 2 (by norm_num) (by decide)
theorem R1633 : ∃ j : ℕ, syracuseStep^[j] 1633 = 1 := reachStep S1633 R1225
theorem S1661 : syracuseStep 1661 = 623 := stepEq 3 (by norm_num) (by decide)
theorem R1661 : ∃ j : ℕ, syracuseStep^[j] 1661 = 1 := reachStep S1661 R623
theorem S1691 : syracuseStep 1691 = 2537 := stepEq 1 (by norm_num) (by decide)
theorem R1691 : ∃ j : ℕ, syracuseStep^[j] 1691 = 1 := reachStep S1691 R2537
theorem S2177 : syracuseStep 2177 = 1633 := stepEq 2 (by norm_num) (by decide)
theorem R2177 : ∃ j : ℕ, syracuseStep^[j] 2177 = 1 := reachStep S2177 R1633
theorem S2195 : syracuseStep 2195 = 3293 := stepEq 1 (by norm_num) (by decide)
theorem R2195 : ∃ j : ℕ, syracuseStep^[j] 2195 = 1 := reachStep S2195 R3293
theorem S2213 : syracuseStep 2213 = 415 := stepEq 4 (by norm_num) (by decide)
theorem R2213 : ∃ j : ℕ, syracuseStep^[j] 2213 = 1 := reachStep S2213 R415
theorem S2227 : syracuseStep 2227 = 3341 := stepEq 1 (by norm_num) (by decide)
theorem R2227 : ∃ j : ℕ, syracuseStep^[j] 2227 = 1 := reachStep S2227 R3341
theorem S543 : syracuseStep 543 = 815 := stepEq 1 (by norm_num) (by decide)
theorem R543 : ∃ j : ℕ, syracuseStep^[j] 543 = 1 := reachStep S543 R815
theorem S553 : syracuseStep 553 = 415 := stepEq 2 (by norm_num) (by decide)
theorem R553 : ∃ j : ℕ, syracuseStep^[j] 553 = 1 := reachStep S553 R415
theorem S17131 : syracuseStep 17131 = 25697 := stepEq 1 (by norm_num) (by decide)
theorem R17131 : ∃ j : ℕ, syracuseStep^[j] 17131 = 1 := reachStep S17131 R25697
theorem S8953 : syracuseStep 8953 = 6715 := stepEq 2 (by norm_num) (by decide)
theorem R8953 : ∃ j : ℕ, syracuseStep^[j] 8953 = 1 := reachStep S8953 R6715
theorem S1081 : syracuseStep 1081 = 811 := stepEq 2 (by norm_num) (by decide)
theorem R1081 : ∃ j : ℕ, syracuseStep^[j] 1081 = 1 := reachStep S1081 R811
theorem S1083 : syracuseStep 1083 = 1625 := stepEq 1 (by norm_num) (by decide)
theorem R1083 : ∃ j : ℕ, syracuseStep^[j] 1083 = 1 := reachStep S1083 R1625
theorem S1087 : syracuseStep 1087 = 1631 := stepEq 1 (by norm_num) (by decide)
theorem R1087 : ∃ j : ℕ, syracuseStep^[j] 1087 = 1 := reachStep S1087 R1631
theorem S1097 : syracuseStep 1097 = 823 := stepEq 2 (by norm_num) (by decide)
theorem R1097 : ∃ j : ℕ, syracuseStep^[j] 1097 = 1 := reachStep S1097 R823
theorem S1107 : syracuseStep 1107 = 1661 := stepEq 1 (by norm_num) (by decide)
theorem R1107 : ∃ j : ℕ, syracuseStep^[j] 1107 = 1 := reachStep S1107 R1661
theorem S1113 : syracuseStep 1113 = 835 := stepEq 2 (by norm_num) (by decide)
theorem R1113 : ∃ j : ℕ, syracuseStep^[j] 1113 = 1 := reachStep S1113 R835
theorem S1127 : syracuseStep 1127 = 1691 := stepEq 1 (by norm_num) (by decide)
theorem R1127 : ∃ j : ℕ, syracuseStep^[j] 1127 = 1 := reachStep S1127 R1691
theorem S22841 : syracuseStep 22841 = 17131 := stepEq 2 (by norm_num) (by decide)
theorem R22841 : ∃ j : ℕ, syracuseStep^[j] 22841 = 1 := reachStep S22841 R17131
theorem S47749 : syracuseStep 47749 = 8953 := stepEq 4 (by norm_num) (by decide)
theorem R47749 : ∃ j : ℕ, syracuseStep^[j] 47749 = 1 := reachStep S47749 R8953
theorem S731 : syracuseStep 731 = 1097 := stepEq 1 (by norm_num) (by decide)
theorem R731 : ∃ j : ℕ, syracuseStep^[j] 731 = 1 := reachStep S731 R1097
theorem S737 : syracuseStep 737 = 553 := stepEq 2 (by norm_num) (by decide)
theorem R737 : ∃ j : ℕ, syracuseStep^[j] 737 = 1 := reachStep S737 R553
theorem S751 : syracuseStep 751 = 1127 := stepEq 1 (by norm_num) (by decide)
theorem R751 : ∃ j : ℕ, syracuseStep^[j] 751 = 1 := reachStep S751 R1127
theorem S2969 : syracuseStep 2969 = 2227 := stepEq 2 (by norm_num) (by decide)
theorem R2969 : ∃ j : ℕ, syracuseStep^[j] 2969 = 1 := reachStep S2969 R2227
theorem S1451 : syracuseStep 1451 = 2177 := stepEq 1 (by norm_num) (by decide)
theorem R1451 : ∃ j : ℕ, syracuseStep^[j] 1451 = 1 := reachStep S1451 R2177
theorem S1463 : syracuseStep 1463 = 2195 := stepEq 1 (by norm_num) (by decide)
theorem R1463 : ∃ j : ℕ, syracuseStep^[j] 1463 = 1 := reachStep S1463 R2195
theorem S1475 : syracuseStep 1475 = 2213 := stepEq 1 (by norm_num) (by decide)
theorem R1475 : ∃ j : ℕ, syracuseStep^[j] 1475 = 1 := reachStep S1475 R2213
theorem S63665 : syracuseStep 63665 = 47749 := stepEq 2 (by norm_num) (by decide)
theorem R63665 : ∃ j : ℕ, syracuseStep^[j] 63665 = 1 := reachStep S63665 R47749
theorem S487 : syracuseStep 487 = 731 := stepEq 1 (by norm_num) (by decide)
theorem R487 : ∃ j : ℕ, syracuseStep^[j] 487 = 1 := reachStep S487 R731
theorem S491 : syracuseStep 491 = 737 := stepEq 1 (by norm_num) (by decide)
theorem R491 : ∃ j : ℕ, syracuseStep^[j] 491 = 1 := reachStep S491 R737
theorem S15227 : syracuseStep 15227 = 22841 := stepEq 1 (by norm_num) (by decide)
theorem R15227 : ∃ j : ℕ, syracuseStep^[j] 15227 = 1 := reachStep S15227 R22841
theorem S967 : syracuseStep 967 = 1451 := stepEq 1 (by norm_num) (by decide)
theorem R967 : ∃ j : ℕ, syracuseStep^[j] 967 = 1 := reachStep S967 R1451
theorem S975 : syracuseStep 975 = 1463 := stepEq 1 (by norm_num) (by decide)
theorem R975 : ∃ j : ℕ, syracuseStep^[j] 975 = 1 := reachStep S975 R1463
theorem S983 : syracuseStep 983 = 1475 := stepEq 1 (by norm_num) (by decide)
theorem R983 : ∃ j : ℕ, syracuseStep^[j] 983 = 1 := reachStep S983 R1475
theorem S1001 : syracuseStep 1001 = 751 := stepEq 2 (by norm_num) (by decide)
theorem R1001 : ∃ j : ℕ, syracuseStep^[j] 1001 = 1 := reachStep S1001 R751
theorem S1979 : syracuseStep 1979 = 2969 := stepEq 1 (by norm_num) (by decide)
theorem R1979 : ∃ j : ℕ, syracuseStep^[j] 1979 = 1 := reachStep S1979 R2969
theorem S327 : syracuseStep 327 = 491 := stepEq 1 (by norm_num) (by decide)
theorem R327 : ∃ j : ℕ, syracuseStep^[j] 327 = 1 := reachStep S327 R491
theorem S649 : syracuseStep 649 = 487 := stepEq 2 (by norm_num) (by decide)
theorem R649 : ∃ j : ℕ, syracuseStep^[j] 649 = 1 := reachStep S649 R487
theorem S655 : syracuseStep 655 = 983 := stepEq 1 (by norm_num) (by decide)
theorem R655 : ∃ j : ℕ, syracuseStep^[j] 655 = 1 := reachStep S655 R983
theorem S667 : syracuseStep 667 = 1001 := stepEq 1 (by norm_num) (by decide)
theorem R667 : ∃ j : ℕ, syracuseStep^[j] 667 = 1 := reachStep S667 R1001
theorem S1289 : syracuseStep 1289 = 967 := stepEq 2 (by norm_num) (by decide)
theorem R1289 : ∃ j : ℕ, syracuseStep^[j] 1289 = 1 := reachStep S1289 R967
theorem S1309 : syracuseStep 1309 = 491 := stepEq 3 (by norm_num) (by decide)
theorem R1309 : ∃ j : ℕ, syracuseStep^[j] 1309 = 1 := reachStep S1309 R491
theorem S1319 : syracuseStep 1319 = 1979 := stepEq 1 (by norm_num) (by decide)
theorem R1319 : ∃ j : ℕ, syracuseStep^[j] 1319 = 1 := reachStep S1319 R1979
theorem S42443 : syracuseStep 42443 = 63665 := stepEq 1 (by norm_num) (by decide)
theorem R42443 : ∃ j : ℕ, syracuseStep^[j] 42443 = 1 := reachStep S42443 R63665
theorem S10151 : syracuseStep 10151 = 15227 := stepEq 1 (by norm_num) (by decide)
theorem R10151 : ∃ j : ℕ, syracuseStep^[j] 10151 = 1 := reachStep S10151 R15227
theorem S6767 : syracuseStep 6767 = 10151 := stepEq 1 (by norm_num) (by decide)
theorem R6767 : ∃ j : ℕ, syracuseStep^[j] 6767 = 1 := reachStep S6767 R10151
theorem S859 : syracuseStep 859 = 1289 := stepEq 1 (by norm_num) (by decide)
theorem R859 : ∃ j : ℕ, syracuseStep^[j] 859 = 1 := reachStep S859 R1289
theorem S865 : syracuseStep 865 = 649 := stepEq 2 (by norm_num) (by decide)
theorem R865 : ∃ j : ℕ, syracuseStep^[j] 865 = 1 := reachStep S865 R649
theorem S873 : syracuseStep 873 = 655 := stepEq 2 (by norm_num) (by decide)
theorem R873 : ∃ j : ℕ, syracuseStep^[j] 873 = 1 := reachStep S873 R655
theorem S879 : syracuseStep 879 = 1319 := stepEq 1 (by norm_num) (by decide)
theorem R879 : ∃ j : ℕ, syracuseStep^[j] 879 = 1 := reachStep S879 R1319
theorem S889 : syracuseStep 889 = 667 := stepEq 2 (by norm_num) (by decide)
theorem R889 : ∃ j : ℕ, syracuseStep^[j] 889 = 1 := reachStep S889 R667
theorem S28295 : syracuseStep 28295 = 42443 := stepEq 1 (by norm_num) (by decide)
theorem R28295 : ∃ j : ℕ, syracuseStep^[j] 28295 = 1 := reachStep S28295 R42443
theorem S1745 : syracuseStep 1745 = 1309 := stepEq 2 (by norm_num) (by decide)
theorem R1745 : ∃ j : ℕ, syracuseStep^[j] 1745 = 1 := reachStep S1745 R1309
theorem S4511 : syracuseStep 4511 = 6767 := stepEq 1 (by norm_num) (by decide)
theorem R4511 : ∃ j : ℕ, syracuseStep^[j] 4511 = 1 := reachStep S4511 R6767
theorem S18863 : syracuseStep 18863 = 28295 := stepEq 1 (by norm_num) (by decide)
theorem R18863 : ∃ j : ℕ, syracuseStep^[j] 18863 = 1 := reachStep S18863 R28295
theorem S1145 : syracuseStep 1145 = 859 := stepEq 2 (by norm_num) (by decide)
theorem R1145 : ∃ j : ℕ, syracuseStep^[j] 1145 = 1 := reachStep S1145 R859
theorem S1153 : syracuseStep 1153 = 865 := stepEq 2 (by norm_num) (by decide)
theorem R1153 : ∃ j : ℕ, syracuseStep^[j] 1153 = 1 := reachStep S1153 R865
theorem S1163 : syracuseStep 1163 = 1745 := stepEq 1 (by norm_num) (by decide)
theorem R1163 : ∃ j : ℕ, syracuseStep^[j] 1163 = 1 := reachStep S1163 R1745
theorem S1185 : syracuseStep 1185 = 889 := stepEq 2 (by norm_num) (by decide)
theorem R1185 : ∃ j : ℕ, syracuseStep^[j] 1185 = 1 := reachStep S1185 R889
theorem S12575 : syracuseStep 12575 = 18863 := stepEq 1 (by norm_num) (by decide)
theorem R12575 : ∃ j : ℕ, syracuseStep^[j] 12575 = 1 := reachStep S12575 R18863
theorem S763 : syracuseStep 763 = 1145 := stepEq 1 (by norm_num) (by decide)
theorem R763 : ∃ j : ℕ, syracuseStep^[j] 763 = 1 := reachStep S763 R1145
theorem S775 : syracuseStep 775 = 1163 := stepEq 1 (by norm_num) (by decide)
theorem R775 : ∃ j : ℕ, syracuseStep^[j] 775 = 1 := reachStep S775 R1163
theorem S3007 : syracuseStep 3007 = 4511 := stepEq 1 (by norm_num) (by decide)
theorem R3007 : ∃ j : ℕ, syracuseStep^[j] 3007 = 1 := reachStep S3007 R4511
theorem S3053 : syracuseStep 3053 = 1145 := stepEq 3 (by norm_num) (by decide)
theorem R3053 : ∃ j : ℕ, syracuseStep^[j] 3053 = 1 := reachStep S3053 R1145
theorem S8383 : syracuseStep 8383 = 12575 := stepEq 1 (by norm_num) (by decide)
theorem R8383 : ∃ j : ℕ, syracuseStep^[j] 8383 = 1 := reachStep S8383 R12575
theorem S1017 : syracuseStep 1017 = 763 := stepEq 2 (by norm_num) (by decide)
theorem R1017 : ∃ j : ℕ, syracuseStep^[j] 1017 = 1 := reachStep S1017 R763
theorem S1033 : syracuseStep 1033 = 775 := stepEq 2 (by norm_num) (by decide)
theorem R1033 : ∃ j : ℕ, syracuseStep^[j] 1033 = 1 := reachStep S1033 R775
theorem S4009 : syracuseStep 4009 = 3007 := stepEq 2 (by norm_num) (by decide)
theorem R4009 : ∃ j : ℕ, syracuseStep^[j] 4009 = 1 := reachStep S4009 R3007
theorem S2035 : syracuseStep 2035 = 3053 := stepEq 1 (by norm_num) (by decide)
theorem R2035 : ∃ j : ℕ, syracuseStep^[j] 2035 = 1 := reachStep S2035 R3053
theorem S2713 : syracuseStep 2713 = 2035 := stepEq 2 (by norm_num) (by decide)
theorem R2713 : ∃ j : ℕ, syracuseStep^[j] 2713 = 1 := reachStep S2713 R2035
theorem S11177 : syracuseStep 11177 = 8383 := stepEq 2 (by norm_num) (by decide)
theorem R11177 : ∃ j : ℕ, syracuseStep^[j] 11177 = 1 := reachStep S11177 R8383
theorem S5345 : syracuseStep 5345 = 4009 := stepEq 2 (by norm_num) (by decide)
theorem R5345 : ∃ j : ℕ, syracuseStep^[j] 5345 = 1 := reachStep S5345 R4009
theorem S7451 : syracuseStep 7451 = 11177 := stepEq 1 (by norm_num) (by decide)
theorem R7451 : ∃ j : ℕ, syracuseStep^[j] 7451 = 1 := reachStep S7451 R11177
theorem S3563 : syracuseStep 3563 = 5345 := stepEq 1 (by norm_num) (by decide)
theorem R3563 : ∃ j : ℕ, syracuseStep^[j] 3563 = 1 := reachStep S3563 R5345
theorem S3617 : syracuseStep 3617 = 2713 := stepEq 2 (by norm_num) (by decide)
theorem R3617 : ∃ j : ℕ, syracuseStep^[j] 3617 = 1 := reachStep S3617 R2713
theorem S2375 : syracuseStep 2375 = 3563 := stepEq 1 (by norm_num) (by decide)
theorem R2375 : ∃ j : ℕ, syracuseStep^[j] 2375 = 1 := reachStep S2375 R3563
theorem S2411 : syracuseStep 2411 = 3617 := stepEq 1 (by norm_num) (by decide)
theorem R2411 : ∃ j : ℕ, syracuseStep^[j] 2411 = 1 := reachStep S2411 R3617
theorem S4967 : syracuseStep 4967 = 7451 := stepEq 1 (by norm_num) (by decide)
theorem R4967 : ∃ j : ℕ, syracuseStep^[j] 4967 = 1 := reachStep S4967 R7451
theorem S3311 : syracuseStep 3311 = 4967 := stepEq 1 (by norm_num) (by decide)
theorem R3311 : ∃ j : ℕ, syracuseStep^[j] 3311 = 1 := reachStep S3311 R4967
theorem S1583 : syracuseStep 1583 = 2375 := stepEq 1 (by norm_num) (by decide)
theorem R1583 : ∃ j : ℕ, syracuseStep^[j] 1583 = 1 := reachStep S1583 R2375
theorem S1607 : syracuseStep 1607 = 2411 := stepEq 1 (by norm_num) (by decide)
theorem R1607 : ∃ j : ℕ, syracuseStep^[j] 1607 = 1 := reachStep S1607 R2411
theorem S2207 : syracuseStep 2207 = 3311 := stepEq 1 (by norm_num) (by decide)
theorem R2207 : ∃ j : ℕ, syracuseStep^[j] 2207 = 1 := reachStep S2207 R3311
theorem S1055 : syracuseStep 1055 = 1583 := stepEq 1 (by norm_num) (by decide)
theorem R1055 : ∃ j : ℕ, syracuseStep^[j] 1055 = 1 := reachStep S1055 R1583
theorem S1071 : syracuseStep 1071 = 1607 := stepEq 1 (by norm_num) (by decide)
theorem R1071 : ∃ j : ℕ, syracuseStep^[j] 1071 = 1 := reachStep S1071 R1607
theorem S703 : syracuseStep 703 = 1055 := stepEq 1 (by norm_num) (by decide)
theorem R703 : ∃ j : ℕ, syracuseStep^[j] 703 = 1 := reachStep S703 R1055
theorem S1471 : syracuseStep 1471 = 2207 := stepEq 1 (by norm_num) (by decide)
theorem R1471 : ∃ j : ℕ, syracuseStep^[j] 1471 = 1 := reachStep S1471 R2207
theorem S937 : syracuseStep 937 = 703 := stepEq 2 (by norm_num) (by decide)
theorem R937 : ∃ j : ℕ, syracuseStep^[j] 937 = 1 := reachStep S937 R703
theorem S1961 : syracuseStep 1961 = 1471 := stepEq 2 (by norm_num) (by decide)
theorem R1961 : ∃ j : ℕ, syracuseStep^[j] 1961 = 1 := reachStep S1961 R1471
theorem S1307 : syracuseStep 1307 = 1961 := stepEq 1 (by norm_num) (by decide)
theorem R1307 : ∃ j : ℕ, syracuseStep^[j] 1307 = 1 := reachStep S1307 R1961
theorem S871 : syracuseStep 871 = 1307 := stepEq 1 (by norm_num) (by decide)
theorem R871 : ∃ j : ℕ, syracuseStep^[j] 871 = 1 := reachStep S871 R1307
theorem S1161 : syracuseStep 1161 = 871 := stepEq 2 (by norm_num) (by decide)
theorem R1161 : ∃ j : ℕ, syracuseStep^[j] 1161 = 1 := reachStep S1161 R871

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 1192) :
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
  · omega
  · exact R35
  · omega
  · exact R37
  · omega
  · exact R39
  · omega
  · exact R41
  · omega
  · exact R43
  · omega
  · exact R45
  · omega
  · exact R47
  · omega
  · exact R49
  · omega
  · exact R51
  · omega
  · exact R53
  · omega
  · exact R55
  · omega
  · exact R57
  · omega
  · exact R59
  · omega
  · exact R61
  · omega
  · exact R63
  · omega
  · exact R65
  · omega
  · exact R67
  · omega
  · exact R69
  · omega
  · exact R71
  · omega
  · exact R73
  · omega
  · exact R75
  · omega
  · exact R77
  · omega
  · exact R79
  · omega
  · exact R81
  · omega
  · exact R83
  · omega
  · exact R85
  · omega
  · exact R87
  · omega
  · exact R89
  · omega
  · exact R91
  · omega
  · exact R93
  · omega
  · exact R95
  · omega
  · exact R97
  · omega
  · exact R99
  · omega
  · exact R101
  · omega
  · exact R103
  · omega
  · exact R105
  · omega
  · exact R107
  · omega
  · exact R109
  · omega
  · exact R111
  · omega
  · exact R113
  · omega
  · exact R115
  · omega
  · exact R117
  · omega
  · exact R119
  · omega
  · exact R121
  · omega
  · exact R123
  · omega
  · exact R125
  · omega
  · exact R127
  · omega
  · exact R129
  · omega
  · exact R131
  · omega
  · exact R133
  · omega
  · exact R135
  · omega
  · exact R137
  · omega
  · exact R139
  · omega
  · exact R141
  · omega
  · exact R143
  · omega
  · exact R145
  · omega
  · exact R147
  · omega
  · exact R149
  · omega
  · exact R151
  · omega
  · exact R153
  · omega
  · exact R155
  · omega
  · exact R157
  · omega
  · exact R159
  · omega
  · exact R161
  · omega
  · exact R163
  · omega
  · exact R165
  · omega
  · exact R167
  · omega
  · exact R169
  · omega
  · exact R171
  · omega
  · exact R173
  · omega
  · exact R175
  · omega
  · exact R177
  · omega
  · exact R179
  · omega
  · exact R181
  · omega
  · exact R183
  · omega
  · exact R185
  · omega
  · exact R187
  · omega
  · exact R189
  · omega
  · exact R191
  · omega
  · exact R193
  · omega
  · exact R195
  · omega
  · exact R197
  · omega
  · exact R199
  · omega
  · exact R201
  · omega
  · exact R203
  · omega
  · exact R205
  · omega
  · exact R207
  · omega
  · exact R209
  · omega
  · exact R211
  · omega
  · exact R213
  · omega
  · exact R215
  · omega
  · exact R217
  · omega
  · exact R219
  · omega
  · exact R221
  · omega
  · exact R223
  · omega
  · exact R225
  · omega
  · exact R227
  · omega
  · exact R229
  · omega
  · exact R231
  · omega
  · exact R233
  · omega
  · exact R235
  · omega
  · exact R237
  · omega
  · exact R239
  · omega
  · exact R241
  · omega
  · exact R243
  · omega
  · exact R245
  · omega
  · exact R247
  · omega
  · exact R249
  · omega
  · exact R251
  · omega
  · exact R253
  · omega
  · exact R255
  · omega
  · exact R257
  · omega
  · exact R259
  · omega
  · exact R261
  · omega
  · exact R263
  · omega
  · exact R265
  · omega
  · exact R267
  · omega
  · exact R269
  · omega
  · exact R271
  · omega
  · exact R273
  · omega
  · exact R275
  · omega
  · exact R277
  · omega
  · exact R279
  · omega
  · exact R281
  · omega
  · exact R283
  · omega
  · exact R285
  · omega
  · exact R287
  · omega
  · exact R289
  · omega
  · exact R291
  · omega
  · exact R293
  · omega
  · exact R295
  · omega
  · exact R297
  · omega
  · exact R299
  · omega
  · exact R301
  · omega
  · exact R303
  · omega
  · exact R305
  · omega
  · exact R307
  · omega
  · exact R309
  · omega
  · exact R311
  · omega
  · exact R313
  · omega
  · exact R315
  · omega
  · exact R317
  · omega
  · exact R319
  · omega
  · exact R321
  · omega
  · exact R323
  · omega
  · exact R325
  · omega
  · exact R327
  · omega
  · exact R329
  · omega
  · exact R331
  · omega
  · exact R333
  · omega
  · exact R335
  · omega
  · exact R337
  · omega
  · exact R339
  · omega
  · exact R341
  · omega
  · exact R343
  · omega
  · exact R345
  · omega
  · exact R347
  · omega
  · exact R349
  · omega
  · exact R351
  · omega
  · exact R353
  · omega
  · exact R355
  · omega
  · exact R357
  · omega
  · exact R359
  · omega
  · exact R361
  · omega
  · exact R363
  · omega
  · exact R365
  · omega
  · exact R367
  · omega
  · exact R369
  · omega
  · exact R371
  · omega
  · exact R373
  · omega
  · exact R375
  · omega
  · exact R377
  · omega
  · exact R379
  · omega
  · exact R381
  · omega
  · exact R383
  · omega
  · exact R385
  · omega
  · exact R387
  · omega
  · exact R389
  · omega
  · exact R391
  · omega
  · exact R393
  · omega
  · exact R395
  · omega
  · exact R397
  · omega
  · exact R399
  · omega
  · exact R401
  · omega
  · exact R403
  · omega
  · exact R405
  · omega
  · exact R407
  · omega
  · exact R409
  · omega
  · exact R411
  · omega
  · exact R413
  · omega
  · exact R415
  · omega
  · exact R417
  · omega
  · exact R419
  · omega
  · exact R421
  · omega
  · exact R423
  · omega
  · exact R425
  · omega
  · exact R427
  · omega
  · exact R429
  · omega
  · exact R431
  · omega
  · exact R433
  · omega
  · exact R435
  · omega
  · exact R437
  · omega
  · exact R439
  · omega
  · exact R441
  · omega
  · exact R443
  · omega
  · exact R445
  · omega
  · exact R447
  · omega
  · exact R449
  · omega
  · exact R451
  · omega
  · exact R453
  · omega
  · exact R455
  · omega
  · exact R457
  · omega
  · exact R459
  · omega
  · exact R461
  · omega
  · exact R463
  · omega
  · exact R465
  · omega
  · exact R467
  · omega
  · exact R469
  · omega
  · exact R471
  · omega
  · exact R473
  · omega
  · exact R475
  · omega
  · exact R477
  · omega
  · exact R479
  · omega
  · exact R481
  · omega
  · exact R483
  · omega
  · exact R485
  · omega
  · exact R487
  · omega
  · exact R489
  · omega
  · exact R491
  · omega
  · exact R493
  · omega
  · exact R495
  · omega
  · exact R497
  · omega
  · exact R499
  · omega
  · exact R501
  · omega
  · exact R503
  · omega
  · exact R505
  · omega
  · exact R507
  · omega
  · exact R509
  · omega
  · exact R511
  · omega
  · exact R513
  · omega
  · exact R515
  · omega
  · exact R517
  · omega
  · exact R519
  · omega
  · exact R521
  · omega
  · exact R523
  · omega
  · exact R525
  · omega
  · exact R527
  · omega
  · exact R529
  · omega
  · exact R531
  · omega
  · exact R533
  · omega
  · exact R535
  · omega
  · exact R537
  · omega
  · exact R539
  · omega
  · exact R541
  · omega
  · exact R543
  · omega
  · exact R545
  · omega
  · exact R547
  · omega
  · exact R549
  · omega
  · exact R551
  · omega
  · exact R553
  · omega
  · exact R555
  · omega
  · exact R557
  · omega
  · exact R559
  · omega
  · exact R561
  · omega
  · exact R563
  · omega
  · exact R565
  · omega
  · exact R567
  · omega
  · exact R569
  · omega
  · exact R571
  · omega
  · exact R573
  · omega
  · exact R575
  · omega
  · exact R577
  · omega
  · exact R579
  · omega
  · exact R581
  · omega
  · exact R583
  · omega
  · exact R585
  · omega
  · exact R587
  · omega
  · exact R589
  · omega
  · exact R591
  · omega
  · exact R593
  · omega
  · exact R595
  · omega
  · exact R597
  · omega
  · exact R599
  · omega
  · exact R601
  · omega
  · exact R603
  · omega
  · exact R605
  · omega
  · exact R607
  · omega
  · exact R609
  · omega
  · exact R611
  · omega
  · exact R613
  · omega
  · exact R615
  · omega
  · exact R617
  · omega
  · exact R619
  · omega
  · exact R621
  · omega
  · exact R623
  · omega
  · exact R625
  · omega
  · exact R627
  · omega
  · exact R629
  · omega
  · exact R631
  · omega
  · exact R633
  · omega
  · exact R635
  · omega
  · exact R637
  · omega
  · exact R639
  · omega
  · exact R641
  · omega
  · exact R643
  · omega
  · exact R645
  · omega
  · exact R647
  · omega
  · exact R649
  · omega
  · exact R651
  · omega
  · exact R653
  · omega
  · exact R655
  · omega
  · exact R657
  · omega
  · exact R659
  · omega
  · exact R661
  · omega
  · exact R663
  · omega
  · exact R665
  · omega
  · exact R667
  · omega
  · exact R669
  · omega
  · exact R671
  · omega
  · exact R673
  · omega
  · exact R675
  · omega
  · exact R677
  · omega
  · exact R679
  · omega
  · exact R681
  · omega
  · exact R683
  · omega
  · exact R685
  · omega
  · exact R687
  · omega
  · exact R689
  · omega
  · exact R691
  · omega
  · exact R693
  · omega
  · exact R695
  · omega
  · exact R697
  · omega
  · exact R699
  · omega
  · exact R701
  · omega
  · exact R703
  · omega
  · exact R705
  · omega
  · exact R707
  · omega
  · exact R709
  · omega
  · exact R711
  · omega
  · exact R713
  · omega
  · exact R715
  · omega
  · exact R717
  · omega
  · exact R719
  · omega
  · exact R721
  · omega
  · exact R723
  · omega
  · exact R725
  · omega
  · exact R727
  · omega
  · exact R729
  · omega
  · exact R731
  · omega
  · exact R733
  · omega
  · exact R735
  · omega
  · exact R737
  · omega
  · exact R739
  · omega
  · exact R741
  · omega
  · exact R743
  · omega
  · exact R745
  · omega
  · exact R747
  · omega
  · exact R749
  · omega
  · exact R751
  · omega
  · exact R753
  · omega
  · exact R755
  · omega
  · exact R757
  · omega
  · exact R759
  · omega
  · exact R761
  · omega
  · exact R763
  · omega
  · exact R765
  · omega
  · exact R767
  · omega
  · exact R769
  · omega
  · exact R771
  · omega
  · exact R773
  · omega
  · exact R775
  · omega
  · exact R777
  · omega
  · exact R779
  · omega
  · exact R781
  · omega
  · exact R783
  · omega
  · exact R785
  · omega
  · exact R787
  · omega
  · exact R789
  · omega
  · exact R791
  · omega
  · exact R793
  · omega
  · exact R795
  · omega
  · exact R797
  · omega
  · exact R799
  · omega
  · exact R801
  · omega
  · exact R803
  · omega
  · exact R805
  · omega
  · exact R807
  · omega
  · exact R809
  · omega
  · exact R811
  · omega
  · exact R813
  · omega
  · exact R815
  · omega
  · exact R817
  · omega
  · exact R819
  · omega
  · exact R821
  · omega
  · exact R823
  · omega
  · exact R825
  · omega
  · exact R827
  · omega
  · exact R829
  · omega
  · exact R831
  · omega
  · exact R833
  · omega
  · exact R835
  · omega
  · exact R837
  · omega
  · exact R839
  · omega
  · exact R841
  · omega
  · exact R843
  · omega
  · exact R845
  · omega
  · exact R847
  · omega
  · exact R849
  · omega
  · exact R851
  · omega
  · exact R853
  · omega
  · exact R855
  · omega
  · exact R857
  · omega
  · exact R859
  · omega
  · exact R861
  · omega
  · exact R863
  · omega
  · exact R865
  · omega
  · exact R867
  · omega
  · exact R869
  · omega
  · exact R871
  · omega
  · exact R873
  · omega
  · exact R875
  · omega
  · exact R877
  · omega
  · exact R879
  · omega
  · exact R881
  · omega
  · exact R883
  · omega
  · exact R885
  · omega
  · exact R887
  · omega
  · exact R889
  · omega
  · exact R891
  · omega
  · exact R893
  · omega
  · exact R895
  · omega
  · exact R897
  · omega
  · exact R899
  · omega
  · exact R901
  · omega
  · exact R903
  · omega
  · exact R905
  · omega
  · exact R907
  · omega
  · exact R909
  · omega
  · exact R911
  · omega
  · exact R913
  · omega
  · exact R915
  · omega
  · exact R917
  · omega
  · exact R919
  · omega
  · exact R921
  · omega
  · exact R923
  · omega
  · exact R925
  · omega
  · exact R927
  · omega
  · exact R929
  · omega
  · exact R931
  · omega
  · exact R933
  · omega
  · exact R935
  · omega
  · exact R937
  · omega
  · exact R939
  · omega
  · exact R941
  · omega
  · exact R943
  · omega
  · exact R945
  · omega
  · exact R947
  · omega
  · exact R949
  · omega
  · exact R951
  · omega
  · exact R953
  · omega
  · exact R955
  · omega
  · exact R957
  · omega
  · exact R959
  · omega
  · exact R961
  · omega
  · exact R963
  · omega
  · exact R965
  · omega
  · exact R967
  · omega
  · exact R969
  · omega
  · exact R971
  · omega
  · exact R973
  · omega
  · exact R975
  · omega
  · exact R977
  · omega
  · exact R979
  · omega
  · exact R981
  · omega
  · exact R983
  · omega
  · exact R985
  · omega
  · exact R987
  · omega
  · exact R989
  · omega
  · exact R991
  · omega
  · exact R993
  · omega
  · exact R995
  · omega
  · exact R997
  · omega
  · exact R999
  · omega
  · exact R1001
  · omega
  · exact R1003
  · omega
  · exact R1005
  · omega
  · exact R1007
  · omega
  · exact R1009
  · omega
  · exact R1011
  · omega
  · exact R1013
  · omega
  · exact R1015
  · omega
  · exact R1017
  · omega
  · exact R1019
  · omega
  · exact R1021
  · omega
  · exact R1023
  · omega
  · exact R1025
  · omega
  · exact R1027
  · omega
  · exact R1029
  · omega
  · exact R1031
  · omega
  · exact R1033
  · omega
  · exact R1035
  · omega
  · exact R1037
  · omega
  · exact R1039
  · omega
  · exact R1041
  · omega
  · exact R1043
  · omega
  · exact R1045
  · omega
  · exact R1047
  · omega
  · exact R1049
  · omega
  · exact R1051
  · omega
  · exact R1053
  · omega
  · exact R1055
  · omega
  · exact R1057
  · omega
  · exact R1059
  · omega
  · exact R1061
  · omega
  · exact R1063
  · omega
  · exact R1065
  · omega
  · exact R1067
  · omega
  · exact R1069
  · omega
  · exact R1071
  · omega
  · exact R1073
  · omega
  · exact R1075
  · omega
  · exact R1077
  · omega
  · exact R1079
  · omega
  · exact R1081
  · omega
  · exact R1083
  · omega
  · exact R1085
  · omega
  · exact R1087
  · omega
  · exact R1089
  · omega
  · exact R1091
  · omega
  · exact R1093
  · omega
  · exact R1095
  · omega
  · exact R1097
  · omega
  · exact R1099
  · omega
  · exact R1101
  · omega
  · exact R1103
  · omega
  · exact R1105
  · omega
  · exact R1107
  · omega
  · exact R1109
  · omega
  · exact R1111
  · omega
  · exact R1113
  · omega
  · exact R1115
  · omega
  · exact R1117
  · omega
  · exact R1119
  · omega
  · exact R1121
  · omega
  · exact R1123
  · omega
  · exact R1125
  · omega
  · exact R1127
  · omega
  · exact R1129
  · omega
  · exact R1131
  · omega
  · exact R1133
  · omega
  · exact R1135
  · omega
  · exact R1137
  · omega
  · exact R1139
  · omega
  · exact R1141
  · omega
  · exact R1143
  · omega
  · exact R1145
  · omega
  · exact R1147
  · omega
  · exact R1149
  · omega
  · exact R1151
  · omega
  · exact R1153
  · omega
  · exact R1155
  · omega
  · exact R1157
  · omega
  · exact R1159
  · omega
  · exact R1161
  · omega
  · exact R1163
  · omega
  · exact R1165
  · omega
  · exact R1167
  · omega
  · exact R1169
  · omega
  · exact R1171
  · omega
  · exact R1173
  · omega
  · exact R1175
  · omega
  · exact R1177
  · omega
  · exact R1179
  · omega
  · exact R1181
  · omega
  · exact R1183
  · omega
  · exact R1185
  · omega
  · exact R1187
  · omega
  · exact R1189
  · omega
  · exact R1191
  · omega
