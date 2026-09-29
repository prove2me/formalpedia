-- Prove2me | solution 1 for syracuse_reaches_one_below_6725
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T04:02:54.227683+00:00
-- url     : https://prove2.me/submissions/8e854593-92ee-4130-8e54-f418571ff46b

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

theorem R5 : ∃ j : ℕ, syracuseStep^[j] 5 = 1 := reachStep (stepEq 4 (by rfl) ⟨0, by rfl⟩ : syracuseStep 5 = 1) R1
theorem R21 : ∃ j : ℕ, syracuseStep^[j] 21 = 1 := reachStep (stepEq 6 (by rfl) ⟨0, by rfl⟩ : syracuseStep 21 = 1) R1
theorem R85 : ∃ j : ℕ, syracuseStep^[j] 85 = 1 := reachStep (stepEq 8 (by rfl) ⟨0, by rfl⟩ : syracuseStep 85 = 1) R1
theorem R341 : ∃ j : ℕ, syracuseStep^[j] 341 = 1 := reachStep (stepEq 10 (by rfl) ⟨0, by rfl⟩ : syracuseStep 341 = 1) R1
theorem R1365 : ∃ j : ℕ, syracuseStep^[j] 1365 = 1 := reachStep (stepEq 12 (by rfl) ⟨0, by rfl⟩ : syracuseStep 1365 = 1) R1
theorem R5461 : ∃ j : ℕ, syracuseStep^[j] 5461 = 1 := reachStep (stepEq 14 (by rfl) ⟨0, by rfl⟩ : syracuseStep 5461 = 1) R1
theorem R3 : ∃ j : ℕ, syracuseStep^[j] 3 = 1 := reachStep (stepEq 1 (by rfl) ⟨2, by rfl⟩ : syracuseStep 3 = 5) R5
theorem R13 : ∃ j : ℕ, syracuseStep^[j] 13 = 1 := reachStep (stepEq 3 (by rfl) ⟨2, by rfl⟩ : syracuseStep 13 = 5) R5
theorem R53 : ∃ j : ℕ, syracuseStep^[j] 53 = 1 := reachStep (stepEq 5 (by rfl) ⟨2, by rfl⟩ : syracuseStep 53 = 5) R5
theorem R113 : ∃ j : ℕ, syracuseStep^[j] 113 = 1 := reachStep (stepEq 2 (by rfl) ⟨42, by rfl⟩ : syracuseStep 113 = 85) R85
theorem R213 : ∃ j : ℕ, syracuseStep^[j] 213 = 1 := reachStep (stepEq 7 (by rfl) ⟨2, by rfl⟩ : syracuseStep 213 = 5) R5
theorem R227 : ∃ j : ℕ, syracuseStep^[j] 227 = 1 := reachStep (stepEq 1 (by rfl) ⟨170, by rfl⟩ : syracuseStep 227 = 341) R341
theorem R453 : ∃ j : ℕ, syracuseStep^[j] 453 = 1 := reachStep (stepEq 4 (by rfl) ⟨42, by rfl⟩ : syracuseStep 453 = 85) R85
theorem R853 : ∃ j : ℕ, syracuseStep^[j] 853 = 1 := reachStep (stepEq 9 (by rfl) ⟨2, by rfl⟩ : syracuseStep 853 = 5) R5
theorem R909 : ∃ j : ℕ, syracuseStep^[j] 909 = 1 := reachStep (stepEq 3 (by rfl) ⟨170, by rfl⟩ : syracuseStep 909 = 341) R341
theorem R1813 : ∃ j : ℕ, syracuseStep^[j] 1813 = 1 := reachStep (stepEq 6 (by rfl) ⟨42, by rfl⟩ : syracuseStep 1813 = 85) R85
theorem R3413 : ∃ j : ℕ, syracuseStep^[j] 3413 = 1 := reachStep (stepEq 11 (by rfl) ⟨2, by rfl⟩ : syracuseStep 3413 = 5) R5
theorem R3637 : ∃ j : ℕ, syracuseStep^[j] 3637 = 1 := reachStep (stepEq 5 (by rfl) ⟨170, by rfl⟩ : syracuseStep 3637 = 341) R341
theorem R7253 : ∃ j : ℕ, syracuseStep^[j] 7253 = 1 := reachStep (stepEq 8 (by rfl) ⟨42, by rfl⟩ : syracuseStep 7253 = 85) R85
theorem R17 : ∃ j : ℕ, syracuseStep^[j] 17 = 1 := reachStep (stepEq 2 (by rfl) ⟨6, by rfl⟩ : syracuseStep 17 = 13) R13
theorem R35 : ∃ j : ℕ, syracuseStep^[j] 35 = 1 := reachStep (stepEq 1 (by rfl) ⟨26, by rfl⟩ : syracuseStep 35 = 53) R53
theorem R69 : ∃ j : ℕ, syracuseStep^[j] 69 = 1 := reachStep (stepEq 4 (by rfl) ⟨6, by rfl⟩ : syracuseStep 69 = 13) R13
theorem R75 : ∃ j : ℕ, syracuseStep^[j] 75 = 1 := reachStep (stepEq 1 (by rfl) ⟨56, by rfl⟩ : syracuseStep 75 = 113) R113
theorem R141 : ∃ j : ℕ, syracuseStep^[j] 141 = 1 := reachStep (stepEq 3 (by rfl) ⟨26, by rfl⟩ : syracuseStep 141 = 53) R53
theorem R151 : ∃ j : ℕ, syracuseStep^[j] 151 = 1 := reachStep (stepEq 1 (by rfl) ⟨113, by rfl⟩ : syracuseStep 151 = 227) R227
theorem R277 : ∃ j : ℕ, syracuseStep^[j] 277 = 1 := reachStep (stepEq 6 (by rfl) ⟨6, by rfl⟩ : syracuseStep 277 = 13) R13
theorem R301 : ∃ j : ℕ, syracuseStep^[j] 301 = 1 := reachStep (stepEq 3 (by rfl) ⟨56, by rfl⟩ : syracuseStep 301 = 113) R113
theorem R565 : ∃ j : ℕ, syracuseStep^[j] 565 = 1 := reachStep (stepEq 5 (by rfl) ⟨26, by rfl⟩ : syracuseStep 565 = 53) R53
theorem R605 : ∃ j : ℕ, syracuseStep^[j] 605 = 1 := reachStep (stepEq 3 (by rfl) ⟨113, by rfl⟩ : syracuseStep 605 = 227) R227
theorem R1109 : ∃ j : ℕ, syracuseStep^[j] 1109 = 1 := reachStep (stepEq 8 (by rfl) ⟨6, by rfl⟩ : syracuseStep 1109 = 13) R13
theorem R1137 : ∃ j : ℕ, syracuseStep^[j] 1137 = 1 := reachStep (stepEq 2 (by rfl) ⟨426, by rfl⟩ : syracuseStep 1137 = 853) R853
theorem R1205 : ∃ j : ℕ, syracuseStep^[j] 1205 = 1 := reachStep (stepEq 5 (by rfl) ⟨56, by rfl⟩ : syracuseStep 1205 = 113) R113
theorem R2261 : ∃ j : ℕ, syracuseStep^[j] 2261 = 1 := reachStep (stepEq 7 (by rfl) ⟨26, by rfl⟩ : syracuseStep 2261 = 53) R53
theorem R2275 : ∃ j : ℕ, syracuseStep^[j] 2275 = 1 := reachStep (stepEq 1 (by rfl) ⟨1706, by rfl⟩ : syracuseStep 2275 = 3413) R3413
theorem R2417 : ∃ j : ℕ, syracuseStep^[j] 2417 = 1 := reachStep (stepEq 2 (by rfl) ⟨906, by rfl⟩ : syracuseStep 2417 = 1813) R1813
theorem R2421 : ∃ j : ℕ, syracuseStep^[j] 2421 = 1 := reachStep (stepEq 5 (by rfl) ⟨113, by rfl⟩ : syracuseStep 2421 = 227) R227
theorem R4437 : ∃ j : ℕ, syracuseStep^[j] 4437 = 1 := reachStep (stepEq 10 (by rfl) ⟨6, by rfl⟩ : syracuseStep 4437 = 13) R13
theorem R4549 : ∃ j : ℕ, syracuseStep^[j] 4549 = 1 := reachStep (stepEq 4 (by rfl) ⟨426, by rfl⟩ : syracuseStep 4549 = 853) R853
theorem R4821 : ∃ j : ℕ, syracuseStep^[j] 4821 = 1 := reachStep (stepEq 7 (by rfl) ⟨56, by rfl⟩ : syracuseStep 4821 = 113) R113
theorem R4835 : ∃ j : ℕ, syracuseStep^[j] 4835 = 1 := reachStep (stepEq 1 (by rfl) ⟨3626, by rfl⟩ : syracuseStep 4835 = 7253) R7253
theorem R4849 : ∃ j : ℕ, syracuseStep^[j] 4849 = 1 := reachStep (stepEq 2 (by rfl) ⟨1818, by rfl⟩ : syracuseStep 4849 = 3637) R3637
theorem R9101 : ∃ j : ℕ, syracuseStep^[j] 9101 = 1 := reachStep (stepEq 3 (by rfl) ⟨1706, by rfl⟩ : syracuseStep 9101 = 3413) R3413
theorem R18197 : ∃ j : ℕ, syracuseStep^[j] 18197 = 1 := reachStep (stepEq 6 (by rfl) ⟨426, by rfl⟩ : syracuseStep 18197 = 853) R853
theorem R11 : ∃ j : ℕ, syracuseStep^[j] 11 = 1 := reachStep (stepEq 1 (by rfl) ⟨8, by rfl⟩ : syracuseStep 11 = 17) R17
theorem R23 : ∃ j : ℕ, syracuseStep^[j] 23 = 1 := reachStep (stepEq 1 (by rfl) ⟨17, by rfl⟩ : syracuseStep 23 = 35) R35
theorem R45 : ∃ j : ℕ, syracuseStep^[j] 45 = 1 := reachStep (stepEq 3 (by rfl) ⟨8, by rfl⟩ : syracuseStep 45 = 17) R17
theorem R93 : ∃ j : ℕ, syracuseStep^[j] 93 = 1 := reachStep (stepEq 3 (by rfl) ⟨17, by rfl⟩ : syracuseStep 93 = 35) R35
theorem R181 : ∃ j : ℕ, syracuseStep^[j] 181 = 1 := reachStep (stepEq 5 (by rfl) ⟨8, by rfl⟩ : syracuseStep 181 = 17) R17
theorem R201 : ∃ j : ℕ, syracuseStep^[j] 201 = 1 := reachStep (stepEq 2 (by rfl) ⟨75, by rfl⟩ : syracuseStep 201 = 151) R151
theorem R369 : ∃ j : ℕ, syracuseStep^[j] 369 = 1 := reachStep (stepEq 2 (by rfl) ⟨138, by rfl⟩ : syracuseStep 369 = 277) R277
theorem R373 : ∃ j : ℕ, syracuseStep^[j] 373 = 1 := reachStep (stepEq 5 (by rfl) ⟨17, by rfl⟩ : syracuseStep 373 = 35) R35
theorem R401 : ∃ j : ℕ, syracuseStep^[j] 401 = 1 := reachStep (stepEq 2 (by rfl) ⟨150, by rfl⟩ : syracuseStep 401 = 301) R301
theorem R403 : ∃ j : ℕ, syracuseStep^[j] 403 = 1 := reachStep (stepEq 1 (by rfl) ⟨302, by rfl⟩ : syracuseStep 403 = 605) R605
theorem R725 : ∃ j : ℕ, syracuseStep^[j] 725 = 1 := reachStep (stepEq 7 (by rfl) ⟨8, by rfl⟩ : syracuseStep 725 = 17) R17
theorem R739 : ∃ j : ℕ, syracuseStep^[j] 739 = 1 := reachStep (stepEq 1 (by rfl) ⟨554, by rfl⟩ : syracuseStep 739 = 1109) R1109
theorem R753 : ∃ j : ℕ, syracuseStep^[j] 753 = 1 := reachStep (stepEq 2 (by rfl) ⟨282, by rfl⟩ : syracuseStep 753 = 565) R565
theorem R803 : ∃ j : ℕ, syracuseStep^[j] 803 = 1 := reachStep (stepEq 1 (by rfl) ⟨602, by rfl⟩ : syracuseStep 803 = 1205) R1205
theorem R805 : ∃ j : ℕ, syracuseStep^[j] 805 = 1 := reachStep (stepEq 4 (by rfl) ⟨75, by rfl⟩ : syracuseStep 805 = 151) R151
theorem R1477 : ∃ j : ℕ, syracuseStep^[j] 1477 = 1 := reachStep (stepEq 4 (by rfl) ⟨138, by rfl⟩ : syracuseStep 1477 = 277) R277
theorem R1493 : ∃ j : ℕ, syracuseStep^[j] 1493 = 1 := reachStep (stepEq 7 (by rfl) ⟨17, by rfl⟩ : syracuseStep 1493 = 35) R35
theorem R1507 : ∃ j : ℕ, syracuseStep^[j] 1507 = 1 := reachStep (stepEq 1 (by rfl) ⟨1130, by rfl⟩ : syracuseStep 1507 = 2261) R2261
theorem R1605 : ∃ j : ℕ, syracuseStep^[j] 1605 = 1 := reachStep (stepEq 4 (by rfl) ⟨150, by rfl⟩ : syracuseStep 1605 = 301) R301
theorem R1611 : ∃ j : ℕ, syracuseStep^[j] 1611 = 1 := reachStep (stepEq 1 (by rfl) ⟨1208, by rfl⟩ : syracuseStep 1611 = 2417) R2417
theorem R1613 : ∃ j : ℕ, syracuseStep^[j] 1613 = 1 := reachStep (stepEq 3 (by rfl) ⟨302, by rfl⟩ : syracuseStep 1613 = 605) R605
theorem R2901 : ∃ j : ℕ, syracuseStep^[j] 2901 = 1 := reachStep (stepEq 9 (by rfl) ⟨8, by rfl⟩ : syracuseStep 2901 = 17) R17
theorem R2957 : ∃ j : ℕ, syracuseStep^[j] 2957 = 1 := reachStep (stepEq 3 (by rfl) ⟨554, by rfl⟩ : syracuseStep 2957 = 1109) R1109
theorem R3013 : ∃ j : ℕ, syracuseStep^[j] 3013 = 1 := reachStep (stepEq 4 (by rfl) ⟨282, by rfl⟩ : syracuseStep 3013 = 565) R565
theorem R3033 : ∃ j : ℕ, syracuseStep^[j] 3033 = 1 := reachStep (stepEq 2 (by rfl) ⟨1137, by rfl⟩ : syracuseStep 3033 = 2275) R2275
theorem R3213 : ∃ j : ℕ, syracuseStep^[j] 3213 = 1 := reachStep (stepEq 3 (by rfl) ⟨602, by rfl⟩ : syracuseStep 3213 = 1205) R1205
theorem R3221 : ∃ j : ℕ, syracuseStep^[j] 3221 = 1 := reachStep (stepEq 6 (by rfl) ⟨75, by rfl⟩ : syracuseStep 3221 = 151) R151
theorem R3223 : ∃ j : ℕ, syracuseStep^[j] 3223 = 1 := reachStep (stepEq 1 (by rfl) ⟨2417, by rfl⟩ : syracuseStep 3223 = 4835) R4835
theorem R5909 : ∃ j : ℕ, syracuseStep^[j] 5909 = 1 := reachStep (stepEq 6 (by rfl) ⟨138, by rfl⟩ : syracuseStep 5909 = 277) R277
theorem R5973 : ∃ j : ℕ, syracuseStep^[j] 5973 = 1 := reachStep (stepEq 9 (by rfl) ⟨17, by rfl⟩ : syracuseStep 5973 = 35) R35
theorem R6029 : ∃ j : ℕ, syracuseStep^[j] 6029 = 1 := reachStep (stepEq 3 (by rfl) ⟨1130, by rfl⟩ : syracuseStep 6029 = 2261) R2261
theorem R6065 : ∃ j : ℕ, syracuseStep^[j] 6065 = 1 := reachStep (stepEq 2 (by rfl) ⟨2274, by rfl⟩ : syracuseStep 6065 = 4549) R4549
theorem R6067 : ∃ j : ℕ, syracuseStep^[j] 6067 = 1 := reachStep (stepEq 1 (by rfl) ⟨4550, by rfl⟩ : syracuseStep 6067 = 9101) R9101
theorem R6421 : ∃ j : ℕ, syracuseStep^[j] 6421 = 1 := reachStep (stepEq 6 (by rfl) ⟨150, by rfl⟩ : syracuseStep 6421 = 301) R301
theorem R6445 : ∃ j : ℕ, syracuseStep^[j] 6445 = 1 := reachStep (stepEq 3 (by rfl) ⟨1208, by rfl⟩ : syracuseStep 6445 = 2417) R2417
theorem R6453 : ∃ j : ℕ, syracuseStep^[j] 6453 = 1 := reachStep (stepEq 5 (by rfl) ⟨302, by rfl⟩ : syracuseStep 6453 = 605) R605
theorem R6465 : ∃ j : ℕ, syracuseStep^[j] 6465 = 1 := reachStep (stepEq 2 (by rfl) ⟨2424, by rfl⟩ : syracuseStep 6465 = 4849) R4849
theorem R12131 : ∃ j : ℕ, syracuseStep^[j] 12131 = 1 := reachStep (stepEq 1 (by rfl) ⟨9098, by rfl⟩ : syracuseStep 12131 = 18197) R18197
theorem R7 : ∃ j : ℕ, syracuseStep^[j] 7 = 1 := reachStep (stepEq 1 (by rfl) ⟨5, by rfl⟩ : syracuseStep 7 = 11) R11
theorem R15 : ∃ j : ℕ, syracuseStep^[j] 15 = 1 := reachStep (stepEq 1 (by rfl) ⟨11, by rfl⟩ : syracuseStep 15 = 23) R23
theorem R29 : ∃ j : ℕ, syracuseStep^[j] 29 = 1 := reachStep (stepEq 3 (by rfl) ⟨5, by rfl⟩ : syracuseStep 29 = 11) R11
theorem R61 : ∃ j : ℕ, syracuseStep^[j] 61 = 1 := reachStep (stepEq 3 (by rfl) ⟨11, by rfl⟩ : syracuseStep 61 = 23) R23
theorem R117 : ∃ j : ℕ, syracuseStep^[j] 117 = 1 := reachStep (stepEq 5 (by rfl) ⟨5, by rfl⟩ : syracuseStep 117 = 11) R11
theorem R241 : ∃ j : ℕ, syracuseStep^[j] 241 = 1 := reachStep (stepEq 2 (by rfl) ⟨90, by rfl⟩ : syracuseStep 241 = 181) R181
theorem R245 : ∃ j : ℕ, syracuseStep^[j] 245 = 1 := reachStep (stepEq 5 (by rfl) ⟨11, by rfl⟩ : syracuseStep 245 = 23) R23
theorem R267 : ∃ j : ℕ, syracuseStep^[j] 267 = 1 := reachStep (stepEq 1 (by rfl) ⟨200, by rfl⟩ : syracuseStep 267 = 401) R401
theorem R469 : ∃ j : ℕ, syracuseStep^[j] 469 = 1 := reachStep (stepEq 7 (by rfl) ⟨5, by rfl⟩ : syracuseStep 469 = 11) R11
theorem R483 : ∃ j : ℕ, syracuseStep^[j] 483 = 1 := reachStep (stepEq 1 (by rfl) ⟨362, by rfl⟩ : syracuseStep 483 = 725) R725
theorem R497 : ∃ j : ℕ, syracuseStep^[j] 497 = 1 := reachStep (stepEq 2 (by rfl) ⟨186, by rfl⟩ : syracuseStep 497 = 373) R373
theorem R535 : ∃ j : ℕ, syracuseStep^[j] 535 = 1 := reachStep (stepEq 1 (by rfl) ⟨401, by rfl⟩ : syracuseStep 535 = 803) R803
theorem R537 : ∃ j : ℕ, syracuseStep^[j] 537 = 1 := reachStep (stepEq 2 (by rfl) ⟨201, by rfl⟩ : syracuseStep 537 = 403) R403
theorem R965 : ∃ j : ℕ, syracuseStep^[j] 965 = 1 := reachStep (stepEq 4 (by rfl) ⟨90, by rfl⟩ : syracuseStep 965 = 181) R181
theorem R981 : ∃ j : ℕ, syracuseStep^[j] 981 = 1 := reachStep (stepEq 7 (by rfl) ⟨11, by rfl⟩ : syracuseStep 981 = 23) R23
theorem R985 : ∃ j : ℕ, syracuseStep^[j] 985 = 1 := reachStep (stepEq 2 (by rfl) ⟨369, by rfl⟩ : syracuseStep 985 = 739) R739
theorem R995 : ∃ j : ℕ, syracuseStep^[j] 995 = 1 := reachStep (stepEq 1 (by rfl) ⟨746, by rfl⟩ : syracuseStep 995 = 1493) R1493
theorem R1069 : ∃ j : ℕ, syracuseStep^[j] 1069 = 1 := reachStep (stepEq 3 (by rfl) ⟨200, by rfl⟩ : syracuseStep 1069 = 401) R401
theorem R1073 : ∃ j : ℕ, syracuseStep^[j] 1073 = 1 := reachStep (stepEq 2 (by rfl) ⟨402, by rfl⟩ : syracuseStep 1073 = 805) R805
theorem R1075 : ∃ j : ℕ, syracuseStep^[j] 1075 = 1 := reachStep (stepEq 1 (by rfl) ⟨806, by rfl⟩ : syracuseStep 1075 = 1613) R1613
theorem R1877 : ∃ j : ℕ, syracuseStep^[j] 1877 = 1 := reachStep (stepEq 9 (by rfl) ⟨5, by rfl⟩ : syracuseStep 1877 = 11) R11
theorem R1933 : ∃ j : ℕ, syracuseStep^[j] 1933 = 1 := reachStep (stepEq 3 (by rfl) ⟨362, by rfl⟩ : syracuseStep 1933 = 725) R725
theorem R1969 : ∃ j : ℕ, syracuseStep^[j] 1969 = 1 := reachStep (stepEq 2 (by rfl) ⟨738, by rfl⟩ : syracuseStep 1969 = 1477) R1477
theorem R1971 : ∃ j : ℕ, syracuseStep^[j] 1971 = 1 := reachStep (stepEq 1 (by rfl) ⟨1478, by rfl⟩ : syracuseStep 1971 = 2957) R2957
theorem R1989 : ∃ j : ℕ, syracuseStep^[j] 1989 = 1 := reachStep (stepEq 4 (by rfl) ⟨186, by rfl⟩ : syracuseStep 1989 = 373) R373
theorem R2009 : ∃ j : ℕ, syracuseStep^[j] 2009 = 1 := reachStep (stepEq 2 (by rfl) ⟨753, by rfl⟩ : syracuseStep 2009 = 1507) R1507
theorem R2141 : ∃ j : ℕ, syracuseStep^[j] 2141 = 1 := reachStep (stepEq 3 (by rfl) ⟨401, by rfl⟩ : syracuseStep 2141 = 803) R803
theorem R2147 : ∃ j : ℕ, syracuseStep^[j] 2147 = 1 := reachStep (stepEq 1 (by rfl) ⟨1610, by rfl⟩ : syracuseStep 2147 = 3221) R3221
theorem R2149 : ∃ j : ℕ, syracuseStep^[j] 2149 = 1 := reachStep (stepEq 4 (by rfl) ⟨201, by rfl⟩ : syracuseStep 2149 = 403) R403
theorem R3861 : ∃ j : ℕ, syracuseStep^[j] 3861 = 1 := reachStep (stepEq 6 (by rfl) ⟨90, by rfl⟩ : syracuseStep 3861 = 181) R181
theorem R3925 : ∃ j : ℕ, syracuseStep^[j] 3925 = 1 := reachStep (stepEq 9 (by rfl) ⟨11, by rfl⟩ : syracuseStep 3925 = 23) R23
theorem R3939 : ∃ j : ℕ, syracuseStep^[j] 3939 = 1 := reachStep (stepEq 1 (by rfl) ⟨2954, by rfl⟩ : syracuseStep 3939 = 5909) R5909
theorem R3941 : ∃ j : ℕ, syracuseStep^[j] 3941 = 1 := reachStep (stepEq 4 (by rfl) ⟨369, by rfl⟩ : syracuseStep 3941 = 739) R739
theorem R3981 : ∃ j : ℕ, syracuseStep^[j] 3981 = 1 := reachStep (stepEq 3 (by rfl) ⟨746, by rfl⟩ : syracuseStep 3981 = 1493) R1493
theorem R4017 : ∃ j : ℕ, syracuseStep^[j] 4017 = 1 := reachStep (stepEq 2 (by rfl) ⟨1506, by rfl⟩ : syracuseStep 4017 = 3013) R3013
theorem R4019 : ∃ j : ℕ, syracuseStep^[j] 4019 = 1 := reachStep (stepEq 1 (by rfl) ⟨3014, by rfl⟩ : syracuseStep 4019 = 6029) R6029
theorem R4043 : ∃ j : ℕ, syracuseStep^[j] 4043 = 1 := reachStep (stepEq 1 (by rfl) ⟨3032, by rfl⟩ : syracuseStep 4043 = 6065) R6065
theorem R4277 : ∃ j : ℕ, syracuseStep^[j] 4277 = 1 := reachStep (stepEq 5 (by rfl) ⟨200, by rfl⟩ : syracuseStep 4277 = 401) R401
theorem R4293 : ∃ j : ℕ, syracuseStep^[j] 4293 = 1 := reachStep (stepEq 4 (by rfl) ⟨402, by rfl⟩ : syracuseStep 4293 = 805) R805
theorem R4297 : ∃ j : ℕ, syracuseStep^[j] 4297 = 1 := reachStep (stepEq 2 (by rfl) ⟨1611, by rfl⟩ : syracuseStep 4297 = 3223) R3223
theorem R4301 : ∃ j : ℕ, syracuseStep^[j] 4301 = 1 := reachStep (stepEq 3 (by rfl) ⟨806, by rfl⟩ : syracuseStep 4301 = 1613) R1613
theorem R7733 : ∃ j : ℕ, syracuseStep^[j] 7733 = 1 := reachStep (stepEq 5 (by rfl) ⟨362, by rfl⟩ : syracuseStep 7733 = 725) R725
theorem R7877 : ∃ j : ℕ, syracuseStep^[j] 7877 = 1 := reachStep (stepEq 4 (by rfl) ⟨738, by rfl⟩ : syracuseStep 7877 = 1477) R1477
theorem R8087 : ∃ j : ℕ, syracuseStep^[j] 8087 = 1 := reachStep (stepEq 1 (by rfl) ⟨6065, by rfl⟩ : syracuseStep 8087 = 12131) R12131
theorem R8561 : ∃ j : ℕ, syracuseStep^[j] 8561 = 1 := reachStep (stepEq 2 (by rfl) ⟨3210, by rfl⟩ : syracuseStep 8561 = 6421) R6421
theorem R8597 : ∃ j : ℕ, syracuseStep^[j] 8597 = 1 := reachStep (stepEq 6 (by rfl) ⟨201, by rfl⟩ : syracuseStep 8597 = 403) R403
theorem R9 : ∃ j : ℕ, syracuseStep^[j] 9 = 1 := reachStep (stepEq 2 (by rfl) ⟨3, by rfl⟩ : syracuseStep 9 = 7) R7
theorem R19 : ∃ j : ℕ, syracuseStep^[j] 19 = 1 := reachStep (stepEq 1 (by rfl) ⟨14, by rfl⟩ : syracuseStep 19 = 29) R29
theorem R37 : ∃ j : ℕ, syracuseStep^[j] 37 = 1 := reachStep (stepEq 4 (by rfl) ⟨3, by rfl⟩ : syracuseStep 37 = 7) R7
theorem R77 : ∃ j : ℕ, syracuseStep^[j] 77 = 1 := reachStep (stepEq 3 (by rfl) ⟨14, by rfl⟩ : syracuseStep 77 = 29) R29
theorem R81 : ∃ j : ℕ, syracuseStep^[j] 81 = 1 := reachStep (stepEq 2 (by rfl) ⟨30, by rfl⟩ : syracuseStep 81 = 61) R61
theorem R149 : ∃ j : ℕ, syracuseStep^[j] 149 = 1 := reachStep (stepEq 6 (by rfl) ⟨3, by rfl⟩ : syracuseStep 149 = 7) R7
theorem R163 : ∃ j : ℕ, syracuseStep^[j] 163 = 1 := reachStep (stepEq 1 (by rfl) ⟨122, by rfl⟩ : syracuseStep 163 = 245) R245
theorem R309 : ∃ j : ℕ, syracuseStep^[j] 309 = 1 := reachStep (stepEq 5 (by rfl) ⟨14, by rfl⟩ : syracuseStep 309 = 29) R29
theorem R321 : ∃ j : ℕ, syracuseStep^[j] 321 = 1 := reachStep (stepEq 2 (by rfl) ⟨120, by rfl⟩ : syracuseStep 321 = 241) R241
theorem R325 : ∃ j : ℕ, syracuseStep^[j] 325 = 1 := reachStep (stepEq 4 (by rfl) ⟨30, by rfl⟩ : syracuseStep 325 = 61) R61
theorem R331 : ∃ j : ℕ, syracuseStep^[j] 331 = 1 := reachStep (stepEq 1 (by rfl) ⟨248, by rfl⟩ : syracuseStep 331 = 497) R497
theorem R597 : ∃ j : ℕ, syracuseStep^[j] 597 = 1 := reachStep (stepEq 8 (by rfl) ⟨3, by rfl⟩ : syracuseStep 597 = 7) R7
theorem R625 : ∃ j : ℕ, syracuseStep^[j] 625 = 1 := reachStep (stepEq 2 (by rfl) ⟨234, by rfl⟩ : syracuseStep 625 = 469) R469
theorem R643 : ∃ j : ℕ, syracuseStep^[j] 643 = 1 := reachStep (stepEq 1 (by rfl) ⟨482, by rfl⟩ : syracuseStep 643 = 965) R965
theorem R653 : ∃ j : ℕ, syracuseStep^[j] 653 = 1 := reachStep (stepEq 3 (by rfl) ⟨122, by rfl⟩ : syracuseStep 653 = 245) R245
theorem R663 : ∃ j : ℕ, syracuseStep^[j] 663 = 1 := reachStep (stepEq 1 (by rfl) ⟨497, by rfl⟩ : syracuseStep 663 = 995) R995
theorem R713 : ∃ j : ℕ, syracuseStep^[j] 713 = 1 := reachStep (stepEq 2 (by rfl) ⟨267, by rfl⟩ : syracuseStep 713 = 535) R535
theorem R715 : ∃ j : ℕ, syracuseStep^[j] 715 = 1 := reachStep (stepEq 1 (by rfl) ⟨536, by rfl⟩ : syracuseStep 715 = 1073) R1073
theorem R1237 : ∃ j : ℕ, syracuseStep^[j] 1237 = 1 := reachStep (stepEq 7 (by rfl) ⟨14, by rfl⟩ : syracuseStep 1237 = 29) R29
theorem R1251 : ∃ j : ℕ, syracuseStep^[j] 1251 = 1 := reachStep (stepEq 1 (by rfl) ⟨938, by rfl⟩ : syracuseStep 1251 = 1877) R1877
theorem R1285 : ∃ j : ℕ, syracuseStep^[j] 1285 = 1 := reachStep (stepEq 4 (by rfl) ⟨120, by rfl⟩ : syracuseStep 1285 = 241) R241
theorem R1301 : ∃ j : ℕ, syracuseStep^[j] 1301 = 1 := reachStep (stepEq 6 (by rfl) ⟨30, by rfl⟩ : syracuseStep 1301 = 61) R61
theorem R1313 : ∃ j : ℕ, syracuseStep^[j] 1313 = 1 := reachStep (stepEq 2 (by rfl) ⟨492, by rfl⟩ : syracuseStep 1313 = 985) R985
theorem R1325 : ∃ j : ℕ, syracuseStep^[j] 1325 = 1 := reachStep (stepEq 3 (by rfl) ⟨248, by rfl⟩ : syracuseStep 1325 = 497) R497
theorem R1339 : ∃ j : ℕ, syracuseStep^[j] 1339 = 1 := reachStep (stepEq 1 (by rfl) ⟨1004, by rfl⟩ : syracuseStep 1339 = 2009) R2009
theorem R1425 : ∃ j : ℕ, syracuseStep^[j] 1425 = 1 := reachStep (stepEq 2 (by rfl) ⟨534, by rfl⟩ : syracuseStep 1425 = 1069) R1069
theorem R1427 : ∃ j : ℕ, syracuseStep^[j] 1427 = 1 := reachStep (stepEq 1 (by rfl) ⟨1070, by rfl⟩ : syracuseStep 1427 = 2141) R2141
theorem R1431 : ∃ j : ℕ, syracuseStep^[j] 1431 = 1 := reachStep (stepEq 1 (by rfl) ⟨1073, by rfl⟩ : syracuseStep 1431 = 2147) R2147
theorem R1433 : ∃ j : ℕ, syracuseStep^[j] 1433 = 1 := reachStep (stepEq 2 (by rfl) ⟨537, by rfl⟩ : syracuseStep 1433 = 1075) R1075
theorem R2389 : ∃ j : ℕ, syracuseStep^[j] 2389 = 1 := reachStep (stepEq 10 (by rfl) ⟨3, by rfl⟩ : syracuseStep 2389 = 7) R7
theorem R2501 : ∃ j : ℕ, syracuseStep^[j] 2501 = 1 := reachStep (stepEq 4 (by rfl) ⟨234, by rfl⟩ : syracuseStep 2501 = 469) R469
theorem R2573 : ∃ j : ℕ, syracuseStep^[j] 2573 = 1 := reachStep (stepEq 3 (by rfl) ⟨482, by rfl⟩ : syracuseStep 2573 = 965) R965
theorem R2577 : ∃ j : ℕ, syracuseStep^[j] 2577 = 1 := reachStep (stepEq 2 (by rfl) ⟨966, by rfl⟩ : syracuseStep 2577 = 1933) R1933
theorem R2613 : ∃ j : ℕ, syracuseStep^[j] 2613 = 1 := reachStep (stepEq 5 (by rfl) ⟨122, by rfl⟩ : syracuseStep 2613 = 245) R245
theorem R2625 : ∃ j : ℕ, syracuseStep^[j] 2625 = 1 := reachStep (stepEq 2 (by rfl) ⟨984, by rfl⟩ : syracuseStep 2625 = 1969) R1969
theorem R2627 : ∃ j : ℕ, syracuseStep^[j] 2627 = 1 := reachStep (stepEq 1 (by rfl) ⟨1970, by rfl⟩ : syracuseStep 2627 = 3941) R3941
theorem R2653 : ∃ j : ℕ, syracuseStep^[j] 2653 = 1 := reachStep (stepEq 3 (by rfl) ⟨497, by rfl⟩ : syracuseStep 2653 = 995) R995
theorem R2679 : ∃ j : ℕ, syracuseStep^[j] 2679 = 1 := reachStep (stepEq 1 (by rfl) ⟨2009, by rfl⟩ : syracuseStep 2679 = 4019) R4019
theorem R2695 : ∃ j : ℕ, syracuseStep^[j] 2695 = 1 := reachStep (stepEq 1 (by rfl) ⟨2021, by rfl⟩ : syracuseStep 2695 = 4043) R4043
theorem R2851 : ∃ j : ℕ, syracuseStep^[j] 2851 = 1 := reachStep (stepEq 1 (by rfl) ⟨2138, by rfl⟩ : syracuseStep 2851 = 4277) R4277
theorem R2853 : ∃ j : ℕ, syracuseStep^[j] 2853 = 1 := reachStep (stepEq 4 (by rfl) ⟨267, by rfl⟩ : syracuseStep 2853 = 535) R535
theorem R2861 : ∃ j : ℕ, syracuseStep^[j] 2861 = 1 := reachStep (stepEq 3 (by rfl) ⟨536, by rfl⟩ : syracuseStep 2861 = 1073) R1073
theorem R2865 : ∃ j : ℕ, syracuseStep^[j] 2865 = 1 := reachStep (stepEq 2 (by rfl) ⟨1074, by rfl⟩ : syracuseStep 2865 = 2149) R2149
theorem R2867 : ∃ j : ℕ, syracuseStep^[j] 2867 = 1 := reachStep (stepEq 1 (by rfl) ⟨2150, by rfl⟩ : syracuseStep 2867 = 4301) R4301
theorem R4949 : ∃ j : ℕ, syracuseStep^[j] 4949 = 1 := reachStep (stepEq 9 (by rfl) ⟨14, by rfl⟩ : syracuseStep 4949 = 29) R29
theorem R5005 : ∃ j : ℕ, syracuseStep^[j] 5005 = 1 := reachStep (stepEq 3 (by rfl) ⟨938, by rfl⟩ : syracuseStep 5005 = 1877) R1877
theorem R5141 : ∃ j : ℕ, syracuseStep^[j] 5141 = 1 := reachStep (stepEq 6 (by rfl) ⟨120, by rfl⟩ : syracuseStep 5141 = 241) R241
theorem R5155 : ∃ j : ℕ, syracuseStep^[j] 5155 = 1 := reachStep (stepEq 1 (by rfl) ⟨3866, by rfl⟩ : syracuseStep 5155 = 7733) R7733
theorem R5205 : ∃ j : ℕ, syracuseStep^[j] 5205 = 1 := reachStep (stepEq 8 (by rfl) ⟨30, by rfl⟩ : syracuseStep 5205 = 61) R61
theorem R5233 : ∃ j : ℕ, syracuseStep^[j] 5233 = 1 := reachStep (stepEq 2 (by rfl) ⟨1962, by rfl⟩ : syracuseStep 5233 = 3925) R3925
theorem R5251 : ∃ j : ℕ, syracuseStep^[j] 5251 = 1 := reachStep (stepEq 1 (by rfl) ⟨3938, by rfl⟩ : syracuseStep 5251 = 7877) R7877
theorem R5253 : ∃ j : ℕ, syracuseStep^[j] 5253 = 1 := reachStep (stepEq 4 (by rfl) ⟨492, by rfl⟩ : syracuseStep 5253 = 985) R985
theorem R5301 : ∃ j : ℕ, syracuseStep^[j] 5301 = 1 := reachStep (stepEq 5 (by rfl) ⟨248, by rfl⟩ : syracuseStep 5301 = 497) R497
theorem R5357 : ∃ j : ℕ, syracuseStep^[j] 5357 = 1 := reachStep (stepEq 3 (by rfl) ⟨1004, by rfl⟩ : syracuseStep 5357 = 2009) R2009
theorem R5391 : ∃ j : ℕ, syracuseStep^[j] 5391 = 1 := reachStep (stepEq 1 (by rfl) ⟨4043, by rfl⟩ : syracuseStep 5391 = 8087) R8087
theorem R5701 : ∃ j : ℕ, syracuseStep^[j] 5701 = 1 := reachStep (stepEq 4 (by rfl) ⟨534, by rfl⟩ : syracuseStep 5701 = 1069) R1069
theorem R5707 : ∃ j : ℕ, syracuseStep^[j] 5707 = 1 := reachStep (stepEq 1 (by rfl) ⟨4280, by rfl⟩ : syracuseStep 5707 = 8561) R8561
theorem R5709 : ∃ j : ℕ, syracuseStep^[j] 5709 = 1 := reachStep (stepEq 3 (by rfl) ⟨1070, by rfl⟩ : syracuseStep 5709 = 2141) R2141
theorem R5725 : ∃ j : ℕ, syracuseStep^[j] 5725 = 1 := reachStep (stepEq 3 (by rfl) ⟨1073, by rfl⟩ : syracuseStep 5725 = 2147) R2147
theorem R5729 : ∃ j : ℕ, syracuseStep^[j] 5729 = 1 := reachStep (stepEq 2 (by rfl) ⟨2148, by rfl⟩ : syracuseStep 5729 = 4297) R4297
theorem R5731 : ∃ j : ℕ, syracuseStep^[j] 5731 = 1 := reachStep (stepEq 1 (by rfl) ⟨4298, by rfl⟩ : syracuseStep 5731 = 8597) R8597
theorem R5733 : ∃ j : ℕ, syracuseStep^[j] 5733 = 1 := reachStep (stepEq 4 (by rfl) ⟨537, by rfl⟩ : syracuseStep 5733 = 1075) R1075
theorem R9557 : ∃ j : ℕ, syracuseStep^[j] 9557 = 1 := reachStep (stepEq 12 (by rfl) ⟨3, by rfl⟩ : syracuseStep 9557 = 7) R7
theorem R10781 : ∃ j : ℕ, syracuseStep^[j] 10781 = 1 := reachStep (stepEq 3 (by rfl) ⟨2021, by rfl⟩ : syracuseStep 10781 = 4043) R4043
theorem R11461 : ∃ j : ℕ, syracuseStep^[j] 11461 = 1 := reachStep (stepEq 4 (by rfl) ⟨1074, by rfl⟩ : syracuseStep 11461 = 2149) R2149
theorem R21005 : ∃ j : ℕ, syracuseStep^[j] 21005 = 1 := reachStep (stepEq 3 (by rfl) ⟨3938, by rfl⟩ : syracuseStep 21005 = 7877) R7877
theorem R25 : ∃ j : ℕ, syracuseStep^[j] 25 = 1 := reachStep (stepEq 2 (by rfl) ⟨9, by rfl⟩ : syracuseStep 25 = 19) R19
theorem R49 : ∃ j : ℕ, syracuseStep^[j] 49 = 1 := reachStep (stepEq 2 (by rfl) ⟨18, by rfl⟩ : syracuseStep 49 = 37) R37
theorem R51 : ∃ j : ℕ, syracuseStep^[j] 51 = 1 := reachStep (stepEq 1 (by rfl) ⟨38, by rfl⟩ : syracuseStep 51 = 77) R77
theorem R99 : ∃ j : ℕ, syracuseStep^[j] 99 = 1 := reachStep (stepEq 1 (by rfl) ⟨74, by rfl⟩ : syracuseStep 99 = 149) R149
theorem R101 : ∃ j : ℕ, syracuseStep^[j] 101 = 1 := reachStep (stepEq 4 (by rfl) ⟨9, by rfl⟩ : syracuseStep 101 = 19) R19
theorem R197 : ∃ j : ℕ, syracuseStep^[j] 197 = 1 := reachStep (stepEq 4 (by rfl) ⟨18, by rfl⟩ : syracuseStep 197 = 37) R37
theorem R205 : ∃ j : ℕ, syracuseStep^[j] 205 = 1 := reachStep (stepEq 3 (by rfl) ⟨38, by rfl⟩ : syracuseStep 205 = 77) R77
theorem R217 : ∃ j : ℕ, syracuseStep^[j] 217 = 1 := reachStep (stepEq 2 (by rfl) ⟨81, by rfl⟩ : syracuseStep 217 = 163) R163
theorem R397 : ∃ j : ℕ, syracuseStep^[j] 397 = 1 := reachStep (stepEq 3 (by rfl) ⟨74, by rfl⟩ : syracuseStep 397 = 149) R149
theorem R405 : ∃ j : ℕ, syracuseStep^[j] 405 = 1 := reachStep (stepEq 6 (by rfl) ⟨9, by rfl⟩ : syracuseStep 405 = 19) R19
theorem R433 : ∃ j : ℕ, syracuseStep^[j] 433 = 1 := reachStep (stepEq 2 (by rfl) ⟨162, by rfl⟩ : syracuseStep 433 = 325) R325
theorem R435 : ∃ j : ℕ, syracuseStep^[j] 435 = 1 := reachStep (stepEq 1 (by rfl) ⟨326, by rfl⟩ : syracuseStep 435 = 653) R653
theorem R441 : ∃ j : ℕ, syracuseStep^[j] 441 = 1 := reachStep (stepEq 2 (by rfl) ⟨165, by rfl⟩ : syracuseStep 441 = 331) R331
theorem R475 : ∃ j : ℕ, syracuseStep^[j] 475 = 1 := reachStep (stepEq 1 (by rfl) ⟨356, by rfl⟩ : syracuseStep 475 = 713) R713
theorem R789 : ∃ j : ℕ, syracuseStep^[j] 789 = 1 := reachStep (stepEq 6 (by rfl) ⟨18, by rfl⟩ : syracuseStep 789 = 37) R37
theorem R821 : ∃ j : ℕ, syracuseStep^[j] 821 = 1 := reachStep (stepEq 5 (by rfl) ⟨38, by rfl⟩ : syracuseStep 821 = 77) R77
theorem R833 : ∃ j : ℕ, syracuseStep^[j] 833 = 1 := reachStep (stepEq 2 (by rfl) ⟨312, by rfl⟩ : syracuseStep 833 = 625) R625
theorem R857 : ∃ j : ℕ, syracuseStep^[j] 857 = 1 := reachStep (stepEq 2 (by rfl) ⟨321, by rfl⟩ : syracuseStep 857 = 643) R643
theorem R867 : ∃ j : ℕ, syracuseStep^[j] 867 = 1 := reachStep (stepEq 1 (by rfl) ⟨650, by rfl⟩ : syracuseStep 867 = 1301) R1301
theorem R869 : ∃ j : ℕ, syracuseStep^[j] 869 = 1 := reachStep (stepEq 4 (by rfl) ⟨81, by rfl⟩ : syracuseStep 869 = 163) R163
theorem R875 : ∃ j : ℕ, syracuseStep^[j] 875 = 1 := reachStep (stepEq 1 (by rfl) ⟨656, by rfl⟩ : syracuseStep 875 = 1313) R1313
theorem R883 : ∃ j : ℕ, syracuseStep^[j] 883 = 1 := reachStep (stepEq 1 (by rfl) ⟨662, by rfl⟩ : syracuseStep 883 = 1325) R1325
theorem R951 : ∃ j : ℕ, syracuseStep^[j] 951 = 1 := reachStep (stepEq 1 (by rfl) ⟨713, by rfl⟩ : syracuseStep 951 = 1427) R1427
theorem R953 : ∃ j : ℕ, syracuseStep^[j] 953 = 1 := reachStep (stepEq 2 (by rfl) ⟨357, by rfl⟩ : syracuseStep 953 = 715) R715
theorem R955 : ∃ j : ℕ, syracuseStep^[j] 955 = 1 := reachStep (stepEq 1 (by rfl) ⟨716, by rfl⟩ : syracuseStep 955 = 1433) R1433
theorem R1589 : ∃ j : ℕ, syracuseStep^[j] 1589 = 1 := reachStep (stepEq 5 (by rfl) ⟨74, by rfl⟩ : syracuseStep 1589 = 149) R149
theorem R1621 : ∃ j : ℕ, syracuseStep^[j] 1621 = 1 := reachStep (stepEq 8 (by rfl) ⟨9, by rfl⟩ : syracuseStep 1621 = 19) R19
theorem R1649 : ∃ j : ℕ, syracuseStep^[j] 1649 = 1 := reachStep (stepEq 2 (by rfl) ⟨618, by rfl⟩ : syracuseStep 1649 = 1237) R1237
theorem R1667 : ∃ j : ℕ, syracuseStep^[j] 1667 = 1 := reachStep (stepEq 1 (by rfl) ⟨1250, by rfl⟩ : syracuseStep 1667 = 2501) R2501
theorem R1713 : ∃ j : ℕ, syracuseStep^[j] 1713 = 1 := reachStep (stepEq 2 (by rfl) ⟨642, by rfl⟩ : syracuseStep 1713 = 1285) R1285
theorem R1715 : ∃ j : ℕ, syracuseStep^[j] 1715 = 1 := reachStep (stepEq 1 (by rfl) ⟨1286, by rfl⟩ : syracuseStep 1715 = 2573) R2573
theorem R1733 : ∃ j : ℕ, syracuseStep^[j] 1733 = 1 := reachStep (stepEq 4 (by rfl) ⟨162, by rfl⟩ : syracuseStep 1733 = 325) R325
theorem R1741 : ∃ j : ℕ, syracuseStep^[j] 1741 = 1 := reachStep (stepEq 3 (by rfl) ⟨326, by rfl⟩ : syracuseStep 1741 = 653) R653
theorem R1751 : ∃ j : ℕ, syracuseStep^[j] 1751 = 1 := reachStep (stepEq 1 (by rfl) ⟨1313, by rfl⟩ : syracuseStep 1751 = 2627) R2627
theorem R1765 : ∃ j : ℕ, syracuseStep^[j] 1765 = 1 := reachStep (stepEq 4 (by rfl) ⟨165, by rfl⟩ : syracuseStep 1765 = 331) R331
theorem R1785 : ∃ j : ℕ, syracuseStep^[j] 1785 = 1 := reachStep (stepEq 2 (by rfl) ⟨669, by rfl⟩ : syracuseStep 1785 = 1339) R1339
theorem R1901 : ∃ j : ℕ, syracuseStep^[j] 1901 = 1 := reachStep (stepEq 3 (by rfl) ⟨356, by rfl⟩ : syracuseStep 1901 = 713) R713
theorem R1907 : ∃ j : ℕ, syracuseStep^[j] 1907 = 1 := reachStep (stepEq 1 (by rfl) ⟨1430, by rfl⟩ : syracuseStep 1907 = 2861) R2861
theorem R1911 : ∃ j : ℕ, syracuseStep^[j] 1911 = 1 := reachStep (stepEq 1 (by rfl) ⟨1433, by rfl⟩ : syracuseStep 1911 = 2867) R2867
theorem R3157 : ∃ j : ℕ, syracuseStep^[j] 3157 = 1 := reachStep (stepEq 8 (by rfl) ⟨18, by rfl⟩ : syracuseStep 3157 = 37) R37
theorem R3185 : ∃ j : ℕ, syracuseStep^[j] 3185 = 1 := reachStep (stepEq 2 (by rfl) ⟨1194, by rfl⟩ : syracuseStep 3185 = 2389) R2389
theorem R3285 : ∃ j : ℕ, syracuseStep^[j] 3285 = 1 := reachStep (stepEq 7 (by rfl) ⟨38, by rfl⟩ : syracuseStep 3285 = 77) R77
theorem R3299 : ∃ j : ℕ, syracuseStep^[j] 3299 = 1 := reachStep (stepEq 1 (by rfl) ⟨2474, by rfl⟩ : syracuseStep 3299 = 4949) R4949
theorem R3333 : ∃ j : ℕ, syracuseStep^[j] 3333 = 1 := reachStep (stepEq 4 (by rfl) ⟨312, by rfl⟩ : syracuseStep 3333 = 625) R625
theorem R3427 : ∃ j : ℕ, syracuseStep^[j] 3427 = 1 := reachStep (stepEq 1 (by rfl) ⟨2570, by rfl⟩ : syracuseStep 3427 = 5141) R5141
theorem R3429 : ∃ j : ℕ, syracuseStep^[j] 3429 = 1 := reachStep (stepEq 4 (by rfl) ⟨321, by rfl⟩ : syracuseStep 3429 = 643) R643
theorem R3469 : ∃ j : ℕ, syracuseStep^[j] 3469 = 1 := reachStep (stepEq 3 (by rfl) ⟨650, by rfl⟩ : syracuseStep 3469 = 1301) R1301
theorem R3477 : ∃ j : ℕ, syracuseStep^[j] 3477 = 1 := reachStep (stepEq 6 (by rfl) ⟨81, by rfl⟩ : syracuseStep 3477 = 163) R163
theorem R3501 : ∃ j : ℕ, syracuseStep^[j] 3501 = 1 := reachStep (stepEq 3 (by rfl) ⟨656, by rfl⟩ : syracuseStep 3501 = 1313) R1313
theorem R3533 : ∃ j : ℕ, syracuseStep^[j] 3533 = 1 := reachStep (stepEq 3 (by rfl) ⟨662, by rfl⟩ : syracuseStep 3533 = 1325) R1325
theorem R3537 : ∃ j : ℕ, syracuseStep^[j] 3537 = 1 := reachStep (stepEq 2 (by rfl) ⟨1326, by rfl⟩ : syracuseStep 3537 = 2653) R2653
theorem R3571 : ∃ j : ℕ, syracuseStep^[j] 3571 = 1 := reachStep (stepEq 1 (by rfl) ⟨2678, by rfl⟩ : syracuseStep 3571 = 5357) R5357
theorem R3593 : ∃ j : ℕ, syracuseStep^[j] 3593 = 1 := reachStep (stepEq 2 (by rfl) ⟨1347, by rfl⟩ : syracuseStep 3593 = 2695) R2695
theorem R3801 : ∃ j : ℕ, syracuseStep^[j] 3801 = 1 := reachStep (stepEq 2 (by rfl) ⟨1425, by rfl⟩ : syracuseStep 3801 = 2851) R2851
theorem R3805 : ∃ j : ℕ, syracuseStep^[j] 3805 = 1 := reachStep (stepEq 3 (by rfl) ⟨713, by rfl⟩ : syracuseStep 3805 = 1427) R1427
theorem R3813 : ∃ j : ℕ, syracuseStep^[j] 3813 = 1 := reachStep (stepEq 4 (by rfl) ⟨357, by rfl⟩ : syracuseStep 3813 = 715) R715
theorem R3819 : ∃ j : ℕ, syracuseStep^[j] 3819 = 1 := reachStep (stepEq 1 (by rfl) ⟨2864, by rfl⟩ : syracuseStep 3819 = 5729) R5729
theorem R3821 : ∃ j : ℕ, syracuseStep^[j] 3821 = 1 := reachStep (stepEq 3 (by rfl) ⟨716, by rfl⟩ : syracuseStep 3821 = 1433) R1433
theorem R6357 : ∃ j : ℕ, syracuseStep^[j] 6357 = 1 := reachStep (stepEq 7 (by rfl) ⟨74, by rfl⟩ : syracuseStep 6357 = 149) R149
theorem R6371 : ∃ j : ℕ, syracuseStep^[j] 6371 = 1 := reachStep (stepEq 1 (by rfl) ⟨4778, by rfl⟩ : syracuseStep 6371 = 9557) R9557
theorem R6485 : ∃ j : ℕ, syracuseStep^[j] 6485 = 1 := reachStep (stepEq 10 (by rfl) ⟨9, by rfl⟩ : syracuseStep 6485 = 19) R19
theorem R6597 : ∃ j : ℕ, syracuseStep^[j] 6597 = 1 := reachStep (stepEq 4 (by rfl) ⟨618, by rfl⟩ : syracuseStep 6597 = 1237) R1237
theorem R6669 : ∃ j : ℕ, syracuseStep^[j] 6669 = 1 := reachStep (stepEq 3 (by rfl) ⟨1250, by rfl⟩ : syracuseStep 6669 = 2501) R2501
theorem R6673 : ∃ j : ℕ, syracuseStep^[j] 6673 = 1 := reachStep (stepEq 2 (by rfl) ⟨2502, by rfl⟩ : syracuseStep 6673 = 5005) R5005
theorem R6853 : ∃ j : ℕ, syracuseStep^[j] 6853 = 1 := reachStep (stepEq 4 (by rfl) ⟨642, by rfl⟩ : syracuseStep 6853 = 1285) R1285
theorem R6965 : ∃ j : ℕ, syracuseStep^[j] 6965 = 1 := reachStep (stepEq 5 (by rfl) ⟨326, by rfl⟩ : syracuseStep 6965 = 653) R653
theorem R6977 : ∃ j : ℕ, syracuseStep^[j] 6977 = 1 := reachStep (stepEq 2 (by rfl) ⟨2616, by rfl⟩ : syracuseStep 6977 = 5233) R5233
theorem R7001 : ∃ j : ℕ, syracuseStep^[j] 7001 = 1 := reachStep (stepEq 2 (by rfl) ⟨2625, by rfl⟩ : syracuseStep 7001 = 5251) R5251
theorem R7061 : ∃ j : ℕ, syracuseStep^[j] 7061 = 1 := reachStep (stepEq 6 (by rfl) ⟨165, by rfl⟩ : syracuseStep 7061 = 331) R331
theorem R7141 : ∃ j : ℕ, syracuseStep^[j] 7141 = 1 := reachStep (stepEq 4 (by rfl) ⟨669, by rfl⟩ : syracuseStep 7141 = 1339) R1339
theorem R7187 : ∃ j : ℕ, syracuseStep^[j] 7187 = 1 := reachStep (stepEq 1 (by rfl) ⟨5390, by rfl⟩ : syracuseStep 7187 = 10781) R10781
theorem R7601 : ∃ j : ℕ, syracuseStep^[j] 7601 = 1 := reachStep (stepEq 2 (by rfl) ⟨2850, by rfl⟩ : syracuseStep 7601 = 5701) R5701
theorem R7609 : ∃ j : ℕ, syracuseStep^[j] 7609 = 1 := reachStep (stepEq 2 (by rfl) ⟨2853, by rfl⟩ : syracuseStep 7609 = 5707) R5707
theorem R12629 : ∃ j : ℕ, syracuseStep^[j] 12629 = 1 := reachStep (stepEq 10 (by rfl) ⟨18, by rfl⟩ : syracuseStep 12629 = 37) R37
theorem R13709 : ∃ j : ℕ, syracuseStep^[j] 13709 = 1 := reachStep (stepEq 3 (by rfl) ⟨2570, by rfl⟩ : syracuseStep 13709 = 5141) R5141
theorem R13877 : ∃ j : ℕ, syracuseStep^[j] 13877 = 1 := reachStep (stepEq 5 (by rfl) ⟨650, by rfl⟩ : syracuseStep 13877 = 1301) R1301
theorem R14003 : ∃ j : ℕ, syracuseStep^[j] 14003 = 1 := reachStep (stepEq 1 (by rfl) ⟨10502, by rfl⟩ : syracuseStep 14003 = 21005) R21005
theorem R15281 : ∃ j : ℕ, syracuseStep^[j] 15281 = 1 := reachStep (stepEq 2 (by rfl) ⟨5730, by rfl⟩ : syracuseStep 15281 = 11461) R11461
theorem R28021 : ∃ j : ℕ, syracuseStep^[j] 28021 = 1 := reachStep (stepEq 5 (by rfl) ⟨1313, by rfl⟩ : syracuseStep 28021 = 2627) R2627
theorem R33 : ∃ j : ℕ, syracuseStep^[j] 33 = 1 := reachStep (stepEq 2 (by rfl) ⟨12, by rfl⟩ : syracuseStep 33 = 25) R25
theorem R65 : ∃ j : ℕ, syracuseStep^[j] 65 = 1 := reachStep (stepEq 2 (by rfl) ⟨24, by rfl⟩ : syracuseStep 65 = 49) R49
theorem R67 : ∃ j : ℕ, syracuseStep^[j] 67 = 1 := reachStep (stepEq 1 (by rfl) ⟨50, by rfl⟩ : syracuseStep 67 = 101) R101
theorem R131 : ∃ j : ℕ, syracuseStep^[j] 131 = 1 := reachStep (stepEq 1 (by rfl) ⟨98, by rfl⟩ : syracuseStep 131 = 197) R197
theorem R133 : ∃ j : ℕ, syracuseStep^[j] 133 = 1 := reachStep (stepEq 4 (by rfl) ⟨12, by rfl⟩ : syracuseStep 133 = 25) R25
theorem R261 : ∃ j : ℕ, syracuseStep^[j] 261 = 1 := reachStep (stepEq 4 (by rfl) ⟨24, by rfl⟩ : syracuseStep 261 = 49) R49
theorem R269 : ∃ j : ℕ, syracuseStep^[j] 269 = 1 := reachStep (stepEq 3 (by rfl) ⟨50, by rfl⟩ : syracuseStep 269 = 101) R101
theorem R273 : ∃ j : ℕ, syracuseStep^[j] 273 = 1 := reachStep (stepEq 2 (by rfl) ⟨102, by rfl⟩ : syracuseStep 273 = 205) R205
theorem R289 : ∃ j : ℕ, syracuseStep^[j] 289 = 1 := reachStep (stepEq 2 (by rfl) ⟨108, by rfl⟩ : syracuseStep 289 = 217) R217
theorem R525 : ∃ j : ℕ, syracuseStep^[j] 525 = 1 := reachStep (stepEq 3 (by rfl) ⟨98, by rfl⟩ : syracuseStep 525 = 197) R197
theorem R529 : ∃ j : ℕ, syracuseStep^[j] 529 = 1 := reachStep (stepEq 2 (by rfl) ⟨198, by rfl⟩ : syracuseStep 529 = 397) R397
theorem R533 : ∃ j : ℕ, syracuseStep^[j] 533 = 1 := reachStep (stepEq 6 (by rfl) ⟨12, by rfl⟩ : syracuseStep 533 = 25) R25
theorem R547 : ∃ j : ℕ, syracuseStep^[j] 547 = 1 := reachStep (stepEq 1 (by rfl) ⟨410, by rfl⟩ : syracuseStep 547 = 821) R821
theorem R555 : ∃ j : ℕ, syracuseStep^[j] 555 = 1 := reachStep (stepEq 1 (by rfl) ⟨416, by rfl⟩ : syracuseStep 555 = 833) R833
theorem R571 : ∃ j : ℕ, syracuseStep^[j] 571 = 1 := reachStep (stepEq 1 (by rfl) ⟨428, by rfl⟩ : syracuseStep 571 = 857) R857
theorem R577 : ∃ j : ℕ, syracuseStep^[j] 577 = 1 := reachStep (stepEq 2 (by rfl) ⟨216, by rfl⟩ : syracuseStep 577 = 433) R433
theorem R579 : ∃ j : ℕ, syracuseStep^[j] 579 = 1 := reachStep (stepEq 1 (by rfl) ⟨434, by rfl⟩ : syracuseStep 579 = 869) R869
theorem R583 : ∃ j : ℕ, syracuseStep^[j] 583 = 1 := reachStep (stepEq 1 (by rfl) ⟨437, by rfl⟩ : syracuseStep 583 = 875) R875
theorem R633 : ∃ j : ℕ, syracuseStep^[j] 633 = 1 := reachStep (stepEq 2 (by rfl) ⟨237, by rfl⟩ : syracuseStep 633 = 475) R475
theorem R635 : ∃ j : ℕ, syracuseStep^[j] 635 = 1 := reachStep (stepEq 1 (by rfl) ⟨476, by rfl⟩ : syracuseStep 635 = 953) R953
theorem R1045 : ∃ j : ℕ, syracuseStep^[j] 1045 = 1 := reachStep (stepEq 6 (by rfl) ⟨24, by rfl⟩ : syracuseStep 1045 = 49) R49
theorem R1059 : ∃ j : ℕ, syracuseStep^[j] 1059 = 1 := reachStep (stepEq 1 (by rfl) ⟨794, by rfl⟩ : syracuseStep 1059 = 1589) R1589
theorem R1077 : ∃ j : ℕ, syracuseStep^[j] 1077 = 1 := reachStep (stepEq 5 (by rfl) ⟨50, by rfl⟩ : syracuseStep 1077 = 101) R101
theorem R1093 : ∃ j : ℕ, syracuseStep^[j] 1093 = 1 := reachStep (stepEq 4 (by rfl) ⟨102, by rfl⟩ : syracuseStep 1093 = 205) R205
theorem R1099 : ∃ j : ℕ, syracuseStep^[j] 1099 = 1 := reachStep (stepEq 1 (by rfl) ⟨824, by rfl⟩ : syracuseStep 1099 = 1649) R1649
theorem R1111 : ∃ j : ℕ, syracuseStep^[j] 1111 = 1 := reachStep (stepEq 1 (by rfl) ⟨833, by rfl⟩ : syracuseStep 1111 = 1667) R1667
theorem R1143 : ∃ j : ℕ, syracuseStep^[j] 1143 = 1 := reachStep (stepEq 1 (by rfl) ⟨857, by rfl⟩ : syracuseStep 1143 = 1715) R1715
theorem R1155 : ∃ j : ℕ, syracuseStep^[j] 1155 = 1 := reachStep (stepEq 1 (by rfl) ⟨866, by rfl⟩ : syracuseStep 1155 = 1733) R1733
theorem R1157 : ∃ j : ℕ, syracuseStep^[j] 1157 = 1 := reachStep (stepEq 4 (by rfl) ⟨108, by rfl⟩ : syracuseStep 1157 = 217) R217
theorem R1167 : ∃ j : ℕ, syracuseStep^[j] 1167 = 1 := reachStep (stepEq 1 (by rfl) ⟨875, by rfl⟩ : syracuseStep 1167 = 1751) R1751
theorem R1177 : ∃ j : ℕ, syracuseStep^[j] 1177 = 1 := reachStep (stepEq 2 (by rfl) ⟨441, by rfl⟩ : syracuseStep 1177 = 883) R883
theorem R1267 : ∃ j : ℕ, syracuseStep^[j] 1267 = 1 := reachStep (stepEq 1 (by rfl) ⟨950, by rfl⟩ : syracuseStep 1267 = 1901) R1901
theorem R1271 : ∃ j : ℕ, syracuseStep^[j] 1271 = 1 := reachStep (stepEq 1 (by rfl) ⟨953, by rfl⟩ : syracuseStep 1271 = 1907) R1907
theorem R1273 : ∃ j : ℕ, syracuseStep^[j] 1273 = 1 := reachStep (stepEq 2 (by rfl) ⟨477, by rfl⟩ : syracuseStep 1273 = 955) R955
theorem R2101 : ∃ j : ℕ, syracuseStep^[j] 2101 = 1 := reachStep (stepEq 5 (by rfl) ⟨98, by rfl⟩ : syracuseStep 2101 = 197) R197
theorem R2117 : ∃ j : ℕ, syracuseStep^[j] 2117 = 1 := reachStep (stepEq 4 (by rfl) ⟨198, by rfl⟩ : syracuseStep 2117 = 397) R397
theorem R2123 : ∃ j : ℕ, syracuseStep^[j] 2123 = 1 := reachStep (stepEq 1 (by rfl) ⟨1592, by rfl⟩ : syracuseStep 2123 = 3185) R3185
theorem R2133 : ∃ j : ℕ, syracuseStep^[j] 2133 = 1 := reachStep (stepEq 8 (by rfl) ⟨12, by rfl⟩ : syracuseStep 2133 = 25) R25
theorem R2161 : ∃ j : ℕ, syracuseStep^[j] 2161 = 1 := reachStep (stepEq 2 (by rfl) ⟨810, by rfl⟩ : syracuseStep 2161 = 1621) R1621
theorem R2189 : ∃ j : ℕ, syracuseStep^[j] 2189 = 1 := reachStep (stepEq 3 (by rfl) ⟨410, by rfl⟩ : syracuseStep 2189 = 821) R821
theorem R2199 : ∃ j : ℕ, syracuseStep^[j] 2199 = 1 := reachStep (stepEq 1 (by rfl) ⟨1649, by rfl⟩ : syracuseStep 2199 = 3299) R3299
theorem R2221 : ∃ j : ℕ, syracuseStep^[j] 2221 = 1 := reachStep (stepEq 3 (by rfl) ⟨416, by rfl⟩ : syracuseStep 2221 = 833) R833
theorem R2285 : ∃ j : ℕ, syracuseStep^[j] 2285 = 1 := reachStep (stepEq 3 (by rfl) ⟨428, by rfl⟩ : syracuseStep 2285 = 857) R857
theorem R2309 : ∃ j : ℕ, syracuseStep^[j] 2309 = 1 := reachStep (stepEq 4 (by rfl) ⟨216, by rfl⟩ : syracuseStep 2309 = 433) R433
theorem R2317 : ∃ j : ℕ, syracuseStep^[j] 2317 = 1 := reachStep (stepEq 3 (by rfl) ⟨434, by rfl⟩ : syracuseStep 2317 = 869) R869
theorem R2321 : ∃ j : ℕ, syracuseStep^[j] 2321 = 1 := reachStep (stepEq 2 (by rfl) ⟨870, by rfl⟩ : syracuseStep 2321 = 1741) R1741
theorem R2333 : ∃ j : ℕ, syracuseStep^[j] 2333 = 1 := reachStep (stepEq 3 (by rfl) ⟨437, by rfl⟩ : syracuseStep 2333 = 875) R875
theorem R2353 : ∃ j : ℕ, syracuseStep^[j] 2353 = 1 := reachStep (stepEq 2 (by rfl) ⟨882, by rfl⟩ : syracuseStep 2353 = 1765) R1765
theorem R2355 : ∃ j : ℕ, syracuseStep^[j] 2355 = 1 := reachStep (stepEq 1 (by rfl) ⟨1766, by rfl⟩ : syracuseStep 2355 = 3533) R3533
theorem R2395 : ∃ j : ℕ, syracuseStep^[j] 2395 = 1 := reachStep (stepEq 1 (by rfl) ⟨1796, by rfl⟩ : syracuseStep 2395 = 3593) R3593
theorem R2533 : ∃ j : ℕ, syracuseStep^[j] 2533 = 1 := reachStep (stepEq 4 (by rfl) ⟨237, by rfl⟩ : syracuseStep 2533 = 475) R475
theorem R2541 : ∃ j : ℕ, syracuseStep^[j] 2541 = 1 := reachStep (stepEq 3 (by rfl) ⟨476, by rfl⟩ : syracuseStep 2541 = 953) R953
theorem R2547 : ∃ j : ℕ, syracuseStep^[j] 2547 = 1 := reachStep (stepEq 1 (by rfl) ⟨1910, by rfl⟩ : syracuseStep 2547 = 3821) R3821
theorem R4181 : ∃ j : ℕ, syracuseStep^[j] 4181 = 1 := reachStep (stepEq 8 (by rfl) ⟨24, by rfl⟩ : syracuseStep 4181 = 49) R49
theorem R4209 : ∃ j : ℕ, syracuseStep^[j] 4209 = 1 := reachStep (stepEq 2 (by rfl) ⟨1578, by rfl⟩ : syracuseStep 4209 = 3157) R3157
theorem R4237 : ∃ j : ℕ, syracuseStep^[j] 4237 = 1 := reachStep (stepEq 3 (by rfl) ⟨794, by rfl⟩ : syracuseStep 4237 = 1589) R1589
theorem R4247 : ∃ j : ℕ, syracuseStep^[j] 4247 = 1 := reachStep (stepEq 1 (by rfl) ⟨3185, by rfl⟩ : syracuseStep 4247 = 6371) R6371
theorem R4309 : ∃ j : ℕ, syracuseStep^[j] 4309 = 1 := reachStep (stepEq 7 (by rfl) ⟨50, by rfl⟩ : syracuseStep 4309 = 101) R101
theorem R4323 : ∃ j : ℕ, syracuseStep^[j] 4323 = 1 := reachStep (stepEq 1 (by rfl) ⟨3242, by rfl⟩ : syracuseStep 4323 = 6485) R6485
theorem R4373 : ∃ j : ℕ, syracuseStep^[j] 4373 = 1 := reachStep (stepEq 6 (by rfl) ⟨102, by rfl⟩ : syracuseStep 4373 = 205) R205
theorem R4397 : ∃ j : ℕ, syracuseStep^[j] 4397 = 1 := reachStep (stepEq 3 (by rfl) ⟨824, by rfl⟩ : syracuseStep 4397 = 1649) R1649
theorem R4445 : ∃ j : ℕ, syracuseStep^[j] 4445 = 1 := reachStep (stepEq 3 (by rfl) ⟨833, by rfl⟩ : syracuseStep 4445 = 1667) R1667
theorem R4569 : ∃ j : ℕ, syracuseStep^[j] 4569 = 1 := reachStep (stepEq 2 (by rfl) ⟨1713, by rfl⟩ : syracuseStep 4569 = 3427) R3427
theorem R4573 : ∃ j : ℕ, syracuseStep^[j] 4573 = 1 := reachStep (stepEq 3 (by rfl) ⟨857, by rfl⟩ : syracuseStep 4573 = 1715) R1715
theorem R37361 : ∃ j : ℕ, syracuseStep^[j] 37361 = 1 := reachStep (stepEq 2 (by rfl) ⟨14010, by rfl⟩ : syracuseStep 37361 = 28021) R28021
theorem R4621 : ∃ j : ℕ, syracuseStep^[j] 4621 = 1 := reachStep (stepEq 3 (by rfl) ⟨866, by rfl⟩ : syracuseStep 4621 = 1733) R1733
theorem R4625 : ∃ j : ℕ, syracuseStep^[j] 4625 = 1 := reachStep (stepEq 2 (by rfl) ⟨1734, by rfl⟩ : syracuseStep 4625 = 3469) R3469
theorem R4629 : ∃ j : ℕ, syracuseStep^[j] 4629 = 1 := reachStep (stepEq 6 (by rfl) ⟨108, by rfl⟩ : syracuseStep 4629 = 217) R217
theorem R4643 : ∃ j : ℕ, syracuseStep^[j] 4643 = 1 := reachStep (stepEq 1 (by rfl) ⟨3482, by rfl⟩ : syracuseStep 4643 = 6965) R6965
theorem R4651 : ∃ j : ℕ, syracuseStep^[j] 4651 = 1 := reachStep (stepEq 1 (by rfl) ⟨3488, by rfl⟩ : syracuseStep 4651 = 6977) R6977
theorem R4667 : ∃ j : ℕ, syracuseStep^[j] 4667 = 1 := reachStep (stepEq 1 (by rfl) ⟨3500, by rfl⟩ : syracuseStep 4667 = 7001) R7001
theorem R4669 : ∃ j : ℕ, syracuseStep^[j] 4669 = 1 := reachStep (stepEq 3 (by rfl) ⟨875, by rfl⟩ : syracuseStep 4669 = 1751) R1751
theorem R4707 : ∃ j : ℕ, syracuseStep^[j] 4707 = 1 := reachStep (stepEq 1 (by rfl) ⟨3530, by rfl⟩ : syracuseStep 4707 = 7061) R7061
theorem R4709 : ∃ j : ℕ, syracuseStep^[j] 4709 = 1 := reachStep (stepEq 4 (by rfl) ⟨441, by rfl⟩ : syracuseStep 4709 = 883) R883
theorem R4761 : ∃ j : ℕ, syracuseStep^[j] 4761 = 1 := reachStep (stepEq 2 (by rfl) ⟨1785, by rfl⟩ : syracuseStep 4761 = 3571) R3571
theorem R4791 : ∃ j : ℕ, syracuseStep^[j] 4791 = 1 := reachStep (stepEq 1 (by rfl) ⟨3593, by rfl⟩ : syracuseStep 4791 = 7187) R7187
theorem R5067 : ∃ j : ℕ, syracuseStep^[j] 5067 = 1 := reachStep (stepEq 1 (by rfl) ⟨3800, by rfl⟩ : syracuseStep 5067 = 7601) R7601
theorem R5069 : ∃ j : ℕ, syracuseStep^[j] 5069 = 1 := reachStep (stepEq 3 (by rfl) ⟨950, by rfl⟩ : syracuseStep 5069 = 1901) R1901
theorem R5073 : ∃ j : ℕ, syracuseStep^[j] 5073 = 1 := reachStep (stepEq 2 (by rfl) ⟨1902, by rfl⟩ : syracuseStep 5073 = 3805) R3805
theorem R5085 : ∃ j : ℕ, syracuseStep^[j] 5085 = 1 := reachStep (stepEq 3 (by rfl) ⟨953, by rfl⟩ : syracuseStep 5085 = 1907) R1907
theorem R5093 : ∃ j : ℕ, syracuseStep^[j] 5093 = 1 := reachStep (stepEq 4 (by rfl) ⟨477, by rfl⟩ : syracuseStep 5093 = 955) R955
theorem R8405 : ∃ j : ℕ, syracuseStep^[j] 8405 = 1 := reachStep (stepEq 7 (by rfl) ⟨98, by rfl⟩ : syracuseStep 8405 = 197) R197
theorem R8419 : ∃ j : ℕ, syracuseStep^[j] 8419 = 1 := reachStep (stepEq 1 (by rfl) ⟨6314, by rfl⟩ : syracuseStep 8419 = 12629) R12629
theorem R8645 : ∃ j : ℕ, syracuseStep^[j] 8645 = 1 := reachStep (stepEq 4 (by rfl) ⟨810, by rfl⟩ : syracuseStep 8645 = 1621) R1621
theorem R8885 : ∃ j : ℕ, syracuseStep^[j] 8885 = 1 := reachStep (stepEq 5 (by rfl) ⟨416, by rfl⟩ : syracuseStep 8885 = 833) R833
theorem R8897 : ∃ j : ℕ, syracuseStep^[j] 8897 = 1 := reachStep (stepEq 2 (by rfl) ⟨3336, by rfl⟩ : syracuseStep 8897 = 6673) R6673
theorem R9137 : ∃ j : ℕ, syracuseStep^[j] 9137 = 1 := reachStep (stepEq 2 (by rfl) ⟨3426, by rfl⟩ : syracuseStep 9137 = 6853) R6853
theorem R9139 : ∃ j : ℕ, syracuseStep^[j] 9139 = 1 := reachStep (stepEq 1 (by rfl) ⟨6854, by rfl⟩ : syracuseStep 9139 = 13709) R13709
theorem R9251 : ∃ j : ℕ, syracuseStep^[j] 9251 = 1 := reachStep (stepEq 1 (by rfl) ⟨6938, by rfl⟩ : syracuseStep 9251 = 13877) R13877
theorem R9269 : ∃ j : ℕ, syracuseStep^[j] 9269 = 1 := reachStep (stepEq 5 (by rfl) ⟨434, by rfl⟩ : syracuseStep 9269 = 869) R869
theorem R9335 : ∃ j : ℕ, syracuseStep^[j] 9335 = 1 := reachStep (stepEq 1 (by rfl) ⟨7001, by rfl⟩ : syracuseStep 9335 = 14003) R14003
theorem R9413 : ∃ j : ℕ, syracuseStep^[j] 9413 = 1 := reachStep (stepEq 4 (by rfl) ⟨882, by rfl⟩ : syracuseStep 9413 = 1765) R1765
theorem R9521 : ∃ j : ℕ, syracuseStep^[j] 9521 = 1 := reachStep (stepEq 2 (by rfl) ⟨3570, by rfl⟩ : syracuseStep 9521 = 7141) R7141
theorem R9581 : ∃ j : ℕ, syracuseStep^[j] 9581 = 1 := reachStep (stepEq 3 (by rfl) ⟨1796, by rfl⟩ : syracuseStep 9581 = 3593) R3593
theorem R10133 : ∃ j : ℕ, syracuseStep^[j] 10133 = 1 := reachStep (stepEq 6 (by rfl) ⟨237, by rfl⟩ : syracuseStep 10133 = 475) R475
theorem R10145 : ∃ j : ℕ, syracuseStep^[j] 10145 = 1 := reachStep (stepEq 2 (by rfl) ⟨3804, by rfl⟩ : syracuseStep 10145 = 7609) R7609
theorem R10165 : ∃ j : ℕ, syracuseStep^[j] 10165 = 1 := reachStep (stepEq 5 (by rfl) ⟨476, by rfl⟩ : syracuseStep 10165 = 953) R953
theorem R10187 : ∃ j : ℕ, syracuseStep^[j] 10187 = 1 := reachStep (stepEq 1 (by rfl) ⟨7640, by rfl⟩ : syracuseStep 10187 = 15281) R15281
theorem R16949 : ∃ j : ℕ, syracuseStep^[j] 16949 = 1 := reachStep (stepEq 5 (by rfl) ⟨794, by rfl⟩ : syracuseStep 16949 = 1589) R1589
theorem R18829 : ∃ j : ℕ, syracuseStep^[j] 18829 = 1 := reachStep (stepEq 3 (by rfl) ⟨3530, by rfl⟩ : syracuseStep 18829 = 7061) R7061
theorem R19045 : ∃ j : ℕ, syracuseStep^[j] 19045 = 1 := reachStep (stepEq 4 (by rfl) ⟨1785, by rfl⟩ : syracuseStep 19045 = 3571) R3571
theorem R43 : ∃ j : ℕ, syracuseStep^[j] 43 = 1 := reachStep (stepEq 1 (by rfl) ⟨32, by rfl⟩ : syracuseStep 43 = 65) R65
theorem R87 : ∃ j : ℕ, syracuseStep^[j] 87 = 1 := reachStep (stepEq 1 (by rfl) ⟨65, by rfl⟩ : syracuseStep 87 = 131) R131
theorem R89 : ∃ j : ℕ, syracuseStep^[j] 89 = 1 := reachStep (stepEq 2 (by rfl) ⟨33, by rfl⟩ : syracuseStep 89 = 67) R67
theorem R173 : ∃ j : ℕ, syracuseStep^[j] 173 = 1 := reachStep (stepEq 3 (by rfl) ⟨32, by rfl⟩ : syracuseStep 173 = 65) R65
theorem R177 : ∃ j : ℕ, syracuseStep^[j] 177 = 1 := reachStep (stepEq 2 (by rfl) ⟨66, by rfl⟩ : syracuseStep 177 = 133) R133
theorem R179 : ∃ j : ℕ, syracuseStep^[j] 179 = 1 := reachStep (stepEq 1 (by rfl) ⟨134, by rfl⟩ : syracuseStep 179 = 269) R269
theorem R349 : ∃ j : ℕ, syracuseStep^[j] 349 = 1 := reachStep (stepEq 3 (by rfl) ⟨65, by rfl⟩ : syracuseStep 349 = 131) R131
theorem R355 : ∃ j : ℕ, syracuseStep^[j] 355 = 1 := reachStep (stepEq 1 (by rfl) ⟨266, by rfl⟩ : syracuseStep 355 = 533) R533
theorem R357 : ∃ j : ℕ, syracuseStep^[j] 357 = 1 := reachStep (stepEq 4 (by rfl) ⟨33, by rfl⟩ : syracuseStep 357 = 67) R67
theorem R385 : ∃ j : ℕ, syracuseStep^[j] 385 = 1 := reachStep (stepEq 2 (by rfl) ⟨144, by rfl⟩ : syracuseStep 385 = 289) R289
theorem R423 : ∃ j : ℕ, syracuseStep^[j] 423 = 1 := reachStep (stepEq 1 (by rfl) ⟨317, by rfl⟩ : syracuseStep 423 = 635) R635
theorem R693 : ∃ j : ℕ, syracuseStep^[j] 693 = 1 := reachStep (stepEq 5 (by rfl) ⟨32, by rfl⟩ : syracuseStep 693 = 65) R65
theorem R705 : ∃ j : ℕ, syracuseStep^[j] 705 = 1 := reachStep (stepEq 2 (by rfl) ⟨264, by rfl⟩ : syracuseStep 705 = 529) R529
theorem R709 : ∃ j : ℕ, syracuseStep^[j] 709 = 1 := reachStep (stepEq 4 (by rfl) ⟨66, by rfl⟩ : syracuseStep 709 = 133) R133
theorem R717 : ∃ j : ℕ, syracuseStep^[j] 717 = 1 := reachStep (stepEq 3 (by rfl) ⟨134, by rfl⟩ : syracuseStep 717 = 269) R269
theorem R729 : ∃ j : ℕ, syracuseStep^[j] 729 = 1 := reachStep (stepEq 2 (by rfl) ⟨273, by rfl⟩ : syracuseStep 729 = 547) R547
theorem R761 : ∃ j : ℕ, syracuseStep^[j] 761 = 1 := reachStep (stepEq 2 (by rfl) ⟨285, by rfl⟩ : syracuseStep 761 = 571) R571
theorem R769 : ∃ j : ℕ, syracuseStep^[j] 769 = 1 := reachStep (stepEq 2 (by rfl) ⟨288, by rfl⟩ : syracuseStep 769 = 577) R577
theorem R771 : ∃ j : ℕ, syracuseStep^[j] 771 = 1 := reachStep (stepEq 1 (by rfl) ⟨578, by rfl⟩ : syracuseStep 771 = 1157) R1157
theorem R777 : ∃ j : ℕ, syracuseStep^[j] 777 = 1 := reachStep (stepEq 2 (by rfl) ⟨291, by rfl⟩ : syracuseStep 777 = 583) R583
theorem R847 : ∃ j : ℕ, syracuseStep^[j] 847 = 1 := reachStep (stepEq 1 (by rfl) ⟨635, by rfl⟩ : syracuseStep 847 = 1271) R1271
theorem R1393 : ∃ j : ℕ, syracuseStep^[j] 1393 = 1 := reachStep (stepEq 2 (by rfl) ⟨522, by rfl⟩ : syracuseStep 1393 = 1045) R1045
theorem R1397 : ∃ j : ℕ, syracuseStep^[j] 1397 = 1 := reachStep (stepEq 5 (by rfl) ⟨65, by rfl⟩ : syracuseStep 1397 = 131) R131
theorem R1411 : ∃ j : ℕ, syracuseStep^[j] 1411 = 1 := reachStep (stepEq 1 (by rfl) ⟨1058, by rfl⟩ : syracuseStep 1411 = 2117) R2117
theorem R1415 : ∃ j : ℕ, syracuseStep^[j] 1415 = 1 := reachStep (stepEq 1 (by rfl) ⟨1061, by rfl⟩ : syracuseStep 1415 = 2123) R2123
theorem R1421 : ∃ j : ℕ, syracuseStep^[j] 1421 = 1 := reachStep (stepEq 3 (by rfl) ⟨266, by rfl⟩ : syracuseStep 1421 = 533) R533
theorem R1429 : ∃ j : ℕ, syracuseStep^[j] 1429 = 1 := reachStep (stepEq 6 (by rfl) ⟨33, by rfl⟩ : syracuseStep 1429 = 67) R67
theorem R1457 : ∃ j : ℕ, syracuseStep^[j] 1457 = 1 := reachStep (stepEq 2 (by rfl) ⟨546, by rfl⟩ : syracuseStep 1457 = 1093) R1093
theorem R1459 : ∃ j : ℕ, syracuseStep^[j] 1459 = 1 := reachStep (stepEq 1 (by rfl) ⟨1094, by rfl⟩ : syracuseStep 1459 = 2189) R2189
theorem R1465 : ∃ j : ℕ, syracuseStep^[j] 1465 = 1 := reachStep (stepEq 2 (by rfl) ⟨549, by rfl⟩ : syracuseStep 1465 = 1099) R1099
theorem R1481 : ∃ j : ℕ, syracuseStep^[j] 1481 = 1 := reachStep (stepEq 2 (by rfl) ⟨555, by rfl⟩ : syracuseStep 1481 = 1111) R1111
theorem R1523 : ∃ j : ℕ, syracuseStep^[j] 1523 = 1 := reachStep (stepEq 1 (by rfl) ⟨1142, by rfl⟩ : syracuseStep 1523 = 2285) R2285
theorem R1539 : ∃ j : ℕ, syracuseStep^[j] 1539 = 1 := reachStep (stepEq 1 (by rfl) ⟨1154, by rfl⟩ : syracuseStep 1539 = 2309) R2309
theorem R1541 : ∃ j : ℕ, syracuseStep^[j] 1541 = 1 := reachStep (stepEq 4 (by rfl) ⟨144, by rfl⟩ : syracuseStep 1541 = 289) R289
theorem R1547 : ∃ j : ℕ, syracuseStep^[j] 1547 = 1 := reachStep (stepEq 1 (by rfl) ⟨1160, by rfl⟩ : syracuseStep 1547 = 2321) R2321
theorem R1555 : ∃ j : ℕ, syracuseStep^[j] 1555 = 1 := reachStep (stepEq 1 (by rfl) ⟨1166, by rfl⟩ : syracuseStep 1555 = 2333) R2333
theorem R1569 : ∃ j : ℕ, syracuseStep^[j] 1569 = 1 := reachStep (stepEq 2 (by rfl) ⟨588, by rfl⟩ : syracuseStep 1569 = 1177) R1177
theorem R1689 : ∃ j : ℕ, syracuseStep^[j] 1689 = 1 := reachStep (stepEq 2 (by rfl) ⟨633, by rfl⟩ : syracuseStep 1689 = 1267) R1267
theorem R1693 : ∃ j : ℕ, syracuseStep^[j] 1693 = 1 := reachStep (stepEq 3 (by rfl) ⟨317, by rfl⟩ : syracuseStep 1693 = 635) R635
theorem R1697 : ∃ j : ℕ, syracuseStep^[j] 1697 = 1 := reachStep (stepEq 2 (by rfl) ⟨636, by rfl⟩ : syracuseStep 1697 = 1273) R1273
theorem R2773 : ∃ j : ℕ, syracuseStep^[j] 2773 = 1 := reachStep (stepEq 7 (by rfl) ⟨32, by rfl⟩ : syracuseStep 2773 = 65) R65
theorem R2787 : ∃ j : ℕ, syracuseStep^[j] 2787 = 1 := reachStep (stepEq 1 (by rfl) ⟨2090, by rfl⟩ : syracuseStep 2787 = 4181) R4181
theorem R2801 : ∃ j : ℕ, syracuseStep^[j] 2801 = 1 := reachStep (stepEq 2 (by rfl) ⟨1050, by rfl⟩ : syracuseStep 2801 = 2101) R2101
theorem R2821 : ∃ j : ℕ, syracuseStep^[j] 2821 = 1 := reachStep (stepEq 4 (by rfl) ⟨264, by rfl⟩ : syracuseStep 2821 = 529) R529
theorem R2831 : ∃ j : ℕ, syracuseStep^[j] 2831 = 1 := reachStep (stepEq 1 (by rfl) ⟨2123, by rfl⟩ : syracuseStep 2831 = 4247) R4247
theorem R2837 : ∃ j : ℕ, syracuseStep^[j] 2837 = 1 := reachStep (stepEq 6 (by rfl) ⟨66, by rfl⟩ : syracuseStep 2837 = 133) R133
theorem R2869 : ∃ j : ℕ, syracuseStep^[j] 2869 = 1 := reachStep (stepEq 5 (by rfl) ⟨134, by rfl⟩ : syracuseStep 2869 = 269) R269
theorem R2881 : ∃ j : ℕ, syracuseStep^[j] 2881 = 1 := reachStep (stepEq 2 (by rfl) ⟨1080, by rfl⟩ : syracuseStep 2881 = 2161) R2161
theorem R2915 : ∃ j : ℕ, syracuseStep^[j] 2915 = 1 := reachStep (stepEq 1 (by rfl) ⟨2186, by rfl⟩ : syracuseStep 2915 = 4373) R4373
theorem R2917 : ∃ j : ℕ, syracuseStep^[j] 2917 = 1 := reachStep (stepEq 4 (by rfl) ⟨273, by rfl⟩ : syracuseStep 2917 = 547) R547
theorem R2931 : ∃ j : ℕ, syracuseStep^[j] 2931 = 1 := reachStep (stepEq 1 (by rfl) ⟨2198, by rfl⟩ : syracuseStep 2931 = 4397) R4397
theorem R2961 : ∃ j : ℕ, syracuseStep^[j] 2961 = 1 := reachStep (stepEq 2 (by rfl) ⟨1110, by rfl⟩ : syracuseStep 2961 = 2221) R2221
theorem R2963 : ∃ j : ℕ, syracuseStep^[j] 2963 = 1 := reachStep (stepEq 1 (by rfl) ⟨2222, by rfl⟩ : syracuseStep 2963 = 4445) R4445
theorem R3045 : ∃ j : ℕ, syracuseStep^[j] 3045 = 1 := reachStep (stepEq 4 (by rfl) ⟨285, by rfl⟩ : syracuseStep 3045 = 571) R571
theorem R3077 : ∃ j : ℕ, syracuseStep^[j] 3077 = 1 := reachStep (stepEq 4 (by rfl) ⟨288, by rfl⟩ : syracuseStep 3077 = 577) R577
theorem R3083 : ∃ j : ℕ, syracuseStep^[j] 3083 = 1 := reachStep (stepEq 1 (by rfl) ⟨2312, by rfl⟩ : syracuseStep 3083 = 4625) R4625
theorem R3085 : ∃ j : ℕ, syracuseStep^[j] 3085 = 1 := reachStep (stepEq 3 (by rfl) ⟨578, by rfl⟩ : syracuseStep 3085 = 1157) R1157
theorem R3089 : ∃ j : ℕ, syracuseStep^[j] 3089 = 1 := reachStep (stepEq 2 (by rfl) ⟨1158, by rfl⟩ : syracuseStep 3089 = 2317) R2317
theorem R3095 : ∃ j : ℕ, syracuseStep^[j] 3095 = 1 := reachStep (stepEq 1 (by rfl) ⟨2321, by rfl⟩ : syracuseStep 3095 = 4643) R4643
theorem R3109 : ∃ j : ℕ, syracuseStep^[j] 3109 = 1 := reachStep (stepEq 4 (by rfl) ⟨291, by rfl⟩ : syracuseStep 3109 = 583) R583
theorem R3111 : ∃ j : ℕ, syracuseStep^[j] 3111 = 1 := reachStep (stepEq 1 (by rfl) ⟨2333, by rfl⟩ : syracuseStep 3111 = 4667) R4667
theorem R3137 : ∃ j : ℕ, syracuseStep^[j] 3137 = 1 := reachStep (stepEq 2 (by rfl) ⟨1176, by rfl⟩ : syracuseStep 3137 = 2353) R2353
theorem R3139 : ∃ j : ℕ, syracuseStep^[j] 3139 = 1 := reachStep (stepEq 1 (by rfl) ⟨2354, by rfl⟩ : syracuseStep 3139 = 4709) R4709
theorem R3193 : ∃ j : ℕ, syracuseStep^[j] 3193 = 1 := reachStep (stepEq 2 (by rfl) ⟨1197, by rfl⟩ : syracuseStep 3193 = 2395) R2395
theorem R3377 : ∃ j : ℕ, syracuseStep^[j] 3377 = 1 := reachStep (stepEq 2 (by rfl) ⟨1266, by rfl⟩ : syracuseStep 3377 = 2533) R2533
theorem R3379 : ∃ j : ℕ, syracuseStep^[j] 3379 = 1 := reachStep (stepEq 1 (by rfl) ⟨2534, by rfl⟩ : syracuseStep 3379 = 5069) R5069
theorem R3389 : ∃ j : ℕ, syracuseStep^[j] 3389 = 1 := reachStep (stepEq 3 (by rfl) ⟨635, by rfl⟩ : syracuseStep 3389 = 1271) R1271
theorem R3395 : ∃ j : ℕ, syracuseStep^[j] 3395 = 1 := reachStep (stepEq 1 (by rfl) ⟨2546, by rfl⟩ : syracuseStep 3395 = 5093) R5093
theorem R5573 : ∃ j : ℕ, syracuseStep^[j] 5573 = 1 := reachStep (stepEq 4 (by rfl) ⟨522, by rfl⟩ : syracuseStep 5573 = 1045) R1045
theorem R5589 : ∃ j : ℕ, syracuseStep^[j] 5589 = 1 := reachStep (stepEq 7 (by rfl) ⟨65, by rfl⟩ : syracuseStep 5589 = 131) R131
theorem R5603 : ∃ j : ℕ, syracuseStep^[j] 5603 = 1 := reachStep (stepEq 1 (by rfl) ⟨4202, by rfl⟩ : syracuseStep 5603 = 8405) R8405
theorem R5645 : ∃ j : ℕ, syracuseStep^[j] 5645 = 1 := reachStep (stepEq 3 (by rfl) ⟨1058, by rfl⟩ : syracuseStep 5645 = 2117) R2117
theorem R5649 : ∃ j : ℕ, syracuseStep^[j] 5649 = 1 := reachStep (stepEq 2 (by rfl) ⟨2118, by rfl⟩ : syracuseStep 5649 = 4237) R4237
theorem R5661 : ∃ j : ℕ, syracuseStep^[j] 5661 = 1 := reachStep (stepEq 3 (by rfl) ⟨1061, by rfl⟩ : syracuseStep 5661 = 2123) R2123
theorem R5685 : ∃ j : ℕ, syracuseStep^[j] 5685 = 1 := reachStep (stepEq 5 (by rfl) ⟨266, by rfl⟩ : syracuseStep 5685 = 533) R533
theorem R5717 : ∃ j : ℕ, syracuseStep^[j] 5717 = 1 := reachStep (stepEq 8 (by rfl) ⟨33, by rfl⟩ : syracuseStep 5717 = 67) R67
theorem R5745 : ∃ j : ℕ, syracuseStep^[j] 5745 = 1 := reachStep (stepEq 2 (by rfl) ⟨2154, by rfl⟩ : syracuseStep 5745 = 4309) R4309
theorem R5763 : ∃ j : ℕ, syracuseStep^[j] 5763 = 1 := reachStep (stepEq 1 (by rfl) ⟨4322, by rfl⟩ : syracuseStep 5763 = 8645) R8645
theorem R5829 : ∃ j : ℕ, syracuseStep^[j] 5829 = 1 := reachStep (stepEq 4 (by rfl) ⟨546, by rfl⟩ : syracuseStep 5829 = 1093) R1093
theorem R5837 : ∃ j : ℕ, syracuseStep^[j] 5837 = 1 := reachStep (stepEq 3 (by rfl) ⟨1094, by rfl⟩ : syracuseStep 5837 = 2189) R2189
theorem R5861 : ∃ j : ℕ, syracuseStep^[j] 5861 = 1 := reachStep (stepEq 4 (by rfl) ⟨549, by rfl⟩ : syracuseStep 5861 = 1099) R1099
theorem R5923 : ∃ j : ℕ, syracuseStep^[j] 5923 = 1 := reachStep (stepEq 1 (by rfl) ⟨4442, by rfl⟩ : syracuseStep 5923 = 8885) R8885
theorem R5925 : ∃ j : ℕ, syracuseStep^[j] 5925 = 1 := reachStep (stepEq 4 (by rfl) ⟨555, by rfl⟩ : syracuseStep 5925 = 1111) R1111
theorem R5931 : ∃ j : ℕ, syracuseStep^[j] 5931 = 1 := reachStep (stepEq 1 (by rfl) ⟨4448, by rfl⟩ : syracuseStep 5931 = 8897) R8897
theorem R6091 : ∃ j : ℕ, syracuseStep^[j] 6091 = 1 := reachStep (stepEq 1 (by rfl) ⟨4568, by rfl⟩ : syracuseStep 6091 = 9137) R9137
theorem R6093 : ∃ j : ℕ, syracuseStep^[j] 6093 = 1 := reachStep (stepEq 3 (by rfl) ⟨1142, by rfl⟩ : syracuseStep 6093 = 2285) R2285
theorem R6097 : ∃ j : ℕ, syracuseStep^[j] 6097 = 1 := reachStep (stepEq 2 (by rfl) ⟨2286, by rfl⟩ : syracuseStep 6097 = 4573) R4573
theorem R6157 : ∃ j : ℕ, syracuseStep^[j] 6157 = 1 := reachStep (stepEq 3 (by rfl) ⟨1154, by rfl⟩ : syracuseStep 6157 = 2309) R2309
theorem R6161 : ∃ j : ℕ, syracuseStep^[j] 6161 = 1 := reachStep (stepEq 2 (by rfl) ⟨2310, by rfl⟩ : syracuseStep 6161 = 4621) R4621
theorem R6165 : ∃ j : ℕ, syracuseStep^[j] 6165 = 1 := reachStep (stepEq 6 (by rfl) ⟨144, by rfl⟩ : syracuseStep 6165 = 289) R289
theorem R6167 : ∃ j : ℕ, syracuseStep^[j] 6167 = 1 := reachStep (stepEq 1 (by rfl) ⟨4625, by rfl⟩ : syracuseStep 6167 = 9251) R9251
theorem R6179 : ∃ j : ℕ, syracuseStep^[j] 6179 = 1 := reachStep (stepEq 1 (by rfl) ⟨4634, by rfl⟩ : syracuseStep 6179 = 9269) R9269
theorem R6189 : ∃ j : ℕ, syracuseStep^[j] 6189 = 1 := reachStep (stepEq 3 (by rfl) ⟨1160, by rfl⟩ : syracuseStep 6189 = 2321) R2321
theorem R6201 : ∃ j : ℕ, syracuseStep^[j] 6201 = 1 := reachStep (stepEq 2 (by rfl) ⟨2325, by rfl⟩ : syracuseStep 6201 = 4651) R4651
theorem R6221 : ∃ j : ℕ, syracuseStep^[j] 6221 = 1 := reachStep (stepEq 3 (by rfl) ⟨1166, by rfl⟩ : syracuseStep 6221 = 2333) R2333
theorem R6223 : ∃ j : ℕ, syracuseStep^[j] 6223 = 1 := reachStep (stepEq 1 (by rfl) ⟨4667, by rfl⟩ : syracuseStep 6223 = 9335) R9335
theorem R6225 : ∃ j : ℕ, syracuseStep^[j] 6225 = 1 := reachStep (stepEq 2 (by rfl) ⟨2334, by rfl⟩ : syracuseStep 6225 = 4669) R4669
theorem R6275 : ∃ j : ℕ, syracuseStep^[j] 6275 = 1 := reachStep (stepEq 1 (by rfl) ⟨4706, by rfl⟩ : syracuseStep 6275 = 9413) R9413
theorem R6277 : ∃ j : ℕ, syracuseStep^[j] 6277 = 1 := reachStep (stepEq 4 (by rfl) ⟨588, by rfl⟩ : syracuseStep 6277 = 1177) R1177
theorem R6347 : ∃ j : ℕ, syracuseStep^[j] 6347 = 1 := reachStep (stepEq 1 (by rfl) ⟨4760, by rfl⟩ : syracuseStep 6347 = 9521) R9521
theorem R6387 : ∃ j : ℕ, syracuseStep^[j] 6387 = 1 := reachStep (stepEq 1 (by rfl) ⟨4790, by rfl⟩ : syracuseStep 6387 = 9581) R9581
theorem R6755 : ∃ j : ℕ, syracuseStep^[j] 6755 = 1 := reachStep (stepEq 1 (by rfl) ⟨5066, by rfl⟩ : syracuseStep 6755 = 10133) R10133
theorem R6763 : ∃ j : ℕ, syracuseStep^[j] 6763 = 1 := reachStep (stepEq 1 (by rfl) ⟨5072, by rfl⟩ : syracuseStep 6763 = 10145) R10145
theorem R6773 : ∃ j : ℕ, syracuseStep^[j] 6773 = 1 := reachStep (stepEq 5 (by rfl) ⟨317, by rfl⟩ : syracuseStep 6773 = 635) R635
theorem R6791 : ∃ j : ℕ, syracuseStep^[j] 6791 = 1 := reachStep (stepEq 1 (by rfl) ⟨5093, by rfl⟩ : syracuseStep 6791 = 10187) R10187
theorem R11225 : ∃ j : ℕ, syracuseStep^[j] 11225 = 1 := reachStep (stepEq 2 (by rfl) ⟨4209, by rfl⟩ : syracuseStep 11225 = 8419) R8419
theorem R11285 : ∃ j : ℕ, syracuseStep^[j] 11285 = 1 := reachStep (stepEq 6 (by rfl) ⟨264, by rfl⟩ : syracuseStep 11285 = 529) R529
theorem R11299 : ∃ j : ℕ, syracuseStep^[j] 11299 = 1 := reachStep (stepEq 1 (by rfl) ⟨8474, by rfl⟩ : syracuseStep 11299 = 16949) R16949
theorem R11477 : ∃ j : ℕ, syracuseStep^[j] 11477 = 1 := reachStep (stepEq 7 (by rfl) ⟨134, by rfl⟩ : syracuseStep 11477 = 269) R269
theorem R12185 : ∃ j : ℕ, syracuseStep^[j] 12185 = 1 := reachStep (stepEq 2 (by rfl) ⟨4569, by rfl⟩ : syracuseStep 12185 = 9139) R9139
theorem R45197 : ∃ j : ℕ, syracuseStep^[j] 45197 = 1 := reachStep (stepEq 3 (by rfl) ⟨8474, by rfl⟩ : syracuseStep 45197 = 16949) R16949
theorem R12437 : ∃ j : ℕ, syracuseStep^[j] 12437 = 1 := reachStep (stepEq 6 (by rfl) ⟨291, by rfl⟩ : syracuseStep 12437 = 583) R583
theorem R12773 : ∃ j : ℕ, syracuseStep^[j] 12773 = 1 := reachStep (stepEq 4 (by rfl) ⟨1197, by rfl⟩ : syracuseStep 12773 = 2395) R2395
theorem R13517 : ∃ j : ℕ, syracuseStep^[j] 13517 = 1 := reachStep (stepEq 3 (by rfl) ⟨2534, by rfl⟩ : syracuseStep 13517 = 5069) R5069
theorem R13553 : ∃ j : ℕ, syracuseStep^[j] 13553 = 1 := reachStep (stepEq 2 (by rfl) ⟨5082, by rfl⟩ : syracuseStep 13553 = 10165) R10165
theorem R24893 : ∃ j : ℕ, syracuseStep^[j] 24893 = 1 := reachStep (stepEq 3 (by rfl) ⟨4667, by rfl⟩ : syracuseStep 24893 = 9335) R9335
theorem R24907 : ∃ j : ℕ, syracuseStep^[j] 24907 = 1 := reachStep (stepEq 1 (by rfl) ⟨18680, by rfl⟩ : syracuseStep 24907 = 37361) R37361
theorem R25105 : ∃ j : ℕ, syracuseStep^[j] 25105 = 1 := reachStep (stepEq 2 (by rfl) ⟨9414, by rfl⟩ : syracuseStep 25105 = 18829) R18829
theorem R25109 : ∃ j : ℕ, syracuseStep^[j] 25109 = 1 := reachStep (stepEq 6 (by rfl) ⟨588, by rfl⟩ : syracuseStep 25109 = 1177) R1177
theorem R25393 : ∃ j : ℕ, syracuseStep^[j] 25393 = 1 := reachStep (stepEq 2 (by rfl) ⟨9522, by rfl⟩ : syracuseStep 25393 = 19045) R19045
theorem R27053 : ∃ j : ℕ, syracuseStep^[j] 27053 = 1 := reachStep (stepEq 3 (by rfl) ⟨5072, by rfl⟩ : syracuseStep 27053 = 10145) R10145
theorem R57 : ∃ j : ℕ, syracuseStep^[j] 57 = 1 := reachStep (stepEq 2 (by rfl) ⟨21, by rfl⟩ : syracuseStep 57 = 43) R43
theorem R59 : ∃ j : ℕ, syracuseStep^[j] 59 = 1 := reachStep (stepEq 1 (by rfl) ⟨44, by rfl⟩ : syracuseStep 59 = 89) R89
theorem R115 : ∃ j : ℕ, syracuseStep^[j] 115 = 1 := reachStep (stepEq 1 (by rfl) ⟨86, by rfl⟩ : syracuseStep 115 = 173) R173
theorem R32885 : ∃ j : ℕ, syracuseStep^[j] 32885 = 1 := reachStep (stepEq 5 (by rfl) ⟨1541, by rfl⟩ : syracuseStep 32885 = 3083) R3083
theorem R119 : ∃ j : ℕ, syracuseStep^[j] 119 = 1 := reachStep (stepEq 1 (by rfl) ⟨89, by rfl⟩ : syracuseStep 119 = 179) R179
theorem R229 : ∃ j : ℕ, syracuseStep^[j] 229 = 1 := reachStep (stepEq 4 (by rfl) ⟨21, by rfl⟩ : syracuseStep 229 = 43) R43
theorem R237 : ∃ j : ℕ, syracuseStep^[j] 237 = 1 := reachStep (stepEq 3 (by rfl) ⟨44, by rfl⟩ : syracuseStep 237 = 89) R89
theorem R33209 : ∃ j : ℕ, syracuseStep^[j] 33209 = 1 := reachStep (stepEq 2 (by rfl) ⟨12453, by rfl⟩ : syracuseStep 33209 = 24907) R24907
theorem R461 : ∃ j : ℕ, syracuseStep^[j] 461 = 1 := reachStep (stepEq 3 (by rfl) ⟨86, by rfl⟩ : syracuseStep 461 = 173) R173
theorem R465 : ∃ j : ℕ, syracuseStep^[j] 465 = 1 := reachStep (stepEq 2 (by rfl) ⟨174, by rfl⟩ : syracuseStep 465 = 349) R349
theorem R473 : ∃ j : ℕ, syracuseStep^[j] 473 = 1 := reachStep (stepEq 2 (by rfl) ⟨177, by rfl⟩ : syracuseStep 473 = 355) R355
theorem R477 : ∃ j : ℕ, syracuseStep^[j] 477 = 1 := reachStep (stepEq 3 (by rfl) ⟨89, by rfl⟩ : syracuseStep 477 = 179) R179
theorem R507 : ∃ j : ℕ, syracuseStep^[j] 507 = 1 := reachStep (stepEq 1 (by rfl) ⟨380, by rfl⟩ : syracuseStep 507 = 761) R761
theorem R513 : ∃ j : ℕ, syracuseStep^[j] 513 = 1 := reachStep (stepEq 2 (by rfl) ⟨192, by rfl⟩ : syracuseStep 513 = 385) R385
theorem R33473 : ∃ j : ℕ, syracuseStep^[j] 33473 = 1 := reachStep (stepEq 2 (by rfl) ⟨12552, by rfl⟩ : syracuseStep 33473 = 25105) R25105
theorem R917 : ∃ j : ℕ, syracuseStep^[j] 917 = 1 := reachStep (stepEq 6 (by rfl) ⟨21, by rfl⟩ : syracuseStep 917 = 43) R43
theorem R931 : ∃ j : ℕ, syracuseStep^[j] 931 = 1 := reachStep (stepEq 1 (by rfl) ⟨698, by rfl⟩ : syracuseStep 931 = 1397) R1397
theorem R943 : ∃ j : ℕ, syracuseStep^[j] 943 = 1 := reachStep (stepEq 1 (by rfl) ⟨707, by rfl⟩ : syracuseStep 943 = 1415) R1415
theorem R945 : ∃ j : ℕ, syracuseStep^[j] 945 = 1 := reachStep (stepEq 2 (by rfl) ⟨354, by rfl⟩ : syracuseStep 945 = 709) R709
theorem R947 : ∃ j : ℕ, syracuseStep^[j] 947 = 1 := reachStep (stepEq 1 (by rfl) ⟨710, by rfl⟩ : syracuseStep 947 = 1421) R1421
theorem R949 : ∃ j : ℕ, syracuseStep^[j] 949 = 1 := reachStep (stepEq 5 (by rfl) ⟨44, by rfl⟩ : syracuseStep 949 = 89) R89
theorem R971 : ∃ j : ℕ, syracuseStep^[j] 971 = 1 := reachStep (stepEq 1 (by rfl) ⟨728, by rfl⟩ : syracuseStep 971 = 1457) R1457
theorem R987 : ∃ j : ℕ, syracuseStep^[j] 987 = 1 := reachStep (stepEq 1 (by rfl) ⟨740, by rfl⟩ : syracuseStep 987 = 1481) R1481
theorem R1015 : ∃ j : ℕ, syracuseStep^[j] 1015 = 1 := reachStep (stepEq 1 (by rfl) ⟨761, by rfl⟩ : syracuseStep 1015 = 1523) R1523
theorem R1025 : ∃ j : ℕ, syracuseStep^[j] 1025 = 1 := reachStep (stepEq 2 (by rfl) ⟨384, by rfl⟩ : syracuseStep 1025 = 769) R769
theorem R1027 : ∃ j : ℕ, syracuseStep^[j] 1027 = 1 := reachStep (stepEq 1 (by rfl) ⟨770, by rfl⟩ : syracuseStep 1027 = 1541) R1541
theorem R1031 : ∃ j : ℕ, syracuseStep^[j] 1031 = 1 := reachStep (stepEq 1 (by rfl) ⟨773, by rfl⟩ : syracuseStep 1031 = 1547) R1547
theorem R33857 : ∃ j : ℕ, syracuseStep^[j] 33857 = 1 := reachStep (stepEq 2 (by rfl) ⟨12696, by rfl⟩ : syracuseStep 33857 = 25393) R25393
theorem R1129 : ∃ j : ℕ, syracuseStep^[j] 1129 = 1 := reachStep (stepEq 2 (by rfl) ⟨423, by rfl⟩ : syracuseStep 1129 = 847) R847
theorem R1131 : ∃ j : ℕ, syracuseStep^[j] 1131 = 1 := reachStep (stepEq 1 (by rfl) ⟨848, by rfl⟩ : syracuseStep 1131 = 1697) R1697
theorem R1845 : ∃ j : ℕ, syracuseStep^[j] 1845 = 1 := reachStep (stepEq 5 (by rfl) ⟨86, by rfl⟩ : syracuseStep 1845 = 173) R173
theorem R1857 : ∃ j : ℕ, syracuseStep^[j] 1857 = 1 := reachStep (stepEq 2 (by rfl) ⟨696, by rfl⟩ : syracuseStep 1857 = 1393) R1393
theorem R1861 : ∃ j : ℕ, syracuseStep^[j] 1861 = 1 := reachStep (stepEq 4 (by rfl) ⟨174, by rfl⟩ : syracuseStep 1861 = 349) R349
theorem R1867 : ∃ j : ℕ, syracuseStep^[j] 1867 = 1 := reachStep (stepEq 1 (by rfl) ⟨1400, by rfl⟩ : syracuseStep 1867 = 2801) R2801
theorem R1881 : ∃ j : ℕ, syracuseStep^[j] 1881 = 1 := reachStep (stepEq 2 (by rfl) ⟨705, by rfl⟩ : syracuseStep 1881 = 1411) R1411
theorem R1887 : ∃ j : ℕ, syracuseStep^[j] 1887 = 1 := reachStep (stepEq 1 (by rfl) ⟨1415, by rfl⟩ : syracuseStep 1887 = 2831) R2831
theorem R1891 : ∃ j : ℕ, syracuseStep^[j] 1891 = 1 := reachStep (stepEq 1 (by rfl) ⟨1418, by rfl⟩ : syracuseStep 1891 = 2837) R2837
theorem R1893 : ∃ j : ℕ, syracuseStep^[j] 1893 = 1 := reachStep (stepEq 4 (by rfl) ⟨177, by rfl⟩ : syracuseStep 1893 = 355) R355
theorem R1905 : ∃ j : ℕ, syracuseStep^[j] 1905 = 1 := reachStep (stepEq 2 (by rfl) ⟨714, by rfl⟩ : syracuseStep 1905 = 1429) R1429
theorem R1909 : ∃ j : ℕ, syracuseStep^[j] 1909 = 1 := reachStep (stepEq 5 (by rfl) ⟨89, by rfl⟩ : syracuseStep 1909 = 179) R179
theorem R1943 : ∃ j : ℕ, syracuseStep^[j] 1943 = 1 := reachStep (stepEq 1 (by rfl) ⟨1457, by rfl⟩ : syracuseStep 1943 = 2915) R2915
theorem R1945 : ∃ j : ℕ, syracuseStep^[j] 1945 = 1 := reachStep (stepEq 2 (by rfl) ⟨729, by rfl⟩ : syracuseStep 1945 = 1459) R1459
theorem R1953 : ∃ j : ℕ, syracuseStep^[j] 1953 = 1 := reachStep (stepEq 2 (by rfl) ⟨732, by rfl⟩ : syracuseStep 1953 = 1465) R1465
theorem R1975 : ∃ j : ℕ, syracuseStep^[j] 1975 = 1 := reachStep (stepEq 1 (by rfl) ⟨1481, by rfl⟩ : syracuseStep 1975 = 2963) R2963
theorem R2029 : ∃ j : ℕ, syracuseStep^[j] 2029 = 1 := reachStep (stepEq 3 (by rfl) ⟨380, by rfl⟩ : syracuseStep 2029 = 761) R761
theorem R2051 : ∃ j : ℕ, syracuseStep^[j] 2051 = 1 := reachStep (stepEq 1 (by rfl) ⟨1538, by rfl⟩ : syracuseStep 2051 = 3077) R3077
theorem R2053 : ∃ j : ℕ, syracuseStep^[j] 2053 = 1 := reachStep (stepEq 4 (by rfl) ⟨192, by rfl⟩ : syracuseStep 2053 = 385) R385
theorem R2055 : ∃ j : ℕ, syracuseStep^[j] 2055 = 1 := reachStep (stepEq 1 (by rfl) ⟨1541, by rfl⟩ : syracuseStep 2055 = 3083) R3083
theorem R2059 : ∃ j : ℕ, syracuseStep^[j] 2059 = 1 := reachStep (stepEq 1 (by rfl) ⟨1544, by rfl⟩ : syracuseStep 2059 = 3089) R3089
theorem R2063 : ∃ j : ℕ, syracuseStep^[j] 2063 = 1 := reachStep (stepEq 1 (by rfl) ⟨1547, by rfl⟩ : syracuseStep 2063 = 3095) R3095
theorem R2073 : ∃ j : ℕ, syracuseStep^[j] 2073 = 1 := reachStep (stepEq 2 (by rfl) ⟨777, by rfl⟩ : syracuseStep 2073 = 1555) R1555
theorem R2091 : ∃ j : ℕ, syracuseStep^[j] 2091 = 1 := reachStep (stepEq 1 (by rfl) ⟨1568, by rfl⟩ : syracuseStep 2091 = 3137) R3137
theorem R2251 : ∃ j : ℕ, syracuseStep^[j] 2251 = 1 := reachStep (stepEq 1 (by rfl) ⟨1688, by rfl⟩ : syracuseStep 2251 = 3377) R3377
theorem R2257 : ∃ j : ℕ, syracuseStep^[j] 2257 = 1 := reachStep (stepEq 2 (by rfl) ⟨846, by rfl⟩ : syracuseStep 2257 = 1693) R1693
theorem R2259 : ∃ j : ℕ, syracuseStep^[j] 2259 = 1 := reachStep (stepEq 1 (by rfl) ⟨1694, by rfl⟩ : syracuseStep 2259 = 3389) R3389
theorem R2263 : ∃ j : ℕ, syracuseStep^[j] 2263 = 1 := reachStep (stepEq 1 (by rfl) ⟨1697, by rfl⟩ : syracuseStep 2263 = 3395) R3395
theorem R3669 : ∃ j : ℕ, syracuseStep^[j] 3669 = 1 := reachStep (stepEq 8 (by rfl) ⟨21, by rfl⟩ : syracuseStep 3669 = 43) R43
theorem R3697 : ∃ j : ℕ, syracuseStep^[j] 3697 = 1 := reachStep (stepEq 2 (by rfl) ⟨1386, by rfl⟩ : syracuseStep 3697 = 2773) R2773
theorem R3715 : ∃ j : ℕ, syracuseStep^[j] 3715 = 1 := reachStep (stepEq 1 (by rfl) ⟨2786, by rfl⟩ : syracuseStep 3715 = 5573) R5573
theorem R3725 : ∃ j : ℕ, syracuseStep^[j] 3725 = 1 := reachStep (stepEq 3 (by rfl) ⟨698, by rfl⟩ : syracuseStep 3725 = 1397) R1397
theorem R3735 : ∃ j : ℕ, syracuseStep^[j] 3735 = 1 := reachStep (stepEq 1 (by rfl) ⟨2801, by rfl⟩ : syracuseStep 3735 = 5603) R5603
theorem R3761 : ∃ j : ℕ, syracuseStep^[j] 3761 = 1 := reachStep (stepEq 2 (by rfl) ⟨1410, by rfl⟩ : syracuseStep 3761 = 2821) R2821
theorem R3763 : ∃ j : ℕ, syracuseStep^[j] 3763 = 1 := reachStep (stepEq 1 (by rfl) ⟨2822, by rfl⟩ : syracuseStep 3763 = 5645) R5645
theorem R3773 : ∃ j : ℕ, syracuseStep^[j] 3773 = 1 := reachStep (stepEq 3 (by rfl) ⟨707, by rfl⟩ : syracuseStep 3773 = 1415) R1415
theorem R3781 : ∃ j : ℕ, syracuseStep^[j] 3781 = 1 := reachStep (stepEq 4 (by rfl) ⟨354, by rfl⟩ : syracuseStep 3781 = 709) R709
theorem R3789 : ∃ j : ℕ, syracuseStep^[j] 3789 = 1 := reachStep (stepEq 3 (by rfl) ⟨710, by rfl⟩ : syracuseStep 3789 = 1421) R1421
theorem R3797 : ∃ j : ℕ, syracuseStep^[j] 3797 = 1 := reachStep (stepEq 7 (by rfl) ⟨44, by rfl⟩ : syracuseStep 3797 = 89) R89
theorem R3811 : ∃ j : ℕ, syracuseStep^[j] 3811 = 1 := reachStep (stepEq 1 (by rfl) ⟨2858, by rfl⟩ : syracuseStep 3811 = 5717) R5717
theorem R3825 : ∃ j : ℕ, syracuseStep^[j] 3825 = 1 := reachStep (stepEq 2 (by rfl) ⟨1434, by rfl⟩ : syracuseStep 3825 = 2869) R2869
theorem R3841 : ∃ j : ℕ, syracuseStep^[j] 3841 = 1 := reachStep (stepEq 2 (by rfl) ⟨1440, by rfl⟩ : syracuseStep 3841 = 2881) R2881
theorem R3885 : ∃ j : ℕ, syracuseStep^[j] 3885 = 1 := reachStep (stepEq 3 (by rfl) ⟨728, by rfl⟩ : syracuseStep 3885 = 1457) R1457
theorem R3889 : ∃ j : ℕ, syracuseStep^[j] 3889 = 1 := reachStep (stepEq 2 (by rfl) ⟨1458, by rfl⟩ : syracuseStep 3889 = 2917) R2917
theorem R3891 : ∃ j : ℕ, syracuseStep^[j] 3891 = 1 := reachStep (stepEq 1 (by rfl) ⟨2918, by rfl⟩ : syracuseStep 3891 = 5837) R5837
theorem R3907 : ∃ j : ℕ, syracuseStep^[j] 3907 = 1 := reachStep (stepEq 1 (by rfl) ⟨2930, by rfl⟩ : syracuseStep 3907 = 5861) R5861
theorem R3949 : ∃ j : ℕ, syracuseStep^[j] 3949 = 1 := reachStep (stepEq 3 (by rfl) ⟨740, by rfl⟩ : syracuseStep 3949 = 1481) R1481
theorem R4061 : ∃ j : ℕ, syracuseStep^[j] 4061 = 1 := reachStep (stepEq 3 (by rfl) ⟨761, by rfl⟩ : syracuseStep 4061 = 1523) R1523
theorem R4101 : ∃ j : ℕ, syracuseStep^[j] 4101 = 1 := reachStep (stepEq 4 (by rfl) ⟨384, by rfl⟩ : syracuseStep 4101 = 769) R769
theorem R4107 : ∃ j : ℕ, syracuseStep^[j] 4107 = 1 := reachStep (stepEq 1 (by rfl) ⟨3080, by rfl⟩ : syracuseStep 4107 = 6161) R6161
theorem R4109 : ∃ j : ℕ, syracuseStep^[j] 4109 = 1 := reachStep (stepEq 3 (by rfl) ⟨770, by rfl⟩ : syracuseStep 4109 = 1541) R1541
theorem R4111 : ∃ j : ℕ, syracuseStep^[j] 4111 = 1 := reachStep (stepEq 1 (by rfl) ⟨3083, by rfl⟩ : syracuseStep 4111 = 6167) R6167
theorem R4113 : ∃ j : ℕ, syracuseStep^[j] 4113 = 1 := reachStep (stepEq 2 (by rfl) ⟨1542, by rfl⟩ : syracuseStep 4113 = 3085) R3085
theorem R4119 : ∃ j : ℕ, syracuseStep^[j] 4119 = 1 := reachStep (stepEq 1 (by rfl) ⟨3089, by rfl⟩ : syracuseStep 4119 = 6179) R6179
theorem R4125 : ∃ j : ℕ, syracuseStep^[j] 4125 = 1 := reachStep (stepEq 3 (by rfl) ⟨773, by rfl⟩ : syracuseStep 4125 = 1547) R1547
theorem R4145 : ∃ j : ℕ, syracuseStep^[j] 4145 = 1 := reachStep (stepEq 2 (by rfl) ⟨1554, by rfl⟩ : syracuseStep 4145 = 3109) R3109
theorem R4147 : ∃ j : ℕ, syracuseStep^[j] 4147 = 1 := reachStep (stepEq 1 (by rfl) ⟨3110, by rfl⟩ : syracuseStep 4147 = 6221) R6221
theorem R4183 : ∃ j : ℕ, syracuseStep^[j] 4183 = 1 := reachStep (stepEq 1 (by rfl) ⟨3137, by rfl⟩ : syracuseStep 4183 = 6275) R6275
theorem R4185 : ∃ j : ℕ, syracuseStep^[j] 4185 = 1 := reachStep (stepEq 2 (by rfl) ⟨1569, by rfl⟩ : syracuseStep 4185 = 3139) R3139
theorem R4231 : ∃ j : ℕ, syracuseStep^[j] 4231 = 1 := reachStep (stepEq 1 (by rfl) ⟨3173, by rfl⟩ : syracuseStep 4231 = 6347) R6347
theorem R4257 : ∃ j : ℕ, syracuseStep^[j] 4257 = 1 := reachStep (stepEq 2 (by rfl) ⟨1596, by rfl⟩ : syracuseStep 4257 = 3193) R3193
theorem R4503 : ∃ j : ℕ, syracuseStep^[j] 4503 = 1 := reachStep (stepEq 1 (by rfl) ⟨3377, by rfl⟩ : syracuseStep 4503 = 6755) R6755
theorem R4505 : ∃ j : ℕ, syracuseStep^[j] 4505 = 1 := reachStep (stepEq 2 (by rfl) ⟨1689, by rfl⟩ : syracuseStep 4505 = 3379) R3379
theorem R4515 : ∃ j : ℕ, syracuseStep^[j] 4515 = 1 := reachStep (stepEq 1 (by rfl) ⟨3386, by rfl⟩ : syracuseStep 4515 = 6773) R6773
theorem R4517 : ∃ j : ℕ, syracuseStep^[j] 4517 = 1 := reachStep (stepEq 4 (by rfl) ⟨423, by rfl⟩ : syracuseStep 4517 = 847) R847
theorem R4525 : ∃ j : ℕ, syracuseStep^[j] 4525 = 1 := reachStep (stepEq 3 (by rfl) ⟨848, by rfl⟩ : syracuseStep 4525 = 1697) R1697
theorem R4527 : ∃ j : ℕ, syracuseStep^[j] 4527 = 1 := reachStep (stepEq 1 (by rfl) ⟨3395, by rfl⟩ : syracuseStep 4527 = 6791) R6791
theorem R7381 : ∃ j : ℕ, syracuseStep^[j] 7381 = 1 := reachStep (stepEq 7 (by rfl) ⟨86, by rfl⟩ : syracuseStep 7381 = 173) R173
theorem R7429 : ∃ j : ℕ, syracuseStep^[j] 7429 = 1 := reachStep (stepEq 4 (by rfl) ⟨696, by rfl⟩ : syracuseStep 7429 = 1393) R1393
theorem R7445 : ∃ j : ℕ, syracuseStep^[j] 7445 = 1 := reachStep (stepEq 6 (by rfl) ⟨174, by rfl⟩ : syracuseStep 7445 = 349) R349
theorem R7469 : ∃ j : ℕ, syracuseStep^[j] 7469 = 1 := reachStep (stepEq 3 (by rfl) ⟨1400, by rfl⟩ : syracuseStep 7469 = 2801) R2801
theorem R7483 : ∃ j : ℕ, syracuseStep^[j] 7483 = 1 := reachStep (stepEq 1 (by rfl) ⟨5612, by rfl⟩ : syracuseStep 7483 = 11225) R11225
theorem R7523 : ∃ j : ℕ, syracuseStep^[j] 7523 = 1 := reachStep (stepEq 1 (by rfl) ⟨5642, by rfl⟩ : syracuseStep 7523 = 11285) R11285
theorem R7565 : ∃ j : ℕ, syracuseStep^[j] 7565 = 1 := reachStep (stepEq 3 (by rfl) ⟨1418, by rfl⟩ : syracuseStep 7565 = 2837) R2837
theorem R7573 : ∃ j : ℕ, syracuseStep^[j] 7573 = 1 := reachStep (stepEq 6 (by rfl) ⟨177, by rfl⟩ : syracuseStep 7573 = 355) R355
theorem R7637 : ∃ j : ℕ, syracuseStep^[j] 7637 = 1 := reachStep (stepEq 7 (by rfl) ⟨89, by rfl⟩ : syracuseStep 7637 = 179) R179
theorem R7651 : ∃ j : ℕ, syracuseStep^[j] 7651 = 1 := reachStep (stepEq 1 (by rfl) ⟨5738, by rfl⟩ : syracuseStep 7651 = 11477) R11477
theorem R7781 : ∃ j : ℕ, syracuseStep^[j] 7781 = 1 := reachStep (stepEq 4 (by rfl) ⟨729, by rfl⟩ : syracuseStep 7781 = 1459) R1459
theorem R7897 : ∃ j : ℕ, syracuseStep^[j] 7897 = 1 := reachStep (stepEq 2 (by rfl) ⟨2961, by rfl⟩ : syracuseStep 7897 = 5923) R5923
theorem R7901 : ∃ j : ℕ, syracuseStep^[j] 7901 = 1 := reachStep (stepEq 3 (by rfl) ⟨1481, by rfl⟩ : syracuseStep 7901 = 2963) R2963
theorem R8117 : ∃ j : ℕ, syracuseStep^[j] 8117 = 1 := reachStep (stepEq 5 (by rfl) ⟨380, by rfl⟩ : syracuseStep 8117 = 761) R761
theorem R8123 : ∃ j : ℕ, syracuseStep^[j] 8123 = 1 := reachStep (stepEq 1 (by rfl) ⟨6092, by rfl⟩ : syracuseStep 8123 = 12185) R12185
theorem R8129 : ∃ j : ℕ, syracuseStep^[j] 8129 = 1 := reachStep (stepEq 2 (by rfl) ⟨3048, by rfl⟩ : syracuseStep 8129 = 6097) R6097
theorem R8213 : ∃ j : ℕ, syracuseStep^[j] 8213 = 1 := reachStep (stepEq 6 (by rfl) ⟨192, by rfl⟩ : syracuseStep 8213 = 385) R385
theorem R8221 : ∃ j : ℕ, syracuseStep^[j] 8221 = 1 := reachStep (stepEq 3 (by rfl) ⟨1541, by rfl⟩ : syracuseStep 8221 = 3083) R3083
theorem R8237 : ∃ j : ℕ, syracuseStep^[j] 8237 = 1 := reachStep (stepEq 3 (by rfl) ⟨1544, by rfl⟩ : syracuseStep 8237 = 3089) R3089
theorem R8291 : ∃ j : ℕ, syracuseStep^[j] 8291 = 1 := reachStep (stepEq 1 (by rfl) ⟨6218, by rfl⟩ : syracuseStep 8291 = 12437) R12437
theorem R8297 : ∃ j : ℕ, syracuseStep^[j] 8297 = 1 := reachStep (stepEq 2 (by rfl) ⟨3111, by rfl⟩ : syracuseStep 8297 = 6223) R6223
theorem R8369 : ∃ j : ℕ, syracuseStep^[j] 8369 = 1 := reachStep (stepEq 2 (by rfl) ⟨3138, by rfl⟩ : syracuseStep 8369 = 6277) R6277
theorem R8515 : ∃ j : ℕ, syracuseStep^[j] 8515 = 1 := reachStep (stepEq 1 (by rfl) ⟨6386, by rfl⟩ : syracuseStep 8515 = 12773) R12773
theorem R9005 : ∃ j : ℕ, syracuseStep^[j] 9005 = 1 := reachStep (stepEq 3 (by rfl) ⟨1688, by rfl⟩ : syracuseStep 9005 = 3377) R3377
theorem R9011 : ∃ j : ℕ, syracuseStep^[j] 9011 = 1 := reachStep (stepEq 1 (by rfl) ⟨6758, by rfl⟩ : syracuseStep 9011 = 13517) R13517
theorem R9017 : ∃ j : ℕ, syracuseStep^[j] 9017 = 1 := reachStep (stepEq 2 (by rfl) ⟨3381, by rfl⟩ : syracuseStep 9017 = 6763) R6763
theorem R9029 : ∃ j : ℕ, syracuseStep^[j] 9029 = 1 := reachStep (stepEq 4 (by rfl) ⟨846, by rfl⟩ : syracuseStep 9029 = 1693) R1693
theorem R9035 : ∃ j : ℕ, syracuseStep^[j] 9035 = 1 := reachStep (stepEq 1 (by rfl) ⟨6776, by rfl⟩ : syracuseStep 9035 = 13553) R13553
theorem R9053 : ∃ j : ℕ, syracuseStep^[j] 9053 = 1 := reachStep (stepEq 3 (by rfl) ⟨1697, by rfl⟩ : syracuseStep 9053 = 3395) R3395
theorem R15065 : ∃ j : ℕ, syracuseStep^[j] 15065 = 1 := reachStep (stepEq 2 (by rfl) ⟨5649, by rfl⟩ : syracuseStep 15065 = 11299) R11299
theorem R16595 : ∃ j : ℕ, syracuseStep^[j] 16595 = 1 := reachStep (stepEq 1 (by rfl) ⟨12446, by rfl⟩ : syracuseStep 16595 = 24893) R24893
theorem R16733 : ∃ j : ℕ, syracuseStep^[j] 16733 = 1 := reachStep (stepEq 3 (by rfl) ⟨3137, by rfl⟩ : syracuseStep 16733 = 6275) R6275
theorem R16739 : ∃ j : ℕ, syracuseStep^[j] 16739 = 1 := reachStep (stepEq 1 (by rfl) ⟨12554, by rfl⟩ : syracuseStep 16739 = 25109) R25109
theorem R18035 : ∃ j : ℕ, syracuseStep^[j] 18035 = 1 := reachStep (stepEq 1 (by rfl) ⟨13526, by rfl⟩ : syracuseStep 18035 = 27053) R27053
theorem R30131 : ∃ j : ℕ, syracuseStep^[j] 30131 = 1 := reachStep (stepEq 1 (by rfl) ⟨22598, by rfl⟩ : syracuseStep 30131 = 45197) R45197
theorem R30293 : ∃ j : ℕ, syracuseStep^[j] 30293 = 1 := reachStep (stepEq 8 (by rfl) ⟨177, by rfl⟩ : syracuseStep 30293 = 355) R355
theorem R31589 : ∃ j : ℕ, syracuseStep^[j] 31589 = 1 := reachStep (stepEq 4 (by rfl) ⟨2961, by rfl⟩ : syracuseStep 31589 = 5923) R5923
theorem R39 : ∃ j : ℕ, syracuseStep^[j] 39 = 1 := reachStep (stepEq 1 (by rfl) ⟨29, by rfl⟩ : syracuseStep 39 = 59) R59
theorem R79 : ∃ j : ℕ, syracuseStep^[j] 79 = 1 := reachStep (stepEq 1 (by rfl) ⟨59, by rfl⟩ : syracuseStep 79 = 119) R119
theorem R153 : ∃ j : ℕ, syracuseStep^[j] 153 = 1 := reachStep (stepEq 2 (by rfl) ⟨57, by rfl⟩ : syracuseStep 153 = 115) R115
theorem R157 : ∃ j : ℕ, syracuseStep^[j] 157 = 1 := reachStep (stepEq 3 (by rfl) ⟨29, by rfl⟩ : syracuseStep 157 = 59) R59
theorem R305 : ∃ j : ℕ, syracuseStep^[j] 305 = 1 := reachStep (stepEq 2 (by rfl) ⟨114, by rfl⟩ : syracuseStep 305 = 229) R229
theorem R307 : ∃ j : ℕ, syracuseStep^[j] 307 = 1 := reachStep (stepEq 1 (by rfl) ⟨230, by rfl⟩ : syracuseStep 307 = 461) R461
theorem R315 : ∃ j : ℕ, syracuseStep^[j] 315 = 1 := reachStep (stepEq 1 (by rfl) ⟨236, by rfl⟩ : syracuseStep 315 = 473) R473
theorem R317 : ∃ j : ℕ, syracuseStep^[j] 317 = 1 := reachStep (stepEq 3 (by rfl) ⟨59, by rfl⟩ : syracuseStep 317 = 119) R119
theorem R611 : ∃ j : ℕ, syracuseStep^[j] 611 = 1 := reachStep (stepEq 1 (by rfl) ⟨458, by rfl⟩ : syracuseStep 611 = 917) R917
theorem R613 : ∃ j : ℕ, syracuseStep^[j] 613 = 1 := reachStep (stepEq 4 (by rfl) ⟨57, by rfl⟩ : syracuseStep 613 = 115) R115
theorem R629 : ∃ j : ℕ, syracuseStep^[j] 629 = 1 := reachStep (stepEq 5 (by rfl) ⟨29, by rfl⟩ : syracuseStep 629 = 59) R59
theorem R631 : ∃ j : ℕ, syracuseStep^[j] 631 = 1 := reachStep (stepEq 1 (by rfl) ⟨473, by rfl⟩ : syracuseStep 631 = 947) R947
theorem R647 : ∃ j : ℕ, syracuseStep^[j] 647 = 1 := reachStep (stepEq 1 (by rfl) ⟨485, by rfl⟩ : syracuseStep 647 = 971) R971
theorem R683 : ∃ j : ℕ, syracuseStep^[j] 683 = 1 := reachStep (stepEq 1 (by rfl) ⟨512, by rfl⟩ : syracuseStep 683 = 1025) R1025
theorem R687 : ∃ j : ℕ, syracuseStep^[j] 687 = 1 := reachStep (stepEq 1 (by rfl) ⟨515, by rfl⟩ : syracuseStep 687 = 1031) R1031
theorem R1221 : ∃ j : ℕ, syracuseStep^[j] 1221 = 1 := reachStep (stepEq 4 (by rfl) ⟨114, by rfl⟩ : syracuseStep 1221 = 229) R229
theorem R1229 : ∃ j : ℕ, syracuseStep^[j] 1229 = 1 := reachStep (stepEq 3 (by rfl) ⟨230, by rfl⟩ : syracuseStep 1229 = 461) R461
theorem R1241 : ∃ j : ℕ, syracuseStep^[j] 1241 = 1 := reachStep (stepEq 2 (by rfl) ⟨465, by rfl⟩ : syracuseStep 1241 = 931) R931
theorem R1257 : ∃ j : ℕ, syracuseStep^[j] 1257 = 1 := reachStep (stepEq 2 (by rfl) ⟨471, by rfl⟩ : syracuseStep 1257 = 943) R943
theorem R1261 : ∃ j : ℕ, syracuseStep^[j] 1261 = 1 := reachStep (stepEq 3 (by rfl) ⟨236, by rfl⟩ : syracuseStep 1261 = 473) R473
theorem R1265 : ∃ j : ℕ, syracuseStep^[j] 1265 = 1 := reachStep (stepEq 2 (by rfl) ⟨474, by rfl⟩ : syracuseStep 1265 = 949) R949
theorem R1269 : ∃ j : ℕ, syracuseStep^[j] 1269 = 1 := reachStep (stepEq 5 (by rfl) ⟨59, by rfl⟩ : syracuseStep 1269 = 119) R119
theorem R1295 : ∃ j : ℕ, syracuseStep^[j] 1295 = 1 := reachStep (stepEq 1 (by rfl) ⟨971, by rfl⟩ : syracuseStep 1295 = 1943) R1943
theorem R1353 : ∃ j : ℕ, syracuseStep^[j] 1353 = 1 := reachStep (stepEq 2 (by rfl) ⟨507, by rfl⟩ : syracuseStep 1353 = 1015) R1015
theorem R1367 : ∃ j : ℕ, syracuseStep^[j] 1367 = 1 := reachStep (stepEq 1 (by rfl) ⟨1025, by rfl⟩ : syracuseStep 1367 = 2051) R2051
theorem R1369 : ∃ j : ℕ, syracuseStep^[j] 1369 = 1 := reachStep (stepEq 2 (by rfl) ⟨513, by rfl⟩ : syracuseStep 1369 = 1027) R1027
theorem R1375 : ∃ j : ℕ, syracuseStep^[j] 1375 = 1 := reachStep (stepEq 1 (by rfl) ⟨1031, by rfl⟩ : syracuseStep 1375 = 2063) R2063
theorem R1505 : ∃ j : ℕ, syracuseStep^[j] 1505 = 1 := reachStep (stepEq 2 (by rfl) ⟨564, by rfl⟩ : syracuseStep 1505 = 1129) R1129
theorem R2445 : ∃ j : ℕ, syracuseStep^[j] 2445 = 1 := reachStep (stepEq 3 (by rfl) ⟨458, by rfl⟩ : syracuseStep 2445 = 917) R917
theorem R2453 : ∃ j : ℕ, syracuseStep^[j] 2453 = 1 := reachStep (stepEq 6 (by rfl) ⟨57, by rfl⟩ : syracuseStep 2453 = 115) R115
theorem R2481 : ∃ j : ℕ, syracuseStep^[j] 2481 = 1 := reachStep (stepEq 2 (by rfl) ⟨930, by rfl⟩ : syracuseStep 2481 = 1861) R1861
theorem R2483 : ∃ j : ℕ, syracuseStep^[j] 2483 = 1 := reachStep (stepEq 1 (by rfl) ⟨1862, by rfl⟩ : syracuseStep 2483 = 3725) R3725
theorem R2489 : ∃ j : ℕ, syracuseStep^[j] 2489 = 1 := reachStep (stepEq 2 (by rfl) ⟨933, by rfl⟩ : syracuseStep 2489 = 1867) R1867
theorem R2507 : ∃ j : ℕ, syracuseStep^[j] 2507 = 1 := reachStep (stepEq 1 (by rfl) ⟨1880, by rfl⟩ : syracuseStep 2507 = 3761) R3761
theorem R2515 : ∃ j : ℕ, syracuseStep^[j] 2515 = 1 := reachStep (stepEq 1 (by rfl) ⟨1886, by rfl⟩ : syracuseStep 2515 = 3773) R3773
theorem R2517 : ∃ j : ℕ, syracuseStep^[j] 2517 = 1 := reachStep (stepEq 7 (by rfl) ⟨29, by rfl⟩ : syracuseStep 2517 = 59) R59
theorem R2521 : ∃ j : ℕ, syracuseStep^[j] 2521 = 1 := reachStep (stepEq 2 (by rfl) ⟨945, by rfl⟩ : syracuseStep 2521 = 1891) R1891
theorem R2525 : ∃ j : ℕ, syracuseStep^[j] 2525 = 1 := reachStep (stepEq 3 (by rfl) ⟨473, by rfl⟩ : syracuseStep 2525 = 947) R947
theorem R2531 : ∃ j : ℕ, syracuseStep^[j] 2531 = 1 := reachStep (stepEq 1 (by rfl) ⟨1898, by rfl⟩ : syracuseStep 2531 = 3797) R3797
theorem R2545 : ∃ j : ℕ, syracuseStep^[j] 2545 = 1 := reachStep (stepEq 2 (by rfl) ⟨954, by rfl⟩ : syracuseStep 2545 = 1909) R1909
theorem R2589 : ∃ j : ℕ, syracuseStep^[j] 2589 = 1 := reachStep (stepEq 3 (by rfl) ⟨485, by rfl⟩ : syracuseStep 2589 = 971) R971
theorem R2593 : ∃ j : ℕ, syracuseStep^[j] 2593 = 1 := reachStep (stepEq 2 (by rfl) ⟨972, by rfl⟩ : syracuseStep 2593 = 1945) R1945
theorem R2633 : ∃ j : ℕ, syracuseStep^[j] 2633 = 1 := reachStep (stepEq 2 (by rfl) ⟨987, by rfl⟩ : syracuseStep 2633 = 1975) R1975
theorem R2705 : ∃ j : ℕ, syracuseStep^[j] 2705 = 1 := reachStep (stepEq 2 (by rfl) ⟨1014, by rfl⟩ : syracuseStep 2705 = 2029) R2029
theorem R2707 : ∃ j : ℕ, syracuseStep^[j] 2707 = 1 := reachStep (stepEq 1 (by rfl) ⟨2030, by rfl⟩ : syracuseStep 2707 = 4061) R4061
theorem R2733 : ∃ j : ℕ, syracuseStep^[j] 2733 = 1 := reachStep (stepEq 3 (by rfl) ⟨512, by rfl⟩ : syracuseStep 2733 = 1025) R1025
theorem R2737 : ∃ j : ℕ, syracuseStep^[j] 2737 = 1 := reachStep (stepEq 2 (by rfl) ⟨1026, by rfl⟩ : syracuseStep 2737 = 2053) R2053
theorem R2739 : ∃ j : ℕ, syracuseStep^[j] 2739 = 1 := reachStep (stepEq 1 (by rfl) ⟨2054, by rfl⟩ : syracuseStep 2739 = 4109) R4109
theorem R2745 : ∃ j : ℕ, syracuseStep^[j] 2745 = 1 := reachStep (stepEq 2 (by rfl) ⟨1029, by rfl⟩ : syracuseStep 2745 = 2059) R2059
theorem R2749 : ∃ j : ℕ, syracuseStep^[j] 2749 = 1 := reachStep (stepEq 3 (by rfl) ⟨515, by rfl⟩ : syracuseStep 2749 = 1031) R1031
theorem R2763 : ∃ j : ℕ, syracuseStep^[j] 2763 = 1 := reachStep (stepEq 1 (by rfl) ⟨2072, by rfl⟩ : syracuseStep 2763 = 4145) R4145
theorem R3001 : ∃ j : ℕ, syracuseStep^[j] 3001 = 1 := reachStep (stepEq 2 (by rfl) ⟨1125, by rfl⟩ : syracuseStep 3001 = 2251) R2251
theorem R3003 : ∃ j : ℕ, syracuseStep^[j] 3003 = 1 := reachStep (stepEq 1 (by rfl) ⟨2252, by rfl⟩ : syracuseStep 3003 = 4505) R4505
theorem R3009 : ∃ j : ℕ, syracuseStep^[j] 3009 = 1 := reachStep (stepEq 2 (by rfl) ⟨1128, by rfl⟩ : syracuseStep 3009 = 2257) R2257
theorem R3011 : ∃ j : ℕ, syracuseStep^[j] 3011 = 1 := reachStep (stepEq 1 (by rfl) ⟨2258, by rfl⟩ : syracuseStep 3011 = 4517) R4517
theorem R3017 : ∃ j : ℕ, syracuseStep^[j] 3017 = 1 := reachStep (stepEq 2 (by rfl) ⟨1131, by rfl⟩ : syracuseStep 3017 = 2263) R2263
theorem R4885 : ∃ j : ℕ, syracuseStep^[j] 4885 = 1 := reachStep (stepEq 6 (by rfl) ⟨114, by rfl⟩ : syracuseStep 4885 = 229) R229
theorem R4917 : ∃ j : ℕ, syracuseStep^[j] 4917 = 1 := reachStep (stepEq 5 (by rfl) ⟨230, by rfl⟩ : syracuseStep 4917 = 461) R461
theorem R4929 : ∃ j : ℕ, syracuseStep^[j] 4929 = 1 := reachStep (stepEq 2 (by rfl) ⟨1848, by rfl⟩ : syracuseStep 4929 = 3697) R3697
theorem R4953 : ∃ j : ℕ, syracuseStep^[j] 4953 = 1 := reachStep (stepEq 2 (by rfl) ⟨1857, by rfl⟩ : syracuseStep 4953 = 3715) R3715
theorem R4963 : ∃ j : ℕ, syracuseStep^[j] 4963 = 1 := reachStep (stepEq 1 (by rfl) ⟨3722, by rfl⟩ : syracuseStep 4963 = 7445) R7445
theorem R4965 : ∃ j : ℕ, syracuseStep^[j] 4965 = 1 := reachStep (stepEq 4 (by rfl) ⟨465, by rfl⟩ : syracuseStep 4965 = 931) R931
theorem R4979 : ∃ j : ℕ, syracuseStep^[j] 4979 = 1 := reachStep (stepEq 1 (by rfl) ⟨3734, by rfl⟩ : syracuseStep 4979 = 7469) R7469
theorem R5015 : ∃ j : ℕ, syracuseStep^[j] 5015 = 1 := reachStep (stepEq 1 (by rfl) ⟨3761, by rfl⟩ : syracuseStep 5015 = 7523) R7523
theorem R5017 : ∃ j : ℕ, syracuseStep^[j] 5017 = 1 := reachStep (stepEq 2 (by rfl) ⟨1881, by rfl⟩ : syracuseStep 5017 = 3763) R3763
theorem R5029 : ∃ j : ℕ, syracuseStep^[j] 5029 = 1 := reachStep (stepEq 4 (by rfl) ⟨471, by rfl⟩ : syracuseStep 5029 = 943) R943
theorem R5041 : ∃ j : ℕ, syracuseStep^[j] 5041 = 1 := reachStep (stepEq 2 (by rfl) ⟨1890, by rfl⟩ : syracuseStep 5041 = 3781) R3781
theorem R5043 : ∃ j : ℕ, syracuseStep^[j] 5043 = 1 := reachStep (stepEq 1 (by rfl) ⟨3782, by rfl⟩ : syracuseStep 5043 = 7565) R7565
theorem R5045 : ∃ j : ℕ, syracuseStep^[j] 5045 = 1 := reachStep (stepEq 5 (by rfl) ⟨236, by rfl⟩ : syracuseStep 5045 = 473) R473
theorem R5061 : ∃ j : ℕ, syracuseStep^[j] 5061 = 1 := reachStep (stepEq 4 (by rfl) ⟨474, by rfl⟩ : syracuseStep 5061 = 949) R949
theorem R5077 : ∃ j : ℕ, syracuseStep^[j] 5077 = 1 := reachStep (stepEq 7 (by rfl) ⟨59, by rfl⟩ : syracuseStep 5077 = 119) R119
theorem R5081 : ∃ j : ℕ, syracuseStep^[j] 5081 = 1 := reachStep (stepEq 2 (by rfl) ⟨1905, by rfl⟩ : syracuseStep 5081 = 3811) R3811
theorem R5091 : ∃ j : ℕ, syracuseStep^[j] 5091 = 1 := reachStep (stepEq 1 (by rfl) ⟨3818, by rfl⟩ : syracuseStep 5091 = 7637) R7637
theorem R5121 : ∃ j : ℕ, syracuseStep^[j] 5121 = 1 := reachStep (stepEq 2 (by rfl) ⟨1920, by rfl⟩ : syracuseStep 5121 = 3841) R3841
theorem R5181 : ∃ j : ℕ, syracuseStep^[j] 5181 = 1 := reachStep (stepEq 3 (by rfl) ⟨971, by rfl⟩ : syracuseStep 5181 = 1943) R1943
theorem R5185 : ∃ j : ℕ, syracuseStep^[j] 5185 = 1 := reachStep (stepEq 2 (by rfl) ⟨1944, by rfl⟩ : syracuseStep 5185 = 3889) R3889
theorem R5187 : ∃ j : ℕ, syracuseStep^[j] 5187 = 1 := reachStep (stepEq 1 (by rfl) ⟨3890, by rfl⟩ : syracuseStep 5187 = 7781) R7781
theorem R5209 : ∃ j : ℕ, syracuseStep^[j] 5209 = 1 := reachStep (stepEq 2 (by rfl) ⟨1953, by rfl⟩ : syracuseStep 5209 = 3907) R3907
theorem R5265 : ∃ j : ℕ, syracuseStep^[j] 5265 = 1 := reachStep (stepEq 2 (by rfl) ⟨1974, by rfl⟩ : syracuseStep 5265 = 3949) R3949
theorem R5267 : ∃ j : ℕ, syracuseStep^[j] 5267 = 1 := reachStep (stepEq 1 (by rfl) ⟨3950, by rfl⟩ : syracuseStep 5267 = 7901) R7901
theorem R5411 : ∃ j : ℕ, syracuseStep^[j] 5411 = 1 := reachStep (stepEq 1 (by rfl) ⟨4058, by rfl⟩ : syracuseStep 5411 = 8117) R8117
theorem R5413 : ∃ j : ℕ, syracuseStep^[j] 5413 = 1 := reachStep (stepEq 4 (by rfl) ⟨507, by rfl⟩ : syracuseStep 5413 = 1015) R1015
theorem R5415 : ∃ j : ℕ, syracuseStep^[j] 5415 = 1 := reachStep (stepEq 1 (by rfl) ⟨4061, by rfl⟩ : syracuseStep 5415 = 8123) R8123
theorem R5419 : ∃ j : ℕ, syracuseStep^[j] 5419 = 1 := reachStep (stepEq 1 (by rfl) ⟨4064, by rfl⟩ : syracuseStep 5419 = 8129) R8129
theorem R5469 : ∃ j : ℕ, syracuseStep^[j] 5469 = 1 := reachStep (stepEq 3 (by rfl) ⟨1025, by rfl⟩ : syracuseStep 5469 = 2051) R2051
theorem R5475 : ∃ j : ℕ, syracuseStep^[j] 5475 = 1 := reachStep (stepEq 1 (by rfl) ⟨4106, by rfl⟩ : syracuseStep 5475 = 8213) R8213
theorem R5477 : ∃ j : ℕ, syracuseStep^[j] 5477 = 1 := reachStep (stepEq 4 (by rfl) ⟨513, by rfl⟩ : syracuseStep 5477 = 1027) R1027
theorem R5481 : ∃ j : ℕ, syracuseStep^[j] 5481 = 1 := reachStep (stepEq 2 (by rfl) ⟨2055, by rfl⟩ : syracuseStep 5481 = 4111) R4111
theorem R5491 : ∃ j : ℕ, syracuseStep^[j] 5491 = 1 := reachStep (stepEq 1 (by rfl) ⟨4118, by rfl⟩ : syracuseStep 5491 = 8237) R8237
theorem R5501 : ∃ j : ℕ, syracuseStep^[j] 5501 = 1 := reachStep (stepEq 3 (by rfl) ⟨1031, by rfl⟩ : syracuseStep 5501 = 2063) R2063
theorem R5527 : ∃ j : ℕ, syracuseStep^[j] 5527 = 1 := reachStep (stepEq 1 (by rfl) ⟨4145, by rfl⟩ : syracuseStep 5527 = 8291) R8291
theorem R5529 : ∃ j : ℕ, syracuseStep^[j] 5529 = 1 := reachStep (stepEq 2 (by rfl) ⟨2073, by rfl⟩ : syracuseStep 5529 = 4147) R4147
theorem R5531 : ∃ j : ℕ, syracuseStep^[j] 5531 = 1 := reachStep (stepEq 1 (by rfl) ⟨4148, by rfl⟩ : syracuseStep 5531 = 8297) R8297
theorem R5577 : ∃ j : ℕ, syracuseStep^[j] 5577 = 1 := reachStep (stepEq 2 (by rfl) ⟨2091, by rfl⟩ : syracuseStep 5577 = 4183) R4183
theorem R5579 : ∃ j : ℕ, syracuseStep^[j] 5579 = 1 := reachStep (stepEq 1 (by rfl) ⟨4184, by rfl⟩ : syracuseStep 5579 = 8369) R8369
theorem R5641 : ∃ j : ℕ, syracuseStep^[j] 5641 = 1 := reachStep (stepEq 2 (by rfl) ⟨2115, by rfl⟩ : syracuseStep 5641 = 4231) R4231
theorem R6003 : ∃ j : ℕ, syracuseStep^[j] 6003 = 1 := reachStep (stepEq 1 (by rfl) ⟨4502, by rfl⟩ : syracuseStep 6003 = 9005) R9005
theorem R6007 : ∃ j : ℕ, syracuseStep^[j] 6007 = 1 := reachStep (stepEq 1 (by rfl) ⟨4505, by rfl⟩ : syracuseStep 6007 = 9011) R9011
theorem R6011 : ∃ j : ℕ, syracuseStep^[j] 6011 = 1 := reachStep (stepEq 1 (by rfl) ⟨4508, by rfl⟩ : syracuseStep 6011 = 9017) R9017
theorem R6019 : ∃ j : ℕ, syracuseStep^[j] 6019 = 1 := reachStep (stepEq 1 (by rfl) ⟨4514, by rfl⟩ : syracuseStep 6019 = 9029) R9029
theorem R6021 : ∃ j : ℕ, syracuseStep^[j] 6021 = 1 := reachStep (stepEq 4 (by rfl) ⟨564, by rfl⟩ : syracuseStep 6021 = 1129) R1129
theorem R6023 : ∃ j : ℕ, syracuseStep^[j] 6023 = 1 := reachStep (stepEq 1 (by rfl) ⟨4517, by rfl⟩ : syracuseStep 6023 = 9035) R9035
theorem R6033 : ∃ j : ℕ, syracuseStep^[j] 6033 = 1 := reachStep (stepEq 2 (by rfl) ⟨2262, by rfl⟩ : syracuseStep 6033 = 4525) R4525
theorem R6035 : ∃ j : ℕ, syracuseStep^[j] 6035 = 1 := reachStep (stepEq 1 (by rfl) ⟨4526, by rfl⟩ : syracuseStep 6035 = 9053) R9053
theorem R39365 : ∃ j : ℕ, syracuseStep^[j] 39365 = 1 := reachStep (stepEq 4 (by rfl) ⟨3690, by rfl⟩ : syracuseStep 39365 = 7381) R7381
theorem R9841 : ∃ j : ℕ, syracuseStep^[j] 9841 = 1 := reachStep (stepEq 2 (by rfl) ⟨3690, by rfl⟩ : syracuseStep 9841 = 7381) R7381
theorem R9905 : ∃ j : ℕ, syracuseStep^[j] 9905 = 1 := reachStep (stepEq 2 (by rfl) ⟨3714, by rfl⟩ : syracuseStep 9905 = 7429) R7429
theorem R9977 : ∃ j : ℕ, syracuseStep^[j] 9977 = 1 := reachStep (stepEq 2 (by rfl) ⟨3741, by rfl⟩ : syracuseStep 9977 = 7483) R7483
theorem R10043 : ∃ j : ℕ, syracuseStep^[j] 10043 = 1 := reachStep (stepEq 1 (by rfl) ⟨7532, by rfl⟩ : syracuseStep 10043 = 15065) R15065
theorem R10061 : ∃ j : ℕ, syracuseStep^[j] 10061 = 1 := reachStep (stepEq 3 (by rfl) ⟨1886, by rfl⟩ : syracuseStep 10061 = 3773) R3773
theorem R10085 : ∃ j : ℕ, syracuseStep^[j] 10085 = 1 := reachStep (stepEq 4 (by rfl) ⟨945, by rfl⟩ : syracuseStep 10085 = 1891) R1891
theorem R10097 : ∃ j : ℕ, syracuseStep^[j] 10097 = 1 := reachStep (stepEq 2 (by rfl) ⟨3786, by rfl⟩ : syracuseStep 10097 = 7573) R7573
theorem R10201 : ∃ j : ℕ, syracuseStep^[j] 10201 = 1 := reachStep (stepEq 2 (by rfl) ⟨3825, by rfl⟩ : syracuseStep 10201 = 7651) R7651
theorem R10529 : ∃ j : ℕ, syracuseStep^[j] 10529 = 1 := reachStep (stepEq 2 (by rfl) ⟨3948, by rfl⟩ : syracuseStep 10529 = 7897) R7897
theorem R10829 : ∃ j : ℕ, syracuseStep^[j] 10829 = 1 := reachStep (stepEq 3 (by rfl) ⟨2030, by rfl⟩ : syracuseStep 10829 = 4061) R4061
theorem R10957 : ∃ j : ℕ, syracuseStep^[j] 10957 = 1 := reachStep (stepEq 3 (by rfl) ⟨2054, by rfl⟩ : syracuseStep 10957 = 4109) R4109
theorem R10961 : ∃ j : ℕ, syracuseStep^[j] 10961 = 1 := reachStep (stepEq 2 (by rfl) ⟨4110, by rfl⟩ : syracuseStep 10961 = 8221) R8221
theorem R10997 : ∃ j : ℕ, syracuseStep^[j] 10997 = 1 := reachStep (stepEq 5 (by rfl) ⟨515, by rfl⟩ : syracuseStep 10997 = 1031) R1031
theorem R11063 : ∃ j : ℕ, syracuseStep^[j] 11063 = 1 := reachStep (stepEq 1 (by rfl) ⟨8297, by rfl⟩ : syracuseStep 11063 = 16595) R16595
theorem R11159 : ∃ j : ℕ, syracuseStep^[j] 11159 = 1 := reachStep (stepEq 1 (by rfl) ⟨8369, by rfl⟩ : syracuseStep 11159 = 16739) R16739
theorem R11353 : ∃ j : ℕ, syracuseStep^[j] 11353 = 1 := reachStep (stepEq 2 (by rfl) ⟨4257, by rfl⟩ : syracuseStep 11353 = 8515) R8515
theorem R44621 : ∃ j : ℕ, syracuseStep^[j] 44621 = 1 := reachStep (stepEq 3 (by rfl) ⟨8366, by rfl⟩ : syracuseStep 44621 = 16733) R16733
theorem R12005 : ∃ j : ℕ, syracuseStep^[j] 12005 = 1 := reachStep (stepEq 4 (by rfl) ⟨1125, by rfl⟩ : syracuseStep 12005 = 2251) R2251
theorem R12023 : ∃ j : ℕ, syracuseStep^[j] 12023 = 1 := reachStep (stepEq 1 (by rfl) ⟨9017, by rfl⟩ : syracuseStep 12023 = 18035) R18035
theorem R20087 : ∃ j : ℕ, syracuseStep^[j] 20087 = 1 := reachStep (stepEq 1 (by rfl) ⟨15065, by rfl⟩ : syracuseStep 20087 = 30131) R30131
theorem R20195 : ∃ j : ℕ, syracuseStep^[j] 20195 = 1 := reachStep (stepEq 1 (by rfl) ⟨15146, by rfl⟩ : syracuseStep 20195 = 30293) R30293
theorem R20837 : ∃ j : ℕ, syracuseStep^[j] 20837 = 1 := reachStep (stepEq 4 (by rfl) ⟨1953, by rfl⟩ : syracuseStep 20837 = 3907) R3907
theorem R21059 : ∃ j : ℕ, syracuseStep^[j] 21059 = 1 := reachStep (stepEq 1 (by rfl) ⟨15794, by rfl⟩ : syracuseStep 21059 = 31589) R31589
theorem R21061 : ∃ j : ℕ, syracuseStep^[j] 21061 = 1 := reachStep (stepEq 4 (by rfl) ⟨1974, by rfl⟩ : syracuseStep 21061 = 3949) R3949
theorem R21653 : ∃ j : ℕ, syracuseStep^[j] 21653 = 1 := reachStep (stepEq 6 (by rfl) ⟨507, by rfl⟩ : syracuseStep 21653 = 1015) R1015
theorem R21923 : ∃ j : ℕ, syracuseStep^[j] 21923 = 1 := reachStep (stepEq 1 (by rfl) ⟨16442, by rfl⟩ : syracuseStep 21923 = 32885) R32885
theorem R22139 : ∃ j : ℕ, syracuseStep^[j] 22139 = 1 := reachStep (stepEq 1 (by rfl) ⟨16604, by rfl⟩ : syracuseStep 22139 = 33209) R33209
theorem R22315 : ∃ j : ℕ, syracuseStep^[j] 22315 = 1 := reachStep (stepEq 1 (by rfl) ⟨16736, by rfl⟩ : syracuseStep 22315 = 33473) R33473
theorem R22571 : ∃ j : ℕ, syracuseStep^[j] 22571 = 1 := reachStep (stepEq 1 (by rfl) ⟨16928, by rfl⟩ : syracuseStep 22571 = 33857) R33857
theorem R105 : ∃ j : ℕ, syracuseStep^[j] 105 = 1 := reachStep (stepEq 2 (by rfl) ⟨39, by rfl⟩ : syracuseStep 105 = 79) R79
theorem R203 : ∃ j : ℕ, syracuseStep^[j] 203 = 1 := reachStep (stepEq 1 (by rfl) ⟨152, by rfl⟩ : syracuseStep 203 = 305) R305
theorem R209 : ∃ j : ℕ, syracuseStep^[j] 209 = 1 := reachStep (stepEq 2 (by rfl) ⟨78, by rfl⟩ : syracuseStep 209 = 157) R157
theorem R211 : ∃ j : ℕ, syracuseStep^[j] 211 = 1 := reachStep (stepEq 1 (by rfl) ⟨158, by rfl⟩ : syracuseStep 211 = 317) R317
theorem R407 : ∃ j : ℕ, syracuseStep^[j] 407 = 1 := reachStep (stepEq 1 (by rfl) ⟨305, by rfl⟩ : syracuseStep 407 = 611) R611
theorem R409 : ∃ j : ℕ, syracuseStep^[j] 409 = 1 := reachStep (stepEq 2 (by rfl) ⟨153, by rfl⟩ : syracuseStep 409 = 307) R307
theorem R419 : ∃ j : ℕ, syracuseStep^[j] 419 = 1 := reachStep (stepEq 1 (by rfl) ⟨314, by rfl⟩ : syracuseStep 419 = 629) R629
theorem R421 : ∃ j : ℕ, syracuseStep^[j] 421 = 1 := reachStep (stepEq 4 (by rfl) ⟨39, by rfl⟩ : syracuseStep 421 = 79) R79
theorem R431 : ∃ j : ℕ, syracuseStep^[j] 431 = 1 := reachStep (stepEq 1 (by rfl) ⟨323, by rfl⟩ : syracuseStep 431 = 647) R647
theorem R455 : ∃ j : ℕ, syracuseStep^[j] 455 = 1 := reachStep (stepEq 1 (by rfl) ⟨341, by rfl⟩ : syracuseStep 455 = 683) R683
theorem R813 : ∃ j : ℕ, syracuseStep^[j] 813 = 1 := reachStep (stepEq 3 (by rfl) ⟨152, by rfl⟩ : syracuseStep 813 = 305) R305
theorem R817 : ∃ j : ℕ, syracuseStep^[j] 817 = 1 := reachStep (stepEq 2 (by rfl) ⟨306, by rfl⟩ : syracuseStep 817 = 613) R613
theorem R819 : ∃ j : ℕ, syracuseStep^[j] 819 = 1 := reachStep (stepEq 1 (by rfl) ⟨614, by rfl⟩ : syracuseStep 819 = 1229) R1229
theorem R827 : ∃ j : ℕ, syracuseStep^[j] 827 = 1 := reachStep (stepEq 1 (by rfl) ⟨620, by rfl⟩ : syracuseStep 827 = 1241) R1241
theorem R837 : ∃ j : ℕ, syracuseStep^[j] 837 = 1 := reachStep (stepEq 4 (by rfl) ⟨78, by rfl⟩ : syracuseStep 837 = 157) R157
theorem R841 : ∃ j : ℕ, syracuseStep^[j] 841 = 1 := reachStep (stepEq 2 (by rfl) ⟨315, by rfl⟩ : syracuseStep 841 = 631) R631
theorem R843 : ∃ j : ℕ, syracuseStep^[j] 843 = 1 := reachStep (stepEq 1 (by rfl) ⟨632, by rfl⟩ : syracuseStep 843 = 1265) R1265
theorem R845 : ∃ j : ℕ, syracuseStep^[j] 845 = 1 := reachStep (stepEq 3 (by rfl) ⟨158, by rfl⟩ : syracuseStep 845 = 317) R317
theorem R863 : ∃ j : ℕ, syracuseStep^[j] 863 = 1 := reachStep (stepEq 1 (by rfl) ⟨647, by rfl⟩ : syracuseStep 863 = 1295) R1295
theorem R911 : ∃ j : ℕ, syracuseStep^[j] 911 = 1 := reachStep (stepEq 1 (by rfl) ⟨683, by rfl⟩ : syracuseStep 911 = 1367) R1367
theorem R1003 : ∃ j : ℕ, syracuseStep^[j] 1003 = 1 := reachStep (stepEq 1 (by rfl) ⟨752, by rfl⟩ : syracuseStep 1003 = 1505) R1505
theorem R1629 : ∃ j : ℕ, syracuseStep^[j] 1629 = 1 := reachStep (stepEq 3 (by rfl) ⟨305, by rfl⟩ : syracuseStep 1629 = 611) R611
theorem R1635 : ∃ j : ℕ, syracuseStep^[j] 1635 = 1 := reachStep (stepEq 1 (by rfl) ⟨1226, by rfl⟩ : syracuseStep 1635 = 2453) R2453
theorem R1637 : ∃ j : ℕ, syracuseStep^[j] 1637 = 1 := reachStep (stepEq 4 (by rfl) ⟨153, by rfl⟩ : syracuseStep 1637 = 307) R307
theorem R1655 : ∃ j : ℕ, syracuseStep^[j] 1655 = 1 := reachStep (stepEq 1 (by rfl) ⟨1241, by rfl⟩ : syracuseStep 1655 = 2483) R2483
theorem R1659 : ∃ j : ℕ, syracuseStep^[j] 1659 = 1 := reachStep (stepEq 1 (by rfl) ⟨1244, by rfl⟩ : syracuseStep 1659 = 2489) R2489
theorem R1671 : ∃ j : ℕ, syracuseStep^[j] 1671 = 1 := reachStep (stepEq 1 (by rfl) ⟨1253, by rfl⟩ : syracuseStep 1671 = 2507) R2507
theorem R1677 : ∃ j : ℕ, syracuseStep^[j] 1677 = 1 := reachStep (stepEq 3 (by rfl) ⟨314, by rfl⟩ : syracuseStep 1677 = 629) R629
theorem R1681 : ∃ j : ℕ, syracuseStep^[j] 1681 = 1 := reachStep (stepEq 2 (by rfl) ⟨630, by rfl⟩ : syracuseStep 1681 = 1261) R1261
theorem R1683 : ∃ j : ℕ, syracuseStep^[j] 1683 = 1 := reachStep (stepEq 1 (by rfl) ⟨1262, by rfl⟩ : syracuseStep 1683 = 2525) R2525
theorem R1685 : ∃ j : ℕ, syracuseStep^[j] 1685 = 1 := reachStep (stepEq 6 (by rfl) ⟨39, by rfl⟩ : syracuseStep 1685 = 79) R79
theorem R1687 : ∃ j : ℕ, syracuseStep^[j] 1687 = 1 := reachStep (stepEq 1 (by rfl) ⟨1265, by rfl⟩ : syracuseStep 1687 = 2531) R2531
theorem R1725 : ∃ j : ℕ, syracuseStep^[j] 1725 = 1 := reachStep (stepEq 3 (by rfl) ⟨323, by rfl⟩ : syracuseStep 1725 = 647) R647
theorem R1755 : ∃ j : ℕ, syracuseStep^[j] 1755 = 1 := reachStep (stepEq 1 (by rfl) ⟨1316, by rfl⟩ : syracuseStep 1755 = 2633) R2633
theorem R1803 : ∃ j : ℕ, syracuseStep^[j] 1803 = 1 := reachStep (stepEq 1 (by rfl) ⟨1352, by rfl⟩ : syracuseStep 1803 = 2705) R2705
theorem R1821 : ∃ j : ℕ, syracuseStep^[j] 1821 = 1 := reachStep (stepEq 3 (by rfl) ⟨341, by rfl⟩ : syracuseStep 1821 = 683) R683
theorem R1825 : ∃ j : ℕ, syracuseStep^[j] 1825 = 1 := reachStep (stepEq 2 (by rfl) ⟨684, by rfl⟩ : syracuseStep 1825 = 1369) R1369
theorem R1833 : ∃ j : ℕ, syracuseStep^[j] 1833 = 1 := reachStep (stepEq 2 (by rfl) ⟨687, by rfl⟩ : syracuseStep 1833 = 1375) R1375
theorem R2007 : ∃ j : ℕ, syracuseStep^[j] 2007 = 1 := reachStep (stepEq 1 (by rfl) ⟨1505, by rfl⟩ : syracuseStep 2007 = 3011) R3011
theorem R2011 : ∃ j : ℕ, syracuseStep^[j] 2011 = 1 := reachStep (stepEq 1 (by rfl) ⟨1508, by rfl⟩ : syracuseStep 2011 = 3017) R3017
theorem R3253 : ∃ j : ℕ, syracuseStep^[j] 3253 = 1 := reachStep (stepEq 5 (by rfl) ⟨152, by rfl⟩ : syracuseStep 3253 = 305) R305
theorem R3269 : ∃ j : ℕ, syracuseStep^[j] 3269 = 1 := reachStep (stepEq 4 (by rfl) ⟨306, by rfl⟩ : syracuseStep 3269 = 613) R613
theorem R3277 : ∃ j : ℕ, syracuseStep^[j] 3277 = 1 := reachStep (stepEq 3 (by rfl) ⟨614, by rfl⟩ : syracuseStep 3277 = 1229) R1229
theorem R3309 : ∃ j : ℕ, syracuseStep^[j] 3309 = 1 := reachStep (stepEq 3 (by rfl) ⟨620, by rfl⟩ : syracuseStep 3309 = 1241) R1241
theorem R3319 : ∃ j : ℕ, syracuseStep^[j] 3319 = 1 := reachStep (stepEq 1 (by rfl) ⟨2489, by rfl⟩ : syracuseStep 3319 = 4979) R4979
theorem R3343 : ∃ j : ℕ, syracuseStep^[j] 3343 = 1 := reachStep (stepEq 1 (by rfl) ⟨2507, by rfl⟩ : syracuseStep 3343 = 5015) R5015
theorem R3349 : ∃ j : ℕ, syracuseStep^[j] 3349 = 1 := reachStep (stepEq 6 (by rfl) ⟨78, by rfl⟩ : syracuseStep 3349 = 157) R157
theorem R3353 : ∃ j : ℕ, syracuseStep^[j] 3353 = 1 := reachStep (stepEq 2 (by rfl) ⟨1257, by rfl⟩ : syracuseStep 3353 = 2515) R2515
theorem R3361 : ∃ j : ℕ, syracuseStep^[j] 3361 = 1 := reachStep (stepEq 2 (by rfl) ⟨1260, by rfl⟩ : syracuseStep 3361 = 2521) R2521
theorem R3363 : ∃ j : ℕ, syracuseStep^[j] 3363 = 1 := reachStep (stepEq 1 (by rfl) ⟨2522, by rfl⟩ : syracuseStep 3363 = 5045) R5045
theorem R3365 : ∃ j : ℕ, syracuseStep^[j] 3365 = 1 := reachStep (stepEq 4 (by rfl) ⟨315, by rfl⟩ : syracuseStep 3365 = 631) R631
theorem R3373 : ∃ j : ℕ, syracuseStep^[j] 3373 = 1 := reachStep (stepEq 3 (by rfl) ⟨632, by rfl⟩ : syracuseStep 3373 = 1265) R1265
theorem R3381 : ∃ j : ℕ, syracuseStep^[j] 3381 = 1 := reachStep (stepEq 5 (by rfl) ⟨158, by rfl⟩ : syracuseStep 3381 = 317) R317
theorem R3387 : ∃ j : ℕ, syracuseStep^[j] 3387 = 1 := reachStep (stepEq 1 (by rfl) ⟨2540, by rfl⟩ : syracuseStep 3387 = 5081) R5081
theorem R3393 : ∃ j : ℕ, syracuseStep^[j] 3393 = 1 := reachStep (stepEq 2 (by rfl) ⟨1272, by rfl⟩ : syracuseStep 3393 = 2545) R2545
theorem R3453 : ∃ j : ℕ, syracuseStep^[j] 3453 = 1 := reachStep (stepEq 3 (by rfl) ⟨647, by rfl⟩ : syracuseStep 3453 = 1295) R1295
theorem R3457 : ∃ j : ℕ, syracuseStep^[j] 3457 = 1 := reachStep (stepEq 2 (by rfl) ⟨1296, by rfl⟩ : syracuseStep 3457 = 2593) R2593
theorem R3511 : ∃ j : ℕ, syracuseStep^[j] 3511 = 1 := reachStep (stepEq 1 (by rfl) ⟨2633, by rfl⟩ : syracuseStep 3511 = 5267) R5267
theorem R3607 : ∃ j : ℕ, syracuseStep^[j] 3607 = 1 := reachStep (stepEq 1 (by rfl) ⟨2705, by rfl⟩ : syracuseStep 3607 = 5411) R5411
theorem R3609 : ∃ j : ℕ, syracuseStep^[j] 3609 = 1 := reachStep (stepEq 2 (by rfl) ⟨1353, by rfl⟩ : syracuseStep 3609 = 2707) R2707
theorem R3645 : ∃ j : ℕ, syracuseStep^[j] 3645 = 1 := reachStep (stepEq 3 (by rfl) ⟨683, by rfl⟩ : syracuseStep 3645 = 1367) R1367
theorem R3649 : ∃ j : ℕ, syracuseStep^[j] 3649 = 1 := reachStep (stepEq 2 (by rfl) ⟨1368, by rfl⟩ : syracuseStep 3649 = 2737) R2737
theorem R3651 : ∃ j : ℕ, syracuseStep^[j] 3651 = 1 := reachStep (stepEq 1 (by rfl) ⟨2738, by rfl⟩ : syracuseStep 3651 = 5477) R5477
theorem R3665 : ∃ j : ℕ, syracuseStep^[j] 3665 = 1 := reachStep (stepEq 2 (by rfl) ⟨1374, by rfl⟩ : syracuseStep 3665 = 2749) R2749
theorem R3667 : ∃ j : ℕ, syracuseStep^[j] 3667 = 1 := reachStep (stepEq 1 (by rfl) ⟨2750, by rfl⟩ : syracuseStep 3667 = 5501) R5501
theorem R3687 : ∃ j : ℕ, syracuseStep^[j] 3687 = 1 := reachStep (stepEq 1 (by rfl) ⟨2765, by rfl⟩ : syracuseStep 3687 = 5531) R5531
theorem R3719 : ∃ j : ℕ, syracuseStep^[j] 3719 = 1 := reachStep (stepEq 1 (by rfl) ⟨2789, by rfl⟩ : syracuseStep 3719 = 5579) R5579
theorem R4001 : ∃ j : ℕ, syracuseStep^[j] 4001 = 1 := reachStep (stepEq 2 (by rfl) ⟨1500, by rfl⟩ : syracuseStep 4001 = 3001) R3001
theorem R4007 : ∃ j : ℕ, syracuseStep^[j] 4007 = 1 := reachStep (stepEq 1 (by rfl) ⟨3005, by rfl⟩ : syracuseStep 4007 = 6011) R6011
theorem R4013 : ∃ j : ℕ, syracuseStep^[j] 4013 = 1 := reachStep (stepEq 3 (by rfl) ⟨752, by rfl⟩ : syracuseStep 4013 = 1505) R1505
theorem R4015 : ∃ j : ℕ, syracuseStep^[j] 4015 = 1 := reachStep (stepEq 1 (by rfl) ⟨3011, by rfl⟩ : syracuseStep 4015 = 6023) R6023
theorem R4023 : ∃ j : ℕ, syracuseStep^[j] 4023 = 1 := reachStep (stepEq 1 (by rfl) ⟨3017, by rfl⟩ : syracuseStep 4023 = 6035) R6035
theorem R6513 : ∃ j : ℕ, syracuseStep^[j] 6513 = 1 := reachStep (stepEq 2 (by rfl) ⟨2442, by rfl⟩ : syracuseStep 6513 = 4885) R4885
theorem R6517 : ∃ j : ℕ, syracuseStep^[j] 6517 = 1 := reachStep (stepEq 5 (by rfl) ⟨305, by rfl⟩ : syracuseStep 6517 = 611) R611
theorem R6541 : ∃ j : ℕ, syracuseStep^[j] 6541 = 1 := reachStep (stepEq 3 (by rfl) ⟨1226, by rfl⟩ : syracuseStep 6541 = 2453) R2453
theorem R6549 : ∃ j : ℕ, syracuseStep^[j] 6549 = 1 := reachStep (stepEq 6 (by rfl) ⟨153, by rfl⟩ : syracuseStep 6549 = 307) R307
theorem R6603 : ∃ j : ℕ, syracuseStep^[j] 6603 = 1 := reachStep (stepEq 1 (by rfl) ⟨4952, by rfl⟩ : syracuseStep 6603 = 9905) R9905
theorem R6617 : ∃ j : ℕ, syracuseStep^[j] 6617 = 1 := reachStep (stepEq 2 (by rfl) ⟨2481, by rfl⟩ : syracuseStep 6617 = 4963) R4963
theorem R6621 : ∃ j : ℕ, syracuseStep^[j] 6621 = 1 := reachStep (stepEq 3 (by rfl) ⟨1241, by rfl⟩ : syracuseStep 6621 = 2483) R2483
theorem R6637 : ∃ j : ℕ, syracuseStep^[j] 6637 = 1 := reachStep (stepEq 3 (by rfl) ⟨1244, by rfl⟩ : syracuseStep 6637 = 2489) R2489
theorem R6651 : ∃ j : ℕ, syracuseStep^[j] 6651 = 1 := reachStep (stepEq 1 (by rfl) ⟨4988, by rfl⟩ : syracuseStep 6651 = 9977) R9977
theorem R6685 : ∃ j : ℕ, syracuseStep^[j] 6685 = 1 := reachStep (stepEq 3 (by rfl) ⟨1253, by rfl⟩ : syracuseStep 6685 = 2507) R2507
theorem R6689 : ∃ j : ℕ, syracuseStep^[j] 6689 = 1 := reachStep (stepEq 2 (by rfl) ⟨2508, by rfl⟩ : syracuseStep 6689 = 5017) R5017
theorem R6695 : ∃ j : ℕ, syracuseStep^[j] 6695 = 1 := reachStep (stepEq 1 (by rfl) ⟨5021, by rfl⟩ : syracuseStep 6695 = 10043) R10043
theorem R6705 : ∃ j : ℕ, syracuseStep^[j] 6705 = 1 := reachStep (stepEq 2 (by rfl) ⟨2514, by rfl⟩ : syracuseStep 6705 = 5029) R5029
theorem R6707 : ∃ j : ℕ, syracuseStep^[j] 6707 = 1 := reachStep (stepEq 1 (by rfl) ⟨5030, by rfl⟩ : syracuseStep 6707 = 10061) R10061
theorem R6709 : ∃ j : ℕ, syracuseStep^[j] 6709 = 1 := reachStep (stepEq 5 (by rfl) ⟨314, by rfl⟩ : syracuseStep 6709 = 629) R629
theorem R6721 : ∃ j : ℕ, syracuseStep^[j] 6721 = 1 := reachStep (stepEq 2 (by rfl) ⟨2520, by rfl⟩ : syracuseStep 6721 = 5041) R5041
theorem R6723 : ∃ j : ℕ, syracuseStep^[j] 6723 = 1 := reachStep (stepEq 1 (by rfl) ⟨5042, by rfl⟩ : syracuseStep 6723 = 10085) R10085
theorem R6725 : ∃ j : ℕ, syracuseStep^[j] 6725 = 1 := reachStep (stepEq 4 (by rfl) ⟨630, by rfl⟩ : syracuseStep 6725 = 1261) R1261
theorem R6731 : ∃ j : ℕ, syracuseStep^[j] 6731 = 1 := reachStep (stepEq 1 (by rfl) ⟨5048, by rfl⟩ : syracuseStep 6731 = 10097) R10097
theorem R6733 : ∃ j : ℕ, syracuseStep^[j] 6733 = 1 := reachStep (stepEq 3 (by rfl) ⟨1262, by rfl⟩ : syracuseStep 6733 = 2525) R2525
theorem R6749 : ∃ j : ℕ, syracuseStep^[j] 6749 = 1 := reachStep (stepEq 3 (by rfl) ⟨1265, by rfl⟩ : syracuseStep 6749 = 2531) R2531
theorem R7019 : ∃ j : ℕ, syracuseStep^[j] 7019 = 1 := reachStep (stepEq 1 (by rfl) ⟨5264, by rfl⟩ : syracuseStep 7019 = 10529) R10529
theorem R7213 : ∃ j : ℕ, syracuseStep^[j] 7213 = 1 := reachStep (stepEq 3 (by rfl) ⟨1352, by rfl⟩ : syracuseStep 7213 = 2705) R2705
theorem R7217 : ∃ j : ℕ, syracuseStep^[j] 7217 = 1 := reachStep (stepEq 2 (by rfl) ⟨2706, by rfl⟩ : syracuseStep 7217 = 5413) R5413
theorem R7219 : ∃ j : ℕ, syracuseStep^[j] 7219 = 1 := reachStep (stepEq 1 (by rfl) ⟨5414, by rfl⟩ : syracuseStep 7219 = 10829) R10829
theorem R7285 : ∃ j : ℕ, syracuseStep^[j] 7285 = 1 := reachStep (stepEq 5 (by rfl) ⟨341, by rfl⟩ : syracuseStep 7285 = 683) R683
theorem R7301 : ∃ j : ℕ, syracuseStep^[j] 7301 = 1 := reachStep (stepEq 4 (by rfl) ⟨684, by rfl⟩ : syracuseStep 7301 = 1369) R1369
theorem R7307 : ∃ j : ℕ, syracuseStep^[j] 7307 = 1 := reachStep (stepEq 1 (by rfl) ⟨5480, by rfl⟩ : syracuseStep 7307 = 10961) R10961
theorem R7321 : ∃ j : ℕ, syracuseStep^[j] 7321 = 1 := reachStep (stepEq 2 (by rfl) ⟨2745, by rfl⟩ : syracuseStep 7321 = 5491) R5491
theorem R7331 : ∃ j : ℕ, syracuseStep^[j] 7331 = 1 := reachStep (stepEq 1 (by rfl) ⟨5498, by rfl⟩ : syracuseStep 7331 = 10997) R10997
theorem R7375 : ∃ j : ℕ, syracuseStep^[j] 7375 = 1 := reachStep (stepEq 1 (by rfl) ⟨5531, by rfl⟩ : syracuseStep 7375 = 11063) R11063
theorem R7439 : ∃ j : ℕ, syracuseStep^[j] 7439 = 1 := reachStep (stepEq 1 (by rfl) ⟨5579, by rfl⟩ : syracuseStep 7439 = 11159) R11159
theorem R8003 : ∃ j : ℕ, syracuseStep^[j] 8003 = 1 := reachStep (stepEq 1 (by rfl) ⟨6002, by rfl⟩ : syracuseStep 8003 = 12005) R12005
theorem R8009 : ∃ j : ℕ, syracuseStep^[j] 8009 = 1 := reachStep (stepEq 2 (by rfl) ⟨3003, by rfl⟩ : syracuseStep 8009 = 6007) R6007
theorem R8015 : ∃ j : ℕ, syracuseStep^[j] 8015 = 1 := reachStep (stepEq 1 (by rfl) ⟨6011, by rfl⟩ : syracuseStep 8015 = 12023) R12023
theorem R8029 : ∃ j : ℕ, syracuseStep^[j] 8029 = 1 := reachStep (stepEq 3 (by rfl) ⟨1505, by rfl⟩ : syracuseStep 8029 = 3011) R3011
theorem R8045 : ∃ j : ℕ, syracuseStep^[j] 8045 = 1 := reachStep (stepEq 3 (by rfl) ⟨1508, by rfl⟩ : syracuseStep 8045 = 3017) R3017
theorem R13013 : ∃ j : ℕ, syracuseStep^[j] 13013 = 1 := reachStep (stepEq 7 (by rfl) ⟨152, by rfl⟩ : syracuseStep 13013 = 305) R305
theorem R13121 : ∃ j : ℕ, syracuseStep^[j] 13121 = 1 := reachStep (stepEq 2 (by rfl) ⟨4920, by rfl⟩ : syracuseStep 13121 = 9841) R9841
theorem R13277 : ∃ j : ℕ, syracuseStep^[j] 13277 = 1 := reachStep (stepEq 3 (by rfl) ⟨2489, by rfl⟩ : syracuseStep 13277 = 4979) R4979
theorem R13373 : ∃ j : ℕ, syracuseStep^[j] 13373 = 1 := reachStep (stepEq 3 (by rfl) ⟨2507, by rfl⟩ : syracuseStep 13373 = 5015) R5015
theorem R13391 : ∃ j : ℕ, syracuseStep^[j] 13391 = 1 := reachStep (stepEq 1 (by rfl) ⟨10043, by rfl⟩ : syracuseStep 13391 = 20087) R20087
theorem R13445 : ∃ j : ℕ, syracuseStep^[j] 13445 = 1 := reachStep (stepEq 4 (by rfl) ⟨1260, by rfl⟩ : syracuseStep 13445 = 2521) R2521
theorem R13463 : ∃ j : ℕ, syracuseStep^[j] 13463 = 1 := reachStep (stepEq 1 (by rfl) ⟨10097, by rfl⟩ : syracuseStep 13463 = 20195) R20195
theorem R13601 : ∃ j : ℕ, syracuseStep^[j] 13601 = 1 := reachStep (stepEq 2 (by rfl) ⟨5100, by rfl⟩ : syracuseStep 13601 = 10201) R10201
theorem R13891 : ∃ j : ℕ, syracuseStep^[j] 13891 = 1 := reachStep (stepEq 1 (by rfl) ⟨10418, by rfl⟩ : syracuseStep 13891 = 20837) R20837
theorem R14039 : ∃ j : ℕ, syracuseStep^[j] 14039 = 1 := reachStep (stepEq 1 (by rfl) ⟨10529, by rfl⟩ : syracuseStep 14039 = 21059) R21059
theorem R14435 : ∃ j : ℕ, syracuseStep^[j] 14435 = 1 := reachStep (stepEq 1 (by rfl) ⟨10826, by rfl⟩ : syracuseStep 14435 = 21653) R21653
theorem R14597 : ∃ j : ℕ, syracuseStep^[j] 14597 = 1 := reachStep (stepEq 4 (by rfl) ⟨1368, by rfl⟩ : syracuseStep 14597 = 2737) R2737
theorem R14609 : ∃ j : ℕ, syracuseStep^[j] 14609 = 1 := reachStep (stepEq 2 (by rfl) ⟨5478, by rfl⟩ : syracuseStep 14609 = 10957) R10957
theorem R14615 : ∃ j : ℕ, syracuseStep^[j] 14615 = 1 := reachStep (stepEq 1 (by rfl) ⟨10961, by rfl⟩ : syracuseStep 14615 = 21923) R21923
theorem R14669 : ∃ j : ℕ, syracuseStep^[j] 14669 = 1 := reachStep (stepEq 3 (by rfl) ⟨2750, by rfl⟩ : syracuseStep 14669 = 5501) R5501
theorem R14759 : ∃ j : ℕ, syracuseStep^[j] 14759 = 1 := reachStep (stepEq 1 (by rfl) ⟨11069, by rfl⟩ : syracuseStep 14759 = 22139) R22139
theorem R15047 : ∃ j : ℕ, syracuseStep^[j] 15047 = 1 := reachStep (stepEq 1 (by rfl) ⟨11285, by rfl⟩ : syracuseStep 15047 = 22571) R22571
theorem R15137 : ∃ j : ℕ, syracuseStep^[j] 15137 = 1 := reachStep (stepEq 2 (by rfl) ⟨5676, by rfl⟩ : syracuseStep 15137 = 11353) R11353
theorem R55565 : ∃ j : ℕ, syracuseStep^[j] 55565 = 1 := reachStep (stepEq 3 (by rfl) ⟨10418, by rfl⟩ : syracuseStep 55565 = 20837) R20837
theorem R26243 : ∃ j : ℕ, syracuseStep^[j] 26243 = 1 := reachStep (stepEq 1 (by rfl) ⟨19682, by rfl⟩ : syracuseStep 26243 = 39365) R39365
theorem R26837 : ∃ j : ℕ, syracuseStep^[j] 26837 = 1 := reachStep (stepEq 7 (by rfl) ⟨314, by rfl⟩ : syracuseStep 26837 = 629) R629
theorem R28081 : ∃ j : ℕ, syracuseStep^[j] 28081 = 1 := reachStep (stepEq 2 (by rfl) ⟨10530, by rfl⟩ : syracuseStep 28081 = 21061) R21061
theorem R29747 : ∃ j : ℕ, syracuseStep^[j] 29747 = 1 := reachStep (stepEq 1 (by rfl) ⟨22310, by rfl⟩ : syracuseStep 29747 = 44621) R44621
theorem R29753 : ∃ j : ℕ, syracuseStep^[j] 29753 = 1 := reachStep (stepEq 2 (by rfl) ⟨11157, by rfl⟩ : syracuseStep 29753 = 22315) R22315
theorem R135 : ∃ j : ℕ, syracuseStep^[j] 135 = 1 := reachStep (stepEq 1 (by rfl) ⟨101, by rfl⟩ : syracuseStep 135 = 203) R203
theorem R139 : ∃ j : ℕ, syracuseStep^[j] 139 = 1 := reachStep (stepEq 1 (by rfl) ⟨104, by rfl⟩ : syracuseStep 139 = 209) R209
theorem R271 : ∃ j : ℕ, syracuseStep^[j] 271 = 1 := reachStep (stepEq 1 (by rfl) ⟨203, by rfl⟩ : syracuseStep 271 = 407) R407
theorem R279 : ∃ j : ℕ, syracuseStep^[j] 279 = 1 := reachStep (stepEq 1 (by rfl) ⟨209, by rfl⟩ : syracuseStep 279 = 419) R419
theorem R281 : ∃ j : ℕ, syracuseStep^[j] 281 = 1 := reachStep (stepEq 2 (by rfl) ⟨105, by rfl⟩ : syracuseStep 281 = 211) R211
theorem R287 : ∃ j : ℕ, syracuseStep^[j] 287 = 1 := reachStep (stepEq 1 (by rfl) ⟨215, by rfl⟩ : syracuseStep 287 = 431) R431
theorem R303 : ∃ j : ℕ, syracuseStep^[j] 303 = 1 := reachStep (stepEq 1 (by rfl) ⟨227, by rfl⟩ : syracuseStep 303 = 455) R455
theorem R541 : ∃ j : ℕ, syracuseStep^[j] 541 = 1 := reachStep (stepEq 3 (by rfl) ⟨101, by rfl⟩ : syracuseStep 541 = 203) R203
theorem R545 : ∃ j : ℕ, syracuseStep^[j] 545 = 1 := reachStep (stepEq 2 (by rfl) ⟨204, by rfl⟩ : syracuseStep 545 = 409) R409
theorem R551 : ∃ j : ℕ, syracuseStep^[j] 551 = 1 := reachStep (stepEq 1 (by rfl) ⟨413, by rfl⟩ : syracuseStep 551 = 827) R827
theorem R557 : ∃ j : ℕ, syracuseStep^[j] 557 = 1 := reachStep (stepEq 3 (by rfl) ⟨104, by rfl⟩ : syracuseStep 557 = 209) R209
theorem R561 : ∃ j : ℕ, syracuseStep^[j] 561 = 1 := reachStep (stepEq 2 (by rfl) ⟨210, by rfl⟩ : syracuseStep 561 = 421) R421
theorem R563 : ∃ j : ℕ, syracuseStep^[j] 563 = 1 := reachStep (stepEq 1 (by rfl) ⟨422, by rfl⟩ : syracuseStep 563 = 845) R845
theorem R575 : ∃ j : ℕ, syracuseStep^[j] 575 = 1 := reachStep (stepEq 1 (by rfl) ⟨431, by rfl⟩ : syracuseStep 575 = 863) R863
theorem R607 : ∃ j : ℕ, syracuseStep^[j] 607 = 1 := reachStep (stepEq 1 (by rfl) ⟨455, by rfl⟩ : syracuseStep 607 = 911) R911
theorem R1085 : ∃ j : ℕ, syracuseStep^[j] 1085 = 1 := reachStep (stepEq 3 (by rfl) ⟨203, by rfl⟩ : syracuseStep 1085 = 407) R407
theorem R1089 : ∃ j : ℕ, syracuseStep^[j] 1089 = 1 := reachStep (stepEq 2 (by rfl) ⟨408, by rfl⟩ : syracuseStep 1089 = 817) R817
theorem R1091 : ∃ j : ℕ, syracuseStep^[j] 1091 = 1 := reachStep (stepEq 1 (by rfl) ⟨818, by rfl⟩ : syracuseStep 1091 = 1637) R1637
theorem R1103 : ∃ j : ℕ, syracuseStep^[j] 1103 = 1 := reachStep (stepEq 1 (by rfl) ⟨827, by rfl⟩ : syracuseStep 1103 = 1655) R1655
theorem R1117 : ∃ j : ℕ, syracuseStep^[j] 1117 = 1 := reachStep (stepEq 3 (by rfl) ⟨209, by rfl⟩ : syracuseStep 1117 = 419) R419
theorem R1121 : ∃ j : ℕ, syracuseStep^[j] 1121 = 1 := reachStep (stepEq 2 (by rfl) ⟨420, by rfl⟩ : syracuseStep 1121 = 841) R841
theorem R1123 : ∃ j : ℕ, syracuseStep^[j] 1123 = 1 := reachStep (stepEq 1 (by rfl) ⟨842, by rfl⟩ : syracuseStep 1123 = 1685) R1685
theorem R1125 : ∃ j : ℕ, syracuseStep^[j] 1125 = 1 := reachStep (stepEq 4 (by rfl) ⟨105, by rfl⟩ : syracuseStep 1125 = 211) R211
theorem R1149 : ∃ j : ℕ, syracuseStep^[j] 1149 = 1 := reachStep (stepEq 3 (by rfl) ⟨215, by rfl⟩ : syracuseStep 1149 = 431) R431
theorem R1213 : ∃ j : ℕ, syracuseStep^[j] 1213 = 1 := reachStep (stepEq 3 (by rfl) ⟨227, by rfl⟩ : syracuseStep 1213 = 455) R455
theorem R1337 : ∃ j : ℕ, syracuseStep^[j] 1337 = 1 := reachStep (stepEq 2 (by rfl) ⟨501, by rfl⟩ : syracuseStep 1337 = 1003) R1003
theorem R34901 : ∃ j : ℕ, syracuseStep^[j] 34901 = 1 := reachStep (stepEq 8 (by rfl) ⟨204, by rfl⟩ : syracuseStep 34901 = 409) R409
theorem R2165 : ∃ j : ℕ, syracuseStep^[j] 2165 = 1 := reachStep (stepEq 5 (by rfl) ⟨101, by rfl⟩ : syracuseStep 2165 = 203) R203
theorem R2179 : ∃ j : ℕ, syracuseStep^[j] 2179 = 1 := reachStep (stepEq 1 (by rfl) ⟨1634, by rfl⟩ : syracuseStep 2179 = 3269) R3269
theorem R2181 : ∃ j : ℕ, syracuseStep^[j] 2181 = 1 := reachStep (stepEq 4 (by rfl) ⟨204, by rfl⟩ : syracuseStep 2181 = 409) R409
theorem R2205 : ∃ j : ℕ, syracuseStep^[j] 2205 = 1 := reachStep (stepEq 3 (by rfl) ⟨413, by rfl⟩ : syracuseStep 2205 = 827) R827
theorem R2229 : ∃ j : ℕ, syracuseStep^[j] 2229 = 1 := reachStep (stepEq 5 (by rfl) ⟨104, by rfl⟩ : syracuseStep 2229 = 209) R209
theorem R2235 : ∃ j : ℕ, syracuseStep^[j] 2235 = 1 := reachStep (stepEq 1 (by rfl) ⟨1676, by rfl⟩ : syracuseStep 2235 = 3353) R3353
theorem R2241 : ∃ j : ℕ, syracuseStep^[j] 2241 = 1 := reachStep (stepEq 2 (by rfl) ⟨840, by rfl⟩ : syracuseStep 2241 = 1681) R1681
theorem R2243 : ∃ j : ℕ, syracuseStep^[j] 2243 = 1 := reachStep (stepEq 1 (by rfl) ⟨1682, by rfl⟩ : syracuseStep 2243 = 3365) R3365
theorem R2245 : ∃ j : ℕ, syracuseStep^[j] 2245 = 1 := reachStep (stepEq 4 (by rfl) ⟨210, by rfl⟩ : syracuseStep 2245 = 421) R421
theorem R2249 : ∃ j : ℕ, syracuseStep^[j] 2249 = 1 := reachStep (stepEq 2 (by rfl) ⟨843, by rfl⟩ : syracuseStep 2249 = 1687) R1687
theorem R2253 : ∃ j : ℕ, syracuseStep^[j] 2253 = 1 := reachStep (stepEq 3 (by rfl) ⟨422, by rfl⟩ : syracuseStep 2253 = 845) R845
theorem R2301 : ∃ j : ℕ, syracuseStep^[j] 2301 = 1 := reachStep (stepEq 3 (by rfl) ⟨431, by rfl⟩ : syracuseStep 2301 = 863) R863
theorem R2429 : ∃ j : ℕ, syracuseStep^[j] 2429 = 1 := reachStep (stepEq 3 (by rfl) ⟨455, by rfl⟩ : syracuseStep 2429 = 911) R911
theorem R2433 : ∃ j : ℕ, syracuseStep^[j] 2433 = 1 := reachStep (stepEq 2 (by rfl) ⟨912, by rfl⟩ : syracuseStep 2433 = 1825) R1825
theorem R2443 : ∃ j : ℕ, syracuseStep^[j] 2443 = 1 := reachStep (stepEq 1 (by rfl) ⟨1832, by rfl⟩ : syracuseStep 2443 = 3665) R3665
theorem R2479 : ∃ j : ℕ, syracuseStep^[j] 2479 = 1 := reachStep (stepEq 1 (by rfl) ⟨1859, by rfl⟩ : syracuseStep 2479 = 3719) R3719
theorem R2667 : ∃ j : ℕ, syracuseStep^[j] 2667 = 1 := reachStep (stepEq 1 (by rfl) ⟨2000, by rfl⟩ : syracuseStep 2667 = 4001) R4001
theorem R2671 : ∃ j : ℕ, syracuseStep^[j] 2671 = 1 := reachStep (stepEq 1 (by rfl) ⟨2003, by rfl⟩ : syracuseStep 2671 = 4007) R4007
theorem R2675 : ∃ j : ℕ, syracuseStep^[j] 2675 = 1 := reachStep (stepEq 1 (by rfl) ⟨2006, by rfl⟩ : syracuseStep 2675 = 4013) R4013
theorem R2681 : ∃ j : ℕ, syracuseStep^[j] 2681 = 1 := reachStep (stepEq 2 (by rfl) ⟨1005, by rfl⟩ : syracuseStep 2681 = 2011) R2011
theorem R37043 : ∃ j : ℕ, syracuseStep^[j] 37043 = 1 := reachStep (stepEq 1 (by rfl) ⟨27782, by rfl⟩ : syracuseStep 37043 = 55565) R55565
theorem R4337 : ∃ j : ℕ, syracuseStep^[j] 4337 = 1 := reachStep (stepEq 2 (by rfl) ⟨1626, by rfl⟩ : syracuseStep 4337 = 3253) R3253
theorem R4341 : ∃ j : ℕ, syracuseStep^[j] 4341 = 1 := reachStep (stepEq 5 (by rfl) ⟨203, by rfl⟩ : syracuseStep 4341 = 407) R407
theorem R4357 : ∃ j : ℕ, syracuseStep^[j] 4357 = 1 := reachStep (stepEq 4 (by rfl) ⟨408, by rfl⟩ : syracuseStep 4357 = 817) R817
theorem R4365 : ∃ j : ℕ, syracuseStep^[j] 4365 = 1 := reachStep (stepEq 3 (by rfl) ⟨818, by rfl⟩ : syracuseStep 4365 = 1637) R1637
theorem R4369 : ∃ j : ℕ, syracuseStep^[j] 4369 = 1 := reachStep (stepEq 2 (by rfl) ⟨1638, by rfl⟩ : syracuseStep 4369 = 3277) R3277
theorem R4411 : ∃ j : ℕ, syracuseStep^[j] 4411 = 1 := reachStep (stepEq 1 (by rfl) ⟨3308, by rfl⟩ : syracuseStep 4411 = 6617) R6617
theorem R4413 : ∃ j : ℕ, syracuseStep^[j] 4413 = 1 := reachStep (stepEq 3 (by rfl) ⟨827, by rfl⟩ : syracuseStep 4413 = 1655) R1655
theorem R4425 : ∃ j : ℕ, syracuseStep^[j] 4425 = 1 := reachStep (stepEq 2 (by rfl) ⟨1659, by rfl⟩ : syracuseStep 4425 = 3319) R3319
theorem R4457 : ∃ j : ℕ, syracuseStep^[j] 4457 = 1 := reachStep (stepEq 2 (by rfl) ⟨1671, by rfl⟩ : syracuseStep 4457 = 3343) R3343
theorem R4459 : ∃ j : ℕ, syracuseStep^[j] 4459 = 1 := reachStep (stepEq 1 (by rfl) ⟨3344, by rfl⟩ : syracuseStep 4459 = 6689) R6689
theorem R4463 : ∃ j : ℕ, syracuseStep^[j] 4463 = 1 := reachStep (stepEq 1 (by rfl) ⟨3347, by rfl⟩ : syracuseStep 4463 = 6695) R6695
theorem R4465 : ∃ j : ℕ, syracuseStep^[j] 4465 = 1 := reachStep (stepEq 2 (by rfl) ⟨1674, by rfl⟩ : syracuseStep 4465 = 3349) R3349
theorem R4469 : ∃ j : ℕ, syracuseStep^[j] 4469 = 1 := reachStep (stepEq 5 (by rfl) ⟨209, by rfl⟩ : syracuseStep 4469 = 419) R419
theorem R4471 : ∃ j : ℕ, syracuseStep^[j] 4471 = 1 := reachStep (stepEq 1 (by rfl) ⟨3353, by rfl⟩ : syracuseStep 4471 = 6707) R6707
theorem R4481 : ∃ j : ℕ, syracuseStep^[j] 4481 = 1 := reachStep (stepEq 2 (by rfl) ⟨1680, by rfl⟩ : syracuseStep 4481 = 3361) R3361
theorem R4483 : ∃ j : ℕ, syracuseStep^[j] 4483 = 1 := reachStep (stepEq 1 (by rfl) ⟨3362, by rfl⟩ : syracuseStep 4483 = 6725) R6725
theorem R4485 : ∃ j : ℕ, syracuseStep^[j] 4485 = 1 := reachStep (stepEq 4 (by rfl) ⟨420, by rfl⟩ : syracuseStep 4485 = 841) R841
theorem R4487 : ∃ j : ℕ, syracuseStep^[j] 4487 = 1 := reachStep (stepEq 1 (by rfl) ⟨3365, by rfl⟩ : syracuseStep 4487 = 6731) R6731
theorem R4493 : ∃ j : ℕ, syracuseStep^[j] 4493 = 1 := reachStep (stepEq 3 (by rfl) ⟨842, by rfl⟩ : syracuseStep 4493 = 1685) R1685
theorem R4497 : ∃ j : ℕ, syracuseStep^[j] 4497 = 1 := reachStep (stepEq 2 (by rfl) ⟨1686, by rfl⟩ : syracuseStep 4497 = 3373) R3373
theorem R4499 : ∃ j : ℕ, syracuseStep^[j] 4499 = 1 := reachStep (stepEq 1 (by rfl) ⟨3374, by rfl⟩ : syracuseStep 4499 = 6749) R6749
theorem R4501 : ∃ j : ℕ, syracuseStep^[j] 4501 = 1 := reachStep (stepEq 6 (by rfl) ⟨105, by rfl⟩ : syracuseStep 4501 = 211) R211
theorem R4597 : ∃ j : ℕ, syracuseStep^[j] 4597 = 1 := reachStep (stepEq 5 (by rfl) ⟨215, by rfl⟩ : syracuseStep 4597 = 431) R431
theorem R4609 : ∃ j : ℕ, syracuseStep^[j] 4609 = 1 := reachStep (stepEq 2 (by rfl) ⟨1728, by rfl⟩ : syracuseStep 4609 = 3457) R3457
theorem R37441 : ∃ j : ℕ, syracuseStep^[j] 37441 = 1 := reachStep (stepEq 2 (by rfl) ⟨14040, by rfl⟩ : syracuseStep 37441 = 28081) R28081
theorem R4679 : ∃ j : ℕ, syracuseStep^[j] 4679 = 1 := reachStep (stepEq 1 (by rfl) ⟨3509, by rfl⟩ : syracuseStep 4679 = 7019) R7019
theorem R4681 : ∃ j : ℕ, syracuseStep^[j] 4681 = 1 := reachStep (stepEq 2 (by rfl) ⟨1755, by rfl⟩ : syracuseStep 4681 = 3511) R3511
theorem R4809 : ∃ j : ℕ, syracuseStep^[j] 4809 = 1 := reachStep (stepEq 2 (by rfl) ⟨1803, by rfl⟩ : syracuseStep 4809 = 3607) R3607
theorem R4811 : ∃ j : ℕ, syracuseStep^[j] 4811 = 1 := reachStep (stepEq 1 (by rfl) ⟨3608, by rfl⟩ : syracuseStep 4811 = 7217) R7217
theorem R4853 : ∃ j : ℕ, syracuseStep^[j] 4853 = 1 := reachStep (stepEq 5 (by rfl) ⟨227, by rfl⟩ : syracuseStep 4853 = 455) R455
theorem R4865 : ∃ j : ℕ, syracuseStep^[j] 4865 = 1 := reachStep (stepEq 2 (by rfl) ⟨1824, by rfl⟩ : syracuseStep 4865 = 3649) R3649
theorem R4867 : ∃ j : ℕ, syracuseStep^[j] 4867 = 1 := reachStep (stepEq 1 (by rfl) ⟨3650, by rfl⟩ : syracuseStep 4867 = 7301) R7301
theorem R4871 : ∃ j : ℕ, syracuseStep^[j] 4871 = 1 := reachStep (stepEq 1 (by rfl) ⟨3653, by rfl⟩ : syracuseStep 4871 = 7307) R7307
theorem R4887 : ∃ j : ℕ, syracuseStep^[j] 4887 = 1 := reachStep (stepEq 1 (by rfl) ⟨3665, by rfl⟩ : syracuseStep 4887 = 7331) R7331
theorem R4889 : ∃ j : ℕ, syracuseStep^[j] 4889 = 1 := reachStep (stepEq 2 (by rfl) ⟨1833, by rfl⟩ : syracuseStep 4889 = 3667) R3667
theorem R4959 : ∃ j : ℕ, syracuseStep^[j] 4959 = 1 := reachStep (stepEq 1 (by rfl) ⟨3719, by rfl⟩ : syracuseStep 4959 = 7439) R7439
theorem R5335 : ∃ j : ℕ, syracuseStep^[j] 5335 = 1 := reachStep (stepEq 1 (by rfl) ⟨4001, by rfl⟩ : syracuseStep 5335 = 8003) R8003
theorem R5339 : ∃ j : ℕ, syracuseStep^[j] 5339 = 1 := reachStep (stepEq 1 (by rfl) ⟨4004, by rfl⟩ : syracuseStep 5339 = 8009) R8009
theorem R5343 : ∃ j : ℕ, syracuseStep^[j] 5343 = 1 := reachStep (stepEq 1 (by rfl) ⟨4007, by rfl⟩ : syracuseStep 5343 = 8015) R8015
theorem R5349 : ∃ j : ℕ, syracuseStep^[j] 5349 = 1 := reachStep (stepEq 4 (by rfl) ⟨501, by rfl⟩ : syracuseStep 5349 = 1003) R1003
theorem R5353 : ∃ j : ℕ, syracuseStep^[j] 5353 = 1 := reachStep (stepEq 2 (by rfl) ⟨2007, by rfl⟩ : syracuseStep 5353 = 4015) R4015
theorem R5363 : ∃ j : ℕ, syracuseStep^[j] 5363 = 1 := reachStep (stepEq 1 (by rfl) ⟨4022, by rfl⟩ : syracuseStep 5363 = 8045) R8045
theorem R8675 : ∃ j : ℕ, syracuseStep^[j] 8675 = 1 := reachStep (stepEq 1 (by rfl) ⟨6506, by rfl⟩ : syracuseStep 8675 = 13013) R13013
theorem R8689 : ∃ j : ℕ, syracuseStep^[j] 8689 = 1 := reachStep (stepEq 2 (by rfl) ⟨3258, by rfl⟩ : syracuseStep 8689 = 6517) R6517
theorem R8717 : ∃ j : ℕ, syracuseStep^[j] 8717 = 1 := reachStep (stepEq 3 (by rfl) ⟨1634, by rfl⟩ : syracuseStep 8717 = 3269) R3269
theorem R8747 : ∃ j : ℕ, syracuseStep^[j] 8747 = 1 := reachStep (stepEq 1 (by rfl) ⟨6560, by rfl⟩ : syracuseStep 8747 = 13121) R13121
theorem R8849 : ∃ j : ℕ, syracuseStep^[j] 8849 = 1 := reachStep (stepEq 2 (by rfl) ⟨3318, by rfl⟩ : syracuseStep 8849 = 6637) R6637
theorem R8851 : ∃ j : ℕ, syracuseStep^[j] 8851 = 1 := reachStep (stepEq 1 (by rfl) ⟨6638, by rfl⟩ : syracuseStep 8851 = 13277) R13277
theorem R8915 : ∃ j : ℕ, syracuseStep^[j] 8915 = 1 := reachStep (stepEq 1 (by rfl) ⟨6686, by rfl⟩ : syracuseStep 8915 = 13373) R13373
theorem R8927 : ∃ j : ℕ, syracuseStep^[j] 8927 = 1 := reachStep (stepEq 1 (by rfl) ⟨6695, by rfl⟩ : syracuseStep 8927 = 13391) R13391
theorem R8945 : ∃ j : ℕ, syracuseStep^[j] 8945 = 1 := reachStep (stepEq 2 (by rfl) ⟨3354, by rfl⟩ : syracuseStep 8945 = 6709) R6709
theorem R8963 : ∃ j : ℕ, syracuseStep^[j] 8963 = 1 := reachStep (stepEq 1 (by rfl) ⟨6722, by rfl⟩ : syracuseStep 8963 = 13445) R13445
theorem R8975 : ∃ j : ℕ, syracuseStep^[j] 8975 = 1 := reachStep (stepEq 1 (by rfl) ⟨6731, by rfl⟩ : syracuseStep 8975 = 13463) R13463
theorem R8977 : ∃ j : ℕ, syracuseStep^[j] 8977 = 1 := reachStep (stepEq 2 (by rfl) ⟨3366, by rfl⟩ : syracuseStep 8977 = 6733) R6733
theorem R8981 : ∃ j : ℕ, syracuseStep^[j] 8981 = 1 := reachStep (stepEq 6 (by rfl) ⟨210, by rfl⟩ : syracuseStep 8981 = 421) R421
theorem R9067 : ∃ j : ℕ, syracuseStep^[j] 9067 = 1 := reachStep (stepEq 1 (by rfl) ⟨6800, by rfl⟩ : syracuseStep 9067 = 13601) R13601
theorem R9359 : ∃ j : ℕ, syracuseStep^[j] 9359 = 1 := reachStep (stepEq 1 (by rfl) ⟨7019, by rfl⟩ : syracuseStep 9359 = 14039) R14039
theorem R9617 : ∃ j : ℕ, syracuseStep^[j] 9617 = 1 := reachStep (stepEq 2 (by rfl) ⟨3606, by rfl⟩ : syracuseStep 9617 = 7213) R7213
theorem R9623 : ∃ j : ℕ, syracuseStep^[j] 9623 = 1 := reachStep (stepEq 1 (by rfl) ⟨7217, by rfl⟩ : syracuseStep 9623 = 14435) R14435
theorem R9625 : ∃ j : ℕ, syracuseStep^[j] 9625 = 1 := reachStep (stepEq 2 (by rfl) ⟨3609, by rfl⟩ : syracuseStep 9625 = 7219) R7219
theorem R9713 : ∃ j : ℕ, syracuseStep^[j] 9713 = 1 := reachStep (stepEq 2 (by rfl) ⟨3642, by rfl⟩ : syracuseStep 9713 = 7285) R7285
theorem R9731 : ∃ j : ℕ, syracuseStep^[j] 9731 = 1 := reachStep (stepEq 1 (by rfl) ⟨7298, by rfl⟩ : syracuseStep 9731 = 14597) R14597
theorem R9733 : ∃ j : ℕ, syracuseStep^[j] 9733 = 1 := reachStep (stepEq 4 (by rfl) ⟨912, by rfl⟩ : syracuseStep 9733 = 1825) R1825
theorem R9739 : ∃ j : ℕ, syracuseStep^[j] 9739 = 1 := reachStep (stepEq 1 (by rfl) ⟨7304, by rfl⟩ : syracuseStep 9739 = 14609) R14609
theorem R9743 : ∃ j : ℕ, syracuseStep^[j] 9743 = 1 := reachStep (stepEq 1 (by rfl) ⟨7307, by rfl⟩ : syracuseStep 9743 = 14615) R14615
theorem R9761 : ∃ j : ℕ, syracuseStep^[j] 9761 = 1 := reachStep (stepEq 2 (by rfl) ⟨3660, by rfl⟩ : syracuseStep 9761 = 7321) R7321
theorem R9773 : ∃ j : ℕ, syracuseStep^[j] 9773 = 1 := reachStep (stepEq 3 (by rfl) ⟨1832, by rfl⟩ : syracuseStep 9773 = 3665) R3665
theorem R9779 : ∃ j : ℕ, syracuseStep^[j] 9779 = 1 := reachStep (stepEq 1 (by rfl) ⟨7334, by rfl⟩ : syracuseStep 9779 = 14669) R14669
theorem R9833 : ∃ j : ℕ, syracuseStep^[j] 9833 = 1 := reachStep (stepEq 2 (by rfl) ⟨3687, by rfl⟩ : syracuseStep 9833 = 7375) R7375
theorem R9839 : ∃ j : ℕ, syracuseStep^[j] 9839 = 1 := reachStep (stepEq 1 (by rfl) ⟨7379, by rfl⟩ : syracuseStep 9839 = 14759) R14759
theorem R9917 : ∃ j : ℕ, syracuseStep^[j] 9917 = 1 := reachStep (stepEq 3 (by rfl) ⟨1859, by rfl⟩ : syracuseStep 9917 = 3719) R3719
theorem R10031 : ∃ j : ℕ, syracuseStep^[j] 10031 = 1 := reachStep (stepEq 1 (by rfl) ⟨7523, by rfl⟩ : syracuseStep 10031 = 15047) R15047
theorem R10091 : ∃ j : ℕ, syracuseStep^[j] 10091 = 1 := reachStep (stepEq 1 (by rfl) ⟨7568, by rfl⟩ : syracuseStep 10091 = 15137) R15137
theorem R10685 : ∃ j : ℕ, syracuseStep^[j] 10685 = 1 := reachStep (stepEq 3 (by rfl) ⟨2003, by rfl⟩ : syracuseStep 10685 = 4007) R4007
theorem R10705 : ∃ j : ℕ, syracuseStep^[j] 10705 = 1 := reachStep (stepEq 2 (by rfl) ⟨4014, by rfl⟩ : syracuseStep 10705 = 8029) R8029
theorem R79325 : ∃ j : ℕ, syracuseStep^[j] 79325 = 1 := reachStep (stepEq 3 (by rfl) ⟨14873, by rfl⟩ : syracuseStep 79325 = 29747) R29747
theorem R17495 : ∃ j : ℕ, syracuseStep^[j] 17495 = 1 := reachStep (stepEq 1 (by rfl) ⟨13121, by rfl⟩ : syracuseStep 17495 = 26243) R26243
theorem R17891 : ∃ j : ℕ, syracuseStep^[j] 17891 = 1 := reachStep (stepEq 1 (by rfl) ⟨13418, by rfl⟩ : syracuseStep 17891 = 26837) R26837
theorem R17941 : ∃ j : ℕ, syracuseStep^[j] 17941 = 1 := reachStep (stepEq 6 (by rfl) ⟨420, by rfl⟩ : syracuseStep 17941 = 841) R841
theorem R18521 : ∃ j : ℕ, syracuseStep^[j] 18521 = 1 := reachStep (stepEq 2 (by rfl) ⟨6945, by rfl⟩ : syracuseStep 18521 = 13891) R13891
theorem R19835 : ∃ j : ℕ, syracuseStep^[j] 19835 = 1 := reachStep (stepEq 1 (by rfl) ⟨14876, by rfl⟩ : syracuseStep 19835 = 29753) R29753
theorem R185 : ∃ j : ℕ, syracuseStep^[j] 185 = 1 := reachStep (stepEq 2 (by rfl) ⟨69, by rfl⟩ : syracuseStep 185 = 139) R139
theorem R187 : ∃ j : ℕ, syracuseStep^[j] 187 = 1 := reachStep (stepEq 1 (by rfl) ⟨140, by rfl⟩ : syracuseStep 187 = 281) R281
theorem R191 : ∃ j : ℕ, syracuseStep^[j] 191 = 1 := reachStep (stepEq 1 (by rfl) ⟨143, by rfl⟩ : syracuseStep 191 = 287) R287
theorem R361 : ∃ j : ℕ, syracuseStep^[j] 361 = 1 := reachStep (stepEq 2 (by rfl) ⟨135, by rfl⟩ : syracuseStep 361 = 271) R271
theorem R363 : ∃ j : ℕ, syracuseStep^[j] 363 = 1 := reachStep (stepEq 1 (by rfl) ⟨272, by rfl⟩ : syracuseStep 363 = 545) R545
theorem R367 : ∃ j : ℕ, syracuseStep^[j] 367 = 1 := reachStep (stepEq 1 (by rfl) ⟨275, by rfl⟩ : syracuseStep 367 = 551) R551
theorem R371 : ∃ j : ℕ, syracuseStep^[j] 371 = 1 := reachStep (stepEq 1 (by rfl) ⟨278, by rfl⟩ : syracuseStep 371 = 557) R557
theorem R375 : ∃ j : ℕ, syracuseStep^[j] 375 = 1 := reachStep (stepEq 1 (by rfl) ⟨281, by rfl⟩ : syracuseStep 375 = 563) R563
theorem R383 : ∃ j : ℕ, syracuseStep^[j] 383 = 1 := reachStep (stepEq 1 (by rfl) ⟨287, by rfl⟩ : syracuseStep 383 = 575) R575
theorem R721 : ∃ j : ℕ, syracuseStep^[j] 721 = 1 := reachStep (stepEq 2 (by rfl) ⟨270, by rfl⟩ : syracuseStep 721 = 541) R541
theorem R723 : ∃ j : ℕ, syracuseStep^[j] 723 = 1 := reachStep (stepEq 1 (by rfl) ⟨542, by rfl⟩ : syracuseStep 723 = 1085) R1085
theorem R727 : ∃ j : ℕ, syracuseStep^[j] 727 = 1 := reachStep (stepEq 1 (by rfl) ⟨545, by rfl⟩ : syracuseStep 727 = 1091) R1091
theorem R735 : ∃ j : ℕ, syracuseStep^[j] 735 = 1 := reachStep (stepEq 1 (by rfl) ⟨551, by rfl⟩ : syracuseStep 735 = 1103) R1103
theorem R741 : ∃ j : ℕ, syracuseStep^[j] 741 = 1 := reachStep (stepEq 4 (by rfl) ⟨69, by rfl⟩ : syracuseStep 741 = 139) R139
theorem R747 : ∃ j : ℕ, syracuseStep^[j] 747 = 1 := reachStep (stepEq 1 (by rfl) ⟨560, by rfl⟩ : syracuseStep 747 = 1121) R1121
theorem R749 : ∃ j : ℕ, syracuseStep^[j] 749 = 1 := reachStep (stepEq 3 (by rfl) ⟨140, by rfl⟩ : syracuseStep 749 = 281) R281
theorem R765 : ∃ j : ℕ, syracuseStep^[j] 765 = 1 := reachStep (stepEq 3 (by rfl) ⟨143, by rfl⟩ : syracuseStep 765 = 287) R287
theorem R809 : ∃ j : ℕ, syracuseStep^[j] 809 = 1 := reachStep (stepEq 2 (by rfl) ⟨303, by rfl⟩ : syracuseStep 809 = 607) R607
theorem R891 : ∃ j : ℕ, syracuseStep^[j] 891 = 1 := reachStep (stepEq 1 (by rfl) ⟨668, by rfl⟩ : syracuseStep 891 = 1337) R1337
theorem R1443 : ∃ j : ℕ, syracuseStep^[j] 1443 = 1 := reachStep (stepEq 1 (by rfl) ⟨1082, by rfl⟩ : syracuseStep 1443 = 2165) R2165
theorem R1445 : ∃ j : ℕ, syracuseStep^[j] 1445 = 1 := reachStep (stepEq 4 (by rfl) ⟨135, by rfl⟩ : syracuseStep 1445 = 271) R271
theorem R1453 : ∃ j : ℕ, syracuseStep^[j] 1453 = 1 := reachStep (stepEq 3 (by rfl) ⟨272, by rfl⟩ : syracuseStep 1453 = 545) R545
theorem R1469 : ∃ j : ℕ, syracuseStep^[j] 1469 = 1 := reachStep (stepEq 3 (by rfl) ⟨275, by rfl⟩ : syracuseStep 1469 = 551) R551
theorem R1485 : ∃ j : ℕ, syracuseStep^[j] 1485 = 1 := reachStep (stepEq 3 (by rfl) ⟨278, by rfl⟩ : syracuseStep 1485 = 557) R557
theorem R1489 : ∃ j : ℕ, syracuseStep^[j] 1489 = 1 := reachStep (stepEq 2 (by rfl) ⟨558, by rfl⟩ : syracuseStep 1489 = 1117) R1117
theorem R1495 : ∃ j : ℕ, syracuseStep^[j] 1495 = 1 := reachStep (stepEq 1 (by rfl) ⟨1121, by rfl⟩ : syracuseStep 1495 = 2243) R2243
theorem R1497 : ∃ j : ℕ, syracuseStep^[j] 1497 = 1 := reachStep (stepEq 2 (by rfl) ⟨561, by rfl⟩ : syracuseStep 1497 = 1123) R1123
theorem R1499 : ∃ j : ℕ, syracuseStep^[j] 1499 = 1 := reachStep (stepEq 1 (by rfl) ⟨1124, by rfl⟩ : syracuseStep 1499 = 2249) R2249
theorem R1501 : ∃ j : ℕ, syracuseStep^[j] 1501 = 1 := reachStep (stepEq 3 (by rfl) ⟨281, by rfl⟩ : syracuseStep 1501 = 563) R563
theorem R1533 : ∃ j : ℕ, syracuseStep^[j] 1533 = 1 := reachStep (stepEq 3 (by rfl) ⟨287, by rfl⟩ : syracuseStep 1533 = 575) R575
theorem R1617 : ∃ j : ℕ, syracuseStep^[j] 1617 = 1 := reachStep (stepEq 2 (by rfl) ⟨606, by rfl⟩ : syracuseStep 1617 = 1213) R1213
theorem R1619 : ∃ j : ℕ, syracuseStep^[j] 1619 = 1 := reachStep (stepEq 1 (by rfl) ⟨1214, by rfl⟩ : syracuseStep 1619 = 2429) R2429
theorem R1783 : ∃ j : ℕ, syracuseStep^[j] 1783 = 1 := reachStep (stepEq 1 (by rfl) ⟨1337, by rfl⟩ : syracuseStep 1783 = 2675) R2675
theorem R1787 : ∃ j : ℕ, syracuseStep^[j] 1787 = 1 := reachStep (stepEq 1 (by rfl) ⟨1340, by rfl⟩ : syracuseStep 1787 = 2681) R2681
theorem R2885 : ∃ j : ℕ, syracuseStep^[j] 2885 = 1 := reachStep (stepEq 4 (by rfl) ⟨270, by rfl⟩ : syracuseStep 2885 = 541) R541
theorem R2891 : ∃ j : ℕ, syracuseStep^[j] 2891 = 1 := reachStep (stepEq 1 (by rfl) ⟨2168, by rfl⟩ : syracuseStep 2891 = 4337) R4337
theorem R2893 : ∃ j : ℕ, syracuseStep^[j] 2893 = 1 := reachStep (stepEq 3 (by rfl) ⟨542, by rfl⟩ : syracuseStep 2893 = 1085) R1085
theorem R2905 : ∃ j : ℕ, syracuseStep^[j] 2905 = 1 := reachStep (stepEq 2 (by rfl) ⟨1089, by rfl⟩ : syracuseStep 2905 = 2179) R2179
theorem R2909 : ∃ j : ℕ, syracuseStep^[j] 2909 = 1 := reachStep (stepEq 3 (by rfl) ⟨545, by rfl⟩ : syracuseStep 2909 = 1091) R1091
theorem R2941 : ∃ j : ℕ, syracuseStep^[j] 2941 = 1 := reachStep (stepEq 3 (by rfl) ⟨551, by rfl⟩ : syracuseStep 2941 = 1103) R1103
theorem R2965 : ∃ j : ℕ, syracuseStep^[j] 2965 = 1 := reachStep (stepEq 6 (by rfl) ⟨69, by rfl⟩ : syracuseStep 2965 = 139) R139
theorem R2971 : ∃ j : ℕ, syracuseStep^[j] 2971 = 1 := reachStep (stepEq 1 (by rfl) ⟨2228, by rfl⟩ : syracuseStep 2971 = 4457) R4457
theorem R2975 : ∃ j : ℕ, syracuseStep^[j] 2975 = 1 := reachStep (stepEq 1 (by rfl) ⟨2231, by rfl⟩ : syracuseStep 2975 = 4463) R4463
theorem R2979 : ∃ j : ℕ, syracuseStep^[j] 2979 = 1 := reachStep (stepEq 1 (by rfl) ⟨2234, by rfl⟩ : syracuseStep 2979 = 4469) R4469
theorem R2987 : ∃ j : ℕ, syracuseStep^[j] 2987 = 1 := reachStep (stepEq 1 (by rfl) ⟨2240, by rfl⟩ : syracuseStep 2987 = 4481) R4481
theorem R2989 : ∃ j : ℕ, syracuseStep^[j] 2989 = 1 := reachStep (stepEq 3 (by rfl) ⟨560, by rfl⟩ : syracuseStep 2989 = 1121) R1121
theorem R2991 : ∃ j : ℕ, syracuseStep^[j] 2991 = 1 := reachStep (stepEq 1 (by rfl) ⟨2243, by rfl⟩ : syracuseStep 2991 = 4487) R4487
theorem R2993 : ∃ j : ℕ, syracuseStep^[j] 2993 = 1 := reachStep (stepEq 2 (by rfl) ⟨1122, by rfl⟩ : syracuseStep 2993 = 2245) R2245
theorem R2995 : ∃ j : ℕ, syracuseStep^[j] 2995 = 1 := reachStep (stepEq 1 (by rfl) ⟨2246, by rfl⟩ : syracuseStep 2995 = 4493) R4493
theorem R2997 : ∃ j : ℕ, syracuseStep^[j] 2997 = 1 := reachStep (stepEq 5 (by rfl) ⟨140, by rfl⟩ : syracuseStep 2997 = 281) R281
theorem R2999 : ∃ j : ℕ, syracuseStep^[j] 2999 = 1 := reachStep (stepEq 1 (by rfl) ⟨2249, by rfl⟩ : syracuseStep 2999 = 4499) R4499
theorem R3061 : ∃ j : ℕ, syracuseStep^[j] 3061 = 1 := reachStep (stepEq 5 (by rfl) ⟨143, by rfl⟩ : syracuseStep 3061 = 287) R287
theorem R199685 : ∃ j : ℕ, syracuseStep^[j] 199685 = 1 := reachStep (stepEq 4 (by rfl) ⟨18720, by rfl⟩ : syracuseStep 199685 = 37441) R37441
theorem R3119 : ∃ j : ℕ, syracuseStep^[j] 3119 = 1 := reachStep (stepEq 1 (by rfl) ⟨2339, by rfl⟩ : syracuseStep 3119 = 4679) R4679
theorem R3207 : ∃ j : ℕ, syracuseStep^[j] 3207 = 1 := reachStep (stepEq 1 (by rfl) ⟨2405, by rfl⟩ : syracuseStep 3207 = 4811) R4811
theorem R3235 : ∃ j : ℕ, syracuseStep^[j] 3235 = 1 := reachStep (stepEq 1 (by rfl) ⟨2426, by rfl⟩ : syracuseStep 3235 = 4853) R4853
theorem R3237 : ∃ j : ℕ, syracuseStep^[j] 3237 = 1 := reachStep (stepEq 4 (by rfl) ⟨303, by rfl⟩ : syracuseStep 3237 = 607) R607
theorem R3243 : ∃ j : ℕ, syracuseStep^[j] 3243 = 1 := reachStep (stepEq 1 (by rfl) ⟨2432, by rfl⟩ : syracuseStep 3243 = 4865) R4865
theorem R3247 : ∃ j : ℕ, syracuseStep^[j] 3247 = 1 := reachStep (stepEq 1 (by rfl) ⟨2435, by rfl⟩ : syracuseStep 3247 = 4871) R4871
theorem R3257 : ∃ j : ℕ, syracuseStep^[j] 3257 = 1 := reachStep (stepEq 2 (by rfl) ⟨1221, by rfl⟩ : syracuseStep 3257 = 2443) R2443
theorem R3259 : ∃ j : ℕ, syracuseStep^[j] 3259 = 1 := reachStep (stepEq 1 (by rfl) ⟨2444, by rfl⟩ : syracuseStep 3259 = 4889) R4889
theorem R3305 : ∃ j : ℕ, syracuseStep^[j] 3305 = 1 := reachStep (stepEq 2 (by rfl) ⟨1239, by rfl⟩ : syracuseStep 3305 = 2479) R2479
theorem R3559 : ∃ j : ℕ, syracuseStep^[j] 3559 = 1 := reachStep (stepEq 1 (by rfl) ⟨2669, by rfl⟩ : syracuseStep 3559 = 5339) R5339
theorem R3561 : ∃ j : ℕ, syracuseStep^[j] 3561 = 1 := reachStep (stepEq 2 (by rfl) ⟨1335, by rfl⟩ : syracuseStep 3561 = 2671) R2671
theorem R3565 : ∃ j : ℕ, syracuseStep^[j] 3565 = 1 := reachStep (stepEq 3 (by rfl) ⟨668, by rfl⟩ : syracuseStep 3565 = 1337) R1337
theorem R3575 : ∃ j : ℕ, syracuseStep^[j] 3575 = 1 := reachStep (stepEq 1 (by rfl) ⟨2681, by rfl⟩ : syracuseStep 3575 = 5363) R5363
theorem R5773 : ∃ j : ℕ, syracuseStep^[j] 5773 = 1 := reachStep (stepEq 3 (by rfl) ⟨1082, by rfl⟩ : syracuseStep 5773 = 2165) R2165
theorem R5781 : ∃ j : ℕ, syracuseStep^[j] 5781 = 1 := reachStep (stepEq 6 (by rfl) ⟨135, by rfl⟩ : syracuseStep 5781 = 271) R271
theorem R5783 : ∃ j : ℕ, syracuseStep^[j] 5783 = 1 := reachStep (stepEq 1 (by rfl) ⟨4337, by rfl⟩ : syracuseStep 5783 = 8675) R8675
theorem R5809 : ∃ j : ℕ, syracuseStep^[j] 5809 = 1 := reachStep (stepEq 2 (by rfl) ⟨2178, by rfl⟩ : syracuseStep 5809 = 4357) R4357
theorem R5811 : ∃ j : ℕ, syracuseStep^[j] 5811 = 1 := reachStep (stepEq 1 (by rfl) ⟨4358, by rfl⟩ : syracuseStep 5811 = 8717) R8717
theorem R5813 : ∃ j : ℕ, syracuseStep^[j] 5813 = 1 := reachStep (stepEq 5 (by rfl) ⟨272, by rfl⟩ : syracuseStep 5813 = 545) R545
theorem R5825 : ∃ j : ℕ, syracuseStep^[j] 5825 = 1 := reachStep (stepEq 2 (by rfl) ⟨2184, by rfl⟩ : syracuseStep 5825 = 4369) R4369
theorem R5831 : ∃ j : ℕ, syracuseStep^[j] 5831 = 1 := reachStep (stepEq 1 (by rfl) ⟨4373, by rfl⟩ : syracuseStep 5831 = 8747) R8747
theorem R5877 : ∃ j : ℕ, syracuseStep^[j] 5877 = 1 := reachStep (stepEq 5 (by rfl) ⟨275, by rfl⟩ : syracuseStep 5877 = 551) R551
theorem R5881 : ∃ j : ℕ, syracuseStep^[j] 5881 = 1 := reachStep (stepEq 2 (by rfl) ⟨2205, by rfl⟩ : syracuseStep 5881 = 4411) R4411
theorem R5899 : ∃ j : ℕ, syracuseStep^[j] 5899 = 1 := reachStep (stepEq 1 (by rfl) ⟨4424, by rfl⟩ : syracuseStep 5899 = 8849) R8849
theorem R5941 : ∃ j : ℕ, syracuseStep^[j] 5941 = 1 := reachStep (stepEq 5 (by rfl) ⟨278, by rfl⟩ : syracuseStep 5941 = 557) R557
theorem R5943 : ∃ j : ℕ, syracuseStep^[j] 5943 = 1 := reachStep (stepEq 1 (by rfl) ⟨4457, by rfl⟩ : syracuseStep 5943 = 8915) R8915
theorem R5945 : ∃ j : ℕ, syracuseStep^[j] 5945 = 1 := reachStep (stepEq 2 (by rfl) ⟨2229, by rfl⟩ : syracuseStep 5945 = 4459) R4459
theorem R5951 : ∃ j : ℕ, syracuseStep^[j] 5951 = 1 := reachStep (stepEq 1 (by rfl) ⟨4463, by rfl⟩ : syracuseStep 5951 = 8927) R8927
theorem R5953 : ∃ j : ℕ, syracuseStep^[j] 5953 = 1 := reachStep (stepEq 2 (by rfl) ⟨2232, by rfl⟩ : syracuseStep 5953 = 4465) R4465
theorem R5957 : ∃ j : ℕ, syracuseStep^[j] 5957 = 1 := reachStep (stepEq 4 (by rfl) ⟨558, by rfl⟩ : syracuseStep 5957 = 1117) R1117
theorem R5961 : ∃ j : ℕ, syracuseStep^[j] 5961 = 1 := reachStep (stepEq 2 (by rfl) ⟨2235, by rfl⟩ : syracuseStep 5961 = 4471) R4471
theorem R5963 : ∃ j : ℕ, syracuseStep^[j] 5963 = 1 := reachStep (stepEq 1 (by rfl) ⟨4472, by rfl⟩ : syracuseStep 5963 = 8945) R8945
theorem R5975 : ∃ j : ℕ, syracuseStep^[j] 5975 = 1 := reachStep (stepEq 1 (by rfl) ⟨4481, by rfl⟩ : syracuseStep 5975 = 8963) R8963
theorem R5977 : ∃ j : ℕ, syracuseStep^[j] 5977 = 1 := reachStep (stepEq 2 (by rfl) ⟨2241, by rfl⟩ : syracuseStep 5977 = 4483) R4483
theorem R5981 : ∃ j : ℕ, syracuseStep^[j] 5981 = 1 := reachStep (stepEq 3 (by rfl) ⟨1121, by rfl⟩ : syracuseStep 5981 = 2243) R2243
theorem R5983 : ∃ j : ℕ, syracuseStep^[j] 5983 = 1 := reachStep (stepEq 1 (by rfl) ⟨4487, by rfl⟩ : syracuseStep 5983 = 8975) R8975
theorem R5987 : ∃ j : ℕ, syracuseStep^[j] 5987 = 1 := reachStep (stepEq 1 (by rfl) ⟨4490, by rfl⟩ : syracuseStep 5987 = 8981) R8981
theorem R5989 : ∃ j : ℕ, syracuseStep^[j] 5989 = 1 := reachStep (stepEq 4 (by rfl) ⟨561, by rfl⟩ : syracuseStep 5989 = 1123) R1123
theorem R5997 : ∃ j : ℕ, syracuseStep^[j] 5997 = 1 := reachStep (stepEq 3 (by rfl) ⟨1124, by rfl⟩ : syracuseStep 5997 = 2249) R2249
theorem R6001 : ∃ j : ℕ, syracuseStep^[j] 6001 = 1 := reachStep (stepEq 2 (by rfl) ⟨2250, by rfl⟩ : syracuseStep 6001 = 4501) R4501
theorem R6005 : ∃ j : ℕ, syracuseStep^[j] 6005 = 1 := reachStep (stepEq 5 (by rfl) ⟨281, by rfl⟩ : syracuseStep 6005 = 563) R563
theorem R6129 : ∃ j : ℕ, syracuseStep^[j] 6129 = 1 := reachStep (stepEq 2 (by rfl) ⟨2298, by rfl⟩ : syracuseStep 6129 = 4597) R4597
theorem R6133 : ∃ j : ℕ, syracuseStep^[j] 6133 = 1 := reachStep (stepEq 5 (by rfl) ⟨287, by rfl⟩ : syracuseStep 6133 = 575) R575
theorem R6145 : ∃ j : ℕ, syracuseStep^[j] 6145 = 1 := reachStep (stepEq 2 (by rfl) ⟨2304, by rfl⟩ : syracuseStep 6145 = 4609) R4609
theorem R6239 : ∃ j : ℕ, syracuseStep^[j] 6239 = 1 := reachStep (stepEq 1 (by rfl) ⟨4679, by rfl⟩ : syracuseStep 6239 = 9359) R9359
theorem R6241 : ∃ j : ℕ, syracuseStep^[j] 6241 = 1 := reachStep (stepEq 2 (by rfl) ⟨2340, by rfl⟩ : syracuseStep 6241 = 4681) R4681
theorem R6411 : ∃ j : ℕ, syracuseStep^[j] 6411 = 1 := reachStep (stepEq 1 (by rfl) ⟨4808, by rfl⟩ : syracuseStep 6411 = 9617) R9617
theorem R6415 : ∃ j : ℕ, syracuseStep^[j] 6415 = 1 := reachStep (stepEq 1 (by rfl) ⟨4811, by rfl⟩ : syracuseStep 6415 = 9623) R9623
theorem R6469 : ∃ j : ℕ, syracuseStep^[j] 6469 = 1 := reachStep (stepEq 4 (by rfl) ⟨606, by rfl⟩ : syracuseStep 6469 = 1213) R1213
theorem R6475 : ∃ j : ℕ, syracuseStep^[j] 6475 = 1 := reachStep (stepEq 1 (by rfl) ⟨4856, by rfl⟩ : syracuseStep 6475 = 9713) R9713
theorem R6477 : ∃ j : ℕ, syracuseStep^[j] 6477 = 1 := reachStep (stepEq 3 (by rfl) ⟨1214, by rfl⟩ : syracuseStep 6477 = 2429) R2429
theorem R6487 : ∃ j : ℕ, syracuseStep^[j] 6487 = 1 := reachStep (stepEq 1 (by rfl) ⟨4865, by rfl⟩ : syracuseStep 6487 = 9731) R9731
theorem R6489 : ∃ j : ℕ, syracuseStep^[j] 6489 = 1 := reachStep (stepEq 2 (by rfl) ⟨2433, by rfl⟩ : syracuseStep 6489 = 4867) R4867
theorem R6495 : ∃ j : ℕ, syracuseStep^[j] 6495 = 1 := reachStep (stepEq 1 (by rfl) ⟨4871, by rfl⟩ : syracuseStep 6495 = 9743) R9743
theorem R6507 : ∃ j : ℕ, syracuseStep^[j] 6507 = 1 := reachStep (stepEq 1 (by rfl) ⟨4880, by rfl⟩ : syracuseStep 6507 = 9761) R9761
theorem R6515 : ∃ j : ℕ, syracuseStep^[j] 6515 = 1 := reachStep (stepEq 1 (by rfl) ⟨4886, by rfl⟩ : syracuseStep 6515 = 9773) R9773
theorem R6519 : ∃ j : ℕ, syracuseStep^[j] 6519 = 1 := reachStep (stepEq 1 (by rfl) ⟨4889, by rfl⟩ : syracuseStep 6519 = 9779) R9779
theorem R6555 : ∃ j : ℕ, syracuseStep^[j] 6555 = 1 := reachStep (stepEq 1 (by rfl) ⟨4916, by rfl⟩ : syracuseStep 6555 = 9833) R9833
theorem R6559 : ∃ j : ℕ, syracuseStep^[j] 6559 = 1 := reachStep (stepEq 1 (by rfl) ⟨4919, by rfl⟩ : syracuseStep 6559 = 9839) R9839
theorem R6611 : ∃ j : ℕ, syracuseStep^[j] 6611 = 1 := reachStep (stepEq 1 (by rfl) ⟨4958, by rfl⟩ : syracuseStep 6611 = 9917) R9917
theorem R6687 : ∃ j : ℕ, syracuseStep^[j] 6687 = 1 := reachStep (stepEq 1 (by rfl) ⟨5015, by rfl⟩ : syracuseStep 6687 = 10031) R10031
theorem R6727 : ∃ j : ℕ, syracuseStep^[j] 6727 = 1 := reachStep (stepEq 1 (by rfl) ⟨5045, by rfl⟩ : syracuseStep 6727 = 10091) R10091
theorem R7123 : ∃ j : ℕ, syracuseStep^[j] 7123 = 1 := reachStep (stepEq 1 (by rfl) ⟨5342, by rfl⟩ : syracuseStep 7123 = 10685) R10685
theorem R7133 : ∃ j : ℕ, syracuseStep^[j] 7133 = 1 := reachStep (stepEq 3 (by rfl) ⟨1337, by rfl⟩ : syracuseStep 7133 = 2675) R2675
theorem R11573 : ∃ j : ℕ, syracuseStep^[j] 11573 = 1 := reachStep (stepEq 5 (by rfl) ⟨542, by rfl⟩ : syracuseStep 11573 = 1085) R1085
theorem R11585 : ∃ j : ℕ, syracuseStep^[j] 11585 = 1 := reachStep (stepEq 2 (by rfl) ⟨4344, by rfl⟩ : syracuseStep 11585 = 8689) R8689
theorem R11663 : ∃ j : ℕ, syracuseStep^[j] 11663 = 1 := reachStep (stepEq 1 (by rfl) ⟨8747, by rfl⟩ : syracuseStep 11663 = 17495) R17495
theorem R11765 : ∃ j : ℕ, syracuseStep^[j] 11765 = 1 := reachStep (stepEq 5 (by rfl) ⟨551, by rfl⟩ : syracuseStep 11765 = 1103) R1103
theorem R11801 : ∃ j : ℕ, syracuseStep^[j] 11801 = 1 := reachStep (stepEq 2 (by rfl) ⟨4425, by rfl⟩ : syracuseStep 11801 = 8851) R8851
theorem R11861 : ∃ j : ℕ, syracuseStep^[j] 11861 = 1 := reachStep (stepEq 8 (by rfl) ⟨69, by rfl⟩ : syracuseStep 11861 = 139) R139
theorem R11927 : ∃ j : ℕ, syracuseStep^[j] 11927 = 1 := reachStep (stepEq 1 (by rfl) ⟨8945, by rfl⟩ : syracuseStep 11927 = 17891) R17891
theorem R11969 : ∃ j : ℕ, syracuseStep^[j] 11969 = 1 := reachStep (stepEq 2 (by rfl) ⟨4488, by rfl⟩ : syracuseStep 11969 = 8977) R8977
theorem R12089 : ∃ j : ℕ, syracuseStep^[j] 12089 = 1 := reachStep (stepEq 2 (by rfl) ⟨4533, by rfl⟩ : syracuseStep 12089 = 9067) R9067
theorem R12347 : ∃ j : ℕ, syracuseStep^[j] 12347 = 1 := reachStep (stepEq 1 (by rfl) ⟨9260, by rfl⟩ : syracuseStep 12347 = 18521) R18521
theorem R12833 : ∃ j : ℕ, syracuseStep^[j] 12833 = 1 := reachStep (stepEq 2 (by rfl) ⟨4812, by rfl⟩ : syracuseStep 12833 = 9625) R9625
theorem R12941 : ∃ j : ℕ, syracuseStep^[j] 12941 = 1 := reachStep (stepEq 3 (by rfl) ⟨2426, by rfl⟩ : syracuseStep 12941 = 4853) R4853
theorem R12977 : ∃ j : ℕ, syracuseStep^[j] 12977 = 1 := reachStep (stepEq 2 (by rfl) ⟨4866, by rfl⟩ : syracuseStep 12977 = 9733) R9733
theorem R13223 : ∃ j : ℕ, syracuseStep^[j] 13223 = 1 := reachStep (stepEq 1 (by rfl) ⟨9917, by rfl⟩ : syracuseStep 13223 = 19835) R19835
theorem R14237 : ∃ j : ℕ, syracuseStep^[j] 14237 = 1 := reachStep (stepEq 3 (by rfl) ⟨2669, by rfl⟩ : syracuseStep 14237 = 5339) R5339
theorem R14273 : ∃ j : ℕ, syracuseStep^[j] 14273 = 1 := reachStep (stepEq 2 (by rfl) ⟨5352, by rfl⟩ : syracuseStep 14273 = 10705) R10705
theorem R51941 : ∃ j : ℕ, syracuseStep^[j] 51941 = 1 := reachStep (stepEq 4 (by rfl) ⟨4869, by rfl⟩ : syracuseStep 51941 = 9739) R9739
theorem R52883 : ∃ j : ℕ, syracuseStep^[j] 52883 = 1 := reachStep (stepEq 1 (by rfl) ⟨39662, by rfl⟩ : syracuseStep 52883 = 79325) R79325
theorem R23237 : ∃ j : ℕ, syracuseStep^[j] 23237 = 1 := reachStep (stepEq 4 (by rfl) ⟨2178, by rfl⟩ : syracuseStep 23237 = 4357) R4357
theorem R23267 : ∃ j : ℕ, syracuseStep^[j] 23267 = 1 := reachStep (stepEq 1 (by rfl) ⟨17450, by rfl⟩ : syracuseStep 23267 = 34901) R34901
theorem R23813 : ∃ j : ℕ, syracuseStep^[j] 23813 = 1 := reachStep (stepEq 4 (by rfl) ⟨2232, by rfl⟩ : syracuseStep 23813 = 4465) R4465
theorem R23921 : ∃ j : ℕ, syracuseStep^[j] 23921 = 1 := reachStep (stepEq 2 (by rfl) ⟨8970, by rfl⟩ : syracuseStep 23921 = 17941) R17941
theorem R23989 : ∃ j : ℕ, syracuseStep^[j] 23989 = 1 := reachStep (stepEq 5 (by rfl) ⟨1124, by rfl⟩ : syracuseStep 23989 = 2249) R2249
theorem R24695 : ∃ j : ℕ, syracuseStep^[j] 24695 = 1 := reachStep (stepEq 1 (by rfl) ⟨18521, by rfl⟩ : syracuseStep 24695 = 37043) R37043
theorem R123 : ∃ j : ℕ, syracuseStep^[j] 123 = 1 := reachStep (stepEq 1 (by rfl) ⟨92, by rfl⟩ : syracuseStep 123 = 185) R185
theorem R127 : ∃ j : ℕ, syracuseStep^[j] 127 = 1 := reachStep (stepEq 1 (by rfl) ⟨95, by rfl⟩ : syracuseStep 127 = 191) R191
theorem R247 : ∃ j : ℕ, syracuseStep^[j] 247 = 1 := reachStep (stepEq 1 (by rfl) ⟨185, by rfl⟩ : syracuseStep 247 = 371) R371
theorem R249 : ∃ j : ℕ, syracuseStep^[j] 249 = 1 := reachStep (stepEq 2 (by rfl) ⟨93, by rfl⟩ : syracuseStep 249 = 187) R187
theorem R255 : ∃ j : ℕ, syracuseStep^[j] 255 = 1 := reachStep (stepEq 1 (by rfl) ⟨191, by rfl⟩ : syracuseStep 255 = 383) R383
theorem R481 : ∃ j : ℕ, syracuseStep^[j] 481 = 1 := reachStep (stepEq 2 (by rfl) ⟨180, by rfl⟩ : syracuseStep 481 = 361) R361
theorem R489 : ∃ j : ℕ, syracuseStep^[j] 489 = 1 := reachStep (stepEq 2 (by rfl) ⟨183, by rfl⟩ : syracuseStep 489 = 367) R367
theorem R493 : ∃ j : ℕ, syracuseStep^[j] 493 = 1 := reachStep (stepEq 3 (by rfl) ⟨92, by rfl⟩ : syracuseStep 493 = 185) R185
theorem R499 : ∃ j : ℕ, syracuseStep^[j] 499 = 1 := reachStep (stepEq 1 (by rfl) ⟨374, by rfl⟩ : syracuseStep 499 = 749) R749
theorem R509 : ∃ j : ℕ, syracuseStep^[j] 509 = 1 := reachStep (stepEq 3 (by rfl) ⟨95, by rfl⟩ : syracuseStep 509 = 191) R191
theorem R539 : ∃ j : ℕ, syracuseStep^[j] 539 = 1 := reachStep (stepEq 1 (by rfl) ⟨404, by rfl⟩ : syracuseStep 539 = 809) R809
theorem R961 : ∃ j : ℕ, syracuseStep^[j] 961 = 1 := reachStep (stepEq 2 (by rfl) ⟨360, by rfl⟩ : syracuseStep 961 = 721) R721
theorem R963 : ∃ j : ℕ, syracuseStep^[j] 963 = 1 := reachStep (stepEq 1 (by rfl) ⟨722, by rfl⟩ : syracuseStep 963 = 1445) R1445
theorem R969 : ∃ j : ℕ, syracuseStep^[j] 969 = 1 := reachStep (stepEq 2 (by rfl) ⟨363, by rfl⟩ : syracuseStep 969 = 727) R727
theorem R979 : ∃ j : ℕ, syracuseStep^[j] 979 = 1 := reachStep (stepEq 1 (by rfl) ⟨734, by rfl⟩ : syracuseStep 979 = 1469) R1469
theorem R989 : ∃ j : ℕ, syracuseStep^[j] 989 = 1 := reachStep (stepEq 3 (by rfl) ⟨185, by rfl⟩ : syracuseStep 989 = 371) R371
theorem R997 : ∃ j : ℕ, syracuseStep^[j] 997 = 1 := reachStep (stepEq 4 (by rfl) ⟨93, by rfl⟩ : syracuseStep 997 = 187) R187
theorem R999 : ∃ j : ℕ, syracuseStep^[j] 999 = 1 := reachStep (stepEq 1 (by rfl) ⟨749, by rfl⟩ : syracuseStep 999 = 1499) R1499
theorem R1021 : ∃ j : ℕ, syracuseStep^[j] 1021 = 1 := reachStep (stepEq 3 (by rfl) ⟨191, by rfl⟩ : syracuseStep 1021 = 383) R383
theorem R1079 : ∃ j : ℕ, syracuseStep^[j] 1079 = 1 := reachStep (stepEq 1 (by rfl) ⟨809, by rfl⟩ : syracuseStep 1079 = 1619) R1619
theorem R1191 : ∃ j : ℕ, syracuseStep^[j] 1191 = 1 := reachStep (stepEq 1 (by rfl) ⟨893, by rfl⟩ : syracuseStep 1191 = 1787) R1787
theorem R34627 : ∃ j : ℕ, syracuseStep^[j] 34627 = 1 := reachStep (stepEq 1 (by rfl) ⟨25970, by rfl⟩ : syracuseStep 34627 = 51941) R51941
theorem R1923 : ∃ j : ℕ, syracuseStep^[j] 1923 = 1 := reachStep (stepEq 1 (by rfl) ⟨1442, by rfl⟩ : syracuseStep 1923 = 2885) R2885
theorem R1925 : ∃ j : ℕ, syracuseStep^[j] 1925 = 1 := reachStep (stepEq 4 (by rfl) ⟨180, by rfl⟩ : syracuseStep 1925 = 361) R361
theorem R1927 : ∃ j : ℕ, syracuseStep^[j] 1927 = 1 := reachStep (stepEq 1 (by rfl) ⟨1445, by rfl⟩ : syracuseStep 1927 = 2891) R2891
theorem R1937 : ∃ j : ℕ, syracuseStep^[j] 1937 = 1 := reachStep (stepEq 2 (by rfl) ⟨726, by rfl⟩ : syracuseStep 1937 = 1453) R1453
theorem R1939 : ∃ j : ℕ, syracuseStep^[j] 1939 = 1 := reachStep (stepEq 1 (by rfl) ⟨1454, by rfl⟩ : syracuseStep 1939 = 2909) R2909
theorem R1957 : ∃ j : ℕ, syracuseStep^[j] 1957 = 1 := reachStep (stepEq 4 (by rfl) ⟨183, by rfl⟩ : syracuseStep 1957 = 367) R367
theorem R1973 : ∃ j : ℕ, syracuseStep^[j] 1973 = 1 := reachStep (stepEq 5 (by rfl) ⟨92, by rfl⟩ : syracuseStep 1973 = 185) R185
theorem R1983 : ∃ j : ℕ, syracuseStep^[j] 1983 = 1 := reachStep (stepEq 1 (by rfl) ⟨1487, by rfl⟩ : syracuseStep 1983 = 2975) R2975
theorem R1985 : ∃ j : ℕ, syracuseStep^[j] 1985 = 1 := reachStep (stepEq 2 (by rfl) ⟨744, by rfl⟩ : syracuseStep 1985 = 1489) R1489
theorem R1991 : ∃ j : ℕ, syracuseStep^[j] 1991 = 1 := reachStep (stepEq 1 (by rfl) ⟨1493, by rfl⟩ : syracuseStep 1991 = 2987) R2987
theorem R1993 : ∃ j : ℕ, syracuseStep^[j] 1993 = 1 := reachStep (stepEq 2 (by rfl) ⟨747, by rfl⟩ : syracuseStep 1993 = 1495) R1495
theorem R1995 : ∃ j : ℕ, syracuseStep^[j] 1995 = 1 := reachStep (stepEq 1 (by rfl) ⟨1496, by rfl⟩ : syracuseStep 1995 = 2993) R2993
theorem R1997 : ∃ j : ℕ, syracuseStep^[j] 1997 = 1 := reachStep (stepEq 3 (by rfl) ⟨374, by rfl⟩ : syracuseStep 1997 = 749) R749
theorem R1999 : ∃ j : ℕ, syracuseStep^[j] 1999 = 1 := reachStep (stepEq 1 (by rfl) ⟨1499, by rfl⟩ : syracuseStep 1999 = 2999) R2999
theorem R2001 : ∃ j : ℕ, syracuseStep^[j] 2001 = 1 := reachStep (stepEq 2 (by rfl) ⟨750, by rfl⟩ : syracuseStep 2001 = 1501) R1501
theorem R2037 : ∃ j : ℕ, syracuseStep^[j] 2037 = 1 := reachStep (stepEq 5 (by rfl) ⟨95, by rfl⟩ : syracuseStep 2037 = 191) R191
theorem R133123 : ∃ j : ℕ, syracuseStep^[j] 133123 = 1 := reachStep (stepEq 1 (by rfl) ⟨99842, by rfl⟩ : syracuseStep 133123 = 199685) R199685
theorem R2079 : ∃ j : ℕ, syracuseStep^[j] 2079 = 1 := reachStep (stepEq 1 (by rfl) ⟨1559, by rfl⟩ : syracuseStep 2079 = 3119) R3119
theorem R2157 : ∃ j : ℕ, syracuseStep^[j] 2157 = 1 := reachStep (stepEq 3 (by rfl) ⟨404, by rfl⟩ : syracuseStep 2157 = 809) R809
theorem R2171 : ∃ j : ℕ, syracuseStep^[j] 2171 = 1 := reachStep (stepEq 1 (by rfl) ⟨1628, by rfl⟩ : syracuseStep 2171 = 3257) R3257
theorem R2203 : ∃ j : ℕ, syracuseStep^[j] 2203 = 1 := reachStep (stepEq 1 (by rfl) ⟨1652, by rfl⟩ : syracuseStep 2203 = 3305) R3305
theorem R2377 : ∃ j : ℕ, syracuseStep^[j] 2377 = 1 := reachStep (stepEq 2 (by rfl) ⟨891, by rfl⟩ : syracuseStep 2377 = 1783) R1783
theorem R2383 : ∃ j : ℕ, syracuseStep^[j] 2383 = 1 := reachStep (stepEq 1 (by rfl) ⟨1787, by rfl⟩ : syracuseStep 2383 = 3575) R3575
theorem R35255 : ∃ j : ℕ, syracuseStep^[j] 35255 = 1 := reachStep (stepEq 1 (by rfl) ⟨26441, by rfl⟩ : syracuseStep 35255 = 52883) R52883
theorem R3845 : ∃ j : ℕ, syracuseStep^[j] 3845 = 1 := reachStep (stepEq 4 (by rfl) ⟨360, by rfl⟩ : syracuseStep 3845 = 721) R721
theorem R3853 : ∃ j : ℕ, syracuseStep^[j] 3853 = 1 := reachStep (stepEq 3 (by rfl) ⟨722, by rfl⟩ : syracuseStep 3853 = 1445) R1445
theorem R3855 : ∃ j : ℕ, syracuseStep^[j] 3855 = 1 := reachStep (stepEq 1 (by rfl) ⟨2891, by rfl⟩ : syracuseStep 3855 = 5783) R5783
theorem R3857 : ∃ j : ℕ, syracuseStep^[j] 3857 = 1 := reachStep (stepEq 2 (by rfl) ⟨1446, by rfl⟩ : syracuseStep 3857 = 2893) R2893
theorem R3873 : ∃ j : ℕ, syracuseStep^[j] 3873 = 1 := reachStep (stepEq 2 (by rfl) ⟨1452, by rfl⟩ : syracuseStep 3873 = 2905) R2905
theorem R3875 : ∃ j : ℕ, syracuseStep^[j] 3875 = 1 := reachStep (stepEq 1 (by rfl) ⟨2906, by rfl⟩ : syracuseStep 3875 = 5813) R5813
theorem R3877 : ∃ j : ℕ, syracuseStep^[j] 3877 = 1 := reachStep (stepEq 4 (by rfl) ⟨363, by rfl⟩ : syracuseStep 3877 = 727) R727
theorem R3883 : ∃ j : ℕ, syracuseStep^[j] 3883 = 1 := reachStep (stepEq 1 (by rfl) ⟨2912, by rfl⟩ : syracuseStep 3883 = 5825) R5825
theorem R3887 : ∃ j : ℕ, syracuseStep^[j] 3887 = 1 := reachStep (stepEq 1 (by rfl) ⟨2915, by rfl⟩ : syracuseStep 3887 = 5831) R5831
theorem R3917 : ∃ j : ℕ, syracuseStep^[j] 3917 = 1 := reachStep (stepEq 3 (by rfl) ⟨734, by rfl⟩ : syracuseStep 3917 = 1469) R1469
theorem R3921 : ∃ j : ℕ, syracuseStep^[j] 3921 = 1 := reachStep (stepEq 2 (by rfl) ⟨1470, by rfl⟩ : syracuseStep 3921 = 2941) R2941
theorem R3953 : ∃ j : ℕ, syracuseStep^[j] 3953 = 1 := reachStep (stepEq 2 (by rfl) ⟨1482, by rfl⟩ : syracuseStep 3953 = 2965) R2965
theorem R3957 : ∃ j : ℕ, syracuseStep^[j] 3957 = 1 := reachStep (stepEq 5 (by rfl) ⟨185, by rfl⟩ : syracuseStep 3957 = 371) R371
theorem R3961 : ∃ j : ℕ, syracuseStep^[j] 3961 = 1 := reachStep (stepEq 2 (by rfl) ⟨1485, by rfl⟩ : syracuseStep 3961 = 2971) R2971
theorem R3963 : ∃ j : ℕ, syracuseStep^[j] 3963 = 1 := reachStep (stepEq 1 (by rfl) ⟨2972, by rfl⟩ : syracuseStep 3963 = 5945) R5945
theorem R3967 : ∃ j : ℕ, syracuseStep^[j] 3967 = 1 := reachStep (stepEq 1 (by rfl) ⟨2975, by rfl⟩ : syracuseStep 3967 = 5951) R5951
theorem R3971 : ∃ j : ℕ, syracuseStep^[j] 3971 = 1 := reachStep (stepEq 1 (by rfl) ⟨2978, by rfl⟩ : syracuseStep 3971 = 5957) R5957
theorem R3975 : ∃ j : ℕ, syracuseStep^[j] 3975 = 1 := reachStep (stepEq 1 (by rfl) ⟨2981, by rfl⟩ : syracuseStep 3975 = 5963) R5963
theorem R3983 : ∃ j : ℕ, syracuseStep^[j] 3983 = 1 := reachStep (stepEq 1 (by rfl) ⟨2987, by rfl⟩ : syracuseStep 3983 = 5975) R5975
theorem R3985 : ∃ j : ℕ, syracuseStep^[j] 3985 = 1 := reachStep (stepEq 2 (by rfl) ⟨1494, by rfl⟩ : syracuseStep 3985 = 2989) R2989
theorem R3987 : ∃ j : ℕ, syracuseStep^[j] 3987 = 1 := reachStep (stepEq 1 (by rfl) ⟨2990, by rfl⟩ : syracuseStep 3987 = 5981) R5981
theorem R3989 : ∃ j : ℕ, syracuseStep^[j] 3989 = 1 := reachStep (stepEq 6 (by rfl) ⟨93, by rfl⟩ : syracuseStep 3989 = 187) R187
theorem R3991 : ∃ j : ℕ, syracuseStep^[j] 3991 = 1 := reachStep (stepEq 1 (by rfl) ⟨2993, by rfl⟩ : syracuseStep 3991 = 5987) R5987
theorem R3993 : ∃ j : ℕ, syracuseStep^[j] 3993 = 1 := reachStep (stepEq 2 (by rfl) ⟨1497, by rfl⟩ : syracuseStep 3993 = 2995) R2995
theorem R3997 : ∃ j : ℕ, syracuseStep^[j] 3997 = 1 := reachStep (stepEq 3 (by rfl) ⟨749, by rfl⟩ : syracuseStep 3997 = 1499) R1499
theorem R4003 : ∃ j : ℕ, syracuseStep^[j] 4003 = 1 := reachStep (stepEq 1 (by rfl) ⟨3002, by rfl⟩ : syracuseStep 4003 = 6005) R6005
theorem R4081 : ∃ j : ℕ, syracuseStep^[j] 4081 = 1 := reachStep (stepEq 2 (by rfl) ⟨1530, by rfl⟩ : syracuseStep 4081 = 3061) R3061
theorem R4085 : ∃ j : ℕ, syracuseStep^[j] 4085 = 1 := reachStep (stepEq 5 (by rfl) ⟨191, by rfl⟩ : syracuseStep 4085 = 383) R383
theorem R4159 : ∃ j : ℕ, syracuseStep^[j] 4159 = 1 := reachStep (stepEq 1 (by rfl) ⟨3119, by rfl⟩ : syracuseStep 4159 = 6239) R6239
theorem R4313 : ∃ j : ℕ, syracuseStep^[j] 4313 = 1 := reachStep (stepEq 2 (by rfl) ⟨1617, by rfl⟩ : syracuseStep 4313 = 3235) R3235
theorem R4317 : ∃ j : ℕ, syracuseStep^[j] 4317 = 1 := reachStep (stepEq 3 (by rfl) ⟨809, by rfl⟩ : syracuseStep 4317 = 1619) R1619
theorem R4329 : ∃ j : ℕ, syracuseStep^[j] 4329 = 1 := reachStep (stepEq 2 (by rfl) ⟨1623, by rfl⟩ : syracuseStep 4329 = 3247) R3247
theorem R4343 : ∃ j : ℕ, syracuseStep^[j] 4343 = 1 := reachStep (stepEq 1 (by rfl) ⟨3257, by rfl⟩ : syracuseStep 4343 = 6515) R6515
theorem R4345 : ∃ j : ℕ, syracuseStep^[j] 4345 = 1 := reachStep (stepEq 2 (by rfl) ⟨1629, by rfl⟩ : syracuseStep 4345 = 3259) R3259
theorem R4407 : ∃ j : ℕ, syracuseStep^[j] 4407 = 1 := reachStep (stepEq 1 (by rfl) ⟨3305, by rfl⟩ : syracuseStep 4407 = 6611) R6611
theorem R4745 : ∃ j : ℕ, syracuseStep^[j] 4745 = 1 := reachStep (stepEq 2 (by rfl) ⟨1779, by rfl⟩ : syracuseStep 4745 = 3559) R3559
theorem R4753 : ∃ j : ℕ, syracuseStep^[j] 4753 = 1 := reachStep (stepEq 2 (by rfl) ⟨1782, by rfl⟩ : syracuseStep 4753 = 3565) R3565
theorem R4755 : ∃ j : ℕ, syracuseStep^[j] 4755 = 1 := reachStep (stepEq 1 (by rfl) ⟨3566, by rfl⟩ : syracuseStep 4755 = 7133) R7133
theorem R4765 : ∃ j : ℕ, syracuseStep^[j] 4765 = 1 := reachStep (stepEq 3 (by rfl) ⟨893, by rfl⟩ : syracuseStep 4765 = 1787) R1787
theorem R7697 : ∃ j : ℕ, syracuseStep^[j] 7697 = 1 := reachStep (stepEq 2 (by rfl) ⟨2886, by rfl⟩ : syracuseStep 7697 = 5773) R5773
theorem R7709 : ∃ j : ℕ, syracuseStep^[j] 7709 = 1 := reachStep (stepEq 3 (by rfl) ⟨1445, by rfl⟩ : syracuseStep 7709 = 2891) R2891
theorem R7715 : ∃ j : ℕ, syracuseStep^[j] 7715 = 1 := reachStep (stepEq 1 (by rfl) ⟨5786, by rfl⟩ : syracuseStep 7715 = 11573) R11573
theorem R7723 : ∃ j : ℕ, syracuseStep^[j] 7723 = 1 := reachStep (stepEq 1 (by rfl) ⟨5792, by rfl⟩ : syracuseStep 7723 = 11585) R11585
theorem R7745 : ∃ j : ℕ, syracuseStep^[j] 7745 = 1 := reachStep (stepEq 2 (by rfl) ⟨2904, by rfl⟩ : syracuseStep 7745 = 5809) R5809
theorem R7757 : ∃ j : ℕ, syracuseStep^[j] 7757 = 1 := reachStep (stepEq 3 (by rfl) ⟨1454, by rfl⟩ : syracuseStep 7757 = 2909) R2909
theorem R7775 : ∃ j : ℕ, syracuseStep^[j] 7775 = 1 := reachStep (stepEq 1 (by rfl) ⟨5831, by rfl⟩ : syracuseStep 7775 = 11663) R11663
theorem R7829 : ∃ j : ℕ, syracuseStep^[j] 7829 = 1 := reachStep (stepEq 6 (by rfl) ⟨183, by rfl⟩ : syracuseStep 7829 = 367) R367
theorem R7841 : ∃ j : ℕ, syracuseStep^[j] 7841 = 1 := reachStep (stepEq 2 (by rfl) ⟨2940, by rfl⟩ : syracuseStep 7841 = 5881) R5881
theorem R7843 : ∃ j : ℕ, syracuseStep^[j] 7843 = 1 := reachStep (stepEq 1 (by rfl) ⟨5882, by rfl⟩ : syracuseStep 7843 = 11765) R11765
theorem R7865 : ∃ j : ℕ, syracuseStep^[j] 7865 = 1 := reachStep (stepEq 2 (by rfl) ⟨2949, by rfl⟩ : syracuseStep 7865 = 5899) R5899
theorem R7867 : ∃ j : ℕ, syracuseStep^[j] 7867 = 1 := reachStep (stepEq 1 (by rfl) ⟨5900, by rfl⟩ : syracuseStep 7867 = 11801) R11801
theorem R7907 : ∃ j : ℕ, syracuseStep^[j] 7907 = 1 := reachStep (stepEq 1 (by rfl) ⟨5930, by rfl⟩ : syracuseStep 7907 = 11861) R11861
theorem R7933 : ∃ j : ℕ, syracuseStep^[j] 7933 = 1 := reachStep (stepEq 3 (by rfl) ⟨1487, by rfl⟩ : syracuseStep 7933 = 2975) R2975
theorem R7937 : ∃ j : ℕ, syracuseStep^[j] 7937 = 1 := reachStep (stepEq 2 (by rfl) ⟨2976, by rfl⟩ : syracuseStep 7937 = 5953) R5953
theorem R7951 : ∃ j : ℕ, syracuseStep^[j] 7951 = 1 := reachStep (stepEq 1 (by rfl) ⟨5963, by rfl⟩ : syracuseStep 7951 = 11927) R11927
theorem R7973 : ∃ j : ℕ, syracuseStep^[j] 7973 = 1 := reachStep (stepEq 4 (by rfl) ⟨747, by rfl⟩ : syracuseStep 7973 = 1495) R1495
theorem R7979 : ∃ j : ℕ, syracuseStep^[j] 7979 = 1 := reachStep (stepEq 1 (by rfl) ⟨5984, by rfl⟩ : syracuseStep 7979 = 11969) R11969
theorem R7985 : ∃ j : ℕ, syracuseStep^[j] 7985 = 1 := reachStep (stepEq 2 (by rfl) ⟨2994, by rfl⟩ : syracuseStep 7985 = 5989) R5989
theorem R7997 : ∃ j : ℕ, syracuseStep^[j] 7997 = 1 := reachStep (stepEq 3 (by rfl) ⟨1499, by rfl⟩ : syracuseStep 7997 = 2999) R2999
theorem R8005 : ∃ j : ℕ, syracuseStep^[j] 8005 = 1 := reachStep (stepEq 4 (by rfl) ⟨750, by rfl⟩ : syracuseStep 8005 = 1501) R1501
theorem R8059 : ∃ j : ℕ, syracuseStep^[j] 8059 = 1 := reachStep (stepEq 1 (by rfl) ⟨6044, by rfl⟩ : syracuseStep 8059 = 12089) R12089
theorem R8177 : ∃ j : ℕ, syracuseStep^[j] 8177 = 1 := reachStep (stepEq 2 (by rfl) ⟨3066, by rfl⟩ : syracuseStep 8177 = 6133) R6133
theorem R8231 : ∃ j : ℕ, syracuseStep^[j] 8231 = 1 := reachStep (stepEq 1 (by rfl) ⟨6173, by rfl⟩ : syracuseStep 8231 = 12347) R12347
theorem R8321 : ∃ j : ℕ, syracuseStep^[j] 8321 = 1 := reachStep (stepEq 2 (by rfl) ⟨3120, by rfl⟩ : syracuseStep 8321 = 6241) R6241
theorem R8555 : ∃ j : ℕ, syracuseStep^[j] 8555 = 1 := reachStep (stepEq 1 (by rfl) ⟨6416, by rfl⟩ : syracuseStep 8555 = 12833) R12833
theorem R8627 : ∃ j : ℕ, syracuseStep^[j] 8627 = 1 := reachStep (stepEq 1 (by rfl) ⟨6470, by rfl⟩ : syracuseStep 8627 = 12941) R12941
theorem R8633 : ∃ j : ℕ, syracuseStep^[j] 8633 = 1 := reachStep (stepEq 2 (by rfl) ⟨3237, by rfl⟩ : syracuseStep 8633 = 6475) R6475
theorem R8651 : ∃ j : ℕ, syracuseStep^[j] 8651 = 1 := reachStep (stepEq 1 (by rfl) ⟨6488, by rfl⟩ : syracuseStep 8651 = 12977) R12977
theorem R8813 : ∃ j : ℕ, syracuseStep^[j] 8813 = 1 := reachStep (stepEq 3 (by rfl) ⟨1652, by rfl⟩ : syracuseStep 8813 = 3305) R3305
theorem R8815 : ∃ j : ℕ, syracuseStep^[j] 8815 = 1 := reachStep (stepEq 1 (by rfl) ⟨6611, by rfl⟩ : syracuseStep 8815 = 13223) R13223
theorem R8969 : ∃ j : ℕ, syracuseStep^[j] 8969 = 1 := reachStep (stepEq 2 (by rfl) ⟨3363, by rfl⟩ : syracuseStep 8969 = 6727) R6727
theorem R9491 : ∃ j : ℕ, syracuseStep^[j] 9491 = 1 := reachStep (stepEq 1 (by rfl) ⟨7118, by rfl⟩ : syracuseStep 9491 = 14237) R14237
theorem R9497 : ∃ j : ℕ, syracuseStep^[j] 9497 = 1 := reachStep (stepEq 2 (by rfl) ⟨3561, by rfl⟩ : syracuseStep 9497 = 7123) R7123
theorem R9509 : ∃ j : ℕ, syracuseStep^[j] 9509 = 1 := reachStep (stepEq 4 (by rfl) ⟨891, by rfl⟩ : syracuseStep 9509 = 1783) R1783
theorem R9515 : ∃ j : ℕ, syracuseStep^[j] 9515 = 1 := reachStep (stepEq 1 (by rfl) ⟨7136, by rfl⟩ : syracuseStep 9515 = 14273) R14273
theorem R9533 : ∃ j : ℕ, syracuseStep^[j] 9533 = 1 := reachStep (stepEq 3 (by rfl) ⟨1787, by rfl⟩ : syracuseStep 9533 = 3575) R3575
theorem R15491 : ∃ j : ℕ, syracuseStep^[j] 15491 = 1 := reachStep (stepEq 1 (by rfl) ⟨11618, by rfl⟩ : syracuseStep 15491 = 23237) R23237
theorem R15511 : ∃ j : ℕ, syracuseStep^[j] 15511 = 1 := reachStep (stepEq 1 (by rfl) ⟨11633, by rfl⟩ : syracuseStep 15511 = 23267) R23267
theorem R15875 : ∃ j : ℕ, syracuseStep^[j] 15875 = 1 := reachStep (stepEq 1 (by rfl) ⟨11906, by rfl⟩ : syracuseStep 15875 = 23813) R23813
theorem R15947 : ∃ j : ℕ, syracuseStep^[j] 15947 = 1 := reachStep (stepEq 1 (by rfl) ⟨11960, by rfl⟩ : syracuseStep 15947 = 23921) R23921
theorem R16463 : ∃ j : ℕ, syracuseStep^[j] 16463 = 1 := reachStep (stepEq 1 (by rfl) ⟨12347, by rfl⟩ : syracuseStep 16463 = 24695) R24695
theorem R19061 : ∃ j : ℕ, syracuseStep^[j] 19061 = 1 := reachStep (stepEq 5 (by rfl) ⟨893, by rfl⟩ : syracuseStep 19061 = 1787) R1787
theorem R31909 : ∃ j : ℕ, syracuseStep^[j] 31909 = 1 := reachStep (stepEq 4 (by rfl) ⟨2991, by rfl⟩ : syracuseStep 31909 = 5983) R5983
theorem R31985 : ∃ j : ℕ, syracuseStep^[j] 31985 = 1 := reachStep (stepEq 2 (by rfl) ⟨11994, by rfl⟩ : syracuseStep 31985 = 23989) R23989
theorem R32237 : ∃ j : ℕ, syracuseStep^[j] 32237 = 1 := reachStep (stepEq 3 (by rfl) ⟨6044, by rfl⟩ : syracuseStep 32237 = 12089) R12089
theorem R169 : ∃ j : ℕ, syracuseStep^[j] 169 = 1 := reachStep (stepEq 2 (by rfl) ⟨63, by rfl⟩ : syracuseStep 169 = 127) R127
theorem R329 : ∃ j : ℕ, syracuseStep^[j] 329 = 1 := reachStep (stepEq 2 (by rfl) ⟨123, by rfl⟩ : syracuseStep 329 = 247) R247
theorem R339 : ∃ j : ℕ, syracuseStep^[j] 339 = 1 := reachStep (stepEq 1 (by rfl) ⟨254, by rfl⟩ : syracuseStep 339 = 509) R509
theorem R359 : ∃ j : ℕ, syracuseStep^[j] 359 = 1 := reachStep (stepEq 1 (by rfl) ⟨269, by rfl⟩ : syracuseStep 359 = 539) R539
theorem R641 : ∃ j : ℕ, syracuseStep^[j] 641 = 1 := reachStep (stepEq 2 (by rfl) ⟨240, by rfl⟩ : syracuseStep 641 = 481) R481
theorem R657 : ∃ j : ℕ, syracuseStep^[j] 657 = 1 := reachStep (stepEq 2 (by rfl) ⟨246, by rfl⟩ : syracuseStep 657 = 493) R493
theorem R659 : ∃ j : ℕ, syracuseStep^[j] 659 = 1 := reachStep (stepEq 1 (by rfl) ⟨494, by rfl⟩ : syracuseStep 659 = 989) R989
theorem R665 : ∃ j : ℕ, syracuseStep^[j] 665 = 1 := reachStep (stepEq 2 (by rfl) ⟨249, by rfl⟩ : syracuseStep 665 = 499) R499
theorem R677 : ∃ j : ℕ, syracuseStep^[j] 677 = 1 := reachStep (stepEq 4 (by rfl) ⟨63, by rfl⟩ : syracuseStep 677 = 127) R127
theorem R719 : ∃ j : ℕ, syracuseStep^[j] 719 = 1 := reachStep (stepEq 1 (by rfl) ⟨539, by rfl⟩ : syracuseStep 719 = 1079) R1079
theorem R1281 : ∃ j : ℕ, syracuseStep^[j] 1281 = 1 := reachStep (stepEq 2 (by rfl) ⟨480, by rfl⟩ : syracuseStep 1281 = 961) R961
theorem R1283 : ∃ j : ℕ, syracuseStep^[j] 1283 = 1 := reachStep (stepEq 1 (by rfl) ⟨962, by rfl⟩ : syracuseStep 1283 = 1925) R1925
theorem R1291 : ∃ j : ℕ, syracuseStep^[j] 1291 = 1 := reachStep (stepEq 1 (by rfl) ⟨968, by rfl⟩ : syracuseStep 1291 = 1937) R1937
theorem R1305 : ∃ j : ℕ, syracuseStep^[j] 1305 = 1 := reachStep (stepEq 2 (by rfl) ⟨489, by rfl⟩ : syracuseStep 1305 = 979) R979
theorem R1315 : ∃ j : ℕ, syracuseStep^[j] 1315 = 1 := reachStep (stepEq 1 (by rfl) ⟨986, by rfl⟩ : syracuseStep 1315 = 1973) R1973
theorem R1317 : ∃ j : ℕ, syracuseStep^[j] 1317 = 1 := reachStep (stepEq 4 (by rfl) ⟨123, by rfl⟩ : syracuseStep 1317 = 247) R247
theorem R1323 : ∃ j : ℕ, syracuseStep^[j] 1323 = 1 := reachStep (stepEq 1 (by rfl) ⟨992, by rfl⟩ : syracuseStep 1323 = 1985) R1985
theorem R1327 : ∃ j : ℕ, syracuseStep^[j] 1327 = 1 := reachStep (stepEq 1 (by rfl) ⟨995, by rfl⟩ : syracuseStep 1327 = 1991) R1991
theorem R1329 : ∃ j : ℕ, syracuseStep^[j] 1329 = 1 := reachStep (stepEq 2 (by rfl) ⟨498, by rfl⟩ : syracuseStep 1329 = 997) R997
theorem R1331 : ∃ j : ℕ, syracuseStep^[j] 1331 = 1 := reachStep (stepEq 1 (by rfl) ⟨998, by rfl⟩ : syracuseStep 1331 = 1997) R1997
theorem R1357 : ∃ j : ℕ, syracuseStep^[j] 1357 = 1 := reachStep (stepEq 3 (by rfl) ⟨254, by rfl⟩ : syracuseStep 1357 = 509) R509
theorem R1361 : ∃ j : ℕ, syracuseStep^[j] 1361 = 1 := reachStep (stepEq 2 (by rfl) ⟨510, by rfl⟩ : syracuseStep 1361 = 1021) R1021
theorem R1437 : ∃ j : ℕ, syracuseStep^[j] 1437 = 1 := reachStep (stepEq 3 (by rfl) ⟨269, by rfl⟩ : syracuseStep 1437 = 539) R539
theorem R1447 : ∃ j : ℕ, syracuseStep^[j] 1447 = 1 := reachStep (stepEq 1 (by rfl) ⟨1085, by rfl⟩ : syracuseStep 1447 = 2171) R2171
theorem R2563 : ∃ j : ℕ, syracuseStep^[j] 2563 = 1 := reachStep (stepEq 1 (by rfl) ⟨1922, by rfl⟩ : syracuseStep 2563 = 3845) R3845
theorem R2565 : ∃ j : ℕ, syracuseStep^[j] 2565 = 1 := reachStep (stepEq 4 (by rfl) ⟨240, by rfl⟩ : syracuseStep 2565 = 481) R481
theorem R2569 : ∃ j : ℕ, syracuseStep^[j] 2569 = 1 := reachStep (stepEq 2 (by rfl) ⟨963, by rfl⟩ : syracuseStep 2569 = 1927) R1927
theorem R2571 : ∃ j : ℕ, syracuseStep^[j] 2571 = 1 := reachStep (stepEq 1 (by rfl) ⟨1928, by rfl⟩ : syracuseStep 2571 = 3857) R3857
theorem R2583 : ∃ j : ℕ, syracuseStep^[j] 2583 = 1 := reachStep (stepEq 1 (by rfl) ⟨1937, by rfl⟩ : syracuseStep 2583 = 3875) R3875
theorem R2585 : ∃ j : ℕ, syracuseStep^[j] 2585 = 1 := reachStep (stepEq 2 (by rfl) ⟨969, by rfl⟩ : syracuseStep 2585 = 1939) R1939
theorem R2591 : ∃ j : ℕ, syracuseStep^[j] 2591 = 1 := reachStep (stepEq 1 (by rfl) ⟨1943, by rfl⟩ : syracuseStep 2591 = 3887) R3887
theorem R2609 : ∃ j : ℕ, syracuseStep^[j] 2609 = 1 := reachStep (stepEq 2 (by rfl) ⟨978, by rfl⟩ : syracuseStep 2609 = 1957) R1957
theorem R2611 : ∃ j : ℕ, syracuseStep^[j] 2611 = 1 := reachStep (stepEq 1 (by rfl) ⟨1958, by rfl⟩ : syracuseStep 2611 = 3917) R3917
theorem R2629 : ∃ j : ℕ, syracuseStep^[j] 2629 = 1 := reachStep (stepEq 4 (by rfl) ⟨246, by rfl⟩ : syracuseStep 2629 = 493) R493
theorem R2635 : ∃ j : ℕ, syracuseStep^[j] 2635 = 1 := reachStep (stepEq 1 (by rfl) ⟨1976, by rfl⟩ : syracuseStep 2635 = 3953) R3953
theorem R2637 : ∃ j : ℕ, syracuseStep^[j] 2637 = 1 := reachStep (stepEq 3 (by rfl) ⟨494, by rfl⟩ : syracuseStep 2637 = 989) R989
theorem R2647 : ∃ j : ℕ, syracuseStep^[j] 2647 = 1 := reachStep (stepEq 1 (by rfl) ⟨1985, by rfl⟩ : syracuseStep 2647 = 3971) R3971
theorem R2655 : ∃ j : ℕ, syracuseStep^[j] 2655 = 1 := reachStep (stepEq 1 (by rfl) ⟨1991, by rfl⟩ : syracuseStep 2655 = 3983) R3983
theorem R2657 : ∃ j : ℕ, syracuseStep^[j] 2657 = 1 := reachStep (stepEq 2 (by rfl) ⟨996, by rfl⟩ : syracuseStep 2657 = 1993) R1993
theorem R2659 : ∃ j : ℕ, syracuseStep^[j] 2659 = 1 := reachStep (stepEq 1 (by rfl) ⟨1994, by rfl⟩ : syracuseStep 2659 = 3989) R3989
theorem R2661 : ∃ j : ℕ, syracuseStep^[j] 2661 = 1 := reachStep (stepEq 4 (by rfl) ⟨249, by rfl⟩ : syracuseStep 2661 = 499) R499
theorem R2665 : ∃ j : ℕ, syracuseStep^[j] 2665 = 1 := reachStep (stepEq 2 (by rfl) ⟨999, by rfl⟩ : syracuseStep 2665 = 1999) R1999
theorem R2709 : ∃ j : ℕ, syracuseStep^[j] 2709 = 1 := reachStep (stepEq 6 (by rfl) ⟨63, by rfl⟩ : syracuseStep 2709 = 127) R127
theorem R2723 : ∃ j : ℕ, syracuseStep^[j] 2723 = 1 := reachStep (stepEq 1 (by rfl) ⟨2042, by rfl⟩ : syracuseStep 2723 = 4085) R4085
theorem R2875 : ∃ j : ℕ, syracuseStep^[j] 2875 = 1 := reachStep (stepEq 1 (by rfl) ⟨2156, by rfl⟩ : syracuseStep 2875 = 4313) R4313
theorem R2877 : ∃ j : ℕ, syracuseStep^[j] 2877 = 1 := reachStep (stepEq 3 (by rfl) ⟨539, by rfl⟩ : syracuseStep 2877 = 1079) R1079
theorem R2895 : ∃ j : ℕ, syracuseStep^[j] 2895 = 1 := reachStep (stepEq 1 (by rfl) ⟨2171, by rfl⟩ : syracuseStep 2895 = 4343) R4343
theorem R2937 : ∃ j : ℕ, syracuseStep^[j] 2937 = 1 := reachStep (stepEq 2 (by rfl) ⟨1101, by rfl⟩ : syracuseStep 2937 = 2203) R2203
theorem R3163 : ∃ j : ℕ, syracuseStep^[j] 3163 = 1 := reachStep (stepEq 1 (by rfl) ⟨2372, by rfl⟩ : syracuseStep 3163 = 4745) R4745
theorem R3169 : ∃ j : ℕ, syracuseStep^[j] 3169 = 1 := reachStep (stepEq 2 (by rfl) ⟨1188, by rfl⟩ : syracuseStep 3169 = 2377) R2377
theorem R3177 : ∃ j : ℕ, syracuseStep^[j] 3177 = 1 := reachStep (stepEq 2 (by rfl) ⟨1191, by rfl⟩ : syracuseStep 3177 = 2383) R2383
theorem R5125 : ∃ j : ℕ, syracuseStep^[j] 5125 = 1 := reachStep (stepEq 4 (by rfl) ⟨480, by rfl⟩ : syracuseStep 5125 = 961) R961
theorem R5131 : ∃ j : ℕ, syracuseStep^[j] 5131 = 1 := reachStep (stepEq 1 (by rfl) ⟨3848, by rfl⟩ : syracuseStep 5131 = 7697) R7697
theorem R5133 : ∃ j : ℕ, syracuseStep^[j] 5133 = 1 := reachStep (stepEq 3 (by rfl) ⟨962, by rfl⟩ : syracuseStep 5133 = 1925) R1925
theorem R5137 : ∃ j : ℕ, syracuseStep^[j] 5137 = 1 := reachStep (stepEq 2 (by rfl) ⟨1926, by rfl⟩ : syracuseStep 5137 = 3853) R3853
theorem R5139 : ∃ j : ℕ, syracuseStep^[j] 5139 = 1 := reachStep (stepEq 1 (by rfl) ⟨3854, by rfl⟩ : syracuseStep 5139 = 7709) R7709
theorem R5143 : ∃ j : ℕ, syracuseStep^[j] 5143 = 1 := reachStep (stepEq 1 (by rfl) ⟨3857, by rfl⟩ : syracuseStep 5143 = 7715) R7715
theorem R5163 : ∃ j : ℕ, syracuseStep^[j] 5163 = 1 := reachStep (stepEq 1 (by rfl) ⟨3872, by rfl⟩ : syracuseStep 5163 = 7745) R7745
theorem R5165 : ∃ j : ℕ, syracuseStep^[j] 5165 = 1 := reachStep (stepEq 3 (by rfl) ⟨968, by rfl⟩ : syracuseStep 5165 = 1937) R1937
theorem R5169 : ∃ j : ℕ, syracuseStep^[j] 5169 = 1 := reachStep (stepEq 2 (by rfl) ⟨1938, by rfl⟩ : syracuseStep 5169 = 3877) R3877
theorem R5171 : ∃ j : ℕ, syracuseStep^[j] 5171 = 1 := reachStep (stepEq 1 (by rfl) ⟨3878, by rfl⟩ : syracuseStep 5171 = 7757) R7757
theorem R5177 : ∃ j : ℕ, syracuseStep^[j] 5177 = 1 := reachStep (stepEq 2 (by rfl) ⟨1941, by rfl⟩ : syracuseStep 5177 = 3883) R3883
theorem R5183 : ∃ j : ℕ, syracuseStep^[j] 5183 = 1 := reachStep (stepEq 1 (by rfl) ⟨3887, by rfl⟩ : syracuseStep 5183 = 7775) R7775
theorem R5219 : ∃ j : ℕ, syracuseStep^[j] 5219 = 1 := reachStep (stepEq 1 (by rfl) ⟨3914, by rfl⟩ : syracuseStep 5219 = 7829) R7829
theorem R5221 : ∃ j : ℕ, syracuseStep^[j] 5221 = 1 := reachStep (stepEq 4 (by rfl) ⟨489, by rfl⟩ : syracuseStep 5221 = 979) R979
theorem R5227 : ∃ j : ℕ, syracuseStep^[j] 5227 = 1 := reachStep (stepEq 1 (by rfl) ⟨3920, by rfl⟩ : syracuseStep 5227 = 7841) R7841
theorem R5243 : ∃ j : ℕ, syracuseStep^[j] 5243 = 1 := reachStep (stepEq 1 (by rfl) ⟨3932, by rfl⟩ : syracuseStep 5243 = 7865) R7865
theorem R5261 : ∃ j : ℕ, syracuseStep^[j] 5261 = 1 := reachStep (stepEq 3 (by rfl) ⟨986, by rfl⟩ : syracuseStep 5261 = 1973) R1973
theorem R5269 : ∃ j : ℕ, syracuseStep^[j] 5269 = 1 := reachStep (stepEq 6 (by rfl) ⟨123, by rfl⟩ : syracuseStep 5269 = 247) R247
theorem R5271 : ∃ j : ℕ, syracuseStep^[j] 5271 = 1 := reachStep (stepEq 1 (by rfl) ⟨3953, by rfl⟩ : syracuseStep 5271 = 7907) R7907
theorem R5281 : ∃ j : ℕ, syracuseStep^[j] 5281 = 1 := reachStep (stepEq 2 (by rfl) ⟨1980, by rfl⟩ : syracuseStep 5281 = 3961) R3961
theorem R5289 : ∃ j : ℕ, syracuseStep^[j] 5289 = 1 := reachStep (stepEq 2 (by rfl) ⟨1983, by rfl⟩ : syracuseStep 5289 = 3967) R3967
theorem R5291 : ∃ j : ℕ, syracuseStep^[j] 5291 = 1 := reachStep (stepEq 1 (by rfl) ⟨3968, by rfl⟩ : syracuseStep 5291 = 7937) R7937
theorem R5293 : ∃ j : ℕ, syracuseStep^[j] 5293 = 1 := reachStep (stepEq 3 (by rfl) ⟨992, by rfl⟩ : syracuseStep 5293 = 1985) R1985
theorem R5309 : ∃ j : ℕ, syracuseStep^[j] 5309 = 1 := reachStep (stepEq 3 (by rfl) ⟨995, by rfl⟩ : syracuseStep 5309 = 1991) R1991
theorem R5313 : ∃ j : ℕ, syracuseStep^[j] 5313 = 1 := reachStep (stepEq 2 (by rfl) ⟨1992, by rfl⟩ : syracuseStep 5313 = 3985) R3985
theorem R5315 : ∃ j : ℕ, syracuseStep^[j] 5315 = 1 := reachStep (stepEq 1 (by rfl) ⟨3986, by rfl⟩ : syracuseStep 5315 = 7973) R7973
theorem R5317 : ∃ j : ℕ, syracuseStep^[j] 5317 = 1 := reachStep (stepEq 4 (by rfl) ⟨498, by rfl⟩ : syracuseStep 5317 = 997) R997
theorem R5319 : ∃ j : ℕ, syracuseStep^[j] 5319 = 1 := reachStep (stepEq 1 (by rfl) ⟨3989, by rfl⟩ : syracuseStep 5319 = 7979) R7979
theorem R5321 : ∃ j : ℕ, syracuseStep^[j] 5321 = 1 := reachStep (stepEq 2 (by rfl) ⟨1995, by rfl⟩ : syracuseStep 5321 = 3991) R3991
theorem R5323 : ∃ j : ℕ, syracuseStep^[j] 5323 = 1 := reachStep (stepEq 1 (by rfl) ⟨3992, by rfl⟩ : syracuseStep 5323 = 7985) R7985
theorem R5325 : ∃ j : ℕ, syracuseStep^[j] 5325 = 1 := reachStep (stepEq 3 (by rfl) ⟨998, by rfl⟩ : syracuseStep 5325 = 1997) R1997
theorem R5329 : ∃ j : ℕ, syracuseStep^[j] 5329 = 1 := reachStep (stepEq 2 (by rfl) ⟨1998, by rfl⟩ : syracuseStep 5329 = 3997) R3997
theorem R5331 : ∃ j : ℕ, syracuseStep^[j] 5331 = 1 := reachStep (stepEq 1 (by rfl) ⟨3998, by rfl⟩ : syracuseStep 5331 = 7997) R7997
theorem R5337 : ∃ j : ℕ, syracuseStep^[j] 5337 = 1 := reachStep (stepEq 2 (by rfl) ⟨2001, by rfl⟩ : syracuseStep 5337 = 4003) R4003
theorem R5429 : ∃ j : ℕ, syracuseStep^[j] 5429 = 1 := reachStep (stepEq 5 (by rfl) ⟨254, by rfl⟩ : syracuseStep 5429 = 509) R509
theorem R5441 : ∃ j : ℕ, syracuseStep^[j] 5441 = 1 := reachStep (stepEq 2 (by rfl) ⟨2040, by rfl⟩ : syracuseStep 5441 = 4081) R4081
theorem R5445 : ∃ j : ℕ, syracuseStep^[j] 5445 = 1 := reachStep (stepEq 4 (by rfl) ⟨510, by rfl⟩ : syracuseStep 5445 = 1021) R1021
theorem R5451 : ∃ j : ℕ, syracuseStep^[j] 5451 = 1 := reachStep (stepEq 1 (by rfl) ⟨4088, by rfl⟩ : syracuseStep 5451 = 8177) R8177
theorem R5487 : ∃ j : ℕ, syracuseStep^[j] 5487 = 1 := reachStep (stepEq 1 (by rfl) ⟨4115, by rfl⟩ : syracuseStep 5487 = 8231) R8231
theorem R5545 : ∃ j : ℕ, syracuseStep^[j] 5545 = 1 := reachStep (stepEq 2 (by rfl) ⟨2079, by rfl⟩ : syracuseStep 5545 = 4159) R4159
theorem R5547 : ∃ j : ℕ, syracuseStep^[j] 5547 = 1 := reachStep (stepEq 1 (by rfl) ⟨4160, by rfl⟩ : syracuseStep 5547 = 8321) R8321
theorem R5703 : ∃ j : ℕ, syracuseStep^[j] 5703 = 1 := reachStep (stepEq 1 (by rfl) ⟨4277, by rfl⟩ : syracuseStep 5703 = 8555) R8555
theorem R5749 : ∃ j : ℕ, syracuseStep^[j] 5749 = 1 := reachStep (stepEq 5 (by rfl) ⟨269, by rfl⟩ : syracuseStep 5749 = 539) R539
theorem R5751 : ∃ j : ℕ, syracuseStep^[j] 5751 = 1 := reachStep (stepEq 1 (by rfl) ⟨4313, by rfl⟩ : syracuseStep 5751 = 8627) R8627
theorem R5755 : ∃ j : ℕ, syracuseStep^[j] 5755 = 1 := reachStep (stepEq 1 (by rfl) ⟨4316, by rfl⟩ : syracuseStep 5755 = 8633) R8633
theorem R5767 : ∃ j : ℕ, syracuseStep^[j] 5767 = 1 := reachStep (stepEq 1 (by rfl) ⟨4325, by rfl⟩ : syracuseStep 5767 = 8651) R8651
theorem R5789 : ∃ j : ℕ, syracuseStep^[j] 5789 = 1 := reachStep (stepEq 3 (by rfl) ⟨1085, by rfl⟩ : syracuseStep 5789 = 2171) R2171
theorem R5793 : ∃ j : ℕ, syracuseStep^[j] 5793 = 1 := reachStep (stepEq 2 (by rfl) ⟨2172, by rfl⟩ : syracuseStep 5793 = 4345) R4345
theorem R5875 : ∃ j : ℕ, syracuseStep^[j] 5875 = 1 := reachStep (stepEq 1 (by rfl) ⟨4406, by rfl⟩ : syracuseStep 5875 = 8813) R8813
theorem R5979 : ∃ j : ℕ, syracuseStep^[j] 5979 = 1 := reachStep (stepEq 1 (by rfl) ⟨4484, by rfl⟩ : syracuseStep 5979 = 8969) R8969
theorem R6327 : ∃ j : ℕ, syracuseStep^[j] 6327 = 1 := reachStep (stepEq 1 (by rfl) ⟨4745, by rfl⟩ : syracuseStep 6327 = 9491) R9491
theorem R6331 : ∃ j : ℕ, syracuseStep^[j] 6331 = 1 := reachStep (stepEq 1 (by rfl) ⟨4748, by rfl⟩ : syracuseStep 6331 = 9497) R9497
theorem R6337 : ∃ j : ℕ, syracuseStep^[j] 6337 = 1 := reachStep (stepEq 2 (by rfl) ⟨2376, by rfl⟩ : syracuseStep 6337 = 4753) R4753
theorem R6339 : ∃ j : ℕ, syracuseStep^[j] 6339 = 1 := reachStep (stepEq 1 (by rfl) ⟨4754, by rfl⟩ : syracuseStep 6339 = 9509) R9509
theorem R6343 : ∃ j : ℕ, syracuseStep^[j] 6343 = 1 := reachStep (stepEq 1 (by rfl) ⟨4757, by rfl⟩ : syracuseStep 6343 = 9515) R9515
theorem R6353 : ∃ j : ℕ, syracuseStep^[j] 6353 = 1 := reachStep (stepEq 2 (by rfl) ⟨2382, by rfl⟩ : syracuseStep 6353 = 4765) R4765
theorem R6355 : ∃ j : ℕ, syracuseStep^[j] 6355 = 1 := reachStep (stepEq 1 (by rfl) ⟨4766, by rfl⟩ : syracuseStep 6355 = 9533) R9533
theorem R41309 : ∃ j : ℕ, syracuseStep^[j] 41309 = 1 := reachStep (stepEq 3 (by rfl) ⟨7745, by rfl⟩ : syracuseStep 41309 = 15491) R15491
theorem R42545 : ∃ j : ℕ, syracuseStep^[j] 42545 = 1 := reachStep (stepEq 2 (by rfl) ⟨15954, by rfl⟩ : syracuseStep 42545 = 31909) R31909
theorem R10253 : ∃ j : ℕ, syracuseStep^[j] 10253 = 1 := reachStep (stepEq 3 (by rfl) ⟨1922, by rfl⟩ : syracuseStep 10253 = 3845) R3845
theorem R10277 : ∃ j : ℕ, syracuseStep^[j] 10277 = 1 := reachStep (stepEq 4 (by rfl) ⟨963, by rfl⟩ : syracuseStep 10277 = 1927) R1927
theorem R10297 : ∃ j : ℕ, syracuseStep^[j] 10297 = 1 := reachStep (stepEq 2 (by rfl) ⟨3861, by rfl⟩ : syracuseStep 10297 = 7723) R7723
theorem R10327 : ∃ j : ℕ, syracuseStep^[j] 10327 = 1 := reachStep (stepEq 1 (by rfl) ⟨7745, by rfl⟩ : syracuseStep 10327 = 15491) R15491
theorem R10457 : ∃ j : ℕ, syracuseStep^[j] 10457 = 1 := reachStep (stepEq 2 (by rfl) ⟨3921, by rfl⟩ : syracuseStep 10457 = 7843) R7843
theorem R10489 : ∃ j : ℕ, syracuseStep^[j] 10489 = 1 := reachStep (stepEq 2 (by rfl) ⟨3933, by rfl⟩ : syracuseStep 10489 = 7867) R7867
theorem R10577 : ∃ j : ℕ, syracuseStep^[j] 10577 = 1 := reachStep (stepEq 2 (by rfl) ⟨3966, by rfl⟩ : syracuseStep 10577 = 7933) R7933
theorem R10583 : ∃ j : ℕ, syracuseStep^[j] 10583 = 1 := reachStep (stepEq 1 (by rfl) ⟨7937, by rfl⟩ : syracuseStep 10583 = 15875) R15875
theorem R10601 : ∃ j : ℕ, syracuseStep^[j] 10601 = 1 := reachStep (stepEq 2 (by rfl) ⟨3975, by rfl⟩ : syracuseStep 10601 = 7951) R7951
theorem R10631 : ∃ j : ℕ, syracuseStep^[j] 10631 = 1 := reachStep (stepEq 1 (by rfl) ⟨7973, by rfl⟩ : syracuseStep 10631 = 15947) R15947
theorem R10637 : ∃ j : ℕ, syracuseStep^[j] 10637 = 1 := reachStep (stepEq 3 (by rfl) ⟨1994, by rfl⟩ : syracuseStep 10637 = 3989) R3989
theorem R10673 : ∃ j : ℕ, syracuseStep^[j] 10673 = 1 := reachStep (stepEq 2 (by rfl) ⟨4002, by rfl⟩ : syracuseStep 10673 = 8005) R8005
theorem R10745 : ∃ j : ℕ, syracuseStep^[j] 10745 = 1 := reachStep (stepEq 2 (by rfl) ⟨4029, by rfl⟩ : syracuseStep 10745 = 8059) R8059
theorem R10975 : ∃ j : ℕ, syracuseStep^[j] 10975 = 1 := reachStep (stepEq 1 (by rfl) ⟨8231, by rfl⟩ : syracuseStep 10975 = 16463) R16463
theorem R11501 : ∃ j : ℕ, syracuseStep^[j] 11501 = 1 := reachStep (stepEq 3 (by rfl) ⟨2156, by rfl⟩ : syracuseStep 11501 = 4313) R4313
theorem R11753 : ∃ j : ℕ, syracuseStep^[j] 11753 = 1 := reachStep (stepEq 2 (by rfl) ⟨4407, by rfl⟩ : syracuseStep 11753 = 8815) R8815
theorem R12653 : ∃ j : ℕ, syracuseStep^[j] 12653 = 1 := reachStep (stepEq 3 (by rfl) ⟨2372, by rfl⟩ : syracuseStep 12653 = 4745) R4745
theorem R12707 : ∃ j : ℕ, syracuseStep^[j] 12707 = 1 := reachStep (stepEq 1 (by rfl) ⟨9530, by rfl⟩ : syracuseStep 12707 = 19061) R19061
theorem R46169 : ∃ j : ℕ, syracuseStep^[j] 46169 = 1 := reachStep (stepEq 2 (by rfl) ⟨17313, by rfl⟩ : syracuseStep 46169 = 34627) R34627
theorem R177497 : ∃ j : ℕ, syracuseStep^[j] 177497 = 1 := reachStep (stepEq 2 (by rfl) ⟨66561, by rfl⟩ : syracuseStep 177497 = 133123) R133123
theorem R20501 : ∃ j : ℕ, syracuseStep^[j] 20501 = 1 := reachStep (stepEq 6 (by rfl) ⟨480, by rfl⟩ : syracuseStep 20501 = 961) R961
theorem R20533 : ∃ j : ℕ, syracuseStep^[j] 20533 = 1 := reachStep (stepEq 5 (by rfl) ⟨962, by rfl⟩ : syracuseStep 20533 = 1925) R1925
theorem R20573 : ∃ j : ℕ, syracuseStep^[j] 20573 = 1 := reachStep (stepEq 3 (by rfl) ⟨3857, by rfl⟩ : syracuseStep 20573 = 7715) R7715
theorem R20681 : ∃ j : ℕ, syracuseStep^[j] 20681 = 1 := reachStep (stepEq 2 (by rfl) ⟨7755, by rfl⟩ : syracuseStep 20681 = 15511) R15511
theorem R21293 : ∃ j : ℕ, syracuseStep^[j] 21293 = 1 := reachStep (stepEq 3 (by rfl) ⟨3992, by rfl⟩ : syracuseStep 21293 = 7985) R7985
theorem R21323 : ∃ j : ℕ, syracuseStep^[j] 21323 = 1 := reachStep (stepEq 1 (by rfl) ⟨15992, by rfl⟩ : syracuseStep 21323 = 31985) R31985
theorem R21491 : ∃ j : ℕ, syracuseStep^[j] 21491 = 1 := reachStep (stepEq 1 (by rfl) ⟨16118, by rfl⟩ : syracuseStep 21491 = 32237) R32237
theorem R23503 : ∃ j : ℕ, syracuseStep^[j] 23503 = 1 := reachStep (stepEq 1 (by rfl) ⟨17627, by rfl⟩ : syracuseStep 23503 = 35255) R35255
theorem R25373 : ∃ j : ℕ, syracuseStep^[j] 25373 = 1 := reachStep (stepEq 3 (by rfl) ⟨4757, by rfl⟩ : syracuseStep 25373 = 9515) R9515
theorem R219 : ∃ j : ℕ, syracuseStep^[j] 219 = 1 := reachStep (stepEq 1 (by rfl) ⟨164, by rfl⟩ : syracuseStep 219 = 329) R329
theorem R225 : ∃ j : ℕ, syracuseStep^[j] 225 = 1 := reachStep (stepEq 2 (by rfl) ⟨84, by rfl⟩ : syracuseStep 225 = 169) R169
theorem R239 : ∃ j : ℕ, syracuseStep^[j] 239 = 1 := reachStep (stepEq 1 (by rfl) ⟨179, by rfl⟩ : syracuseStep 239 = 359) R359
theorem R427 : ∃ j : ℕ, syracuseStep^[j] 427 = 1 := reachStep (stepEq 1 (by rfl) ⟨320, by rfl⟩ : syracuseStep 427 = 641) R641
theorem R439 : ∃ j : ℕ, syracuseStep^[j] 439 = 1 := reachStep (stepEq 1 (by rfl) ⟨329, by rfl⟩ : syracuseStep 439 = 659) R659
theorem R443 : ∃ j : ℕ, syracuseStep^[j] 443 = 1 := reachStep (stepEq 1 (by rfl) ⟨332, by rfl⟩ : syracuseStep 443 = 665) R665
theorem R451 : ∃ j : ℕ, syracuseStep^[j] 451 = 1 := reachStep (stepEq 1 (by rfl) ⟨338, by rfl⟩ : syracuseStep 451 = 677) R677
theorem R479 : ∃ j : ℕ, syracuseStep^[j] 479 = 1 := reachStep (stepEq 1 (by rfl) ⟨359, by rfl⟩ : syracuseStep 479 = 719) R719
theorem R855 : ∃ j : ℕ, syracuseStep^[j] 855 = 1 := reachStep (stepEq 1 (by rfl) ⟨641, by rfl⟩ : syracuseStep 855 = 1283) R1283
theorem R877 : ∃ j : ℕ, syracuseStep^[j] 877 = 1 := reachStep (stepEq 3 (by rfl) ⟨164, by rfl⟩ : syracuseStep 877 = 329) R329
theorem R887 : ∃ j : ℕ, syracuseStep^[j] 887 = 1 := reachStep (stepEq 1 (by rfl) ⟨665, by rfl⟩ : syracuseStep 887 = 1331) R1331
theorem R901 : ∃ j : ℕ, syracuseStep^[j] 901 = 1 := reachStep (stepEq 4 (by rfl) ⟨84, by rfl⟩ : syracuseStep 901 = 169) R169
theorem R907 : ∃ j : ℕ, syracuseStep^[j] 907 = 1 := reachStep (stepEq 1 (by rfl) ⟨680, by rfl⟩ : syracuseStep 907 = 1361) R1361
theorem R957 : ∃ j : ℕ, syracuseStep^[j] 957 = 1 := reachStep (stepEq 3 (by rfl) ⟨179, by rfl⟩ : syracuseStep 957 = 359) R359
theorem R1709 : ∃ j : ℕ, syracuseStep^[j] 1709 = 1 := reachStep (stepEq 3 (by rfl) ⟨320, by rfl⟩ : syracuseStep 1709 = 641) R641
theorem R1721 : ∃ j : ℕ, syracuseStep^[j] 1721 = 1 := reachStep (stepEq 2 (by rfl) ⟨645, by rfl⟩ : syracuseStep 1721 = 1291) R1291
theorem R1723 : ∃ j : ℕ, syracuseStep^[j] 1723 = 1 := reachStep (stepEq 1 (by rfl) ⟨1292, by rfl⟩ : syracuseStep 1723 = 2585) R2585
theorem R1727 : ∃ j : ℕ, syracuseStep^[j] 1727 = 1 := reachStep (stepEq 1 (by rfl) ⟨1295, by rfl⟩ : syracuseStep 1727 = 2591) R2591
theorem R1739 : ∃ j : ℕ, syracuseStep^[j] 1739 = 1 := reachStep (stepEq 1 (by rfl) ⟨1304, by rfl⟩ : syracuseStep 1739 = 2609) R2609
theorem R1753 : ∃ j : ℕ, syracuseStep^[j] 1753 = 1 := reachStep (stepEq 2 (by rfl) ⟨657, by rfl⟩ : syracuseStep 1753 = 1315) R1315
theorem R1757 : ∃ j : ℕ, syracuseStep^[j] 1757 = 1 := reachStep (stepEq 3 (by rfl) ⟨329, by rfl⟩ : syracuseStep 1757 = 659) R659
theorem R1769 : ∃ j : ℕ, syracuseStep^[j] 1769 = 1 := reachStep (stepEq 2 (by rfl) ⟨663, by rfl⟩ : syracuseStep 1769 = 1327) R1327
theorem R1771 : ∃ j : ℕ, syracuseStep^[j] 1771 = 1 := reachStep (stepEq 1 (by rfl) ⟨1328, by rfl⟩ : syracuseStep 1771 = 2657) R2657
theorem R1773 : ∃ j : ℕ, syracuseStep^[j] 1773 = 1 := reachStep (stepEq 3 (by rfl) ⟨332, by rfl⟩ : syracuseStep 1773 = 665) R665
theorem R1805 : ∃ j : ℕ, syracuseStep^[j] 1805 = 1 := reachStep (stepEq 3 (by rfl) ⟨338, by rfl⟩ : syracuseStep 1805 = 677) R677
theorem R1809 : ∃ j : ℕ, syracuseStep^[j] 1809 = 1 := reachStep (stepEq 2 (by rfl) ⟨678, by rfl⟩ : syracuseStep 1809 = 1357) R1357
theorem R1815 : ∃ j : ℕ, syracuseStep^[j] 1815 = 1 := reachStep (stepEq 1 (by rfl) ⟨1361, by rfl⟩ : syracuseStep 1815 = 2723) R2723
theorem R1917 : ∃ j : ℕ, syracuseStep^[j] 1917 = 1 := reachStep (stepEq 3 (by rfl) ⟨359, by rfl⟩ : syracuseStep 1917 = 719) R719
theorem R1929 : ∃ j : ℕ, syracuseStep^[j] 1929 = 1 := reachStep (stepEq 2 (by rfl) ⟨723, by rfl⟩ : syracuseStep 1929 = 1447) R1447
theorem R67661 : ∃ j : ℕ, syracuseStep^[j] 67661 = 1 := reachStep (stepEq 3 (by rfl) ⟨12686, by rfl⟩ : syracuseStep 67661 = 25373) R25373
theorem R3417 : ∃ j : ℕ, syracuseStep^[j] 3417 = 1 := reachStep (stepEq 2 (by rfl) ⟨1281, by rfl⟩ : syracuseStep 3417 = 2563) R2563
theorem R3421 : ∃ j : ℕ, syracuseStep^[j] 3421 = 1 := reachStep (stepEq 3 (by rfl) ⟨641, by rfl⟩ : syracuseStep 3421 = 1283) R1283
theorem R3425 : ∃ j : ℕ, syracuseStep^[j] 3425 = 1 := reachStep (stepEq 2 (by rfl) ⟨1284, by rfl⟩ : syracuseStep 3425 = 2569) R2569
theorem R3443 : ∃ j : ℕ, syracuseStep^[j] 3443 = 1 := reachStep (stepEq 1 (by rfl) ⟨2582, by rfl⟩ : syracuseStep 3443 = 5165) R5165
theorem R3447 : ∃ j : ℕ, syracuseStep^[j] 3447 = 1 := reachStep (stepEq 1 (by rfl) ⟨2585, by rfl⟩ : syracuseStep 3447 = 5171) R5171
theorem R3451 : ∃ j : ℕ, syracuseStep^[j] 3451 = 1 := reachStep (stepEq 1 (by rfl) ⟨2588, by rfl⟩ : syracuseStep 3451 = 5177) R5177
theorem R3455 : ∃ j : ℕ, syracuseStep^[j] 3455 = 1 := reachStep (stepEq 1 (by rfl) ⟨2591, by rfl⟩ : syracuseStep 3455 = 5183) R5183
theorem R3479 : ∃ j : ℕ, syracuseStep^[j] 3479 = 1 := reachStep (stepEq 1 (by rfl) ⟨2609, by rfl⟩ : syracuseStep 3479 = 5219) R5219
theorem R3481 : ∃ j : ℕ, syracuseStep^[j] 3481 = 1 := reachStep (stepEq 2 (by rfl) ⟨1305, by rfl⟩ : syracuseStep 3481 = 2611) R2611
theorem R3495 : ∃ j : ℕ, syracuseStep^[j] 3495 = 1 := reachStep (stepEq 1 (by rfl) ⟨2621, by rfl⟩ : syracuseStep 3495 = 5243) R5243
theorem R3505 : ∃ j : ℕ, syracuseStep^[j] 3505 = 1 := reachStep (stepEq 2 (by rfl) ⟨1314, by rfl⟩ : syracuseStep 3505 = 2629) R2629
theorem R3507 : ∃ j : ℕ, syracuseStep^[j] 3507 = 1 := reachStep (stepEq 1 (by rfl) ⟨2630, by rfl⟩ : syracuseStep 3507 = 5261) R5261
theorem R3509 : ∃ j : ℕ, syracuseStep^[j] 3509 = 1 := reachStep (stepEq 5 (by rfl) ⟨164, by rfl⟩ : syracuseStep 3509 = 329) R329
theorem R3513 : ∃ j : ℕ, syracuseStep^[j] 3513 = 1 := reachStep (stepEq 2 (by rfl) ⟨1317, by rfl⟩ : syracuseStep 3513 = 2635) R2635
theorem R3527 : ∃ j : ℕ, syracuseStep^[j] 3527 = 1 := reachStep (stepEq 1 (by rfl) ⟨2645, by rfl⟩ : syracuseStep 3527 = 5291) R5291
theorem R3529 : ∃ j : ℕ, syracuseStep^[j] 3529 = 1 := reachStep (stepEq 2 (by rfl) ⟨1323, by rfl⟩ : syracuseStep 3529 = 2647) R2647
theorem R3539 : ∃ j : ℕ, syracuseStep^[j] 3539 = 1 := reachStep (stepEq 1 (by rfl) ⟨2654, by rfl⟩ : syracuseStep 3539 = 5309) R5309
theorem R3543 : ∃ j : ℕ, syracuseStep^[j] 3543 = 1 := reachStep (stepEq 1 (by rfl) ⟨2657, by rfl⟩ : syracuseStep 3543 = 5315) R5315
theorem R3545 : ∃ j : ℕ, syracuseStep^[j] 3545 = 1 := reachStep (stepEq 2 (by rfl) ⟨1329, by rfl⟩ : syracuseStep 3545 = 2659) R2659
theorem R3547 : ∃ j : ℕ, syracuseStep^[j] 3547 = 1 := reachStep (stepEq 1 (by rfl) ⟨2660, by rfl⟩ : syracuseStep 3547 = 5321) R5321
theorem R3549 : ∃ j : ℕ, syracuseStep^[j] 3549 = 1 := reachStep (stepEq 3 (by rfl) ⟨665, by rfl⟩ : syracuseStep 3549 = 1331) R1331
theorem R3553 : ∃ j : ℕ, syracuseStep^[j] 3553 = 1 := reachStep (stepEq 2 (by rfl) ⟨1332, by rfl⟩ : syracuseStep 3553 = 2665) R2665
theorem R3605 : ∃ j : ℕ, syracuseStep^[j] 3605 = 1 := reachStep (stepEq 6 (by rfl) ⟨84, by rfl⟩ : syracuseStep 3605 = 169) R169
theorem R3619 : ∃ j : ℕ, syracuseStep^[j] 3619 = 1 := reachStep (stepEq 1 (by rfl) ⟨2714, by rfl⟩ : syracuseStep 3619 = 5429) R5429
theorem R3627 : ∃ j : ℕ, syracuseStep^[j] 3627 = 1 := reachStep (stepEq 1 (by rfl) ⟨2720, by rfl⟩ : syracuseStep 3627 = 5441) R5441
theorem R3629 : ∃ j : ℕ, syracuseStep^[j] 3629 = 1 := reachStep (stepEq 3 (by rfl) ⟨680, by rfl⟩ : syracuseStep 3629 = 1361) R1361
theorem R3829 : ∃ j : ℕ, syracuseStep^[j] 3829 = 1 := reachStep (stepEq 5 (by rfl) ⟨179, by rfl⟩ : syracuseStep 3829 = 359) R359
theorem R3833 : ∃ j : ℕ, syracuseStep^[j] 3833 = 1 := reachStep (stepEq 2 (by rfl) ⟨1437, by rfl⟩ : syracuseStep 3833 = 2875) R2875
theorem R3859 : ∃ j : ℕ, syracuseStep^[j] 3859 = 1 := reachStep (stepEq 1 (by rfl) ⟨2894, by rfl⟩ : syracuseStep 3859 = 5789) R5789
theorem R4217 : ∃ j : ℕ, syracuseStep^[j] 4217 = 1 := reachStep (stepEq 2 (by rfl) ⟨1581, by rfl⟩ : syracuseStep 4217 = 3163) R3163
theorem R4225 : ∃ j : ℕ, syracuseStep^[j] 4225 = 1 := reachStep (stepEq 2 (by rfl) ⟨1584, by rfl⟩ : syracuseStep 4225 = 3169) R3169
theorem R4235 : ∃ j : ℕ, syracuseStep^[j] 4235 = 1 := reachStep (stepEq 1 (by rfl) ⟨3176, by rfl⟩ : syracuseStep 4235 = 6353) R6353
theorem R6833 : ∃ j : ℕ, syracuseStep^[j] 6833 = 1 := reachStep (stepEq 2 (by rfl) ⟨2562, by rfl⟩ : syracuseStep 6833 = 5125) R5125
theorem R6835 : ∃ j : ℕ, syracuseStep^[j] 6835 = 1 := reachStep (stepEq 1 (by rfl) ⟨5126, by rfl⟩ : syracuseStep 6835 = 10253) R10253
theorem R6851 : ∃ j : ℕ, syracuseStep^[j] 6851 = 1 := reachStep (stepEq 1 (by rfl) ⟨5138, by rfl⟩ : syracuseStep 6851 = 10277) R10277
theorem R6857 : ∃ j : ℕ, syracuseStep^[j] 6857 = 1 := reachStep (stepEq 2 (by rfl) ⟨2571, by rfl⟩ : syracuseStep 6857 = 5143) R5143
theorem R6893 : ∃ j : ℕ, syracuseStep^[j] 6893 = 1 := reachStep (stepEq 3 (by rfl) ⟨1292, by rfl⟩ : syracuseStep 6893 = 2585) R2585
theorem R6961 : ∃ j : ℕ, syracuseStep^[j] 6961 = 1 := reachStep (stepEq 2 (by rfl) ⟨2610, by rfl⟩ : syracuseStep 6961 = 5221) R5221
theorem R6971 : ∃ j : ℕ, syracuseStep^[j] 6971 = 1 := reachStep (stepEq 1 (by rfl) ⟨5228, by rfl⟩ : syracuseStep 6971 = 10457) R10457
theorem R7013 : ∃ j : ℕ, syracuseStep^[j] 7013 = 1 := reachStep (stepEq 4 (by rfl) ⟨657, by rfl⟩ : syracuseStep 7013 = 1315) R1315
theorem R7025 : ∃ j : ℕ, syracuseStep^[j] 7025 = 1 := reachStep (stepEq 2 (by rfl) ⟨2634, by rfl⟩ : syracuseStep 7025 = 5269) R5269
theorem R7051 : ∃ j : ℕ, syracuseStep^[j] 7051 = 1 := reachStep (stepEq 1 (by rfl) ⟨5288, by rfl⟩ : syracuseStep 7051 = 10577) R10577
theorem R7055 : ∃ j : ℕ, syracuseStep^[j] 7055 = 1 := reachStep (stepEq 1 (by rfl) ⟨5291, by rfl⟩ : syracuseStep 7055 = 10583) R10583
theorem R7057 : ∃ j : ℕ, syracuseStep^[j] 7057 = 1 := reachStep (stepEq 2 (by rfl) ⟨2646, by rfl⟩ : syracuseStep 7057 = 5293) R5293
theorem R7067 : ∃ j : ℕ, syracuseStep^[j] 7067 = 1 := reachStep (stepEq 1 (by rfl) ⟨5300, by rfl⟩ : syracuseStep 7067 = 10601) R10601
theorem R7085 : ∃ j : ℕ, syracuseStep^[j] 7085 = 1 := reachStep (stepEq 3 (by rfl) ⟨1328, by rfl⟩ : syracuseStep 7085 = 2657) R2657
theorem R7087 : ∃ j : ℕ, syracuseStep^[j] 7087 = 1 := reachStep (stepEq 1 (by rfl) ⟨5315, by rfl⟩ : syracuseStep 7087 = 10631) R10631
theorem R7091 : ∃ j : ℕ, syracuseStep^[j] 7091 = 1 := reachStep (stepEq 1 (by rfl) ⟨5318, by rfl⟩ : syracuseStep 7091 = 10637) R10637
theorem R7093 : ∃ j : ℕ, syracuseStep^[j] 7093 = 1 := reachStep (stepEq 5 (by rfl) ⟨332, by rfl⟩ : syracuseStep 7093 = 665) R665
theorem R7097 : ∃ j : ℕ, syracuseStep^[j] 7097 = 1 := reachStep (stepEq 2 (by rfl) ⟨2661, by rfl⟩ : syracuseStep 7097 = 5323) R5323
theorem R7105 : ∃ j : ℕ, syracuseStep^[j] 7105 = 1 := reachStep (stepEq 2 (by rfl) ⟨2664, by rfl⟩ : syracuseStep 7105 = 5329) R5329
theorem R7115 : ∃ j : ℕ, syracuseStep^[j] 7115 = 1 := reachStep (stepEq 1 (by rfl) ⟨5336, by rfl⟩ : syracuseStep 7115 = 10673) R10673
theorem R7163 : ∃ j : ℕ, syracuseStep^[j] 7163 = 1 := reachStep (stepEq 1 (by rfl) ⟨5372, by rfl⟩ : syracuseStep 7163 = 10745) R10745
theorem R7393 : ∃ j : ℕ, syracuseStep^[j] 7393 = 1 := reachStep (stepEq 2 (by rfl) ⟨2772, by rfl⟩ : syracuseStep 7393 = 5545) R5545
theorem R7667 : ∃ j : ℕ, syracuseStep^[j] 7667 = 1 := reachStep (stepEq 1 (by rfl) ⟨5750, by rfl⟩ : syracuseStep 7667 = 11501) R11501
theorem R7673 : ∃ j : ℕ, syracuseStep^[j] 7673 = 1 := reachStep (stepEq 2 (by rfl) ⟨2877, by rfl⟩ : syracuseStep 7673 = 5755) R5755
theorem R7835 : ∃ j : ℕ, syracuseStep^[j] 7835 = 1 := reachStep (stepEq 1 (by rfl) ⟨5876, by rfl⟩ : syracuseStep 7835 = 11753) R11753
theorem R8435 : ∃ j : ℕ, syracuseStep^[j] 8435 = 1 := reachStep (stepEq 1 (by rfl) ⟨6326, by rfl⟩ : syracuseStep 8435 = 12653) R12653
theorem R8441 : ∃ j : ℕ, syracuseStep^[j] 8441 = 1 := reachStep (stepEq 2 (by rfl) ⟨3165, by rfl⟩ : syracuseStep 8441 = 6331) R6331
theorem R8471 : ∃ j : ℕ, syracuseStep^[j] 8471 = 1 := reachStep (stepEq 1 (by rfl) ⟨6353, by rfl⟩ : syracuseStep 8471 = 12707) R12707
theorem R13667 : ∃ j : ℕ, syracuseStep^[j] 13667 = 1 := reachStep (stepEq 1 (by rfl) ⟨10250, by rfl⟩ : syracuseStep 13667 = 20501) R20501
theorem R13715 : ∃ j : ℕ, syracuseStep^[j] 13715 = 1 := reachStep (stepEq 1 (by rfl) ⟨10286, by rfl⟩ : syracuseStep 13715 = 20573) R20573
theorem R13729 : ∃ j : ℕ, syracuseStep^[j] 13729 = 1 := reachStep (stepEq 2 (by rfl) ⟨5148, by rfl⟩ : syracuseStep 13729 = 10297) R10297
theorem R13769 : ∃ j : ℕ, syracuseStep^[j] 13769 = 1 := reachStep (stepEq 2 (by rfl) ⟨5163, by rfl⟩ : syracuseStep 13769 = 10327) R10327
theorem R13787 : ∃ j : ℕ, syracuseStep^[j] 13787 = 1 := reachStep (stepEq 1 (by rfl) ⟨10340, by rfl⟩ : syracuseStep 13787 = 20681) R20681
theorem R13805 : ∃ j : ℕ, syracuseStep^[j] 13805 = 1 := reachStep (stepEq 3 (by rfl) ⟨2588, by rfl⟩ : syracuseStep 13805 = 5177) R5177
theorem R13981 : ∃ j : ℕ, syracuseStep^[j] 13981 = 1 := reachStep (stepEq 3 (by rfl) ⟨2621, by rfl⟩ : syracuseStep 13981 = 5243) R5243
theorem R13985 : ∃ j : ℕ, syracuseStep^[j] 13985 = 1 := reachStep (stepEq 2 (by rfl) ⟨5244, by rfl⟩ : syracuseStep 13985 = 10489) R10489
theorem R14021 : ∃ j : ℕ, syracuseStep^[j] 14021 = 1 := reachStep (stepEq 4 (by rfl) ⟨1314, by rfl⟩ : syracuseStep 14021 = 2629) R2629
theorem R14029 : ∃ j : ℕ, syracuseStep^[j] 14029 = 1 := reachStep (stepEq 3 (by rfl) ⟨2630, by rfl⟩ : syracuseStep 14029 = 5261) R5261
theorem R14053 : ∃ j : ℕ, syracuseStep^[j] 14053 = 1 := reachStep (stepEq 4 (by rfl) ⟨1317, by rfl⟩ : syracuseStep 14053 = 2635) R2635
theorem R14195 : ∃ j : ℕ, syracuseStep^[j] 14195 = 1 := reachStep (stepEq 1 (by rfl) ⟨10646, by rfl⟩ : syracuseStep 14195 = 21293) R21293
theorem R14215 : ∃ j : ℕ, syracuseStep^[j] 14215 = 1 := reachStep (stepEq 1 (by rfl) ⟨10661, by rfl⟩ : syracuseStep 14215 = 21323) R21323
theorem R14327 : ∃ j : ℕ, syracuseStep^[j] 14327 = 1 := reachStep (stepEq 1 (by rfl) ⟨10745, by rfl⟩ : syracuseStep 14327 = 21491) R21491
theorem R14633 : ∃ j : ℕ, syracuseStep^[j] 14633 = 1 := reachStep (stepEq 2 (by rfl) ⟨5487, by rfl⟩ : syracuseStep 14633 = 10975) R10975
theorem R16901 : ∃ j : ℕ, syracuseStep^[j] 16901 = 1 := reachStep (stepEq 4 (by rfl) ⟨1584, by rfl⟩ : syracuseStep 16901 = 3169) R3169
theorem R118331 : ∃ j : ℕ, syracuseStep^[j] 118331 = 1 := reachStep (stepEq 1 (by rfl) ⟨88748, by rfl⟩ : syracuseStep 118331 = 177497) R177497
theorem R54917 : ∃ j : ℕ, syracuseStep^[j] 54917 = 1 := reachStep (stepEq 4 (by rfl) ⟨5148, by rfl⟩ : syracuseStep 54917 = 10297) R10297
theorem R56861 : ∃ j : ℕ, syracuseStep^[j] 56861 = 1 := reachStep (stepEq 3 (by rfl) ⟨10661, by rfl⟩ : syracuseStep 56861 = 21323) R21323
theorem R27377 : ∃ j : ℕ, syracuseStep^[j] 27377 = 1 := reachStep (stepEq 2 (by rfl) ⟨10266, by rfl⟩ : syracuseStep 27377 = 20533) R20533
theorem R27539 : ∃ j : ℕ, syracuseStep^[j] 27539 = 1 := reachStep (stepEq 1 (by rfl) ⟨20654, by rfl⟩ : syracuseStep 27539 = 41309) R41309
theorem R28349 : ∃ j : ℕ, syracuseStep^[j] 28349 = 1 := reachStep (stepEq 3 (by rfl) ⟨5315, by rfl⟩ : syracuseStep 28349 = 10631) R10631
theorem R28363 : ∃ j : ℕ, syracuseStep^[j] 28363 = 1 := reachStep (stepEq 1 (by rfl) ⟨21272, by rfl⟩ : syracuseStep 28363 = 42545) R42545
theorem R30779 : ∃ j : ℕ, syracuseStep^[j] 30779 = 1 := reachStep (stepEq 1 (by rfl) ⟨23084, by rfl⟩ : syracuseStep 30779 = 46169) R46169
theorem R31337 : ∃ j : ℕ, syracuseStep^[j] 31337 = 1 := reachStep (stepEq 2 (by rfl) ⟨11751, by rfl⟩ : syracuseStep 31337 = 23503) R23503
theorem R159 : ∃ j : ℕ, syracuseStep^[j] 159 = 1 := reachStep (stepEq 1 (by rfl) ⟨119, by rfl⟩ : syracuseStep 159 = 239) R239
theorem R295 : ∃ j : ℕ, syracuseStep^[j] 295 = 1 := reachStep (stepEq 1 (by rfl) ⟨221, by rfl⟩ : syracuseStep 295 = 443) R443
theorem R319 : ∃ j : ℕ, syracuseStep^[j] 319 = 1 := reachStep (stepEq 1 (by rfl) ⟨239, by rfl⟩ : syracuseStep 319 = 479) R479
theorem R569 : ∃ j : ℕ, syracuseStep^[j] 569 = 1 := reachStep (stepEq 2 (by rfl) ⟨213, by rfl⟩ : syracuseStep 569 = 427) R427
theorem R585 : ∃ j : ℕ, syracuseStep^[j] 585 = 1 := reachStep (stepEq 2 (by rfl) ⟨219, by rfl⟩ : syracuseStep 585 = 439) R439
theorem R591 : ∃ j : ℕ, syracuseStep^[j] 591 = 1 := reachStep (stepEq 1 (by rfl) ⟨443, by rfl⟩ : syracuseStep 591 = 887) R887
theorem R601 : ∃ j : ℕ, syracuseStep^[j] 601 = 1 := reachStep (stepEq 2 (by rfl) ⟨225, by rfl⟩ : syracuseStep 601 = 451) R451
theorem R637 : ∃ j : ℕ, syracuseStep^[j] 637 = 1 := reachStep (stepEq 3 (by rfl) ⟨119, by rfl⟩ : syracuseStep 637 = 239) R239
theorem R1139 : ∃ j : ℕ, syracuseStep^[j] 1139 = 1 := reachStep (stepEq 1 (by rfl) ⟨854, by rfl⟩ : syracuseStep 1139 = 1709) R1709
theorem R1147 : ∃ j : ℕ, syracuseStep^[j] 1147 = 1 := reachStep (stepEq 1 (by rfl) ⟨860, by rfl⟩ : syracuseStep 1147 = 1721) R1721
theorem R1151 : ∃ j : ℕ, syracuseStep^[j] 1151 = 1 := reachStep (stepEq 1 (by rfl) ⟨863, by rfl⟩ : syracuseStep 1151 = 1727) R1727
theorem R1159 : ∃ j : ℕ, syracuseStep^[j] 1159 = 1 := reachStep (stepEq 1 (by rfl) ⟨869, by rfl⟩ : syracuseStep 1159 = 1739) R1739
theorem R1169 : ∃ j : ℕ, syracuseStep^[j] 1169 = 1 := reachStep (stepEq 2 (by rfl) ⟨438, by rfl⟩ : syracuseStep 1169 = 877) R877
theorem R1171 : ∃ j : ℕ, syracuseStep^[j] 1171 = 1 := reachStep (stepEq 1 (by rfl) ⟨878, by rfl⟩ : syracuseStep 1171 = 1757) R1757
theorem R1179 : ∃ j : ℕ, syracuseStep^[j] 1179 = 1 := reachStep (stepEq 1 (by rfl) ⟨884, by rfl⟩ : syracuseStep 1179 = 1769) R1769
theorem R1181 : ∃ j : ℕ, syracuseStep^[j] 1181 = 1 := reachStep (stepEq 3 (by rfl) ⟨221, by rfl⟩ : syracuseStep 1181 = 443) R443
theorem R1201 : ∃ j : ℕ, syracuseStep^[j] 1201 = 1 := reachStep (stepEq 2 (by rfl) ⟨450, by rfl⟩ : syracuseStep 1201 = 901) R901
theorem R1203 : ∃ j : ℕ, syracuseStep^[j] 1203 = 1 := reachStep (stepEq 1 (by rfl) ⟨902, by rfl⟩ : syracuseStep 1203 = 1805) R1805
theorem R1209 : ∃ j : ℕ, syracuseStep^[j] 1209 = 1 := reachStep (stepEq 2 (by rfl) ⟨453, by rfl⟩ : syracuseStep 1209 = 907) R907
theorem R1277 : ∃ j : ℕ, syracuseStep^[j] 1277 = 1 := reachStep (stepEq 3 (by rfl) ⟨239, by rfl⟩ : syracuseStep 1277 = 479) R479
theorem R2277 : ∃ j : ℕ, syracuseStep^[j] 2277 = 1 := reachStep (stepEq 4 (by rfl) ⟨213, by rfl⟩ : syracuseStep 2277 = 427) R427
theorem R2283 : ∃ j : ℕ, syracuseStep^[j] 2283 = 1 := reachStep (stepEq 1 (by rfl) ⟨1712, by rfl⟩ : syracuseStep 2283 = 3425) R3425
theorem R2295 : ∃ j : ℕ, syracuseStep^[j] 2295 = 1 := reachStep (stepEq 1 (by rfl) ⟨1721, by rfl⟩ : syracuseStep 2295 = 3443) R3443
theorem R2297 : ∃ j : ℕ, syracuseStep^[j] 2297 = 1 := reachStep (stepEq 2 (by rfl) ⟨861, by rfl⟩ : syracuseStep 2297 = 1723) R1723
theorem R2303 : ∃ j : ℕ, syracuseStep^[j] 2303 = 1 := reachStep (stepEq 1 (by rfl) ⟨1727, by rfl⟩ : syracuseStep 2303 = 3455) R3455
theorem R2319 : ∃ j : ℕ, syracuseStep^[j] 2319 = 1 := reachStep (stepEq 1 (by rfl) ⟨1739, by rfl⟩ : syracuseStep 2319 = 3479) R3479
theorem R2337 : ∃ j : ℕ, syracuseStep^[j] 2337 = 1 := reachStep (stepEq 2 (by rfl) ⟨876, by rfl⟩ : syracuseStep 2337 = 1753) R1753
theorem R2339 : ∃ j : ℕ, syracuseStep^[j] 2339 = 1 := reachStep (stepEq 1 (by rfl) ⟨1754, by rfl⟩ : syracuseStep 2339 = 3509) R3509
theorem R2341 : ∃ j : ℕ, syracuseStep^[j] 2341 = 1 := reachStep (stepEq 4 (by rfl) ⟨219, by rfl⟩ : syracuseStep 2341 = 439) R439
theorem R2351 : ∃ j : ℕ, syracuseStep^[j] 2351 = 1 := reachStep (stepEq 1 (by rfl) ⟨1763, by rfl⟩ : syracuseStep 2351 = 3527) R3527
theorem R2359 : ∃ j : ℕ, syracuseStep^[j] 2359 = 1 := reachStep (stepEq 1 (by rfl) ⟨1769, by rfl⟩ : syracuseStep 2359 = 3539) R3539
theorem R2361 : ∃ j : ℕ, syracuseStep^[j] 2361 = 1 := reachStep (stepEq 2 (by rfl) ⟨885, by rfl⟩ : syracuseStep 2361 = 1771) R1771
theorem R2363 : ∃ j : ℕ, syracuseStep^[j] 2363 = 1 := reachStep (stepEq 1 (by rfl) ⟨1772, by rfl⟩ : syracuseStep 2363 = 3545) R3545
theorem R2365 : ∃ j : ℕ, syracuseStep^[j] 2365 = 1 := reachStep (stepEq 3 (by rfl) ⟨443, by rfl⟩ : syracuseStep 2365 = 887) R887
theorem R2403 : ∃ j : ℕ, syracuseStep^[j] 2403 = 1 := reachStep (stepEq 1 (by rfl) ⟨1802, by rfl⟩ : syracuseStep 2403 = 3605) R3605
theorem R2405 : ∃ j : ℕ, syracuseStep^[j] 2405 = 1 := reachStep (stepEq 4 (by rfl) ⟨225, by rfl⟩ : syracuseStep 2405 = 451) R451
theorem R2419 : ∃ j : ℕ, syracuseStep^[j] 2419 = 1 := reachStep (stepEq 1 (by rfl) ⟨1814, by rfl⟩ : syracuseStep 2419 = 3629) R3629
theorem R2549 : ∃ j : ℕ, syracuseStep^[j] 2549 = 1 := reachStep (stepEq 5 (by rfl) ⟨119, by rfl⟩ : syracuseStep 2549 = 239) R239
theorem R2555 : ∃ j : ℕ, syracuseStep^[j] 2555 = 1 := reachStep (stepEq 1 (by rfl) ⟨1916, by rfl⟩ : syracuseStep 2555 = 3833) R3833
theorem R2811 : ∃ j : ℕ, syracuseStep^[j] 2811 = 1 := reachStep (stepEq 1 (by rfl) ⟨2108, by rfl⟩ : syracuseStep 2811 = 4217) R4217
theorem R2823 : ∃ j : ℕ, syracuseStep^[j] 2823 = 1 := reachStep (stepEq 1 (by rfl) ⟨2117, by rfl⟩ : syracuseStep 2823 = 4235) R4235
theorem R36445 : ∃ j : ℕ, syracuseStep^[j] 36445 = 1 := reachStep (stepEq 3 (by rfl) ⟨6833, by rfl⟩ : syracuseStep 36445 = 13667) R13667
theorem R36611 : ∃ j : ℕ, syracuseStep^[j] 36611 = 1 := reachStep (stepEq 1 (by rfl) ⟨27458, by rfl⟩ : syracuseStep 36611 = 54917) R54917
theorem R299285 : ∃ j : ℕ, syracuseStep^[j] 299285 = 1 := reachStep (stepEq 6 (by rfl) ⟨7014, by rfl⟩ : syracuseStep 299285 = 14029) R14029
theorem R4555 : ∃ j : ℕ, syracuseStep^[j] 4555 = 1 := reachStep (stepEq 1 (by rfl) ⟨3416, by rfl⟩ : syracuseStep 4555 = 6833) R6833
theorem R4557 : ∃ j : ℕ, syracuseStep^[j] 4557 = 1 := reachStep (stepEq 3 (by rfl) ⟨854, by rfl⟩ : syracuseStep 4557 = 1709) R1709
theorem R4561 : ∃ j : ℕ, syracuseStep^[j] 4561 = 1 := reachStep (stepEq 2 (by rfl) ⟨1710, by rfl⟩ : syracuseStep 4561 = 3421) R3421
theorem R4567 : ∃ j : ℕ, syracuseStep^[j] 4567 = 1 := reachStep (stepEq 1 (by rfl) ⟨3425, by rfl⟩ : syracuseStep 4567 = 6851) R6851
theorem R4571 : ∃ j : ℕ, syracuseStep^[j] 4571 = 1 := reachStep (stepEq 1 (by rfl) ⟨3428, by rfl⟩ : syracuseStep 4571 = 6857) R6857
theorem R4589 : ∃ j : ℕ, syracuseStep^[j] 4589 = 1 := reachStep (stepEq 3 (by rfl) ⟨860, by rfl⟩ : syracuseStep 4589 = 1721) R1721
theorem R4595 : ∃ j : ℕ, syracuseStep^[j] 4595 = 1 := reachStep (stepEq 1 (by rfl) ⟨3446, by rfl⟩ : syracuseStep 4595 = 6893) R6893
theorem R4601 : ∃ j : ℕ, syracuseStep^[j] 4601 = 1 := reachStep (stepEq 2 (by rfl) ⟨1725, by rfl⟩ : syracuseStep 4601 = 3451) R3451
theorem R4605 : ∃ j : ℕ, syracuseStep^[j] 4605 = 1 := reachStep (stepEq 3 (by rfl) ⟨863, by rfl⟩ : syracuseStep 4605 = 1727) R1727
theorem R4637 : ∃ j : ℕ, syracuseStep^[j] 4637 = 1 := reachStep (stepEq 3 (by rfl) ⟨869, by rfl⟩ : syracuseStep 4637 = 1739) R1739
theorem R4641 : ∃ j : ℕ, syracuseStep^[j] 4641 = 1 := reachStep (stepEq 2 (by rfl) ⟨1740, by rfl⟩ : syracuseStep 4641 = 3481) R3481
theorem R4647 : ∃ j : ℕ, syracuseStep^[j] 4647 = 1 := reachStep (stepEq 1 (by rfl) ⟨3485, by rfl⟩ : syracuseStep 4647 = 6971) R6971
theorem R4673 : ∃ j : ℕ, syracuseStep^[j] 4673 = 1 := reachStep (stepEq 2 (by rfl) ⟨1752, by rfl⟩ : syracuseStep 4673 = 3505) R3505
theorem R4675 : ∃ j : ℕ, syracuseStep^[j] 4675 = 1 := reachStep (stepEq 1 (by rfl) ⟨3506, by rfl⟩ : syracuseStep 4675 = 7013) R7013
theorem R4677 : ∃ j : ℕ, syracuseStep^[j] 4677 = 1 := reachStep (stepEq 4 (by rfl) ⟨438, by rfl⟩ : syracuseStep 4677 = 877) R877
theorem R4683 : ∃ j : ℕ, syracuseStep^[j] 4683 = 1 := reachStep (stepEq 1 (by rfl) ⟨3512, by rfl⟩ : syracuseStep 4683 = 7025) R7025
theorem R4685 : ∃ j : ℕ, syracuseStep^[j] 4685 = 1 := reachStep (stepEq 3 (by rfl) ⟨878, by rfl⟩ : syracuseStep 4685 = 1757) R1757
theorem R4703 : ∃ j : ℕ, syracuseStep^[j] 4703 = 1 := reachStep (stepEq 1 (by rfl) ⟨3527, by rfl⟩ : syracuseStep 4703 = 7055) R7055
theorem R4705 : ∃ j : ℕ, syracuseStep^[j] 4705 = 1 := reachStep (stepEq 2 (by rfl) ⟨1764, by rfl⟩ : syracuseStep 4705 = 3529) R3529
theorem R4711 : ∃ j : ℕ, syracuseStep^[j] 4711 = 1 := reachStep (stepEq 1 (by rfl) ⟨3533, by rfl⟩ : syracuseStep 4711 = 7067) R7067
theorem R4717 : ∃ j : ℕ, syracuseStep^[j] 4717 = 1 := reachStep (stepEq 3 (by rfl) ⟨884, by rfl⟩ : syracuseStep 4717 = 1769) R1769
theorem R4723 : ∃ j : ℕ, syracuseStep^[j] 4723 = 1 := reachStep (stepEq 1 (by rfl) ⟨3542, by rfl⟩ : syracuseStep 4723 = 7085) R7085
theorem R4725 : ∃ j : ℕ, syracuseStep^[j] 4725 = 1 := reachStep (stepEq 5 (by rfl) ⟨221, by rfl⟩ : syracuseStep 4725 = 443) R443
theorem R4727 : ∃ j : ℕ, syracuseStep^[j] 4727 = 1 := reachStep (stepEq 1 (by rfl) ⟨3545, by rfl⟩ : syracuseStep 4727 = 7091) R7091
theorem R4729 : ∃ j : ℕ, syracuseStep^[j] 4729 = 1 := reachStep (stepEq 2 (by rfl) ⟨1773, by rfl⟩ : syracuseStep 4729 = 3547) R3547
theorem R4731 : ∃ j : ℕ, syracuseStep^[j] 4731 = 1 := reachStep (stepEq 1 (by rfl) ⟨3548, by rfl⟩ : syracuseStep 4731 = 7097) R7097
theorem R4737 : ∃ j : ℕ, syracuseStep^[j] 4737 = 1 := reachStep (stepEq 2 (by rfl) ⟨1776, by rfl⟩ : syracuseStep 4737 = 3553) R3553
theorem R4743 : ∃ j : ℕ, syracuseStep^[j] 4743 = 1 := reachStep (stepEq 1 (by rfl) ⟨3557, by rfl⟩ : syracuseStep 4743 = 7115) R7115
theorem R4775 : ∃ j : ℕ, syracuseStep^[j] 4775 = 1 := reachStep (stepEq 1 (by rfl) ⟨3581, by rfl⟩ : syracuseStep 4775 = 7163) R7163
theorem R4805 : ∃ j : ℕ, syracuseStep^[j] 4805 = 1 := reachStep (stepEq 4 (by rfl) ⟨450, by rfl⟩ : syracuseStep 4805 = 901) R901
theorem R4813 : ∃ j : ℕ, syracuseStep^[j] 4813 = 1 := reachStep (stepEq 3 (by rfl) ⟨902, by rfl⟩ : syracuseStep 4813 = 1805) R1805
theorem R4825 : ∃ j : ℕ, syracuseStep^[j] 4825 = 1 := reachStep (stepEq 2 (by rfl) ⟨1809, by rfl⟩ : syracuseStep 4825 = 3619) R3619
theorem R4837 : ∃ j : ℕ, syracuseStep^[j] 4837 = 1 := reachStep (stepEq 4 (by rfl) ⟨453, by rfl⟩ : syracuseStep 4837 = 907) R907
theorem R37817 : ∃ j : ℕ, syracuseStep^[j] 37817 = 1 := reachStep (stepEq 2 (by rfl) ⟨14181, by rfl⟩ : syracuseStep 37817 = 28363) R28363
theorem R37829 : ∃ j : ℕ, syracuseStep^[j] 37829 = 1 := reachStep (stepEq 4 (by rfl) ⟨3546, by rfl⟩ : syracuseStep 37829 = 7093) R7093
theorem R5105 : ∃ j : ℕ, syracuseStep^[j] 5105 = 1 := reachStep (stepEq 2 (by rfl) ⟨1914, by rfl⟩ : syracuseStep 5105 = 3829) R3829
theorem R5109 : ∃ j : ℕ, syracuseStep^[j] 5109 = 1 := reachStep (stepEq 5 (by rfl) ⟨239, by rfl⟩ : syracuseStep 5109 = 479) R479
theorem R5111 : ∃ j : ℕ, syracuseStep^[j] 5111 = 1 := reachStep (stepEq 1 (by rfl) ⟨3833, by rfl⟩ : syracuseStep 5111 = 7667) R7667
theorem R5115 : ∃ j : ℕ, syracuseStep^[j] 5115 = 1 := reachStep (stepEq 1 (by rfl) ⟨3836, by rfl⟩ : syracuseStep 5115 = 7673) R7673
theorem R37907 : ∃ j : ℕ, syracuseStep^[j] 37907 = 1 := reachStep (stepEq 1 (by rfl) ⟨28430, by rfl⟩ : syracuseStep 37907 = 56861) R56861
theorem R5145 : ∃ j : ℕ, syracuseStep^[j] 5145 = 1 := reachStep (stepEq 2 (by rfl) ⟨1929, by rfl⟩ : syracuseStep 5145 = 3859) R3859
theorem R5223 : ∃ j : ℕ, syracuseStep^[j] 5223 = 1 := reachStep (stepEq 1 (by rfl) ⟨3917, by rfl⟩ : syracuseStep 5223 = 7835) R7835
theorem R5623 : ∃ j : ℕ, syracuseStep^[j] 5623 = 1 := reachStep (stepEq 1 (by rfl) ⟨4217, by rfl⟩ : syracuseStep 5623 = 8435) R8435
theorem R5627 : ∃ j : ℕ, syracuseStep^[j] 5627 = 1 := reachStep (stepEq 1 (by rfl) ⟨4220, by rfl⟩ : syracuseStep 5627 = 8441) R8441
theorem R5633 : ∃ j : ℕ, syracuseStep^[j] 5633 = 1 := reachStep (stepEq 2 (by rfl) ⟨2112, by rfl⟩ : syracuseStep 5633 = 4225) R4225
theorem R5647 : ∃ j : ℕ, syracuseStep^[j] 5647 = 1 := reachStep (stepEq 1 (by rfl) ⟨4235, by rfl⟩ : syracuseStep 5647 = 8471) R8471
theorem R74357 : ∃ j : ℕ, syracuseStep^[j] 74357 = 1 := reachStep (stepEq 5 (by rfl) ⟨3485, by rfl⟩ : syracuseStep 74357 = 6971) R6971
theorem R9113 : ∃ j : ℕ, syracuseStep^[j] 9113 = 1 := reachStep (stepEq 2 (by rfl) ⟨3417, by rfl⟩ : syracuseStep 9113 = 6835) R6835
theorem R9143 : ∃ j : ℕ, syracuseStep^[j] 9143 = 1 := reachStep (stepEq 1 (by rfl) ⟨6857, by rfl⟩ : syracuseStep 9143 = 13715) R13715
theorem R9179 : ∃ j : ℕ, syracuseStep^[j] 9179 = 1 := reachStep (stepEq 1 (by rfl) ⟨6884, by rfl⟩ : syracuseStep 9179 = 13769) R13769
theorem R9181 : ∃ j : ℕ, syracuseStep^[j] 9181 = 1 := reachStep (stepEq 3 (by rfl) ⟨1721, by rfl⟩ : syracuseStep 9181 = 3443) R3443
theorem R9191 : ∃ j : ℕ, syracuseStep^[j] 9191 = 1 := reachStep (stepEq 1 (by rfl) ⟨6893, by rfl⟩ : syracuseStep 9191 = 13787) R13787
theorem R9203 : ∃ j : ℕ, syracuseStep^[j] 9203 = 1 := reachStep (stepEq 1 (by rfl) ⟨6902, by rfl⟩ : syracuseStep 9203 = 13805) R13805
theorem R9281 : ∃ j : ℕ, syracuseStep^[j] 9281 = 1 := reachStep (stepEq 2 (by rfl) ⟨3480, by rfl⟩ : syracuseStep 9281 = 6961) R6961
theorem R9323 : ∃ j : ℕ, syracuseStep^[j] 9323 = 1 := reachStep (stepEq 1 (by rfl) ⟨6992, by rfl⟩ : syracuseStep 9323 = 13985) R13985
theorem R9347 : ∃ j : ℕ, syracuseStep^[j] 9347 = 1 := reachStep (stepEq 1 (by rfl) ⟨7010, by rfl⟩ : syracuseStep 9347 = 14021) R14021
theorem R9365 : ∃ j : ℕ, syracuseStep^[j] 9365 = 1 := reachStep (stepEq 6 (by rfl) ⟨219, by rfl⟩ : syracuseStep 9365 = 439) R439
theorem R9401 : ∃ j : ℕ, syracuseStep^[j] 9401 = 1 := reachStep (stepEq 2 (by rfl) ⟨3525, by rfl⟩ : syracuseStep 9401 = 7051) R7051
theorem R9409 : ∃ j : ℕ, syracuseStep^[j] 9409 = 1 := reachStep (stepEq 2 (by rfl) ⟨3528, by rfl⟩ : syracuseStep 9409 = 7057) R7057
theorem R9437 : ∃ j : ℕ, syracuseStep^[j] 9437 = 1 := reachStep (stepEq 3 (by rfl) ⟨1769, by rfl⟩ : syracuseStep 9437 = 3539) R3539
theorem R9449 : ∃ j : ℕ, syracuseStep^[j] 9449 = 1 := reachStep (stepEq 2 (by rfl) ⟨3543, by rfl⟩ : syracuseStep 9449 = 7087) R7087
theorem R9461 : ∃ j : ℕ, syracuseStep^[j] 9461 = 1 := reachStep (stepEq 5 (by rfl) ⟨443, by rfl⟩ : syracuseStep 9461 = 887) R887
theorem R9463 : ∃ j : ℕ, syracuseStep^[j] 9463 = 1 := reachStep (stepEq 1 (by rfl) ⟨7097, by rfl⟩ : syracuseStep 9463 = 14195) R14195
theorem R9473 : ∃ j : ℕ, syracuseStep^[j] 9473 = 1 := reachStep (stepEq 2 (by rfl) ⟨3552, by rfl⟩ : syracuseStep 9473 = 7105) R7105
theorem R9551 : ∃ j : ℕ, syracuseStep^[j] 9551 = 1 := reachStep (stepEq 1 (by rfl) ⟨7163, by rfl⟩ : syracuseStep 9551 = 14327) R14327
theorem R9677 : ∃ j : ℕ, syracuseStep^[j] 9677 = 1 := reachStep (stepEq 3 (by rfl) ⟨1814, by rfl⟩ : syracuseStep 9677 = 3629) R3629
theorem R9755 : ∃ j : ℕ, syracuseStep^[j] 9755 = 1 := reachStep (stepEq 1 (by rfl) ⟨7316, by rfl⟩ : syracuseStep 9755 = 14633) R14633
theorem R9857 : ∃ j : ℕ, syracuseStep^[j] 9857 = 1 := reachStep (stepEq 2 (by rfl) ⟨3696, by rfl⟩ : syracuseStep 9857 = 7393) R7393
theorem R11245 : ∃ j : ℕ, syracuseStep^[j] 11245 = 1 := reachStep (stepEq 3 (by rfl) ⟨2108, by rfl⟩ : syracuseStep 11245 = 4217) R4217
theorem R11267 : ∃ j : ℕ, syracuseStep^[j] 11267 = 1 := reachStep (stepEq 1 (by rfl) ⟨8450, by rfl⟩ : syracuseStep 11267 = 16901) R16901
theorem R45107 : ∃ j : ℕ, syracuseStep^[j] 45107 = 1 := reachStep (stepEq 1 (by rfl) ⟨33830, by rfl⟩ : syracuseStep 45107 = 67661) R67661
theorem R78887 : ∃ j : ℕ, syracuseStep^[j] 78887 = 1 := reachStep (stepEq 1 (by rfl) ⟨59165, by rfl⟩ : syracuseStep 78887 = 118331) R118331
theorem R18251 : ∃ j : ℕ, syracuseStep^[j] 18251 = 1 := reachStep (stepEq 1 (by rfl) ⟨13688, by rfl⟩ : syracuseStep 18251 = 27377) R27377
theorem R18305 : ∃ j : ℕ, syracuseStep^[j] 18305 = 1 := reachStep (stepEq 2 (by rfl) ⟨6864, by rfl⟩ : syracuseStep 18305 = 13729) R13729
theorem R18359 : ∃ j : ℕ, syracuseStep^[j] 18359 = 1 := reachStep (stepEq 1 (by rfl) ⟨13769, by rfl⟩ : syracuseStep 18359 = 27539) R27539
theorem R18589 : ∃ j : ℕ, syracuseStep^[j] 18589 = 1 := reachStep (stepEq 3 (by rfl) ⟨3485, by rfl⟩ : syracuseStep 18589 = 6971) R6971
theorem R18641 : ∃ j : ℕ, syracuseStep^[j] 18641 = 1 := reachStep (stepEq 2 (by rfl) ⟨6990, by rfl⟩ : syracuseStep 18641 = 13981) R13981
theorem R18737 : ∃ j : ℕ, syracuseStep^[j] 18737 = 1 := reachStep (stepEq 2 (by rfl) ⟨7026, by rfl⟩ : syracuseStep 18737 = 14053) R14053
theorem R18845 : ∃ j : ℕ, syracuseStep^[j] 18845 = 1 := reachStep (stepEq 3 (by rfl) ⟨3533, by rfl⟩ : syracuseStep 18845 = 7067) R7067
theorem R18893 : ∃ j : ℕ, syracuseStep^[j] 18893 = 1 := reachStep (stepEq 3 (by rfl) ⟨3542, by rfl⟩ : syracuseStep 18893 = 7085) R7085
theorem R18899 : ∃ j : ℕ, syracuseStep^[j] 18899 = 1 := reachStep (stepEq 1 (by rfl) ⟨14174, by rfl⟩ : syracuseStep 18899 = 28349) R28349
theorem R18953 : ∃ j : ℕ, syracuseStep^[j] 18953 = 1 := reachStep (stepEq 2 (by rfl) ⟨7107, by rfl⟩ : syracuseStep 18953 = 14215) R14215
theorem R19349 : ∃ j : ℕ, syracuseStep^[j] 19349 = 1 := reachStep (stepEq 6 (by rfl) ⟨453, by rfl⟩ : syracuseStep 19349 = 907) R907
theorem R20519 : ∃ j : ℕ, syracuseStep^[j] 20519 = 1 := reachStep (stepEq 1 (by rfl) ⟨15389, by rfl⟩ : syracuseStep 20519 = 30779) R30779
theorem R20891 : ∃ j : ℕ, syracuseStep^[j] 20891 = 1 := reachStep (stepEq 1 (by rfl) ⟨15668, by rfl⟩ : syracuseStep 20891 = 31337) R31337
theorem R22589 : ∃ j : ℕ, syracuseStep^[j] 22589 = 1 := reachStep (stepEq 3 (by rfl) ⟨4235, by rfl⟩ : syracuseStep 22589 = 8471) R8471
theorem R379 : ∃ j : ℕ, syracuseStep^[j] 379 = 1 := reachStep (stepEq 1 (by rfl) ⟨284, by rfl⟩ : syracuseStep 379 = 569) R569
theorem R393 : ∃ j : ℕ, syracuseStep^[j] 393 = 1 := reachStep (stepEq 2 (by rfl) ⟨147, by rfl⟩ : syracuseStep 393 = 295) R295
theorem R425 : ∃ j : ℕ, syracuseStep^[j] 425 = 1 := reachStep (stepEq 2 (by rfl) ⟨159, by rfl⟩ : syracuseStep 425 = 319) R319
theorem R759 : ∃ j : ℕ, syracuseStep^[j] 759 = 1 := reachStep (stepEq 1 (by rfl) ⟨569, by rfl⟩ : syracuseStep 759 = 1139) R1139
theorem R767 : ∃ j : ℕ, syracuseStep^[j] 767 = 1 := reachStep (stepEq 1 (by rfl) ⟨575, by rfl⟩ : syracuseStep 767 = 1151) R1151
theorem R779 : ∃ j : ℕ, syracuseStep^[j] 779 = 1 := reachStep (stepEq 1 (by rfl) ⟨584, by rfl⟩ : syracuseStep 779 = 1169) R1169
theorem R787 : ∃ j : ℕ, syracuseStep^[j] 787 = 1 := reachStep (stepEq 1 (by rfl) ⟨590, by rfl⟩ : syracuseStep 787 = 1181) R1181
theorem R801 : ∃ j : ℕ, syracuseStep^[j] 801 = 1 := reachStep (stepEq 2 (by rfl) ⟨300, by rfl⟩ : syracuseStep 801 = 601) R601
theorem R849 : ∃ j : ℕ, syracuseStep^[j] 849 = 1 := reachStep (stepEq 2 (by rfl) ⟨318, by rfl⟩ : syracuseStep 849 = 637) R637
theorem R851 : ∃ j : ℕ, syracuseStep^[j] 851 = 1 := reachStep (stepEq 1 (by rfl) ⟨638, by rfl⟩ : syracuseStep 851 = 1277) R1277
theorem R1517 : ∃ j : ℕ, syracuseStep^[j] 1517 = 1 := reachStep (stepEq 3 (by rfl) ⟨284, by rfl⟩ : syracuseStep 1517 = 569) R569
theorem R1529 : ∃ j : ℕ, syracuseStep^[j] 1529 = 1 := reachStep (stepEq 2 (by rfl) ⟨573, by rfl⟩ : syracuseStep 1529 = 1147) R1147
theorem R1531 : ∃ j : ℕ, syracuseStep^[j] 1531 = 1 := reachStep (stepEq 1 (by rfl) ⟨1148, by rfl⟩ : syracuseStep 1531 = 2297) R2297
theorem R1535 : ∃ j : ℕ, syracuseStep^[j] 1535 = 1 := reachStep (stepEq 1 (by rfl) ⟨1151, by rfl⟩ : syracuseStep 1535 = 2303) R2303
theorem R1545 : ∃ j : ℕ, syracuseStep^[j] 1545 = 1 := reachStep (stepEq 2 (by rfl) ⟨579, by rfl⟩ : syracuseStep 1545 = 1159) R1159
theorem R1559 : ∃ j : ℕ, syracuseStep^[j] 1559 = 1 := reachStep (stepEq 1 (by rfl) ⟨1169, by rfl⟩ : syracuseStep 1559 = 2339) R2339
theorem R1561 : ∃ j : ℕ, syracuseStep^[j] 1561 = 1 := reachStep (stepEq 2 (by rfl) ⟨585, by rfl⟩ : syracuseStep 1561 = 1171) R1171
theorem R1567 : ∃ j : ℕ, syracuseStep^[j] 1567 = 1 := reachStep (stepEq 1 (by rfl) ⟨1175, by rfl⟩ : syracuseStep 1567 = 2351) R2351
theorem R1573 : ∃ j : ℕ, syracuseStep^[j] 1573 = 1 := reachStep (stepEq 4 (by rfl) ⟨147, by rfl⟩ : syracuseStep 1573 = 295) R295
theorem R1575 : ∃ j : ℕ, syracuseStep^[j] 1575 = 1 := reachStep (stepEq 1 (by rfl) ⟨1181, by rfl⟩ : syracuseStep 1575 = 2363) R2363
theorem R1601 : ∃ j : ℕ, syracuseStep^[j] 1601 = 1 := reachStep (stepEq 2 (by rfl) ⟨600, by rfl⟩ : syracuseStep 1601 = 1201) R1201
theorem R1603 : ∃ j : ℕ, syracuseStep^[j] 1603 = 1 := reachStep (stepEq 1 (by rfl) ⟨1202, by rfl⟩ : syracuseStep 1603 = 2405) R2405
theorem R1699 : ∃ j : ℕ, syracuseStep^[j] 1699 = 1 := reachStep (stepEq 1 (by rfl) ⟨1274, by rfl⟩ : syracuseStep 1699 = 2549) R2549
theorem R1701 : ∃ j : ℕ, syracuseStep^[j] 1701 = 1 := reachStep (stepEq 4 (by rfl) ⟨159, by rfl⟩ : syracuseStep 1701 = 319) R319
theorem R1703 : ∃ j : ℕ, syracuseStep^[j] 1703 = 1 := reachStep (stepEq 1 (by rfl) ⟨1277, by rfl⟩ : syracuseStep 1703 = 2555) R2555
theorem R199523 : ∃ j : ℕ, syracuseStep^[j] 199523 = 1 := reachStep (stepEq 1 (by rfl) ⟨149642, by rfl⟩ : syracuseStep 199523 = 299285) R299285
theorem R3037 : ∃ j : ℕ, syracuseStep^[j] 3037 = 1 := reachStep (stepEq 3 (by rfl) ⟨569, by rfl⟩ : syracuseStep 3037 = 1139) R1139
theorem R3047 : ∃ j : ℕ, syracuseStep^[j] 3047 = 1 := reachStep (stepEq 1 (by rfl) ⟨2285, by rfl⟩ : syracuseStep 3047 = 4571) R4571
theorem R3059 : ∃ j : ℕ, syracuseStep^[j] 3059 = 1 := reachStep (stepEq 1 (by rfl) ⟨2294, by rfl⟩ : syracuseStep 3059 = 4589) R4589
theorem R3063 : ∃ j : ℕ, syracuseStep^[j] 3063 = 1 := reachStep (stepEq 1 (by rfl) ⟨2297, by rfl⟩ : syracuseStep 3063 = 4595) R4595
theorem R3067 : ∃ j : ℕ, syracuseStep^[j] 3067 = 1 := reachStep (stepEq 1 (by rfl) ⟨2300, by rfl⟩ : syracuseStep 3067 = 4601) R4601
theorem R3069 : ∃ j : ℕ, syracuseStep^[j] 3069 = 1 := reachStep (stepEq 3 (by rfl) ⟨575, by rfl⟩ : syracuseStep 3069 = 1151) R1151
theorem R3091 : ∃ j : ℕ, syracuseStep^[j] 3091 = 1 := reachStep (stepEq 1 (by rfl) ⟨2318, by rfl⟩ : syracuseStep 3091 = 4637) R4637
theorem R3115 : ∃ j : ℕ, syracuseStep^[j] 3115 = 1 := reachStep (stepEq 1 (by rfl) ⟨2336, by rfl⟩ : syracuseStep 3115 = 4673) R4673
theorem R3117 : ∃ j : ℕ, syracuseStep^[j] 3117 = 1 := reachStep (stepEq 3 (by rfl) ⟨584, by rfl⟩ : syracuseStep 3117 = 1169) R1169
theorem R3121 : ∃ j : ℕ, syracuseStep^[j] 3121 = 1 := reachStep (stepEq 2 (by rfl) ⟨1170, by rfl⟩ : syracuseStep 3121 = 2341) R2341
theorem R3123 : ∃ j : ℕ, syracuseStep^[j] 3123 = 1 := reachStep (stepEq 1 (by rfl) ⟨2342, by rfl⟩ : syracuseStep 3123 = 4685) R4685
theorem R3135 : ∃ j : ℕ, syracuseStep^[j] 3135 = 1 := reachStep (stepEq 1 (by rfl) ⟨2351, by rfl⟩ : syracuseStep 3135 = 4703) R4703
theorem R3145 : ∃ j : ℕ, syracuseStep^[j] 3145 = 1 := reachStep (stepEq 2 (by rfl) ⟨1179, by rfl⟩ : syracuseStep 3145 = 2359) R2359
theorem R3149 : ∃ j : ℕ, syracuseStep^[j] 3149 = 1 := reachStep (stepEq 3 (by rfl) ⟨590, by rfl⟩ : syracuseStep 3149 = 1181) R1181
theorem R3151 : ∃ j : ℕ, syracuseStep^[j] 3151 = 1 := reachStep (stepEq 1 (by rfl) ⟨2363, by rfl⟩ : syracuseStep 3151 = 4727) R4727
theorem R3153 : ∃ j : ℕ, syracuseStep^[j] 3153 = 1 := reachStep (stepEq 2 (by rfl) ⟨1182, by rfl⟩ : syracuseStep 3153 = 2365) R2365
theorem R3183 : ∃ j : ℕ, syracuseStep^[j] 3183 = 1 := reachStep (stepEq 1 (by rfl) ⟨2387, by rfl⟩ : syracuseStep 3183 = 4775) R4775
theorem R3203 : ∃ j : ℕ, syracuseStep^[j] 3203 = 1 := reachStep (stepEq 1 (by rfl) ⟨2402, by rfl⟩ : syracuseStep 3203 = 4805) R4805
theorem R3205 : ∃ j : ℕ, syracuseStep^[j] 3205 = 1 := reachStep (stepEq 4 (by rfl) ⟨300, by rfl⟩ : syracuseStep 3205 = 601) R601
theorem R3225 : ∃ j : ℕ, syracuseStep^[j] 3225 = 1 := reachStep (stepEq 2 (by rfl) ⟨1209, by rfl⟩ : syracuseStep 3225 = 2419) R2419
theorem R3397 : ∃ j : ℕ, syracuseStep^[j] 3397 = 1 := reachStep (stepEq 4 (by rfl) ⟨318, by rfl⟩ : syracuseStep 3397 = 637) R637
theorem R3403 : ∃ j : ℕ, syracuseStep^[j] 3403 = 1 := reachStep (stepEq 1 (by rfl) ⟨2552, by rfl⟩ : syracuseStep 3403 = 5105) R5105
theorem R3405 : ∃ j : ℕ, syracuseStep^[j] 3405 = 1 := reachStep (stepEq 3 (by rfl) ⟨638, by rfl⟩ : syracuseStep 3405 = 1277) R1277
theorem R3407 : ∃ j : ℕ, syracuseStep^[j] 3407 = 1 := reachStep (stepEq 1 (by rfl) ⟨2555, by rfl⟩ : syracuseStep 3407 = 5111) R5111
theorem R3751 : ∃ j : ℕ, syracuseStep^[j] 3751 = 1 := reachStep (stepEq 1 (by rfl) ⟨2813, by rfl⟩ : syracuseStep 3751 = 5627) R5627
theorem R3755 : ∃ j : ℕ, syracuseStep^[j] 3755 = 1 := reachStep (stepEq 1 (by rfl) ⟨2816, by rfl⟩ : syracuseStep 3755 = 5633) R5633
theorem R6069 : ∃ j : ℕ, syracuseStep^[j] 6069 = 1 := reachStep (stepEq 5 (by rfl) ⟨284, by rfl⟩ : syracuseStep 6069 = 569) R569
theorem R6073 : ∃ j : ℕ, syracuseStep^[j] 6073 = 1 := reachStep (stepEq 2 (by rfl) ⟨2277, by rfl⟩ : syracuseStep 6073 = 4555) R4555
theorem R6075 : ∃ j : ℕ, syracuseStep^[j] 6075 = 1 := reachStep (stepEq 1 (by rfl) ⟨4556, by rfl⟩ : syracuseStep 6075 = 9113) R9113
theorem R6081 : ∃ j : ℕ, syracuseStep^[j] 6081 = 1 := reachStep (stepEq 2 (by rfl) ⟨2280, by rfl⟩ : syracuseStep 6081 = 4561) R4561
theorem R6089 : ∃ j : ℕ, syracuseStep^[j] 6089 = 1 := reachStep (stepEq 2 (by rfl) ⟨2283, by rfl⟩ : syracuseStep 6089 = 4567) R4567
theorem R6095 : ∃ j : ℕ, syracuseStep^[j] 6095 = 1 := reachStep (stepEq 1 (by rfl) ⟨4571, by rfl⟩ : syracuseStep 6095 = 9143) R9143
theorem R6117 : ∃ j : ℕ, syracuseStep^[j] 6117 = 1 := reachStep (stepEq 4 (by rfl) ⟨573, by rfl⟩ : syracuseStep 6117 = 1147) R1147
theorem R6119 : ∃ j : ℕ, syracuseStep^[j] 6119 = 1 := reachStep (stepEq 1 (by rfl) ⟨4589, by rfl⟩ : syracuseStep 6119 = 9179) R9179
theorem R6125 : ∃ j : ℕ, syracuseStep^[j] 6125 = 1 := reachStep (stepEq 3 (by rfl) ⟨1148, by rfl⟩ : syracuseStep 6125 = 2297) R2297
theorem R6127 : ∃ j : ℕ, syracuseStep^[j] 6127 = 1 := reachStep (stepEq 1 (by rfl) ⟨4595, by rfl⟩ : syracuseStep 6127 = 9191) R9191
theorem R6135 : ∃ j : ℕ, syracuseStep^[j] 6135 = 1 := reachStep (stepEq 1 (by rfl) ⟨4601, by rfl⟩ : syracuseStep 6135 = 9203) R9203
theorem R6141 : ∃ j : ℕ, syracuseStep^[j] 6141 = 1 := reachStep (stepEq 3 (by rfl) ⟨1151, by rfl⟩ : syracuseStep 6141 = 2303) R2303
theorem R6181 : ∃ j : ℕ, syracuseStep^[j] 6181 = 1 := reachStep (stepEq 4 (by rfl) ⟨579, by rfl⟩ : syracuseStep 6181 = 1159) R1159
theorem R6187 : ∃ j : ℕ, syracuseStep^[j] 6187 = 1 := reachStep (stepEq 1 (by rfl) ⟨4640, by rfl⟩ : syracuseStep 6187 = 9281) R9281
theorem R6215 : ∃ j : ℕ, syracuseStep^[j] 6215 = 1 := reachStep (stepEq 1 (by rfl) ⟨4661, by rfl⟩ : syracuseStep 6215 = 9323) R9323
theorem R6231 : ∃ j : ℕ, syracuseStep^[j] 6231 = 1 := reachStep (stepEq 1 (by rfl) ⟨4673, by rfl⟩ : syracuseStep 6231 = 9347) R9347
theorem R6233 : ∃ j : ℕ, syracuseStep^[j] 6233 = 1 := reachStep (stepEq 2 (by rfl) ⟨2337, by rfl⟩ : syracuseStep 6233 = 4675) R4675
theorem R6237 : ∃ j : ℕ, syracuseStep^[j] 6237 = 1 := reachStep (stepEq 3 (by rfl) ⟨1169, by rfl⟩ : syracuseStep 6237 = 2339) R2339
theorem R6243 : ∃ j : ℕ, syracuseStep^[j] 6243 = 1 := reachStep (stepEq 1 (by rfl) ⟨4682, by rfl⟩ : syracuseStep 6243 = 9365) R9365
theorem R6245 : ∃ j : ℕ, syracuseStep^[j] 6245 = 1 := reachStep (stepEq 4 (by rfl) ⟨585, by rfl⟩ : syracuseStep 6245 = 1171) R1171
theorem R6267 : ∃ j : ℕ, syracuseStep^[j] 6267 = 1 := reachStep (stepEq 1 (by rfl) ⟨4700, by rfl⟩ : syracuseStep 6267 = 9401) R9401
theorem R6269 : ∃ j : ℕ, syracuseStep^[j] 6269 = 1 := reachStep (stepEq 3 (by rfl) ⟨1175, by rfl⟩ : syracuseStep 6269 = 2351) R2351
theorem R6273 : ∃ j : ℕ, syracuseStep^[j] 6273 = 1 := reachStep (stepEq 2 (by rfl) ⟨2352, by rfl⟩ : syracuseStep 6273 = 4705) R4705
theorem R6281 : ∃ j : ℕ, syracuseStep^[j] 6281 = 1 := reachStep (stepEq 2 (by rfl) ⟨2355, by rfl⟩ : syracuseStep 6281 = 4711) R4711
theorem R6289 : ∃ j : ℕ, syracuseStep^[j] 6289 = 1 := reachStep (stepEq 2 (by rfl) ⟨2358, by rfl⟩ : syracuseStep 6289 = 4717) R4717
theorem R6291 : ∃ j : ℕ, syracuseStep^[j] 6291 = 1 := reachStep (stepEq 1 (by rfl) ⟨4718, by rfl⟩ : syracuseStep 6291 = 9437) R9437
theorem R6293 : ∃ j : ℕ, syracuseStep^[j] 6293 = 1 := reachStep (stepEq 6 (by rfl) ⟨147, by rfl⟩ : syracuseStep 6293 = 295) R295
theorem R6297 : ∃ j : ℕ, syracuseStep^[j] 6297 = 1 := reachStep (stepEq 2 (by rfl) ⟨2361, by rfl⟩ : syracuseStep 6297 = 4723) R4723
theorem R6299 : ∃ j : ℕ, syracuseStep^[j] 6299 = 1 := reachStep (stepEq 1 (by rfl) ⟨4724, by rfl⟩ : syracuseStep 6299 = 9449) R9449
theorem R6301 : ∃ j : ℕ, syracuseStep^[j] 6301 = 1 := reachStep (stepEq 3 (by rfl) ⟨1181, by rfl⟩ : syracuseStep 6301 = 2363) R2363
theorem R6305 : ∃ j : ℕ, syracuseStep^[j] 6305 = 1 := reachStep (stepEq 2 (by rfl) ⟨2364, by rfl⟩ : syracuseStep 6305 = 4729) R4729
theorem R6307 : ∃ j : ℕ, syracuseStep^[j] 6307 = 1 := reachStep (stepEq 1 (by rfl) ⟨4730, by rfl⟩ : syracuseStep 6307 = 9461) R9461
theorem R6315 : ∃ j : ℕ, syracuseStep^[j] 6315 = 1 := reachStep (stepEq 1 (by rfl) ⟨4736, by rfl⟩ : syracuseStep 6315 = 9473) R9473
theorem R6367 : ∃ j : ℕ, syracuseStep^[j] 6367 = 1 := reachStep (stepEq 1 (by rfl) ⟨4775, by rfl⟩ : syracuseStep 6367 = 9551) R9551
theorem R6405 : ∃ j : ℕ, syracuseStep^[j] 6405 = 1 := reachStep (stepEq 4 (by rfl) ⟨600, by rfl⟩ : syracuseStep 6405 = 1201) R1201
theorem R6413 : ∃ j : ℕ, syracuseStep^[j] 6413 = 1 := reachStep (stepEq 3 (by rfl) ⟨1202, by rfl⟩ : syracuseStep 6413 = 2405) R2405
theorem R6417 : ∃ j : ℕ, syracuseStep^[j] 6417 = 1 := reachStep (stepEq 2 (by rfl) ⟨2406, by rfl⟩ : syracuseStep 6417 = 4813) R4813
theorem R6433 : ∃ j : ℕ, syracuseStep^[j] 6433 = 1 := reachStep (stepEq 2 (by rfl) ⟨2412, by rfl⟩ : syracuseStep 6433 = 4825) R4825
theorem R6449 : ∃ j : ℕ, syracuseStep^[j] 6449 = 1 := reachStep (stepEq 2 (by rfl) ⟨2418, by rfl⟩ : syracuseStep 6449 = 4837) R4837
theorem R6451 : ∃ j : ℕ, syracuseStep^[j] 6451 = 1 := reachStep (stepEq 1 (by rfl) ⟨4838, by rfl⟩ : syracuseStep 6451 = 9677) R9677
theorem R6503 : ∃ j : ℕ, syracuseStep^[j] 6503 = 1 := reachStep (stepEq 1 (by rfl) ⟨4877, by rfl⟩ : syracuseStep 6503 = 9755) R9755
theorem R6571 : ∃ j : ℕ, syracuseStep^[j] 6571 = 1 := reachStep (stepEq 1 (by rfl) ⟨4928, by rfl⟩ : syracuseStep 6571 = 9857) R9857
theorem R6797 : ∃ j : ℕ, syracuseStep^[j] 6797 = 1 := reachStep (stepEq 3 (by rfl) ⟨1274, by rfl⟩ : syracuseStep 6797 = 2549) R2549
theorem R6805 : ∃ j : ℕ, syracuseStep^[j] 6805 = 1 := reachStep (stepEq 6 (by rfl) ⟨159, by rfl⟩ : syracuseStep 6805 = 319) R319
theorem R7511 : ∃ j : ℕ, syracuseStep^[j] 7511 = 1 := reachStep (stepEq 1 (by rfl) ⟨5633, by rfl⟩ : syracuseStep 7511 = 11267) R11267
theorem R7529 : ∃ j : ℕ, syracuseStep^[j] 7529 = 1 := reachStep (stepEq 2 (by rfl) ⟨2823, by rfl⟩ : syracuseStep 7529 = 5647) R5647
theorem R12149 : ∃ j : ℕ, syracuseStep^[j] 12149 = 1 := reachStep (stepEq 5 (by rfl) ⟨569, by rfl⟩ : syracuseStep 12149 = 1139) R1139
theorem R12167 : ∃ j : ℕ, syracuseStep^[j] 12167 = 1 := reachStep (stepEq 1 (by rfl) ⟨9125, by rfl⟩ : syracuseStep 12167 = 18251) R18251
theorem R12203 : ∃ j : ℕ, syracuseStep^[j] 12203 = 1 := reachStep (stepEq 1 (by rfl) ⟨9152, by rfl⟩ : syracuseStep 12203 = 18305) R18305
theorem R12239 : ∃ j : ℕ, syracuseStep^[j] 12239 = 1 := reachStep (stepEq 1 (by rfl) ⟨9179, by rfl⟩ : syracuseStep 12239 = 18359) R18359
theorem R12241 : ∃ j : ℕ, syracuseStep^[j] 12241 = 1 := reachStep (stepEq 2 (by rfl) ⟨4590, by rfl⟩ : syracuseStep 12241 = 9181) R9181
theorem R12365 : ∃ j : ℕ, syracuseStep^[j] 12365 = 1 := reachStep (stepEq 3 (by rfl) ⟨2318, by rfl⟩ : syracuseStep 12365 = 4637) R4637
theorem R12469 : ∃ j : ℕ, syracuseStep^[j] 12469 = 1 := reachStep (stepEq 5 (by rfl) ⟨584, by rfl⟩ : syracuseStep 12469 = 1169) R1169
theorem R12491 : ∃ j : ℕ, syracuseStep^[j] 12491 = 1 := reachStep (stepEq 1 (by rfl) ⟨9368, by rfl⟩ : syracuseStep 12491 = 18737) R18737
theorem R12545 : ∃ j : ℕ, syracuseStep^[j] 12545 = 1 := reachStep (stepEq 2 (by rfl) ⟨4704, by rfl⟩ : syracuseStep 12545 = 9409) R9409
theorem R12563 : ∃ j : ℕ, syracuseStep^[j] 12563 = 1 := reachStep (stepEq 1 (by rfl) ⟨9422, by rfl⟩ : syracuseStep 12563 = 18845) R18845
theorem R12581 : ∃ j : ℕ, syracuseStep^[j] 12581 = 1 := reachStep (stepEq 4 (by rfl) ⟨1179, by rfl⟩ : syracuseStep 12581 = 2359) R2359
theorem R12595 : ∃ j : ℕ, syracuseStep^[j] 12595 = 1 := reachStep (stepEq 1 (by rfl) ⟨9446, by rfl⟩ : syracuseStep 12595 = 18893) R18893
theorem R12599 : ∃ j : ℕ, syracuseStep^[j] 12599 = 1 := reachStep (stepEq 1 (by rfl) ⟨9449, by rfl⟩ : syracuseStep 12599 = 18899) R18899
theorem R12617 : ∃ j : ℕ, syracuseStep^[j] 12617 = 1 := reachStep (stepEq 2 (by rfl) ⟨4731, by rfl⟩ : syracuseStep 12617 = 9463) R9463
theorem R12635 : ∃ j : ℕ, syracuseStep^[j] 12635 = 1 := reachStep (stepEq 1 (by rfl) ⟨9476, by rfl⟩ : syracuseStep 12635 = 18953) R18953
theorem R12899 : ∃ j : ℕ, syracuseStep^[j] 12899 = 1 := reachStep (stepEq 1 (by rfl) ⟨9674, by rfl⟩ : syracuseStep 12899 = 19349) R19349
theorem R13589 : ∃ j : ℕ, syracuseStep^[j] 13589 = 1 := reachStep (stepEq 6 (by rfl) ⟨318, by rfl⟩ : syracuseStep 13589 = 637) R637
theorem R13679 : ∃ j : ℕ, syracuseStep^[j] 13679 = 1 := reachStep (stepEq 1 (by rfl) ⟨10259, by rfl⟩ : syracuseStep 13679 = 20519) R20519
theorem R13927 : ∃ j : ℕ, syracuseStep^[j] 13927 = 1 := reachStep (stepEq 1 (by rfl) ⟨10445, by rfl⟩ : syracuseStep 13927 = 20891) R20891
theorem R14993 : ∃ j : ℕ, syracuseStep^[j] 14993 = 1 := reachStep (stepEq 2 (by rfl) ⟨5622, by rfl⟩ : syracuseStep 14993 = 11245) R11245
theorem R15005 : ∃ j : ℕ, syracuseStep^[j] 15005 = 1 := reachStep (stepEq 3 (by rfl) ⟨2813, by rfl⟩ : syracuseStep 15005 = 5627) R5627
theorem R15059 : ∃ j : ℕ, syracuseStep^[j] 15059 = 1 := reachStep (stepEq 1 (by rfl) ⟨11294, by rfl⟩ : syracuseStep 15059 = 22589) R22589
theorem R48593 : ∃ j : ℕ, syracuseStep^[j] 48593 = 1 := reachStep (stepEq 2 (by rfl) ⟨18222, by rfl⟩ : syracuseStep 48593 = 36445) R36445
theorem R49571 : ∃ j : ℕ, syracuseStep^[j] 49571 = 1 := reachStep (stepEq 1 (by rfl) ⟨37178, by rfl⟩ : syracuseStep 49571 = 74357) R74357
theorem R49709 : ∃ j : ℕ, syracuseStep^[j] 49709 = 1 := reachStep (stepEq 3 (by rfl) ⟨9320, by rfl⟩ : syracuseStep 49709 = 18641) R18641
theorem R50165 : ∃ j : ℕ, syracuseStep^[j] 50165 = 1 := reachStep (stepEq 5 (by rfl) ⟨2351, by rfl⟩ : syracuseStep 50165 = 4703) R4703
theorem R52591 : ∃ j : ℕ, syracuseStep^[j] 52591 = 1 := reachStep (stepEq 1 (by rfl) ⟨39443, by rfl⟩ : syracuseStep 52591 = 78887) R78887
theorem R24407 : ∃ j : ℕ, syracuseStep^[j] 24407 = 1 := reachStep (stepEq 1 (by rfl) ⟨18305, by rfl⟩ : syracuseStep 24407 = 36611) R36611
theorem R24725 : ∃ j : ℕ, syracuseStep^[j] 24725 = 1 := reachStep (stepEq 6 (by rfl) ⟨579, by rfl⟩ : syracuseStep 24725 = 1159) R1159
theorem R24785 : ∃ j : ℕ, syracuseStep^[j] 24785 = 1 := reachStep (stepEq 2 (by rfl) ⟨9294, by rfl⟩ : syracuseStep 24785 = 18589) R18589
theorem R25211 : ∃ j : ℕ, syracuseStep^[j] 25211 = 1 := reachStep (stepEq 1 (by rfl) ⟨18908, by rfl⟩ : syracuseStep 25211 = 37817) R37817
theorem R25219 : ∃ j : ℕ, syracuseStep^[j] 25219 = 1 := reachStep (stepEq 1 (by rfl) ⟨18914, by rfl⟩ : syracuseStep 25219 = 37829) R37829
theorem R25271 : ∃ j : ℕ, syracuseStep^[j] 25271 = 1 := reachStep (stepEq 1 (by rfl) ⟨18953, by rfl⟩ : syracuseStep 25271 = 37907) R37907
theorem R30071 : ∃ j : ℕ, syracuseStep^[j] 30071 = 1 := reachStep (stepEq 1 (by rfl) ⟨22553, by rfl⟩ : syracuseStep 30071 = 45107) R45107
theorem R33047 : ∃ j : ℕ, syracuseStep^[j] 33047 = 1 := reachStep (stepEq 1 (by rfl) ⟨24785, by rfl⟩ : syracuseStep 33047 = 49571) R49571
theorem R283 : ∃ j : ℕ, syracuseStep^[j] 283 = 1 := reachStep (stepEq 1 (by rfl) ⟨212, by rfl⟩ : syracuseStep 283 = 425) R425
theorem R33139 : ∃ j : ℕ, syracuseStep^[j] 33139 = 1 := reachStep (stepEq 1 (by rfl) ⟨24854, by rfl⟩ : syracuseStep 33139 = 49709) R49709
theorem R505 : ∃ j : ℕ, syracuseStep^[j] 505 = 1 := reachStep (stepEq 2 (by rfl) ⟨189, by rfl⟩ : syracuseStep 505 = 379) R379
theorem R511 : ∃ j : ℕ, syracuseStep^[j] 511 = 1 := reachStep (stepEq 1 (by rfl) ⟨383, by rfl⟩ : syracuseStep 511 = 767) R767
theorem R519 : ∃ j : ℕ, syracuseStep^[j] 519 = 1 := reachStep (stepEq 1 (by rfl) ⟨389, by rfl⟩ : syracuseStep 519 = 779) R779
theorem R567 : ∃ j : ℕ, syracuseStep^[j] 567 = 1 := reachStep (stepEq 1 (by rfl) ⟨425, by rfl⟩ : syracuseStep 567 = 851) R851
theorem R33443 : ∃ j : ℕ, syracuseStep^[j] 33443 = 1 := reachStep (stepEq 1 (by rfl) ⟨25082, by rfl⟩ : syracuseStep 33443 = 50165) R50165
theorem R33625 : ∃ j : ℕ, syracuseStep^[j] 33625 = 1 := reachStep (stepEq 2 (by rfl) ⟨12609, by rfl⟩ : syracuseStep 33625 = 25219) R25219
theorem R1011 : ∃ j : ℕ, syracuseStep^[j] 1011 = 1 := reachStep (stepEq 1 (by rfl) ⟨758, by rfl⟩ : syracuseStep 1011 = 1517) R1517
theorem R1019 : ∃ j : ℕ, syracuseStep^[j] 1019 = 1 := reachStep (stepEq 1 (by rfl) ⟨764, by rfl⟩ : syracuseStep 1019 = 1529) R1529
theorem R1023 : ∃ j : ℕ, syracuseStep^[j] 1023 = 1 := reachStep (stepEq 1 (by rfl) ⟨767, by rfl⟩ : syracuseStep 1023 = 1535) R1535
theorem R1039 : ∃ j : ℕ, syracuseStep^[j] 1039 = 1 := reachStep (stepEq 1 (by rfl) ⟨779, by rfl⟩ : syracuseStep 1039 = 1559) R1559
theorem R1049 : ∃ j : ℕ, syracuseStep^[j] 1049 = 1 := reachStep (stepEq 2 (by rfl) ⟨393, by rfl⟩ : syracuseStep 1049 = 787) R787
theorem R1067 : ∃ j : ℕ, syracuseStep^[j] 1067 = 1 := reachStep (stepEq 1 (by rfl) ⟨800, by rfl⟩ : syracuseStep 1067 = 1601) R1601
theorem R1133 : ∃ j : ℕ, syracuseStep^[j] 1133 = 1 := reachStep (stepEq 3 (by rfl) ⟨212, by rfl⟩ : syracuseStep 1133 = 425) R425
theorem R1135 : ∃ j : ℕ, syracuseStep^[j] 1135 = 1 := reachStep (stepEq 1 (by rfl) ⟨851, by rfl⟩ : syracuseStep 1135 = 1703) R1703
theorem R133015 : ∃ j : ℕ, syracuseStep^[j] 133015 = 1 := reachStep (stepEq 1 (by rfl) ⟨99761, by rfl⟩ : syracuseStep 133015 = 199523) R199523
theorem R2021 : ∃ j : ℕ, syracuseStep^[j] 2021 = 1 := reachStep (stepEq 4 (by rfl) ⟨189, by rfl⟩ : syracuseStep 2021 = 379) R379
theorem R2031 : ∃ j : ℕ, syracuseStep^[j] 2031 = 1 := reachStep (stepEq 1 (by rfl) ⟨1523, by rfl⟩ : syracuseStep 2031 = 3047) R3047
theorem R2039 : ∃ j : ℕ, syracuseStep^[j] 2039 = 1 := reachStep (stepEq 1 (by rfl) ⟨1529, by rfl⟩ : syracuseStep 2039 = 3059) R3059
theorem R2041 : ∃ j : ℕ, syracuseStep^[j] 2041 = 1 := reachStep (stepEq 2 (by rfl) ⟨765, by rfl⟩ : syracuseStep 2041 = 1531) R1531
theorem R2045 : ∃ j : ℕ, syracuseStep^[j] 2045 = 1 := reachStep (stepEq 3 (by rfl) ⟨383, by rfl⟩ : syracuseStep 2045 = 767) R767
theorem R2077 : ∃ j : ℕ, syracuseStep^[j] 2077 = 1 := reachStep (stepEq 3 (by rfl) ⟨389, by rfl⟩ : syracuseStep 2077 = 779) R779
theorem R2081 : ∃ j : ℕ, syracuseStep^[j] 2081 = 1 := reachStep (stepEq 2 (by rfl) ⟨780, by rfl⟩ : syracuseStep 2081 = 1561) R1561
theorem R2089 : ∃ j : ℕ, syracuseStep^[j] 2089 = 1 := reachStep (stepEq 2 (by rfl) ⟨783, by rfl⟩ : syracuseStep 2089 = 1567) R1567
theorem R2097 : ∃ j : ℕ, syracuseStep^[j] 2097 = 1 := reachStep (stepEq 2 (by rfl) ⟨786, by rfl⟩ : syracuseStep 2097 = 1573) R1573
theorem R2099 : ∃ j : ℕ, syracuseStep^[j] 2099 = 1 := reachStep (stepEq 1 (by rfl) ⟨1574, by rfl⟩ : syracuseStep 2099 = 3149) R3149
theorem R2135 : ∃ j : ℕ, syracuseStep^[j] 2135 = 1 := reachStep (stepEq 1 (by rfl) ⟨1601, by rfl⟩ : syracuseStep 2135 = 3203) R3203
theorem R2137 : ∃ j : ℕ, syracuseStep^[j] 2137 = 1 := reachStep (stepEq 2 (by rfl) ⟨801, by rfl⟩ : syracuseStep 2137 = 1603) R1603
theorem R2265 : ∃ j : ℕ, syracuseStep^[j] 2265 = 1 := reachStep (stepEq 2 (by rfl) ⟨849, by rfl⟩ : syracuseStep 2265 = 1699) R1699
theorem R2269 : ∃ j : ℕ, syracuseStep^[j] 2269 = 1 := reachStep (stepEq 3 (by rfl) ⟨425, by rfl⟩ : syracuseStep 2269 = 851) R851
theorem R2271 : ∃ j : ℕ, syracuseStep^[j] 2271 = 1 := reachStep (stepEq 1 (by rfl) ⟨1703, by rfl⟩ : syracuseStep 2271 = 3407) R3407
theorem R2503 : ∃ j : ℕ, syracuseStep^[j] 2503 = 1 := reachStep (stepEq 1 (by rfl) ⟨1877, by rfl⟩ : syracuseStep 2503 = 3755) R3755
theorem R4045 : ∃ j : ℕ, syracuseStep^[j] 4045 = 1 := reachStep (stepEq 3 (by rfl) ⟨758, by rfl⟩ : syracuseStep 4045 = 1517) R1517
theorem R4049 : ∃ j : ℕ, syracuseStep^[j] 4049 = 1 := reachStep (stepEq 2 (by rfl) ⟨1518, by rfl⟩ : syracuseStep 4049 = 3037) R3037
theorem R4059 : ∃ j : ℕ, syracuseStep^[j] 4059 = 1 := reachStep (stepEq 1 (by rfl) ⟨3044, by rfl⟩ : syracuseStep 4059 = 6089) R6089
theorem R4063 : ∃ j : ℕ, syracuseStep^[j] 4063 = 1 := reachStep (stepEq 1 (by rfl) ⟨3047, by rfl⟩ : syracuseStep 4063 = 6095) R6095
theorem R4077 : ∃ j : ℕ, syracuseStep^[j] 4077 = 1 := reachStep (stepEq 3 (by rfl) ⟨764, by rfl⟩ : syracuseStep 4077 = 1529) R1529
theorem R4079 : ∃ j : ℕ, syracuseStep^[j] 4079 = 1 := reachStep (stepEq 1 (by rfl) ⟨3059, by rfl⟩ : syracuseStep 4079 = 6119) R6119
theorem R4083 : ∃ j : ℕ, syracuseStep^[j] 4083 = 1 := reachStep (stepEq 1 (by rfl) ⟨3062, by rfl⟩ : syracuseStep 4083 = 6125) R6125
theorem R4089 : ∃ j : ℕ, syracuseStep^[j] 4089 = 1 := reachStep (stepEq 2 (by rfl) ⟨1533, by rfl⟩ : syracuseStep 4089 = 3067) R3067
theorem R4093 : ∃ j : ℕ, syracuseStep^[j] 4093 = 1 := reachStep (stepEq 3 (by rfl) ⟨767, by rfl⟩ : syracuseStep 4093 = 1535) R1535
theorem R4121 : ∃ j : ℕ, syracuseStep^[j] 4121 = 1 := reachStep (stepEq 2 (by rfl) ⟨1545, by rfl⟩ : syracuseStep 4121 = 3091) R3091
theorem R4143 : ∃ j : ℕ, syracuseStep^[j] 4143 = 1 := reachStep (stepEq 1 (by rfl) ⟨3107, by rfl⟩ : syracuseStep 4143 = 6215) R6215
theorem R4153 : ∃ j : ℕ, syracuseStep^[j] 4153 = 1 := reachStep (stepEq 2 (by rfl) ⟨1557, by rfl⟩ : syracuseStep 4153 = 3115) R3115
theorem R4155 : ∃ j : ℕ, syracuseStep^[j] 4155 = 1 := reachStep (stepEq 1 (by rfl) ⟨3116, by rfl⟩ : syracuseStep 4155 = 6233) R6233
theorem R4157 : ∃ j : ℕ, syracuseStep^[j] 4157 = 1 := reachStep (stepEq 3 (by rfl) ⟨779, by rfl⟩ : syracuseStep 4157 = 1559) R1559
theorem R4161 : ∃ j : ℕ, syracuseStep^[j] 4161 = 1 := reachStep (stepEq 2 (by rfl) ⟨1560, by rfl⟩ : syracuseStep 4161 = 3121) R3121
theorem R4163 : ∃ j : ℕ, syracuseStep^[j] 4163 = 1 := reachStep (stepEq 1 (by rfl) ⟨3122, by rfl⟩ : syracuseStep 4163 = 6245) R6245
theorem R4179 : ∃ j : ℕ, syracuseStep^[j] 4179 = 1 := reachStep (stepEq 1 (by rfl) ⟨3134, by rfl⟩ : syracuseStep 4179 = 6269) R6269
theorem R4187 : ∃ j : ℕ, syracuseStep^[j] 4187 = 1 := reachStep (stepEq 1 (by rfl) ⟨3140, by rfl⟩ : syracuseStep 4187 = 6281) R6281
theorem R4193 : ∃ j : ℕ, syracuseStep^[j] 4193 = 1 := reachStep (stepEq 2 (by rfl) ⟨1572, by rfl⟩ : syracuseStep 4193 = 3145) R3145
theorem R4195 : ∃ j : ℕ, syracuseStep^[j] 4195 = 1 := reachStep (stepEq 1 (by rfl) ⟨3146, by rfl⟩ : syracuseStep 4195 = 6293) R6293
theorem R4197 : ∃ j : ℕ, syracuseStep^[j] 4197 = 1 := reachStep (stepEq 4 (by rfl) ⟨393, by rfl⟩ : syracuseStep 4197 = 787) R787
theorem R4199 : ∃ j : ℕ, syracuseStep^[j] 4199 = 1 := reachStep (stepEq 1 (by rfl) ⟨3149, by rfl⟩ : syracuseStep 4199 = 6299) R6299
theorem R4201 : ∃ j : ℕ, syracuseStep^[j] 4201 = 1 := reachStep (stepEq 2 (by rfl) ⟨1575, by rfl⟩ : syracuseStep 4201 = 3151) R3151
theorem R4203 : ∃ j : ℕ, syracuseStep^[j] 4203 = 1 := reachStep (stepEq 1 (by rfl) ⟨3152, by rfl⟩ : syracuseStep 4203 = 6305) R6305
theorem R4269 : ∃ j : ℕ, syracuseStep^[j] 4269 = 1 := reachStep (stepEq 3 (by rfl) ⟨800, by rfl⟩ : syracuseStep 4269 = 1601) R1601
theorem R4273 : ∃ j : ℕ, syracuseStep^[j] 4273 = 1 := reachStep (stepEq 2 (by rfl) ⟨1602, by rfl⟩ : syracuseStep 4273 = 3205) R3205
theorem R4275 : ∃ j : ℕ, syracuseStep^[j] 4275 = 1 := reachStep (stepEq 1 (by rfl) ⟨3206, by rfl⟩ : syracuseStep 4275 = 6413) R6413
theorem R4299 : ∃ j : ℕ, syracuseStep^[j] 4299 = 1 := reachStep (stepEq 1 (by rfl) ⟨3224, by rfl⟩ : syracuseStep 4299 = 6449) R6449
theorem R4335 : ∃ j : ℕ, syracuseStep^[j] 4335 = 1 := reachStep (stepEq 1 (by rfl) ⟨3251, by rfl⟩ : syracuseStep 4335 = 6503) R6503
theorem R4529 : ∃ j : ℕ, syracuseStep^[j] 4529 = 1 := reachStep (stepEq 2 (by rfl) ⟨1698, by rfl⟩ : syracuseStep 4529 = 3397) R3397
theorem R4531 : ∃ j : ℕ, syracuseStep^[j] 4531 = 1 := reachStep (stepEq 1 (by rfl) ⟨3398, by rfl⟩ : syracuseStep 4531 = 6797) R6797
theorem R4533 : ∃ j : ℕ, syracuseStep^[j] 4533 = 1 := reachStep (stepEq 5 (by rfl) ⟨212, by rfl⟩ : syracuseStep 4533 = 425) R425
theorem R4537 : ∃ j : ℕ, syracuseStep^[j] 4537 = 1 := reachStep (stepEq 2 (by rfl) ⟨1701, by rfl⟩ : syracuseStep 4537 = 3403) R3403
theorem R4541 : ∃ j : ℕ, syracuseStep^[j] 4541 = 1 := reachStep (stepEq 3 (by rfl) ⟨851, by rfl⟩ : syracuseStep 4541 = 1703) R1703
theorem R70121 : ∃ j : ℕ, syracuseStep^[j] 70121 = 1 := reachStep (stepEq 2 (by rfl) ⟨26295, by rfl⟩ : syracuseStep 70121 = 52591) R52591
theorem R5001 : ∃ j : ℕ, syracuseStep^[j] 5001 = 1 := reachStep (stepEq 2 (by rfl) ⟨1875, by rfl⟩ : syracuseStep 5001 = 3751) R3751
theorem R5007 : ∃ j : ℕ, syracuseStep^[j] 5007 = 1 := reachStep (stepEq 1 (by rfl) ⟨3755, by rfl⟩ : syracuseStep 5007 = 7511) R7511
theorem R5019 : ∃ j : ℕ, syracuseStep^[j] 5019 = 1 := reachStep (stepEq 1 (by rfl) ⟨3764, by rfl⟩ : syracuseStep 5019 = 7529) R7529
theorem R8099 : ∃ j : ℕ, syracuseStep^[j] 8099 = 1 := reachStep (stepEq 1 (by rfl) ⟨6074, by rfl⟩ : syracuseStep 8099 = 12149) R12149
theorem R8111 : ∃ j : ℕ, syracuseStep^[j] 8111 = 1 := reachStep (stepEq 1 (by rfl) ⟨6083, by rfl⟩ : syracuseStep 8111 = 12167) R12167
theorem R8135 : ∃ j : ℕ, syracuseStep^[j] 8135 = 1 := reachStep (stepEq 1 (by rfl) ⟨6101, by rfl⟩ : syracuseStep 8135 = 12203) R12203
theorem R8159 : ∃ j : ℕ, syracuseStep^[j] 8159 = 1 := reachStep (stepEq 1 (by rfl) ⟨6119, by rfl⟩ : syracuseStep 8159 = 12239) R12239
theorem R8165 : ∃ j : ℕ, syracuseStep^[j] 8165 = 1 := reachStep (stepEq 4 (by rfl) ⟨765, by rfl⟩ : syracuseStep 8165 = 1531) R1531
theorem R8243 : ∃ j : ℕ, syracuseStep^[j] 8243 = 1 := reachStep (stepEq 1 (by rfl) ⟨6182, by rfl⟩ : syracuseStep 8243 = 12365) R12365
theorem R8249 : ∃ j : ℕ, syracuseStep^[j] 8249 = 1 := reachStep (stepEq 2 (by rfl) ⟨3093, by rfl⟩ : syracuseStep 8249 = 6187) R6187
theorem R8309 : ∃ j : ℕ, syracuseStep^[j] 8309 = 1 := reachStep (stepEq 5 (by rfl) ⟨389, by rfl⟩ : syracuseStep 8309 = 779) R779
theorem R8327 : ∃ j : ℕ, syracuseStep^[j] 8327 = 1 := reachStep (stepEq 1 (by rfl) ⟨6245, by rfl⟩ : syracuseStep 8327 = 12491) R12491
theorem R8357 : ∃ j : ℕ, syracuseStep^[j] 8357 = 1 := reachStep (stepEq 4 (by rfl) ⟨783, by rfl⟩ : syracuseStep 8357 = 1567) R1567
theorem R8363 : ∃ j : ℕ, syracuseStep^[j] 8363 = 1 := reachStep (stepEq 1 (by rfl) ⟨6272, by rfl⟩ : syracuseStep 8363 = 12545) R12545
theorem R8375 : ∃ j : ℕ, syracuseStep^[j] 8375 = 1 := reachStep (stepEq 1 (by rfl) ⟨6281, by rfl⟩ : syracuseStep 8375 = 12563) R12563
theorem R8387 : ∃ j : ℕ, syracuseStep^[j] 8387 = 1 := reachStep (stepEq 1 (by rfl) ⟨6290, by rfl⟩ : syracuseStep 8387 = 12581) R12581
theorem R8399 : ∃ j : ℕ, syracuseStep^[j] 8399 = 1 := reachStep (stepEq 1 (by rfl) ⟨6299, by rfl⟩ : syracuseStep 8399 = 12599) R12599
theorem R8411 : ∃ j : ℕ, syracuseStep^[j] 8411 = 1 := reachStep (stepEq 1 (by rfl) ⟨6308, by rfl⟩ : syracuseStep 8411 = 12617) R12617
theorem R8423 : ∃ j : ℕ, syracuseStep^[j] 8423 = 1 := reachStep (stepEq 1 (by rfl) ⟨6317, by rfl⟩ : syracuseStep 8423 = 12635) R12635
theorem R8489 : ∃ j : ℕ, syracuseStep^[j] 8489 = 1 := reachStep (stepEq 2 (by rfl) ⟨3183, by rfl⟩ : syracuseStep 8489 = 6367) R6367
theorem R8549 : ∃ j : ℕ, syracuseStep^[j] 8549 = 1 := reachStep (stepEq 4 (by rfl) ⟨801, by rfl⟩ : syracuseStep 8549 = 1603) R1603
theorem R8599 : ∃ j : ℕ, syracuseStep^[j] 8599 = 1 := reachStep (stepEq 1 (by rfl) ⟨6449, by rfl⟩ : syracuseStep 8599 = 12899) R12899
theorem R8761 : ∃ j : ℕ, syracuseStep^[j] 8761 = 1 := reachStep (stepEq 2 (by rfl) ⟨3285, by rfl⟩ : syracuseStep 8761 = 6571) R6571
theorem R9059 : ∃ j : ℕ, syracuseStep^[j] 9059 = 1 := reachStep (stepEq 1 (by rfl) ⟨6794, by rfl⟩ : syracuseStep 9059 = 13589) R13589
theorem R9073 : ∃ j : ℕ, syracuseStep^[j] 9073 = 1 := reachStep (stepEq 2 (by rfl) ⟨3402, by rfl⟩ : syracuseStep 9073 = 6805) R6805
theorem R9077 : ∃ j : ℕ, syracuseStep^[j] 9077 = 1 := reachStep (stepEq 5 (by rfl) ⟨425, by rfl⟩ : syracuseStep 9077 = 851) R851
theorem R9085 : ∃ j : ℕ, syracuseStep^[j] 9085 = 1 := reachStep (stepEq 3 (by rfl) ⟨1703, by rfl⟩ : syracuseStep 9085 = 3407) R3407
theorem R9119 : ∃ j : ℕ, syracuseStep^[j] 9119 = 1 := reachStep (stepEq 1 (by rfl) ⟨6839, by rfl⟩ : syracuseStep 9119 = 13679) R13679
theorem R9995 : ∃ j : ℕ, syracuseStep^[j] 9995 = 1 := reachStep (stepEq 1 (by rfl) ⟨7496, by rfl⟩ : syracuseStep 9995 = 14993) R14993
theorem R10003 : ∃ j : ℕ, syracuseStep^[j] 10003 = 1 := reachStep (stepEq 1 (by rfl) ⟨7502, by rfl⟩ : syracuseStep 10003 = 15005) R15005
theorem R10013 : ∃ j : ℕ, syracuseStep^[j] 10013 = 1 := reachStep (stepEq 3 (by rfl) ⟨1877, by rfl⟩ : syracuseStep 10013 = 3755) R3755
theorem R10039 : ∃ j : ℕ, syracuseStep^[j] 10039 = 1 := reachStep (stepEq 1 (by rfl) ⟨7529, by rfl⟩ : syracuseStep 10039 = 15059) R15059
theorem R16253 : ∃ j : ℕ, syracuseStep^[j] 16253 = 1 := reachStep (stepEq 3 (by rfl) ⟨3047, by rfl⟩ : syracuseStep 16253 = 6095) R6095
theorem R16271 : ∃ j : ℕ, syracuseStep^[j] 16271 = 1 := reachStep (stepEq 1 (by rfl) ⟨12203, by rfl⟩ : syracuseStep 16271 = 24407) R24407
theorem R16321 : ∃ j : ℕ, syracuseStep^[j] 16321 = 1 := reachStep (stepEq 2 (by rfl) ⟨6120, by rfl⟩ : syracuseStep 16321 = 12241) R12241
theorem R16357 : ∃ j : ℕ, syracuseStep^[j] 16357 = 1 := reachStep (stepEq 4 (by rfl) ⟨1533, by rfl⟩ : syracuseStep 16357 = 3067) R3067
theorem R16483 : ∃ j : ℕ, syracuseStep^[j] 16483 = 1 := reachStep (stepEq 1 (by rfl) ⟨12362, by rfl⟩ : syracuseStep 16483 = 24725) R24725
theorem R16523 : ∃ j : ℕ, syracuseStep^[j] 16523 = 1 := reachStep (stepEq 1 (by rfl) ⟨12392, by rfl⟩ : syracuseStep 16523 = 24785) R24785
theorem R16625 : ∃ j : ℕ, syracuseStep^[j] 16625 = 1 := reachStep (stepEq 2 (by rfl) ⟨6234, by rfl⟩ : syracuseStep 16625 = 12469) R12469
theorem R16645 : ∃ j : ℕ, syracuseStep^[j] 16645 = 1 := reachStep (stepEq 4 (by rfl) ⟨1560, by rfl⟩ : syracuseStep 16645 = 3121) R3121
theorem R16793 : ∃ j : ℕ, syracuseStep^[j] 16793 = 1 := reachStep (stepEq 2 (by rfl) ⟨6297, by rfl⟩ : syracuseStep 16793 = 12595) R12595
theorem R16807 : ∃ j : ℕ, syracuseStep^[j] 16807 = 1 := reachStep (stepEq 1 (by rfl) ⟨12605, by rfl⟩ : syracuseStep 16807 = 25211) R25211
theorem R16847 : ∃ j : ℕ, syracuseStep^[j] 16847 = 1 := reachStep (stepEq 1 (by rfl) ⟨12635, by rfl⟩ : syracuseStep 16847 = 25271) R25271
theorem R18569 : ∃ j : ℕ, syracuseStep^[j] 18569 = 1 := reachStep (stepEq 2 (by rfl) ⟨6963, by rfl⟩ : syracuseStep 18569 = 13927) R13927
theorem R20047 : ∃ j : ℕ, syracuseStep^[j] 20047 = 1 := reachStep (stepEq 1 (by rfl) ⟨15035, by rfl⟩ : syracuseStep 20047 = 30071) R30071
theorem R32395 : ∃ j : ℕ, syracuseStep^[j] 32395 = 1 := reachStep (stepEq 1 (by rfl) ⟨24296, by rfl⟩ : syracuseStep 32395 = 48593) R48593
theorem R377 : ∃ j : ℕ, syracuseStep^[j] 377 = 1 := reachStep (stepEq 2 (by rfl) ⟨141, by rfl⟩ : syracuseStep 377 = 283) R283
theorem R673 : ∃ j : ℕ, syracuseStep^[j] 673 = 1 := reachStep (stepEq 2 (by rfl) ⟨252, by rfl⟩ : syracuseStep 673 = 505) R505
theorem R679 : ∃ j : ℕ, syracuseStep^[j] 679 = 1 := reachStep (stepEq 1 (by rfl) ⟨509, by rfl⟩ : syracuseStep 679 = 1019) R1019
theorem R681 : ∃ j : ℕ, syracuseStep^[j] 681 = 1 := reachStep (stepEq 2 (by rfl) ⟨255, by rfl⟩ : syracuseStep 681 = 511) R511
theorem R699 : ∃ j : ℕ, syracuseStep^[j] 699 = 1 := reachStep (stepEq 1 (by rfl) ⟨524, by rfl⟩ : syracuseStep 699 = 1049) R1049
theorem R711 : ∃ j : ℕ, syracuseStep^[j] 711 = 1 := reachStep (stepEq 1 (by rfl) ⟨533, by rfl⟩ : syracuseStep 711 = 1067) R1067
theorem R755 : ∃ j : ℕ, syracuseStep^[j] 755 = 1 := reachStep (stepEq 1 (by rfl) ⟨566, by rfl⟩ : syracuseStep 755 = 1133) R1133
theorem R1347 : ∃ j : ℕ, syracuseStep^[j] 1347 = 1 := reachStep (stepEq 1 (by rfl) ⟨1010, by rfl⟩ : syracuseStep 1347 = 2021) R2021
theorem R1359 : ∃ j : ℕ, syracuseStep^[j] 1359 = 1 := reachStep (stepEq 1 (by rfl) ⟨1019, by rfl⟩ : syracuseStep 1359 = 2039) R2039
theorem R1363 : ∃ j : ℕ, syracuseStep^[j] 1363 = 1 := reachStep (stepEq 1 (by rfl) ⟨1022, by rfl⟩ : syracuseStep 1363 = 2045) R2045
theorem R1385 : ∃ j : ℕ, syracuseStep^[j] 1385 = 1 := reachStep (stepEq 2 (by rfl) ⟨519, by rfl⟩ : syracuseStep 1385 = 1039) R1039
theorem R1387 : ∃ j : ℕ, syracuseStep^[j] 1387 = 1 := reachStep (stepEq 1 (by rfl) ⟨1040, by rfl⟩ : syracuseStep 1387 = 2081) R2081
theorem R1399 : ∃ j : ℕ, syracuseStep^[j] 1399 = 1 := reachStep (stepEq 1 (by rfl) ⟨1049, by rfl⟩ : syracuseStep 1399 = 2099) R2099
theorem R1423 : ∃ j : ℕ, syracuseStep^[j] 1423 = 1 := reachStep (stepEq 1 (by rfl) ⟨1067, by rfl⟩ : syracuseStep 1423 = 2135) R2135
theorem R1509 : ∃ j : ℕ, syracuseStep^[j] 1509 = 1 := reachStep (stepEq 4 (by rfl) ⟨141, by rfl⟩ : syracuseStep 1509 = 283) R283
theorem R1513 : ∃ j : ℕ, syracuseStep^[j] 1513 = 1 := reachStep (stepEq 2 (by rfl) ⟨567, by rfl⟩ : syracuseStep 1513 = 1135) R1135
theorem R2693 : ∃ j : ℕ, syracuseStep^[j] 2693 = 1 := reachStep (stepEq 4 (by rfl) ⟨252, by rfl⟩ : syracuseStep 2693 = 505) R505
theorem R2699 : ∃ j : ℕ, syracuseStep^[j] 2699 = 1 := reachStep (stepEq 1 (by rfl) ⟨2024, by rfl⟩ : syracuseStep 2699 = 4049) R4049
theorem R2717 : ∃ j : ℕ, syracuseStep^[j] 2717 = 1 := reachStep (stepEq 3 (by rfl) ⟨509, by rfl⟩ : syracuseStep 2717 = 1019) R1019
theorem R2719 : ∃ j : ℕ, syracuseStep^[j] 2719 = 1 := reachStep (stepEq 1 (by rfl) ⟨2039, by rfl⟩ : syracuseStep 2719 = 4079) R4079
theorem R2721 : ∃ j : ℕ, syracuseStep^[j] 2721 = 1 := reachStep (stepEq 2 (by rfl) ⟨1020, by rfl⟩ : syracuseStep 2721 = 2041) R2041
theorem R2725 : ∃ j : ℕ, syracuseStep^[j] 2725 = 1 := reachStep (stepEq 4 (by rfl) ⟨255, by rfl⟩ : syracuseStep 2725 = 511) R511
theorem R2747 : ∃ j : ℕ, syracuseStep^[j] 2747 = 1 := reachStep (stepEq 1 (by rfl) ⟨2060, by rfl⟩ : syracuseStep 2747 = 4121) R4121
theorem R2769 : ∃ j : ℕ, syracuseStep^[j] 2769 = 1 := reachStep (stepEq 2 (by rfl) ⟨1038, by rfl⟩ : syracuseStep 2769 = 2077) R2077
theorem R2771 : ∃ j : ℕ, syracuseStep^[j] 2771 = 1 := reachStep (stepEq 1 (by rfl) ⟨2078, by rfl⟩ : syracuseStep 2771 = 4157) R4157
theorem R2775 : ∃ j : ℕ, syracuseStep^[j] 2775 = 1 := reachStep (stepEq 1 (by rfl) ⟨2081, by rfl⟩ : syracuseStep 2775 = 4163) R4163
theorem R2785 : ∃ j : ℕ, syracuseStep^[j] 2785 = 1 := reachStep (stepEq 2 (by rfl) ⟨1044, by rfl⟩ : syracuseStep 2785 = 2089) R2089
theorem R2791 : ∃ j : ℕ, syracuseStep^[j] 2791 = 1 := reachStep (stepEq 1 (by rfl) ⟨2093, by rfl⟩ : syracuseStep 2791 = 4187) R4187
theorem R2795 : ∃ j : ℕ, syracuseStep^[j] 2795 = 1 := reachStep (stepEq 1 (by rfl) ⟨2096, by rfl⟩ : syracuseStep 2795 = 4193) R4193
theorem R2797 : ∃ j : ℕ, syracuseStep^[j] 2797 = 1 := reachStep (stepEq 3 (by rfl) ⟨524, by rfl⟩ : syracuseStep 2797 = 1049) R1049
theorem R2799 : ∃ j : ℕ, syracuseStep^[j] 2799 = 1 := reachStep (stepEq 1 (by rfl) ⟨2099, by rfl⟩ : syracuseStep 2799 = 4199) R4199
theorem R2845 : ∃ j : ℕ, syracuseStep^[j] 2845 = 1 := reachStep (stepEq 3 (by rfl) ⟨533, by rfl⟩ : syracuseStep 2845 = 1067) R1067
theorem R2849 : ∃ j : ℕ, syracuseStep^[j] 2849 = 1 := reachStep (stepEq 2 (by rfl) ⟨1068, by rfl⟩ : syracuseStep 2849 = 2137) R2137
theorem R3019 : ∃ j : ℕ, syracuseStep^[j] 3019 = 1 := reachStep (stepEq 1 (by rfl) ⟨2264, by rfl⟩ : syracuseStep 3019 = 4529) R4529
theorem R3021 : ∃ j : ℕ, syracuseStep^[j] 3021 = 1 := reachStep (stepEq 3 (by rfl) ⟨566, by rfl⟩ : syracuseStep 3021 = 1133) R1133
theorem R3025 : ∃ j : ℕ, syracuseStep^[j] 3025 = 1 := reachStep (stepEq 2 (by rfl) ⟨1134, by rfl⟩ : syracuseStep 3025 = 2269) R2269
theorem R3027 : ∃ j : ℕ, syracuseStep^[j] 3027 = 1 := reachStep (stepEq 1 (by rfl) ⟨2270, by rfl⟩ : syracuseStep 3027 = 4541) R4541
theorem R3337 : ∃ j : ℕ, syracuseStep^[j] 3337 = 1 := reachStep (stepEq 2 (by rfl) ⟨1251, by rfl⟩ : syracuseStep 3337 = 2503) R2503
theorem R5389 : ∃ j : ℕ, syracuseStep^[j] 5389 = 1 := reachStep (stepEq 3 (by rfl) ⟨1010, by rfl⟩ : syracuseStep 5389 = 2021) R2021
theorem R5393 : ∃ j : ℕ, syracuseStep^[j] 5393 = 1 := reachStep (stepEq 2 (by rfl) ⟨2022, by rfl⟩ : syracuseStep 5393 = 4045) R4045
theorem R5399 : ∃ j : ℕ, syracuseStep^[j] 5399 = 1 := reachStep (stepEq 1 (by rfl) ⟨4049, by rfl⟩ : syracuseStep 5399 = 8099) R8099
theorem R5407 : ∃ j : ℕ, syracuseStep^[j] 5407 = 1 := reachStep (stepEq 1 (by rfl) ⟨4055, by rfl⟩ : syracuseStep 5407 = 8111) R8111
theorem R5417 : ∃ j : ℕ, syracuseStep^[j] 5417 = 1 := reachStep (stepEq 2 (by rfl) ⟨2031, by rfl⟩ : syracuseStep 5417 = 4063) R4063
theorem R5423 : ∃ j : ℕ, syracuseStep^[j] 5423 = 1 := reachStep (stepEq 1 (by rfl) ⟨4067, by rfl⟩ : syracuseStep 5423 = 8135) R8135
theorem R5437 : ∃ j : ℕ, syracuseStep^[j] 5437 = 1 := reachStep (stepEq 3 (by rfl) ⟨1019, by rfl⟩ : syracuseStep 5437 = 2039) R2039
theorem R5439 : ∃ j : ℕ, syracuseStep^[j] 5439 = 1 := reachStep (stepEq 1 (by rfl) ⟨4079, by rfl⟩ : syracuseStep 5439 = 8159) R8159
theorem R5443 : ∃ j : ℕ, syracuseStep^[j] 5443 = 1 := reachStep (stepEq 1 (by rfl) ⟨4082, by rfl⟩ : syracuseStep 5443 = 8165) R8165
theorem R5453 : ∃ j : ℕ, syracuseStep^[j] 5453 = 1 := reachStep (stepEq 3 (by rfl) ⟨1022, by rfl⟩ : syracuseStep 5453 = 2045) R2045
theorem R5457 : ∃ j : ℕ, syracuseStep^[j] 5457 = 1 := reachStep (stepEq 2 (by rfl) ⟨2046, by rfl⟩ : syracuseStep 5457 = 4093) R4093
theorem R5495 : ∃ j : ℕ, syracuseStep^[j] 5495 = 1 := reachStep (stepEq 1 (by rfl) ⟨4121, by rfl⟩ : syracuseStep 5495 = 8243) R8243
theorem R5499 : ∃ j : ℕ, syracuseStep^[j] 5499 = 1 := reachStep (stepEq 1 (by rfl) ⟨4124, by rfl⟩ : syracuseStep 5499 = 8249) R8249
theorem R5537 : ∃ j : ℕ, syracuseStep^[j] 5537 = 1 := reachStep (stepEq 2 (by rfl) ⟨2076, by rfl⟩ : syracuseStep 5537 = 4153) R4153
theorem R5539 : ∃ j : ℕ, syracuseStep^[j] 5539 = 1 := reachStep (stepEq 1 (by rfl) ⟨4154, by rfl⟩ : syracuseStep 5539 = 8309) R8309
theorem R5541 : ∃ j : ℕ, syracuseStep^[j] 5541 = 1 := reachStep (stepEq 4 (by rfl) ⟨519, by rfl⟩ : syracuseStep 5541 = 1039) R1039
theorem R5549 : ∃ j : ℕ, syracuseStep^[j] 5549 = 1 := reachStep (stepEq 3 (by rfl) ⟨1040, by rfl⟩ : syracuseStep 5549 = 2081) R2081
theorem R5551 : ∃ j : ℕ, syracuseStep^[j] 5551 = 1 := reachStep (stepEq 1 (by rfl) ⟨4163, by rfl⟩ : syracuseStep 5551 = 8327) R8327
theorem R5571 : ∃ j : ℕ, syracuseStep^[j] 5571 = 1 := reachStep (stepEq 1 (by rfl) ⟨4178, by rfl⟩ : syracuseStep 5571 = 8357) R8357
theorem R5575 : ∃ j : ℕ, syracuseStep^[j] 5575 = 1 := reachStep (stepEq 1 (by rfl) ⟨4181, by rfl⟩ : syracuseStep 5575 = 8363) R8363
theorem R5583 : ∃ j : ℕ, syracuseStep^[j] 5583 = 1 := reachStep (stepEq 1 (by rfl) ⟨4187, by rfl⟩ : syracuseStep 5583 = 8375) R8375
theorem R5591 : ∃ j : ℕ, syracuseStep^[j] 5591 = 1 := reachStep (stepEq 1 (by rfl) ⟨4193, by rfl⟩ : syracuseStep 5591 = 8387) R8387
theorem R5593 : ∃ j : ℕ, syracuseStep^[j] 5593 = 1 := reachStep (stepEq 2 (by rfl) ⟨2097, by rfl⟩ : syracuseStep 5593 = 4195) R4195
theorem R5597 : ∃ j : ℕ, syracuseStep^[j] 5597 = 1 := reachStep (stepEq 3 (by rfl) ⟨1049, by rfl⟩ : syracuseStep 5597 = 2099) R2099
theorem R5599 : ∃ j : ℕ, syracuseStep^[j] 5599 = 1 := reachStep (stepEq 1 (by rfl) ⟨4199, by rfl⟩ : syracuseStep 5599 = 8399) R8399
theorem R5601 : ∃ j : ℕ, syracuseStep^[j] 5601 = 1 := reachStep (stepEq 2 (by rfl) ⟨2100, by rfl⟩ : syracuseStep 5601 = 4201) R4201
theorem R5607 : ∃ j : ℕ, syracuseStep^[j] 5607 = 1 := reachStep (stepEq 1 (by rfl) ⟨4205, by rfl⟩ : syracuseStep 5607 = 8411) R8411
theorem R5615 : ∃ j : ℕ, syracuseStep^[j] 5615 = 1 := reachStep (stepEq 1 (by rfl) ⟨4211, by rfl⟩ : syracuseStep 5615 = 8423) R8423
theorem R5659 : ∃ j : ℕ, syracuseStep^[j] 5659 = 1 := reachStep (stepEq 1 (by rfl) ⟨4244, by rfl⟩ : syracuseStep 5659 = 8489) R8489
theorem R5693 : ∃ j : ℕ, syracuseStep^[j] 5693 = 1 := reachStep (stepEq 3 (by rfl) ⟨1067, by rfl⟩ : syracuseStep 5693 = 2135) R2135
theorem R5697 : ∃ j : ℕ, syracuseStep^[j] 5697 = 1 := reachStep (stepEq 2 (by rfl) ⟨2136, by rfl⟩ : syracuseStep 5697 = 4273) R4273
theorem R5699 : ∃ j : ℕ, syracuseStep^[j] 5699 = 1 := reachStep (stepEq 1 (by rfl) ⟨4274, by rfl⟩ : syracuseStep 5699 = 8549) R8549
theorem R6037 : ∃ j : ℕ, syracuseStep^[j] 6037 = 1 := reachStep (stepEq 6 (by rfl) ⟨141, by rfl⟩ : syracuseStep 6037 = 283) R283
theorem R6039 : ∃ j : ℕ, syracuseStep^[j] 6039 = 1 := reachStep (stepEq 1 (by rfl) ⟨4529, by rfl⟩ : syracuseStep 6039 = 9059) R9059
theorem R6041 : ∃ j : ℕ, syracuseStep^[j] 6041 = 1 := reachStep (stepEq 2 (by rfl) ⟨2265, by rfl⟩ : syracuseStep 6041 = 4531) R4531
theorem R6049 : ∃ j : ℕ, syracuseStep^[j] 6049 = 1 := reachStep (stepEq 2 (by rfl) ⟨2268, by rfl⟩ : syracuseStep 6049 = 4537) R4537
theorem R6051 : ∃ j : ℕ, syracuseStep^[j] 6051 = 1 := reachStep (stepEq 1 (by rfl) ⟨4538, by rfl⟩ : syracuseStep 6051 = 9077) R9077
theorem R6053 : ∃ j : ℕ, syracuseStep^[j] 6053 = 1 := reachStep (stepEq 4 (by rfl) ⟨567, by rfl⟩ : syracuseStep 6053 = 1135) R1135
theorem R6079 : ∃ j : ℕ, syracuseStep^[j] 6079 = 1 := reachStep (stepEq 1 (by rfl) ⟨4559, by rfl⟩ : syracuseStep 6079 = 9119) R9119
theorem R6663 : ∃ j : ℕ, syracuseStep^[j] 6663 = 1 := reachStep (stepEq 1 (by rfl) ⟨4997, by rfl⟩ : syracuseStep 6663 = 9995) R9995
theorem R6675 : ∃ j : ℕ, syracuseStep^[j] 6675 = 1 := reachStep (stepEq 1 (by rfl) ⟨5006, by rfl⟩ : syracuseStep 6675 = 10013) R10013
theorem R43193 : ∃ j : ℕ, syracuseStep^[j] 43193 = 1 := reachStep (stepEq 2 (by rfl) ⟨16197, by rfl⟩ : syracuseStep 43193 = 32395) R32395
theorem R10835 : ∃ j : ℕ, syracuseStep^[j] 10835 = 1 := reachStep (stepEq 1 (by rfl) ⟨8126, by rfl⟩ : syracuseStep 10835 = 16253) R16253
theorem R10847 : ∃ j : ℕ, syracuseStep^[j] 10847 = 1 := reachStep (stepEq 1 (by rfl) ⟨8135, by rfl⟩ : syracuseStep 10847 = 16271) R16271
theorem R10901 : ∃ j : ℕ, syracuseStep^[j] 10901 = 1 := reachStep (stepEq 6 (by rfl) ⟨255, by rfl⟩ : syracuseStep 10901 = 511) R511
theorem R11015 : ∃ j : ℕ, syracuseStep^[j] 11015 = 1 := reachStep (stepEq 1 (by rfl) ⟨8261, by rfl⟩ : syracuseStep 11015 = 16523) R16523
theorem R11083 : ∃ j : ℕ, syracuseStep^[j] 11083 = 1 := reachStep (stepEq 1 (by rfl) ⟨8312, by rfl⟩ : syracuseStep 11083 = 16625) R16625
theorem R11141 : ∃ j : ℕ, syracuseStep^[j] 11141 = 1 := reachStep (stepEq 4 (by rfl) ⟨1044, by rfl⟩ : syracuseStep 11141 = 2089) R2089
theorem R11195 : ∃ j : ℕ, syracuseStep^[j] 11195 = 1 := reachStep (stepEq 1 (by rfl) ⟨8396, by rfl⟩ : syracuseStep 11195 = 16793) R16793
theorem R11231 : ∃ j : ℕ, syracuseStep^[j] 11231 = 1 := reachStep (stepEq 1 (by rfl) ⟨8423, by rfl⟩ : syracuseStep 11231 = 16847) R16847
theorem R44185 : ∃ j : ℕ, syracuseStep^[j] 44185 = 1 := reachStep (stepEq 2 (by rfl) ⟨16569, by rfl⟩ : syracuseStep 44185 = 33139) R33139
theorem R11465 : ∃ j : ℕ, syracuseStep^[j] 11465 = 1 := reachStep (stepEq 2 (by rfl) ⟨4299, by rfl⟩ : syracuseStep 11465 = 8599) R8599
theorem R11681 : ∃ j : ℕ, syracuseStep^[j] 11681 = 1 := reachStep (stepEq 2 (by rfl) ⟨4380, by rfl⟩ : syracuseStep 11681 = 8761) R8761
theorem R44833 : ∃ j : ℕ, syracuseStep^[j] 44833 = 1 := reachStep (stepEq 2 (by rfl) ⟨16812, by rfl⟩ : syracuseStep 44833 = 33625) R33625
theorem R12077 : ∃ j : ℕ, syracuseStep^[j] 12077 = 1 := reachStep (stepEq 3 (by rfl) ⟨2264, by rfl⟩ : syracuseStep 12077 = 4529) R4529
theorem R12097 : ∃ j : ℕ, syracuseStep^[j] 12097 = 1 := reachStep (stepEq 2 (by rfl) ⟨4536, by rfl⟩ : syracuseStep 12097 = 9073) R9073
theorem R12109 : ∃ j : ℕ, syracuseStep^[j] 12109 = 1 := reachStep (stepEq 3 (by rfl) ⟨2270, by rfl⟩ : syracuseStep 12109 = 4541) R4541
theorem R12113 : ∃ j : ℕ, syracuseStep^[j] 12113 = 1 := reachStep (stepEq 2 (by rfl) ⟨4542, by rfl⟩ : syracuseStep 12113 = 9085) R9085
theorem R13337 : ∃ j : ℕ, syracuseStep^[j] 13337 = 1 := reachStep (stepEq 2 (by rfl) ⟨5001, by rfl⟩ : syracuseStep 13337 = 10003) R10003
theorem R13385 : ∃ j : ℕ, syracuseStep^[j] 13385 = 1 := reachStep (stepEq 2 (by rfl) ⟨5019, by rfl⟩ : syracuseStep 13385 = 10039) R10039
theorem R177353 : ∃ j : ℕ, syracuseStep^[j] 177353 = 1 := reachStep (stepEq 2 (by rfl) ⟨66507, by rfl⟩ : syracuseStep 177353 = 133015) R133015
theorem R46747 : ∃ j : ℕ, syracuseStep^[j] 46747 = 1 := reachStep (stepEq 1 (by rfl) ⟨35060, by rfl⟩ : syracuseStep 46747 = 70121) R70121
theorem R49517 : ∃ j : ℕ, syracuseStep^[j] 49517 = 1 := reachStep (stepEq 3 (by rfl) ⟨9284, by rfl⟩ : syracuseStep 49517 = 18569) R18569
theorem R21761 : ∃ j : ℕ, syracuseStep^[j] 21761 = 1 := reachStep (stepEq 2 (by rfl) ⟨8160, by rfl⟩ : syracuseStep 21761 = 16321) R16321
theorem R21809 : ∃ j : ℕ, syracuseStep^[j] 21809 = 1 := reachStep (stepEq 2 (by rfl) ⟨8178, by rfl⟩ : syracuseStep 21809 = 16357) R16357
theorem R21829 : ∃ j : ℕ, syracuseStep^[j] 21829 = 1 := reachStep (stepEq 4 (by rfl) ⟨2046, by rfl⟩ : syracuseStep 21829 = 4093) R4093
theorem R21977 : ∃ j : ℕ, syracuseStep^[j] 21977 = 1 := reachStep (stepEq 2 (by rfl) ⟨8241, by rfl⟩ : syracuseStep 21977 = 16483) R16483
theorem R22031 : ∃ j : ℕ, syracuseStep^[j] 22031 = 1 := reachStep (stepEq 1 (by rfl) ⟨16523, by rfl⟩ : syracuseStep 22031 = 33047) R33047
theorem R22193 : ∃ j : ℕ, syracuseStep^[j] 22193 = 1 := reachStep (stepEq 2 (by rfl) ⟨8322, by rfl⟩ : syracuseStep 22193 = 16645) R16645
theorem R22295 : ∃ j : ℕ, syracuseStep^[j] 22295 = 1 := reachStep (stepEq 1 (by rfl) ⟨16721, by rfl⟩ : syracuseStep 22295 = 33443) R33443
theorem R22301 : ∃ j : ℕ, syracuseStep^[j] 22301 = 1 := reachStep (stepEq 3 (by rfl) ⟨4181, by rfl⟩ : syracuseStep 22301 = 8363) R8363
theorem R22409 : ∃ j : ℕ, syracuseStep^[j] 22409 = 1 := reachStep (stepEq 2 (by rfl) ⟨8403, by rfl⟩ : syracuseStep 22409 = 16807) R16807
theorem R26729 : ∃ j : ℕ, syracuseStep^[j] 26729 = 1 := reachStep (stepEq 2 (by rfl) ⟨10023, by rfl⟩ : syracuseStep 26729 = 20047) R20047
theorem R33011 : ∃ j : ℕ, syracuseStep^[j] 33011 = 1 := reachStep (stepEq 1 (by rfl) ⟨24758, by rfl⟩ : syracuseStep 33011 = 49517) R49517
theorem R251 : ∃ j : ℕ, syracuseStep^[j] 251 = 1 := reachStep (stepEq 1 (by rfl) ⟨188, by rfl⟩ : syracuseStep 251 = 377) R377
theorem R503 : ∃ j : ℕ, syracuseStep^[j] 503 = 1 := reachStep (stepEq 1 (by rfl) ⟨377, by rfl⟩ : syracuseStep 503 = 755) R755
theorem R897 : ∃ j : ℕ, syracuseStep^[j] 897 = 1 := reachStep (stepEq 2 (by rfl) ⟨336, by rfl⟩ : syracuseStep 897 = 673) R673
theorem R905 : ∃ j : ℕ, syracuseStep^[j] 905 = 1 := reachStep (stepEq 2 (by rfl) ⟨339, by rfl⟩ : syracuseStep 905 = 679) R679
theorem R923 : ∃ j : ℕ, syracuseStep^[j] 923 = 1 := reachStep (stepEq 1 (by rfl) ⟨692, by rfl⟩ : syracuseStep 923 = 1385) R1385
theorem R1005 : ∃ j : ℕ, syracuseStep^[j] 1005 = 1 := reachStep (stepEq 3 (by rfl) ⟨188, by rfl⟩ : syracuseStep 1005 = 377) R377
theorem R1795 : ∃ j : ℕ, syracuseStep^[j] 1795 = 1 := reachStep (stepEq 1 (by rfl) ⟨1346, by rfl⟩ : syracuseStep 1795 = 2693) R2693
theorem R1799 : ∃ j : ℕ, syracuseStep^[j] 1799 = 1 := reachStep (stepEq 1 (by rfl) ⟨1349, by rfl⟩ : syracuseStep 1799 = 2699) R2699
theorem R1811 : ∃ j : ℕ, syracuseStep^[j] 1811 = 1 := reachStep (stepEq 1 (by rfl) ⟨1358, by rfl⟩ : syracuseStep 1811 = 2717) R2717
theorem R1817 : ∃ j : ℕ, syracuseStep^[j] 1817 = 1 := reachStep (stepEq 2 (by rfl) ⟨681, by rfl⟩ : syracuseStep 1817 = 1363) R1363
theorem R1831 : ∃ j : ℕ, syracuseStep^[j] 1831 = 1 := reachStep (stepEq 1 (by rfl) ⟨1373, by rfl⟩ : syracuseStep 1831 = 2747) R2747
theorem R1847 : ∃ j : ℕ, syracuseStep^[j] 1847 = 1 := reachStep (stepEq 1 (by rfl) ⟨1385, by rfl⟩ : syracuseStep 1847 = 2771) R2771
theorem R1849 : ∃ j : ℕ, syracuseStep^[j] 1849 = 1 := reachStep (stepEq 2 (by rfl) ⟨693, by rfl⟩ : syracuseStep 1849 = 1387) R1387
theorem R1863 : ∃ j : ℕ, syracuseStep^[j] 1863 = 1 := reachStep (stepEq 1 (by rfl) ⟨1397, by rfl⟩ : syracuseStep 1863 = 2795) R2795
theorem R1865 : ∃ j : ℕ, syracuseStep^[j] 1865 = 1 := reachStep (stepEq 2 (by rfl) ⟨699, by rfl⟩ : syracuseStep 1865 = 1399) R1399
theorem R1897 : ∃ j : ℕ, syracuseStep^[j] 1897 = 1 := reachStep (stepEq 2 (by rfl) ⟨711, by rfl⟩ : syracuseStep 1897 = 1423) R1423
theorem R1899 : ∃ j : ℕ, syracuseStep^[j] 1899 = 1 := reachStep (stepEq 1 (by rfl) ⟨1424, by rfl⟩ : syracuseStep 1899 = 2849) R2849
theorem R2013 : ∃ j : ℕ, syracuseStep^[j] 2013 = 1 := reachStep (stepEq 3 (by rfl) ⟨377, by rfl⟩ : syracuseStep 2013 = 755) R755
theorem R2017 : ∃ j : ℕ, syracuseStep^[j] 2017 = 1 := reachStep (stepEq 2 (by rfl) ⟨756, by rfl⟩ : syracuseStep 2017 = 1513) R1513
theorem R3589 : ∃ j : ℕ, syracuseStep^[j] 3589 = 1 := reachStep (stepEq 4 (by rfl) ⟨336, by rfl⟩ : syracuseStep 3589 = 673) R673
theorem R3595 : ∃ j : ℕ, syracuseStep^[j] 3595 = 1 := reachStep (stepEq 1 (by rfl) ⟨2696, by rfl⟩ : syracuseStep 3595 = 5393) R5393
theorem R3599 : ∃ j : ℕ, syracuseStep^[j] 3599 = 1 := reachStep (stepEq 1 (by rfl) ⟨2699, by rfl⟩ : syracuseStep 3599 = 5399) R5399
theorem R3611 : ∃ j : ℕ, syracuseStep^[j] 3611 = 1 := reachStep (stepEq 1 (by rfl) ⟨2708, by rfl⟩ : syracuseStep 3611 = 5417) R5417
theorem R3615 : ∃ j : ℕ, syracuseStep^[j] 3615 = 1 := reachStep (stepEq 1 (by rfl) ⟨2711, by rfl⟩ : syracuseStep 3615 = 5423) R5423
theorem R3621 : ∃ j : ℕ, syracuseStep^[j] 3621 = 1 := reachStep (stepEq 4 (by rfl) ⟨339, by rfl⟩ : syracuseStep 3621 = 679) R679
theorem R3625 : ∃ j : ℕ, syracuseStep^[j] 3625 = 1 := reachStep (stepEq 2 (by rfl) ⟨1359, by rfl⟩ : syracuseStep 3625 = 2719) R2719
theorem R3633 : ∃ j : ℕ, syracuseStep^[j] 3633 = 1 := reachStep (stepEq 2 (by rfl) ⟨1362, by rfl⟩ : syracuseStep 3633 = 2725) R2725
theorem R3635 : ∃ j : ℕ, syracuseStep^[j] 3635 = 1 := reachStep (stepEq 1 (by rfl) ⟨2726, by rfl⟩ : syracuseStep 3635 = 5453) R5453
theorem R3663 : ∃ j : ℕ, syracuseStep^[j] 3663 = 1 := reachStep (stepEq 1 (by rfl) ⟨2747, by rfl⟩ : syracuseStep 3663 = 5495) R5495
theorem R3691 : ∃ j : ℕ, syracuseStep^[j] 3691 = 1 := reachStep (stepEq 1 (by rfl) ⟨2768, by rfl⟩ : syracuseStep 3691 = 5537) R5537
theorem R3693 : ∃ j : ℕ, syracuseStep^[j] 3693 = 1 := reachStep (stepEq 3 (by rfl) ⟨692, by rfl⟩ : syracuseStep 3693 = 1385) R1385
theorem R3699 : ∃ j : ℕ, syracuseStep^[j] 3699 = 1 := reachStep (stepEq 1 (by rfl) ⟨2774, by rfl⟩ : syracuseStep 3699 = 5549) R5549
theorem R3713 : ∃ j : ℕ, syracuseStep^[j] 3713 = 1 := reachStep (stepEq 2 (by rfl) ⟨1392, by rfl⟩ : syracuseStep 3713 = 2785) R2785
theorem R3721 : ∃ j : ℕ, syracuseStep^[j] 3721 = 1 := reachStep (stepEq 2 (by rfl) ⟨1395, by rfl⟩ : syracuseStep 3721 = 2791) R2791
theorem R3727 : ∃ j : ℕ, syracuseStep^[j] 3727 = 1 := reachStep (stepEq 1 (by rfl) ⟨2795, by rfl⟩ : syracuseStep 3727 = 5591) R5591
theorem R3729 : ∃ j : ℕ, syracuseStep^[j] 3729 = 1 := reachStep (stepEq 2 (by rfl) ⟨1398, by rfl⟩ : syracuseStep 3729 = 2797) R2797
theorem R3731 : ∃ j : ℕ, syracuseStep^[j] 3731 = 1 := reachStep (stepEq 1 (by rfl) ⟨2798, by rfl⟩ : syracuseStep 3731 = 5597) R5597
theorem R3743 : ∃ j : ℕ, syracuseStep^[j] 3743 = 1 := reachStep (stepEq 1 (by rfl) ⟨2807, by rfl⟩ : syracuseStep 3743 = 5615) R5615
theorem R3793 : ∃ j : ℕ, syracuseStep^[j] 3793 = 1 := reachStep (stepEq 2 (by rfl) ⟨1422, by rfl⟩ : syracuseStep 3793 = 2845) R2845
theorem R3795 : ∃ j : ℕ, syracuseStep^[j] 3795 = 1 := reachStep (stepEq 1 (by rfl) ⟨2846, by rfl⟩ : syracuseStep 3795 = 5693) R5693
theorem R3799 : ∃ j : ℕ, syracuseStep^[j] 3799 = 1 := reachStep (stepEq 1 (by rfl) ⟨2849, by rfl⟩ : syracuseStep 3799 = 5699) R5699
theorem R4021 : ∃ j : ℕ, syracuseStep^[j] 4021 = 1 := reachStep (stepEq 5 (by rfl) ⟨188, by rfl⟩ : syracuseStep 4021 = 377) R377
theorem R4025 : ∃ j : ℕ, syracuseStep^[j] 4025 = 1 := reachStep (stepEq 2 (by rfl) ⟨1509, by rfl⟩ : syracuseStep 4025 = 3019) R3019
theorem R4027 : ∃ j : ℕ, syracuseStep^[j] 4027 = 1 := reachStep (stepEq 1 (by rfl) ⟨3020, by rfl⟩ : syracuseStep 4027 = 6041) R6041
theorem R4033 : ∃ j : ℕ, syracuseStep^[j] 4033 = 1 := reachStep (stepEq 2 (by rfl) ⟨1512, by rfl⟩ : syracuseStep 4033 = 3025) R3025
theorem R4035 : ∃ j : ℕ, syracuseStep^[j] 4035 = 1 := reachStep (stepEq 1 (by rfl) ⟨3026, by rfl⟩ : syracuseStep 4035 = 6053) R6053
theorem R4449 : ∃ j : ℕ, syracuseStep^[j] 4449 = 1 := reachStep (stepEq 2 (by rfl) ⟨1668, by rfl⟩ : syracuseStep 4449 = 3337) R3337
theorem R7181 : ∃ j : ℕ, syracuseStep^[j] 7181 = 1 := reachStep (stepEq 3 (by rfl) ⟨1346, by rfl⟩ : syracuseStep 7181 = 2693) R2693
theorem R7223 : ∃ j : ℕ, syracuseStep^[j] 7223 = 1 := reachStep (stepEq 1 (by rfl) ⟨5417, by rfl⟩ : syracuseStep 7223 = 10835) R10835
theorem R7231 : ∃ j : ℕ, syracuseStep^[j] 7231 = 1 := reachStep (stepEq 1 (by rfl) ⟨5423, by rfl⟩ : syracuseStep 7231 = 10847) R10847
theorem R7249 : ∃ j : ℕ, syracuseStep^[j] 7249 = 1 := reachStep (stepEq 2 (by rfl) ⟨2718, by rfl⟩ : syracuseStep 7249 = 5437) R5437
theorem R7267 : ∃ j : ℕ, syracuseStep^[j] 7267 = 1 := reachStep (stepEq 1 (by rfl) ⟨5450, by rfl⟩ : syracuseStep 7267 = 10901) R10901
theorem R7325 : ∃ j : ℕ, syracuseStep^[j] 7325 = 1 := reachStep (stepEq 3 (by rfl) ⟨1373, by rfl⟩ : syracuseStep 7325 = 2747) R2747
theorem R7343 : ∃ j : ℕ, syracuseStep^[j] 7343 = 1 := reachStep (stepEq 1 (by rfl) ⟨5507, by rfl⟩ : syracuseStep 7343 = 11015) R11015
theorem R7385 : ∃ j : ℕ, syracuseStep^[j] 7385 = 1 := reachStep (stepEq 2 (by rfl) ⟨2769, by rfl⟩ : syracuseStep 7385 = 5539) R5539
theorem R7397 : ∃ j : ℕ, syracuseStep^[j] 7397 = 1 := reachStep (stepEq 4 (by rfl) ⟨693, by rfl⟩ : syracuseStep 7397 = 1387) R1387
theorem R7427 : ∃ j : ℕ, syracuseStep^[j] 7427 = 1 := reachStep (stepEq 1 (by rfl) ⟨5570, by rfl⟩ : syracuseStep 7427 = 11141) R11141
theorem R7433 : ∃ j : ℕ, syracuseStep^[j] 7433 = 1 := reachStep (stepEq 2 (by rfl) ⟨2787, by rfl⟩ : syracuseStep 7433 = 5575) R5575
theorem R7457 : ∃ j : ℕ, syracuseStep^[j] 7457 = 1 := reachStep (stepEq 2 (by rfl) ⟨2796, by rfl⟩ : syracuseStep 7457 = 5593) R5593
theorem R7463 : ∃ j : ℕ, syracuseStep^[j] 7463 = 1 := reachStep (stepEq 1 (by rfl) ⟨5597, by rfl⟩ : syracuseStep 7463 = 11195) R11195
theorem R7465 : ∃ j : ℕ, syracuseStep^[j] 7465 = 1 := reachStep (stepEq 2 (by rfl) ⟨2799, by rfl⟩ : syracuseStep 7465 = 5599) R5599
theorem R7487 : ∃ j : ℕ, syracuseStep^[j] 7487 = 1 := reachStep (stepEq 1 (by rfl) ⟨5615, by rfl⟩ : syracuseStep 7487 = 11231) R11231
theorem R7589 : ∃ j : ℕ, syracuseStep^[j] 7589 = 1 := reachStep (stepEq 4 (by rfl) ⟨711, by rfl⟩ : syracuseStep 7589 = 1423) R1423
theorem R7643 : ∃ j : ℕ, syracuseStep^[j] 7643 = 1 := reachStep (stepEq 1 (by rfl) ⟨5732, by rfl⟩ : syracuseStep 7643 = 11465) R11465
theorem R7787 : ∃ j : ℕ, syracuseStep^[j] 7787 = 1 := reachStep (stepEq 1 (by rfl) ⟨5840, by rfl⟩ : syracuseStep 7787 = 11681) R11681
theorem R8051 : ∃ j : ℕ, syracuseStep^[j] 8051 = 1 := reachStep (stepEq 1 (by rfl) ⟨6038, by rfl⟩ : syracuseStep 8051 = 12077) R12077
theorem R8069 : ∃ j : ℕ, syracuseStep^[j] 8069 = 1 := reachStep (stepEq 4 (by rfl) ⟨756, by rfl⟩ : syracuseStep 8069 = 1513) R1513
theorem R8075 : ∃ j : ℕ, syracuseStep^[j] 8075 = 1 := reachStep (stepEq 1 (by rfl) ⟨6056, by rfl⟩ : syracuseStep 8075 = 12113) R12113
theorem R8105 : ∃ j : ℕ, syracuseStep^[j] 8105 = 1 := reachStep (stepEq 2 (by rfl) ⟨3039, by rfl⟩ : syracuseStep 8105 = 6079) R6079
theorem R8891 : ∃ j : ℕ, syracuseStep^[j] 8891 = 1 := reachStep (stepEq 1 (by rfl) ⟨6668, by rfl⟩ : syracuseStep 8891 = 13337) R13337
theorem R8923 : ∃ j : ℕ, syracuseStep^[j] 8923 = 1 := reachStep (stepEq 1 (by rfl) ⟨6692, by rfl⟩ : syracuseStep 8923 = 13385) R13385
theorem R14357 : ∃ j : ℕ, syracuseStep^[j] 14357 = 1 := reachStep (stepEq 6 (by rfl) ⟨336, by rfl⟩ : syracuseStep 14357 = 673) R673
theorem R14381 : ∃ j : ℕ, syracuseStep^[j] 14381 = 1 := reachStep (stepEq 3 (by rfl) ⟨2696, by rfl⟩ : syracuseStep 14381 = 5393) R5393
theorem R14501 : ∃ j : ℕ, syracuseStep^[j] 14501 = 1 := reachStep (stepEq 4 (by rfl) ⟨1359, by rfl⟩ : syracuseStep 14501 = 2719) R2719
theorem R14507 : ∃ j : ℕ, syracuseStep^[j] 14507 = 1 := reachStep (stepEq 1 (by rfl) ⟨10880, by rfl⟩ : syracuseStep 14507 = 21761) R21761
theorem R14539 : ∃ j : ℕ, syracuseStep^[j] 14539 = 1 := reachStep (stepEq 1 (by rfl) ⟨10904, by rfl⟩ : syracuseStep 14539 = 21809) R21809
theorem R14651 : ∃ j : ℕ, syracuseStep^[j] 14651 = 1 := reachStep (stepEq 1 (by rfl) ⟨10988, by rfl⟩ : syracuseStep 14651 = 21977) R21977
theorem R14687 : ∃ j : ℕ, syracuseStep^[j] 14687 = 1 := reachStep (stepEq 1 (by rfl) ⟨11015, by rfl⟩ : syracuseStep 14687 = 22031) R22031
theorem R14777 : ∃ j : ℕ, syracuseStep^[j] 14777 = 1 := reachStep (stepEq 2 (by rfl) ⟨5541, by rfl⟩ : syracuseStep 14777 = 11083) R11083
theorem R14795 : ∃ j : ℕ, syracuseStep^[j] 14795 = 1 := reachStep (stepEq 1 (by rfl) ⟨11096, by rfl⟩ : syracuseStep 14795 = 22193) R22193
theorem R14863 : ∃ j : ℕ, syracuseStep^[j] 14863 = 1 := reachStep (stepEq 1 (by rfl) ⟨11147, by rfl⟩ : syracuseStep 14863 = 22295) R22295
theorem R14867 : ∃ j : ℕ, syracuseStep^[j] 14867 = 1 := reachStep (stepEq 1 (by rfl) ⟨11150, by rfl⟩ : syracuseStep 14867 = 22301) R22301
theorem R14885 : ∃ j : ℕ, syracuseStep^[j] 14885 = 1 := reachStep (stepEq 4 (by rfl) ⟨1395, by rfl⟩ : syracuseStep 14885 = 2791) R2791
theorem R14917 : ∃ j : ℕ, syracuseStep^[j] 14917 = 1 := reachStep (stepEq 4 (by rfl) ⟨1398, by rfl⟩ : syracuseStep 14917 = 2797) R2797
theorem R14939 : ∃ j : ℕ, syracuseStep^[j] 14939 = 1 := reachStep (stepEq 1 (by rfl) ⟨11204, by rfl⟩ : syracuseStep 14939 = 22409) R22409
theorem R15173 : ∃ j : ℕ, syracuseStep^[j] 15173 = 1 := reachStep (stepEq 4 (by rfl) ⟨1422, by rfl⟩ : syracuseStep 15173 = 2845) R2845
theorem R16109 : ∃ j : ℕ, syracuseStep^[j] 16109 = 1 := reachStep (stepEq 3 (by rfl) ⟨3020, by rfl⟩ : syracuseStep 16109 = 6041) R6041
theorem R16129 : ∃ j : ℕ, syracuseStep^[j] 16129 = 1 := reachStep (stepEq 2 (by rfl) ⟨6048, by rfl⟩ : syracuseStep 16129 = 12097) R12097
theorem R16145 : ∃ j : ℕ, syracuseStep^[j] 16145 = 1 := reachStep (stepEq 2 (by rfl) ⟨6054, by rfl⟩ : syracuseStep 16145 = 12109) R12109
theorem R115181 : ∃ j : ℕ, syracuseStep^[j] 115181 = 1 := reachStep (stepEq 3 (by rfl) ⟨21596, by rfl⟩ : syracuseStep 115181 = 43193) R43193
theorem R17819 : ∃ j : ℕ, syracuseStep^[j] 17819 = 1 := reachStep (stepEq 1 (by rfl) ⟨13364, by rfl⟩ : syracuseStep 17819 = 26729) R26729
theorem R118235 : ∃ j : ℕ, syracuseStep^[j] 118235 = 1 := reachStep (stepEq 1 (by rfl) ⟨88676, by rfl⟩ : syracuseStep 118235 = 177353) R177353
theorem R58913 : ∃ j : ℕ, syracuseStep^[j] 58913 = 1 := reachStep (stepEq 2 (by rfl) ⟨22092, by rfl⟩ : syracuseStep 58913 = 44185) R44185
theorem R59777 : ∃ j : ℕ, syracuseStep^[j] 59777 = 1 := reachStep (stepEq 2 (by rfl) ⟨22416, by rfl⟩ : syracuseStep 59777 = 44833) R44833
theorem R28795 : ∃ j : ℕ, syracuseStep^[j] 28795 = 1 := reachStep (stepEq 1 (by rfl) ⟨21596, by rfl⟩ : syracuseStep 28795 = 43193) R43193
theorem R28997 : ∃ j : ℕ, syracuseStep^[j] 28997 = 1 := reachStep (stepEq 4 (by rfl) ⟨2718, by rfl⟩ : syracuseStep 28997 = 5437) R5437
theorem R29069 : ∃ j : ℕ, syracuseStep^[j] 29069 = 1 := reachStep (stepEq 3 (by rfl) ⟨5450, by rfl⟩ : syracuseStep 29069 = 10901) R10901
theorem R29105 : ∃ j : ℕ, syracuseStep^[j] 29105 = 1 := reachStep (stepEq 2 (by rfl) ⟨10914, by rfl⟩ : syracuseStep 29105 = 21829) R21829
theorem R62329 : ∃ j : ℕ, syracuseStep^[j] 62329 = 1 := reachStep (stepEq 2 (by rfl) ⟨23373, by rfl⟩ : syracuseStep 62329 = 46747) R46747
theorem R167 : ∃ j : ℕ, syracuseStep^[j] 167 = 1 := reachStep (stepEq 1 (by rfl) ⟨125, by rfl⟩ : syracuseStep 167 = 251) R251
theorem R335 : ∃ j : ℕ, syracuseStep^[j] 335 = 1 := reachStep (stepEq 1 (by rfl) ⟨251, by rfl⟩ : syracuseStep 335 = 503) R503
theorem R603 : ∃ j : ℕ, syracuseStep^[j] 603 = 1 := reachStep (stepEq 1 (by rfl) ⟨452, by rfl⟩ : syracuseStep 603 = 905) R905
theorem R615 : ∃ j : ℕ, syracuseStep^[j] 615 = 1 := reachStep (stepEq 1 (by rfl) ⟨461, by rfl⟩ : syracuseStep 615 = 923) R923
theorem R669 : ∃ j : ℕ, syracuseStep^[j] 669 = 1 := reachStep (stepEq 3 (by rfl) ⟨125, by rfl⟩ : syracuseStep 669 = 251) R251
theorem R1199 : ∃ j : ℕ, syracuseStep^[j] 1199 = 1 := reachStep (stepEq 1 (by rfl) ⟨899, by rfl⟩ : syracuseStep 1199 = 1799) R1799
theorem R1207 : ∃ j : ℕ, syracuseStep^[j] 1207 = 1 := reachStep (stepEq 1 (by rfl) ⟨905, by rfl⟩ : syracuseStep 1207 = 1811) R1811
theorem R1211 : ∃ j : ℕ, syracuseStep^[j] 1211 = 1 := reachStep (stepEq 1 (by rfl) ⟨908, by rfl⟩ : syracuseStep 1211 = 1817) R1817
theorem R1231 : ∃ j : ℕ, syracuseStep^[j] 1231 = 1 := reachStep (stepEq 1 (by rfl) ⟨923, by rfl⟩ : syracuseStep 1231 = 1847) R1847
theorem R1243 : ∃ j : ℕ, syracuseStep^[j] 1243 = 1 := reachStep (stepEq 1 (by rfl) ⟨932, by rfl⟩ : syracuseStep 1243 = 1865) R1865
theorem R1341 : ∃ j : ℕ, syracuseStep^[j] 1341 = 1 := reachStep (stepEq 3 (by rfl) ⟨251, by rfl⟩ : syracuseStep 1341 = 503) R503
theorem R2393 : ∃ j : ℕ, syracuseStep^[j] 2393 = 1 := reachStep (stepEq 2 (by rfl) ⟨897, by rfl⟩ : syracuseStep 2393 = 1795) R1795
theorem R2399 : ∃ j : ℕ, syracuseStep^[j] 2399 = 1 := reachStep (stepEq 1 (by rfl) ⟨1799, by rfl⟩ : syracuseStep 2399 = 3599) R3599
theorem R2407 : ∃ j : ℕ, syracuseStep^[j] 2407 = 1 := reachStep (stepEq 1 (by rfl) ⟨1805, by rfl⟩ : syracuseStep 2407 = 3611) R3611
theorem R2413 : ∃ j : ℕ, syracuseStep^[j] 2413 = 1 := reachStep (stepEq 3 (by rfl) ⟨452, by rfl⟩ : syracuseStep 2413 = 905) R905
theorem R2423 : ∃ j : ℕ, syracuseStep^[j] 2423 = 1 := reachStep (stepEq 1 (by rfl) ⟨1817, by rfl⟩ : syracuseStep 2423 = 3635) R3635
theorem R2441 : ∃ j : ℕ, syracuseStep^[j] 2441 = 1 := reachStep (stepEq 2 (by rfl) ⟨915, by rfl⟩ : syracuseStep 2441 = 1831) R1831
theorem R2461 : ∃ j : ℕ, syracuseStep^[j] 2461 = 1 := reachStep (stepEq 3 (by rfl) ⟨461, by rfl⟩ : syracuseStep 2461 = 923) R923
theorem R2465 : ∃ j : ℕ, syracuseStep^[j] 2465 = 1 := reachStep (stepEq 2 (by rfl) ⟨924, by rfl⟩ : syracuseStep 2465 = 1849) R1849
theorem R2475 : ∃ j : ℕ, syracuseStep^[j] 2475 = 1 := reachStep (stepEq 1 (by rfl) ⟨1856, by rfl⟩ : syracuseStep 2475 = 3713) R3713
theorem R2487 : ∃ j : ℕ, syracuseStep^[j] 2487 = 1 := reachStep (stepEq 1 (by rfl) ⟨1865, by rfl⟩ : syracuseStep 2487 = 3731) R3731
theorem R2495 : ∃ j : ℕ, syracuseStep^[j] 2495 = 1 := reachStep (stepEq 1 (by rfl) ⟨1871, by rfl⟩ : syracuseStep 2495 = 3743) R3743
theorem R2529 : ∃ j : ℕ, syracuseStep^[j] 2529 = 1 := reachStep (stepEq 2 (by rfl) ⟨948, by rfl⟩ : syracuseStep 2529 = 1897) R1897
theorem R2677 : ∃ j : ℕ, syracuseStep^[j] 2677 = 1 := reachStep (stepEq 5 (by rfl) ⟨125, by rfl⟩ : syracuseStep 2677 = 251) R251
theorem R2683 : ∃ j : ℕ, syracuseStep^[j] 2683 = 1 := reachStep (stepEq 1 (by rfl) ⟨2012, by rfl⟩ : syracuseStep 2683 = 4025) R4025
theorem R2689 : ∃ j : ℕ, syracuseStep^[j] 2689 = 1 := reachStep (stepEq 2 (by rfl) ⟨1008, by rfl⟩ : syracuseStep 2689 = 2017) R2017
theorem R4785 : ∃ j : ℕ, syracuseStep^[j] 4785 = 1 := reachStep (stepEq 2 (by rfl) ⟨1794, by rfl⟩ : syracuseStep 4785 = 3589) R3589
theorem R4787 : ∃ j : ℕ, syracuseStep^[j] 4787 = 1 := reachStep (stepEq 1 (by rfl) ⟨3590, by rfl⟩ : syracuseStep 4787 = 7181) R7181
theorem R4793 : ∃ j : ℕ, syracuseStep^[j] 4793 = 1 := reachStep (stepEq 2 (by rfl) ⟨1797, by rfl⟩ : syracuseStep 4793 = 3595) R3595
theorem R4797 : ∃ j : ℕ, syracuseStep^[j] 4797 = 1 := reachStep (stepEq 3 (by rfl) ⟨899, by rfl⟩ : syracuseStep 4797 = 1799) R1799
theorem R4815 : ∃ j : ℕ, syracuseStep^[j] 4815 = 1 := reachStep (stepEq 1 (by rfl) ⟨3611, by rfl⟩ : syracuseStep 4815 = 7223) R7223
theorem R4829 : ∃ j : ℕ, syracuseStep^[j] 4829 = 1 := reachStep (stepEq 3 (by rfl) ⟨905, by rfl⟩ : syracuseStep 4829 = 1811) R1811
theorem R4833 : ∃ j : ℕ, syracuseStep^[j] 4833 = 1 := reachStep (stepEq 2 (by rfl) ⟨1812, by rfl⟩ : syracuseStep 4833 = 3625) R3625
theorem R4845 : ∃ j : ℕ, syracuseStep^[j] 4845 = 1 := reachStep (stepEq 3 (by rfl) ⟨908, by rfl⟩ : syracuseStep 4845 = 1817) R1817
theorem R4883 : ∃ j : ℕ, syracuseStep^[j] 4883 = 1 := reachStep (stepEq 1 (by rfl) ⟨3662, by rfl⟩ : syracuseStep 4883 = 7325) R7325
theorem R4895 : ∃ j : ℕ, syracuseStep^[j] 4895 = 1 := reachStep (stepEq 1 (by rfl) ⟨3671, by rfl⟩ : syracuseStep 4895 = 7343) R7343
theorem R4921 : ∃ j : ℕ, syracuseStep^[j] 4921 = 1 := reachStep (stepEq 2 (by rfl) ⟨1845, by rfl⟩ : syracuseStep 4921 = 3691) R3691
theorem R4923 : ∃ j : ℕ, syracuseStep^[j] 4923 = 1 := reachStep (stepEq 1 (by rfl) ⟨3692, by rfl⟩ : syracuseStep 4923 = 7385) R7385
theorem R4925 : ∃ j : ℕ, syracuseStep^[j] 4925 = 1 := reachStep (stepEq 3 (by rfl) ⟨923, by rfl⟩ : syracuseStep 4925 = 1847) R1847
theorem R4931 : ∃ j : ℕ, syracuseStep^[j] 4931 = 1 := reachStep (stepEq 1 (by rfl) ⟨3698, by rfl⟩ : syracuseStep 4931 = 7397) R7397
theorem R4951 : ∃ j : ℕ, syracuseStep^[j] 4951 = 1 := reachStep (stepEq 1 (by rfl) ⟨3713, by rfl⟩ : syracuseStep 4951 = 7427) R7427
theorem R4955 : ∃ j : ℕ, syracuseStep^[j] 4955 = 1 := reachStep (stepEq 1 (by rfl) ⟨3716, by rfl⟩ : syracuseStep 4955 = 7433) R7433
theorem R4961 : ∃ j : ℕ, syracuseStep^[j] 4961 = 1 := reachStep (stepEq 2 (by rfl) ⟨1860, by rfl⟩ : syracuseStep 4961 = 3721) R3721
theorem R4969 : ∃ j : ℕ, syracuseStep^[j] 4969 = 1 := reachStep (stepEq 2 (by rfl) ⟨1863, by rfl⟩ : syracuseStep 4969 = 3727) R3727
theorem R4971 : ∃ j : ℕ, syracuseStep^[j] 4971 = 1 := reachStep (stepEq 1 (by rfl) ⟨3728, by rfl⟩ : syracuseStep 4971 = 7457) R7457
theorem R4973 : ∃ j : ℕ, syracuseStep^[j] 4973 = 1 := reachStep (stepEq 3 (by rfl) ⟨932, by rfl⟩ : syracuseStep 4973 = 1865) R1865
theorem R4975 : ∃ j : ℕ, syracuseStep^[j] 4975 = 1 := reachStep (stepEq 1 (by rfl) ⟨3731, by rfl⟩ : syracuseStep 4975 = 7463) R7463
theorem R4991 : ∃ j : ℕ, syracuseStep^[j] 4991 = 1 := reachStep (stepEq 1 (by rfl) ⟨3743, by rfl⟩ : syracuseStep 4991 = 7487) R7487
theorem R5057 : ∃ j : ℕ, syracuseStep^[j] 5057 = 1 := reachStep (stepEq 2 (by rfl) ⟨1896, by rfl⟩ : syracuseStep 5057 = 3793) R3793
theorem R5059 : ∃ j : ℕ, syracuseStep^[j] 5059 = 1 := reachStep (stepEq 1 (by rfl) ⟨3794, by rfl⟩ : syracuseStep 5059 = 7589) R7589
theorem R5065 : ∃ j : ℕ, syracuseStep^[j] 5065 = 1 := reachStep (stepEq 2 (by rfl) ⟨1899, by rfl⟩ : syracuseStep 5065 = 3799) R3799
theorem R5095 : ∃ j : ℕ, syracuseStep^[j] 5095 = 1 := reachStep (stepEq 1 (by rfl) ⟨3821, by rfl⟩ : syracuseStep 5095 = 7643) R7643
theorem R5191 : ∃ j : ℕ, syracuseStep^[j] 5191 = 1 := reachStep (stepEq 1 (by rfl) ⟨3893, by rfl⟩ : syracuseStep 5191 = 7787) R7787
theorem R5361 : ∃ j : ℕ, syracuseStep^[j] 5361 = 1 := reachStep (stepEq 2 (by rfl) ⟨2010, by rfl⟩ : syracuseStep 5361 = 4021) R4021
theorem R5365 : ∃ j : ℕ, syracuseStep^[j] 5365 = 1 := reachStep (stepEq 5 (by rfl) ⟨251, by rfl⟩ : syracuseStep 5365 = 503) R503
theorem R5367 : ∃ j : ℕ, syracuseStep^[j] 5367 = 1 := reachStep (stepEq 1 (by rfl) ⟨4025, by rfl⟩ : syracuseStep 5367 = 8051) R8051
theorem R5369 : ∃ j : ℕ, syracuseStep^[j] 5369 = 1 := reachStep (stepEq 2 (by rfl) ⟨2013, by rfl⟩ : syracuseStep 5369 = 4027) R4027
theorem R5377 : ∃ j : ℕ, syracuseStep^[j] 5377 = 1 := reachStep (stepEq 2 (by rfl) ⟨2016, by rfl⟩ : syracuseStep 5377 = 4033) R4033
theorem R5379 : ∃ j : ℕ, syracuseStep^[j] 5379 = 1 := reachStep (stepEq 1 (by rfl) ⟨4034, by rfl⟩ : syracuseStep 5379 = 8069) R8069
theorem R5383 : ∃ j : ℕ, syracuseStep^[j] 5383 = 1 := reachStep (stepEq 1 (by rfl) ⟨4037, by rfl⟩ : syracuseStep 5383 = 8075) R8075
theorem R5403 : ∃ j : ℕ, syracuseStep^[j] 5403 = 1 := reachStep (stepEq 1 (by rfl) ⟨4052, by rfl⟩ : syracuseStep 5403 = 8105) R8105
theorem R38393 : ∃ j : ℕ, syracuseStep^[j] 38393 = 1 := reachStep (stepEq 2 (by rfl) ⟨14397, by rfl⟩ : syracuseStep 38393 = 28795) R28795
theorem R5927 : ∃ j : ℕ, syracuseStep^[j] 5927 = 1 := reachStep (stepEq 1 (by rfl) ⟨4445, by rfl⟩ : syracuseStep 5927 = 8891) R8891
theorem R39275 : ∃ j : ℕ, syracuseStep^[j] 39275 = 1 := reachStep (stepEq 1 (by rfl) ⟨29456, by rfl⟩ : syracuseStep 39275 = 58913) R58913
theorem R39851 : ∃ j : ℕ, syracuseStep^[j] 39851 = 1 := reachStep (stepEq 1 (by rfl) ⟨29888, by rfl⟩ : syracuseStep 39851 = 59777) R59777
theorem R9571 : ∃ j : ℕ, syracuseStep^[j] 9571 = 1 := reachStep (stepEq 1 (by rfl) ⟨7178, by rfl⟩ : syracuseStep 9571 = 14357) R14357
theorem R9587 : ∃ j : ℕ, syracuseStep^[j] 9587 = 1 := reachStep (stepEq 1 (by rfl) ⟨7190, by rfl⟩ : syracuseStep 9587 = 14381) R14381
theorem R9629 : ∃ j : ℕ, syracuseStep^[j] 9629 = 1 := reachStep (stepEq 3 (by rfl) ⟨1805, by rfl⟩ : syracuseStep 9629 = 3611) R3611
theorem R9641 : ∃ j : ℕ, syracuseStep^[j] 9641 = 1 := reachStep (stepEq 2 (by rfl) ⟨3615, by rfl⟩ : syracuseStep 9641 = 7231) R7231
theorem R9653 : ∃ j : ℕ, syracuseStep^[j] 9653 = 1 := reachStep (stepEq 5 (by rfl) ⟨452, by rfl⟩ : syracuseStep 9653 = 905) R905
theorem R9665 : ∃ j : ℕ, syracuseStep^[j] 9665 = 1 := reachStep (stepEq 2 (by rfl) ⟨3624, by rfl⟩ : syracuseStep 9665 = 7249) R7249
theorem R9667 : ∃ j : ℕ, syracuseStep^[j] 9667 = 1 := reachStep (stepEq 1 (by rfl) ⟨7250, by rfl⟩ : syracuseStep 9667 = 14501) R14501
theorem R9671 : ∃ j : ℕ, syracuseStep^[j] 9671 = 1 := reachStep (stepEq 1 (by rfl) ⟨7253, by rfl⟩ : syracuseStep 9671 = 14507) R14507
theorem R9689 : ∃ j : ℕ, syracuseStep^[j] 9689 = 1 := reachStep (stepEq 2 (by rfl) ⟨3633, by rfl⟩ : syracuseStep 9689 = 7267) R7267
theorem R9767 : ∃ j : ℕ, syracuseStep^[j] 9767 = 1 := reachStep (stepEq 1 (by rfl) ⟨7325, by rfl⟩ : syracuseStep 9767 = 14651) R14651
theorem R9791 : ∃ j : ℕ, syracuseStep^[j] 9791 = 1 := reachStep (stepEq 1 (by rfl) ⟨7343, by rfl⟩ : syracuseStep 9791 = 14687) R14687
theorem R9845 : ∃ j : ℕ, syracuseStep^[j] 9845 = 1 := reachStep (stepEq 5 (by rfl) ⟨461, by rfl⟩ : syracuseStep 9845 = 923) R923
theorem R9851 : ∃ j : ℕ, syracuseStep^[j] 9851 = 1 := reachStep (stepEq 1 (by rfl) ⟨7388, by rfl⟩ : syracuseStep 9851 = 14777) R14777
theorem R9863 : ∃ j : ℕ, syracuseStep^[j] 9863 = 1 := reachStep (stepEq 1 (by rfl) ⟨7397, by rfl⟩ : syracuseStep 9863 = 14795) R14795
theorem R9911 : ∃ j : ℕ, syracuseStep^[j] 9911 = 1 := reachStep (stepEq 1 (by rfl) ⟨7433, by rfl⟩ : syracuseStep 9911 = 14867) R14867
theorem R9923 : ∃ j : ℕ, syracuseStep^[j] 9923 = 1 := reachStep (stepEq 1 (by rfl) ⟨7442, by rfl⟩ : syracuseStep 9923 = 14885) R14885
theorem R9949 : ∃ j : ℕ, syracuseStep^[j] 9949 = 1 := reachStep (stepEq 3 (by rfl) ⟨1865, by rfl⟩ : syracuseStep 9949 = 3731) R3731
theorem R9953 : ∃ j : ℕ, syracuseStep^[j] 9953 = 1 := reachStep (stepEq 2 (by rfl) ⟨3732, by rfl⟩ : syracuseStep 9953 = 7465) R7465
theorem R9959 : ∃ j : ℕ, syracuseStep^[j] 9959 = 1 := reachStep (stepEq 1 (by rfl) ⟨7469, by rfl⟩ : syracuseStep 9959 = 14939) R14939
theorem R10115 : ∃ j : ℕ, syracuseStep^[j] 10115 = 1 := reachStep (stepEq 1 (by rfl) ⟨7586, by rfl⟩ : syracuseStep 10115 = 15173) R15173
theorem R10709 : ∃ j : ℕ, syracuseStep^[j] 10709 = 1 := reachStep (stepEq 7 (by rfl) ⟨125, by rfl⟩ : syracuseStep 10709 = 251) R251
theorem R10739 : ∃ j : ℕ, syracuseStep^[j] 10739 = 1 := reachStep (stepEq 1 (by rfl) ⟨8054, by rfl⟩ : syracuseStep 10739 = 16109) R16109
theorem R10763 : ∃ j : ℕ, syracuseStep^[j] 10763 = 1 := reachStep (stepEq 1 (by rfl) ⟨8072, by rfl⟩ : syracuseStep 10763 = 16145) R16145
theorem R76787 : ∃ j : ℕ, syracuseStep^[j] 76787 = 1 := reachStep (stepEq 1 (by rfl) ⟨57590, by rfl⟩ : syracuseStep 76787 = 115181) R115181
theorem R11879 : ∃ j : ℕ, syracuseStep^[j] 11879 = 1 := reachStep (stepEq 1 (by rfl) ⟨8909, by rfl⟩ : syracuseStep 11879 = 17819) R17819
theorem R11897 : ∃ j : ℕ, syracuseStep^[j] 11897 = 1 := reachStep (stepEq 2 (by rfl) ⟨4461, by rfl⟩ : syracuseStep 11897 = 8923) R8923
theorem R78823 : ∃ j : ℕ, syracuseStep^[j] 78823 = 1 := reachStep (stepEq 1 (by rfl) ⟨59117, by rfl⟩ : syracuseStep 78823 = 118235) R118235
theorem R83105 : ∃ j : ℕ, syracuseStep^[j] 83105 = 1 := reachStep (stepEq 2 (by rfl) ⟨31164, by rfl⟩ : syracuseStep 83105 = 62329) R62329
theorem R19331 : ∃ j : ℕ, syracuseStep^[j] 19331 = 1 := reachStep (stepEq 1 (by rfl) ⟨14498, by rfl⟩ : syracuseStep 19331 = 28997) R28997
theorem R19379 : ∃ j : ℕ, syracuseStep^[j] 19379 = 1 := reachStep (stepEq 1 (by rfl) ⟨14534, by rfl⟩ : syracuseStep 19379 = 29069) R29069
theorem R19385 : ∃ j : ℕ, syracuseStep^[j] 19385 = 1 := reachStep (stepEq 2 (by rfl) ⟨7269, by rfl⟩ : syracuseStep 19385 = 14539) R14539
theorem R19403 : ∃ j : ℕ, syracuseStep^[j] 19403 = 1 := reachStep (stepEq 1 (by rfl) ⟨14552, by rfl⟩ : syracuseStep 19403 = 29105) R29105
theorem R19817 : ∃ j : ℕ, syracuseStep^[j] 19817 = 1 := reachStep (stepEq 2 (by rfl) ⟨7431, by rfl⟩ : syracuseStep 19817 = 14863) R14863
theorem R19889 : ∃ j : ℕ, syracuseStep^[j] 19889 = 1 := reachStep (stepEq 2 (by rfl) ⟨7458, by rfl⟩ : syracuseStep 19889 = 14917) R14917
theorem R21505 : ∃ j : ℕ, syracuseStep^[j] 21505 = 1 := reachStep (stepEq 2 (by rfl) ⟨8064, by rfl⟩ : syracuseStep 21505 = 16129) R16129
theorem R22007 : ∃ j : ℕ, syracuseStep^[j] 22007 = 1 := reachStep (stepEq 1 (by rfl) ⟨16505, by rfl⟩ : syracuseStep 22007 = 33011) R33011
theorem R111 : ∃ j : ℕ, syracuseStep^[j] 111 = 1 := reachStep (stepEq 1 (by rfl) ⟨83, by rfl⟩ : syracuseStep 111 = 167) R167
theorem R223 : ∃ j : ℕ, syracuseStep^[j] 223 = 1 := reachStep (stepEq 1 (by rfl) ⟨167, by rfl⟩ : syracuseStep 223 = 335) R335
theorem R445 : ∃ j : ℕ, syracuseStep^[j] 445 = 1 := reachStep (stepEq 3 (by rfl) ⟨83, by rfl⟩ : syracuseStep 445 = 167) R167
theorem R799 : ∃ j : ℕ, syracuseStep^[j] 799 = 1 := reachStep (stepEq 1 (by rfl) ⟨599, by rfl⟩ : syracuseStep 799 = 1199) R1199
theorem R807 : ∃ j : ℕ, syracuseStep^[j] 807 = 1 := reachStep (stepEq 1 (by rfl) ⟨605, by rfl⟩ : syracuseStep 807 = 1211) R1211
theorem R893 : ∃ j : ℕ, syracuseStep^[j] 893 = 1 := reachStep (stepEq 3 (by rfl) ⟨167, by rfl⟩ : syracuseStep 893 = 335) R335
theorem R1595 : ∃ j : ℕ, syracuseStep^[j] 1595 = 1 := reachStep (stepEq 1 (by rfl) ⟨1196, by rfl⟩ : syracuseStep 1595 = 2393) R2393
theorem R1599 : ∃ j : ℕ, syracuseStep^[j] 1599 = 1 := reachStep (stepEq 1 (by rfl) ⟨1199, by rfl⟩ : syracuseStep 1599 = 2399) R2399
theorem R1609 : ∃ j : ℕ, syracuseStep^[j] 1609 = 1 := reachStep (stepEq 2 (by rfl) ⟨603, by rfl⟩ : syracuseStep 1609 = 1207) R1207
theorem R1615 : ∃ j : ℕ, syracuseStep^[j] 1615 = 1 := reachStep (stepEq 1 (by rfl) ⟨1211, by rfl⟩ : syracuseStep 1615 = 2423) R2423
theorem R1627 : ∃ j : ℕ, syracuseStep^[j] 1627 = 1 := reachStep (stepEq 1 (by rfl) ⟨1220, by rfl⟩ : syracuseStep 1627 = 2441) R2441
theorem R1641 : ∃ j : ℕ, syracuseStep^[j] 1641 = 1 := reachStep (stepEq 2 (by rfl) ⟨615, by rfl⟩ : syracuseStep 1641 = 1231) R1231
theorem R1643 : ∃ j : ℕ, syracuseStep^[j] 1643 = 1 := reachStep (stepEq 1 (by rfl) ⟨1232, by rfl⟩ : syracuseStep 1643 = 2465) R2465
theorem R1657 : ∃ j : ℕ, syracuseStep^[j] 1657 = 1 := reachStep (stepEq 2 (by rfl) ⟨621, by rfl⟩ : syracuseStep 1657 = 1243) R1243
theorem R1663 : ∃ j : ℕ, syracuseStep^[j] 1663 = 1 := reachStep (stepEq 1 (by rfl) ⟨1247, by rfl⟩ : syracuseStep 1663 = 2495) R2495
theorem R1781 : ∃ j : ℕ, syracuseStep^[j] 1781 = 1 := reachStep (stepEq 5 (by rfl) ⟨83, by rfl⟩ : syracuseStep 1781 = 167) R167
theorem R3191 : ∃ j : ℕ, syracuseStep^[j] 3191 = 1 := reachStep (stepEq 1 (by rfl) ⟨2393, by rfl⟩ : syracuseStep 3191 = 4787) R4787
theorem R3195 : ∃ j : ℕ, syracuseStep^[j] 3195 = 1 := reachStep (stepEq 1 (by rfl) ⟨2396, by rfl⟩ : syracuseStep 3195 = 4793) R4793
theorem R3197 : ∃ j : ℕ, syracuseStep^[j] 3197 = 1 := reachStep (stepEq 3 (by rfl) ⟨599, by rfl⟩ : syracuseStep 3197 = 1199) R1199
theorem R3209 : ∃ j : ℕ, syracuseStep^[j] 3209 = 1 := reachStep (stepEq 2 (by rfl) ⟨1203, by rfl⟩ : syracuseStep 3209 = 2407) R2407
theorem R3217 : ∃ j : ℕ, syracuseStep^[j] 3217 = 1 := reachStep (stepEq 2 (by rfl) ⟨1206, by rfl⟩ : syracuseStep 3217 = 2413) R2413
theorem R3219 : ∃ j : ℕ, syracuseStep^[j] 3219 = 1 := reachStep (stepEq 1 (by rfl) ⟨2414, by rfl⟩ : syracuseStep 3219 = 4829) R4829
theorem R3229 : ∃ j : ℕ, syracuseStep^[j] 3229 = 1 := reachStep (stepEq 3 (by rfl) ⟨605, by rfl⟩ : syracuseStep 3229 = 1211) R1211
theorem R3255 : ∃ j : ℕ, syracuseStep^[j] 3255 = 1 := reachStep (stepEq 1 (by rfl) ⟨2441, by rfl⟩ : syracuseStep 3255 = 4883) R4883
theorem R3263 : ∃ j : ℕ, syracuseStep^[j] 3263 = 1 := reachStep (stepEq 1 (by rfl) ⟨2447, by rfl⟩ : syracuseStep 3263 = 4895) R4895
theorem R3281 : ∃ j : ℕ, syracuseStep^[j] 3281 = 1 := reachStep (stepEq 2 (by rfl) ⟨1230, by rfl⟩ : syracuseStep 3281 = 2461) R2461
theorem R3283 : ∃ j : ℕ, syracuseStep^[j] 3283 = 1 := reachStep (stepEq 1 (by rfl) ⟨2462, by rfl⟩ : syracuseStep 3283 = 4925) R4925
theorem R3287 : ∃ j : ℕ, syracuseStep^[j] 3287 = 1 := reachStep (stepEq 1 (by rfl) ⟨2465, by rfl⟩ : syracuseStep 3287 = 4931) R4931
theorem R3303 : ∃ j : ℕ, syracuseStep^[j] 3303 = 1 := reachStep (stepEq 1 (by rfl) ⟨2477, by rfl⟩ : syracuseStep 3303 = 4955) R4955
theorem R3307 : ∃ j : ℕ, syracuseStep^[j] 3307 = 1 := reachStep (stepEq 1 (by rfl) ⟨2480, by rfl⟩ : syracuseStep 3307 = 4961) R4961
theorem R3315 : ∃ j : ℕ, syracuseStep^[j] 3315 = 1 := reachStep (stepEq 1 (by rfl) ⟨2486, by rfl⟩ : syracuseStep 3315 = 4973) R4973
theorem R3327 : ∃ j : ℕ, syracuseStep^[j] 3327 = 1 := reachStep (stepEq 1 (by rfl) ⟨2495, by rfl⟩ : syracuseStep 3327 = 4991) R4991
theorem R3371 : ∃ j : ℕ, syracuseStep^[j] 3371 = 1 := reachStep (stepEq 1 (by rfl) ⟨2528, by rfl⟩ : syracuseStep 3371 = 5057) R5057
theorem R3569 : ∃ j : ℕ, syracuseStep^[j] 3569 = 1 := reachStep (stepEq 2 (by rfl) ⟨1338, by rfl⟩ : syracuseStep 3569 = 2677) R2677
theorem R3573 : ∃ j : ℕ, syracuseStep^[j] 3573 = 1 := reachStep (stepEq 5 (by rfl) ⟨167, by rfl⟩ : syracuseStep 3573 = 335) R335
theorem R3577 : ∃ j : ℕ, syracuseStep^[j] 3577 = 1 := reachStep (stepEq 2 (by rfl) ⟨1341, by rfl⟩ : syracuseStep 3577 = 2683) R2683
theorem R3579 : ∃ j : ℕ, syracuseStep^[j] 3579 = 1 := reachStep (stepEq 1 (by rfl) ⟨2684, by rfl⟩ : syracuseStep 3579 = 5369) R5369
theorem R3585 : ∃ j : ℕ, syracuseStep^[j] 3585 = 1 := reachStep (stepEq 2 (by rfl) ⟨1344, by rfl⟩ : syracuseStep 3585 = 2689) R2689
theorem R3951 : ∃ j : ℕ, syracuseStep^[j] 3951 = 1 := reachStep (stepEq 1 (by rfl) ⟨2963, by rfl⟩ : syracuseStep 3951 = 5927) R5927
theorem R6381 : ∃ j : ℕ, syracuseStep^[j] 6381 = 1 := reachStep (stepEq 3 (by rfl) ⟨1196, by rfl⟩ : syracuseStep 6381 = 2393) R2393
theorem R6391 : ∃ j : ℕ, syracuseStep^[j] 6391 = 1 := reachStep (stepEq 1 (by rfl) ⟨4793, by rfl⟩ : syracuseStep 6391 = 9587) R9587
theorem R6397 : ∃ j : ℕ, syracuseStep^[j] 6397 = 1 := reachStep (stepEq 3 (by rfl) ⟨1199, by rfl⟩ : syracuseStep 6397 = 2399) R2399
theorem R6419 : ∃ j : ℕ, syracuseStep^[j] 6419 = 1 := reachStep (stepEq 1 (by rfl) ⟨4814, by rfl⟩ : syracuseStep 6419 = 9629) R9629
theorem R6427 : ∃ j : ℕ, syracuseStep^[j] 6427 = 1 := reachStep (stepEq 1 (by rfl) ⟨4820, by rfl⟩ : syracuseStep 6427 = 9641) R9641
theorem R6435 : ∃ j : ℕ, syracuseStep^[j] 6435 = 1 := reachStep (stepEq 1 (by rfl) ⟨4826, by rfl⟩ : syracuseStep 6435 = 9653) R9653
theorem R6437 : ∃ j : ℕ, syracuseStep^[j] 6437 = 1 := reachStep (stepEq 4 (by rfl) ⟨603, by rfl⟩ : syracuseStep 6437 = 1207) R1207
theorem R6443 : ∃ j : ℕ, syracuseStep^[j] 6443 = 1 := reachStep (stepEq 1 (by rfl) ⟨4832, by rfl⟩ : syracuseStep 6443 = 9665) R9665
theorem R6447 : ∃ j : ℕ, syracuseStep^[j] 6447 = 1 := reachStep (stepEq 1 (by rfl) ⟨4835, by rfl⟩ : syracuseStep 6447 = 9671) R9671
theorem R6459 : ∃ j : ℕ, syracuseStep^[j] 6459 = 1 := reachStep (stepEq 1 (by rfl) ⟨4844, by rfl⟩ : syracuseStep 6459 = 9689) R9689
theorem R6461 : ∃ j : ℕ, syracuseStep^[j] 6461 = 1 := reachStep (stepEq 3 (by rfl) ⟨1211, by rfl⟩ : syracuseStep 6461 = 2423) R2423
theorem R6509 : ∃ j : ℕ, syracuseStep^[j] 6509 = 1 := reachStep (stepEq 3 (by rfl) ⟨1220, by rfl⟩ : syracuseStep 6509 = 2441) R2441
theorem R6511 : ∃ j : ℕ, syracuseStep^[j] 6511 = 1 := reachStep (stepEq 1 (by rfl) ⟨4883, by rfl⟩ : syracuseStep 6511 = 9767) R9767
theorem R6527 : ∃ j : ℕ, syracuseStep^[j] 6527 = 1 := reachStep (stepEq 1 (by rfl) ⟨4895, by rfl⟩ : syracuseStep 6527 = 9791) R9791
theorem R6561 : ∃ j : ℕ, syracuseStep^[j] 6561 = 1 := reachStep (stepEq 2 (by rfl) ⟨2460, by rfl⟩ : syracuseStep 6561 = 4921) R4921
theorem R6563 : ∃ j : ℕ, syracuseStep^[j] 6563 = 1 := reachStep (stepEq 1 (by rfl) ⟨4922, by rfl⟩ : syracuseStep 6563 = 9845) R9845
theorem R6565 : ∃ j : ℕ, syracuseStep^[j] 6565 = 1 := reachStep (stepEq 4 (by rfl) ⟨615, by rfl⟩ : syracuseStep 6565 = 1231) R1231
theorem R6567 : ∃ j : ℕ, syracuseStep^[j] 6567 = 1 := reachStep (stepEq 1 (by rfl) ⟨4925, by rfl⟩ : syracuseStep 6567 = 9851) R9851
theorem R6573 : ∃ j : ℕ, syracuseStep^[j] 6573 = 1 := reachStep (stepEq 3 (by rfl) ⟨1232, by rfl⟩ : syracuseStep 6573 = 2465) R2465
theorem R6575 : ∃ j : ℕ, syracuseStep^[j] 6575 = 1 := reachStep (stepEq 1 (by rfl) ⟨4931, by rfl⟩ : syracuseStep 6575 = 9863) R9863
theorem R6601 : ∃ j : ℕ, syracuseStep^[j] 6601 = 1 := reachStep (stepEq 2 (by rfl) ⟨2475, by rfl⟩ : syracuseStep 6601 = 4951) R4951
theorem R6607 : ∃ j : ℕ, syracuseStep^[j] 6607 = 1 := reachStep (stepEq 1 (by rfl) ⟨4955, by rfl⟩ : syracuseStep 6607 = 9911) R9911
theorem R6615 : ∃ j : ℕ, syracuseStep^[j] 6615 = 1 := reachStep (stepEq 1 (by rfl) ⟨4961, by rfl⟩ : syracuseStep 6615 = 9923) R9923
theorem R6625 : ∃ j : ℕ, syracuseStep^[j] 6625 = 1 := reachStep (stepEq 2 (by rfl) ⟨2484, by rfl⟩ : syracuseStep 6625 = 4969) R4969
theorem R6629 : ∃ j : ℕ, syracuseStep^[j] 6629 = 1 := reachStep (stepEq 4 (by rfl) ⟨621, by rfl⟩ : syracuseStep 6629 = 1243) R1243
theorem R6633 : ∃ j : ℕ, syracuseStep^[j] 6633 = 1 := reachStep (stepEq 2 (by rfl) ⟨2487, by rfl⟩ : syracuseStep 6633 = 4975) R4975
theorem R6635 : ∃ j : ℕ, syracuseStep^[j] 6635 = 1 := reachStep (stepEq 1 (by rfl) ⟨4976, by rfl⟩ : syracuseStep 6635 = 9953) R9953
theorem R6639 : ∃ j : ℕ, syracuseStep^[j] 6639 = 1 := reachStep (stepEq 1 (by rfl) ⟨4979, by rfl⟩ : syracuseStep 6639 = 9959) R9959
theorem R6653 : ∃ j : ℕ, syracuseStep^[j] 6653 = 1 := reachStep (stepEq 3 (by rfl) ⟨1247, by rfl⟩ : syracuseStep 6653 = 2495) R2495
theorem R6743 : ∃ j : ℕ, syracuseStep^[j] 6743 = 1 := reachStep (stepEq 1 (by rfl) ⟨5057, by rfl⟩ : syracuseStep 6743 = 10115) R10115
theorem R6745 : ∃ j : ℕ, syracuseStep^[j] 6745 = 1 := reachStep (stepEq 2 (by rfl) ⟨2529, by rfl⟩ : syracuseStep 6745 = 5059) R5059
theorem R105097 : ∃ j : ℕ, syracuseStep^[j] 105097 = 1 := reachStep (stepEq 2 (by rfl) ⟨39411, by rfl⟩ : syracuseStep 105097 = 78823) R78823
theorem R7139 : ∃ j : ℕ, syracuseStep^[j] 7139 = 1 := reachStep (stepEq 1 (by rfl) ⟨5354, by rfl⟩ : syracuseStep 7139 = 10709) R10709
theorem R7159 : ∃ j : ℕ, syracuseStep^[j] 7159 = 1 := reachStep (stepEq 1 (by rfl) ⟨5369, by rfl⟩ : syracuseStep 7159 = 10739) R10739
theorem R7169 : ∃ j : ℕ, syracuseStep^[j] 7169 = 1 := reachStep (stepEq 2 (by rfl) ⟨2688, by rfl⟩ : syracuseStep 7169 = 5377) R5377
theorem R7175 : ∃ j : ℕ, syracuseStep^[j] 7175 = 1 := reachStep (stepEq 1 (by rfl) ⟨5381, by rfl⟩ : syracuseStep 7175 = 10763) R10763
theorem R7177 : ∃ j : ℕ, syracuseStep^[j] 7177 = 1 := reachStep (stepEq 2 (by rfl) ⟨2691, by rfl⟩ : syracuseStep 7177 = 5383) R5383
theorem R7919 : ∃ j : ℕ, syracuseStep^[j] 7919 = 1 := reachStep (stepEq 1 (by rfl) ⟨5939, by rfl⟩ : syracuseStep 7919 = 11879) R11879
theorem R7931 : ∃ j : ℕ, syracuseStep^[j] 7931 = 1 := reachStep (stepEq 1 (by rfl) ⟨5948, by rfl⟩ : syracuseStep 7931 = 11897) R11897
theorem R12761 : ∃ j : ℕ, syracuseStep^[j] 12761 = 1 := reachStep (stepEq 2 (by rfl) ⟨4785, by rfl⟩ : syracuseStep 12761 = 9571) R9571
theorem R12869 : ∃ j : ℕ, syracuseStep^[j] 12869 = 1 := reachStep (stepEq 4 (by rfl) ⟨1206, by rfl⟩ : syracuseStep 12869 = 2413) R2413
theorem R12887 : ∃ j : ℕ, syracuseStep^[j] 12887 = 1 := reachStep (stepEq 1 (by rfl) ⟨9665, by rfl⟩ : syracuseStep 12887 = 19331) R19331
theorem R12889 : ∃ j : ℕ, syracuseStep^[j] 12889 = 1 := reachStep (stepEq 2 (by rfl) ⟨4833, by rfl⟩ : syracuseStep 12889 = 9667) R9667
theorem R12917 : ∃ j : ℕ, syracuseStep^[j] 12917 = 1 := reachStep (stepEq 5 (by rfl) ⟨605, by rfl⟩ : syracuseStep 12917 = 1211) R1211
theorem R12919 : ∃ j : ℕ, syracuseStep^[j] 12919 = 1 := reachStep (stepEq 1 (by rfl) ⟨9689, by rfl⟩ : syracuseStep 12919 = 19379) R19379
theorem R12923 : ∃ j : ℕ, syracuseStep^[j] 12923 = 1 := reachStep (stepEq 1 (by rfl) ⟨9692, by rfl⟩ : syracuseStep 12923 = 19385) R19385
theorem R12935 : ∃ j : ℕ, syracuseStep^[j] 12935 = 1 := reachStep (stepEq 1 (by rfl) ⟨9701, by rfl⟩ : syracuseStep 12935 = 19403) R19403
theorem R13211 : ∃ j : ℕ, syracuseStep^[j] 13211 = 1 := reachStep (stepEq 1 (by rfl) ⟨9908, by rfl⟩ : syracuseStep 13211 = 19817) R19817
theorem R13213 : ∃ j : ℕ, syracuseStep^[j] 13213 = 1 := reachStep (stepEq 3 (by rfl) ⟨2477, by rfl⟩ : syracuseStep 13213 = 4955) R4955
theorem R13229 : ∃ j : ℕ, syracuseStep^[j] 13229 = 1 := reachStep (stepEq 3 (by rfl) ⟨2480, by rfl⟩ : syracuseStep 13229 = 4961) R4961
theorem R13259 : ∃ j : ℕ, syracuseStep^[j] 13259 = 1 := reachStep (stepEq 1 (by rfl) ⟨9944, by rfl⟩ : syracuseStep 13259 = 19889) R19889
theorem R13265 : ∃ j : ℕ, syracuseStep^[j] 13265 = 1 := reachStep (stepEq 2 (by rfl) ⟨4974, by rfl⟩ : syracuseStep 13265 = 9949) R9949
theorem R14309 : ∃ j : ℕ, syracuseStep^[j] 14309 = 1 := reachStep (stepEq 4 (by rfl) ⟨1341, by rfl⟩ : syracuseStep 14309 = 2683) R2683
theorem R14671 : ∃ j : ℕ, syracuseStep^[j] 14671 = 1 := reachStep (stepEq 1 (by rfl) ⟨11003, by rfl⟩ : syracuseStep 14671 = 22007) R22007
theorem R51191 : ∃ j : ℕ, syracuseStep^[j] 51191 = 1 := reachStep (stepEq 1 (by rfl) ⟨38393, by rfl⟩ : syracuseStep 51191 = 76787) R76787
theorem R55403 : ∃ j : ℕ, syracuseStep^[j] 55403 = 1 := reachStep (stepEq 1 (by rfl) ⟨41552, by rfl⟩ : syracuseStep 55403 = 83105) R83105
theorem R25595 : ∃ j : ℕ, syracuseStep^[j] 25595 = 1 := reachStep (stepEq 1 (by rfl) ⟨19196, by rfl⟩ : syracuseStep 25595 = 38393) R38393
theorem R26183 : ∃ j : ℕ, syracuseStep^[j] 26183 = 1 := reachStep (stepEq 1 (by rfl) ⟨19637, by rfl⟩ : syracuseStep 26183 = 39275) R39275
theorem R26405 : ∃ j : ℕ, syracuseStep^[j] 26405 = 1 := reachStep (stepEq 4 (by rfl) ⟨2475, by rfl⟩ : syracuseStep 26405 = 4951) R4951
theorem R26567 : ∃ j : ℕ, syracuseStep^[j] 26567 = 1 := reachStep (stepEq 1 (by rfl) ⟨19925, by rfl⟩ : syracuseStep 26567 = 39851) R39851
theorem R28613 : ∃ j : ℕ, syracuseStep^[j] 28613 = 1 := reachStep (stepEq 4 (by rfl) ⟨2682, by rfl⟩ : syracuseStep 28613 = 5365) R5365
theorem R28637 : ∃ j : ℕ, syracuseStep^[j] 28637 = 1 := reachStep (stepEq 3 (by rfl) ⟨5369, by rfl⟩ : syracuseStep 28637 = 10739) R10739
theorem R28673 : ∃ j : ℕ, syracuseStep^[j] 28673 = 1 := reachStep (stepEq 2 (by rfl) ⟨10752, by rfl⟩ : syracuseStep 28673 = 21505) R21505
theorem R297 : ∃ j : ℕ, syracuseStep^[j] 297 = 1 := reachStep (stepEq 2 (by rfl) ⟨111, by rfl⟩ : syracuseStep 297 = 223) R223
theorem R593 : ∃ j : ℕ, syracuseStep^[j] 593 = 1 := reachStep (stepEq 2 (by rfl) ⟨222, by rfl⟩ : syracuseStep 593 = 445) R445
theorem R595 : ∃ j : ℕ, syracuseStep^[j] 595 = 1 := reachStep (stepEq 1 (by rfl) ⟨446, by rfl⟩ : syracuseStep 595 = 893) R893
theorem R1063 : ∃ j : ℕ, syracuseStep^[j] 1063 = 1 := reachStep (stepEq 1 (by rfl) ⟨797, by rfl⟩ : syracuseStep 1063 = 1595) R1595
theorem R1065 : ∃ j : ℕ, syracuseStep^[j] 1065 = 1 := reachStep (stepEq 2 (by rfl) ⟨399, by rfl⟩ : syracuseStep 1065 = 799) R799
theorem R1095 : ∃ j : ℕ, syracuseStep^[j] 1095 = 1 := reachStep (stepEq 1 (by rfl) ⟨821, by rfl⟩ : syracuseStep 1095 = 1643) R1643
theorem R1187 : ∃ j : ℕ, syracuseStep^[j] 1187 = 1 := reachStep (stepEq 1 (by rfl) ⟨890, by rfl⟩ : syracuseStep 1187 = 1781) R1781
theorem R1189 : ∃ j : ℕ, syracuseStep^[j] 1189 = 1 := reachStep (stepEq 4 (by rfl) ⟨111, by rfl⟩ : syracuseStep 1189 = 223) R223
theorem R34127 : ∃ j : ℕ, syracuseStep^[j] 34127 = 1 := reachStep (stepEq 1 (by rfl) ⟨25595, by rfl⟩ : syracuseStep 34127 = 51191) R51191
theorem R34445 : ∃ j : ℕ, syracuseStep^[j] 34445 = 1 := reachStep (stepEq 3 (by rfl) ⟨6458, by rfl⟩ : syracuseStep 34445 = 12917) R12917
theorem R2127 : ∃ j : ℕ, syracuseStep^[j] 2127 = 1 := reachStep (stepEq 1 (by rfl) ⟨1595, by rfl⟩ : syracuseStep 2127 = 3191) R3191
theorem R2131 : ∃ j : ℕ, syracuseStep^[j] 2131 = 1 := reachStep (stepEq 1 (by rfl) ⟨1598, by rfl⟩ : syracuseStep 2131 = 3197) R3197
theorem R2139 : ∃ j : ℕ, syracuseStep^[j] 2139 = 1 := reachStep (stepEq 1 (by rfl) ⟨1604, by rfl⟩ : syracuseStep 2139 = 3209) R3209
theorem R2145 : ∃ j : ℕ, syracuseStep^[j] 2145 = 1 := reachStep (stepEq 2 (by rfl) ⟨804, by rfl⟩ : syracuseStep 2145 = 1609) R1609
theorem R2153 : ∃ j : ℕ, syracuseStep^[j] 2153 = 1 := reachStep (stepEq 2 (by rfl) ⟨807, by rfl⟩ : syracuseStep 2153 = 1615) R1615
theorem R2169 : ∃ j : ℕ, syracuseStep^[j] 2169 = 1 := reachStep (stepEq 2 (by rfl) ⟨813, by rfl⟩ : syracuseStep 2169 = 1627) R1627
theorem R2175 : ∃ j : ℕ, syracuseStep^[j] 2175 = 1 := reachStep (stepEq 1 (by rfl) ⟨1631, by rfl⟩ : syracuseStep 2175 = 3263) R3263
theorem R2187 : ∃ j : ℕ, syracuseStep^[j] 2187 = 1 := reachStep (stepEq 1 (by rfl) ⟨1640, by rfl⟩ : syracuseStep 2187 = 3281) R3281
theorem R2191 : ∃ j : ℕ, syracuseStep^[j] 2191 = 1 := reachStep (stepEq 1 (by rfl) ⟨1643, by rfl⟩ : syracuseStep 2191 = 3287) R3287
theorem R2209 : ∃ j : ℕ, syracuseStep^[j] 2209 = 1 := reachStep (stepEq 2 (by rfl) ⟨828, by rfl⟩ : syracuseStep 2209 = 1657) R1657
theorem R2217 : ∃ j : ℕ, syracuseStep^[j] 2217 = 1 := reachStep (stepEq 2 (by rfl) ⟨831, by rfl⟩ : syracuseStep 2217 = 1663) R1663
theorem R2247 : ∃ j : ℕ, syracuseStep^[j] 2247 = 1 := reachStep (stepEq 1 (by rfl) ⟨1685, by rfl⟩ : syracuseStep 2247 = 3371) R3371
theorem R2373 : ∃ j : ℕ, syracuseStep^[j] 2373 = 1 := reachStep (stepEq 4 (by rfl) ⟨222, by rfl⟩ : syracuseStep 2373 = 445) R445
theorem R2379 : ∃ j : ℕ, syracuseStep^[j] 2379 = 1 := reachStep (stepEq 1 (by rfl) ⟨1784, by rfl⟩ : syracuseStep 2379 = 3569) R3569
theorem R2381 : ∃ j : ℕ, syracuseStep^[j] 2381 = 1 := reachStep (stepEq 3 (by rfl) ⟨446, by rfl⟩ : syracuseStep 2381 = 893) R893
theorem R35477 : ∃ j : ℕ, syracuseStep^[j] 35477 = 1 := reachStep (stepEq 6 (by rfl) ⟨831, by rfl⟩ : syracuseStep 35477 = 1663) R1663
theorem R35957 : ∃ j : ℕ, syracuseStep^[j] 35957 = 1 := reachStep (stepEq 5 (by rfl) ⟨1685, by rfl⟩ : syracuseStep 35957 = 3371) R3371
theorem R36935 : ∃ j : ℕ, syracuseStep^[j] 36935 = 1 := reachStep (stepEq 1 (by rfl) ⟨27701, by rfl⟩ : syracuseStep 36935 = 55403) R55403
theorem R4253 : ∃ j : ℕ, syracuseStep^[j] 4253 = 1 := reachStep (stepEq 3 (by rfl) ⟨797, by rfl⟩ : syracuseStep 4253 = 1595) R1595
theorem R4261 : ∃ j : ℕ, syracuseStep^[j] 4261 = 1 := reachStep (stepEq 4 (by rfl) ⟨399, by rfl⟩ : syracuseStep 4261 = 799) R799
theorem R4279 : ∃ j : ℕ, syracuseStep^[j] 4279 = 1 := reachStep (stepEq 1 (by rfl) ⟨3209, by rfl⟩ : syracuseStep 4279 = 6419) R6419
theorem R4289 : ∃ j : ℕ, syracuseStep^[j] 4289 = 1 := reachStep (stepEq 2 (by rfl) ⟨1608, by rfl⟩ : syracuseStep 4289 = 3217) R3217
theorem R4291 : ∃ j : ℕ, syracuseStep^[j] 4291 = 1 := reachStep (stepEq 1 (by rfl) ⟨3218, by rfl⟩ : syracuseStep 4291 = 6437) R6437
theorem R4295 : ∃ j : ℕ, syracuseStep^[j] 4295 = 1 := reachStep (stepEq 1 (by rfl) ⟨3221, by rfl⟩ : syracuseStep 4295 = 6443) R6443
theorem R4305 : ∃ j : ℕ, syracuseStep^[j] 4305 = 1 := reachStep (stepEq 2 (by rfl) ⟨1614, by rfl⟩ : syracuseStep 4305 = 3229) R3229
theorem R4307 : ∃ j : ℕ, syracuseStep^[j] 4307 = 1 := reachStep (stepEq 1 (by rfl) ⟨3230, by rfl⟩ : syracuseStep 4307 = 6461) R6461
theorem R4339 : ∃ j : ℕ, syracuseStep^[j] 4339 = 1 := reachStep (stepEq 1 (by rfl) ⟨3254, by rfl⟩ : syracuseStep 4339 = 6509) R6509
theorem R4351 : ∃ j : ℕ, syracuseStep^[j] 4351 = 1 := reachStep (stepEq 1 (by rfl) ⟨3263, by rfl⟩ : syracuseStep 4351 = 6527) R6527
theorem R4375 : ∃ j : ℕ, syracuseStep^[j] 4375 = 1 := reachStep (stepEq 1 (by rfl) ⟨3281, by rfl⟩ : syracuseStep 4375 = 6563) R6563
theorem R4377 : ∃ j : ℕ, syracuseStep^[j] 4377 = 1 := reachStep (stepEq 2 (by rfl) ⟨1641, by rfl⟩ : syracuseStep 4377 = 3283) R3283
theorem R4381 : ∃ j : ℕ, syracuseStep^[j] 4381 = 1 := reachStep (stepEq 3 (by rfl) ⟨821, by rfl⟩ : syracuseStep 4381 = 1643) R1643
theorem R4383 : ∃ j : ℕ, syracuseStep^[j] 4383 = 1 := reachStep (stepEq 1 (by rfl) ⟨3287, by rfl⟩ : syracuseStep 4383 = 6575) R6575
theorem R4409 : ∃ j : ℕ, syracuseStep^[j] 4409 = 1 := reachStep (stepEq 2 (by rfl) ⟨1653, by rfl⟩ : syracuseStep 4409 = 3307) R3307
theorem R4419 : ∃ j : ℕ, syracuseStep^[j] 4419 = 1 := reachStep (stepEq 1 (by rfl) ⟨3314, by rfl⟩ : syracuseStep 4419 = 6629) R6629
theorem R4423 : ∃ j : ℕ, syracuseStep^[j] 4423 = 1 := reachStep (stepEq 1 (by rfl) ⟨3317, by rfl⟩ : syracuseStep 4423 = 6635) R6635
theorem R4435 : ∃ j : ℕ, syracuseStep^[j] 4435 = 1 := reachStep (stepEq 1 (by rfl) ⟨3326, by rfl⟩ : syracuseStep 4435 = 6653) R6653
theorem R4495 : ∃ j : ℕ, syracuseStep^[j] 4495 = 1 := reachStep (stepEq 1 (by rfl) ⟨3371, by rfl⟩ : syracuseStep 4495 = 6743) R6743
theorem R4749 : ∃ j : ℕ, syracuseStep^[j] 4749 = 1 := reachStep (stepEq 3 (by rfl) ⟨890, by rfl⟩ : syracuseStep 4749 = 1781) R1781
theorem R4757 : ∃ j : ℕ, syracuseStep^[j] 4757 = 1 := reachStep (stepEq 6 (by rfl) ⟨111, by rfl⟩ : syracuseStep 4757 = 223) R223
theorem R4759 : ∃ j : ℕ, syracuseStep^[j] 4759 = 1 := reachStep (stepEq 1 (by rfl) ⟨3569, by rfl⟩ : syracuseStep 4759 = 7139) R7139
theorem R4769 : ∃ j : ℕ, syracuseStep^[j] 4769 = 1 := reachStep (stepEq 2 (by rfl) ⟨1788, by rfl⟩ : syracuseStep 4769 = 3577) R3577
theorem R4779 : ∃ j : ℕ, syracuseStep^[j] 4779 = 1 := reachStep (stepEq 1 (by rfl) ⟨3584, by rfl⟩ : syracuseStep 4779 = 7169) R7169
theorem R4783 : ∃ j : ℕ, syracuseStep^[j] 4783 = 1 := reachStep (stepEq 1 (by rfl) ⟨3587, by rfl⟩ : syracuseStep 4783 = 7175) R7175
theorem R5279 : ∃ j : ℕ, syracuseStep^[j] 5279 = 1 := reachStep (stepEq 1 (by rfl) ⟨3959, by rfl⟩ : syracuseStep 5279 = 7919) R7919
theorem R5287 : ∃ j : ℕ, syracuseStep^[j] 5287 = 1 := reachStep (stepEq 1 (by rfl) ⟨3965, by rfl⟩ : syracuseStep 5287 = 7931) R7931
theorem R38069 : ∃ j : ℕ, syracuseStep^[j] 38069 = 1 := reachStep (stepEq 5 (by rfl) ⟨1784, by rfl⟩ : syracuseStep 38069 = 3569) R3569
theorem R8507 : ∃ j : ℕ, syracuseStep^[j] 8507 = 1 := reachStep (stepEq 1 (by rfl) ⟨6380, by rfl⟩ : syracuseStep 8507 = 12761) R12761
theorem R8509 : ∃ j : ℕ, syracuseStep^[j] 8509 = 1 := reachStep (stepEq 3 (by rfl) ⟨1595, by rfl⟩ : syracuseStep 8509 = 3191) R3191
theorem R8525 : ∃ j : ℕ, syracuseStep^[j] 8525 = 1 := reachStep (stepEq 3 (by rfl) ⟨1598, by rfl⟩ : syracuseStep 8525 = 3197) R3197
theorem R8579 : ∃ j : ℕ, syracuseStep^[j] 8579 = 1 := reachStep (stepEq 1 (by rfl) ⟨6434, by rfl⟩ : syracuseStep 8579 = 12869) R12869
theorem R8581 : ∃ j : ℕ, syracuseStep^[j] 8581 = 1 := reachStep (stepEq 4 (by rfl) ⟨804, by rfl⟩ : syracuseStep 8581 = 1609) R1609
theorem R8591 : ∃ j : ℕ, syracuseStep^[j] 8591 = 1 := reachStep (stepEq 1 (by rfl) ⟨6443, by rfl⟩ : syracuseStep 8591 = 12887) R12887
theorem R8615 : ∃ j : ℕ, syracuseStep^[j] 8615 = 1 := reachStep (stepEq 1 (by rfl) ⟨6461, by rfl⟩ : syracuseStep 8615 = 12923) R12923
theorem R8623 : ∃ j : ℕ, syracuseStep^[j] 8623 = 1 := reachStep (stepEq 1 (by rfl) ⟨6467, by rfl⟩ : syracuseStep 8623 = 12935) R12935
theorem R8681 : ∃ j : ℕ, syracuseStep^[j] 8681 = 1 := reachStep (stepEq 2 (by rfl) ⟨3255, by rfl⟩ : syracuseStep 8681 = 6511) R6511
theorem R8753 : ∃ j : ℕ, syracuseStep^[j] 8753 = 1 := reachStep (stepEq 2 (by rfl) ⟨3282, by rfl⟩ : syracuseStep 8753 = 6565) R6565
theorem R8765 : ∃ j : ℕ, syracuseStep^[j] 8765 = 1 := reachStep (stepEq 3 (by rfl) ⟨1643, by rfl⟩ : syracuseStep 8765 = 3287) R3287
theorem R8801 : ∃ j : ℕ, syracuseStep^[j] 8801 = 1 := reachStep (stepEq 2 (by rfl) ⟨3300, by rfl⟩ : syracuseStep 8801 = 6601) R6601
theorem R8807 : ∃ j : ℕ, syracuseStep^[j] 8807 = 1 := reachStep (stepEq 1 (by rfl) ⟨6605, by rfl⟩ : syracuseStep 8807 = 13211) R13211
theorem R8819 : ∃ j : ℕ, syracuseStep^[j] 8819 = 1 := reachStep (stepEq 1 (by rfl) ⟨6614, by rfl⟩ : syracuseStep 8819 = 13229) R13229
theorem R8837 : ∃ j : ℕ, syracuseStep^[j] 8837 = 1 := reachStep (stepEq 4 (by rfl) ⟨828, by rfl⟩ : syracuseStep 8837 = 1657) R1657
theorem R8839 : ∃ j : ℕ, syracuseStep^[j] 8839 = 1 := reachStep (stepEq 1 (by rfl) ⟨6629, by rfl⟩ : syracuseStep 8839 = 13259) R13259
theorem R8843 : ∃ j : ℕ, syracuseStep^[j] 8843 = 1 := reachStep (stepEq 1 (by rfl) ⟨6632, by rfl⟩ : syracuseStep 8843 = 13265) R13265
theorem R8869 : ∃ j : ℕ, syracuseStep^[j] 8869 = 1 := reachStep (stepEq 4 (by rfl) ⟨831, by rfl⟩ : syracuseStep 8869 = 1663) R1663
theorem R8993 : ∃ j : ℕ, syracuseStep^[j] 8993 = 1 := reachStep (stepEq 2 (by rfl) ⟨3372, by rfl⟩ : syracuseStep 8993 = 6745) R6745
theorem R140129 : ∃ j : ℕ, syracuseStep^[j] 140129 = 1 := reachStep (stepEq 2 (by rfl) ⟨52548, by rfl⟩ : syracuseStep 140129 = 105097) R105097
theorem R9517 : ∃ j : ℕ, syracuseStep^[j] 9517 = 1 := reachStep (stepEq 3 (by rfl) ⟨1784, by rfl⟩ : syracuseStep 9517 = 3569) R3569
theorem R9539 : ∃ j : ℕ, syracuseStep^[j] 9539 = 1 := reachStep (stepEq 1 (by rfl) ⟨7154, by rfl⟩ : syracuseStep 9539 = 14309) R14309
theorem R9545 : ∃ j : ℕ, syracuseStep^[j] 9545 = 1 := reachStep (stepEq 2 (by rfl) ⟨3579, by rfl⟩ : syracuseStep 9545 = 7159) R7159
theorem R9569 : ∃ j : ℕ, syracuseStep^[j] 9569 = 1 := reachStep (stepEq 2 (by rfl) ⟨3588, by rfl⟩ : syracuseStep 9569 = 7177) R7177
theorem R17063 : ∃ j : ℕ, syracuseStep^[j] 17063 = 1 := reachStep (stepEq 1 (by rfl) ⟨12797, by rfl⟩ : syracuseStep 17063 = 25595) R25595
theorem R17117 : ∃ j : ℕ, syracuseStep^[j] 17117 = 1 := reachStep (stepEq 3 (by rfl) ⟨3209, by rfl⟩ : syracuseStep 17117 = 6419) R6419
theorem R17185 : ∃ j : ℕ, syracuseStep^[j] 17185 = 1 := reachStep (stepEq 2 (by rfl) ⟨6444, by rfl⟩ : syracuseStep 17185 = 12889) R12889
theorem R17225 : ∃ j : ℕ, syracuseStep^[j] 17225 = 1 := reachStep (stepEq 2 (by rfl) ⟨6459, by rfl⟩ : syracuseStep 17225 = 12919) R12919
theorem R17405 : ∃ j : ℕ, syracuseStep^[j] 17405 = 1 := reachStep (stepEq 3 (by rfl) ⟨3263, by rfl⟩ : syracuseStep 17405 = 6527) R6527
theorem R17455 : ∃ j : ℕ, syracuseStep^[j] 17455 = 1 := reachStep (stepEq 1 (by rfl) ⟨13091, by rfl⟩ : syracuseStep 17455 = 26183) R26183
theorem R17603 : ∃ j : ℕ, syracuseStep^[j] 17603 = 1 := reachStep (stepEq 1 (by rfl) ⟨13202, by rfl⟩ : syracuseStep 17603 = 26405) R26405
theorem R17617 : ∃ j : ℕ, syracuseStep^[j] 17617 = 1 := reachStep (stepEq 2 (by rfl) ⟨6606, by rfl⟩ : syracuseStep 17617 = 13213) R13213
theorem R17711 : ∃ j : ℕ, syracuseStep^[j] 17711 = 1 := reachStep (stepEq 1 (by rfl) ⟨13283, by rfl⟩ : syracuseStep 17711 = 26567) R26567
theorem R17981 : ∃ j : ℕ, syracuseStep^[j] 17981 = 1 := reachStep (stepEq 3 (by rfl) ⟨3371, by rfl⟩ : syracuseStep 17981 = 6743) R6743
theorem R19075 : ∃ j : ℕ, syracuseStep^[j] 19075 = 1 := reachStep (stepEq 1 (by rfl) ⟨14306, by rfl⟩ : syracuseStep 19075 = 28613) R28613
theorem R19091 : ∃ j : ℕ, syracuseStep^[j] 19091 = 1 := reachStep (stepEq 1 (by rfl) ⟨14318, by rfl⟩ : syracuseStep 19091 = 28637) R28637
theorem R19115 : ∃ j : ℕ, syracuseStep^[j] 19115 = 1 := reachStep (stepEq 1 (by rfl) ⟨14336, by rfl⟩ : syracuseStep 19115 = 28673) R28673
theorem R19133 : ∃ j : ℕ, syracuseStep^[j] 19133 = 1 := reachStep (stepEq 3 (by rfl) ⟨3587, by rfl⟩ : syracuseStep 19133 = 7175) R7175
theorem R19561 : ∃ j : ℕ, syracuseStep^[j] 19561 = 1 := reachStep (stepEq 2 (by rfl) ⟨7335, by rfl⟩ : syracuseStep 19561 = 14671) R14671
theorem R395 : ∃ j : ℕ, syracuseStep^[j] 395 = 1 := reachStep (stepEq 1 (by rfl) ⟨296, by rfl⟩ : syracuseStep 395 = 593) R593
theorem R791 : ∃ j : ℕ, syracuseStep^[j] 791 = 1 := reachStep (stepEq 1 (by rfl) ⟨593, by rfl⟩ : syracuseStep 791 = 1187) R1187
theorem R793 : ∃ j : ℕ, syracuseStep^[j] 793 = 1 := reachStep (stepEq 2 (by rfl) ⟨297, by rfl⟩ : syracuseStep 793 = 595) R595
theorem R1417 : ∃ j : ℕ, syracuseStep^[j] 1417 = 1 := reachStep (stepEq 2 (by rfl) ⟨531, by rfl⟩ : syracuseStep 1417 = 1063) R1063
theorem R1435 : ∃ j : ℕ, syracuseStep^[j] 1435 = 1 := reachStep (stepEq 1 (by rfl) ⟨1076, by rfl⟩ : syracuseStep 1435 = 2153) R2153
theorem R1581 : ∃ j : ℕ, syracuseStep^[j] 1581 = 1 := reachStep (stepEq 3 (by rfl) ⟨296, by rfl⟩ : syracuseStep 1581 = 593) R593
theorem R1585 : ∃ j : ℕ, syracuseStep^[j] 1585 = 1 := reachStep (stepEq 2 (by rfl) ⟨594, by rfl⟩ : syracuseStep 1585 = 1189) R1189
theorem R1587 : ∃ j : ℕ, syracuseStep^[j] 1587 = 1 := reachStep (stepEq 1 (by rfl) ⟨1190, by rfl⟩ : syracuseStep 1587 = 2381) R2381
theorem R2835 : ∃ j : ℕ, syracuseStep^[j] 2835 = 1 := reachStep (stepEq 1 (by rfl) ⟨2126, by rfl⟩ : syracuseStep 2835 = 4253) R4253
theorem R2841 : ∃ j : ℕ, syracuseStep^[j] 2841 = 1 := reachStep (stepEq 2 (by rfl) ⟨1065, by rfl⟩ : syracuseStep 2841 = 2131) R2131
theorem R2859 : ∃ j : ℕ, syracuseStep^[j] 2859 = 1 := reachStep (stepEq 1 (by rfl) ⟨2144, by rfl⟩ : syracuseStep 2859 = 4289) R4289
theorem R2863 : ∃ j : ℕ, syracuseStep^[j] 2863 = 1 := reachStep (stepEq 1 (by rfl) ⟨2147, by rfl⟩ : syracuseStep 2863 = 4295) R4295
theorem R2871 : ∃ j : ℕ, syracuseStep^[j] 2871 = 1 := reachStep (stepEq 1 (by rfl) ⟨2153, by rfl⟩ : syracuseStep 2871 = 4307) R4307
theorem R2921 : ∃ j : ℕ, syracuseStep^[j] 2921 = 1 := reachStep (stepEq 2 (by rfl) ⟨1095, by rfl⟩ : syracuseStep 2921 = 2191) R2191
theorem R2939 : ∃ j : ℕ, syracuseStep^[j] 2939 = 1 := reachStep (stepEq 1 (by rfl) ⟨2204, by rfl⟩ : syracuseStep 2939 = 4409) R4409
theorem R2945 : ∃ j : ℕ, syracuseStep^[j] 2945 = 1 := reachStep (stepEq 2 (by rfl) ⟨1104, by rfl⟩ : syracuseStep 2945 = 2209) R2209
theorem R3165 : ∃ j : ℕ, syracuseStep^[j] 3165 = 1 := reachStep (stepEq 3 (by rfl) ⟨593, by rfl⟩ : syracuseStep 3165 = 1187) R1187
theorem R3171 : ∃ j : ℕ, syracuseStep^[j] 3171 = 1 := reachStep (stepEq 1 (by rfl) ⟨2378, by rfl⟩ : syracuseStep 3171 = 4757) R4757
theorem R3173 : ∃ j : ℕ, syracuseStep^[j] 3173 = 1 := reachStep (stepEq 4 (by rfl) ⟨297, by rfl⟩ : syracuseStep 3173 = 595) R595
theorem R3179 : ∃ j : ℕ, syracuseStep^[j] 3179 = 1 := reachStep (stepEq 1 (by rfl) ⟨2384, by rfl⟩ : syracuseStep 3179 = 4769) R4769
theorem R3519 : ∃ j : ℕ, syracuseStep^[j] 3519 = 1 := reachStep (stepEq 1 (by rfl) ⟨2639, by rfl⟩ : syracuseStep 3519 = 5279) R5279
theorem R5669 : ∃ j : ℕ, syracuseStep^[j] 5669 = 1 := reachStep (stepEq 4 (by rfl) ⟨531, by rfl⟩ : syracuseStep 5669 = 1063) R1063
theorem R5671 : ∃ j : ℕ, syracuseStep^[j] 5671 = 1 := reachStep (stepEq 1 (by rfl) ⟨4253, by rfl⟩ : syracuseStep 5671 = 8507) R8507
theorem R5681 : ∃ j : ℕ, syracuseStep^[j] 5681 = 1 := reachStep (stepEq 2 (by rfl) ⟨2130, by rfl⟩ : syracuseStep 5681 = 4261) R4261
theorem R5683 : ∃ j : ℕ, syracuseStep^[j] 5683 = 1 := reachStep (stepEq 1 (by rfl) ⟨4262, by rfl⟩ : syracuseStep 5683 = 8525) R8525
theorem R5705 : ∃ j : ℕ, syracuseStep^[j] 5705 = 1 := reachStep (stepEq 2 (by rfl) ⟨2139, by rfl⟩ : syracuseStep 5705 = 4279) R4279
theorem R5719 : ∃ j : ℕ, syracuseStep^[j] 5719 = 1 := reachStep (stepEq 1 (by rfl) ⟨4289, by rfl⟩ : syracuseStep 5719 = 8579) R8579
theorem R5721 : ∃ j : ℕ, syracuseStep^[j] 5721 = 1 := reachStep (stepEq 2 (by rfl) ⟨2145, by rfl⟩ : syracuseStep 5721 = 4291) R4291
theorem R5727 : ∃ j : ℕ, syracuseStep^[j] 5727 = 1 := reachStep (stepEq 1 (by rfl) ⟨4295, by rfl⟩ : syracuseStep 5727 = 8591) R8591
theorem R5741 : ∃ j : ℕ, syracuseStep^[j] 5741 = 1 := reachStep (stepEq 3 (by rfl) ⟨1076, by rfl⟩ : syracuseStep 5741 = 2153) R2153
theorem R5743 : ∃ j : ℕ, syracuseStep^[j] 5743 = 1 := reachStep (stepEq 1 (by rfl) ⟨4307, by rfl⟩ : syracuseStep 5743 = 8615) R8615
theorem R5785 : ∃ j : ℕ, syracuseStep^[j] 5785 = 1 := reachStep (stepEq 2 (by rfl) ⟨2169, by rfl⟩ : syracuseStep 5785 = 4339) R4339
theorem R5787 : ∃ j : ℕ, syracuseStep^[j] 5787 = 1 := reachStep (stepEq 1 (by rfl) ⟨4340, by rfl⟩ : syracuseStep 5787 = 8681) R8681
theorem R5801 : ∃ j : ℕ, syracuseStep^[j] 5801 = 1 := reachStep (stepEq 2 (by rfl) ⟨2175, by rfl⟩ : syracuseStep 5801 = 4351) R4351
theorem R5833 : ∃ j : ℕ, syracuseStep^[j] 5833 = 1 := reachStep (stepEq 2 (by rfl) ⟨2187, by rfl⟩ : syracuseStep 5833 = 4375) R4375
theorem R5835 : ∃ j : ℕ, syracuseStep^[j] 5835 = 1 := reachStep (stepEq 1 (by rfl) ⟨4376, by rfl⟩ : syracuseStep 5835 = 8753) R8753
theorem R5841 : ∃ j : ℕ, syracuseStep^[j] 5841 = 1 := reachStep (stepEq 2 (by rfl) ⟨2190, by rfl⟩ : syracuseStep 5841 = 4381) R4381
theorem R5843 : ∃ j : ℕ, syracuseStep^[j] 5843 = 1 := reachStep (stepEq 1 (by rfl) ⟨4382, by rfl⟩ : syracuseStep 5843 = 8765) R8765
theorem R5867 : ∃ j : ℕ, syracuseStep^[j] 5867 = 1 := reachStep (stepEq 1 (by rfl) ⟨4400, by rfl⟩ : syracuseStep 5867 = 8801) R8801
theorem R5871 : ∃ j : ℕ, syracuseStep^[j] 5871 = 1 := reachStep (stepEq 1 (by rfl) ⟨4403, by rfl⟩ : syracuseStep 5871 = 8807) R8807
theorem R5879 : ∃ j : ℕ, syracuseStep^[j] 5879 = 1 := reachStep (stepEq 1 (by rfl) ⟨4409, by rfl⟩ : syracuseStep 5879 = 8819) R8819
theorem R5891 : ∃ j : ℕ, syracuseStep^[j] 5891 = 1 := reachStep (stepEq 1 (by rfl) ⟨4418, by rfl⟩ : syracuseStep 5891 = 8837) R8837
theorem R5895 : ∃ j : ℕ, syracuseStep^[j] 5895 = 1 := reachStep (stepEq 1 (by rfl) ⟨4421, by rfl⟩ : syracuseStep 5895 = 8843) R8843
theorem R5897 : ∃ j : ℕ, syracuseStep^[j] 5897 = 1 := reachStep (stepEq 2 (by rfl) ⟨2211, by rfl⟩ : syracuseStep 5897 = 4423) R4423
theorem R5913 : ∃ j : ℕ, syracuseStep^[j] 5913 = 1 := reachStep (stepEq 2 (by rfl) ⟨2217, by rfl⟩ : syracuseStep 5913 = 4435) R4435
theorem R5993 : ∃ j : ℕ, syracuseStep^[j] 5993 = 1 := reachStep (stepEq 2 (by rfl) ⟨2247, by rfl⟩ : syracuseStep 5993 = 4495) R4495
theorem R5995 : ∃ j : ℕ, syracuseStep^[j] 5995 = 1 := reachStep (stepEq 1 (by rfl) ⟨4496, by rfl⟩ : syracuseStep 5995 = 8993) R8993
theorem R6325 : ∃ j : ℕ, syracuseStep^[j] 6325 = 1 := reachStep (stepEq 5 (by rfl) ⟨296, by rfl⟩ : syracuseStep 6325 = 593) R593
theorem R6341 : ∃ j : ℕ, syracuseStep^[j] 6341 = 1 := reachStep (stepEq 4 (by rfl) ⟨594, by rfl⟩ : syracuseStep 6341 = 1189) R1189
theorem R6345 : ∃ j : ℕ, syracuseStep^[j] 6345 = 1 := reachStep (stepEq 2 (by rfl) ⟨2379, by rfl⟩ : syracuseStep 6345 = 4759) R4759
theorem R6349 : ∃ j : ℕ, syracuseStep^[j] 6349 = 1 := reachStep (stepEq 3 (by rfl) ⟨1190, by rfl⟩ : syracuseStep 6349 = 2381) R2381
theorem R6359 : ∃ j : ℕ, syracuseStep^[j] 6359 = 1 := reachStep (stepEq 1 (by rfl) ⟨4769, by rfl⟩ : syracuseStep 6359 = 9539) R9539
theorem R6363 : ∃ j : ℕ, syracuseStep^[j] 6363 = 1 := reachStep (stepEq 1 (by rfl) ⟨4772, by rfl⟩ : syracuseStep 6363 = 9545) R9545
theorem R6377 : ∃ j : ℕ, syracuseStep^[j] 6377 = 1 := reachStep (stepEq 2 (by rfl) ⟨2391, by rfl⟩ : syracuseStep 6377 = 4783) R4783
theorem R6379 : ∃ j : ℕ, syracuseStep^[j] 6379 = 1 := reachStep (stepEq 1 (by rfl) ⟨4784, by rfl⟩ : syracuseStep 6379 = 9569) R9569
theorem R7049 : ∃ j : ℕ, syracuseStep^[j] 7049 = 1 := reachStep (stepEq 2 (by rfl) ⟨2643, by rfl⟩ : syracuseStep 7049 = 5287) R5287
theorem R11345 : ∃ j : ℕ, syracuseStep^[j] 11345 = 1 := reachStep (stepEq 2 (by rfl) ⟨4254, by rfl⟩ : syracuseStep 11345 = 8509) R8509
theorem R11375 : ∃ j : ℕ, syracuseStep^[j] 11375 = 1 := reachStep (stepEq 1 (by rfl) ⟨8531, by rfl⟩ : syracuseStep 11375 = 17063) R17063
theorem R11411 : ∃ j : ℕ, syracuseStep^[j] 11411 = 1 := reachStep (stepEq 1 (by rfl) ⟨8558, by rfl⟩ : syracuseStep 11411 = 17117) R17117
theorem R11441 : ∃ j : ℕ, syracuseStep^[j] 11441 = 1 := reachStep (stepEq 2 (by rfl) ⟨4290, by rfl⟩ : syracuseStep 11441 = 8581) R8581
theorem R11483 : ∃ j : ℕ, syracuseStep^[j] 11483 = 1 := reachStep (stepEq 1 (by rfl) ⟨8612, by rfl⟩ : syracuseStep 11483 = 17225) R17225
theorem R11497 : ∃ j : ℕ, syracuseStep^[j] 11497 = 1 := reachStep (stepEq 2 (by rfl) ⟨4311, by rfl⟩ : syracuseStep 11497 = 8623) R8623
theorem R11603 : ∃ j : ℕ, syracuseStep^[j] 11603 = 1 := reachStep (stepEq 1 (by rfl) ⟨8702, by rfl⟩ : syracuseStep 11603 = 17405) R17405
theorem R11735 : ∃ j : ℕ, syracuseStep^[j] 11735 = 1 := reachStep (stepEq 1 (by rfl) ⟨8801, by rfl⟩ : syracuseStep 11735 = 17603) R17603
theorem R11785 : ∃ j : ℕ, syracuseStep^[j] 11785 = 1 := reachStep (stepEq 2 (by rfl) ⟨4419, by rfl⟩ : syracuseStep 11785 = 8839) R8839
theorem R11807 : ∃ j : ℕ, syracuseStep^[j] 11807 = 1 := reachStep (stepEq 1 (by rfl) ⟨8855, by rfl⟩ : syracuseStep 11807 = 17711) R17711
theorem R11825 : ∃ j : ℕ, syracuseStep^[j] 11825 = 1 := reachStep (stepEq 2 (by rfl) ⟨4434, by rfl⟩ : syracuseStep 11825 = 8869) R8869
theorem R11987 : ∃ j : ℕ, syracuseStep^[j] 11987 = 1 := reachStep (stepEq 1 (by rfl) ⟨8990, by rfl⟩ : syracuseStep 11987 = 17981) R17981
theorem R12689 : ∃ j : ℕ, syracuseStep^[j] 12689 = 1 := reachStep (stepEq 2 (by rfl) ⟨4758, by rfl⟩ : syracuseStep 12689 = 9517) R9517
theorem R12727 : ∃ j : ℕ, syracuseStep^[j] 12727 = 1 := reachStep (stepEq 1 (by rfl) ⟨9545, by rfl⟩ : syracuseStep 12727 = 19091) R19091
theorem R12743 : ∃ j : ℕ, syracuseStep^[j] 12743 = 1 := reachStep (stepEq 1 (by rfl) ⟨9557, by rfl⟩ : syracuseStep 12743 = 19115) R19115
theorem R12755 : ∃ j : ℕ, syracuseStep^[j] 12755 = 1 := reachStep (stepEq 1 (by rfl) ⟨9566, by rfl⟩ : syracuseStep 12755 = 19133) R19133
theorem R47141 : ∃ j : ℕ, syracuseStep^[j] 47141 = 1 := reachStep (stepEq 4 (by rfl) ⟨4419, by rfl⟩ : syracuseStep 47141 = 8839) R8839
theorem R22751 : ∃ j : ℕ, syracuseStep^[j] 22751 = 1 := reachStep (stepEq 1 (by rfl) ⟨17063, by rfl⟩ : syracuseStep 22751 = 34127) R34127
theorem R22913 : ∃ j : ℕ, syracuseStep^[j] 22913 = 1 := reachStep (stepEq 2 (by rfl) ⟨8592, by rfl⟩ : syracuseStep 22913 = 17185) R17185
theorem R22963 : ∃ j : ℕ, syracuseStep^[j] 22963 = 1 := reachStep (stepEq 1 (by rfl) ⟨17222, by rfl⟩ : syracuseStep 22963 = 34445) R34445
theorem R23273 : ∃ j : ℕ, syracuseStep^[j] 23273 = 1 := reachStep (stepEq 2 (by rfl) ⟨8727, by rfl⟩ : syracuseStep 23273 = 17455) R17455
theorem R23485 : ∃ j : ℕ, syracuseStep^[j] 23485 = 1 := reachStep (stepEq 3 (by rfl) ⟨4403, by rfl⟩ : syracuseStep 23485 = 8807) R8807
theorem R23489 : ∃ j : ℕ, syracuseStep^[j] 23489 = 1 := reachStep (stepEq 2 (by rfl) ⟨8808, by rfl⟩ : syracuseStep 23489 = 17617) R17617
theorem R23651 : ∃ j : ℕ, syracuseStep^[j] 23651 = 1 := reachStep (stepEq 1 (by rfl) ⟨17738, by rfl⟩ : syracuseStep 23651 = 35477) R35477
theorem R23971 : ∃ j : ℕ, syracuseStep^[j] 23971 = 1 := reachStep (stepEq 1 (by rfl) ⟨17978, by rfl⟩ : syracuseStep 23971 = 35957) R35957
theorem R24623 : ∃ j : ℕ, syracuseStep^[j] 24623 = 1 := reachStep (stepEq 1 (by rfl) ⟨18467, by rfl⟩ : syracuseStep 24623 = 36935) R36935
theorem R25379 : ∃ j : ℕ, syracuseStep^[j] 25379 = 1 := reachStep (stepEq 1 (by rfl) ⟨19034, by rfl⟩ : syracuseStep 25379 = 38069) R38069
theorem R25433 : ∃ j : ℕ, syracuseStep^[j] 25433 = 1 := reachStep (stepEq 2 (by rfl) ⟨9537, by rfl⟩ : syracuseStep 25433 = 19075) R19075
theorem R26081 : ∃ j : ℕ, syracuseStep^[j] 26081 = 1 := reachStep (stepEq 2 (by rfl) ⟨9780, by rfl⟩ : syracuseStep 26081 = 19561) R19561
theorem R91853 : ∃ j : ℕ, syracuseStep^[j] 91853 = 1 := reachStep (stepEq 3 (by rfl) ⟨17222, by rfl⟩ : syracuseStep 91853 = 34445) R34445
theorem R93419 : ∃ j : ℕ, syracuseStep^[j] 93419 = 1 := reachStep (stepEq 1 (by rfl) ⟨70064, by rfl⟩ : syracuseStep 93419 = 140129) R140129
theorem R263 : ∃ j : ℕ, syracuseStep^[j] 263 = 1 := reachStep (stepEq 1 (by rfl) ⟨197, by rfl⟩ : syracuseStep 263 = 395) R395
theorem R527 : ∃ j : ℕ, syracuseStep^[j] 527 = 1 := reachStep (stepEq 1 (by rfl) ⟨395, by rfl⟩ : syracuseStep 527 = 791) R791
theorem R1053 : ∃ j : ℕ, syracuseStep^[j] 1053 = 1 := reachStep (stepEq 3 (by rfl) ⟨197, by rfl⟩ : syracuseStep 1053 = 395) R395
theorem R1057 : ∃ j : ℕ, syracuseStep^[j] 1057 = 1 := reachStep (stepEq 2 (by rfl) ⟨396, by rfl⟩ : syracuseStep 1057 = 793) R793
theorem R1889 : ∃ j : ℕ, syracuseStep^[j] 1889 = 1 := reachStep (stepEq 2 (by rfl) ⟨708, by rfl⟩ : syracuseStep 1889 = 1417) R1417
theorem R1913 : ∃ j : ℕ, syracuseStep^[j] 1913 = 1 := reachStep (stepEq 2 (by rfl) ⟨717, by rfl⟩ : syracuseStep 1913 = 1435) R1435
theorem R1947 : ∃ j : ℕ, syracuseStep^[j] 1947 = 1 := reachStep (stepEq 1 (by rfl) ⟨1460, by rfl⟩ : syracuseStep 1947 = 2921) R2921
theorem R1959 : ∃ j : ℕ, syracuseStep^[j] 1959 = 1 := reachStep (stepEq 1 (by rfl) ⟨1469, by rfl⟩ : syracuseStep 1959 = 2939) R2939
theorem R1963 : ∃ j : ℕ, syracuseStep^[j] 1963 = 1 := reachStep (stepEq 1 (by rfl) ⟨1472, by rfl⟩ : syracuseStep 1963 = 2945) R2945
theorem R2109 : ∃ j : ℕ, syracuseStep^[j] 2109 = 1 := reachStep (stepEq 3 (by rfl) ⟨395, by rfl⟩ : syracuseStep 2109 = 791) R791
theorem R2113 : ∃ j : ℕ, syracuseStep^[j] 2113 = 1 := reachStep (stepEq 2 (by rfl) ⟨792, by rfl⟩ : syracuseStep 2113 = 1585) R1585
theorem R2115 : ∃ j : ℕ, syracuseStep^[j] 2115 = 1 := reachStep (stepEq 1 (by rfl) ⟨1586, by rfl⟩ : syracuseStep 2115 = 3173) R3173
theorem R2119 : ∃ j : ℕ, syracuseStep^[j] 2119 = 1 := reachStep (stepEq 1 (by rfl) ⟨1589, by rfl⟩ : syracuseStep 2119 = 3179) R3179
theorem R3779 : ∃ j : ℕ, syracuseStep^[j] 3779 = 1 := reachStep (stepEq 1 (by rfl) ⟨2834, by rfl⟩ : syracuseStep 3779 = 5669) R5669
theorem R3787 : ∃ j : ℕ, syracuseStep^[j] 3787 = 1 := reachStep (stepEq 1 (by rfl) ⟨2840, by rfl⟩ : syracuseStep 3787 = 5681) R5681
theorem R3803 : ∃ j : ℕ, syracuseStep^[j] 3803 = 1 := reachStep (stepEq 1 (by rfl) ⟨2852, by rfl⟩ : syracuseStep 3803 = 5705) R5705
theorem R3817 : ∃ j : ℕ, syracuseStep^[j] 3817 = 1 := reachStep (stepEq 2 (by rfl) ⟨1431, by rfl⟩ : syracuseStep 3817 = 2863) R2863
theorem R3827 : ∃ j : ℕ, syracuseStep^[j] 3827 = 1 := reachStep (stepEq 1 (by rfl) ⟨2870, by rfl⟩ : syracuseStep 3827 = 5741) R5741
theorem R3867 : ∃ j : ℕ, syracuseStep^[j] 3867 = 1 := reachStep (stepEq 1 (by rfl) ⟨2900, by rfl⟩ : syracuseStep 3867 = 5801) R5801
theorem R3895 : ∃ j : ℕ, syracuseStep^[j] 3895 = 1 := reachStep (stepEq 1 (by rfl) ⟨2921, by rfl⟩ : syracuseStep 3895 = 5843) R5843
theorem R3911 : ∃ j : ℕ, syracuseStep^[j] 3911 = 1 := reachStep (stepEq 1 (by rfl) ⟨2933, by rfl⟩ : syracuseStep 3911 = 5867) R5867
theorem R3919 : ∃ j : ℕ, syracuseStep^[j] 3919 = 1 := reachStep (stepEq 1 (by rfl) ⟨2939, by rfl⟩ : syracuseStep 3919 = 5879) R5879
theorem R3927 : ∃ j : ℕ, syracuseStep^[j] 3927 = 1 := reachStep (stepEq 1 (by rfl) ⟨2945, by rfl⟩ : syracuseStep 3927 = 5891) R5891
theorem R3931 : ∃ j : ℕ, syracuseStep^[j] 3931 = 1 := reachStep (stepEq 1 (by rfl) ⟨2948, by rfl⟩ : syracuseStep 3931 = 5897) R5897
theorem R3995 : ∃ j : ℕ, syracuseStep^[j] 3995 = 1 := reachStep (stepEq 1 (by rfl) ⟨2996, by rfl⟩ : syracuseStep 3995 = 5993) R5993
theorem R4213 : ∃ j : ℕ, syracuseStep^[j] 4213 = 1 := reachStep (stepEq 5 (by rfl) ⟨197, by rfl⟩ : syracuseStep 4213 = 395) R395
theorem R4227 : ∃ j : ℕ, syracuseStep^[j] 4227 = 1 := reachStep (stepEq 1 (by rfl) ⟨3170, by rfl⟩ : syracuseStep 4227 = 6341) R6341
theorem R4229 : ∃ j : ℕ, syracuseStep^[j] 4229 = 1 := reachStep (stepEq 4 (by rfl) ⟨396, by rfl⟩ : syracuseStep 4229 = 793) R793
theorem R4239 : ∃ j : ℕ, syracuseStep^[j] 4239 = 1 := reachStep (stepEq 1 (by rfl) ⟨3179, by rfl⟩ : syracuseStep 4239 = 6359) R6359
theorem R4251 : ∃ j : ℕ, syracuseStep^[j] 4251 = 1 := reachStep (stepEq 1 (by rfl) ⟨3188, by rfl⟩ : syracuseStep 4251 = 6377) R6377
theorem R4699 : ∃ j : ℕ, syracuseStep^[j] 4699 = 1 := reachStep (stepEq 1 (by rfl) ⟨3524, by rfl⟩ : syracuseStep 4699 = 7049) R7049
theorem R7561 : ∃ j : ℕ, syracuseStep^[j] 7561 = 1 := reachStep (stepEq 2 (by rfl) ⟨2835, by rfl⟩ : syracuseStep 7561 = 5671) R5671
theorem R7577 : ∃ j : ℕ, syracuseStep^[j] 7577 = 1 := reachStep (stepEq 2 (by rfl) ⟨2841, by rfl⟩ : syracuseStep 7577 = 5683) R5683
theorem R7583 : ∃ j : ℕ, syracuseStep^[j] 7583 = 1 := reachStep (stepEq 1 (by rfl) ⟨5687, by rfl⟩ : syracuseStep 7583 = 11375) R11375
theorem R7607 : ∃ j : ℕ, syracuseStep^[j] 7607 = 1 := reachStep (stepEq 1 (by rfl) ⟨5705, by rfl⟩ : syracuseStep 7607 = 11411) R11411
theorem R7625 : ∃ j : ℕ, syracuseStep^[j] 7625 = 1 := reachStep (stepEq 2 (by rfl) ⟨2859, by rfl⟩ : syracuseStep 7625 = 5719) R5719
theorem R7627 : ∃ j : ℕ, syracuseStep^[j] 7627 = 1 := reachStep (stepEq 1 (by rfl) ⟨5720, by rfl⟩ : syracuseStep 7627 = 11441) R11441
theorem R7655 : ∃ j : ℕ, syracuseStep^[j] 7655 = 1 := reachStep (stepEq 1 (by rfl) ⟨5741, by rfl⟩ : syracuseStep 7655 = 11483) R11483
theorem R7735 : ∃ j : ℕ, syracuseStep^[j] 7735 = 1 := reachStep (stepEq 1 (by rfl) ⟨5801, by rfl⟩ : syracuseStep 7735 = 11603) R11603
theorem R7789 : ∃ j : ℕ, syracuseStep^[j] 7789 = 1 := reachStep (stepEq 3 (by rfl) ⟨1460, by rfl⟩ : syracuseStep 7789 = 2921) R2921
theorem R7823 : ∃ j : ℕ, syracuseStep^[j] 7823 = 1 := reachStep (stepEq 1 (by rfl) ⟨5867, by rfl⟩ : syracuseStep 7823 = 11735) R11735
theorem R7853 : ∃ j : ℕ, syracuseStep^[j] 7853 = 1 := reachStep (stepEq 3 (by rfl) ⟨1472, by rfl⟩ : syracuseStep 7853 = 2945) R2945
theorem R7871 : ∃ j : ℕ, syracuseStep^[j] 7871 = 1 := reachStep (stepEq 1 (by rfl) ⟨5903, by rfl⟩ : syracuseStep 7871 = 11807) R11807
theorem R7883 : ∃ j : ℕ, syracuseStep^[j] 7883 = 1 := reachStep (stepEq 1 (by rfl) ⟨5912, by rfl⟩ : syracuseStep 7883 = 11825) R11825
theorem R7991 : ∃ j : ℕ, syracuseStep^[j] 7991 = 1 := reachStep (stepEq 1 (by rfl) ⟨5993, by rfl⟩ : syracuseStep 7991 = 11987) R11987
theorem R8437 : ∃ j : ℕ, syracuseStep^[j] 8437 = 1 := reachStep (stepEq 5 (by rfl) ⟨395, by rfl⟩ : syracuseStep 8437 = 791) R791
theorem R8453 : ∃ j : ℕ, syracuseStep^[j] 8453 = 1 := reachStep (stepEq 4 (by rfl) ⟨792, by rfl⟩ : syracuseStep 8453 = 1585) R1585
theorem R8459 : ∃ j : ℕ, syracuseStep^[j] 8459 = 1 := reachStep (stepEq 1 (by rfl) ⟨6344, by rfl⟩ : syracuseStep 8459 = 12689) R12689
theorem R8465 : ∃ j : ℕ, syracuseStep^[j] 8465 = 1 := reachStep (stepEq 2 (by rfl) ⟨3174, by rfl⟩ : syracuseStep 8465 = 6349) R6349
theorem R8477 : ∃ j : ℕ, syracuseStep^[j] 8477 = 1 := reachStep (stepEq 3 (by rfl) ⟨1589, by rfl⟩ : syracuseStep 8477 = 3179) R3179
theorem R8495 : ∃ j : ℕ, syracuseStep^[j] 8495 = 1 := reachStep (stepEq 1 (by rfl) ⟨6371, by rfl⟩ : syracuseStep 8495 = 12743) R12743
theorem R8503 : ∃ j : ℕ, syracuseStep^[j] 8503 = 1 := reachStep (stepEq 1 (by rfl) ⟨6377, by rfl⟩ : syracuseStep 8503 = 12755) R12755
theorem R15167 : ∃ j : ℕ, syracuseStep^[j] 15167 = 1 := reachStep (stepEq 1 (by rfl) ⟨11375, by rfl⟩ : syracuseStep 15167 = 22751) R22751
theorem R15275 : ∃ j : ℕ, syracuseStep^[j] 15275 = 1 := reachStep (stepEq 1 (by rfl) ⟨11456, by rfl⟩ : syracuseStep 15275 = 22913) R22913
theorem R15329 : ∃ j : ℕ, syracuseStep^[j] 15329 = 1 := reachStep (stepEq 2 (by rfl) ⟨5748, by rfl⟩ : syracuseStep 15329 = 11497) R11497
theorem R15515 : ∃ j : ℕ, syracuseStep^[j] 15515 = 1 := reachStep (stepEq 1 (by rfl) ⟨11636, by rfl⟩ : syracuseStep 15515 = 23273) R23273
theorem R15659 : ∃ j : ℕ, syracuseStep^[j] 15659 = 1 := reachStep (stepEq 1 (by rfl) ⟨11744, by rfl⟩ : syracuseStep 15659 = 23489) R23489
theorem R15713 : ∃ j : ℕ, syracuseStep^[j] 15713 = 1 := reachStep (stepEq 2 (by rfl) ⟨5892, by rfl⟩ : syracuseStep 15713 = 11785) R11785
theorem R15767 : ∃ j : ℕ, syracuseStep^[j] 15767 = 1 := reachStep (stepEq 1 (by rfl) ⟨11825, by rfl⟩ : syracuseStep 15767 = 23651) R23651
theorem R16415 : ∃ j : ℕ, syracuseStep^[j] 16415 = 1 := reachStep (stepEq 1 (by rfl) ⟨12311, by rfl⟩ : syracuseStep 16415 = 24623) R24623
theorem R16919 : ∃ j : ℕ, syracuseStep^[j] 16919 = 1 := reachStep (stepEq 1 (by rfl) ⟨12689, by rfl⟩ : syracuseStep 16919 = 25379) R25379
theorem R16955 : ∃ j : ℕ, syracuseStep^[j] 16955 = 1 := reachStep (stepEq 1 (by rfl) ⟨12716, by rfl⟩ : syracuseStep 16955 = 25433) R25433
theorem R16969 : ∃ j : ℕ, syracuseStep^[j] 16969 = 1 := reachStep (stepEq 2 (by rfl) ⟨6363, by rfl⟩ : syracuseStep 16969 = 12727) R12727
theorem R17387 : ∃ j : ℕ, syracuseStep^[j] 17387 = 1 := reachStep (stepEq 1 (by rfl) ⟨13040, by rfl⟩ : syracuseStep 17387 = 26081) R26081
theorem R61235 : ∃ j : ℕ, syracuseStep^[j] 61235 = 1 := reachStep (stepEq 1 (by rfl) ⟨45926, by rfl⟩ : syracuseStep 61235 = 91853) R91853
theorem R62279 : ∃ j : ℕ, syracuseStep^[j] 62279 = 1 := reachStep (stepEq 1 (by rfl) ⟨46709, by rfl⟩ : syracuseStep 62279 = 93419) R93419
theorem R30253 : ∃ j : ℕ, syracuseStep^[j] 30253 = 1 := reachStep (stepEq 3 (by rfl) ⟨5672, by rfl⟩ : syracuseStep 30253 = 11345) R11345
theorem R30617 : ∃ j : ℕ, syracuseStep^[j] 30617 = 1 := reachStep (stepEq 2 (by rfl) ⟨11481, by rfl⟩ : syracuseStep 30617 = 22963) R22963
theorem R30941 : ∃ j : ℕ, syracuseStep^[j] 30941 = 1 := reachStep (stepEq 3 (by rfl) ⟨5801, by rfl⟩ : syracuseStep 30941 = 11603) R11603
theorem R31313 : ∃ j : ℕ, syracuseStep^[j] 31313 = 1 := reachStep (stepEq 2 (by rfl) ⟨11742, by rfl⟩ : syracuseStep 31313 = 23485) R23485
theorem R31427 : ∃ j : ℕ, syracuseStep^[j] 31427 = 1 := reachStep (stepEq 1 (by rfl) ⟨23570, by rfl⟩ : syracuseStep 31427 = 47141) R47141
theorem R31961 : ∃ j : ℕ, syracuseStep^[j] 31961 = 1 := reachStep (stepEq 2 (by rfl) ⟨11985, by rfl⟩ : syracuseStep 31961 = 23971) R23971
theorem R175 : ∃ j : ℕ, syracuseStep^[j] 175 = 1 := reachStep (stepEq 1 (by rfl) ⟨131, by rfl⟩ : syracuseStep 175 = 263) R263
theorem R351 : ∃ j : ℕ, syracuseStep^[j] 351 = 1 := reachStep (stepEq 1 (by rfl) ⟨263, by rfl⟩ : syracuseStep 351 = 527) R527
theorem R701 : ∃ j : ℕ, syracuseStep^[j] 701 = 1 := reachStep (stepEq 3 (by rfl) ⟨131, by rfl⟩ : syracuseStep 701 = 263) R263
theorem R1259 : ∃ j : ℕ, syracuseStep^[j] 1259 = 1 := reachStep (stepEq 1 (by rfl) ⟨944, by rfl⟩ : syracuseStep 1259 = 1889) R1889
theorem R1275 : ∃ j : ℕ, syracuseStep^[j] 1275 = 1 := reachStep (stepEq 1 (by rfl) ⟨956, by rfl⟩ : syracuseStep 1275 = 1913) R1913
theorem R1405 : ∃ j : ℕ, syracuseStep^[j] 1405 = 1 := reachStep (stepEq 3 (by rfl) ⟨263, by rfl⟩ : syracuseStep 1405 = 527) R527
theorem R1409 : ∃ j : ℕ, syracuseStep^[j] 1409 = 1 := reachStep (stepEq 2 (by rfl) ⟨528, by rfl⟩ : syracuseStep 1409 = 1057) R1057
theorem R2519 : ∃ j : ℕ, syracuseStep^[j] 2519 = 1 := reachStep (stepEq 1 (by rfl) ⟨1889, by rfl⟩ : syracuseStep 2519 = 3779) R3779
theorem R2535 : ∃ j : ℕ, syracuseStep^[j] 2535 = 1 := reachStep (stepEq 1 (by rfl) ⟨1901, by rfl⟩ : syracuseStep 2535 = 3803) R3803
theorem R2551 : ∃ j : ℕ, syracuseStep^[j] 2551 = 1 := reachStep (stepEq 1 (by rfl) ⟨1913, by rfl⟩ : syracuseStep 2551 = 3827) R3827
theorem R2607 : ∃ j : ℕ, syracuseStep^[j] 2607 = 1 := reachStep (stepEq 1 (by rfl) ⟨1955, by rfl⟩ : syracuseStep 2607 = 3911) R3911
theorem R2617 : ∃ j : ℕ, syracuseStep^[j] 2617 = 1 := reachStep (stepEq 2 (by rfl) ⟨981, by rfl⟩ : syracuseStep 2617 = 1963) R1963
theorem R2663 : ∃ j : ℕ, syracuseStep^[j] 2663 = 1 := reachStep (stepEq 1 (by rfl) ⟨1997, by rfl⟩ : syracuseStep 2663 = 3995) R3995
theorem R2805 : ∃ j : ℕ, syracuseStep^[j] 2805 = 1 := reachStep (stepEq 5 (by rfl) ⟨131, by rfl⟩ : syracuseStep 2805 = 263) R263
theorem R2817 : ∃ j : ℕ, syracuseStep^[j] 2817 = 1 := reachStep (stepEq 2 (by rfl) ⟨1056, by rfl⟩ : syracuseStep 2817 = 2113) R2113
theorem R2819 : ∃ j : ℕ, syracuseStep^[j] 2819 = 1 := reachStep (stepEq 1 (by rfl) ⟨2114, by rfl⟩ : syracuseStep 2819 = 4229) R4229
theorem R2825 : ∃ j : ℕ, syracuseStep^[j] 2825 = 1 := reachStep (stepEq 2 (by rfl) ⟨1059, by rfl⟩ : syracuseStep 2825 = 2119) R2119
theorem R5037 : ∃ j : ℕ, syracuseStep^[j] 5037 = 1 := reachStep (stepEq 3 (by rfl) ⟨944, by rfl⟩ : syracuseStep 5037 = 1889) R1889
theorem R5049 : ∃ j : ℕ, syracuseStep^[j] 5049 = 1 := reachStep (stepEq 2 (by rfl) ⟨1893, by rfl⟩ : syracuseStep 5049 = 3787) R3787
theorem R5051 : ∃ j : ℕ, syracuseStep^[j] 5051 = 1 := reachStep (stepEq 1 (by rfl) ⟨3788, by rfl⟩ : syracuseStep 5051 = 7577) R7577
theorem R5055 : ∃ j : ℕ, syracuseStep^[j] 5055 = 1 := reachStep (stepEq 1 (by rfl) ⟨3791, by rfl⟩ : syracuseStep 5055 = 7583) R7583
theorem R5071 : ∃ j : ℕ, syracuseStep^[j] 5071 = 1 := reachStep (stepEq 1 (by rfl) ⟨3803, by rfl⟩ : syracuseStep 5071 = 7607) R7607
theorem R5083 : ∃ j : ℕ, syracuseStep^[j] 5083 = 1 := reachStep (stepEq 1 (by rfl) ⟨3812, by rfl⟩ : syracuseStep 5083 = 7625) R7625
theorem R5089 : ∃ j : ℕ, syracuseStep^[j] 5089 = 1 := reachStep (stepEq 2 (by rfl) ⟨1908, by rfl⟩ : syracuseStep 5089 = 3817) R3817
theorem R5101 : ∃ j : ℕ, syracuseStep^[j] 5101 = 1 := reachStep (stepEq 3 (by rfl) ⟨956, by rfl⟩ : syracuseStep 5101 = 1913) R1913
theorem R5103 : ∃ j : ℕ, syracuseStep^[j] 5103 = 1 := reachStep (stepEq 1 (by rfl) ⟨3827, by rfl⟩ : syracuseStep 5103 = 7655) R7655
theorem R5193 : ∃ j : ℕ, syracuseStep^[j] 5193 = 1 := reachStep (stepEq 2 (by rfl) ⟨1947, by rfl⟩ : syracuseStep 5193 = 3895) R3895
theorem R5215 : ∃ j : ℕ, syracuseStep^[j] 5215 = 1 := reachStep (stepEq 1 (by rfl) ⟨3911, by rfl⟩ : syracuseStep 5215 = 7823) R7823
theorem R5225 : ∃ j : ℕ, syracuseStep^[j] 5225 = 1 := reachStep (stepEq 2 (by rfl) ⟨1959, by rfl⟩ : syracuseStep 5225 = 3919) R3919
theorem R5235 : ∃ j : ℕ, syracuseStep^[j] 5235 = 1 := reachStep (stepEq 1 (by rfl) ⟨3926, by rfl⟩ : syracuseStep 5235 = 7853) R7853
theorem R5241 : ∃ j : ℕ, syracuseStep^[j] 5241 = 1 := reachStep (stepEq 2 (by rfl) ⟨1965, by rfl⟩ : syracuseStep 5241 = 3931) R3931
theorem R5247 : ∃ j : ℕ, syracuseStep^[j] 5247 = 1 := reachStep (stepEq 1 (by rfl) ⟨3935, by rfl⟩ : syracuseStep 5247 = 7871) R7871
theorem R5255 : ∃ j : ℕ, syracuseStep^[j] 5255 = 1 := reachStep (stepEq 1 (by rfl) ⟨3941, by rfl⟩ : syracuseStep 5255 = 7883) R7883
theorem R5327 : ∃ j : ℕ, syracuseStep^[j] 5327 = 1 := reachStep (stepEq 1 (by rfl) ⟨3995, by rfl⟩ : syracuseStep 5327 = 7991) R7991
theorem R5617 : ∃ j : ℕ, syracuseStep^[j] 5617 = 1 := reachStep (stepEq 2 (by rfl) ⟨2106, by rfl⟩ : syracuseStep 5617 = 4213) R4213
theorem R5621 : ∃ j : ℕ, syracuseStep^[j] 5621 = 1 := reachStep (stepEq 5 (by rfl) ⟨263, by rfl⟩ : syracuseStep 5621 = 527) R527
theorem R5635 : ∃ j : ℕ, syracuseStep^[j] 5635 = 1 := reachStep (stepEq 1 (by rfl) ⟨4226, by rfl⟩ : syracuseStep 5635 = 8453) R8453
theorem R5637 : ∃ j : ℕ, syracuseStep^[j] 5637 = 1 := reachStep (stepEq 4 (by rfl) ⟨528, by rfl⟩ : syracuseStep 5637 = 1057) R1057
theorem R5639 : ∃ j : ℕ, syracuseStep^[j] 5639 = 1 := reachStep (stepEq 1 (by rfl) ⟨4229, by rfl⟩ : syracuseStep 5639 = 8459) R8459
theorem R5643 : ∃ j : ℕ, syracuseStep^[j] 5643 = 1 := reachStep (stepEq 1 (by rfl) ⟨4232, by rfl⟩ : syracuseStep 5643 = 8465) R8465
theorem R5651 : ∃ j : ℕ, syracuseStep^[j] 5651 = 1 := reachStep (stepEq 1 (by rfl) ⟨4238, by rfl⟩ : syracuseStep 5651 = 8477) R8477
theorem R5663 : ∃ j : ℕ, syracuseStep^[j] 5663 = 1 := reachStep (stepEq 1 (by rfl) ⟨4247, by rfl⟩ : syracuseStep 5663 = 8495) R8495
theorem R6265 : ∃ j : ℕ, syracuseStep^[j] 6265 = 1 := reachStep (stepEq 2 (by rfl) ⟨2349, by rfl⟩ : syracuseStep 6265 = 4699) R4699
theorem R40337 : ∃ j : ℕ, syracuseStep^[j] 40337 = 1 := reachStep (stepEq 2 (by rfl) ⟨15126, by rfl⟩ : syracuseStep 40337 = 30253) R30253
theorem R40445 : ∃ j : ℕ, syracuseStep^[j] 40445 = 1 := reachStep (stepEq 3 (by rfl) ⟨7583, by rfl⟩ : syracuseStep 40445 = 15167) R15167
theorem R40733 : ∃ j : ℕ, syracuseStep^[j] 40733 = 1 := reachStep (stepEq 3 (by rfl) ⟨7637, by rfl⟩ : syracuseStep 40733 = 15275) R15275
theorem R40823 : ∃ j : ℕ, syracuseStep^[j] 40823 = 1 := reachStep (stepEq 1 (by rfl) ⟨30617, by rfl⟩ : syracuseStep 40823 = 61235) R61235
theorem R41519 : ∃ j : ℕ, syracuseStep^[j] 41519 = 1 := reachStep (stepEq 1 (by rfl) ⟨31139, by rfl⟩ : syracuseStep 41519 = 62279) R62279
theorem R10081 : ∃ j : ℕ, syracuseStep^[j] 10081 = 1 := reachStep (stepEq 2 (by rfl) ⟨3780, by rfl⟩ : syracuseStep 10081 = 7561) R7561
theorem R10111 : ∃ j : ℕ, syracuseStep^[j] 10111 = 1 := reachStep (stepEq 1 (by rfl) ⟨7583, by rfl⟩ : syracuseStep 10111 = 15167) R15167
theorem R10169 : ∃ j : ℕ, syracuseStep^[j] 10169 = 1 := reachStep (stepEq 2 (by rfl) ⟨3813, by rfl⟩ : syracuseStep 10169 = 7627) R7627
theorem R10205 : ∃ j : ℕ, syracuseStep^[j] 10205 = 1 := reachStep (stepEq 3 (by rfl) ⟨1913, by rfl⟩ : syracuseStep 10205 = 3827) R3827
theorem R10219 : ∃ j : ℕ, syracuseStep^[j] 10219 = 1 := reachStep (stepEq 1 (by rfl) ⟨7664, by rfl⟩ : syracuseStep 10219 = 15329) R15329
theorem R10313 : ∃ j : ℕ, syracuseStep^[j] 10313 = 1 := reachStep (stepEq 2 (by rfl) ⟨3867, by rfl⟩ : syracuseStep 10313 = 7735) R7735
theorem R10343 : ∃ j : ℕ, syracuseStep^[j] 10343 = 1 := reachStep (stepEq 1 (by rfl) ⟨7757, by rfl⟩ : syracuseStep 10343 = 15515) R15515
theorem R10385 : ∃ j : ℕ, syracuseStep^[j] 10385 = 1 := reachStep (stepEq 2 (by rfl) ⟨3894, by rfl⟩ : syracuseStep 10385 = 7789) R7789
theorem R10439 : ∃ j : ℕ, syracuseStep^[j] 10439 = 1 := reachStep (stepEq 1 (by rfl) ⟨7829, by rfl⟩ : syracuseStep 10439 = 15659) R15659
theorem R10469 : ∃ j : ℕ, syracuseStep^[j] 10469 = 1 := reachStep (stepEq 4 (by rfl) ⟨981, by rfl⟩ : syracuseStep 10469 = 1963) R1963
theorem R10475 : ∃ j : ℕ, syracuseStep^[j] 10475 = 1 := reachStep (stepEq 1 (by rfl) ⟨7856, by rfl⟩ : syracuseStep 10475 = 15713) R15713
theorem R10511 : ∃ j : ℕ, syracuseStep^[j] 10511 = 1 := reachStep (stepEq 1 (by rfl) ⟨7883, by rfl⟩ : syracuseStep 10511 = 15767) R15767
theorem R10943 : ∃ j : ℕ, syracuseStep^[j] 10943 = 1 := reachStep (stepEq 1 (by rfl) ⟨8207, by rfl⟩ : syracuseStep 10943 = 16415) R16415
theorem R11249 : ∃ j : ℕ, syracuseStep^[j] 11249 = 1 := reachStep (stepEq 2 (by rfl) ⟨4218, by rfl⟩ : syracuseStep 11249 = 8437) R8437
theorem R11269 : ∃ j : ℕ, syracuseStep^[j] 11269 = 1 := reachStep (stepEq 4 (by rfl) ⟨1056, by rfl⟩ : syracuseStep 11269 = 2113) R2113
theorem R11279 : ∃ j : ℕ, syracuseStep^[j] 11279 = 1 := reachStep (stepEq 1 (by rfl) ⟨8459, by rfl⟩ : syracuseStep 11279 = 16919) R16919
theorem R11303 : ∃ j : ℕ, syracuseStep^[j] 11303 = 1 := reachStep (stepEq 1 (by rfl) ⟨8477, by rfl⟩ : syracuseStep 11303 = 16955) R16955
theorem R11591 : ∃ j : ℕ, syracuseStep^[j] 11591 = 1 := reachStep (stepEq 1 (by rfl) ⟨8693, by rfl⟩ : syracuseStep 11591 = 17387) R17387
theorem R181397 : ∃ j : ℕ, syracuseStep^[j] 181397 = 1 := reachStep (stepEq 6 (by rfl) ⟨4251, by rfl⟩ : syracuseStep 181397 = 8503) R8503
theorem R83501 : ∃ j : ℕ, syracuseStep^[j] 83501 = 1 := reachStep (stepEq 3 (by rfl) ⟨15656, by rfl⟩ : syracuseStep 83501 = 31313) R31313
theorem R20357 : ∃ j : ℕ, syracuseStep^[j] 20357 = 1 := reachStep (stepEq 4 (by rfl) ⟨1908, by rfl⟩ : syracuseStep 20357 = 3817) R3817
theorem R20411 : ∃ j : ℕ, syracuseStep^[j] 20411 = 1 := reachStep (stepEq 1 (by rfl) ⟨15308, by rfl⟩ : syracuseStep 20411 = 30617) R30617
theorem R20627 : ∃ j : ℕ, syracuseStep^[j] 20627 = 1 := reachStep (stepEq 1 (by rfl) ⟨15470, by rfl⟩ : syracuseStep 20627 = 30941) R30941
theorem R20951 : ∃ j : ℕ, syracuseStep^[j] 20951 = 1 := reachStep (stepEq 1 (by rfl) ⟨15713, by rfl⟩ : syracuseStep 20951 = 31427) R31427
theorem R21307 : ∃ j : ℕ, syracuseStep^[j] 21307 = 1 := reachStep (stepEq 1 (by rfl) ⟨15980, by rfl⟩ : syracuseStep 21307 = 31961) R31961
theorem R22625 : ∃ j : ℕ, syracuseStep^[j] 22625 = 1 := reachStep (stepEq 2 (by rfl) ⟨8484, by rfl⟩ : syracuseStep 22625 = 16969) R16969
theorem R233 : ∃ j : ℕ, syracuseStep^[j] 233 = 1 := reachStep (stepEq 2 (by rfl) ⟨87, by rfl⟩ : syracuseStep 233 = 175) R175
theorem R467 : ∃ j : ℕ, syracuseStep^[j] 467 = 1 := reachStep (stepEq 1 (by rfl) ⟨350, by rfl⟩ : syracuseStep 467 = 701) R701
theorem R839 : ∃ j : ℕ, syracuseStep^[j] 839 = 1 := reachStep (stepEq 1 (by rfl) ⟨629, by rfl⟩ : syracuseStep 839 = 1259) R1259
theorem R933 : ∃ j : ℕ, syracuseStep^[j] 933 = 1 := reachStep (stepEq 4 (by rfl) ⟨87, by rfl⟩ : syracuseStep 933 = 175) R175
theorem R939 : ∃ j : ℕ, syracuseStep^[j] 939 = 1 := reachStep (stepEq 1 (by rfl) ⟨704, by rfl⟩ : syracuseStep 939 = 1409) R1409
theorem R1679 : ∃ j : ℕ, syracuseStep^[j] 1679 = 1 := reachStep (stepEq 1 (by rfl) ⟨1259, by rfl⟩ : syracuseStep 1679 = 2519) R2519
theorem R1775 : ∃ j : ℕ, syracuseStep^[j] 1775 = 1 := reachStep (stepEq 1 (by rfl) ⟨1331, by rfl⟩ : syracuseStep 1775 = 2663) R2663
theorem R1869 : ∃ j : ℕ, syracuseStep^[j] 1869 = 1 := reachStep (stepEq 3 (by rfl) ⟨350, by rfl⟩ : syracuseStep 1869 = 701) R701
theorem R1873 : ∃ j : ℕ, syracuseStep^[j] 1873 = 1 := reachStep (stepEq 2 (by rfl) ⟨702, by rfl⟩ : syracuseStep 1873 = 1405) R1405
theorem R1879 : ∃ j : ℕ, syracuseStep^[j] 1879 = 1 := reachStep (stepEq 1 (by rfl) ⟨1409, by rfl⟩ : syracuseStep 1879 = 2819) R2819
theorem R1883 : ∃ j : ℕ, syracuseStep^[j] 1883 = 1 := reachStep (stepEq 1 (by rfl) ⟨1412, by rfl⟩ : syracuseStep 1883 = 2825) R2825
theorem R3357 : ∃ j : ℕ, syracuseStep^[j] 3357 = 1 := reachStep (stepEq 3 (by rfl) ⟨629, by rfl⟩ : syracuseStep 3357 = 1259) R1259
theorem R3367 : ∃ j : ℕ, syracuseStep^[j] 3367 = 1 := reachStep (stepEq 1 (by rfl) ⟨2525, by rfl⟩ : syracuseStep 3367 = 5051) R5051
theorem R3401 : ∃ j : ℕ, syracuseStep^[j] 3401 = 1 := reachStep (stepEq 2 (by rfl) ⟨1275, by rfl⟩ : syracuseStep 3401 = 2551) R2551
theorem R3483 : ∃ j : ℕ, syracuseStep^[j] 3483 = 1 := reachStep (stepEq 1 (by rfl) ⟨2612, by rfl⟩ : syracuseStep 3483 = 5225) R5225
theorem R3489 : ∃ j : ℕ, syracuseStep^[j] 3489 = 1 := reachStep (stepEq 2 (by rfl) ⟨1308, by rfl⟩ : syracuseStep 3489 = 2617) R2617
theorem R3503 : ∃ j : ℕ, syracuseStep^[j] 3503 = 1 := reachStep (stepEq 1 (by rfl) ⟨2627, by rfl⟩ : syracuseStep 3503 = 5255) R5255
theorem R3551 : ∃ j : ℕ, syracuseStep^[j] 3551 = 1 := reachStep (stepEq 1 (by rfl) ⟨2663, by rfl⟩ : syracuseStep 3551 = 5327) R5327
theorem R3733 : ∃ j : ℕ, syracuseStep^[j] 3733 = 1 := reachStep (stepEq 6 (by rfl) ⟨87, by rfl⟩ : syracuseStep 3733 = 175) R175
theorem R3747 : ∃ j : ℕ, syracuseStep^[j] 3747 = 1 := reachStep (stepEq 1 (by rfl) ⟨2810, by rfl⟩ : syracuseStep 3747 = 5621) R5621
theorem R3757 : ∃ j : ℕ, syracuseStep^[j] 3757 = 1 := reachStep (stepEq 3 (by rfl) ⟨704, by rfl⟩ : syracuseStep 3757 = 1409) R1409
theorem R3759 : ∃ j : ℕ, syracuseStep^[j] 3759 = 1 := reachStep (stepEq 1 (by rfl) ⟨2819, by rfl⟩ : syracuseStep 3759 = 5639) R5639
theorem R3767 : ∃ j : ℕ, syracuseStep^[j] 3767 = 1 := reachStep (stepEq 1 (by rfl) ⟨2825, by rfl⟩ : syracuseStep 3767 = 5651) R5651
theorem R3775 : ∃ j : ℕ, syracuseStep^[j] 3775 = 1 := reachStep (stepEq 1 (by rfl) ⟨2831, by rfl⟩ : syracuseStep 3775 = 5663) R5663
theorem R6717 : ∃ j : ℕ, syracuseStep^[j] 6717 = 1 := reachStep (stepEq 3 (by rfl) ⟨1259, by rfl⟩ : syracuseStep 6717 = 2519) R2519
theorem R6761 : ∃ j : ℕ, syracuseStep^[j] 6761 = 1 := reachStep (stepEq 2 (by rfl) ⟨2535, by rfl⟩ : syracuseStep 6761 = 5071) R5071
theorem R6779 : ∃ j : ℕ, syracuseStep^[j] 6779 = 1 := reachStep (stepEq 1 (by rfl) ⟨5084, by rfl⟩ : syracuseStep 6779 = 10169) R10169
theorem R6785 : ∃ j : ℕ, syracuseStep^[j] 6785 = 1 := reachStep (stepEq 2 (by rfl) ⟨2544, by rfl⟩ : syracuseStep 6785 = 5089) R5089
theorem R6803 : ∃ j : ℕ, syracuseStep^[j] 6803 = 1 := reachStep (stepEq 1 (by rfl) ⟨5102, by rfl⟩ : syracuseStep 6803 = 10205) R10205
theorem R6875 : ∃ j : ℕ, syracuseStep^[j] 6875 = 1 := reachStep (stepEq 1 (by rfl) ⟨5156, by rfl⟩ : syracuseStep 6875 = 10313) R10313
theorem R6895 : ∃ j : ℕ, syracuseStep^[j] 6895 = 1 := reachStep (stepEq 1 (by rfl) ⟨5171, by rfl⟩ : syracuseStep 6895 = 10343) R10343
theorem R6923 : ∃ j : ℕ, syracuseStep^[j] 6923 = 1 := reachStep (stepEq 1 (by rfl) ⟨5192, by rfl⟩ : syracuseStep 6923 = 10385) R10385
theorem R6953 : ∃ j : ℕ, syracuseStep^[j] 6953 = 1 := reachStep (stepEq 2 (by rfl) ⟨2607, by rfl⟩ : syracuseStep 6953 = 5215) R5215
theorem R6959 : ∃ j : ℕ, syracuseStep^[j] 6959 = 1 := reachStep (stepEq 1 (by rfl) ⟨5219, by rfl⟩ : syracuseStep 6959 = 10439) R10439
theorem R6979 : ∃ j : ℕ, syracuseStep^[j] 6979 = 1 := reachStep (stepEq 1 (by rfl) ⟨5234, by rfl⟩ : syracuseStep 6979 = 10469) R10469
theorem R6983 : ∃ j : ℕ, syracuseStep^[j] 6983 = 1 := reachStep (stepEq 1 (by rfl) ⟨5237, by rfl⟩ : syracuseStep 6983 = 10475) R10475
theorem R7007 : ∃ j : ℕ, syracuseStep^[j] 7007 = 1 := reachStep (stepEq 1 (by rfl) ⟨5255, by rfl⟩ : syracuseStep 7007 = 10511) R10511
theorem R7295 : ∃ j : ℕ, syracuseStep^[j] 7295 = 1 := reachStep (stepEq 1 (by rfl) ⟨5471, by rfl⟩ : syracuseStep 7295 = 10943) R10943
theorem R7493 : ∃ j : ℕ, syracuseStep^[j] 7493 = 1 := reachStep (stepEq 4 (by rfl) ⟨702, by rfl⟩ : syracuseStep 7493 = 1405) R1405
theorem R7499 : ∃ j : ℕ, syracuseStep^[j] 7499 = 1 := reachStep (stepEq 1 (by rfl) ⟨5624, by rfl⟩ : syracuseStep 7499 = 11249) R11249
theorem R7517 : ∃ j : ℕ, syracuseStep^[j] 7517 = 1 := reachStep (stepEq 3 (by rfl) ⟨1409, by rfl⟩ : syracuseStep 7517 = 2819) R2819
theorem R7519 : ∃ j : ℕ, syracuseStep^[j] 7519 = 1 := reachStep (stepEq 1 (by rfl) ⟨5639, by rfl⟩ : syracuseStep 7519 = 11279) R11279
theorem R7535 : ∃ j : ℕ, syracuseStep^[j] 7535 = 1 := reachStep (stepEq 1 (by rfl) ⟨5651, by rfl⟩ : syracuseStep 7535 = 11303) R11303
theorem R7727 : ∃ j : ℕ, syracuseStep^[j] 7727 = 1 := reachStep (stepEq 1 (by rfl) ⟨5795, by rfl⟩ : syracuseStep 7727 = 11591) R11591
theorem R8353 : ∃ j : ℕ, syracuseStep^[j] 8353 = 1 := reachStep (stepEq 2 (by rfl) ⟨3132, by rfl⟩ : syracuseStep 8353 = 6265) R6265
theorem R110717 : ∃ j : ℕ, syracuseStep^[j] 110717 = 1 := reachStep (stepEq 3 (by rfl) ⟨20759, by rfl⟩ : syracuseStep 110717 = 41519) R41519
theorem R13429 : ∃ j : ℕ, syracuseStep^[j] 13429 = 1 := reachStep (stepEq 5 (by rfl) ⟨629, by rfl⟩ : syracuseStep 13429 = 1259) R1259
theorem R13441 : ∃ j : ℕ, syracuseStep^[j] 13441 = 1 := reachStep (stepEq 2 (by rfl) ⟨5040, by rfl⟩ : syracuseStep 13441 = 10081) R10081
theorem R13481 : ∃ j : ℕ, syracuseStep^[j] 13481 = 1 := reachStep (stepEq 2 (by rfl) ⟨5055, by rfl⟩ : syracuseStep 13481 = 10111) R10111
theorem R13571 : ∃ j : ℕ, syracuseStep^[j] 13571 = 1 := reachStep (stepEq 1 (by rfl) ⟨10178, by rfl⟩ : syracuseStep 13571 = 20357) R20357
theorem R13607 : ∃ j : ℕ, syracuseStep^[j] 13607 = 1 := reachStep (stepEq 1 (by rfl) ⟨10205, by rfl⟩ : syracuseStep 13607 = 20411) R20411
theorem R13625 : ∃ j : ℕ, syracuseStep^[j] 13625 = 1 := reachStep (stepEq 2 (by rfl) ⟨5109, by rfl⟩ : syracuseStep 13625 = 10219) R10219
theorem R13751 : ∃ j : ℕ, syracuseStep^[j] 13751 = 1 := reachStep (stepEq 1 (by rfl) ⟨10313, by rfl⟩ : syracuseStep 13751 = 20627) R20627
theorem R13967 : ∃ j : ℕ, syracuseStep^[j] 13967 = 1 := reachStep (stepEq 1 (by rfl) ⟨10475, by rfl⟩ : syracuseStep 13967 = 20951) R20951
theorem R15025 : ∃ j : ℕ, syracuseStep^[j] 15025 = 1 := reachStep (stepEq 2 (by rfl) ⟨5634, by rfl⟩ : syracuseStep 15025 = 11269) R11269
theorem R15029 : ∃ j : ℕ, syracuseStep^[j] 15029 = 1 := reachStep (stepEq 5 (by rfl) ⟨704, by rfl⟩ : syracuseStep 15029 = 1409) R1409
theorem R15083 : ∃ j : ℕ, syracuseStep^[j] 15083 = 1 := reachStep (stepEq 1 (by rfl) ⟨11312, by rfl⟩ : syracuseStep 15083 = 22625) R22625
theorem R15101 : ∃ j : ℕ, syracuseStep^[j] 15101 = 1 := reachStep (stepEq 3 (by rfl) ⟨2831, by rfl⟩ : syracuseStep 15101 = 5663) R5663
theorem R55667 : ∃ j : ℕ, syracuseStep^[j] 55667 = 1 := reachStep (stepEq 1 (by rfl) ⟨41750, by rfl⟩ : syracuseStep 55667 = 83501) R83501
theorem R56821 : ∃ j : ℕ, syracuseStep^[j] 56821 = 1 := reachStep (stepEq 5 (by rfl) ⟨2663, by rfl⟩ : syracuseStep 56821 = 5327) R5327
theorem R483725 : ∃ j : ℕ, syracuseStep^[j] 483725 = 1 := reachStep (stepEq 3 (by rfl) ⟨90698, by rfl⟩ : syracuseStep 483725 = 181397) R181397
theorem R26891 : ∃ j : ℕ, syracuseStep^[j] 26891 = 1 := reachStep (stepEq 1 (by rfl) ⟨20168, by rfl⟩ : syracuseStep 26891 = 40337) R40337
theorem R26963 : ∃ j : ℕ, syracuseStep^[j] 26963 = 1 := reachStep (stepEq 1 (by rfl) ⟨20222, by rfl⟩ : syracuseStep 26963 = 40445) R40445
theorem R27155 : ∃ j : ℕ, syracuseStep^[j] 27155 = 1 := reachStep (stepEq 1 (by rfl) ⟨20366, by rfl⟩ : syracuseStep 27155 = 40733) R40733
theorem R27215 : ∃ j : ℕ, syracuseStep^[j] 27215 = 1 := reachStep (stepEq 1 (by rfl) ⟨20411, by rfl⟩ : syracuseStep 27215 = 40823) R40823
theorem R28409 : ∃ j : ℕ, syracuseStep^[j] 28409 = 1 := reachStep (stepEq 2 (by rfl) ⟨10653, by rfl⟩ : syracuseStep 28409 = 21307) R21307
theorem R155 : ∃ j : ℕ, syracuseStep^[j] 155 = 1 := reachStep (stepEq 1 (by rfl) ⟨116, by rfl⟩ : syracuseStep 155 = 233) R233
theorem R311 : ∃ j : ℕ, syracuseStep^[j] 311 = 1 := reachStep (stepEq 1 (by rfl) ⟨233, by rfl⟩ : syracuseStep 311 = 467) R467
theorem R559 : ∃ j : ℕ, syracuseStep^[j] 559 = 1 := reachStep (stepEq 1 (by rfl) ⟨419, by rfl⟩ : syracuseStep 559 = 839) R839
theorem R621 : ∃ j : ℕ, syracuseStep^[j] 621 = 1 := reachStep (stepEq 3 (by rfl) ⟨116, by rfl⟩ : syracuseStep 621 = 233) R233
theorem R1119 : ∃ j : ℕ, syracuseStep^[j] 1119 = 1 := reachStep (stepEq 1 (by rfl) ⟨839, by rfl⟩ : syracuseStep 1119 = 1679) R1679
theorem R1183 : ∃ j : ℕ, syracuseStep^[j] 1183 = 1 := reachStep (stepEq 1 (by rfl) ⟨887, by rfl⟩ : syracuseStep 1183 = 1775) R1775
theorem R1245 : ∃ j : ℕ, syracuseStep^[j] 1245 = 1 := reachStep (stepEq 3 (by rfl) ⟨233, by rfl⟩ : syracuseStep 1245 = 467) R467
theorem R1255 : ∃ j : ℕ, syracuseStep^[j] 1255 = 1 := reachStep (stepEq 1 (by rfl) ⟨941, by rfl⟩ : syracuseStep 1255 = 1883) R1883
theorem R2237 : ∃ j : ℕ, syracuseStep^[j] 2237 = 1 := reachStep (stepEq 3 (by rfl) ⟨419, by rfl⟩ : syracuseStep 2237 = 839) R839
theorem R2267 : ∃ j : ℕ, syracuseStep^[j] 2267 = 1 := reachStep (stepEq 1 (by rfl) ⟨1700, by rfl⟩ : syracuseStep 2267 = 3401) R3401
theorem R2335 : ∃ j : ℕ, syracuseStep^[j] 2335 = 1 := reachStep (stepEq 1 (by rfl) ⟨1751, by rfl⟩ : syracuseStep 2335 = 3503) R3503
theorem R2367 : ∃ j : ℕ, syracuseStep^[j] 2367 = 1 := reachStep (stepEq 1 (by rfl) ⟨1775, by rfl⟩ : syracuseStep 2367 = 3551) R3551
theorem R2485 : ∃ j : ℕ, syracuseStep^[j] 2485 = 1 := reachStep (stepEq 5 (by rfl) ⟨116, by rfl⟩ : syracuseStep 2485 = 233) R233
theorem R2497 : ∃ j : ℕ, syracuseStep^[j] 2497 = 1 := reachStep (stepEq 2 (by rfl) ⟨936, by rfl⟩ : syracuseStep 2497 = 1873) R1873
theorem R2505 : ∃ j : ℕ, syracuseStep^[j] 2505 = 1 := reachStep (stepEq 2 (by rfl) ⟨939, by rfl⟩ : syracuseStep 2505 = 1879) R1879
theorem R2511 : ∃ j : ℕ, syracuseStep^[j] 2511 = 1 := reachStep (stepEq 1 (by rfl) ⟨1883, by rfl⟩ : syracuseStep 2511 = 3767) R3767
theorem R37111 : ∃ j : ℕ, syracuseStep^[j] 37111 = 1 := reachStep (stepEq 1 (by rfl) ⟨27833, by rfl⟩ : syracuseStep 37111 = 55667) R55667
theorem R4477 : ∃ j : ℕ, syracuseStep^[j] 4477 = 1 := reachStep (stepEq 3 (by rfl) ⟨839, by rfl⟩ : syracuseStep 4477 = 1679) R1679
theorem R4489 : ∃ j : ℕ, syracuseStep^[j] 4489 = 1 := reachStep (stepEq 2 (by rfl) ⟨1683, by rfl⟩ : syracuseStep 4489 = 3367) R3367
theorem R4507 : ∃ j : ℕ, syracuseStep^[j] 4507 = 1 := reachStep (stepEq 1 (by rfl) ⟨3380, by rfl⟩ : syracuseStep 4507 = 6761) R6761
theorem R4519 : ∃ j : ℕ, syracuseStep^[j] 4519 = 1 := reachStep (stepEq 1 (by rfl) ⟨3389, by rfl⟩ : syracuseStep 4519 = 6779) R6779
theorem R4523 : ∃ j : ℕ, syracuseStep^[j] 4523 = 1 := reachStep (stepEq 1 (by rfl) ⟨3392, by rfl⟩ : syracuseStep 4523 = 6785) R6785
theorem R4535 : ∃ j : ℕ, syracuseStep^[j] 4535 = 1 := reachStep (stepEq 1 (by rfl) ⟨3401, by rfl⟩ : syracuseStep 4535 = 6803) R6803
theorem R4583 : ∃ j : ℕ, syracuseStep^[j] 4583 = 1 := reachStep (stepEq 1 (by rfl) ⟨3437, by rfl⟩ : syracuseStep 4583 = 6875) R6875
theorem R4615 : ∃ j : ℕ, syracuseStep^[j] 4615 = 1 := reachStep (stepEq 1 (by rfl) ⟨3461, by rfl⟩ : syracuseStep 4615 = 6923) R6923
theorem R4635 : ∃ j : ℕ, syracuseStep^[j] 4635 = 1 := reachStep (stepEq 1 (by rfl) ⟨3476, by rfl⟩ : syracuseStep 4635 = 6953) R6953
theorem R4639 : ∃ j : ℕ, syracuseStep^[j] 4639 = 1 := reachStep (stepEq 1 (by rfl) ⟨3479, by rfl⟩ : syracuseStep 4639 = 6959) R6959
theorem R4655 : ∃ j : ℕ, syracuseStep^[j] 4655 = 1 := reachStep (stepEq 1 (by rfl) ⟨3491, by rfl⟩ : syracuseStep 4655 = 6983) R6983
theorem R4671 : ∃ j : ℕ, syracuseStep^[j] 4671 = 1 := reachStep (stepEq 1 (by rfl) ⟨3503, by rfl⟩ : syracuseStep 4671 = 7007) R7007
theorem R4733 : ∃ j : ℕ, syracuseStep^[j] 4733 = 1 := reachStep (stepEq 3 (by rfl) ⟨887, by rfl⟩ : syracuseStep 4733 = 1775) R1775
theorem R4863 : ∃ j : ℕ, syracuseStep^[j] 4863 = 1 := reachStep (stepEq 1 (by rfl) ⟨3647, by rfl⟩ : syracuseStep 4863 = 7295) R7295
theorem R4977 : ∃ j : ℕ, syracuseStep^[j] 4977 = 1 := reachStep (stepEq 2 (by rfl) ⟨1866, by rfl⟩ : syracuseStep 4977 = 3733) R3733
theorem R4981 : ∃ j : ℕ, syracuseStep^[j] 4981 = 1 := reachStep (stepEq 5 (by rfl) ⟨233, by rfl⟩ : syracuseStep 4981 = 467) R467
theorem R4995 : ∃ j : ℕ, syracuseStep^[j] 4995 = 1 := reachStep (stepEq 1 (by rfl) ⟨3746, by rfl⟩ : syracuseStep 4995 = 7493) R7493
theorem R4999 : ∃ j : ℕ, syracuseStep^[j] 4999 = 1 := reachStep (stepEq 1 (by rfl) ⟨3749, by rfl⟩ : syracuseStep 4999 = 7499) R7499
theorem R5009 : ∃ j : ℕ, syracuseStep^[j] 5009 = 1 := reachStep (stepEq 2 (by rfl) ⟨1878, by rfl⟩ : syracuseStep 5009 = 3757) R3757
theorem R5011 : ∃ j : ℕ, syracuseStep^[j] 5011 = 1 := reachStep (stepEq 1 (by rfl) ⟨3758, by rfl⟩ : syracuseStep 5011 = 7517) R7517
theorem R5021 : ∃ j : ℕ, syracuseStep^[j] 5021 = 1 := reachStep (stepEq 3 (by rfl) ⟨941, by rfl⟩ : syracuseStep 5021 = 1883) R1883
theorem R5023 : ∃ j : ℕ, syracuseStep^[j] 5023 = 1 := reachStep (stepEq 1 (by rfl) ⟨3767, by rfl⟩ : syracuseStep 5023 = 7535) R7535
theorem R5033 : ∃ j : ℕ, syracuseStep^[j] 5033 = 1 := reachStep (stepEq 2 (by rfl) ⟨1887, by rfl⟩ : syracuseStep 5033 = 3775) R3775
theorem R37877 : ∃ j : ℕ, syracuseStep^[j] 37877 = 1 := reachStep (stepEq 5 (by rfl) ⟨1775, by rfl⟩ : syracuseStep 37877 = 3551) R3551
theorem R5151 : ∃ j : ℕ, syracuseStep^[j] 5151 = 1 := reachStep (stepEq 1 (by rfl) ⟨3863, by rfl⟩ : syracuseStep 5151 = 7727) R7727
theorem R71621 : ∃ j : ℕ, syracuseStep^[j] 71621 = 1 := reachStep (stepEq 4 (by rfl) ⟨6714, by rfl⟩ : syracuseStep 71621 = 13429) R13429
theorem R40085 : ∃ j : ℕ, syracuseStep^[j] 40085 = 1 := reachStep (stepEq 6 (by rfl) ⟨939, by rfl⟩ : syracuseStep 40085 = 1879) R1879
theorem R73811 : ∃ j : ℕ, syracuseStep^[j] 73811 = 1 := reachStep (stepEq 1 (by rfl) ⟨55358, by rfl⟩ : syracuseStep 73811 = 110717) R110717
theorem R8987 : ∃ j : ℕ, syracuseStep^[j] 8987 = 1 := reachStep (stepEq 1 (by rfl) ⟨6740, by rfl⟩ : syracuseStep 8987 = 13481) R13481
theorem R9047 : ∃ j : ℕ, syracuseStep^[j] 9047 = 1 := reachStep (stepEq 1 (by rfl) ⟨6785, by rfl⟩ : syracuseStep 9047 = 13571) R13571
theorem R9071 : ∃ j : ℕ, syracuseStep^[j] 9071 = 1 := reachStep (stepEq 1 (by rfl) ⟨6803, by rfl⟩ : syracuseStep 9071 = 13607) R13607
theorem R9083 : ∃ j : ℕ, syracuseStep^[j] 9083 = 1 := reachStep (stepEq 1 (by rfl) ⟨6812, by rfl⟩ : syracuseStep 9083 = 13625) R13625
theorem R9167 : ∃ j : ℕ, syracuseStep^[j] 9167 = 1 := reachStep (stepEq 1 (by rfl) ⟨6875, by rfl⟩ : syracuseStep 9167 = 13751) R13751
theorem R9193 : ∃ j : ℕ, syracuseStep^[j] 9193 = 1 := reachStep (stepEq 2 (by rfl) ⟨3447, by rfl⟩ : syracuseStep 9193 = 6895) R6895
theorem R9305 : ∃ j : ℕ, syracuseStep^[j] 9305 = 1 := reachStep (stepEq 2 (by rfl) ⟨3489, by rfl⟩ : syracuseStep 9305 = 6979) R6979
theorem R9311 : ∃ j : ℕ, syracuseStep^[j] 9311 = 1 := reachStep (stepEq 1 (by rfl) ⟨6983, by rfl⟩ : syracuseStep 9311 = 13967) R13967
theorem R9341 : ∃ j : ℕ, syracuseStep^[j] 9341 = 1 := reachStep (stepEq 3 (by rfl) ⟨1751, by rfl⟩ : syracuseStep 9341 = 3503) R3503
theorem R9941 : ∃ j : ℕ, syracuseStep^[j] 9941 = 1 := reachStep (stepEq 7 (by rfl) ⟨116, by rfl⟩ : syracuseStep 9941 = 233) R233
theorem R9989 : ∃ j : ℕ, syracuseStep^[j] 9989 = 1 := reachStep (stepEq 4 (by rfl) ⟨936, by rfl⟩ : syracuseStep 9989 = 1873) R1873
theorem R10019 : ∃ j : ℕ, syracuseStep^[j] 10019 = 1 := reachStep (stepEq 1 (by rfl) ⟨7514, by rfl⟩ : syracuseStep 10019 = 15029) R15029
theorem R10025 : ∃ j : ℕ, syracuseStep^[j] 10025 = 1 := reachStep (stepEq 2 (by rfl) ⟨3759, by rfl⟩ : syracuseStep 10025 = 7519) R7519
theorem R10055 : ∃ j : ℕ, syracuseStep^[j] 10055 = 1 := reachStep (stepEq 1 (by rfl) ⟨7541, by rfl⟩ : syracuseStep 10055 = 15083) R15083
theorem R10067 : ∃ j : ℕ, syracuseStep^[j] 10067 = 1 := reachStep (stepEq 1 (by rfl) ⟨7550, by rfl⟩ : syracuseStep 10067 = 15101) R15101
theorem R75757 : ∃ j : ℕ, syracuseStep^[j] 75757 = 1 := reachStep (stepEq 3 (by rfl) ⟨14204, by rfl⟩ : syracuseStep 75757 = 28409) R28409
theorem R75761 : ∃ j : ℕ, syracuseStep^[j] 75761 = 1 := reachStep (stepEq 2 (by rfl) ⟨28410, by rfl⟩ : syracuseStep 75761 = 56821) R56821
theorem R11137 : ∃ j : ℕ, syracuseStep^[j] 11137 = 1 := reachStep (stepEq 2 (by rfl) ⟨4176, by rfl⟩ : syracuseStep 11137 = 8353) R8353
theorem R17921 : ∃ j : ℕ, syracuseStep^[j] 17921 = 1 := reachStep (stepEq 2 (by rfl) ⟨6720, by rfl⟩ : syracuseStep 17921 = 13441) R13441
theorem R17927 : ∃ j : ℕ, syracuseStep^[j] 17927 = 1 := reachStep (stepEq 1 (by rfl) ⟨13445, by rfl⟩ : syracuseStep 17927 = 26891) R26891
theorem R17975 : ∃ j : ℕ, syracuseStep^[j] 17975 = 1 := reachStep (stepEq 1 (by rfl) ⟨13481, by rfl⟩ : syracuseStep 17975 = 26963) R26963
theorem R18103 : ∃ j : ℕ, syracuseStep^[j] 18103 = 1 := reachStep (stepEq 1 (by rfl) ⟨13577, by rfl⟩ : syracuseStep 18103 = 27155) R27155
theorem R18143 : ∃ j : ℕ, syracuseStep^[j] 18143 = 1 := reachStep (stepEq 1 (by rfl) ⟨13607, by rfl⟩ : syracuseStep 18143 = 27215) R27215
theorem R19453 : ∃ j : ℕ, syracuseStep^[j] 19453 = 1 := reachStep (stepEq 3 (by rfl) ⟨3647, by rfl⟩ : syracuseStep 19453 = 7295) R7295
theorem R19925 : ∃ j : ℕ, syracuseStep^[j] 19925 = 1 := reachStep (stepEq 7 (by rfl) ⟨233, by rfl⟩ : syracuseStep 19925 = 467) R467
theorem R20033 : ∃ j : ℕ, syracuseStep^[j] 20033 = 1 := reachStep (stepEq 2 (by rfl) ⟨7512, by rfl⟩ : syracuseStep 20033 = 15025) R15025
theorem R20093 : ∃ j : ℕ, syracuseStep^[j] 20093 = 1 := reachStep (stepEq 3 (by rfl) ⟨3767, by rfl⟩ : syracuseStep 20093 = 7535) R7535
theorem R322483 : ∃ j : ℕ, syracuseStep^[j] 322483 = 1 := reachStep (stepEq 1 (by rfl) ⟨241862, by rfl⟩ : syracuseStep 322483 = 483725) R483725
theorem R103 : ∃ j : ℕ, syracuseStep^[j] 103 = 1 := reachStep (stepEq 1 (by rfl) ⟨77, by rfl⟩ : syracuseStep 103 = 155) R155
theorem R207 : ∃ j : ℕ, syracuseStep^[j] 207 = 1 := reachStep (stepEq 1 (by rfl) ⟨155, by rfl⟩ : syracuseStep 207 = 311) R311
theorem R196829 : ∃ j : ℕ, syracuseStep^[j] 196829 = 1 := reachStep (stepEq 3 (by rfl) ⟨36905, by rfl⟩ : syracuseStep 196829 = 73811) R73811
theorem R413 : ∃ j : ℕ, syracuseStep^[j] 413 = 1 := reachStep (stepEq 3 (by rfl) ⟨77, by rfl⟩ : syracuseStep 413 = 155) R155
theorem R745 : ∃ j : ℕ, syracuseStep^[j] 745 = 1 := reachStep (stepEq 2 (by rfl) ⟨279, by rfl⟩ : syracuseStep 745 = 559) R559
theorem R829 : ∃ j : ℕ, syracuseStep^[j] 829 = 1 := reachStep (stepEq 3 (by rfl) ⟨155, by rfl⟩ : syracuseStep 829 = 311) R311
theorem R1491 : ∃ j : ℕ, syracuseStep^[j] 1491 = 1 := reachStep (stepEq 1 (by rfl) ⟨1118, by rfl⟩ : syracuseStep 1491 = 2237) R2237
theorem R1511 : ∃ j : ℕ, syracuseStep^[j] 1511 = 1 := reachStep (stepEq 1 (by rfl) ⟨1133, by rfl⟩ : syracuseStep 1511 = 2267) R2267
theorem R1577 : ∃ j : ℕ, syracuseStep^[j] 1577 = 1 := reachStep (stepEq 2 (by rfl) ⟨591, by rfl⟩ : syracuseStep 1577 = 1183) R1183
theorem R1653 : ∃ j : ℕ, syracuseStep^[j] 1653 = 1 := reachStep (stepEq 5 (by rfl) ⟨77, by rfl⟩ : syracuseStep 1653 = 155) R155
theorem R1673 : ∃ j : ℕ, syracuseStep^[j] 1673 = 1 := reachStep (stepEq 2 (by rfl) ⟨627, by rfl⟩ : syracuseStep 1673 = 1255) R1255
theorem R101009 : ∃ j : ℕ, syracuseStep^[j] 101009 = 1 := reachStep (stepEq 2 (by rfl) ⟨37878, by rfl⟩ : syracuseStep 101009 = 75757) R75757
theorem R2981 : ∃ j : ℕ, syracuseStep^[j] 2981 = 1 := reachStep (stepEq 4 (by rfl) ⟨279, by rfl⟩ : syracuseStep 2981 = 559) R559
theorem R3015 : ∃ j : ℕ, syracuseStep^[j] 3015 = 1 := reachStep (stepEq 1 (by rfl) ⟨2261, by rfl⟩ : syracuseStep 3015 = 4523) R4523
theorem R3023 : ∃ j : ℕ, syracuseStep^[j] 3023 = 1 := reachStep (stepEq 1 (by rfl) ⟨2267, by rfl⟩ : syracuseStep 3023 = 4535) R4535
theorem R3055 : ∃ j : ℕ, syracuseStep^[j] 3055 = 1 := reachStep (stepEq 1 (by rfl) ⟨2291, by rfl⟩ : syracuseStep 3055 = 4583) R4583
theorem R3103 : ∃ j : ℕ, syracuseStep^[j] 3103 = 1 := reachStep (stepEq 1 (by rfl) ⟨2327, by rfl⟩ : syracuseStep 3103 = 4655) R4655
theorem R3113 : ∃ j : ℕ, syracuseStep^[j] 3113 = 1 := reachStep (stepEq 2 (by rfl) ⟨1167, by rfl⟩ : syracuseStep 3113 = 2335) R2335
theorem R3155 : ∃ j : ℕ, syracuseStep^[j] 3155 = 1 := reachStep (stepEq 1 (by rfl) ⟨2366, by rfl⟩ : syracuseStep 3155 = 4733) R4733
theorem R3313 : ∃ j : ℕ, syracuseStep^[j] 3313 = 1 := reachStep (stepEq 2 (by rfl) ⟨1242, by rfl⟩ : syracuseStep 3313 = 2485) R2485
theorem R3317 : ∃ j : ℕ, syracuseStep^[j] 3317 = 1 := reachStep (stepEq 5 (by rfl) ⟨155, by rfl⟩ : syracuseStep 3317 = 311) R311
theorem R3329 : ∃ j : ℕ, syracuseStep^[j] 3329 = 1 := reachStep (stepEq 2 (by rfl) ⟨1248, by rfl⟩ : syracuseStep 3329 = 2497) R2497
theorem R3339 : ∃ j : ℕ, syracuseStep^[j] 3339 = 1 := reachStep (stepEq 1 (by rfl) ⟨2504, by rfl⟩ : syracuseStep 3339 = 5009) R5009
theorem R3347 : ∃ j : ℕ, syracuseStep^[j] 3347 = 1 := reachStep (stepEq 1 (by rfl) ⟨2510, by rfl⟩ : syracuseStep 3347 = 5021) R5021
theorem R3355 : ∃ j : ℕ, syracuseStep^[j] 3355 = 1 := reachStep (stepEq 1 (by rfl) ⟨2516, by rfl⟩ : syracuseStep 3355 = 5033) R5033
theorem R429977 : ∃ j : ℕ, syracuseStep^[j] 429977 = 1 := reachStep (stepEq 2 (by rfl) ⟨161241, by rfl⟩ : syracuseStep 429977 = 322483) R322483
theorem R5965 : ∃ j : ℕ, syracuseStep^[j] 5965 = 1 := reachStep (stepEq 3 (by rfl) ⟨1118, by rfl⟩ : syracuseStep 5965 = 2237) R2237
theorem R5969 : ∃ j : ℕ, syracuseStep^[j] 5969 = 1 := reachStep (stepEq 2 (by rfl) ⟨2238, by rfl⟩ : syracuseStep 5969 = 4477) R4477
theorem R5985 : ∃ j : ℕ, syracuseStep^[j] 5985 = 1 := reachStep (stepEq 2 (by rfl) ⟨2244, by rfl⟩ : syracuseStep 5985 = 4489) R4489
theorem R5991 : ∃ j : ℕ, syracuseStep^[j] 5991 = 1 := reachStep (stepEq 1 (by rfl) ⟨4493, by rfl⟩ : syracuseStep 5991 = 8987) R8987
theorem R6009 : ∃ j : ℕ, syracuseStep^[j] 6009 = 1 := reachStep (stepEq 2 (by rfl) ⟨2253, by rfl⟩ : syracuseStep 6009 = 4507) R4507
theorem R6025 : ∃ j : ℕ, syracuseStep^[j] 6025 = 1 := reachStep (stepEq 2 (by rfl) ⟨2259, by rfl⟩ : syracuseStep 6025 = 4519) R4519
theorem R6031 : ∃ j : ℕ, syracuseStep^[j] 6031 = 1 := reachStep (stepEq 1 (by rfl) ⟨4523, by rfl⟩ : syracuseStep 6031 = 9047) R9047
theorem R6045 : ∃ j : ℕ, syracuseStep^[j] 6045 = 1 := reachStep (stepEq 3 (by rfl) ⟨1133, by rfl⟩ : syracuseStep 6045 = 2267) R2267
theorem R6047 : ∃ j : ℕ, syracuseStep^[j] 6047 = 1 := reachStep (stepEq 1 (by rfl) ⟨4535, by rfl⟩ : syracuseStep 6047 = 9071) R9071
theorem R6055 : ∃ j : ℕ, syracuseStep^[j] 6055 = 1 := reachStep (stepEq 1 (by rfl) ⟨4541, by rfl⟩ : syracuseStep 6055 = 9083) R9083
theorem R6111 : ∃ j : ℕ, syracuseStep^[j] 6111 = 1 := reachStep (stepEq 1 (by rfl) ⟨4583, by rfl⟩ : syracuseStep 6111 = 9167) R9167
theorem R6153 : ∃ j : ℕ, syracuseStep^[j] 6153 = 1 := reachStep (stepEq 2 (by rfl) ⟨2307, by rfl⟩ : syracuseStep 6153 = 4615) R4615
theorem R6185 : ∃ j : ℕ, syracuseStep^[j] 6185 = 1 := reachStep (stepEq 2 (by rfl) ⟨2319, by rfl⟩ : syracuseStep 6185 = 4639) R4639
theorem R6203 : ∃ j : ℕ, syracuseStep^[j] 6203 = 1 := reachStep (stepEq 1 (by rfl) ⟨4652, by rfl⟩ : syracuseStep 6203 = 9305) R9305
theorem R6207 : ∃ j : ℕ, syracuseStep^[j] 6207 = 1 := reachStep (stepEq 1 (by rfl) ⟨4655, by rfl⟩ : syracuseStep 6207 = 9311) R9311
theorem R6227 : ∃ j : ℕ, syracuseStep^[j] 6227 = 1 := reachStep (stepEq 1 (by rfl) ⟨4670, by rfl⟩ : syracuseStep 6227 = 9341) R9341
theorem R6309 : ∃ j : ℕ, syracuseStep^[j] 6309 = 1 := reachStep (stepEq 4 (by rfl) ⟨591, by rfl⟩ : syracuseStep 6309 = 1183) R1183
theorem R6613 : ∃ j : ℕ, syracuseStep^[j] 6613 = 1 := reachStep (stepEq 7 (by rfl) ⟨77, by rfl⟩ : syracuseStep 6613 = 155) R155
theorem R6627 : ∃ j : ℕ, syracuseStep^[j] 6627 = 1 := reachStep (stepEq 1 (by rfl) ⟨4970, by rfl⟩ : syracuseStep 6627 = 9941) R9941
theorem R6641 : ∃ j : ℕ, syracuseStep^[j] 6641 = 1 := reachStep (stepEq 2 (by rfl) ⟨2490, by rfl⟩ : syracuseStep 6641 = 4981) R4981
theorem R6659 : ∃ j : ℕ, syracuseStep^[j] 6659 = 1 := reachStep (stepEq 1 (by rfl) ⟨4994, by rfl⟩ : syracuseStep 6659 = 9989) R9989
theorem R6665 : ∃ j : ℕ, syracuseStep^[j] 6665 = 1 := reachStep (stepEq 2 (by rfl) ⟨2499, by rfl⟩ : syracuseStep 6665 = 4999) R4999
theorem R6679 : ∃ j : ℕ, syracuseStep^[j] 6679 = 1 := reachStep (stepEq 1 (by rfl) ⟨5009, by rfl⟩ : syracuseStep 6679 = 10019) R10019
theorem R6681 : ∃ j : ℕ, syracuseStep^[j] 6681 = 1 := reachStep (stepEq 2 (by rfl) ⟨2505, by rfl⟩ : syracuseStep 6681 = 5011) R5011
theorem R6683 : ∃ j : ℕ, syracuseStep^[j] 6683 = 1 := reachStep (stepEq 1 (by rfl) ⟨5012, by rfl⟩ : syracuseStep 6683 = 10025) R10025
theorem R6693 : ∃ j : ℕ, syracuseStep^[j] 6693 = 1 := reachStep (stepEq 4 (by rfl) ⟨627, by rfl⟩ : syracuseStep 6693 = 1255) R1255
theorem R6697 : ∃ j : ℕ, syracuseStep^[j] 6697 = 1 := reachStep (stepEq 2 (by rfl) ⟨2511, by rfl⟩ : syracuseStep 6697 = 5023) R5023
theorem R6703 : ∃ j : ℕ, syracuseStep^[j] 6703 = 1 := reachStep (stepEq 1 (by rfl) ⟨5027, by rfl⟩ : syracuseStep 6703 = 10055) R10055
theorem R6711 : ∃ j : ℕ, syracuseStep^[j] 6711 = 1 := reachStep (stepEq 1 (by rfl) ⟨5033, by rfl⟩ : syracuseStep 6711 = 10067) R10067
theorem R404021 : ∃ j : ℕ, syracuseStep^[j] 404021 = 1 := reachStep (stepEq 5 (by rfl) ⟨18938, by rfl⟩ : syracuseStep 404021 = 37877) R37877
theorem R11947 : ∃ j : ℕ, syracuseStep^[j] 11947 = 1 := reachStep (stepEq 1 (by rfl) ⟨8960, by rfl⟩ : syracuseStep 11947 = 17921) R17921
theorem R11951 : ∃ j : ℕ, syracuseStep^[j] 11951 = 1 := reachStep (stepEq 1 (by rfl) ⟨8963, by rfl⟩ : syracuseStep 11951 = 17927) R17927
theorem R11983 : ∃ j : ℕ, syracuseStep^[j] 11983 = 1 := reachStep (stepEq 1 (by rfl) ⟨8987, by rfl⟩ : syracuseStep 11983 = 17975) R17975
theorem R12095 : ∃ j : ℕ, syracuseStep^[j] 12095 = 1 := reachStep (stepEq 1 (by rfl) ⟨9071, by rfl⟩ : syracuseStep 12095 = 18143) R18143
theorem R12221 : ∃ j : ℕ, syracuseStep^[j] 12221 = 1 := reachStep (stepEq 3 (by rfl) ⟨2291, by rfl⟩ : syracuseStep 12221 = 4583) R4583
theorem R12257 : ∃ j : ℕ, syracuseStep^[j] 12257 = 1 := reachStep (stepEq 2 (by rfl) ⟨4596, by rfl⟩ : syracuseStep 12257 = 9193) R9193
theorem R12413 : ∃ j : ℕ, syracuseStep^[j] 12413 = 1 := reachStep (stepEq 3 (by rfl) ⟨2327, by rfl⟩ : syracuseStep 12413 = 4655) R4655
theorem R13283 : ∃ j : ℕ, syracuseStep^[j] 13283 = 1 := reachStep (stepEq 1 (by rfl) ⟨9962, by rfl⟩ : syracuseStep 13283 = 19925) R19925
theorem R13355 : ∃ j : ℕ, syracuseStep^[j] 13355 = 1 := reachStep (stepEq 1 (by rfl) ⟨10016, by rfl⟩ : syracuseStep 13355 = 20033) R20033
theorem R14849 : ∃ j : ℕ, syracuseStep^[j] 14849 = 1 := reachStep (stepEq 2 (by rfl) ⟨5568, by rfl⟩ : syracuseStep 14849 = 11137) R11137
theorem R47747 : ∃ j : ℕ, syracuseStep^[j] 47747 = 1 := reachStep (stepEq 1 (by rfl) ⟨35810, by rfl⟩ : syracuseStep 47747 = 71621) R71621
theorem R49207 : ∃ j : ℕ, syracuseStep^[j] 49207 = 1 := reachStep (stepEq 1 (by rfl) ⟨36905, by rfl⟩ : syracuseStep 49207 = 73811) R73811
theorem R49481 : ∃ j : ℕ, syracuseStep^[j] 49481 = 1 := reachStep (stepEq 2 (by rfl) ⟨18555, by rfl⟩ : syracuseStep 49481 = 37111) R37111
theorem R50507 : ∃ j : ℕ, syracuseStep^[j] 50507 = 1 := reachStep (stepEq 1 (by rfl) ⟨37880, by rfl⟩ : syracuseStep 50507 = 75761) R75761
theorem R53581 : ∃ j : ℕ, syracuseStep^[j] 53581 = 1 := reachStep (stepEq 3 (by rfl) ⟨10046, by rfl⟩ : syracuseStep 53581 = 20093) R20093
theorem R24137 : ∃ j : ℕ, syracuseStep^[j] 24137 = 1 := reachStep (stepEq 2 (by rfl) ⟨9051, by rfl⟩ : syracuseStep 24137 = 18103) R18103
theorem R25937 : ∃ j : ℕ, syracuseStep^[j] 25937 = 1 := reachStep (stepEq 2 (by rfl) ⟨9726, by rfl⟩ : syracuseStep 25937 = 19453) R19453
theorem R26723 : ∃ j : ℕ, syracuseStep^[j] 26723 = 1 := reachStep (stepEq 1 (by rfl) ⟨20042, by rfl⟩ : syracuseStep 26723 = 40085) R40085
theorem R65609 : ∃ j : ℕ, syracuseStep^[j] 65609 = 1 := reachStep (stepEq 2 (by rfl) ⟨24603, by rfl⟩ : syracuseStep 65609 = 49207) R49207
theorem R137 : ∃ j : ℕ, syracuseStep^[j] 137 = 1 := reachStep (stepEq 2 (by rfl) ⟨51, by rfl⟩ : syracuseStep 137 = 103) R103
theorem R131219 : ∃ j : ℕ, syracuseStep^[j] 131219 = 1 := reachStep (stepEq 1 (by rfl) ⟨98414, by rfl⟩ : syracuseStep 131219 = 196829) R196829
theorem R32987 : ∃ j : ℕ, syracuseStep^[j] 32987 = 1 := reachStep (stepEq 1 (by rfl) ⟨24740, by rfl⟩ : syracuseStep 32987 = 49481) R49481
theorem R275 : ∃ j : ℕ, syracuseStep^[j] 275 = 1 := reachStep (stepEq 1 (by rfl) ⟨206, by rfl⟩ : syracuseStep 275 = 413) R413
theorem R549 : ∃ j : ℕ, syracuseStep^[j] 549 = 1 := reachStep (stepEq 4 (by rfl) ⟨51, by rfl⟩ : syracuseStep 549 = 103) R103
theorem R33671 : ∃ j : ℕ, syracuseStep^[j] 33671 = 1 := reachStep (stepEq 1 (by rfl) ⟨25253, by rfl⟩ : syracuseStep 33671 = 50507) R50507
theorem R993 : ∃ j : ℕ, syracuseStep^[j] 993 = 1 := reachStep (stepEq 2 (by rfl) ⟨372, by rfl⟩ : syracuseStep 993 = 745) R745
theorem R1007 : ∃ j : ℕ, syracuseStep^[j] 1007 = 1 := reachStep (stepEq 1 (by rfl) ⟨755, by rfl⟩ : syracuseStep 1007 = 1511) R1511
theorem R1051 : ∃ j : ℕ, syracuseStep^[j] 1051 = 1 := reachStep (stepEq 1 (by rfl) ⟨788, by rfl⟩ : syracuseStep 1051 = 1577) R1577
theorem R1101 : ∃ j : ℕ, syracuseStep^[j] 1101 = 1 := reachStep (stepEq 3 (by rfl) ⟨206, by rfl⟩ : syracuseStep 1101 = 413) R413
theorem R1105 : ∃ j : ℕ, syracuseStep^[j] 1105 = 1 := reachStep (stepEq 2 (by rfl) ⟨414, by rfl⟩ : syracuseStep 1105 = 829) R829
theorem R1115 : ∃ j : ℕ, syracuseStep^[j] 1115 = 1 := reachStep (stepEq 1 (by rfl) ⟨836, by rfl⟩ : syracuseStep 1115 = 1673) R1673
theorem R67339 : ∃ j : ℕ, syracuseStep^[j] 67339 = 1 := reachStep (stepEq 1 (by rfl) ⟨50504, by rfl⟩ : syracuseStep 67339 = 101009) R101009
theorem R1987 : ∃ j : ℕ, syracuseStep^[j] 1987 = 1 := reachStep (stepEq 1 (by rfl) ⟨1490, by rfl⟩ : syracuseStep 1987 = 2981) R2981
theorem R2015 : ∃ j : ℕ, syracuseStep^[j] 2015 = 1 := reachStep (stepEq 1 (by rfl) ⟨1511, by rfl⟩ : syracuseStep 2015 = 3023) R3023
theorem R2075 : ∃ j : ℕ, syracuseStep^[j] 2075 = 1 := reachStep (stepEq 1 (by rfl) ⟨1556, by rfl⟩ : syracuseStep 2075 = 3113) R3113
theorem R2103 : ∃ j : ℕ, syracuseStep^[j] 2103 = 1 := reachStep (stepEq 1 (by rfl) ⟨1577, by rfl⟩ : syracuseStep 2103 = 3155) R3155
theorem R2197 : ∃ j : ℕ, syracuseStep^[j] 2197 = 1 := reachStep (stepEq 6 (by rfl) ⟨51, by rfl⟩ : syracuseStep 2197 = 103) R103
theorem R2211 : ∃ j : ℕ, syracuseStep^[j] 2211 = 1 := reachStep (stepEq 1 (by rfl) ⟨1658, by rfl⟩ : syracuseStep 2211 = 3317) R3317
theorem R2219 : ∃ j : ℕ, syracuseStep^[j] 2219 = 1 := reachStep (stepEq 1 (by rfl) ⟨1664, by rfl⟩ : syracuseStep 2219 = 3329) R3329
theorem R2231 : ∃ j : ℕ, syracuseStep^[j] 2231 = 1 := reachStep (stepEq 1 (by rfl) ⟨1673, by rfl⟩ : syracuseStep 2231 = 3347) R3347
theorem R3973 : ∃ j : ℕ, syracuseStep^[j] 3973 = 1 := reachStep (stepEq 4 (by rfl) ⟨372, by rfl⟩ : syracuseStep 3973 = 745) R745
theorem R3979 : ∃ j : ℕ, syracuseStep^[j] 3979 = 1 := reachStep (stepEq 1 (by rfl) ⟨2984, by rfl⟩ : syracuseStep 3979 = 5969) R5969
theorem R4029 : ∃ j : ℕ, syracuseStep^[j] 4029 = 1 := reachStep (stepEq 3 (by rfl) ⟨755, by rfl⟩ : syracuseStep 4029 = 1511) R1511
theorem R4031 : ∃ j : ℕ, syracuseStep^[j] 4031 = 1 := reachStep (stepEq 1 (by rfl) ⟨3023, by rfl⟩ : syracuseStep 4031 = 6047) R6047
theorem R4073 : ∃ j : ℕ, syracuseStep^[j] 4073 = 1 := reachStep (stepEq 2 (by rfl) ⟨1527, by rfl⟩ : syracuseStep 4073 = 3055) R3055
theorem R4123 : ∃ j : ℕ, syracuseStep^[j] 4123 = 1 := reachStep (stepEq 1 (by rfl) ⟨3092, by rfl⟩ : syracuseStep 4123 = 6185) R6185
theorem R4135 : ∃ j : ℕ, syracuseStep^[j] 4135 = 1 := reachStep (stepEq 1 (by rfl) ⟨3101, by rfl⟩ : syracuseStep 4135 = 6203) R6203
theorem R4137 : ∃ j : ℕ, syracuseStep^[j] 4137 = 1 := reachStep (stepEq 2 (by rfl) ⟨1551, by rfl⟩ : syracuseStep 4137 = 3103) R3103
theorem R4151 : ∃ j : ℕ, syracuseStep^[j] 4151 = 1 := reachStep (stepEq 1 (by rfl) ⟨3113, by rfl⟩ : syracuseStep 4151 = 6227) R6227
theorem R4205 : ∃ j : ℕ, syracuseStep^[j] 4205 = 1 := reachStep (stepEq 3 (by rfl) ⟨788, by rfl⟩ : syracuseStep 4205 = 1577) R1577
theorem R4405 : ∃ j : ℕ, syracuseStep^[j] 4405 = 1 := reachStep (stepEq 5 (by rfl) ⟨206, by rfl⟩ : syracuseStep 4405 = 413) R413
theorem R4417 : ∃ j : ℕ, syracuseStep^[j] 4417 = 1 := reachStep (stepEq 2 (by rfl) ⟨1656, by rfl⟩ : syracuseStep 4417 = 3313) R3313
theorem R4421 : ∃ j : ℕ, syracuseStep^[j] 4421 = 1 := reachStep (stepEq 4 (by rfl) ⟨414, by rfl⟩ : syracuseStep 4421 = 829) R829
theorem R4427 : ∃ j : ℕ, syracuseStep^[j] 4427 = 1 := reachStep (stepEq 1 (by rfl) ⟨3320, by rfl⟩ : syracuseStep 4427 = 6641) R6641
theorem R4439 : ∃ j : ℕ, syracuseStep^[j] 4439 = 1 := reachStep (stepEq 1 (by rfl) ⟨3329, by rfl⟩ : syracuseStep 4439 = 6659) R6659
theorem R4443 : ∃ j : ℕ, syracuseStep^[j] 4443 = 1 := reachStep (stepEq 1 (by rfl) ⟨3332, by rfl⟩ : syracuseStep 4443 = 6665) R6665
theorem R4455 : ∃ j : ℕ, syracuseStep^[j] 4455 = 1 := reachStep (stepEq 1 (by rfl) ⟨3341, by rfl⟩ : syracuseStep 4455 = 6683) R6683
theorem R4461 : ∃ j : ℕ, syracuseStep^[j] 4461 = 1 := reachStep (stepEq 3 (by rfl) ⟨836, by rfl⟩ : syracuseStep 4461 = 1673) R1673
theorem R4473 : ∃ j : ℕ, syracuseStep^[j] 4473 = 1 := reachStep (stepEq 2 (by rfl) ⟨1677, by rfl⟩ : syracuseStep 4473 = 3355) R3355
theorem R71441 : ∃ j : ℕ, syracuseStep^[j] 71441 = 1 := reachStep (stepEq 2 (by rfl) ⟨26790, by rfl⟩ : syracuseStep 71441 = 53581) R53581
theorem R269347 : ∃ j : ℕ, syracuseStep^[j] 269347 = 1 := reachStep (stepEq 1 (by rfl) ⟨202010, by rfl⟩ : syracuseStep 269347 = 404021) R404021
theorem R7949 : ∃ j : ℕ, syracuseStep^[j] 7949 = 1 := reachStep (stepEq 3 (by rfl) ⟨1490, by rfl⟩ : syracuseStep 7949 = 2981) R2981
theorem R7967 : ∃ j : ℕ, syracuseStep^[j] 7967 = 1 := reachStep (stepEq 1 (by rfl) ⟨5975, by rfl⟩ : syracuseStep 7967 = 11951) R11951
theorem R8033 : ∃ j : ℕ, syracuseStep^[j] 8033 = 1 := reachStep (stepEq 2 (by rfl) ⟨3012, by rfl⟩ : syracuseStep 8033 = 6025) R6025
theorem R8063 : ∃ j : ℕ, syracuseStep^[j] 8063 = 1 := reachStep (stepEq 1 (by rfl) ⟨6047, by rfl⟩ : syracuseStep 8063 = 12095) R12095
theorem R8147 : ∃ j : ℕ, syracuseStep^[j] 8147 = 1 := reachStep (stepEq 1 (by rfl) ⟨6110, by rfl⟩ : syracuseStep 8147 = 12221) R12221
theorem R8171 : ∃ j : ℕ, syracuseStep^[j] 8171 = 1 := reachStep (stepEq 1 (by rfl) ⟨6128, by rfl⟩ : syracuseStep 8171 = 12257) R12257
theorem R8275 : ∃ j : ℕ, syracuseStep^[j] 8275 = 1 := reachStep (stepEq 1 (by rfl) ⟨6206, by rfl⟩ : syracuseStep 8275 = 12413) R12413
theorem R8789 : ∃ j : ℕ, syracuseStep^[j] 8789 = 1 := reachStep (stepEq 8 (by rfl) ⟨51, by rfl⟩ : syracuseStep 8789 = 103) R103
theorem R8855 : ∃ j : ℕ, syracuseStep^[j] 8855 = 1 := reachStep (stepEq 1 (by rfl) ⟨6641, by rfl⟩ : syracuseStep 8855 = 13283) R13283
theorem R8903 : ∃ j : ℕ, syracuseStep^[j] 8903 = 1 := reachStep (stepEq 1 (by rfl) ⟨6677, by rfl⟩ : syracuseStep 8903 = 13355) R13355
theorem R9899 : ∃ j : ℕ, syracuseStep^[j] 9899 = 1 := reachStep (stepEq 1 (by rfl) ⟨7424, by rfl⟩ : syracuseStep 9899 = 14849) R14849
theorem R15929 : ∃ j : ℕ, syracuseStep^[j] 15929 = 1 := reachStep (stepEq 2 (by rfl) ⟨5973, by rfl⟩ : syracuseStep 15929 = 11947) R11947
theorem R15977 : ∃ j : ℕ, syracuseStep^[j] 15977 = 1 := reachStep (stepEq 2 (by rfl) ⟨5991, by rfl⟩ : syracuseStep 15977 = 11983) R11983
theorem R16091 : ∃ j : ℕ, syracuseStep^[j] 16091 = 1 := reachStep (stepEq 1 (by rfl) ⟨12068, by rfl⟩ : syracuseStep 16091 = 24137) R24137
theorem R17291 : ∃ j : ℕ, syracuseStep^[j] 17291 = 1 := reachStep (stepEq 1 (by rfl) ⟨12968, by rfl⟩ : syracuseStep 17291 = 25937) R25937
theorem R17815 : ∃ j : ℕ, syracuseStep^[j] 17815 = 1 := reachStep (stepEq 1 (by rfl) ⟨13361, by rfl⟩ : syracuseStep 17815 = 26723) R26723
theorem R286651 : ∃ j : ℕ, syracuseStep^[j] 286651 = 1 := reachStep (stepEq 1 (by rfl) ⟨214988, by rfl⟩ : syracuseStep 286651 = 429977) R429977
theorem R127325 : ∃ j : ℕ, syracuseStep^[j] 127325 = 1 := reachStep (stepEq 3 (by rfl) ⟨23873, by rfl⟩ : syracuseStep 127325 = 47747) R47747
theorem R91 : ∃ j : ℕ, syracuseStep^[j] 91 = 1 := reachStep (stepEq 1 (by rfl) ⟨68, by rfl⟩ : syracuseStep 91 = 137) R137
theorem R183 : ∃ j : ℕ, syracuseStep^[j] 183 = 1 := reachStep (stepEq 1 (by rfl) ⟨137, by rfl⟩ : syracuseStep 183 = 275) R275
theorem R365 : ∃ j : ℕ, syracuseStep^[j] 365 = 1 := reachStep (stepEq 3 (by rfl) ⟨68, by rfl⟩ : syracuseStep 365 = 137) R137
theorem R671 : ∃ j : ℕ, syracuseStep^[j] 671 = 1 := reachStep (stepEq 1 (by rfl) ⟨503, by rfl⟩ : syracuseStep 671 = 1007) R1007
theorem R733 : ∃ j : ℕ, syracuseStep^[j] 733 = 1 := reachStep (stepEq 3 (by rfl) ⟨137, by rfl⟩ : syracuseStep 733 = 275) R275
theorem R743 : ∃ j : ℕ, syracuseStep^[j] 743 = 1 := reachStep (stepEq 1 (by rfl) ⟨557, by rfl⟩ : syracuseStep 743 = 1115) R1115
theorem R1343 : ∃ j : ℕ, syracuseStep^[j] 1343 = 1 := reachStep (stepEq 1 (by rfl) ⟨1007, by rfl⟩ : syracuseStep 1343 = 2015) R2015
theorem R1383 : ∃ j : ℕ, syracuseStep^[j] 1383 = 1 := reachStep (stepEq 1 (by rfl) ⟨1037, by rfl⟩ : syracuseStep 1383 = 2075) R2075
theorem R1401 : ∃ j : ℕ, syracuseStep^[j] 1401 = 1 := reachStep (stepEq 2 (by rfl) ⟨525, by rfl⟩ : syracuseStep 1401 = 1051) R1051
theorem R1461 : ∃ j : ℕ, syracuseStep^[j] 1461 = 1 := reachStep (stepEq 5 (by rfl) ⟨68, by rfl⟩ : syracuseStep 1461 = 137) R137
theorem R1473 : ∃ j : ℕ, syracuseStep^[j] 1473 = 1 := reachStep (stepEq 2 (by rfl) ⟨552, by rfl⟩ : syracuseStep 1473 = 1105) R1105
theorem R1479 : ∃ j : ℕ, syracuseStep^[j] 1479 = 1 := reachStep (stepEq 1 (by rfl) ⟨1109, by rfl⟩ : syracuseStep 1479 = 2219) R2219
theorem R1487 : ∃ j : ℕ, syracuseStep^[j] 1487 = 1 := reachStep (stepEq 1 (by rfl) ⟨1115, by rfl⟩ : syracuseStep 1487 = 2231) R2231
theorem R2649 : ∃ j : ℕ, syracuseStep^[j] 2649 = 1 := reachStep (stepEq 2 (by rfl) ⟨993, by rfl⟩ : syracuseStep 2649 = 1987) R1987
theorem R2685 : ∃ j : ℕ, syracuseStep^[j] 2685 = 1 := reachStep (stepEq 3 (by rfl) ⟨503, by rfl⟩ : syracuseStep 2685 = 1007) R1007
theorem R2687 : ∃ j : ℕ, syracuseStep^[j] 2687 = 1 := reachStep (stepEq 1 (by rfl) ⟨2015, by rfl⟩ : syracuseStep 2687 = 4031) R4031
theorem R2715 : ∃ j : ℕ, syracuseStep^[j] 2715 = 1 := reachStep (stepEq 1 (by rfl) ⟨2036, by rfl⟩ : syracuseStep 2715 = 4073) R4073
theorem R2767 : ∃ j : ℕ, syracuseStep^[j] 2767 = 1 := reachStep (stepEq 1 (by rfl) ⟨2075, by rfl⟩ : syracuseStep 2767 = 4151) R4151
theorem R2803 : ∃ j : ℕ, syracuseStep^[j] 2803 = 1 := reachStep (stepEq 1 (by rfl) ⟨2102, by rfl⟩ : syracuseStep 2803 = 4205) R4205
theorem R2929 : ∃ j : ℕ, syracuseStep^[j] 2929 = 1 := reachStep (stepEq 2 (by rfl) ⟨1098, by rfl⟩ : syracuseStep 2929 = 2197) R2197
theorem R2933 : ∃ j : ℕ, syracuseStep^[j] 2933 = 1 := reachStep (stepEq 5 (by rfl) ⟨137, by rfl⟩ : syracuseStep 2933 = 275) R275
theorem R2947 : ∃ j : ℕ, syracuseStep^[j] 2947 = 1 := reachStep (stepEq 1 (by rfl) ⟨2210, by rfl⟩ : syracuseStep 2947 = 4421) R4421
theorem R2951 : ∃ j : ℕ, syracuseStep^[j] 2951 = 1 := reachStep (stepEq 1 (by rfl) ⟨2213, by rfl⟩ : syracuseStep 2951 = 4427) R4427
theorem R2959 : ∃ j : ℕ, syracuseStep^[j] 2959 = 1 := reachStep (stepEq 1 (by rfl) ⟨2219, by rfl⟩ : syracuseStep 2959 = 4439) R4439
theorem R2973 : ∃ j : ℕ, syracuseStep^[j] 2973 = 1 := reachStep (stepEq 3 (by rfl) ⟨557, by rfl⟩ : syracuseStep 2973 = 1115) R1115
theorem R5297 : ∃ j : ℕ, syracuseStep^[j] 5297 = 1 := reachStep (stepEq 2 (by rfl) ⟨1986, by rfl⟩ : syracuseStep 5297 = 3973) R3973
theorem R5299 : ∃ j : ℕ, syracuseStep^[j] 5299 = 1 := reachStep (stepEq 1 (by rfl) ⟨3974, by rfl⟩ : syracuseStep 5299 = 7949) R7949
theorem R5305 : ∃ j : ℕ, syracuseStep^[j] 5305 = 1 := reachStep (stepEq 2 (by rfl) ⟨1989, by rfl⟩ : syracuseStep 5305 = 3979) R3979
theorem R5311 : ∃ j : ℕ, syracuseStep^[j] 5311 = 1 := reachStep (stepEq 1 (by rfl) ⟨3983, by rfl⟩ : syracuseStep 5311 = 7967) R7967
theorem R5355 : ∃ j : ℕ, syracuseStep^[j] 5355 = 1 := reachStep (stepEq 1 (by rfl) ⟨4016, by rfl⟩ : syracuseStep 5355 = 8033) R8033
theorem R5373 : ∃ j : ℕ, syracuseStep^[j] 5373 = 1 := reachStep (stepEq 3 (by rfl) ⟨1007, by rfl⟩ : syracuseStep 5373 = 2015) R2015
theorem R5375 : ∃ j : ℕ, syracuseStep^[j] 5375 = 1 := reachStep (stepEq 1 (by rfl) ⟨4031, by rfl⟩ : syracuseStep 5375 = 8063) R8063
theorem R5431 : ∃ j : ℕ, syracuseStep^[j] 5431 = 1 := reachStep (stepEq 1 (by rfl) ⟨4073, by rfl⟩ : syracuseStep 5431 = 8147) R8147
theorem R5447 : ∃ j : ℕ, syracuseStep^[j] 5447 = 1 := reachStep (stepEq 1 (by rfl) ⟨4085, by rfl⟩ : syracuseStep 5447 = 8171) R8171
theorem R5497 : ∃ j : ℕ, syracuseStep^[j] 5497 = 1 := reachStep (stepEq 2 (by rfl) ⟨2061, by rfl⟩ : syracuseStep 5497 = 4123) R4123
theorem R5513 : ∃ j : ℕ, syracuseStep^[j] 5513 = 1 := reachStep (stepEq 2 (by rfl) ⟨2067, by rfl⟩ : syracuseStep 5513 = 4135) R4135
theorem R5533 : ∃ j : ℕ, syracuseStep^[j] 5533 = 1 := reachStep (stepEq 3 (by rfl) ⟨1037, by rfl⟩ : syracuseStep 5533 = 2075) R2075
theorem R5605 : ∃ j : ℕ, syracuseStep^[j] 5605 = 1 := reachStep (stepEq 4 (by rfl) ⟨525, by rfl⟩ : syracuseStep 5605 = 1051) R1051
theorem R5845 : ∃ j : ℕ, syracuseStep^[j] 5845 = 1 := reachStep (stepEq 7 (by rfl) ⟨68, by rfl⟩ : syracuseStep 5845 = 137) R137
theorem R5859 : ∃ j : ℕ, syracuseStep^[j] 5859 = 1 := reachStep (stepEq 1 (by rfl) ⟨4394, by rfl⟩ : syracuseStep 5859 = 8789) R8789
theorem R5873 : ∃ j : ℕ, syracuseStep^[j] 5873 = 1 := reachStep (stepEq 2 (by rfl) ⟨2202, by rfl⟩ : syracuseStep 5873 = 4405) R4405
theorem R5889 : ∃ j : ℕ, syracuseStep^[j] 5889 = 1 := reachStep (stepEq 2 (by rfl) ⟨2208, by rfl⟩ : syracuseStep 5889 = 4417) R4417
theorem R5893 : ∃ j : ℕ, syracuseStep^[j] 5893 = 1 := reachStep (stepEq 4 (by rfl) ⟨552, by rfl⟩ : syracuseStep 5893 = 1105) R1105
theorem R5903 : ∃ j : ℕ, syracuseStep^[j] 5903 = 1 := reachStep (stepEq 1 (by rfl) ⟨4427, by rfl⟩ : syracuseStep 5903 = 8855) R8855
theorem R5917 : ∃ j : ℕ, syracuseStep^[j] 5917 = 1 := reachStep (stepEq 3 (by rfl) ⟨1109, by rfl⟩ : syracuseStep 5917 = 2219) R2219
theorem R5935 : ∃ j : ℕ, syracuseStep^[j] 5935 = 1 := reachStep (stepEq 1 (by rfl) ⟨4451, by rfl⟩ : syracuseStep 5935 = 8903) R8903
theorem R5949 : ∃ j : ℕ, syracuseStep^[j] 5949 = 1 := reachStep (stepEq 3 (by rfl) ⟨1115, by rfl⟩ : syracuseStep 5949 = 2231) R2231
theorem R6599 : ∃ j : ℕ, syracuseStep^[j] 6599 = 1 := reachStep (stepEq 1 (by rfl) ⟨4949, by rfl⟩ : syracuseStep 6599 = 9899) R9899
theorem R10597 : ∃ j : ℕ, syracuseStep^[j] 10597 = 1 := reachStep (stepEq 4 (by rfl) ⟨993, by rfl⟩ : syracuseStep 10597 = 1987) R1987
theorem R10619 : ∃ j : ℕ, syracuseStep^[j] 10619 = 1 := reachStep (stepEq 1 (by rfl) ⟨7964, by rfl⟩ : syracuseStep 10619 = 15929) R15929
theorem R10651 : ∃ j : ℕ, syracuseStep^[j] 10651 = 1 := reachStep (stepEq 1 (by rfl) ⟨7988, by rfl⟩ : syracuseStep 10651 = 15977) R15977
theorem R10727 : ∃ j : ℕ, syracuseStep^[j] 10727 = 1 := reachStep (stepEq 1 (by rfl) ⟨8045, by rfl⟩ : syracuseStep 10727 = 16091) R16091
theorem R43739 : ∃ j : ℕ, syracuseStep^[j] 43739 = 1 := reachStep (stepEq 1 (by rfl) ⟨32804, by rfl⟩ : syracuseStep 43739 = 65609) R65609
theorem R11033 : ∃ j : ℕ, syracuseStep^[j] 11033 = 1 := reachStep (stepEq 2 (by rfl) ⟨4137, by rfl⟩ : syracuseStep 11033 = 8275) R8275
theorem R11069 : ∃ j : ℕ, syracuseStep^[j] 11069 = 1 := reachStep (stepEq 3 (by rfl) ⟨2075, by rfl⟩ : syracuseStep 11069 = 4151) R4151
theorem R11213 : ∃ j : ℕ, syracuseStep^[j] 11213 = 1 := reachStep (stepEq 3 (by rfl) ⟨2102, by rfl⟩ : syracuseStep 11213 = 4205) R4205
theorem R11717 : ∃ j : ℕ, syracuseStep^[j] 11717 = 1 := reachStep (stepEq 4 (by rfl) ⟨1098, by rfl⟩ : syracuseStep 11717 = 2197) R2197
theorem R11789 : ∃ j : ℕ, syracuseStep^[j] 11789 = 1 := reachStep (stepEq 3 (by rfl) ⟨2210, by rfl⟩ : syracuseStep 11789 = 4421) R4421
theorem R46109 : ∃ j : ℕ, syracuseStep^[j] 46109 = 1 := reachStep (stepEq 3 (by rfl) ⟨8645, by rfl⟩ : syracuseStep 46109 = 17291) R17291
theorem R47627 : ∃ j : ℕ, syracuseStep^[j] 47627 = 1 := reachStep (stepEq 1 (by rfl) ⟨35720, by rfl⟩ : syracuseStep 47627 = 71441) R71441
theorem R84883 : ∃ j : ℕ, syracuseStep^[j] 84883 = 1 := reachStep (stepEq 1 (by rfl) ⟨63662, by rfl⟩ : syracuseStep 84883 = 127325) R127325
theorem R21221 : ∃ j : ℕ, syracuseStep^[j] 21221 = 1 := reachStep (stepEq 4 (by rfl) ⟨1989, by rfl⟩ : syracuseStep 21221 = 3979) R3979
theorem R382201 : ∃ j : ℕ, syracuseStep^[j] 382201 = 1 := reachStep (stepEq 2 (by rfl) ⟨143325, by rfl⟩ : syracuseStep 382201 = 286651) R286651
theorem R87479 : ∃ j : ℕ, syracuseStep^[j] 87479 = 1 := reachStep (stepEq 1 (by rfl) ⟨65609, by rfl⟩ : syracuseStep 87479 = 131219) R131219
theorem R21991 : ∃ j : ℕ, syracuseStep^[j] 21991 = 1 := reachStep (stepEq 1 (by rfl) ⟨16493, by rfl⟩ : syracuseStep 21991 = 32987) R32987
theorem R22133 : ∃ j : ℕ, syracuseStep^[j] 22133 = 1 := reachStep (stepEq 5 (by rfl) ⟨1037, by rfl⟩ : syracuseStep 22133 = 2075) R2075
theorem R22447 : ∃ j : ℕ, syracuseStep^[j] 22447 = 1 := reachStep (stepEq 1 (by rfl) ⟨16835, by rfl⟩ : syracuseStep 22447 = 33671) R33671
theorem R23753 : ∃ j : ℕ, syracuseStep^[j] 23753 = 1 := reachStep (stepEq 2 (by rfl) ⟨8907, by rfl⟩ : syracuseStep 23753 = 17815) R17815
theorem R89785 : ∃ j : ℕ, syracuseStep^[j] 89785 = 1 := reachStep (stepEq 2 (by rfl) ⟨33669, by rfl⟩ : syracuseStep 89785 = 67339) R67339
theorem R359129 : ∃ j : ℕ, syracuseStep^[j] 359129 = 1 := reachStep (stepEq 2 (by rfl) ⟨134673, by rfl⟩ : syracuseStep 359129 = 269347) R269347
theorem R121 : ∃ j : ℕ, syracuseStep^[j] 121 = 1 := reachStep (stepEq 2 (by rfl) ⟨45, by rfl⟩ : syracuseStep 121 = 91) R91
theorem R243 : ∃ j : ℕ, syracuseStep^[j] 243 = 1 := reachStep (stepEq 1 (by rfl) ⟨182, by rfl⟩ : syracuseStep 243 = 365) R365
theorem R447 : ∃ j : ℕ, syracuseStep^[j] 447 = 1 := reachStep (stepEq 1 (by rfl) ⟨335, by rfl⟩ : syracuseStep 447 = 671) R671
theorem R485 : ∃ j : ℕ, syracuseStep^[j] 485 = 1 := reachStep (stepEq 4 (by rfl) ⟨45, by rfl⟩ : syracuseStep 485 = 91) R91
theorem R495 : ∃ j : ℕ, syracuseStep^[j] 495 = 1 := reachStep (stepEq 1 (by rfl) ⟨371, by rfl⟩ : syracuseStep 495 = 743) R743
theorem R895 : ∃ j : ℕ, syracuseStep^[j] 895 = 1 := reachStep (stepEq 1 (by rfl) ⟨671, by rfl⟩ : syracuseStep 895 = 1343) R1343
theorem R973 : ∃ j : ℕ, syracuseStep^[j] 973 = 1 := reachStep (stepEq 3 (by rfl) ⟨182, by rfl⟩ : syracuseStep 973 = 365) R365
theorem R977 : ∃ j : ℕ, syracuseStep^[j] 977 = 1 := reachStep (stepEq 2 (by rfl) ⟨366, by rfl⟩ : syracuseStep 977 = 733) R733
theorem R991 : ∃ j : ℕ, syracuseStep^[j] 991 = 1 := reachStep (stepEq 1 (by rfl) ⟨743, by rfl⟩ : syracuseStep 991 = 1487) R1487
theorem R1789 : ∃ j : ℕ, syracuseStep^[j] 1789 = 1 := reachStep (stepEq 3 (by rfl) ⟨335, by rfl⟩ : syracuseStep 1789 = 671) R671
theorem R1791 : ∃ j : ℕ, syracuseStep^[j] 1791 = 1 := reachStep (stepEq 1 (by rfl) ⟨1343, by rfl⟩ : syracuseStep 1791 = 2687) R2687
theorem R1941 : ∃ j : ℕ, syracuseStep^[j] 1941 = 1 := reachStep (stepEq 6 (by rfl) ⟨45, by rfl⟩ : syracuseStep 1941 = 91) R91
theorem R1955 : ∃ j : ℕ, syracuseStep^[j] 1955 = 1 := reachStep (stepEq 1 (by rfl) ⟨1466, by rfl⟩ : syracuseStep 1955 = 2933) R2933
theorem R1967 : ∃ j : ℕ, syracuseStep^[j] 1967 = 1 := reachStep (stepEq 1 (by rfl) ⟨1475, by rfl⟩ : syracuseStep 1967 = 2951) R2951
theorem R1981 : ∃ j : ℕ, syracuseStep^[j] 1981 = 1 := reachStep (stepEq 3 (by rfl) ⟨371, by rfl⟩ : syracuseStep 1981 = 743) R743
theorem R3531 : ∃ j : ℕ, syracuseStep^[j] 3531 = 1 := reachStep (stepEq 1 (by rfl) ⟨2648, by rfl⟩ : syracuseStep 3531 = 5297) R5297
theorem R3581 : ∃ j : ℕ, syracuseStep^[j] 3581 = 1 := reachStep (stepEq 3 (by rfl) ⟨671, by rfl⟩ : syracuseStep 3581 = 1343) R1343
theorem R3583 : ∃ j : ℕ, syracuseStep^[j] 3583 = 1 := reachStep (stepEq 1 (by rfl) ⟨2687, by rfl⟩ : syracuseStep 3583 = 5375) R5375
theorem R3631 : ∃ j : ℕ, syracuseStep^[j] 3631 = 1 := reachStep (stepEq 1 (by rfl) ⟨2723, by rfl⟩ : syracuseStep 3631 = 5447) R5447
theorem R3675 : ∃ j : ℕ, syracuseStep^[j] 3675 = 1 := reachStep (stepEq 1 (by rfl) ⟨2756, by rfl⟩ : syracuseStep 3675 = 5513) R5513
theorem R3689 : ∃ j : ℕ, syracuseStep^[j] 3689 = 1 := reachStep (stepEq 2 (by rfl) ⟨1383, by rfl⟩ : syracuseStep 3689 = 2767) R2767
theorem R3737 : ∃ j : ℕ, syracuseStep^[j] 3737 = 1 := reachStep (stepEq 2 (by rfl) ⟨1401, by rfl⟩ : syracuseStep 3737 = 2803) R2803
theorem R3893 : ∃ j : ℕ, syracuseStep^[j] 3893 = 1 := reachStep (stepEq 5 (by rfl) ⟨182, by rfl⟩ : syracuseStep 3893 = 365) R365
theorem R3905 : ∃ j : ℕ, syracuseStep^[j] 3905 = 1 := reachStep (stepEq 2 (by rfl) ⟨1464, by rfl⟩ : syracuseStep 3905 = 2929) R2929
theorem R3909 : ∃ j : ℕ, syracuseStep^[j] 3909 = 1 := reachStep (stepEq 4 (by rfl) ⟨366, by rfl⟩ : syracuseStep 3909 = 733) R733
theorem R3915 : ∃ j : ℕ, syracuseStep^[j] 3915 = 1 := reachStep (stepEq 1 (by rfl) ⟨2936, by rfl⟩ : syracuseStep 3915 = 5873) R5873
theorem R3929 : ∃ j : ℕ, syracuseStep^[j] 3929 = 1 := reachStep (stepEq 2 (by rfl) ⟨1473, by rfl⟩ : syracuseStep 3929 = 2947) R2947
theorem R3935 : ∃ j : ℕ, syracuseStep^[j] 3935 = 1 := reachStep (stepEq 1 (by rfl) ⟨2951, by rfl⟩ : syracuseStep 3935 = 5903) R5903
theorem R3945 : ∃ j : ℕ, syracuseStep^[j] 3945 = 1 := reachStep (stepEq 2 (by rfl) ⟨1479, by rfl⟩ : syracuseStep 3945 = 2959) R2959
theorem R3965 : ∃ j : ℕ, syracuseStep^[j] 3965 = 1 := reachStep (stepEq 3 (by rfl) ⟨743, by rfl⟩ : syracuseStep 3965 = 1487) R1487
theorem R4399 : ∃ j : ℕ, syracuseStep^[j] 4399 = 1 := reachStep (stepEq 1 (by rfl) ⟨3299, by rfl⟩ : syracuseStep 4399 = 6599) R6599
theorem R2038405 : ∃ j : ℕ, syracuseStep^[j] 2038405 = 1 := reachStep (stepEq 4 (by rfl) ⟨191100, by rfl⟩ : syracuseStep 2038405 = 382201) R382201
theorem R7073 : ∃ j : ℕ, syracuseStep^[j] 7073 = 1 := reachStep (stepEq 2 (by rfl) ⟨2652, by rfl⟩ : syracuseStep 7073 = 5305) R5305
theorem R7079 : ∃ j : ℕ, syracuseStep^[j] 7079 = 1 := reachStep (stepEq 1 (by rfl) ⟨5309, by rfl⟩ : syracuseStep 7079 = 10619) R10619
theorem R7151 : ∃ j : ℕ, syracuseStep^[j] 7151 = 1 := reachStep (stepEq 1 (by rfl) ⟨5363, by rfl⟩ : syracuseStep 7151 = 10727) R10727
theorem R7157 : ∃ j : ℕ, syracuseStep^[j] 7157 = 1 := reachStep (stepEq 5 (by rfl) ⟨335, by rfl⟩ : syracuseStep 7157 = 671) R671
theorem R7165 : ∃ j : ℕ, syracuseStep^[j] 7165 = 1 := reachStep (stepEq 3 (by rfl) ⟨1343, by rfl⟩ : syracuseStep 7165 = 2687) R2687
theorem R7241 : ∃ j : ℕ, syracuseStep^[j] 7241 = 1 := reachStep (stepEq 2 (by rfl) ⟨2715, by rfl⟩ : syracuseStep 7241 = 5431) R5431
theorem R7355 : ∃ j : ℕ, syracuseStep^[j] 7355 = 1 := reachStep (stepEq 1 (by rfl) ⟨5516, by rfl⟩ : syracuseStep 7355 = 11033) R11033
theorem R7379 : ∃ j : ℕ, syracuseStep^[j] 7379 = 1 := reachStep (stepEq 1 (by rfl) ⟨5534, by rfl⟩ : syracuseStep 7379 = 11069) R11069
theorem R7475 : ∃ j : ℕ, syracuseStep^[j] 7475 = 1 := reachStep (stepEq 1 (by rfl) ⟨5606, by rfl⟩ : syracuseStep 7475 = 11213) R11213
theorem R7793 : ∃ j : ℕ, syracuseStep^[j] 7793 = 1 := reachStep (stepEq 2 (by rfl) ⟨2922, by rfl⟩ : syracuseStep 7793 = 5845) R5845
theorem R7811 : ∃ j : ℕ, syracuseStep^[j] 7811 = 1 := reachStep (stepEq 1 (by rfl) ⟨5858, by rfl⟩ : syracuseStep 7811 = 11717) R11717
theorem R7859 : ∃ j : ℕ, syracuseStep^[j] 7859 = 1 := reachStep (stepEq 1 (by rfl) ⟨5894, by rfl⟩ : syracuseStep 7859 = 11789) R11789
theorem R7889 : ∃ j : ℕ, syracuseStep^[j] 7889 = 1 := reachStep (stepEq 2 (by rfl) ⟨2958, by rfl⟩ : syracuseStep 7889 = 5917) R5917
theorem R7913 : ∃ j : ℕ, syracuseStep^[j] 7913 = 1 := reachStep (stepEq 2 (by rfl) ⟨2967, by rfl⟩ : syracuseStep 7913 = 5935) R5935
theorem R7925 : ∃ j : ℕ, syracuseStep^[j] 7925 = 1 := reachStep (stepEq 5 (by rfl) ⟨371, by rfl⟩ : syracuseStep 7925 = 743) R743
theorem R239419 : ∃ j : ℕ, syracuseStep^[j] 239419 = 1 := reachStep (stepEq 1 (by rfl) ⟨179564, by rfl⟩ : syracuseStep 239419 = 359129) R359129
theorem R14129 : ∃ j : ℕ, syracuseStep^[j] 14129 = 1 := reachStep (stepEq 2 (by rfl) ⟨5298, by rfl⟩ : syracuseStep 14129 = 10597) R10597
theorem R14147 : ∃ j : ℕ, syracuseStep^[j] 14147 = 1 := reachStep (stepEq 1 (by rfl) ⟨10610, by rfl⟩ : syracuseStep 14147 = 21221) R21221
theorem R14201 : ∃ j : ℕ, syracuseStep^[j] 14201 = 1 := reachStep (stepEq 2 (by rfl) ⟨5325, by rfl⟩ : syracuseStep 14201 = 10651) R10651
theorem R14525 : ∃ j : ℕ, syracuseStep^[j] 14525 = 1 := reachStep (stepEq 3 (by rfl) ⟨2723, by rfl⟩ : syracuseStep 14525 = 5447) R5447
theorem R14701 : ∃ j : ℕ, syracuseStep^[j] 14701 = 1 := reachStep (stepEq 3 (by rfl) ⟨2756, by rfl⟩ : syracuseStep 14701 = 5513) R5513
theorem R14755 : ∃ j : ℕ, syracuseStep^[j] 14755 = 1 := reachStep (stepEq 1 (by rfl) ⟨11066, by rfl⟩ : syracuseStep 14755 = 22133) R22133
theorem R113177 : ∃ j : ℕ, syracuseStep^[j] 113177 = 1 := reachStep (stepEq 2 (by rfl) ⟨42441, by rfl⟩ : syracuseStep 113177 = 84883) R84883
theorem R15835 : ∃ j : ℕ, syracuseStep^[j] 15835 = 1 := reachStep (stepEq 1 (by rfl) ⟨11876, by rfl⟩ : syracuseStep 15835 = 23753) R23753
theorem R119713 : ∃ j : ℕ, syracuseStep^[j] 119713 = 1 := reachStep (stepEq 2 (by rfl) ⟨44892, by rfl⟩ : syracuseStep 119713 = 89785) R89785
theorem R119717 : ∃ j : ℕ, syracuseStep^[j] 119717 = 1 := reachStep (stepEq 4 (by rfl) ⟨11223, by rfl⟩ : syracuseStep 119717 = 22447) R22447
theorem R58319 : ∃ j : ℕ, syracuseStep^[j] 58319 = 1 := reachStep (stepEq 1 (by rfl) ⟨43739, by rfl⟩ : syracuseStep 58319 = 87479) R87479
theorem R29159 : ∃ j : ℕ, syracuseStep^[j] 29159 = 1 := reachStep (stepEq 1 (by rfl) ⟨21869, by rfl⟩ : syracuseStep 29159 = 43739) R43739
theorem R29321 : ∃ j : ℕ, syracuseStep^[j] 29321 = 1 := reachStep (stepEq 2 (by rfl) ⟨10995, by rfl⟩ : syracuseStep 29321 = 21991) R21991
theorem R30739 : ∃ j : ℕ, syracuseStep^[j] 30739 = 1 := reachStep (stepEq 1 (by rfl) ⟨23054, by rfl⟩ : syracuseStep 30739 = 46109) R46109
theorem R31751 : ∃ j : ℕ, syracuseStep^[j] 31751 = 1 := reachStep (stepEq 1 (by rfl) ⟨23813, by rfl⟩ : syracuseStep 31751 = 47627) R47627
theorem R161 : ∃ j : ℕ, syracuseStep^[j] 161 = 1 := reachStep (stepEq 2 (by rfl) ⟨60, by rfl⟩ : syracuseStep 161 = 121) R121
theorem R323 : ∃ j : ℕ, syracuseStep^[j] 323 = 1 := reachStep (stepEq 1 (by rfl) ⟨242, by rfl⟩ : syracuseStep 323 = 485) R485
theorem R645 : ∃ j : ℕ, syracuseStep^[j] 645 = 1 := reachStep (stepEq 4 (by rfl) ⟨60, by rfl⟩ : syracuseStep 645 = 121) R121
theorem R651 : ∃ j : ℕ, syracuseStep^[j] 651 = 1 := reachStep (stepEq 1 (by rfl) ⟨488, by rfl⟩ : syracuseStep 651 = 977) R977
theorem R1193 : ∃ j : ℕ, syracuseStep^[j] 1193 = 1 := reachStep (stepEq 2 (by rfl) ⟨447, by rfl⟩ : syracuseStep 1193 = 895) R895
theorem R1293 : ∃ j : ℕ, syracuseStep^[j] 1293 = 1 := reachStep (stepEq 3 (by rfl) ⟨242, by rfl⟩ : syracuseStep 1293 = 485) R485
theorem R1297 : ∃ j : ℕ, syracuseStep^[j] 1297 = 1 := reachStep (stepEq 2 (by rfl) ⟨486, by rfl⟩ : syracuseStep 1297 = 973) R973
theorem R1303 : ∃ j : ℕ, syracuseStep^[j] 1303 = 1 := reachStep (stepEq 1 (by rfl) ⟨977, by rfl⟩ : syracuseStep 1303 = 1955) R1955
theorem R1311 : ∃ j : ℕ, syracuseStep^[j] 1311 = 1 := reachStep (stepEq 1 (by rfl) ⟨983, by rfl⟩ : syracuseStep 1311 = 1967) R1967
theorem R1321 : ∃ j : ℕ, syracuseStep^[j] 1321 = 1 := reachStep (stepEq 2 (by rfl) ⟨495, by rfl⟩ : syracuseStep 1321 = 991) R991
theorem R2385 : ∃ j : ℕ, syracuseStep^[j] 2385 = 1 := reachStep (stepEq 2 (by rfl) ⟨894, by rfl⟩ : syracuseStep 2385 = 1789) R1789
theorem R2387 : ∃ j : ℕ, syracuseStep^[j] 2387 = 1 := reachStep (stepEq 1 (by rfl) ⟨1790, by rfl⟩ : syracuseStep 2387 = 3581) R3581
theorem R2459 : ∃ j : ℕ, syracuseStep^[j] 2459 = 1 := reachStep (stepEq 1 (by rfl) ⟨1844, by rfl⟩ : syracuseStep 2459 = 3689) R3689
theorem R2491 : ∃ j : ℕ, syracuseStep^[j] 2491 = 1 := reachStep (stepEq 1 (by rfl) ⟨1868, by rfl⟩ : syracuseStep 2491 = 3737) R3737
theorem R2581 : ∃ j : ℕ, syracuseStep^[j] 2581 = 1 := reachStep (stepEq 6 (by rfl) ⟨60, by rfl⟩ : syracuseStep 2581 = 121) R121
theorem R2595 : ∃ j : ℕ, syracuseStep^[j] 2595 = 1 := reachStep (stepEq 1 (by rfl) ⟨1946, by rfl⟩ : syracuseStep 2595 = 3893) R3893
theorem R2603 : ∃ j : ℕ, syracuseStep^[j] 2603 = 1 := reachStep (stepEq 1 (by rfl) ⟨1952, by rfl⟩ : syracuseStep 2603 = 3905) R3905
theorem R2605 : ∃ j : ℕ, syracuseStep^[j] 2605 = 1 := reachStep (stepEq 3 (by rfl) ⟨488, by rfl⟩ : syracuseStep 2605 = 977) R977
theorem R2619 : ∃ j : ℕ, syracuseStep^[j] 2619 = 1 := reachStep (stepEq 1 (by rfl) ⟨1964, by rfl⟩ : syracuseStep 2619 = 3929) R3929
theorem R2623 : ∃ j : ℕ, syracuseStep^[j] 2623 = 1 := reachStep (stepEq 1 (by rfl) ⟨1967, by rfl⟩ : syracuseStep 2623 = 3935) R3935
theorem R2641 : ∃ j : ℕ, syracuseStep^[j] 2641 = 1 := reachStep (stepEq 2 (by rfl) ⟨990, by rfl⟩ : syracuseStep 2641 = 1981) R1981
theorem R2643 : ∃ j : ℕ, syracuseStep^[j] 2643 = 1 := reachStep (stepEq 1 (by rfl) ⟨1982, by rfl⟩ : syracuseStep 2643 = 3965) R3965
theorem R4715 : ∃ j : ℕ, syracuseStep^[j] 4715 = 1 := reachStep (stepEq 1 (by rfl) ⟨3536, by rfl⟩ : syracuseStep 4715 = 7073) R7073
theorem R4719 : ∃ j : ℕ, syracuseStep^[j] 4719 = 1 := reachStep (stepEq 1 (by rfl) ⟨3539, by rfl⟩ : syracuseStep 4719 = 7079) R7079
theorem R4767 : ∃ j : ℕ, syracuseStep^[j] 4767 = 1 := reachStep (stepEq 1 (by rfl) ⟨3575, by rfl⟩ : syracuseStep 4767 = 7151) R7151
theorem R4771 : ∃ j : ℕ, syracuseStep^[j] 4771 = 1 := reachStep (stepEq 1 (by rfl) ⟨3578, by rfl⟩ : syracuseStep 4771 = 7157) R7157
theorem R4773 : ∃ j : ℕ, syracuseStep^[j] 4773 = 1 := reachStep (stepEq 4 (by rfl) ⟨447, by rfl⟩ : syracuseStep 4773 = 895) R895
theorem R4777 : ∃ j : ℕ, syracuseStep^[j] 4777 = 1 := reachStep (stepEq 2 (by rfl) ⟨1791, by rfl⟩ : syracuseStep 4777 = 3583) R3583
theorem R4827 : ∃ j : ℕ, syracuseStep^[j] 4827 = 1 := reachStep (stepEq 1 (by rfl) ⟨3620, by rfl⟩ : syracuseStep 4827 = 7241) R7241
theorem R4841 : ∃ j : ℕ, syracuseStep^[j] 4841 = 1 := reachStep (stepEq 2 (by rfl) ⟨1815, by rfl⟩ : syracuseStep 4841 = 3631) R3631
theorem R4903 : ∃ j : ℕ, syracuseStep^[j] 4903 = 1 := reachStep (stepEq 1 (by rfl) ⟨3677, by rfl⟩ : syracuseStep 4903 = 7355) R7355
theorem R4919 : ∃ j : ℕ, syracuseStep^[j] 4919 = 1 := reachStep (stepEq 1 (by rfl) ⟨3689, by rfl⟩ : syracuseStep 4919 = 7379) R7379
theorem R4983 : ∃ j : ℕ, syracuseStep^[j] 4983 = 1 := reachStep (stepEq 1 (by rfl) ⟨3737, by rfl⟩ : syracuseStep 4983 = 7475) R7475
theorem R5173 : ∃ j : ℕ, syracuseStep^[j] 5173 = 1 := reachStep (stepEq 5 (by rfl) ⟨242, by rfl⟩ : syracuseStep 5173 = 485) R485
theorem R5189 : ∃ j : ℕ, syracuseStep^[j] 5189 = 1 := reachStep (stepEq 4 (by rfl) ⟨486, by rfl⟩ : syracuseStep 5189 = 973) R973
theorem R5195 : ∃ j : ℕ, syracuseStep^[j] 5195 = 1 := reachStep (stepEq 1 (by rfl) ⟨3896, by rfl⟩ : syracuseStep 5195 = 7793) R7793
theorem R5207 : ∃ j : ℕ, syracuseStep^[j] 5207 = 1 := reachStep (stepEq 1 (by rfl) ⟨3905, by rfl⟩ : syracuseStep 5207 = 7811) R7811
theorem R5213 : ∃ j : ℕ, syracuseStep^[j] 5213 = 1 := reachStep (stepEq 3 (by rfl) ⟨977, by rfl⟩ : syracuseStep 5213 = 1955) R1955
theorem R5239 : ∃ j : ℕ, syracuseStep^[j] 5239 = 1 := reachStep (stepEq 1 (by rfl) ⟨3929, by rfl⟩ : syracuseStep 5239 = 7859) R7859
theorem R5245 : ∃ j : ℕ, syracuseStep^[j] 5245 = 1 := reachStep (stepEq 3 (by rfl) ⟨983, by rfl⟩ : syracuseStep 5245 = 1967) R1967
theorem R5259 : ∃ j : ℕ, syracuseStep^[j] 5259 = 1 := reachStep (stepEq 1 (by rfl) ⟨3944, by rfl⟩ : syracuseStep 5259 = 7889) R7889
theorem R5275 : ∃ j : ℕ, syracuseStep^[j] 5275 = 1 := reachStep (stepEq 1 (by rfl) ⟨3956, by rfl⟩ : syracuseStep 5275 = 7913) R7913
theorem R5283 : ∃ j : ℕ, syracuseStep^[j] 5283 = 1 := reachStep (stepEq 1 (by rfl) ⟨3962, by rfl⟩ : syracuseStep 5283 = 7925) R7925
theorem R5285 : ∃ j : ℕ, syracuseStep^[j] 5285 = 1 := reachStep (stepEq 4 (by rfl) ⟨495, by rfl⟩ : syracuseStep 5285 = 991) R991
theorem R5865 : ∃ j : ℕ, syracuseStep^[j] 5865 = 1 := reachStep (stepEq 2 (by rfl) ⟨2199, by rfl⟩ : syracuseStep 5865 = 4399) R4399
theorem R38879 : ∃ j : ℕ, syracuseStep^[j] 38879 = 1 := reachStep (stepEq 1 (by rfl) ⟨29159, by rfl⟩ : syracuseStep 38879 = 58319) R58319
theorem R40985 : ∃ j : ℕ, syracuseStep^[j] 40985 = 1 := reachStep (stepEq 2 (by rfl) ⟨15369, by rfl⟩ : syracuseStep 40985 = 30739) R30739
theorem R9419 : ∃ j : ℕ, syracuseStep^[j] 9419 = 1 := reachStep (stepEq 1 (by rfl) ⟨7064, by rfl⟩ : syracuseStep 9419 = 14129) R14129
theorem R9431 : ∃ j : ℕ, syracuseStep^[j] 9431 = 1 := reachStep (stepEq 1 (by rfl) ⟨7073, by rfl⟩ : syracuseStep 9431 = 14147) R14147
theorem R9467 : ∃ j : ℕ, syracuseStep^[j] 9467 = 1 := reachStep (stepEq 1 (by rfl) ⟨7100, by rfl⟩ : syracuseStep 9467 = 14201) R14201
theorem R9553 : ∃ j : ℕ, syracuseStep^[j] 9553 = 1 := reachStep (stepEq 2 (by rfl) ⟨3582, by rfl⟩ : syracuseStep 9553 = 7165) R7165
theorem R9683 : ∃ j : ℕ, syracuseStep^[j] 9683 = 1 := reachStep (stepEq 1 (by rfl) ⟨7262, by rfl⟩ : syracuseStep 9683 = 14525) R14525
theorem R75451 : ∃ j : ℕ, syracuseStep^[j] 75451 = 1 := reachStep (stepEq 1 (by rfl) ⟨56588, by rfl⟩ : syracuseStep 75451 = 113177) R113177
theorem R9965 : ∃ j : ℕ, syracuseStep^[j] 9965 = 1 := reachStep (stepEq 3 (by rfl) ⟨1868, by rfl⟩ : syracuseStep 9965 = 3737) R3737
theorem R10381 : ∃ j : ℕ, syracuseStep^[j] 10381 = 1 := reachStep (stepEq 3 (by rfl) ⟨1946, by rfl⟩ : syracuseStep 10381 = 3893) R3893
theorem R10421 : ∃ j : ℕ, syracuseStep^[j] 10421 = 1 := reachStep (stepEq 5 (by rfl) ⟨488, by rfl⟩ : syracuseStep 10421 = 977) R977
theorem R10493 : ∃ j : ℕ, syracuseStep^[j] 10493 = 1 := reachStep (stepEq 3 (by rfl) ⟨1967, by rfl⟩ : syracuseStep 10493 = 3935) R3935
theorem R10565 : ∃ j : ℕ, syracuseStep^[j] 10565 = 1 := reachStep (stepEq 4 (by rfl) ⟨990, by rfl⟩ : syracuseStep 10565 = 1981) R1981
theorem R79811 : ∃ j : ℕ, syracuseStep^[j] 79811 = 1 := reachStep (stepEq 1 (by rfl) ⟨59858, by rfl⟩ : syracuseStep 79811 = 119717) R119717
theorem R19439 : ∃ j : ℕ, syracuseStep^[j] 19439 = 1 := reachStep (stepEq 1 (by rfl) ⟨14579, by rfl⟩ : syracuseStep 19439 = 29159) R29159
theorem R19547 : ∃ j : ℕ, syracuseStep^[j] 19547 = 1 := reachStep (stepEq 1 (by rfl) ⟨14660, by rfl⟩ : syracuseStep 19547 = 29321) R29321
theorem R19601 : ∃ j : ℕ, syracuseStep^[j] 19601 = 1 := reachStep (stepEq 2 (by rfl) ⟨7350, by rfl⟩ : syracuseStep 19601 = 14701) R14701
theorem R19673 : ∃ j : ℕ, syracuseStep^[j] 19673 = 1 := reachStep (stepEq 2 (by rfl) ⟨7377, by rfl⟩ : syracuseStep 19673 = 14755) R14755
theorem R21113 : ∃ j : ℕ, syracuseStep^[j] 21113 = 1 := reachStep (stepEq 2 (by rfl) ⟨7917, by rfl⟩ : syracuseStep 21113 = 15835) R15835
theorem R21167 : ∃ j : ℕ, syracuseStep^[j] 21167 = 1 := reachStep (stepEq 1 (by rfl) ⟨15875, by rfl⟩ : syracuseStep 21167 = 31751) R31751
theorem R159617 : ∃ j : ℕ, syracuseStep^[j] 159617 = 1 := reachStep (stepEq 2 (by rfl) ⟨59856, by rfl⟩ : syracuseStep 159617 = 119713) R119713
theorem R2717873 : ∃ j : ℕ, syracuseStep^[j] 2717873 = 1 := reachStep (stepEq 2 (by rfl) ⟨1019202, by rfl⟩ : syracuseStep 2717873 = 2038405) R2038405
theorem R1276901 : ∃ j : ℕ, syracuseStep^[j] 1276901 = 1 := reachStep (stepEq 4 (by rfl) ⟨119709, by rfl⟩ : syracuseStep 1276901 = 239419) R239419
theorem R107 : ∃ j : ℕ, syracuseStep^[j] 107 = 1 := reachStep (stepEq 1 (by rfl) ⟨80, by rfl⟩ : syracuseStep 107 = 161) R161
theorem R215 : ∃ j : ℕ, syracuseStep^[j] 215 = 1 := reachStep (stepEq 1 (by rfl) ⟨161, by rfl⟩ : syracuseStep 215 = 323) R323
theorem R429 : ∃ j : ℕ, syracuseStep^[j] 429 = 1 := reachStep (stepEq 3 (by rfl) ⟨80, by rfl⟩ : syracuseStep 429 = 161) R161
theorem R795 : ∃ j : ℕ, syracuseStep^[j] 795 = 1 := reachStep (stepEq 1 (by rfl) ⟨596, by rfl⟩ : syracuseStep 795 = 1193) R1193
theorem R861 : ∃ j : ℕ, syracuseStep^[j] 861 = 1 := reachStep (stepEq 3 (by rfl) ⟨161, by rfl⟩ : syracuseStep 861 = 323) R323
theorem R1591 : ∃ j : ℕ, syracuseStep^[j] 1591 = 1 := reachStep (stepEq 1 (by rfl) ⟨1193, by rfl⟩ : syracuseStep 1591 = 2387) R2387
theorem R1639 : ∃ j : ℕ, syracuseStep^[j] 1639 = 1 := reachStep (stepEq 1 (by rfl) ⟨1229, by rfl⟩ : syracuseStep 1639 = 2459) R2459
theorem R1717 : ∃ j : ℕ, syracuseStep^[j] 1717 = 1 := reachStep (stepEq 5 (by rfl) ⟨80, by rfl⟩ : syracuseStep 1717 = 161) R161
theorem R1729 : ∃ j : ℕ, syracuseStep^[j] 1729 = 1 := reachStep (stepEq 2 (by rfl) ⟨648, by rfl⟩ : syracuseStep 1729 = 1297) R1297
theorem R1735 : ∃ j : ℕ, syracuseStep^[j] 1735 = 1 := reachStep (stepEq 1 (by rfl) ⟨1301, by rfl⟩ : syracuseStep 1735 = 2603) R2603
theorem R1737 : ∃ j : ℕ, syracuseStep^[j] 1737 = 1 := reachStep (stepEq 2 (by rfl) ⟨651, by rfl⟩ : syracuseStep 1737 = 1303) R1303
theorem R1761 : ∃ j : ℕ, syracuseStep^[j] 1761 = 1 := reachStep (stepEq 2 (by rfl) ⟨660, by rfl⟩ : syracuseStep 1761 = 1321) R1321
theorem R100601 : ∃ j : ℕ, syracuseStep^[j] 100601 = 1 := reachStep (stepEq 2 (by rfl) ⟨37725, by rfl⟩ : syracuseStep 100601 = 75451) R75451
theorem R3143 : ∃ j : ℕ, syracuseStep^[j] 3143 = 1 := reachStep (stepEq 1 (by rfl) ⟨2357, by rfl⟩ : syracuseStep 3143 = 4715) R4715
theorem R3181 : ∃ j : ℕ, syracuseStep^[j] 3181 = 1 := reachStep (stepEq 3 (by rfl) ⟨596, by rfl⟩ : syracuseStep 3181 = 1193) R1193
theorem R3227 : ∃ j : ℕ, syracuseStep^[j] 3227 = 1 := reachStep (stepEq 1 (by rfl) ⟨2420, by rfl⟩ : syracuseStep 3227 = 4841) R4841
theorem R3279 : ∃ j : ℕ, syracuseStep^[j] 3279 = 1 := reachStep (stepEq 1 (by rfl) ⟨2459, by rfl⟩ : syracuseStep 3279 = 4919) R4919
theorem R3321 : ∃ j : ℕ, syracuseStep^[j] 3321 = 1 := reachStep (stepEq 2 (by rfl) ⟨1245, by rfl⟩ : syracuseStep 3321 = 2491) R2491
theorem R3441 : ∃ j : ℕ, syracuseStep^[j] 3441 = 1 := reachStep (stepEq 2 (by rfl) ⟨1290, by rfl⟩ : syracuseStep 3441 = 2581) R2581
theorem R3445 : ∃ j : ℕ, syracuseStep^[j] 3445 = 1 := reachStep (stepEq 5 (by rfl) ⟨161, by rfl⟩ : syracuseStep 3445 = 323) R323
theorem R3459 : ∃ j : ℕ, syracuseStep^[j] 3459 = 1 := reachStep (stepEq 1 (by rfl) ⟨2594, by rfl⟩ : syracuseStep 3459 = 5189) R5189
theorem R3463 : ∃ j : ℕ, syracuseStep^[j] 3463 = 1 := reachStep (stepEq 1 (by rfl) ⟨2597, by rfl⟩ : syracuseStep 3463 = 5195) R5195
theorem R3471 : ∃ j : ℕ, syracuseStep^[j] 3471 = 1 := reachStep (stepEq 1 (by rfl) ⟨2603, by rfl⟩ : syracuseStep 3471 = 5207) R5207
theorem R3473 : ∃ j : ℕ, syracuseStep^[j] 3473 = 1 := reachStep (stepEq 2 (by rfl) ⟨1302, by rfl⟩ : syracuseStep 3473 = 2605) R2605
theorem R3475 : ∃ j : ℕ, syracuseStep^[j] 3475 = 1 := reachStep (stepEq 1 (by rfl) ⟨2606, by rfl⟩ : syracuseStep 3475 = 5213) R5213
theorem R3497 : ∃ j : ℕ, syracuseStep^[j] 3497 = 1 := reachStep (stepEq 2 (by rfl) ⟨1311, by rfl⟩ : syracuseStep 3497 = 2623) R2623
theorem R3521 : ∃ j : ℕ, syracuseStep^[j] 3521 = 1 := reachStep (stepEq 2 (by rfl) ⟨1320, by rfl⟩ : syracuseStep 3521 = 2641) R2641
theorem R3523 : ∃ j : ℕ, syracuseStep^[j] 3523 = 1 := reachStep (stepEq 1 (by rfl) ⟨2642, by rfl⟩ : syracuseStep 3523 = 5285) R5285
theorem R6279 : ∃ j : ℕ, syracuseStep^[j] 6279 = 1 := reachStep (stepEq 1 (by rfl) ⟨4709, by rfl⟩ : syracuseStep 6279 = 9419) R9419
theorem R6287 : ∃ j : ℕ, syracuseStep^[j] 6287 = 1 := reachStep (stepEq 1 (by rfl) ⟨4715, by rfl⟩ : syracuseStep 6287 = 9431) R9431
theorem R6311 : ∃ j : ℕ, syracuseStep^[j] 6311 = 1 := reachStep (stepEq 1 (by rfl) ⟨4733, by rfl⟩ : syracuseStep 6311 = 9467) R9467
theorem R6361 : ∃ j : ℕ, syracuseStep^[j] 6361 = 1 := reachStep (stepEq 2 (by rfl) ⟨2385, by rfl⟩ : syracuseStep 6361 = 4771) R4771
theorem R6365 : ∃ j : ℕ, syracuseStep^[j] 6365 = 1 := reachStep (stepEq 3 (by rfl) ⟨1193, by rfl⟩ : syracuseStep 6365 = 2387) R2387
theorem R6369 : ∃ j : ℕ, syracuseStep^[j] 6369 = 1 := reachStep (stepEq 2 (by rfl) ⟨2388, by rfl⟩ : syracuseStep 6369 = 4777) R4777
theorem R6455 : ∃ j : ℕ, syracuseStep^[j] 6455 = 1 := reachStep (stepEq 1 (by rfl) ⟨4841, by rfl⟩ : syracuseStep 6455 = 9683) R9683
theorem R6537 : ∃ j : ℕ, syracuseStep^[j] 6537 = 1 := reachStep (stepEq 2 (by rfl) ⟨2451, by rfl⟩ : syracuseStep 6537 = 4903) R4903
theorem R6557 : ∃ j : ℕ, syracuseStep^[j] 6557 = 1 := reachStep (stepEq 3 (by rfl) ⟨1229, by rfl⟩ : syracuseStep 6557 = 2459) R2459
theorem R6643 : ∃ j : ℕ, syracuseStep^[j] 6643 = 1 := reachStep (stepEq 1 (by rfl) ⟨4982, by rfl⟩ : syracuseStep 6643 = 9965) R9965
theorem R6869 : ∃ j : ℕ, syracuseStep^[j] 6869 = 1 := reachStep (stepEq 7 (by rfl) ⟨80, by rfl⟩ : syracuseStep 6869 = 161) R161
theorem R6917 : ∃ j : ℕ, syracuseStep^[j] 6917 = 1 := reachStep (stepEq 4 (by rfl) ⟨648, by rfl⟩ : syracuseStep 6917 = 1297) R1297
theorem R6941 : ∃ j : ℕ, syracuseStep^[j] 6941 = 1 := reachStep (stepEq 3 (by rfl) ⟨1301, by rfl⟩ : syracuseStep 6941 = 2603) R2603
theorem R6947 : ∃ j : ℕ, syracuseStep^[j] 6947 = 1 := reachStep (stepEq 1 (by rfl) ⟨5210, by rfl⟩ : syracuseStep 6947 = 10421) R10421
theorem R6995 : ∃ j : ℕ, syracuseStep^[j] 6995 = 1 := reachStep (stepEq 1 (by rfl) ⟨5246, by rfl⟩ : syracuseStep 6995 = 10493) R10493
theorem R7033 : ∃ j : ℕ, syracuseStep^[j] 7033 = 1 := reachStep (stepEq 2 (by rfl) ⟨2637, by rfl⟩ : syracuseStep 7033 = 5275) R5275
theorem R7043 : ∃ j : ℕ, syracuseStep^[j] 7043 = 1 := reachStep (stepEq 1 (by rfl) ⟨5282, by rfl⟩ : syracuseStep 7043 = 10565) R10565
theorem R1811915 : ∃ j : ℕ, syracuseStep^[j] 1811915 = 1 := reachStep (stepEq 1 (by rfl) ⟨1358936, by rfl⟩ : syracuseStep 1811915 = 2717873) R2717873
theorem R12725 : ∃ j : ℕ, syracuseStep^[j] 12725 = 1 := reachStep (stepEq 5 (by rfl) ⟨596, by rfl⟩ : syracuseStep 12725 = 1193) R1193
theorem R12737 : ∃ j : ℕ, syracuseStep^[j] 12737 = 1 := reachStep (stepEq 2 (by rfl) ⟨4776, by rfl⟩ : syracuseStep 12737 = 9553) R9553
theorem R12959 : ∃ j : ℕ, syracuseStep^[j] 12959 = 1 := reachStep (stepEq 1 (by rfl) ⟨9719, by rfl⟩ : syracuseStep 12959 = 19439) R19439
theorem R13031 : ∃ j : ℕ, syracuseStep^[j] 13031 = 1 := reachStep (stepEq 1 (by rfl) ⟨9773, by rfl⟩ : syracuseStep 13031 = 19547) R19547
theorem R13067 : ∃ j : ℕ, syracuseStep^[j] 13067 = 1 := reachStep (stepEq 1 (by rfl) ⟨9800, by rfl⟩ : syracuseStep 13067 = 19601) R19601
theorem R13115 : ∃ j : ℕ, syracuseStep^[j] 13115 = 1 := reachStep (stepEq 1 (by rfl) ⟨9836, by rfl⟩ : syracuseStep 13115 = 19673) R19673
theorem R13841 : ∃ j : ℕ, syracuseStep^[j] 13841 = 1 := reachStep (stepEq 2 (by rfl) ⟨5190, by rfl⟩ : syracuseStep 13841 = 10381) R10381
theorem R14075 : ∃ j : ℕ, syracuseStep^[j] 14075 = 1 := reachStep (stepEq 1 (by rfl) ⟨10556, by rfl⟩ : syracuseStep 14075 = 21113) R21113
theorem R14093 : ∃ j : ℕ, syracuseStep^[j] 14093 = 1 := reachStep (stepEq 3 (by rfl) ⟨2642, by rfl⟩ : syracuseStep 14093 = 5285) R5285
theorem R14111 : ∃ j : ℕ, syracuseStep^[j] 14111 = 1 := reachStep (stepEq 1 (by rfl) ⟨10583, by rfl⟩ : syracuseStep 14111 = 21167) R21167
theorem R53207 : ∃ j : ℕ, syracuseStep^[j] 53207 = 1 := reachStep (stepEq 1 (by rfl) ⟨39905, by rfl⟩ : syracuseStep 53207 = 79811) R79811
theorem R25919 : ∃ j : ℕ, syracuseStep^[j] 25919 = 1 := reachStep (stepEq 1 (by rfl) ⟨19439, by rfl⟩ : syracuseStep 25919 = 38879) R38879
theorem R27323 : ∃ j : ℕ, syracuseStep^[j] 27323 = 1 := reachStep (stepEq 1 (by rfl) ⟨20492, by rfl⟩ : syracuseStep 27323 = 40985) R40985
theorem R28181 : ∃ j : ℕ, syracuseStep^[j] 28181 = 1 := reachStep (stepEq 6 (by rfl) ⟨660, by rfl⟩ : syracuseStep 28181 = 1321) R1321
theorem R851267 : ∃ j : ℕ, syracuseStep^[j] 851267 = 1 := reachStep (stepEq 1 (by rfl) ⟨638450, by rfl⟩ : syracuseStep 851267 = 1276901) R1276901
theorem R425645 : ∃ j : ℕ, syracuseStep^[j] 425645 = 1 := reachStep (stepEq 3 (by rfl) ⟨79808, by rfl⟩ : syracuseStep 425645 = 159617) R159617
theorem R71 : ∃ j : ℕ, syracuseStep^[j] 71 = 1 := reachStep (stepEq 1 (by rfl) ⟨53, by rfl⟩ : syracuseStep 71 = 107) R107
theorem R143 : ∃ j : ℕ, syracuseStep^[j] 143 = 1 := reachStep (stepEq 1 (by rfl) ⟨107, by rfl⟩ : syracuseStep 143 = 215) R215
theorem R285 : ∃ j : ℕ, syracuseStep^[j] 285 = 1 := reachStep (stepEq 3 (by rfl) ⟨53, by rfl⟩ : syracuseStep 285 = 107) R107
theorem R573 : ∃ j : ℕ, syracuseStep^[j] 573 = 1 := reachStep (stepEq 3 (by rfl) ⟨107, by rfl⟩ : syracuseStep 573 = 215) R215
theorem R1141 : ∃ j : ℕ, syracuseStep^[j] 1141 = 1 := reachStep (stepEq 5 (by rfl) ⟨53, by rfl⟩ : syracuseStep 1141 = 107) R107
theorem R67067 : ∃ j : ℕ, syracuseStep^[j] 67067 = 1 := reachStep (stepEq 1 (by rfl) ⟨50300, by rfl⟩ : syracuseStep 67067 = 100601) R100601
theorem R2095 : ∃ j : ℕ, syracuseStep^[j] 2095 = 1 := reachStep (stepEq 1 (by rfl) ⟨1571, by rfl⟩ : syracuseStep 2095 = 3143) R3143
theorem R2121 : ∃ j : ℕ, syracuseStep^[j] 2121 = 1 := reachStep (stepEq 2 (by rfl) ⟨795, by rfl⟩ : syracuseStep 2121 = 1591) R1591
theorem R2151 : ∃ j : ℕ, syracuseStep^[j] 2151 = 1 := reachStep (stepEq 1 (by rfl) ⟨1613, by rfl⟩ : syracuseStep 2151 = 3227) R3227
theorem R2185 : ∃ j : ℕ, syracuseStep^[j] 2185 = 1 := reachStep (stepEq 2 (by rfl) ⟨819, by rfl⟩ : syracuseStep 2185 = 1639) R1639
theorem R2289 : ∃ j : ℕ, syracuseStep^[j] 2289 = 1 := reachStep (stepEq 2 (by rfl) ⟨858, by rfl⟩ : syracuseStep 2289 = 1717) R1717
theorem R2293 : ∃ j : ℕ, syracuseStep^[j] 2293 = 1 := reachStep (stepEq 5 (by rfl) ⟨107, by rfl⟩ : syracuseStep 2293 = 215) R215
theorem R2305 : ∃ j : ℕ, syracuseStep^[j] 2305 = 1 := reachStep (stepEq 2 (by rfl) ⟨864, by rfl⟩ : syracuseStep 2305 = 1729) R1729
theorem R2313 : ∃ j : ℕ, syracuseStep^[j] 2313 = 1 := reachStep (stepEq 2 (by rfl) ⟨867, by rfl⟩ : syracuseStep 2313 = 1735) R1735
theorem R2315 : ∃ j : ℕ, syracuseStep^[j] 2315 = 1 := reachStep (stepEq 1 (by rfl) ⟨1736, by rfl⟩ : syracuseStep 2315 = 3473) R3473
theorem R2331 : ∃ j : ℕ, syracuseStep^[j] 2331 = 1 := reachStep (stepEq 1 (by rfl) ⟨1748, by rfl⟩ : syracuseStep 2331 = 3497) R3497
theorem R2347 : ∃ j : ℕ, syracuseStep^[j] 2347 = 1 := reachStep (stepEq 1 (by rfl) ⟨1760, by rfl⟩ : syracuseStep 2347 = 3521) R3521
theorem R35471 : ∃ j : ℕ, syracuseStep^[j] 35471 = 1 := reachStep (stepEq 1 (by rfl) ⟨26603, by rfl⟩ : syracuseStep 35471 = 53207) R53207
theorem R4191 : ∃ j : ℕ, syracuseStep^[j] 4191 = 1 := reachStep (stepEq 1 (by rfl) ⟨3143, by rfl⟩ : syracuseStep 4191 = 6287) R6287
theorem R4207 : ∃ j : ℕ, syracuseStep^[j] 4207 = 1 := reachStep (stepEq 1 (by rfl) ⟨3155, by rfl⟩ : syracuseStep 4207 = 6311) R6311
theorem R4241 : ∃ j : ℕ, syracuseStep^[j] 4241 = 1 := reachStep (stepEq 2 (by rfl) ⟨1590, by rfl⟩ : syracuseStep 4241 = 3181) R3181
theorem R4243 : ∃ j : ℕ, syracuseStep^[j] 4243 = 1 := reachStep (stepEq 1 (by rfl) ⟨3182, by rfl⟩ : syracuseStep 4243 = 6365) R6365
theorem R4303 : ∃ j : ℕ, syracuseStep^[j] 4303 = 1 := reachStep (stepEq 1 (by rfl) ⟨3227, by rfl⟩ : syracuseStep 4303 = 6455) R6455
theorem R4371 : ∃ j : ℕ, syracuseStep^[j] 4371 = 1 := reachStep (stepEq 1 (by rfl) ⟨3278, by rfl⟩ : syracuseStep 4371 = 6557) R6557
theorem R4565 : ∃ j : ℕ, syracuseStep^[j] 4565 = 1 := reachStep (stepEq 7 (by rfl) ⟨53, by rfl⟩ : syracuseStep 4565 = 107) R107
theorem R4579 : ∃ j : ℕ, syracuseStep^[j] 4579 = 1 := reachStep (stepEq 1 (by rfl) ⟨3434, by rfl⟩ : syracuseStep 4579 = 6869) R6869
theorem R4593 : ∃ j : ℕ, syracuseStep^[j] 4593 = 1 := reachStep (stepEq 2 (by rfl) ⟨1722, by rfl⟩ : syracuseStep 4593 = 3445) R3445
theorem R4611 : ∃ j : ℕ, syracuseStep^[j] 4611 = 1 := reachStep (stepEq 1 (by rfl) ⟨3458, by rfl⟩ : syracuseStep 4611 = 6917) R6917
theorem R4617 : ∃ j : ℕ, syracuseStep^[j] 4617 = 1 := reachStep (stepEq 2 (by rfl) ⟨1731, by rfl⟩ : syracuseStep 4617 = 3463) R3463
theorem R4627 : ∃ j : ℕ, syracuseStep^[j] 4627 = 1 := reachStep (stepEq 1 (by rfl) ⟨3470, by rfl⟩ : syracuseStep 4627 = 6941) R6941
theorem R4631 : ∃ j : ℕ, syracuseStep^[j] 4631 = 1 := reachStep (stepEq 1 (by rfl) ⟨3473, by rfl⟩ : syracuseStep 4631 = 6947) R6947
theorem R4633 : ∃ j : ℕ, syracuseStep^[j] 4633 = 1 := reachStep (stepEq 2 (by rfl) ⟨1737, by rfl⟩ : syracuseStep 4633 = 3475) R3475
theorem R4663 : ∃ j : ℕ, syracuseStep^[j] 4663 = 1 := reachStep (stepEq 1 (by rfl) ⟨3497, by rfl⟩ : syracuseStep 4663 = 6995) R6995
theorem R4695 : ∃ j : ℕ, syracuseStep^[j] 4695 = 1 := reachStep (stepEq 1 (by rfl) ⟨3521, by rfl⟩ : syracuseStep 4695 = 7043) R7043
theorem R4697 : ∃ j : ℕ, syracuseStep^[j] 4697 = 1 := reachStep (stepEq 2 (by rfl) ⟨1761, by rfl⟩ : syracuseStep 4697 = 3523) R3523
theorem R8381 : ∃ j : ℕ, syracuseStep^[j] 8381 = 1 := reachStep (stepEq 3 (by rfl) ⟨1571, by rfl⟩ : syracuseStep 8381 = 3143) R3143
theorem R8483 : ∃ j : ℕ, syracuseStep^[j] 8483 = 1 := reachStep (stepEq 1 (by rfl) ⟨6362, by rfl⟩ : syracuseStep 8483 = 12725) R12725
theorem R8491 : ∃ j : ℕ, syracuseStep^[j] 8491 = 1 := reachStep (stepEq 1 (by rfl) ⟨6368, by rfl⟩ : syracuseStep 8491 = 12737) R12737
theorem R8639 : ∃ j : ℕ, syracuseStep^[j] 8639 = 1 := reachStep (stepEq 1 (by rfl) ⟨6479, by rfl⟩ : syracuseStep 8639 = 12959) R12959
theorem R8687 : ∃ j : ℕ, syracuseStep^[j] 8687 = 1 := reachStep (stepEq 1 (by rfl) ⟨6515, by rfl⟩ : syracuseStep 8687 = 13031) R13031
theorem R8711 : ∃ j : ℕ, syracuseStep^[j] 8711 = 1 := reachStep (stepEq 1 (by rfl) ⟨6533, by rfl⟩ : syracuseStep 8711 = 13067) R13067
theorem R8741 : ∃ j : ℕ, syracuseStep^[j] 8741 = 1 := reachStep (stepEq 4 (by rfl) ⟨819, by rfl⟩ : syracuseStep 8741 = 1639) R1639
theorem R8743 : ∃ j : ℕ, syracuseStep^[j] 8743 = 1 := reachStep (stepEq 1 (by rfl) ⟨6557, by rfl⟩ : syracuseStep 8743 = 13115) R13115
theorem R2270045 : ∃ j : ℕ, syracuseStep^[j] 2270045 = 1 := reachStep (stepEq 3 (by rfl) ⟨425633, by rfl⟩ : syracuseStep 2270045 = 851267) R851267
theorem R9173 : ∃ j : ℕ, syracuseStep^[j] 9173 = 1 := reachStep (stepEq 7 (by rfl) ⟨107, by rfl⟩ : syracuseStep 9173 = 215) R215
theorem R9221 : ∃ j : ℕ, syracuseStep^[j] 9221 = 1 := reachStep (stepEq 4 (by rfl) ⟨864, by rfl⟩ : syracuseStep 9221 = 1729) R1729
theorem R9227 : ∃ j : ℕ, syracuseStep^[j] 9227 = 1 := reachStep (stepEq 1 (by rfl) ⟨6920, by rfl⟩ : syracuseStep 9227 = 13841) R13841
theorem R9325 : ∃ j : ℕ, syracuseStep^[j] 9325 = 1 := reachStep (stepEq 3 (by rfl) ⟨1748, by rfl⟩ : syracuseStep 9325 = 3497) R3497
theorem R9377 : ∃ j : ℕ, syracuseStep^[j] 9377 = 1 := reachStep (stepEq 2 (by rfl) ⟨3516, by rfl⟩ : syracuseStep 9377 = 7033) R7033
theorem R9383 : ∃ j : ℕ, syracuseStep^[j] 9383 = 1 := reachStep (stepEq 1 (by rfl) ⟨7037, by rfl⟩ : syracuseStep 9383 = 14075) R14075
theorem R9389 : ∃ j : ℕ, syracuseStep^[j] 9389 = 1 := reachStep (stepEq 3 (by rfl) ⟨1760, by rfl⟩ : syracuseStep 9389 = 3521) R3521
theorem R9395 : ∃ j : ℕ, syracuseStep^[j] 9395 = 1 := reachStep (stepEq 1 (by rfl) ⟨7046, by rfl⟩ : syracuseStep 9395 = 14093) R14093
theorem R9407 : ∃ j : ℕ, syracuseStep^[j] 9407 = 1 := reachStep (stepEq 1 (by rfl) ⟨7055, by rfl⟩ : syracuseStep 9407 = 14111) R14111
theorem R16973 : ∃ j : ℕ, syracuseStep^[j] 16973 = 1 := reachStep (stepEq 3 (by rfl) ⟨3182, by rfl⟩ : syracuseStep 16973 = 6365) R6365
theorem R17279 : ∃ j : ℕ, syracuseStep^[j] 17279 = 1 := reachStep (stepEq 1 (by rfl) ⟨12959, by rfl⟩ : syracuseStep 17279 = 25919) R25919
theorem R18215 : ∃ j : ℕ, syracuseStep^[j] 18215 = 1 := reachStep (stepEq 1 (by rfl) ⟨13661, by rfl⟩ : syracuseStep 18215 = 27323) R27323
theorem R18787 : ∃ j : ℕ, syracuseStep^[j] 18787 = 1 := reachStep (stepEq 1 (by rfl) ⟨14090, by rfl⟩ : syracuseStep 18787 = 28181) R28181
theorem R283763 : ∃ j : ℕ, syracuseStep^[j] 283763 = 1 := reachStep (stepEq 1 (by rfl) ⟨212822, by rfl⟩ : syracuseStep 283763 = 425645) R425645
theorem R1207943 : ∃ j : ℕ, syracuseStep^[j] 1207943 = 1 := reachStep (stepEq 1 (by rfl) ⟨905957, by rfl⟩ : syracuseStep 1207943 = 1811915) R1811915
theorem R47 : ∃ j : ℕ, syracuseStep^[j] 47 = 1 := reachStep (stepEq 1 (by rfl) ⟨35, by rfl⟩ : syracuseStep 47 = 71) R71
theorem R95 : ∃ j : ℕ, syracuseStep^[j] 95 = 1 := reachStep (stepEq 1 (by rfl) ⟨71, by rfl⟩ : syracuseStep 95 = 143) R143
theorem R189 : ∃ j : ℕ, syracuseStep^[j] 189 = 1 := reachStep (stepEq 3 (by rfl) ⟨35, by rfl⟩ : syracuseStep 189 = 71) R71
theorem R381 : ∃ j : ℕ, syracuseStep^[j] 381 = 1 := reachStep (stepEq 3 (by rfl) ⟨71, by rfl⟩ : syracuseStep 381 = 143) R143
theorem R757 : ∃ j : ℕ, syracuseStep^[j] 757 = 1 := reachStep (stepEq 5 (by rfl) ⟨35, by rfl⟩ : syracuseStep 757 = 71) R71
theorem R1521 : ∃ j : ℕ, syracuseStep^[j] 1521 = 1 := reachStep (stepEq 2 (by rfl) ⟨570, by rfl⟩ : syracuseStep 1521 = 1141) R1141
theorem R1525 : ∃ j : ℕ, syracuseStep^[j] 1525 = 1 := reachStep (stepEq 5 (by rfl) ⟨71, by rfl⟩ : syracuseStep 1525 = 143) R143
theorem R1543 : ∃ j : ℕ, syracuseStep^[j] 1543 = 1 := reachStep (stepEq 1 (by rfl) ⟨1157, by rfl⟩ : syracuseStep 1543 = 2315) R2315
theorem R2793 : ∃ j : ℕ, syracuseStep^[j] 2793 = 1 := reachStep (stepEq 2 (by rfl) ⟨1047, by rfl⟩ : syracuseStep 2793 = 2095) R2095
theorem R2827 : ∃ j : ℕ, syracuseStep^[j] 2827 = 1 := reachStep (stepEq 1 (by rfl) ⟨2120, by rfl⟩ : syracuseStep 2827 = 4241) R4241
theorem R2913 : ∃ j : ℕ, syracuseStep^[j] 2913 = 1 := reachStep (stepEq 2 (by rfl) ⟨1092, by rfl⟩ : syracuseStep 2913 = 2185) R2185
theorem R3029 : ∃ j : ℕ, syracuseStep^[j] 3029 = 1 := reachStep (stepEq 7 (by rfl) ⟨35, by rfl⟩ : syracuseStep 3029 = 71) R71
theorem R3043 : ∃ j : ℕ, syracuseStep^[j] 3043 = 1 := reachStep (stepEq 1 (by rfl) ⟨2282, by rfl⟩ : syracuseStep 3043 = 4565) R4565
theorem R3057 : ∃ j : ℕ, syracuseStep^[j] 3057 = 1 := reachStep (stepEq 2 (by rfl) ⟨1146, by rfl⟩ : syracuseStep 3057 = 2293) R2293
theorem R3073 : ∃ j : ℕ, syracuseStep^[j] 3073 = 1 := reachStep (stepEq 2 (by rfl) ⟨1152, by rfl⟩ : syracuseStep 3073 = 2305) R2305
theorem R3087 : ∃ j : ℕ, syracuseStep^[j] 3087 = 1 := reachStep (stepEq 1 (by rfl) ⟨2315, by rfl⟩ : syracuseStep 3087 = 4631) R4631
theorem R3129 : ∃ j : ℕ, syracuseStep^[j] 3129 = 1 := reachStep (stepEq 2 (by rfl) ⟨1173, by rfl⟩ : syracuseStep 3129 = 2347) R2347
theorem R3131 : ∃ j : ℕ, syracuseStep^[j] 3131 = 1 := reachStep (stepEq 1 (by rfl) ⟨2348, by rfl⟩ : syracuseStep 3131 = 4697) R4697
theorem R5587 : ∃ j : ℕ, syracuseStep^[j] 5587 = 1 := reachStep (stepEq 1 (by rfl) ⟨4190, by rfl⟩ : syracuseStep 5587 = 8381) R8381
theorem R5609 : ∃ j : ℕ, syracuseStep^[j] 5609 = 1 := reachStep (stepEq 2 (by rfl) ⟨2103, by rfl⟩ : syracuseStep 5609 = 4207) R4207
theorem R5655 : ∃ j : ℕ, syracuseStep^[j] 5655 = 1 := reachStep (stepEq 1 (by rfl) ⟨4241, by rfl⟩ : syracuseStep 5655 = 8483) R8483
theorem R5657 : ∃ j : ℕ, syracuseStep^[j] 5657 = 1 := reachStep (stepEq 2 (by rfl) ⟨2121, by rfl⟩ : syracuseStep 5657 = 4243) R4243
theorem R5737 : ∃ j : ℕ, syracuseStep^[j] 5737 = 1 := reachStep (stepEq 2 (by rfl) ⟨2151, by rfl⟩ : syracuseStep 5737 = 4303) R4303
theorem R5759 : ∃ j : ℕ, syracuseStep^[j] 5759 = 1 := reachStep (stepEq 1 (by rfl) ⟨4319, by rfl⟩ : syracuseStep 5759 = 8639) R8639
theorem R5791 : ∃ j : ℕ, syracuseStep^[j] 5791 = 1 := reachStep (stepEq 1 (by rfl) ⟨4343, by rfl⟩ : syracuseStep 5791 = 8687) R8687
theorem R5807 : ∃ j : ℕ, syracuseStep^[j] 5807 = 1 := reachStep (stepEq 1 (by rfl) ⟨4355, by rfl⟩ : syracuseStep 5807 = 8711) R8711
theorem R5827 : ∃ j : ℕ, syracuseStep^[j] 5827 = 1 := reachStep (stepEq 1 (by rfl) ⟨4370, by rfl⟩ : syracuseStep 5827 = 8741) R8741
theorem R1513363 : ∃ j : ℕ, syracuseStep^[j] 1513363 = 1 := reachStep (stepEq 1 (by rfl) ⟨1135022, by rfl⟩ : syracuseStep 1513363 = 2270045) R2270045
theorem R6085 : ∃ j : ℕ, syracuseStep^[j] 6085 = 1 := reachStep (stepEq 4 (by rfl) ⟨570, by rfl⟩ : syracuseStep 6085 = 1141) R1141
theorem R6101 : ∃ j : ℕ, syracuseStep^[j] 6101 = 1 := reachStep (stepEq 7 (by rfl) ⟨71, by rfl⟩ : syracuseStep 6101 = 143) R143
theorem R6105 : ∃ j : ℕ, syracuseStep^[j] 6105 = 1 := reachStep (stepEq 2 (by rfl) ⟨2289, by rfl⟩ : syracuseStep 6105 = 4579) R4579
theorem R6115 : ∃ j : ℕ, syracuseStep^[j] 6115 = 1 := reachStep (stepEq 1 (by rfl) ⟨4586, by rfl⟩ : syracuseStep 6115 = 9173) R9173
theorem R6147 : ∃ j : ℕ, syracuseStep^[j] 6147 = 1 := reachStep (stepEq 1 (by rfl) ⟨4610, by rfl⟩ : syracuseStep 6147 = 9221) R9221
theorem R6151 : ∃ j : ℕ, syracuseStep^[j] 6151 = 1 := reachStep (stepEq 1 (by rfl) ⟨4613, by rfl⟩ : syracuseStep 6151 = 9227) R9227
theorem R6169 : ∃ j : ℕ, syracuseStep^[j] 6169 = 1 := reachStep (stepEq 2 (by rfl) ⟨2313, by rfl⟩ : syracuseStep 6169 = 4627) R4627
theorem R6173 : ∃ j : ℕ, syracuseStep^[j] 6173 = 1 := reachStep (stepEq 3 (by rfl) ⟨1157, by rfl⟩ : syracuseStep 6173 = 2315) R2315
theorem R6177 : ∃ j : ℕ, syracuseStep^[j] 6177 = 1 := reachStep (stepEq 2 (by rfl) ⟨2316, by rfl⟩ : syracuseStep 6177 = 4633) R4633
theorem R6217 : ∃ j : ℕ, syracuseStep^[j] 6217 = 1 := reachStep (stepEq 2 (by rfl) ⟨2331, by rfl⟩ : syracuseStep 6217 = 4663) R4663
theorem R6251 : ∃ j : ℕ, syracuseStep^[j] 6251 = 1 := reachStep (stepEq 1 (by rfl) ⟨4688, by rfl⟩ : syracuseStep 6251 = 9377) R9377
theorem R6255 : ∃ j : ℕ, syracuseStep^[j] 6255 = 1 := reachStep (stepEq 1 (by rfl) ⟨4691, by rfl⟩ : syracuseStep 6255 = 9383) R9383
theorem R6259 : ∃ j : ℕ, syracuseStep^[j] 6259 = 1 := reachStep (stepEq 1 (by rfl) ⟨4694, by rfl⟩ : syracuseStep 6259 = 9389) R9389
theorem R6263 : ∃ j : ℕ, syracuseStep^[j] 6263 = 1 := reachStep (stepEq 1 (by rfl) ⟨4697, by rfl⟩ : syracuseStep 6263 = 9395) R9395
theorem R6271 : ∃ j : ℕ, syracuseStep^[j] 6271 = 1 := reachStep (stepEq 1 (by rfl) ⟨4703, by rfl⟩ : syracuseStep 6271 = 9407) R9407
theorem R11315 : ∃ j : ℕ, syracuseStep^[j] 11315 = 1 := reachStep (stepEq 1 (by rfl) ⟨8486, by rfl⟩ : syracuseStep 11315 = 16973) R16973
theorem R11321 : ∃ j : ℕ, syracuseStep^[j] 11321 = 1 := reachStep (stepEq 2 (by rfl) ⟨4245, by rfl⟩ : syracuseStep 11321 = 8491) R8491
theorem R11519 : ∃ j : ℕ, syracuseStep^[j] 11519 = 1 := reachStep (stepEq 1 (by rfl) ⟨8639, by rfl⟩ : syracuseStep 11519 = 17279) R17279
theorem R11657 : ∃ j : ℕ, syracuseStep^[j] 11657 = 1 := reachStep (stepEq 2 (by rfl) ⟨4371, by rfl⟩ : syracuseStep 11657 = 8743) R8743
theorem R44711 : ∃ j : ℕ, syracuseStep^[j] 44711 = 1 := reachStep (stepEq 1 (by rfl) ⟨33533, by rfl⟩ : syracuseStep 44711 = 67067) R67067
theorem R12143 : ∃ j : ℕ, syracuseStep^[j] 12143 = 1 := reachStep (stepEq 1 (by rfl) ⟨9107, by rfl⟩ : syracuseStep 12143 = 18215) R18215
theorem R12293 : ∃ j : ℕ, syracuseStep^[j] 12293 = 1 := reachStep (stepEq 4 (by rfl) ⟨1152, by rfl⟩ : syracuseStep 12293 = 2305) R2305
theorem R12433 : ∃ j : ℕ, syracuseStep^[j] 12433 = 1 := reachStep (stepEq 2 (by rfl) ⟨4662, by rfl⟩ : syracuseStep 12433 = 9325) R9325
theorem R805295 : ∃ j : ℕ, syracuseStep^[j] 805295 = 1 := reachStep (stepEq 1 (by rfl) ⟨603971, by rfl⟩ : syracuseStep 805295 = 1207943) R1207943
theorem R22349 : ∃ j : ℕ, syracuseStep^[j] 22349 = 1 := reachStep (stepEq 3 (by rfl) ⟨4190, by rfl⟩ : syracuseStep 22349 = 8381) R8381
theorem R22949 : ∃ j : ℕ, syracuseStep^[j] 22949 = 1 := reachStep (stepEq 4 (by rfl) ⟨2151, by rfl⟩ : syracuseStep 22949 = 4303) R4303
theorem R23165 : ∃ j : ℕ, syracuseStep^[j] 23165 = 1 := reachStep (stepEq 3 (by rfl) ⟨4343, by rfl⟩ : syracuseStep 23165 = 8687) R8687
theorem R23647 : ∃ j : ℕ, syracuseStep^[j] 23647 = 1 := reachStep (stepEq 1 (by rfl) ⟨17735, by rfl⟩ : syracuseStep 23647 = 35471) R35471
theorem R24421 : ∃ j : ℕ, syracuseStep^[j] 24421 = 1 := reachStep (stepEq 4 (by rfl) ⟨2289, by rfl⟩ : syracuseStep 24421 = 4579) R4579
theorem R24461 : ∃ j : ℕ, syracuseStep^[j] 24461 = 1 := reachStep (stepEq 3 (by rfl) ⟨4586, by rfl⟩ : syracuseStep 24461 = 9173) R9173
theorem R25049 : ∃ j : ℕ, syracuseStep^[j] 25049 = 1 := reachStep (stepEq 2 (by rfl) ⟨9393, by rfl⟩ : syracuseStep 25049 = 18787) R18787
theorem R189175 : ∃ j : ℕ, syracuseStep^[j] 189175 = 1 := reachStep (stepEq 1 (by rfl) ⟨141881, by rfl⟩ : syracuseStep 189175 = 283763) R283763
theorem R31 : ∃ j : ℕ, syracuseStep^[j] 31 = 1 := reachStep (stepEq 1 (by rfl) ⟨23, by rfl⟩ : syracuseStep 31 = 47) R47
theorem R63 : ∃ j : ℕ, syracuseStep^[j] 63 = 1 := reachStep (stepEq 1 (by rfl) ⟨47, by rfl⟩ : syracuseStep 63 = 95) R95
theorem R125 : ∃ j : ℕ, syracuseStep^[j] 125 = 1 := reachStep (stepEq 3 (by rfl) ⟨23, by rfl⟩ : syracuseStep 125 = 47) R47
theorem R253 : ∃ j : ℕ, syracuseStep^[j] 253 = 1 := reachStep (stepEq 3 (by rfl) ⟨47, by rfl⟩ : syracuseStep 253 = 95) R95
theorem R501 : ∃ j : ℕ, syracuseStep^[j] 501 = 1 := reachStep (stepEq 5 (by rfl) ⟨23, by rfl⟩ : syracuseStep 501 = 47) R47
theorem R1009 : ∃ j : ℕ, syracuseStep^[j] 1009 = 1 := reachStep (stepEq 2 (by rfl) ⟨378, by rfl⟩ : syracuseStep 1009 = 757) R757
theorem R1013 : ∃ j : ℕ, syracuseStep^[j] 1013 = 1 := reachStep (stepEq 5 (by rfl) ⟨47, by rfl⟩ : syracuseStep 1013 = 95) R95
theorem R2005 : ∃ j : ℕ, syracuseStep^[j] 2005 = 1 := reachStep (stepEq 7 (by rfl) ⟨23, by rfl⟩ : syracuseStep 2005 = 47) R47
theorem R2019 : ∃ j : ℕ, syracuseStep^[j] 2019 = 1 := reachStep (stepEq 1 (by rfl) ⟨1514, by rfl⟩ : syracuseStep 2019 = 3029) R3029
theorem R2033 : ∃ j : ℕ, syracuseStep^[j] 2033 = 1 := reachStep (stepEq 2 (by rfl) ⟨762, by rfl⟩ : syracuseStep 2033 = 1525) R1525
theorem R2057 : ∃ j : ℕ, syracuseStep^[j] 2057 = 1 := reachStep (stepEq 2 (by rfl) ⟨771, by rfl⟩ : syracuseStep 2057 = 1543) R1543
theorem R2087 : ∃ j : ℕ, syracuseStep^[j] 2087 = 1 := reachStep (stepEq 1 (by rfl) ⟨1565, by rfl⟩ : syracuseStep 2087 = 3131) R3131
theorem R3739 : ∃ j : ℕ, syracuseStep^[j] 3739 = 1 := reachStep (stepEq 1 (by rfl) ⟨2804, by rfl⟩ : syracuseStep 3739 = 5609) R5609
theorem R3769 : ∃ j : ℕ, syracuseStep^[j] 3769 = 1 := reachStep (stepEq 2 (by rfl) ⟨1413, by rfl⟩ : syracuseStep 3769 = 2827) R2827
theorem R3771 : ∃ j : ℕ, syracuseStep^[j] 3771 = 1 := reachStep (stepEq 1 (by rfl) ⟨2828, by rfl⟩ : syracuseStep 3771 = 5657) R5657
theorem R3839 : ∃ j : ℕ, syracuseStep^[j] 3839 = 1 := reachStep (stepEq 1 (by rfl) ⟨2879, by rfl⟩ : syracuseStep 3839 = 5759) R5759
theorem R3871 : ∃ j : ℕ, syracuseStep^[j] 3871 = 1 := reachStep (stepEq 1 (by rfl) ⟨2903, by rfl⟩ : syracuseStep 3871 = 5807) R5807
theorem R4037 : ∃ j : ℕ, syracuseStep^[j] 4037 = 1 := reachStep (stepEq 4 (by rfl) ⟨378, by rfl⟩ : syracuseStep 4037 = 757) R757
theorem R4053 : ∃ j : ℕ, syracuseStep^[j] 4053 = 1 := reachStep (stepEq 7 (by rfl) ⟨47, by rfl⟩ : syracuseStep 4053 = 95) R95
theorem R4057 : ∃ j : ℕ, syracuseStep^[j] 4057 = 1 := reachStep (stepEq 2 (by rfl) ⟨1521, by rfl⟩ : syracuseStep 4057 = 3043) R3043
theorem R4067 : ∃ j : ℕ, syracuseStep^[j] 4067 = 1 := reachStep (stepEq 1 (by rfl) ⟨3050, by rfl⟩ : syracuseStep 4067 = 6101) R6101
theorem R4097 : ∃ j : ℕ, syracuseStep^[j] 4097 = 1 := reachStep (stepEq 2 (by rfl) ⟨1536, by rfl⟩ : syracuseStep 4097 = 3073) R3073
theorem R4115 : ∃ j : ℕ, syracuseStep^[j] 4115 = 1 := reachStep (stepEq 1 (by rfl) ⟨3086, by rfl⟩ : syracuseStep 4115 = 6173) R6173
theorem R4167 : ∃ j : ℕ, syracuseStep^[j] 4167 = 1 := reachStep (stepEq 1 (by rfl) ⟨3125, by rfl⟩ : syracuseStep 4167 = 6251) R6251
theorem R4175 : ∃ j : ℕ, syracuseStep^[j] 4175 = 1 := reachStep (stepEq 1 (by rfl) ⟨3131, by rfl⟩ : syracuseStep 4175 = 6263) R6263
theorem R7543 : ∃ j : ℕ, syracuseStep^[j] 7543 = 1 := reachStep (stepEq 1 (by rfl) ⟨5657, by rfl⟩ : syracuseStep 7543 = 11315) R11315
theorem R7547 : ∃ j : ℕ, syracuseStep^[j] 7547 = 1 := reachStep (stepEq 1 (by rfl) ⟨5660, by rfl⟩ : syracuseStep 7547 = 11321) R11321
theorem R7649 : ∃ j : ℕ, syracuseStep^[j] 7649 = 1 := reachStep (stepEq 2 (by rfl) ⟨2868, by rfl⟩ : syracuseStep 7649 = 5737) R5737
theorem R7679 : ∃ j : ℕ, syracuseStep^[j] 7679 = 1 := reachStep (stepEq 1 (by rfl) ⟨5759, by rfl⟩ : syracuseStep 7679 = 11519) R11519
theorem R7721 : ∃ j : ℕ, syracuseStep^[j] 7721 = 1 := reachStep (stepEq 2 (by rfl) ⟨2895, by rfl⟩ : syracuseStep 7721 = 5791) R5791
theorem R7769 : ∃ j : ℕ, syracuseStep^[j] 7769 = 1 := reachStep (stepEq 2 (by rfl) ⟨2913, by rfl⟩ : syracuseStep 7769 = 5827) R5827
theorem R7771 : ∃ j : ℕ, syracuseStep^[j] 7771 = 1 := reachStep (stepEq 1 (by rfl) ⟨5828, by rfl⟩ : syracuseStep 7771 = 11657) R11657
theorem R8021 : ∃ j : ℕ, syracuseStep^[j] 8021 = 1 := reachStep (stepEq 9 (by rfl) ⟨23, by rfl⟩ : syracuseStep 8021 = 47) R47
theorem R8095 : ∃ j : ℕ, syracuseStep^[j] 8095 = 1 := reachStep (stepEq 1 (by rfl) ⟨6071, by rfl⟩ : syracuseStep 8095 = 12143) R12143
theorem R8113 : ∃ j : ℕ, syracuseStep^[j] 8113 = 1 := reachStep (stepEq 2 (by rfl) ⟨3042, by rfl⟩ : syracuseStep 8113 = 6085) R6085
theorem R8153 : ∃ j : ℕ, syracuseStep^[j] 8153 = 1 := reachStep (stepEq 2 (by rfl) ⟨3057, by rfl⟩ : syracuseStep 8153 = 6115) R6115
theorem R8195 : ∃ j : ℕ, syracuseStep^[j] 8195 = 1 := reachStep (stepEq 1 (by rfl) ⟨6146, by rfl⟩ : syracuseStep 8195 = 12293) R12293
theorem R8201 : ∃ j : ℕ, syracuseStep^[j] 8201 = 1 := reachStep (stepEq 2 (by rfl) ⟨3075, by rfl⟩ : syracuseStep 8201 = 6151) R6151
theorem R8225 : ∃ j : ℕ, syracuseStep^[j] 8225 = 1 := reachStep (stepEq 2 (by rfl) ⟨3084, by rfl⟩ : syracuseStep 8225 = 6169) R6169
theorem R8345 : ∃ j : ℕ, syracuseStep^[j] 8345 = 1 := reachStep (stepEq 2 (by rfl) ⟨3129, by rfl⟩ : syracuseStep 8345 = 6259) R6259
theorem R536863 : ∃ j : ℕ, syracuseStep^[j] 536863 = 1 := reachStep (stepEq 1 (by rfl) ⟨402647, by rfl⟩ : syracuseStep 536863 = 805295) R805295
theorem R14899 : ∃ j : ℕ, syracuseStep^[j] 14899 = 1 := reachStep (stepEq 1 (by rfl) ⟨11174, by rfl⟩ : syracuseStep 14899 = 22349) R22349
theorem R14957 : ∃ j : ℕ, syracuseStep^[j] 14957 = 1 := reachStep (stepEq 3 (by rfl) ⟨2804, by rfl⟩ : syracuseStep 14957 = 5609) R5609
theorem R15299 : ∃ j : ℕ, syracuseStep^[j] 15299 = 1 := reachStep (stepEq 1 (by rfl) ⟨11474, by rfl⟩ : syracuseStep 15299 = 22949) R22949
theorem R15443 : ∃ j : ℕ, syracuseStep^[j] 15443 = 1 := reachStep (stepEq 1 (by rfl) ⟨11582, by rfl⟩ : syracuseStep 15443 = 23165) R23165
theorem R16213 : ∃ j : ℕ, syracuseStep^[j] 16213 = 1 := reachStep (stepEq 9 (by rfl) ⟨47, by rfl⟩ : syracuseStep 16213 = 95) R95
theorem R16307 : ∃ j : ℕ, syracuseStep^[j] 16307 = 1 := reachStep (stepEq 1 (by rfl) ⟨12230, by rfl⟩ : syracuseStep 16307 = 24461) R24461
theorem R16577 : ∃ j : ℕ, syracuseStep^[j] 16577 = 1 := reachStep (stepEq 2 (by rfl) ⟨6216, by rfl⟩ : syracuseStep 16577 = 12433) R12433
theorem R16699 : ∃ j : ℕ, syracuseStep^[j] 16699 = 1 := reachStep (stepEq 1 (by rfl) ⟨12524, by rfl⟩ : syracuseStep 16699 = 25049) R25049
theorem R2017817 : ∃ j : ℕ, syracuseStep^[j] 2017817 = 1 := reachStep (stepEq 2 (by rfl) ⟨756681, by rfl⟩ : syracuseStep 2017817 = 1513363) R1513363
theorem R252233 : ∃ j : ℕ, syracuseStep^[j] 252233 = 1 := reachStep (stepEq 2 (by rfl) ⟨94587, by rfl⟩ : syracuseStep 252233 = 189175) R189175
theorem R29807 : ∃ j : ℕ, syracuseStep^[j] 29807 = 1 := reachStep (stepEq 1 (by rfl) ⟨22355, by rfl⟩ : syracuseStep 29807 = 44711) R44711
theorem R31529 : ∃ j : ℕ, syracuseStep^[j] 31529 = 1 := reachStep (stepEq 2 (by rfl) ⟨11823, by rfl⟩ : syracuseStep 31529 = 23647) R23647
theorem R32561 : ∃ j : ℕ, syracuseStep^[j] 32561 = 1 := reachStep (stepEq 2 (by rfl) ⟨12210, by rfl⟩ : syracuseStep 32561 = 24421) R24421
theorem R41 : ∃ j : ℕ, syracuseStep^[j] 41 = 1 := reachStep (stepEq 2 (by rfl) ⟨15, by rfl⟩ : syracuseStep 41 = 31) R31
theorem R83 : ∃ j : ℕ, syracuseStep^[j] 83 = 1 := reachStep (stepEq 1 (by rfl) ⟨62, by rfl⟩ : syracuseStep 83 = 125) R125
theorem R165 : ∃ j : ℕ, syracuseStep^[j] 165 = 1 := reachStep (stepEq 4 (by rfl) ⟨15, by rfl⟩ : syracuseStep 165 = 31) R31
theorem R333 : ∃ j : ℕ, syracuseStep^[j] 333 = 1 := reachStep (stepEq 3 (by rfl) ⟨62, by rfl⟩ : syracuseStep 333 = 125) R125
theorem R337 : ∃ j : ℕ, syracuseStep^[j] 337 = 1 := reachStep (stepEq 2 (by rfl) ⟨126, by rfl⟩ : syracuseStep 337 = 253) R253
theorem R661 : ∃ j : ℕ, syracuseStep^[j] 661 = 1 := reachStep (stepEq 6 (by rfl) ⟨15, by rfl⟩ : syracuseStep 661 = 31) R31
theorem R675 : ∃ j : ℕ, syracuseStep^[j] 675 = 1 := reachStep (stepEq 1 (by rfl) ⟨506, by rfl⟩ : syracuseStep 675 = 1013) R1013
theorem R1333 : ∃ j : ℕ, syracuseStep^[j] 1333 = 1 := reachStep (stepEq 5 (by rfl) ⟨62, by rfl⟩ : syracuseStep 1333 = 125) R125
theorem R1345 : ∃ j : ℕ, syracuseStep^[j] 1345 = 1 := reachStep (stepEq 2 (by rfl) ⟨504, by rfl⟩ : syracuseStep 1345 = 1009) R1009
theorem R1349 : ∃ j : ℕ, syracuseStep^[j] 1349 = 1 := reachStep (stepEq 4 (by rfl) ⟨126, by rfl⟩ : syracuseStep 1349 = 253) R253
theorem R1355 : ∃ j : ℕ, syracuseStep^[j] 1355 = 1 := reachStep (stepEq 1 (by rfl) ⟨1016, by rfl⟩ : syracuseStep 1355 = 2033) R2033
theorem R1371 : ∃ j : ℕ, syracuseStep^[j] 1371 = 1 := reachStep (stepEq 1 (by rfl) ⟨1028, by rfl⟩ : syracuseStep 1371 = 2057) R2057
theorem R1391 : ∃ j : ℕ, syracuseStep^[j] 1391 = 1 := reachStep (stepEq 1 (by rfl) ⟨1043, by rfl⟩ : syracuseStep 1391 = 2087) R2087
theorem R1345211 : ∃ j : ℕ, syracuseStep^[j] 1345211 = 1 := reachStep (stepEq 1 (by rfl) ⟨1008908, by rfl⟩ : syracuseStep 1345211 = 2017817) R2017817
theorem R2559 : ∃ j : ℕ, syracuseStep^[j] 2559 = 1 := reachStep (stepEq 1 (by rfl) ⟨1919, by rfl⟩ : syracuseStep 2559 = 3839) R3839
theorem R2645 : ∃ j : ℕ, syracuseStep^[j] 2645 = 1 := reachStep (stepEq 8 (by rfl) ⟨15, by rfl⟩ : syracuseStep 2645 = 31) R31
theorem R2673 : ∃ j : ℕ, syracuseStep^[j] 2673 = 1 := reachStep (stepEq 2 (by rfl) ⟨1002, by rfl⟩ : syracuseStep 2673 = 2005) R2005
theorem R2691 : ∃ j : ℕ, syracuseStep^[j] 2691 = 1 := reachStep (stepEq 1 (by rfl) ⟨2018, by rfl⟩ : syracuseStep 2691 = 4037) R4037
theorem R2701 : ∃ j : ℕ, syracuseStep^[j] 2701 = 1 := reachStep (stepEq 3 (by rfl) ⟨506, by rfl⟩ : syracuseStep 2701 = 1013) R1013
theorem R2711 : ∃ j : ℕ, syracuseStep^[j] 2711 = 1 := reachStep (stepEq 1 (by rfl) ⟨2033, by rfl⟩ : syracuseStep 2711 = 4067) R4067
theorem R2731 : ∃ j : ℕ, syracuseStep^[j] 2731 = 1 := reachStep (stepEq 1 (by rfl) ⟨2048, by rfl⟩ : syracuseStep 2731 = 4097) R4097
theorem R2743 : ∃ j : ℕ, syracuseStep^[j] 2743 = 1 := reachStep (stepEq 1 (by rfl) ⟨2057, by rfl⟩ : syracuseStep 2743 = 4115) R4115
theorem R2783 : ∃ j : ℕ, syracuseStep^[j] 2783 = 1 := reachStep (stepEq 1 (by rfl) ⟨2087, by rfl⟩ : syracuseStep 2783 = 4175) R4175
theorem R168155 : ∃ j : ℕ, syracuseStep^[j] 168155 = 1 := reachStep (stepEq 1 (by rfl) ⟨126116, by rfl⟩ : syracuseStep 168155 = 252233) R252233
theorem R4985 : ∃ j : ℕ, syracuseStep^[j] 4985 = 1 := reachStep (stepEq 2 (by rfl) ⟨1869, by rfl⟩ : syracuseStep 4985 = 3739) R3739
theorem R5025 : ∃ j : ℕ, syracuseStep^[j] 5025 = 1 := reachStep (stepEq 2 (by rfl) ⟨1884, by rfl⟩ : syracuseStep 5025 = 3769) R3769
theorem R5031 : ∃ j : ℕ, syracuseStep^[j] 5031 = 1 := reachStep (stepEq 1 (by rfl) ⟨3773, by rfl⟩ : syracuseStep 5031 = 7547) R7547
theorem R5099 : ∃ j : ℕ, syracuseStep^[j] 5099 = 1 := reachStep (stepEq 1 (by rfl) ⟨3824, by rfl⟩ : syracuseStep 5099 = 7649) R7649
theorem R5119 : ∃ j : ℕ, syracuseStep^[j] 5119 = 1 := reachStep (stepEq 1 (by rfl) ⟨3839, by rfl⟩ : syracuseStep 5119 = 7679) R7679
theorem R5147 : ∃ j : ℕ, syracuseStep^[j] 5147 = 1 := reachStep (stepEq 1 (by rfl) ⟨3860, by rfl⟩ : syracuseStep 5147 = 7721) R7721
theorem R5161 : ∃ j : ℕ, syracuseStep^[j] 5161 = 1 := reachStep (stepEq 2 (by rfl) ⟨1935, by rfl⟩ : syracuseStep 5161 = 3871) R3871
theorem R5179 : ∃ j : ℕ, syracuseStep^[j] 5179 = 1 := reachStep (stepEq 1 (by rfl) ⟨3884, by rfl⟩ : syracuseStep 5179 = 7769) R7769
theorem R5333 : ∃ j : ℕ, syracuseStep^[j] 5333 = 1 := reachStep (stepEq 7 (by rfl) ⟨62, by rfl⟩ : syracuseStep 5333 = 125) R125
theorem R5347 : ∃ j : ℕ, syracuseStep^[j] 5347 = 1 := reachStep (stepEq 1 (by rfl) ⟨4010, by rfl⟩ : syracuseStep 5347 = 8021) R8021
theorem R5381 : ∃ j : ℕ, syracuseStep^[j] 5381 = 1 := reachStep (stepEq 4 (by rfl) ⟨504, by rfl⟩ : syracuseStep 5381 = 1009) R1009
theorem R5397 : ∃ j : ℕ, syracuseStep^[j] 5397 = 1 := reachStep (stepEq 6 (by rfl) ⟨126, by rfl⟩ : syracuseStep 5397 = 253) R253
theorem R5409 : ∃ j : ℕ, syracuseStep^[j] 5409 = 1 := reachStep (stepEq 2 (by rfl) ⟨2028, by rfl⟩ : syracuseStep 5409 = 4057) R4057
theorem R5421 : ∃ j : ℕ, syracuseStep^[j] 5421 = 1 := reachStep (stepEq 3 (by rfl) ⟨1016, by rfl⟩ : syracuseStep 5421 = 2033) R2033
theorem R5435 : ∃ j : ℕ, syracuseStep^[j] 5435 = 1 := reachStep (stepEq 1 (by rfl) ⟨4076, by rfl⟩ : syracuseStep 5435 = 8153) R8153
theorem R5463 : ∃ j : ℕ, syracuseStep^[j] 5463 = 1 := reachStep (stepEq 1 (by rfl) ⟨4097, by rfl⟩ : syracuseStep 5463 = 8195) R8195
theorem R5467 : ∃ j : ℕ, syracuseStep^[j] 5467 = 1 := reachStep (stepEq 1 (by rfl) ⟨4100, by rfl⟩ : syracuseStep 5467 = 8201) R8201
theorem R5483 : ∃ j : ℕ, syracuseStep^[j] 5483 = 1 := reachStep (stepEq 1 (by rfl) ⟨4112, by rfl⟩ : syracuseStep 5483 = 8225) R8225
theorem R5485 : ∃ j : ℕ, syracuseStep^[j] 5485 = 1 := reachStep (stepEq 3 (by rfl) ⟨1028, by rfl⟩ : syracuseStep 5485 = 2057) R2057
theorem R5563 : ∃ j : ℕ, syracuseStep^[j] 5563 = 1 := reachStep (stepEq 1 (by rfl) ⟨4172, by rfl⟩ : syracuseStep 5563 = 8345) R8345
theorem R5565 : ∃ j : ℕ, syracuseStep^[j] 5565 = 1 := reachStep (stepEq 3 (by rfl) ⟨1043, by rfl⟩ : syracuseStep 5565 = 2087) R2087
theorem R9971 : ∃ j : ℕ, syracuseStep^[j] 9971 = 1 := reachStep (stepEq 1 (by rfl) ⟨7478, by rfl⟩ : syracuseStep 9971 = 14957) R14957
theorem R10057 : ∃ j : ℕ, syracuseStep^[j] 10057 = 1 := reachStep (stepEq 2 (by rfl) ⟨3771, by rfl⟩ : syracuseStep 10057 = 7543) R7543
theorem R10199 : ∃ j : ℕ, syracuseStep^[j] 10199 = 1 := reachStep (stepEq 1 (by rfl) ⟨7649, by rfl⟩ : syracuseStep 10199 = 15299) R15299
theorem R10295 : ∃ j : ℕ, syracuseStep^[j] 10295 = 1 := reachStep (stepEq 1 (by rfl) ⟨7721, by rfl⟩ : syracuseStep 10295 = 15443) R15443
theorem R10361 : ∃ j : ℕ, syracuseStep^[j] 10361 = 1 := reachStep (stepEq 2 (by rfl) ⟨3885, by rfl⟩ : syracuseStep 10361 = 7771) R7771
theorem R10793 : ∃ j : ℕ, syracuseStep^[j] 10793 = 1 := reachStep (stepEq 2 (by rfl) ⟨4047, by rfl⟩ : syracuseStep 10793 = 8095) R8095
theorem R10817 : ∃ j : ℕ, syracuseStep^[j] 10817 = 1 := reachStep (stepEq 2 (by rfl) ⟨4056, by rfl⟩ : syracuseStep 10817 = 8113) R8113
theorem R10871 : ∃ j : ℕ, syracuseStep^[j] 10871 = 1 := reachStep (stepEq 1 (by rfl) ⟨8153, by rfl⟩ : syracuseStep 10871 = 16307) R16307
theorem R10925 : ∃ j : ℕ, syracuseStep^[j] 10925 = 1 := reachStep (stepEq 3 (by rfl) ⟨2048, by rfl⟩ : syracuseStep 10925 = 4097) R4097
theorem R11051 : ∃ j : ℕ, syracuseStep^[j] 11051 = 1 := reachStep (stepEq 1 (by rfl) ⟨8288, by rfl⟩ : syracuseStep 11051 = 16577) R16577
theorem R19865 : ∃ j : ℕ, syracuseStep^[j] 19865 = 1 := reachStep (stepEq 2 (by rfl) ⟨7449, by rfl⟩ : syracuseStep 19865 = 14899) R14899
theorem R19871 : ∃ j : ℕ, syracuseStep^[j] 19871 = 1 := reachStep (stepEq 1 (by rfl) ⟨14903, by rfl⟩ : syracuseStep 19871 = 29807) R29807
theorem R21019 : ∃ j : ℕ, syracuseStep^[j] 21019 = 1 := reachStep (stepEq 1 (by rfl) ⟨15764, by rfl⟩ : syracuseStep 21019 = 31529) R31529
theorem R21617 : ∃ j : ℕ, syracuseStep^[j] 21617 = 1 := reachStep (stepEq 2 (by rfl) ⟨8106, by rfl⟩ : syracuseStep 21617 = 16213) R16213
theorem R21707 : ∃ j : ℕ, syracuseStep^[j] 21707 = 1 := reachStep (stepEq 1 (by rfl) ⟨16280, by rfl⟩ : syracuseStep 21707 = 32561) R32561
theorem R21869 : ∃ j : ℕ, syracuseStep^[j] 21869 = 1 := reachStep (stepEq 3 (by rfl) ⟨4100, by rfl⟩ : syracuseStep 21869 = 8201) R8201
theorem R22265 : ∃ j : ℕ, syracuseStep^[j] 22265 = 1 := reachStep (stepEq 2 (by rfl) ⟨8349, by rfl⟩ : syracuseStep 22265 = 16699) R16699
theorem R715817 : ∃ j : ℕ, syracuseStep^[j] 715817 = 1 := reachStep (stepEq 2 (by rfl) ⟨268431, by rfl⟩ : syracuseStep 715817 = 536863) R536863
theorem R27 : ∃ j : ℕ, syracuseStep^[j] 27 = 1 := reachStep (stepEq 1 (by rfl) ⟨20, by rfl⟩ : syracuseStep 27 = 41) R41
theorem R55 : ∃ j : ℕ, syracuseStep^[j] 55 = 1 := reachStep (stepEq 1 (by rfl) ⟨41, by rfl⟩ : syracuseStep 55 = 83) R83
theorem R109 : ∃ j : ℕ, syracuseStep^[j] 109 = 1 := reachStep (stepEq 3 (by rfl) ⟨20, by rfl⟩ : syracuseStep 109 = 41) R41
theorem R221 : ∃ j : ℕ, syracuseStep^[j] 221 = 1 := reachStep (stepEq 3 (by rfl) ⟨41, by rfl⟩ : syracuseStep 221 = 83) R83
theorem R437 : ∃ j : ℕ, syracuseStep^[j] 437 = 1 := reachStep (stepEq 5 (by rfl) ⟨20, by rfl⟩ : syracuseStep 437 = 41) R41
theorem R449 : ∃ j : ℕ, syracuseStep^[j] 449 = 1 := reachStep (stepEq 2 (by rfl) ⟨168, by rfl⟩ : syracuseStep 449 = 337) R337
theorem R881 : ∃ j : ℕ, syracuseStep^[j] 881 = 1 := reachStep (stepEq 2 (by rfl) ⟨330, by rfl⟩ : syracuseStep 881 = 661) R661
theorem R885 : ∃ j : ℕ, syracuseStep^[j] 885 = 1 := reachStep (stepEq 5 (by rfl) ⟨41, by rfl⟩ : syracuseStep 885 = 83) R83
theorem R899 : ∃ j : ℕ, syracuseStep^[j] 899 = 1 := reachStep (stepEq 1 (by rfl) ⟨674, by rfl⟩ : syracuseStep 899 = 1349) R1349
theorem R903 : ∃ j : ℕ, syracuseStep^[j] 903 = 1 := reachStep (stepEq 1 (by rfl) ⟨677, by rfl⟩ : syracuseStep 903 = 1355) R1355
theorem R927 : ∃ j : ℕ, syracuseStep^[j] 927 = 1 := reachStep (stepEq 1 (by rfl) ⟨695, by rfl⟩ : syracuseStep 927 = 1391) R1391
theorem R1749 : ∃ j : ℕ, syracuseStep^[j] 1749 = 1 := reachStep (stepEq 7 (by rfl) ⟨20, by rfl⟩ : syracuseStep 1749 = 41) R41
theorem R1763 : ∃ j : ℕ, syracuseStep^[j] 1763 = 1 := reachStep (stepEq 1 (by rfl) ⟨1322, by rfl⟩ : syracuseStep 1763 = 2645) R2645
theorem R1777 : ∃ j : ℕ, syracuseStep^[j] 1777 = 1 := reachStep (stepEq 2 (by rfl) ⟨666, by rfl⟩ : syracuseStep 1777 = 1333) R1333
theorem R1793 : ∃ j : ℕ, syracuseStep^[j] 1793 = 1 := reachStep (stepEq 2 (by rfl) ⟨672, by rfl⟩ : syracuseStep 1793 = 1345) R1345
theorem R1797 : ∃ j : ℕ, syracuseStep^[j] 1797 = 1 := reachStep (stepEq 4 (by rfl) ⟨168, by rfl⟩ : syracuseStep 1797 = 337) R337
theorem R1807 : ∃ j : ℕ, syracuseStep^[j] 1807 = 1 := reachStep (stepEq 1 (by rfl) ⟨1355, by rfl⟩ : syracuseStep 1807 = 2711) R2711
theorem R1855 : ∃ j : ℕ, syracuseStep^[j] 1855 = 1 := reachStep (stepEq 1 (by rfl) ⟨1391, by rfl⟩ : syracuseStep 1855 = 2783) R2783
theorem R3323 : ∃ j : ℕ, syracuseStep^[j] 3323 = 1 := reachStep (stepEq 1 (by rfl) ⟨2492, by rfl⟩ : syracuseStep 3323 = 4985) R4985
theorem R3399 : ∃ j : ℕ, syracuseStep^[j] 3399 = 1 := reachStep (stepEq 1 (by rfl) ⟨2549, by rfl⟩ : syracuseStep 3399 = 5099) R5099
theorem R3431 : ∃ j : ℕ, syracuseStep^[j] 3431 = 1 := reachStep (stepEq 1 (by rfl) ⟨2573, by rfl⟩ : syracuseStep 3431 = 5147) R5147
theorem R3525 : ∃ j : ℕ, syracuseStep^[j] 3525 = 1 := reachStep (stepEq 4 (by rfl) ⟨330, by rfl⟩ : syracuseStep 3525 = 661) R661
theorem R3541 : ∃ j : ℕ, syracuseStep^[j] 3541 = 1 := reachStep (stepEq 7 (by rfl) ⟨41, by rfl⟩ : syracuseStep 3541 = 83) R83
theorem R3555 : ∃ j : ℕ, syracuseStep^[j] 3555 = 1 := reachStep (stepEq 1 (by rfl) ⟨2666, by rfl⟩ : syracuseStep 3555 = 5333) R5333
theorem R3587 : ∃ j : ℕ, syracuseStep^[j] 3587 = 1 := reachStep (stepEq 1 (by rfl) ⟨2690, by rfl⟩ : syracuseStep 3587 = 5381) R5381
theorem R3597 : ∃ j : ℕ, syracuseStep^[j] 3597 = 1 := reachStep (stepEq 3 (by rfl) ⟨674, by rfl⟩ : syracuseStep 3597 = 1349) R1349
theorem R3601 : ∃ j : ℕ, syracuseStep^[j] 3601 = 1 := reachStep (stepEq 2 (by rfl) ⟨1350, by rfl⟩ : syracuseStep 3601 = 2701) R2701
theorem R3613 : ∃ j : ℕ, syracuseStep^[j] 3613 = 1 := reachStep (stepEq 3 (by rfl) ⟨677, by rfl⟩ : syracuseStep 3613 = 1355) R1355
theorem R3623 : ∃ j : ℕ, syracuseStep^[j] 3623 = 1 := reachStep (stepEq 1 (by rfl) ⟨2717, by rfl⟩ : syracuseStep 3623 = 5435) R5435
theorem R3641 : ∃ j : ℕ, syracuseStep^[j] 3641 = 1 := reachStep (stepEq 2 (by rfl) ⟨1365, by rfl⟩ : syracuseStep 3641 = 2731) R2731
theorem R3655 : ∃ j : ℕ, syracuseStep^[j] 3655 = 1 := reachStep (stepEq 1 (by rfl) ⟨2741, by rfl⟩ : syracuseStep 3655 = 5483) R5483
theorem R3657 : ∃ j : ℕ, syracuseStep^[j] 3657 = 1 := reachStep (stepEq 2 (by rfl) ⟨1371, by rfl⟩ : syracuseStep 3657 = 2743) R2743
theorem R3709 : ∃ j : ℕ, syracuseStep^[j] 3709 = 1 := reachStep (stepEq 3 (by rfl) ⟨695, by rfl⟩ : syracuseStep 3709 = 1391) R1391
theorem R6647 : ∃ j : ℕ, syracuseStep^[j] 6647 = 1 := reachStep (stepEq 1 (by rfl) ⟨4985, by rfl⟩ : syracuseStep 6647 = 9971) R9971
theorem R6799 : ∃ j : ℕ, syracuseStep^[j] 6799 = 1 := reachStep (stepEq 1 (by rfl) ⟨5099, by rfl⟩ : syracuseStep 6799 = 10199) R10199
theorem R6863 : ∃ j : ℕ, syracuseStep^[j] 6863 = 1 := reachStep (stepEq 1 (by rfl) ⟨5147, by rfl⟩ : syracuseStep 6863 = 10295) R10295
theorem R6881 : ∃ j : ℕ, syracuseStep^[j] 6881 = 1 := reachStep (stepEq 2 (by rfl) ⟨2580, by rfl⟩ : syracuseStep 6881 = 5161) R5161
theorem R6905 : ∃ j : ℕ, syracuseStep^[j] 6905 = 1 := reachStep (stepEq 2 (by rfl) ⟨2589, by rfl⟩ : syracuseStep 6905 = 5179) R5179
theorem R6907 : ∃ j : ℕ, syracuseStep^[j] 6907 = 1 := reachStep (stepEq 1 (by rfl) ⟨5180, by rfl⟩ : syracuseStep 6907 = 10361) R10361
theorem R6997 : ∃ j : ℕ, syracuseStep^[j] 6997 = 1 := reachStep (stepEq 9 (by rfl) ⟨20, by rfl⟩ : syracuseStep 6997 = 41) R41
theorem R7109 : ∃ j : ℕ, syracuseStep^[j] 7109 = 1 := reachStep (stepEq 4 (by rfl) ⟨666, by rfl⟩ : syracuseStep 7109 = 1333) R1333
theorem R7189 : ∃ j : ℕ, syracuseStep^[j] 7189 = 1 := reachStep (stepEq 6 (by rfl) ⟨168, by rfl⟩ : syracuseStep 7189 = 337) R337
theorem R7195 : ∃ j : ℕ, syracuseStep^[j] 7195 = 1 := reachStep (stepEq 1 (by rfl) ⟨5396, by rfl⟩ : syracuseStep 7195 = 10793) R10793
theorem R7211 : ∃ j : ℕ, syracuseStep^[j] 7211 = 1 := reachStep (stepEq 1 (by rfl) ⟨5408, by rfl⟩ : syracuseStep 7211 = 10817) R10817
theorem R7229 : ∃ j : ℕ, syracuseStep^[j] 7229 = 1 := reachStep (stepEq 3 (by rfl) ⟨1355, by rfl⟩ : syracuseStep 7229 = 2711) R2711
theorem R7247 : ∃ j : ℕ, syracuseStep^[j] 7247 = 1 := reachStep (stepEq 1 (by rfl) ⟨5435, by rfl⟩ : syracuseStep 7247 = 10871) R10871
theorem R7283 : ∃ j : ℕ, syracuseStep^[j] 7283 = 1 := reachStep (stepEq 1 (by rfl) ⟨5462, by rfl⟩ : syracuseStep 7283 = 10925) R10925
theorem R7289 : ∃ j : ℕ, syracuseStep^[j] 7289 = 1 := reachStep (stepEq 2 (by rfl) ⟨2733, by rfl⟩ : syracuseStep 7289 = 5467) R5467
theorem R7313 : ∃ j : ℕ, syracuseStep^[j] 7313 = 1 := reachStep (stepEq 2 (by rfl) ⟨2742, by rfl⟩ : syracuseStep 7313 = 5485) R5485
theorem R7367 : ∃ j : ℕ, syracuseStep^[j] 7367 = 1 := reachStep (stepEq 1 (by rfl) ⟨5525, by rfl⟩ : syracuseStep 7367 = 11051) R11051
theorem R7421 : ∃ j : ℕ, syracuseStep^[j] 7421 = 1 := reachStep (stepEq 3 (by rfl) ⟨1391, by rfl⟩ : syracuseStep 7421 = 2783) R2783
theorem R896807 : ∃ j : ℕ, syracuseStep^[j] 896807 = 1 := reachStep (stepEq 1 (by rfl) ⟨672605, by rfl⟩ : syracuseStep 896807 = 1345211) R1345211
theorem R13243 : ∃ j : ℕ, syracuseStep^[j] 13243 = 1 := reachStep (stepEq 1 (by rfl) ⟨9932, by rfl⟩ : syracuseStep 13243 = 19865) R19865
theorem R13247 : ∃ j : ℕ, syracuseStep^[j] 13247 = 1 := reachStep (stepEq 1 (by rfl) ⟨9935, by rfl⟩ : syracuseStep 13247 = 19871) R19871
theorem R13409 : ∃ j : ℕ, syracuseStep^[j] 13409 = 1 := reachStep (stepEq 2 (by rfl) ⟨5028, by rfl⟩ : syracuseStep 13409 = 10057) R10057
theorem R112103 : ∃ j : ℕ, syracuseStep^[j] 112103 = 1 := reachStep (stepEq 1 (by rfl) ⟨84077, by rfl⟩ : syracuseStep 112103 = 168155) R168155
theorem R14165 : ∃ j : ℕ, syracuseStep^[j] 14165 = 1 := reachStep (stepEq 9 (by rfl) ⟨41, by rfl⟩ : syracuseStep 14165 = 83) R83
theorem R14411 : ∃ j : ℕ, syracuseStep^[j] 14411 = 1 := reachStep (stepEq 1 (by rfl) ⟨10808, by rfl⟩ : syracuseStep 14411 = 21617) R21617
theorem R14453 : ∃ j : ℕ, syracuseStep^[j] 14453 = 1 := reachStep (stepEq 5 (by rfl) ⟨677, by rfl⟩ : syracuseStep 14453 = 1355) R1355
theorem R14471 : ∃ j : ℕ, syracuseStep^[j] 14471 = 1 := reachStep (stepEq 1 (by rfl) ⟨10853, by rfl⟩ : syracuseStep 14471 = 21707) R21707
theorem R14579 : ∃ j : ℕ, syracuseStep^[j] 14579 = 1 := reachStep (stepEq 1 (by rfl) ⟨10934, by rfl⟩ : syracuseStep 14579 = 21869) R21869
theorem R14843 : ∃ j : ℕ, syracuseStep^[j] 14843 = 1 := reachStep (stepEq 1 (by rfl) ⟨11132, by rfl⟩ : syracuseStep 14843 = 22265) R22265
theorem R477211 : ∃ j : ℕ, syracuseStep^[j] 477211 = 1 := reachStep (stepEq 1 (by rfl) ⟨357908, by rfl⟩ : syracuseStep 477211 = 715817) R715817
theorem R28025 : ∃ j : ℕ, syracuseStep^[j] 28025 = 1 := reachStep (stepEq 2 (by rfl) ⟨10509, by rfl⟩ : syracuseStep 28025 = 21019) R21019
theorem R73 : ∃ j : ℕ, syracuseStep^[j] 73 = 1 := reachStep (stepEq 2 (by rfl) ⟨27, by rfl⟩ : syracuseStep 73 = 55) R55
theorem R145 : ∃ j : ℕ, syracuseStep^[j] 145 = 1 := reachStep (stepEq 2 (by rfl) ⟨54, by rfl⟩ : syracuseStep 145 = 109) R109
theorem R147 : ∃ j : ℕ, syracuseStep^[j] 147 = 1 := reachStep (stepEq 1 (by rfl) ⟨110, by rfl⟩ : syracuseStep 147 = 221) R221
theorem R291 : ∃ j : ℕ, syracuseStep^[j] 291 = 1 := reachStep (stepEq 1 (by rfl) ⟨218, by rfl⟩ : syracuseStep 291 = 437) R437
theorem R293 : ∃ j : ℕ, syracuseStep^[j] 293 = 1 := reachStep (stepEq 4 (by rfl) ⟨27, by rfl⟩ : syracuseStep 293 = 55) R55
theorem R299 : ∃ j : ℕ, syracuseStep^[j] 299 = 1 := reachStep (stepEq 1 (by rfl) ⟨224, by rfl⟩ : syracuseStep 299 = 449) R449
theorem R581 : ∃ j : ℕ, syracuseStep^[j] 581 = 1 := reachStep (stepEq 4 (by rfl) ⟨54, by rfl⟩ : syracuseStep 581 = 109) R109
theorem R587 : ∃ j : ℕ, syracuseStep^[j] 587 = 1 := reachStep (stepEq 1 (by rfl) ⟨440, by rfl⟩ : syracuseStep 587 = 881) R881
theorem R589 : ∃ j : ℕ, syracuseStep^[j] 589 = 1 := reachStep (stepEq 3 (by rfl) ⟨110, by rfl⟩ : syracuseStep 589 = 221) R221
theorem R599 : ∃ j : ℕ, syracuseStep^[j] 599 = 1 := reachStep (stepEq 1 (by rfl) ⟨449, by rfl⟩ : syracuseStep 599 = 899) R899
theorem R1165 : ∃ j : ℕ, syracuseStep^[j] 1165 = 1 := reachStep (stepEq 3 (by rfl) ⟨218, by rfl⟩ : syracuseStep 1165 = 437) R437
theorem R1173 : ∃ j : ℕ, syracuseStep^[j] 1173 = 1 := reachStep (stepEq 6 (by rfl) ⟨27, by rfl⟩ : syracuseStep 1173 = 55) R55
theorem R1175 : ∃ j : ℕ, syracuseStep^[j] 1175 = 1 := reachStep (stepEq 1 (by rfl) ⟨881, by rfl⟩ : syracuseStep 1175 = 1763) R1763
theorem R1195 : ∃ j : ℕ, syracuseStep^[j] 1195 = 1 := reachStep (stepEq 1 (by rfl) ⟨896, by rfl⟩ : syracuseStep 1195 = 1793) R1793
theorem R1197 : ∃ j : ℕ, syracuseStep^[j] 1197 = 1 := reachStep (stepEq 3 (by rfl) ⟨224, by rfl⟩ : syracuseStep 1197 = 449) R449
theorem R2215 : ∃ j : ℕ, syracuseStep^[j] 2215 = 1 := reachStep (stepEq 1 (by rfl) ⟨1661, by rfl⟩ : syracuseStep 2215 = 3323) R3323
theorem R2287 : ∃ j : ℕ, syracuseStep^[j] 2287 = 1 := reachStep (stepEq 1 (by rfl) ⟨1715, by rfl⟩ : syracuseStep 2287 = 3431) R3431
theorem R2325 : ∃ j : ℕ, syracuseStep^[j] 2325 = 1 := reachStep (stepEq 6 (by rfl) ⟨54, by rfl⟩ : syracuseStep 2325 = 109) R109
theorem R2349 : ∃ j : ℕ, syracuseStep^[j] 2349 = 1 := reachStep (stepEq 3 (by rfl) ⟨440, by rfl⟩ : syracuseStep 2349 = 881) R881
theorem R2357 : ∃ j : ℕ, syracuseStep^[j] 2357 = 1 := reachStep (stepEq 5 (by rfl) ⟨110, by rfl⟩ : syracuseStep 2357 = 221) R221
theorem R2369 : ∃ j : ℕ, syracuseStep^[j] 2369 = 1 := reachStep (stepEq 2 (by rfl) ⟨888, by rfl⟩ : syracuseStep 2369 = 1777) R1777
theorem R2391 : ∃ j : ℕ, syracuseStep^[j] 2391 = 1 := reachStep (stepEq 1 (by rfl) ⟨1793, by rfl⟩ : syracuseStep 2391 = 3587) R3587
theorem R2397 : ∃ j : ℕ, syracuseStep^[j] 2397 = 1 := reachStep (stepEq 3 (by rfl) ⟨449, by rfl⟩ : syracuseStep 2397 = 899) R899
theorem R2409 : ∃ j : ℕ, syracuseStep^[j] 2409 = 1 := reachStep (stepEq 2 (by rfl) ⟨903, by rfl⟩ : syracuseStep 2409 = 1807) R1807
theorem R2415 : ∃ j : ℕ, syracuseStep^[j] 2415 = 1 := reachStep (stepEq 1 (by rfl) ⟨1811, by rfl⟩ : syracuseStep 2415 = 3623) R3623
theorem R2427 : ∃ j : ℕ, syracuseStep^[j] 2427 = 1 := reachStep (stepEq 1 (by rfl) ⟨1820, by rfl⟩ : syracuseStep 2427 = 3641) R3641
theorem R2473 : ∃ j : ℕ, syracuseStep^[j] 2473 = 1 := reachStep (stepEq 2 (by rfl) ⟨927, by rfl⟩ : syracuseStep 2473 = 1855) R1855
theorem R4431 : ∃ j : ℕ, syracuseStep^[j] 4431 = 1 := reachStep (stepEq 1 (by rfl) ⟨3323, by rfl⟩ : syracuseStep 4431 = 6647) R6647
theorem R4575 : ∃ j : ℕ, syracuseStep^[j] 4575 = 1 := reachStep (stepEq 1 (by rfl) ⟨3431, by rfl⟩ : syracuseStep 4575 = 6863) R6863
theorem R4587 : ∃ j : ℕ, syracuseStep^[j] 4587 = 1 := reachStep (stepEq 1 (by rfl) ⟨3440, by rfl⟩ : syracuseStep 4587 = 6881) R6881
theorem R4603 : ∃ j : ℕ, syracuseStep^[j] 4603 = 1 := reachStep (stepEq 1 (by rfl) ⟨3452, by rfl⟩ : syracuseStep 4603 = 6905) R6905
theorem R4661 : ∃ j : ℕ, syracuseStep^[j] 4661 = 1 := reachStep (stepEq 5 (by rfl) ⟨218, by rfl⟩ : syracuseStep 4661 = 437) R437
theorem R4693 : ∃ j : ℕ, syracuseStep^[j] 4693 = 1 := reachStep (stepEq 8 (by rfl) ⟨27, by rfl⟩ : syracuseStep 4693 = 55) R55
theorem R4701 : ∃ j : ℕ, syracuseStep^[j] 4701 = 1 := reachStep (stepEq 3 (by rfl) ⟨881, by rfl⟩ : syracuseStep 4701 = 1763) R1763
theorem R4721 : ∃ j : ℕ, syracuseStep^[j] 4721 = 1 := reachStep (stepEq 2 (by rfl) ⟨1770, by rfl⟩ : syracuseStep 4721 = 3541) R3541
theorem R4739 : ∃ j : ℕ, syracuseStep^[j] 4739 = 1 := reachStep (stepEq 1 (by rfl) ⟨3554, by rfl⟩ : syracuseStep 4739 = 7109) R7109
theorem R4781 : ∃ j : ℕ, syracuseStep^[j] 4781 = 1 := reachStep (stepEq 3 (by rfl) ⟨896, by rfl⟩ : syracuseStep 4781 = 1793) R1793
theorem R4789 : ∃ j : ℕ, syracuseStep^[j] 4789 = 1 := reachStep (stepEq 5 (by rfl) ⟨224, by rfl⟩ : syracuseStep 4789 = 449) R449
theorem R4801 : ∃ j : ℕ, syracuseStep^[j] 4801 = 1 := reachStep (stepEq 2 (by rfl) ⟨1800, by rfl⟩ : syracuseStep 4801 = 3601) R3601
theorem R4807 : ∃ j : ℕ, syracuseStep^[j] 4807 = 1 := reachStep (stepEq 1 (by rfl) ⟨3605, by rfl⟩ : syracuseStep 4807 = 7211) R7211
theorem R4817 : ∃ j : ℕ, syracuseStep^[j] 4817 = 1 := reachStep (stepEq 2 (by rfl) ⟨1806, by rfl⟩ : syracuseStep 4817 = 3613) R3613
theorem R4819 : ∃ j : ℕ, syracuseStep^[j] 4819 = 1 := reachStep (stepEq 1 (by rfl) ⟨3614, by rfl⟩ : syracuseStep 4819 = 7229) R7229
theorem R4831 : ∃ j : ℕ, syracuseStep^[j] 4831 = 1 := reachStep (stepEq 1 (by rfl) ⟨3623, by rfl⟩ : syracuseStep 4831 = 7247) R7247
theorem R4855 : ∃ j : ℕ, syracuseStep^[j] 4855 = 1 := reachStep (stepEq 1 (by rfl) ⟨3641, by rfl⟩ : syracuseStep 4855 = 7283) R7283
theorem R4859 : ∃ j : ℕ, syracuseStep^[j] 4859 = 1 := reachStep (stepEq 1 (by rfl) ⟨3644, by rfl⟩ : syracuseStep 4859 = 7289) R7289
theorem R4873 : ∃ j : ℕ, syracuseStep^[j] 4873 = 1 := reachStep (stepEq 2 (by rfl) ⟨1827, by rfl⟩ : syracuseStep 4873 = 3655) R3655
theorem R4875 : ∃ j : ℕ, syracuseStep^[j] 4875 = 1 := reachStep (stepEq 1 (by rfl) ⟨3656, by rfl⟩ : syracuseStep 4875 = 7313) R7313
theorem R4911 : ∃ j : ℕ, syracuseStep^[j] 4911 = 1 := reachStep (stepEq 1 (by rfl) ⟨3683, by rfl⟩ : syracuseStep 4911 = 7367) R7367
theorem R4945 : ∃ j : ℕ, syracuseStep^[j] 4945 = 1 := reachStep (stepEq 2 (by rfl) ⟨1854, by rfl⟩ : syracuseStep 4945 = 3709) R3709
theorem R4947 : ∃ j : ℕ, syracuseStep^[j] 4947 = 1 := reachStep (stepEq 1 (by rfl) ⟨3710, by rfl⟩ : syracuseStep 4947 = 7421) R7421
theorem R38341 : ∃ j : ℕ, syracuseStep^[j] 38341 = 1 := reachStep (stepEq 4 (by rfl) ⟨3594, by rfl⟩ : syracuseStep 38341 = 7189) R7189
theorem R597871 : ∃ j : ℕ, syracuseStep^[j] 597871 = 1 := reachStep (stepEq 1 (by rfl) ⟨448403, by rfl⟩ : syracuseStep 597871 = 896807) R896807
theorem R8831 : ∃ j : ℕ, syracuseStep^[j] 8831 = 1 := reachStep (stepEq 1 (by rfl) ⟨6623, by rfl⟩ : syracuseStep 8831 = 13247) R13247
theorem R8861 : ∃ j : ℕ, syracuseStep^[j] 8861 = 1 := reachStep (stepEq 3 (by rfl) ⟨1661, by rfl⟩ : syracuseStep 8861 = 3323) R3323
theorem R8939 : ∃ j : ℕ, syracuseStep^[j] 8939 = 1 := reachStep (stepEq 1 (by rfl) ⟨6704, by rfl⟩ : syracuseStep 8939 = 13409) R13409
theorem R9065 : ∃ j : ℕ, syracuseStep^[j] 9065 = 1 := reachStep (stepEq 2 (by rfl) ⟨3399, by rfl⟩ : syracuseStep 9065 = 6799) R6799
theorem R9149 : ∃ j : ℕ, syracuseStep^[j] 9149 = 1 := reachStep (stepEq 3 (by rfl) ⟨1715, by rfl⟩ : syracuseStep 9149 = 3431) R3431
theorem R74735 : ∃ j : ℕ, syracuseStep^[j] 74735 = 1 := reachStep (stepEq 1 (by rfl) ⟨56051, by rfl⟩ : syracuseStep 74735 = 112103) R112103
theorem R9209 : ∃ j : ℕ, syracuseStep^[j] 9209 = 1 := reachStep (stepEq 2 (by rfl) ⟨3453, by rfl⟩ : syracuseStep 9209 = 6907) R6907
theorem R9301 : ∃ j : ℕ, syracuseStep^[j] 9301 = 1 := reachStep (stepEq 8 (by rfl) ⟨54, by rfl⟩ : syracuseStep 9301 = 109) R109
theorem R9329 : ∃ j : ℕ, syracuseStep^[j] 9329 = 1 := reachStep (stepEq 2 (by rfl) ⟨3498, by rfl⟩ : syracuseStep 9329 = 6997) R6997
theorem R9443 : ∃ j : ℕ, syracuseStep^[j] 9443 = 1 := reachStep (stepEq 1 (by rfl) ⟨7082, by rfl⟩ : syracuseStep 9443 = 14165) R14165
theorem R9593 : ∃ j : ℕ, syracuseStep^[j] 9593 = 1 := reachStep (stepEq 2 (by rfl) ⟨3597, by rfl⟩ : syracuseStep 9593 = 7195) R7195
theorem R9607 : ∃ j : ℕ, syracuseStep^[j] 9607 = 1 := reachStep (stepEq 1 (by rfl) ⟨7205, by rfl⟩ : syracuseStep 9607 = 14411) R14411
theorem R9635 : ∃ j : ℕ, syracuseStep^[j] 9635 = 1 := reachStep (stepEq 1 (by rfl) ⟨7226, by rfl⟩ : syracuseStep 9635 = 14453) R14453
theorem R9647 : ∃ j : ℕ, syracuseStep^[j] 9647 = 1 := reachStep (stepEq 1 (by rfl) ⟨7235, by rfl⟩ : syracuseStep 9647 = 14471) R14471
theorem R9719 : ∃ j : ℕ, syracuseStep^[j] 9719 = 1 := reachStep (stepEq 1 (by rfl) ⟨7289, by rfl⟩ : syracuseStep 9719 = 14579) R14579
theorem R9893 : ∃ j : ℕ, syracuseStep^[j] 9893 = 1 := reachStep (stepEq 4 (by rfl) ⟨927, by rfl⟩ : syracuseStep 9893 = 1855) R1855
theorem R9895 : ∃ j : ℕ, syracuseStep^[j] 9895 = 1 := reachStep (stepEq 1 (by rfl) ⟨7421, by rfl⟩ : syracuseStep 9895 = 14843) R14843
theorem R636281 : ∃ j : ℕ, syracuseStep^[j] 636281 = 1 := reachStep (stepEq 2 (by rfl) ⟨238605, by rfl⟩ : syracuseStep 636281 = 477211) R477211
theorem R17657 : ∃ j : ℕ, syracuseStep^[j] 17657 = 1 := reachStep (stepEq 2 (by rfl) ⟨6621, by rfl⟩ : syracuseStep 17657 = 13243) R13243
theorem R18413 : ∃ j : ℕ, syracuseStep^[j] 18413 = 1 := reachStep (stepEq 3 (by rfl) ⟨3452, by rfl⟩ : syracuseStep 18413 = 6905) R6905
theorem R18683 : ∃ j : ℕ, syracuseStep^[j] 18683 = 1 := reachStep (stepEq 1 (by rfl) ⟨14012, by rfl⟩ : syracuseStep 18683 = 28025) R28025
theorem R19277 : ∃ j : ℕ, syracuseStep^[j] 19277 = 1 := reachStep (stepEq 3 (by rfl) ⟨3614, by rfl⟩ : syracuseStep 19277 = 7229) R7229
theorem R19493 : ∃ j : ℕ, syracuseStep^[j] 19493 = 1 := reachStep (stepEq 4 (by rfl) ⟨1827, by rfl⟩ : syracuseStep 19493 = 3655) R3655
theorem R97 : ∃ j : ℕ, syracuseStep^[j] 97 = 1 := reachStep (stepEq 2 (by rfl) ⟨36, by rfl⟩ : syracuseStep 97 = 73) R73
theorem R193 : ∃ j : ℕ, syracuseStep^[j] 193 = 1 := reachStep (stepEq 2 (by rfl) ⟨72, by rfl⟩ : syracuseStep 193 = 145) R145
theorem R195 : ∃ j : ℕ, syracuseStep^[j] 195 = 1 := reachStep (stepEq 1 (by rfl) ⟨146, by rfl⟩ : syracuseStep 195 = 293) R293
theorem R199 : ∃ j : ℕ, syracuseStep^[j] 199 = 1 := reachStep (stepEq 1 (by rfl) ⟨149, by rfl⟩ : syracuseStep 199 = 299) R299
theorem R387 : ∃ j : ℕ, syracuseStep^[j] 387 = 1 := reachStep (stepEq 1 (by rfl) ⟨290, by rfl⟩ : syracuseStep 387 = 581) R581
theorem R389 : ∃ j : ℕ, syracuseStep^[j] 389 = 1 := reachStep (stepEq 4 (by rfl) ⟨36, by rfl⟩ : syracuseStep 389 = 73) R73
theorem R391 : ∃ j : ℕ, syracuseStep^[j] 391 = 1 := reachStep (stepEq 1 (by rfl) ⟨293, by rfl⟩ : syracuseStep 391 = 587) R587
theorem R399 : ∃ j : ℕ, syracuseStep^[j] 399 = 1 := reachStep (stepEq 1 (by rfl) ⟨299, by rfl⟩ : syracuseStep 399 = 599) R599
theorem R773 : ∃ j : ℕ, syracuseStep^[j] 773 = 1 := reachStep (stepEq 4 (by rfl) ⟨72, by rfl⟩ : syracuseStep 773 = 145) R145
theorem R781 : ∃ j : ℕ, syracuseStep^[j] 781 = 1 := reachStep (stepEq 3 (by rfl) ⟨146, by rfl⟩ : syracuseStep 781 = 293) R293
theorem R783 : ∃ j : ℕ, syracuseStep^[j] 783 = 1 := reachStep (stepEq 1 (by rfl) ⟨587, by rfl⟩ : syracuseStep 783 = 1175) R1175
theorem R785 : ∃ j : ℕ, syracuseStep^[j] 785 = 1 := reachStep (stepEq 2 (by rfl) ⟨294, by rfl⟩ : syracuseStep 785 = 589) R589
theorem R797 : ∃ j : ℕ, syracuseStep^[j] 797 = 1 := reachStep (stepEq 3 (by rfl) ⟨149, by rfl⟩ : syracuseStep 797 = 299) R299
theorem R1549 : ∃ j : ℕ, syracuseStep^[j] 1549 = 1 := reachStep (stepEq 3 (by rfl) ⟨290, by rfl⟩ : syracuseStep 1549 = 581) R581
theorem R1553 : ∃ j : ℕ, syracuseStep^[j] 1553 = 1 := reachStep (stepEq 2 (by rfl) ⟨582, by rfl⟩ : syracuseStep 1553 = 1165) R1165
theorem R1557 : ∃ j : ℕ, syracuseStep^[j] 1557 = 1 := reachStep (stepEq 6 (by rfl) ⟨36, by rfl⟩ : syracuseStep 1557 = 73) R73
theorem R1565 : ∃ j : ℕ, syracuseStep^[j] 1565 = 1 := reachStep (stepEq 3 (by rfl) ⟨293, by rfl⟩ : syracuseStep 1565 = 587) R587
theorem R1571 : ∃ j : ℕ, syracuseStep^[j] 1571 = 1 := reachStep (stepEq 1 (by rfl) ⟨1178, by rfl⟩ : syracuseStep 1571 = 2357) R2357
theorem R1579 : ∃ j : ℕ, syracuseStep^[j] 1579 = 1 := reachStep (stepEq 1 (by rfl) ⟨1184, by rfl⟩ : syracuseStep 1579 = 2369) R2369
theorem R1593 : ∃ j : ℕ, syracuseStep^[j] 1593 = 1 := reachStep (stepEq 2 (by rfl) ⟨597, by rfl⟩ : syracuseStep 1593 = 1195) R1195
theorem R1597 : ∃ j : ℕ, syracuseStep^[j] 1597 = 1 := reachStep (stepEq 3 (by rfl) ⟨299, by rfl⟩ : syracuseStep 1597 = 599) R599
theorem R2953 : ∃ j : ℕ, syracuseStep^[j] 2953 = 1 := reachStep (stepEq 2 (by rfl) ⟨1107, by rfl⟩ : syracuseStep 2953 = 2215) R2215
theorem R3049 : ∃ j : ℕ, syracuseStep^[j] 3049 = 1 := reachStep (stepEq 2 (by rfl) ⟨1143, by rfl⟩ : syracuseStep 3049 = 2287) R2287
theorem R3093 : ∃ j : ℕ, syracuseStep^[j] 3093 = 1 := reachStep (stepEq 6 (by rfl) ⟨72, by rfl⟩ : syracuseStep 3093 = 145) R145
theorem R3107 : ∃ j : ℕ, syracuseStep^[j] 3107 = 1 := reachStep (stepEq 1 (by rfl) ⟨2330, by rfl⟩ : syracuseStep 3107 = 4661) R4661
theorem R3125 : ∃ j : ℕ, syracuseStep^[j] 3125 = 1 := reachStep (stepEq 5 (by rfl) ⟨146, by rfl⟩ : syracuseStep 3125 = 293) R293
theorem R3133 : ∃ j : ℕ, syracuseStep^[j] 3133 = 1 := reachStep (stepEq 3 (by rfl) ⟨587, by rfl⟩ : syracuseStep 3133 = 1175) R1175
theorem R3141 : ∃ j : ℕ, syracuseStep^[j] 3141 = 1 := reachStep (stepEq 4 (by rfl) ⟨294, by rfl⟩ : syracuseStep 3141 = 589) R589
theorem R3147 : ∃ j : ℕ, syracuseStep^[j] 3147 = 1 := reachStep (stepEq 1 (by rfl) ⟨2360, by rfl⟩ : syracuseStep 3147 = 4721) R4721
theorem R3159 : ∃ j : ℕ, syracuseStep^[j] 3159 = 1 := reachStep (stepEq 1 (by rfl) ⟨2369, by rfl⟩ : syracuseStep 3159 = 4739) R4739
theorem R3187 : ∃ j : ℕ, syracuseStep^[j] 3187 = 1 := reachStep (stepEq 1 (by rfl) ⟨2390, by rfl⟩ : syracuseStep 3187 = 4781) R4781
theorem R3189 : ∃ j : ℕ, syracuseStep^[j] 3189 = 1 := reachStep (stepEq 5 (by rfl) ⟨149, by rfl⟩ : syracuseStep 3189 = 299) R299
theorem R3211 : ∃ j : ℕ, syracuseStep^[j] 3211 = 1 := reachStep (stepEq 1 (by rfl) ⟨2408, by rfl⟩ : syracuseStep 3211 = 4817) R4817
theorem R3239 : ∃ j : ℕ, syracuseStep^[j] 3239 = 1 := reachStep (stepEq 1 (by rfl) ⟨2429, by rfl⟩ : syracuseStep 3239 = 4859) R4859
theorem R3297 : ∃ j : ℕ, syracuseStep^[j] 3297 = 1 := reachStep (stepEq 2 (by rfl) ⟨1236, by rfl⟩ : syracuseStep 3297 = 2473) R2473
theorem R5887 : ∃ j : ℕ, syracuseStep^[j] 5887 = 1 := reachStep (stepEq 1 (by rfl) ⟨4415, by rfl⟩ : syracuseStep 5887 = 8831) R8831
theorem R5907 : ∃ j : ℕ, syracuseStep^[j] 5907 = 1 := reachStep (stepEq 1 (by rfl) ⟨4430, by rfl⟩ : syracuseStep 5907 = 8861) R8861
theorem R5959 : ∃ j : ℕ, syracuseStep^[j] 5959 = 1 := reachStep (stepEq 1 (by rfl) ⟨4469, by rfl⟩ : syracuseStep 5959 = 8939) R8939
theorem R6043 : ∃ j : ℕ, syracuseStep^[j] 6043 = 1 := reachStep (stepEq 1 (by rfl) ⟨4532, by rfl⟩ : syracuseStep 6043 = 9065) R9065
theorem R6099 : ∃ j : ℕ, syracuseStep^[j] 6099 = 1 := reachStep (stepEq 1 (by rfl) ⟨4574, by rfl⟩ : syracuseStep 6099 = 9149) R9149
theorem R6137 : ∃ j : ℕ, syracuseStep^[j] 6137 = 1 := reachStep (stepEq 2 (by rfl) ⟨2301, by rfl⟩ : syracuseStep 6137 = 4603) R4603
theorem R6139 : ∃ j : ℕ, syracuseStep^[j] 6139 = 1 := reachStep (stepEq 1 (by rfl) ⟨4604, by rfl⟩ : syracuseStep 6139 = 9209) R9209
theorem R6197 : ∃ j : ℕ, syracuseStep^[j] 6197 = 1 := reachStep (stepEq 5 (by rfl) ⟨290, by rfl⟩ : syracuseStep 6197 = 581) R581
theorem R6213 : ∃ j : ℕ, syracuseStep^[j] 6213 = 1 := reachStep (stepEq 4 (by rfl) ⟨582, by rfl⟩ : syracuseStep 6213 = 1165) R1165
theorem R6219 : ∃ j : ℕ, syracuseStep^[j] 6219 = 1 := reachStep (stepEq 1 (by rfl) ⟨4664, by rfl⟩ : syracuseStep 6219 = 9329) R9329
theorem R6229 : ∃ j : ℕ, syracuseStep^[j] 6229 = 1 := reachStep (stepEq 8 (by rfl) ⟨36, by rfl⟩ : syracuseStep 6229 = 73) R73
theorem R6257 : ∃ j : ℕ, syracuseStep^[j] 6257 = 1 := reachStep (stepEq 2 (by rfl) ⟨2346, by rfl⟩ : syracuseStep 6257 = 4693) R4693
theorem R6261 : ∃ j : ℕ, syracuseStep^[j] 6261 = 1 := reachStep (stepEq 5 (by rfl) ⟨293, by rfl⟩ : syracuseStep 6261 = 587) R587
theorem R6285 : ∃ j : ℕ, syracuseStep^[j] 6285 = 1 := reachStep (stepEq 3 (by rfl) ⟨1178, by rfl⟩ : syracuseStep 6285 = 2357) R2357
theorem R6295 : ∃ j : ℕ, syracuseStep^[j] 6295 = 1 := reachStep (stepEq 1 (by rfl) ⟨4721, by rfl⟩ : syracuseStep 6295 = 9443) R9443
theorem R6317 : ∃ j : ℕ, syracuseStep^[j] 6317 = 1 := reachStep (stepEq 3 (by rfl) ⟨1184, by rfl⟩ : syracuseStep 6317 = 2369) R2369
theorem R6373 : ∃ j : ℕ, syracuseStep^[j] 6373 = 1 := reachStep (stepEq 4 (by rfl) ⟨597, by rfl⟩ : syracuseStep 6373 = 1195) R1195
theorem R6385 : ∃ j : ℕ, syracuseStep^[j] 6385 = 1 := reachStep (stepEq 2 (by rfl) ⟨2394, by rfl⟩ : syracuseStep 6385 = 4789) R4789
theorem R6389 : ∃ j : ℕ, syracuseStep^[j] 6389 = 1 := reachStep (stepEq 5 (by rfl) ⟨299, by rfl⟩ : syracuseStep 6389 = 599) R599
theorem R6395 : ∃ j : ℕ, syracuseStep^[j] 6395 = 1 := reachStep (stepEq 1 (by rfl) ⟨4796, by rfl⟩ : syracuseStep 6395 = 9593) R9593
theorem R6401 : ∃ j : ℕ, syracuseStep^[j] 6401 = 1 := reachStep (stepEq 2 (by rfl) ⟨2400, by rfl⟩ : syracuseStep 6401 = 4801) R4801
theorem R6409 : ∃ j : ℕ, syracuseStep^[j] 6409 = 1 := reachStep (stepEq 2 (by rfl) ⟨2403, by rfl⟩ : syracuseStep 6409 = 4807) R4807
theorem R6423 : ∃ j : ℕ, syracuseStep^[j] 6423 = 1 := reachStep (stepEq 1 (by rfl) ⟨4817, by rfl⟩ : syracuseStep 6423 = 9635) R9635
theorem R6425 : ∃ j : ℕ, syracuseStep^[j] 6425 = 1 := reachStep (stepEq 2 (by rfl) ⟨2409, by rfl⟩ : syracuseStep 6425 = 4819) R4819
theorem R6431 : ∃ j : ℕ, syracuseStep^[j] 6431 = 1 := reachStep (stepEq 1 (by rfl) ⟨4823, by rfl⟩ : syracuseStep 6431 = 9647) R9647
theorem R6441 : ∃ j : ℕ, syracuseStep^[j] 6441 = 1 := reachStep (stepEq 2 (by rfl) ⟨2415, by rfl⟩ : syracuseStep 6441 = 4831) R4831
theorem R6473 : ∃ j : ℕ, syracuseStep^[j] 6473 = 1 := reachStep (stepEq 2 (by rfl) ⟨2427, by rfl⟩ : syracuseStep 6473 = 4855) R4855
theorem R6479 : ∃ j : ℕ, syracuseStep^[j] 6479 = 1 := reachStep (stepEq 1 (by rfl) ⟨4859, by rfl⟩ : syracuseStep 6479 = 9719) R9719
theorem R6497 : ∃ j : ℕ, syracuseStep^[j] 6497 = 1 := reachStep (stepEq 2 (by rfl) ⟨2436, by rfl⟩ : syracuseStep 6497 = 4873) R4873
theorem R6593 : ∃ j : ℕ, syracuseStep^[j] 6593 = 1 := reachStep (stepEq 2 (by rfl) ⟨2472, by rfl⟩ : syracuseStep 6593 = 4945) R4945
theorem R6595 : ∃ j : ℕ, syracuseStep^[j] 6595 = 1 := reachStep (stepEq 1 (by rfl) ⟨4946, by rfl⟩ : syracuseStep 6595 = 9893) R9893
theorem R797161 : ∃ j : ℕ, syracuseStep^[j] 797161 = 1 := reachStep (stepEq 2 (by rfl) ⟨298935, by rfl⟩ : syracuseStep 797161 = 597871) R597871
theorem R11771 : ∃ j : ℕ, syracuseStep^[j] 11771 = 1 := reachStep (stepEq 1 (by rfl) ⟨8828, by rfl⟩ : syracuseStep 11771 = 17657) R17657
theorem R12197 : ∃ j : ℕ, syracuseStep^[j] 12197 = 1 := reachStep (stepEq 4 (by rfl) ⟨1143, by rfl⟩ : syracuseStep 12197 = 2287) R2287
theorem R12275 : ∃ j : ℕ, syracuseStep^[j] 12275 = 1 := reachStep (stepEq 1 (by rfl) ⟨9206, by rfl⟩ : syracuseStep 12275 = 18413) R18413
theorem R12401 : ∃ j : ℕ, syracuseStep^[j] 12401 = 1 := reachStep (stepEq 2 (by rfl) ⟨4650, by rfl⟩ : syracuseStep 12401 = 9301) R9301
theorem R12455 : ∃ j : ℕ, syracuseStep^[j] 12455 = 1 := reachStep (stepEq 1 (by rfl) ⟨9341, by rfl⟩ : syracuseStep 12455 = 18683) R18683
theorem R12757 : ∃ j : ℕ, syracuseStep^[j] 12757 = 1 := reachStep (stepEq 7 (by rfl) ⟨149, by rfl⟩ : syracuseStep 12757 = 299) R299
theorem R12809 : ∃ j : ℕ, syracuseStep^[j] 12809 = 1 := reachStep (stepEq 2 (by rfl) ⟨4803, by rfl⟩ : syracuseStep 12809 = 9607) R9607
theorem R12851 : ∃ j : ℕ, syracuseStep^[j] 12851 = 1 := reachStep (stepEq 1 (by rfl) ⟨9638, by rfl⟩ : syracuseStep 12851 = 19277) R19277
theorem R12995 : ∃ j : ℕ, syracuseStep^[j] 12995 = 1 := reachStep (stepEq 1 (by rfl) ⟨9746, by rfl⟩ : syracuseStep 12995 = 19493) R19493
theorem R13193 : ∃ j : ℕ, syracuseStep^[j] 13193 = 1 := reachStep (stepEq 2 (by rfl) ⟨4947, by rfl⟩ : syracuseStep 13193 = 9895) R9895
theorem R49823 : ∃ j : ℕ, syracuseStep^[j] 49823 = 1 := reachStep (stepEq 1 (by rfl) ⟨37367, by rfl⟩ : syracuseStep 49823 = 74735) R74735
theorem R51029 : ∃ j : ℕ, syracuseStep^[j] 51029 = 1 := reachStep (stepEq 9 (by rfl) ⟨149, by rfl⟩ : syracuseStep 51029 = 299) R299
theorem R51121 : ∃ j : ℕ, syracuseStep^[j] 51121 = 1 := reachStep (stepEq 2 (by rfl) ⟨19170, by rfl⟩ : syracuseStep 51121 = 38341) R38341
theorem R24877 : ∃ j : ℕ, syracuseStep^[j] 24877 = 1 := reachStep (stepEq 3 (by rfl) ⟨4664, by rfl⟩ : syracuseStep 24877 = 9329) R9329
theorem R25181 : ∃ j : ℕ, syracuseStep^[j] 25181 = 1 := reachStep (stepEq 3 (by rfl) ⟨4721, by rfl⟩ : syracuseStep 25181 = 9443) R9443
theorem R26381 : ∃ j : ℕ, syracuseStep^[j] 26381 = 1 := reachStep (stepEq 3 (by rfl) ⟨4946, by rfl⟩ : syracuseStep 26381 = 9893) R9893
theorem R424187 : ∃ j : ℕ, syracuseStep^[j] 424187 = 1 := reachStep (stepEq 1 (by rfl) ⟨318140, by rfl⟩ : syracuseStep 424187 = 636281) R636281
theorem R129 : ∃ j : ℕ, syracuseStep^[j] 129 = 1 := reachStep (stepEq 2 (by rfl) ⟨48, by rfl⟩ : syracuseStep 129 = 97) R97
theorem R257 : ∃ j : ℕ, syracuseStep^[j] 257 = 1 := reachStep (stepEq 2 (by rfl) ⟨96, by rfl⟩ : syracuseStep 257 = 193) R193
theorem R259 : ∃ j : ℕ, syracuseStep^[j] 259 = 1 := reachStep (stepEq 1 (by rfl) ⟨194, by rfl⟩ : syracuseStep 259 = 389) R389
theorem R265 : ∃ j : ℕ, syracuseStep^[j] 265 = 1 := reachStep (stepEq 2 (by rfl) ⟨99, by rfl⟩ : syracuseStep 265 = 199) R199
theorem R33169 : ∃ j : ℕ, syracuseStep^[j] 33169 = 1 := reachStep (stepEq 2 (by rfl) ⟨12438, by rfl⟩ : syracuseStep 33169 = 24877) R24877
theorem R33215 : ∃ j : ℕ, syracuseStep^[j] 33215 = 1 := reachStep (stepEq 1 (by rfl) ⟨24911, by rfl⟩ : syracuseStep 33215 = 49823) R49823
theorem R515 : ∃ j : ℕ, syracuseStep^[j] 515 = 1 := reachStep (stepEq 1 (by rfl) ⟨386, by rfl⟩ : syracuseStep 515 = 773) R773
theorem R517 : ∃ j : ℕ, syracuseStep^[j] 517 = 1 := reachStep (stepEq 4 (by rfl) ⟨48, by rfl⟩ : syracuseStep 517 = 97) R97
theorem R521 : ∃ j : ℕ, syracuseStep^[j] 521 = 1 := reachStep (stepEq 2 (by rfl) ⟨195, by rfl⟩ : syracuseStep 521 = 391) R391
theorem R523 : ∃ j : ℕ, syracuseStep^[j] 523 = 1 := reachStep (stepEq 1 (by rfl) ⟨392, by rfl⟩ : syracuseStep 523 = 785) R785
theorem R531 : ∃ j : ℕ, syracuseStep^[j] 531 = 1 := reachStep (stepEq 1 (by rfl) ⟨398, by rfl⟩ : syracuseStep 531 = 797) R797
theorem R1029 : ∃ j : ℕ, syracuseStep^[j] 1029 = 1 := reachStep (stepEq 4 (by rfl) ⟨96, by rfl⟩ : syracuseStep 1029 = 193) R193
theorem R1035 : ∃ j : ℕ, syracuseStep^[j] 1035 = 1 := reachStep (stepEq 1 (by rfl) ⟨776, by rfl⟩ : syracuseStep 1035 = 1553) R1553
theorem R1037 : ∃ j : ℕ, syracuseStep^[j] 1037 = 1 := reachStep (stepEq 3 (by rfl) ⟨194, by rfl⟩ : syracuseStep 1037 = 389) R389
theorem R1041 : ∃ j : ℕ, syracuseStep^[j] 1041 = 1 := reachStep (stepEq 2 (by rfl) ⟨390, by rfl⟩ : syracuseStep 1041 = 781) R781
theorem R1043 : ∃ j : ℕ, syracuseStep^[j] 1043 = 1 := reachStep (stepEq 1 (by rfl) ⟨782, by rfl⟩ : syracuseStep 1043 = 1565) R1565
theorem R1047 : ∃ j : ℕ, syracuseStep^[j] 1047 = 1 := reachStep (stepEq 1 (by rfl) ⟨785, by rfl⟩ : syracuseStep 1047 = 1571) R1571
theorem R1061 : ∃ j : ℕ, syracuseStep^[j] 1061 = 1 := reachStep (stepEq 4 (by rfl) ⟨99, by rfl⟩ : syracuseStep 1061 = 199) R199
theorem R34019 : ∃ j : ℕ, syracuseStep^[j] 34019 = 1 := reachStep (stepEq 1 (by rfl) ⟨25514, by rfl⟩ : syracuseStep 34019 = 51029) R51029
theorem R34157 : ∃ j : ℕ, syracuseStep^[j] 34157 = 1 := reachStep (stepEq 3 (by rfl) ⟨6404, by rfl⟩ : syracuseStep 34157 = 12809) R12809
theorem R2061 : ∃ j : ℕ, syracuseStep^[j] 2061 = 1 := reachStep (stepEq 3 (by rfl) ⟨386, by rfl⟩ : syracuseStep 2061 = 773) R773
theorem R2065 : ∃ j : ℕ, syracuseStep^[j] 2065 = 1 := reachStep (stepEq 2 (by rfl) ⟨774, by rfl⟩ : syracuseStep 2065 = 1549) R1549
theorem R2069 : ∃ j : ℕ, syracuseStep^[j] 2069 = 1 := reachStep (stepEq 6 (by rfl) ⟨48, by rfl⟩ : syracuseStep 2069 = 97) R97
theorem R2071 : ∃ j : ℕ, syracuseStep^[j] 2071 = 1 := reachStep (stepEq 1 (by rfl) ⟨1553, by rfl⟩ : syracuseStep 2071 = 3107) R3107
theorem R2083 : ∃ j : ℕ, syracuseStep^[j] 2083 = 1 := reachStep (stepEq 1 (by rfl) ⟨1562, by rfl⟩ : syracuseStep 2083 = 3125) R3125
theorem R2085 : ∃ j : ℕ, syracuseStep^[j] 2085 = 1 := reachStep (stepEq 4 (by rfl) ⟨195, by rfl⟩ : syracuseStep 2085 = 391) R391
theorem R2093 : ∃ j : ℕ, syracuseStep^[j] 2093 = 1 := reachStep (stepEq 3 (by rfl) ⟨392, by rfl⟩ : syracuseStep 2093 = 785) R785
theorem R2105 : ∃ j : ℕ, syracuseStep^[j] 2105 = 1 := reachStep (stepEq 2 (by rfl) ⟨789, by rfl⟩ : syracuseStep 2105 = 1579) R1579
theorem R2125 : ∃ j : ℕ, syracuseStep^[j] 2125 = 1 := reachStep (stepEq 3 (by rfl) ⟨398, by rfl⟩ : syracuseStep 2125 = 797) R797
theorem R2129 : ∃ j : ℕ, syracuseStep^[j] 2129 = 1 := reachStep (stepEq 2 (by rfl) ⟨798, by rfl⟩ : syracuseStep 2129 = 1597) R1597
theorem R2159 : ∃ j : ℕ, syracuseStep^[j] 2159 = 1 := reachStep (stepEq 1 (by rfl) ⟨1619, by rfl⟩ : syracuseStep 2159 = 3239) R3239
theorem R3937 : ∃ j : ℕ, syracuseStep^[j] 3937 = 1 := reachStep (stepEq 2 (by rfl) ⟨1476, by rfl⟩ : syracuseStep 3937 = 2953) R2953
theorem R4065 : ∃ j : ℕ, syracuseStep^[j] 4065 = 1 := reachStep (stepEq 2 (by rfl) ⟨1524, by rfl⟩ : syracuseStep 4065 = 3049) R3049
theorem R4091 : ∃ j : ℕ, syracuseStep^[j] 4091 = 1 := reachStep (stepEq 1 (by rfl) ⟨3068, by rfl⟩ : syracuseStep 4091 = 6137) R6137
theorem R4117 : ∃ j : ℕ, syracuseStep^[j] 4117 = 1 := reachStep (stepEq 6 (by rfl) ⟨96, by rfl⟩ : syracuseStep 4117 = 193) R193
theorem R4131 : ∃ j : ℕ, syracuseStep^[j] 4131 = 1 := reachStep (stepEq 1 (by rfl) ⟨3098, by rfl⟩ : syracuseStep 4131 = 6197) R6197
theorem R4141 : ∃ j : ℕ, syracuseStep^[j] 4141 = 1 := reachStep (stepEq 3 (by rfl) ⟨776, by rfl⟩ : syracuseStep 4141 = 1553) R1553
theorem R4149 : ∃ j : ℕ, syracuseStep^[j] 4149 = 1 := reachStep (stepEq 5 (by rfl) ⟨194, by rfl⟩ : syracuseStep 4149 = 389) R389
theorem R4165 : ∃ j : ℕ, syracuseStep^[j] 4165 = 1 := reachStep (stepEq 4 (by rfl) ⟨390, by rfl⟩ : syracuseStep 4165 = 781) R781
theorem R4171 : ∃ j : ℕ, syracuseStep^[j] 4171 = 1 := reachStep (stepEq 1 (by rfl) ⟨3128, by rfl⟩ : syracuseStep 4171 = 6257) R6257
theorem R4173 : ∃ j : ℕ, syracuseStep^[j] 4173 = 1 := reachStep (stepEq 3 (by rfl) ⟨782, by rfl⟩ : syracuseStep 4173 = 1565) R1565
theorem R4177 : ∃ j : ℕ, syracuseStep^[j] 4177 = 1 := reachStep (stepEq 2 (by rfl) ⟨1566, by rfl⟩ : syracuseStep 4177 = 3133) R3133
theorem R4189 : ∃ j : ℕ, syracuseStep^[j] 4189 = 1 := reachStep (stepEq 3 (by rfl) ⟨785, by rfl⟩ : syracuseStep 4189 = 1571) R1571
theorem R4211 : ∃ j : ℕ, syracuseStep^[j] 4211 = 1 := reachStep (stepEq 1 (by rfl) ⟨3158, by rfl⟩ : syracuseStep 4211 = 6317) R6317
theorem R4245 : ∃ j : ℕ, syracuseStep^[j] 4245 = 1 := reachStep (stepEq 6 (by rfl) ⟨99, by rfl⟩ : syracuseStep 4245 = 199) R199
theorem R4249 : ∃ j : ℕ, syracuseStep^[j] 4249 = 1 := reachStep (stepEq 2 (by rfl) ⟨1593, by rfl⟩ : syracuseStep 4249 = 3187) R3187
theorem R4259 : ∃ j : ℕ, syracuseStep^[j] 4259 = 1 := reachStep (stepEq 1 (by rfl) ⟨3194, by rfl⟩ : syracuseStep 4259 = 6389) R6389
theorem R4263 : ∃ j : ℕ, syracuseStep^[j] 4263 = 1 := reachStep (stepEq 1 (by rfl) ⟨3197, by rfl⟩ : syracuseStep 4263 = 6395) R6395
theorem R4267 : ∃ j : ℕ, syracuseStep^[j] 4267 = 1 := reachStep (stepEq 1 (by rfl) ⟨3200, by rfl⟩ : syracuseStep 4267 = 6401) R6401
theorem R4281 : ∃ j : ℕ, syracuseStep^[j] 4281 = 1 := reachStep (stepEq 2 (by rfl) ⟨1605, by rfl⟩ : syracuseStep 4281 = 3211) R3211
theorem R4283 : ∃ j : ℕ, syracuseStep^[j] 4283 = 1 := reachStep (stepEq 1 (by rfl) ⟨3212, by rfl⟩ : syracuseStep 4283 = 6425) R6425
theorem R4287 : ∃ j : ℕ, syracuseStep^[j] 4287 = 1 := reachStep (stepEq 1 (by rfl) ⟨3215, by rfl⟩ : syracuseStep 4287 = 6431) R6431
theorem R4315 : ∃ j : ℕ, syracuseStep^[j] 4315 = 1 := reachStep (stepEq 1 (by rfl) ⟨3236, by rfl⟩ : syracuseStep 4315 = 6473) R6473
theorem R4319 : ∃ j : ℕ, syracuseStep^[j] 4319 = 1 := reachStep (stepEq 1 (by rfl) ⟨3239, by rfl⟩ : syracuseStep 4319 = 6479) R6479
theorem R4331 : ∃ j : ℕ, syracuseStep^[j] 4331 = 1 := reachStep (stepEq 1 (by rfl) ⟨3248, by rfl⟩ : syracuseStep 4331 = 6497) R6497
theorem R4395 : ∃ j : ℕ, syracuseStep^[j] 4395 = 1 := reachStep (stepEq 1 (by rfl) ⟨3296, by rfl⟩ : syracuseStep 4395 = 6593) R6593
theorem R7847 : ∃ j : ℕ, syracuseStep^[j] 7847 = 1 := reachStep (stepEq 1 (by rfl) ⟨5885, by rfl⟩ : syracuseStep 7847 = 11771) R11771
theorem R7945 : ∃ j : ℕ, syracuseStep^[j] 7945 = 1 := reachStep (stepEq 2 (by rfl) ⟨2979, by rfl⟩ : syracuseStep 7945 = 5959) R5959
theorem R8057 : ∃ j : ℕ, syracuseStep^[j] 8057 = 1 := reachStep (stepEq 2 (by rfl) ⟨3021, by rfl⟩ : syracuseStep 8057 = 6043) R6043
theorem R8183 : ∃ j : ℕ, syracuseStep^[j] 8183 = 1 := reachStep (stepEq 1 (by rfl) ⟨6137, by rfl⟩ : syracuseStep 8183 = 12275) R12275
theorem R8261 : ∃ j : ℕ, syracuseStep^[j] 8261 = 1 := reachStep (stepEq 4 (by rfl) ⟨774, by rfl⟩ : syracuseStep 8261 = 1549) R1549
theorem R8267 : ∃ j : ℕ, syracuseStep^[j] 8267 = 1 := reachStep (stepEq 1 (by rfl) ⟨6200, by rfl⟩ : syracuseStep 8267 = 12401) R12401
theorem R8285 : ∃ j : ℕ, syracuseStep^[j] 8285 = 1 := reachStep (stepEq 3 (by rfl) ⟨1553, by rfl⟩ : syracuseStep 8285 = 3107) R3107
theorem R8303 : ∃ j : ℕ, syracuseStep^[j] 8303 = 1 := reachStep (stepEq 1 (by rfl) ⟨6227, by rfl⟩ : syracuseStep 8303 = 12455) R12455
theorem R8333 : ∃ j : ℕ, syracuseStep^[j] 8333 = 1 := reachStep (stepEq 3 (by rfl) ⟨1562, by rfl⟩ : syracuseStep 8333 = 3125) R3125
theorem R8393 : ∃ j : ℕ, syracuseStep^[j] 8393 = 1 := reachStep (stepEq 2 (by rfl) ⟨3147, by rfl⟩ : syracuseStep 8393 = 6295) R6295
theorem R8501 : ∃ j : ℕ, syracuseStep^[j] 8501 = 1 := reachStep (stepEq 5 (by rfl) ⟨398, by rfl⟩ : syracuseStep 8501 = 797) R797
theorem R8513 : ∃ j : ℕ, syracuseStep^[j] 8513 = 1 := reachStep (stepEq 2 (by rfl) ⟨3192, by rfl⟩ : syracuseStep 8513 = 6385) R6385
theorem R8545 : ∃ j : ℕ, syracuseStep^[j] 8545 = 1 := reachStep (stepEq 2 (by rfl) ⟨3204, by rfl⟩ : syracuseStep 8545 = 6409) R6409
theorem R8567 : ∃ j : ℕ, syracuseStep^[j] 8567 = 1 := reachStep (stepEq 1 (by rfl) ⟨6425, by rfl⟩ : syracuseStep 8567 = 12851) R12851
theorem R8663 : ∃ j : ℕ, syracuseStep^[j] 8663 = 1 := reachStep (stepEq 1 (by rfl) ⟨6497, by rfl⟩ : syracuseStep 8663 = 12995) R12995
theorem R8795 : ∃ j : ℕ, syracuseStep^[j] 8795 = 1 := reachStep (stepEq 1 (by rfl) ⟨6596, by rfl⟩ : syracuseStep 8795 = 13193) R13193
theorem R272645 : ∃ j : ℕ, syracuseStep^[j] 272645 = 1 := reachStep (stepEq 4 (by rfl) ⟨25560, by rfl⟩ : syracuseStep 272645 = 51121) R51121
theorem R1062881 : ∃ j : ℕ, syracuseStep^[j] 1062881 = 1 := reachStep (stepEq 2 (by rfl) ⟨398580, by rfl⟩ : syracuseStep 1062881 = 797161) R797161
theorem R16469 : ∃ j : ℕ, syracuseStep^[j] 16469 = 1 := reachStep (stepEq 8 (by rfl) ⟨96, by rfl⟩ : syracuseStep 16469 = 193) R193
theorem R16685 : ∃ j : ℕ, syracuseStep^[j] 16685 = 1 := reachStep (stepEq 3 (by rfl) ⟨3128, by rfl⟩ : syracuseStep 16685 = 6257) R6257
theorem R16757 : ∃ j : ℕ, syracuseStep^[j] 16757 = 1 := reachStep (stepEq 5 (by rfl) ⟨785, by rfl⟩ : syracuseStep 16757 = 1571) R1571
theorem R16787 : ∃ j : ℕ, syracuseStep^[j] 16787 = 1 := reachStep (stepEq 1 (by rfl) ⟨12590, by rfl⟩ : syracuseStep 16787 = 25181) R25181
theorem R17009 : ∃ j : ℕ, syracuseStep^[j] 17009 = 1 := reachStep (stepEq 2 (by rfl) ⟨6378, by rfl⟩ : syracuseStep 17009 = 12757) R12757
theorem R17069 : ∃ j : ℕ, syracuseStep^[j] 17069 = 1 := reachStep (stepEq 3 (by rfl) ⟨3200, by rfl⟩ : syracuseStep 17069 = 6401) R6401
theorem R17587 : ∃ j : ℕ, syracuseStep^[j] 17587 = 1 := reachStep (stepEq 1 (by rfl) ⟨13190, by rfl⟩ : syracuseStep 17587 = 26381) R26381
theorem R282791 : ∃ j : ℕ, syracuseStep^[j] 282791 = 1 := reachStep (stepEq 1 (by rfl) ⟨212093, by rfl⟩ : syracuseStep 282791 = 424187) R424187
theorem R32525 : ∃ j : ℕ, syracuseStep^[j] 32525 = 1 := reachStep (stepEq 3 (by rfl) ⟨6098, by rfl⟩ : syracuseStep 32525 = 12197) R12197
theorem R171 : ∃ j : ℕ, syracuseStep^[j] 171 = 1 := reachStep (stepEq 1 (by rfl) ⟨128, by rfl⟩ : syracuseStep 171 = 257) R257
theorem R343 : ∃ j : ℕ, syracuseStep^[j] 343 = 1 := reachStep (stepEq 1 (by rfl) ⟨257, by rfl⟩ : syracuseStep 343 = 515) R515
theorem R345 : ∃ j : ℕ, syracuseStep^[j] 345 = 1 := reachStep (stepEq 2 (by rfl) ⟨129, by rfl⟩ : syracuseStep 345 = 259) R259
theorem R347 : ∃ j : ℕ, syracuseStep^[j] 347 = 1 := reachStep (stepEq 1 (by rfl) ⟨260, by rfl⟩ : syracuseStep 347 = 521) R521
theorem R353 : ∃ j : ℕ, syracuseStep^[j] 353 = 1 := reachStep (stepEq 2 (by rfl) ⟨132, by rfl⟩ : syracuseStep 353 = 265) R265
theorem R685 : ∃ j : ℕ, syracuseStep^[j] 685 = 1 := reachStep (stepEq 3 (by rfl) ⟨128, by rfl⟩ : syracuseStep 685 = 257) R257
theorem R689 : ∃ j : ℕ, syracuseStep^[j] 689 = 1 := reachStep (stepEq 2 (by rfl) ⟨258, by rfl⟩ : syracuseStep 689 = 517) R517
theorem R691 : ∃ j : ℕ, syracuseStep^[j] 691 = 1 := reachStep (stepEq 1 (by rfl) ⟨518, by rfl⟩ : syracuseStep 691 = 1037) R1037
theorem R695 : ∃ j : ℕ, syracuseStep^[j] 695 = 1 := reachStep (stepEq 1 (by rfl) ⟨521, by rfl⟩ : syracuseStep 695 = 1043) R1043
theorem R697 : ∃ j : ℕ, syracuseStep^[j] 697 = 1 := reachStep (stepEq 2 (by rfl) ⟨261, by rfl⟩ : syracuseStep 697 = 523) R523
theorem R707 : ∃ j : ℕ, syracuseStep^[j] 707 = 1 := reachStep (stepEq 1 (by rfl) ⟨530, by rfl⟩ : syracuseStep 707 = 1061) R1061
theorem R1373 : ∃ j : ℕ, syracuseStep^[j] 1373 = 1 := reachStep (stepEq 3 (by rfl) ⟨257, by rfl⟩ : syracuseStep 1373 = 515) R515
theorem R1379 : ∃ j : ℕ, syracuseStep^[j] 1379 = 1 := reachStep (stepEq 1 (by rfl) ⟨1034, by rfl⟩ : syracuseStep 1379 = 2069) R2069
theorem R1381 : ∃ j : ℕ, syracuseStep^[j] 1381 = 1 := reachStep (stepEq 4 (by rfl) ⟨129, by rfl⟩ : syracuseStep 1381 = 259) R259
theorem R1389 : ∃ j : ℕ, syracuseStep^[j] 1389 = 1 := reachStep (stepEq 3 (by rfl) ⟨260, by rfl⟩ : syracuseStep 1389 = 521) R521
theorem R1395 : ∃ j : ℕ, syracuseStep^[j] 1395 = 1 := reachStep (stepEq 1 (by rfl) ⟨1046, by rfl⟩ : syracuseStep 1395 = 2093) R2093
theorem R1403 : ∃ j : ℕ, syracuseStep^[j] 1403 = 1 := reachStep (stepEq 1 (by rfl) ⟨1052, by rfl⟩ : syracuseStep 1403 = 2105) R2105
theorem R1413 : ∃ j : ℕ, syracuseStep^[j] 1413 = 1 := reachStep (stepEq 4 (by rfl) ⟨132, by rfl⟩ : syracuseStep 1413 = 265) R265
theorem R1419 : ∃ j : ℕ, syracuseStep^[j] 1419 = 1 := reachStep (stepEq 1 (by rfl) ⟨1064, by rfl⟩ : syracuseStep 1419 = 2129) R2129
theorem R1439 : ∃ j : ℕ, syracuseStep^[j] 1439 = 1 := reachStep (stepEq 1 (by rfl) ⟨1079, by rfl⟩ : syracuseStep 1439 = 2159) R2159
theorem R2727 : ∃ j : ℕ, syracuseStep^[j] 2727 = 1 := reachStep (stepEq 1 (by rfl) ⟨2045, by rfl⟩ : syracuseStep 2727 = 4091) R4091
theorem R2741 : ∃ j : ℕ, syracuseStep^[j] 2741 = 1 := reachStep (stepEq 5 (by rfl) ⟨128, by rfl⟩ : syracuseStep 2741 = 257) R257
theorem R2753 : ∃ j : ℕ, syracuseStep^[j] 2753 = 1 := reachStep (stepEq 2 (by rfl) ⟨1032, by rfl⟩ : syracuseStep 2753 = 2065) R2065
theorem R2757 : ∃ j : ℕ, syracuseStep^[j] 2757 = 1 := reachStep (stepEq 4 (by rfl) ⟨258, by rfl⟩ : syracuseStep 2757 = 517) R517
theorem R2761 : ∃ j : ℕ, syracuseStep^[j] 2761 = 1 := reachStep (stepEq 2 (by rfl) ⟨1035, by rfl⟩ : syracuseStep 2761 = 2071) R2071
theorem R2765 : ∃ j : ℕ, syracuseStep^[j] 2765 = 1 := reachStep (stepEq 3 (by rfl) ⟨518, by rfl⟩ : syracuseStep 2765 = 1037) R1037
theorem R2777 : ∃ j : ℕ, syracuseStep^[j] 2777 = 1 := reachStep (stepEq 2 (by rfl) ⟨1041, by rfl⟩ : syracuseStep 2777 = 2083) R2083
theorem R2781 : ∃ j : ℕ, syracuseStep^[j] 2781 = 1 := reachStep (stepEq 3 (by rfl) ⟨521, by rfl⟩ : syracuseStep 2781 = 1043) R1043
theorem R2789 : ∃ j : ℕ, syracuseStep^[j] 2789 = 1 := reachStep (stepEq 4 (by rfl) ⟨261, by rfl⟩ : syracuseStep 2789 = 523) R523
theorem R2807 : ∃ j : ℕ, syracuseStep^[j] 2807 = 1 := reachStep (stepEq 1 (by rfl) ⟨2105, by rfl⟩ : syracuseStep 2807 = 4211) R4211
theorem R2829 : ∃ j : ℕ, syracuseStep^[j] 2829 = 1 := reachStep (stepEq 3 (by rfl) ⟨530, by rfl⟩ : syracuseStep 2829 = 1061) R1061
theorem R2833 : ∃ j : ℕ, syracuseStep^[j] 2833 = 1 := reachStep (stepEq 2 (by rfl) ⟨1062, by rfl⟩ : syracuseStep 2833 = 2125) R2125
theorem R2839 : ∃ j : ℕ, syracuseStep^[j] 2839 = 1 := reachStep (stepEq 1 (by rfl) ⟨2129, by rfl⟩ : syracuseStep 2839 = 4259) R4259
theorem R2855 : ∃ j : ℕ, syracuseStep^[j] 2855 = 1 := reachStep (stepEq 1 (by rfl) ⟨2141, by rfl⟩ : syracuseStep 2855 = 4283) R4283
theorem R2879 : ∃ j : ℕ, syracuseStep^[j] 2879 = 1 := reachStep (stepEq 1 (by rfl) ⟨2159, by rfl⟩ : syracuseStep 2879 = 4319) R4319
theorem R2887 : ∃ j : ℕ, syracuseStep^[j] 2887 = 1 := reachStep (stepEq 1 (by rfl) ⟨2165, by rfl⟩ : syracuseStep 2887 = 4331) R4331
theorem R5231 : ∃ j : ℕ, syracuseStep^[j] 5231 = 1 := reachStep (stepEq 1 (by rfl) ⟨3923, by rfl⟩ : syracuseStep 5231 = 7847) R7847
theorem R5249 : ∃ j : ℕ, syracuseStep^[j] 5249 = 1 := reachStep (stepEq 2 (by rfl) ⟨1968, by rfl⟩ : syracuseStep 5249 = 3937) R3937
theorem R5371 : ∃ j : ℕ, syracuseStep^[j] 5371 = 1 := reachStep (stepEq 1 (by rfl) ⟨4028, by rfl⟩ : syracuseStep 5371 = 8057) R8057
theorem R5455 : ∃ j : ℕ, syracuseStep^[j] 5455 = 1 := reachStep (stepEq 1 (by rfl) ⟨4091, by rfl⟩ : syracuseStep 5455 = 8183) R8183
theorem R5489 : ∃ j : ℕ, syracuseStep^[j] 5489 = 1 := reachStep (stepEq 2 (by rfl) ⟨2058, by rfl⟩ : syracuseStep 5489 = 4117) R4117
theorem R5493 : ∃ j : ℕ, syracuseStep^[j] 5493 = 1 := reachStep (stepEq 5 (by rfl) ⟨257, by rfl⟩ : syracuseStep 5493 = 515) R515
theorem R5507 : ∃ j : ℕ, syracuseStep^[j] 5507 = 1 := reachStep (stepEq 1 (by rfl) ⟨4130, by rfl⟩ : syracuseStep 5507 = 8261) R8261
theorem R5511 : ∃ j : ℕ, syracuseStep^[j] 5511 = 1 := reachStep (stepEq 1 (by rfl) ⟨4133, by rfl⟩ : syracuseStep 5511 = 8267) R8267
theorem R5517 : ∃ j : ℕ, syracuseStep^[j] 5517 = 1 := reachStep (stepEq 3 (by rfl) ⟨1034, by rfl⟩ : syracuseStep 5517 = 2069) R2069
theorem R5521 : ∃ j : ℕ, syracuseStep^[j] 5521 = 1 := reachStep (stepEq 2 (by rfl) ⟨2070, by rfl⟩ : syracuseStep 5521 = 4141) R4141
theorem R5523 : ∃ j : ℕ, syracuseStep^[j] 5523 = 1 := reachStep (stepEq 1 (by rfl) ⟨4142, by rfl⟩ : syracuseStep 5523 = 8285) R8285
theorem R5525 : ∃ j : ℕ, syracuseStep^[j] 5525 = 1 := reachStep (stepEq 6 (by rfl) ⟨129, by rfl⟩ : syracuseStep 5525 = 259) R259
theorem R5535 : ∃ j : ℕ, syracuseStep^[j] 5535 = 1 := reachStep (stepEq 1 (by rfl) ⟨4151, by rfl⟩ : syracuseStep 5535 = 8303) R8303
theorem R5553 : ∃ j : ℕ, syracuseStep^[j] 5553 = 1 := reachStep (stepEq 2 (by rfl) ⟨2082, by rfl⟩ : syracuseStep 5553 = 4165) R4165
theorem R5555 : ∃ j : ℕ, syracuseStep^[j] 5555 = 1 := reachStep (stepEq 1 (by rfl) ⟨4166, by rfl⟩ : syracuseStep 5555 = 8333) R8333
theorem R5557 : ∃ j : ℕ, syracuseStep^[j] 5557 = 1 := reachStep (stepEq 5 (by rfl) ⟨260, by rfl⟩ : syracuseStep 5557 = 521) R521
theorem R5561 : ∃ j : ℕ, syracuseStep^[j] 5561 = 1 := reachStep (stepEq 2 (by rfl) ⟨2085, by rfl⟩ : syracuseStep 5561 = 4171) R4171
theorem R5569 : ∃ j : ℕ, syracuseStep^[j] 5569 = 1 := reachStep (stepEq 2 (by rfl) ⟨2088, by rfl⟩ : syracuseStep 5569 = 4177) R4177
theorem R5581 : ∃ j : ℕ, syracuseStep^[j] 5581 = 1 := reachStep (stepEq 3 (by rfl) ⟨1046, by rfl⟩ : syracuseStep 5581 = 2093) R2093
theorem R5585 : ∃ j : ℕ, syracuseStep^[j] 5585 = 1 := reachStep (stepEq 2 (by rfl) ⟨2094, by rfl⟩ : syracuseStep 5585 = 4189) R4189
theorem R5595 : ∃ j : ℕ, syracuseStep^[j] 5595 = 1 := reachStep (stepEq 1 (by rfl) ⟨4196, by rfl⟩ : syracuseStep 5595 = 8393) R8393
theorem R5613 : ∃ j : ℕ, syracuseStep^[j] 5613 = 1 := reachStep (stepEq 3 (by rfl) ⟨1052, by rfl⟩ : syracuseStep 5613 = 2105) R2105
theorem R5653 : ∃ j : ℕ, syracuseStep^[j] 5653 = 1 := reachStep (stepEq 6 (by rfl) ⟨132, by rfl⟩ : syracuseStep 5653 = 265) R265
theorem R5665 : ∃ j : ℕ, syracuseStep^[j] 5665 = 1 := reachStep (stepEq 2 (by rfl) ⟨2124, by rfl⟩ : syracuseStep 5665 = 4249) R4249
theorem R5667 : ∃ j : ℕ, syracuseStep^[j] 5667 = 1 := reachStep (stepEq 1 (by rfl) ⟨4250, by rfl⟩ : syracuseStep 5667 = 8501) R8501
theorem R5675 : ∃ j : ℕ, syracuseStep^[j] 5675 = 1 := reachStep (stepEq 1 (by rfl) ⟨4256, by rfl⟩ : syracuseStep 5675 = 8513) R8513
theorem R5677 : ∃ j : ℕ, syracuseStep^[j] 5677 = 1 := reachStep (stepEq 3 (by rfl) ⟨1064, by rfl⟩ : syracuseStep 5677 = 2129) R2129
theorem R5689 : ∃ j : ℕ, syracuseStep^[j] 5689 = 1 := reachStep (stepEq 2 (by rfl) ⟨2133, by rfl⟩ : syracuseStep 5689 = 4267) R4267
theorem R5711 : ∃ j : ℕ, syracuseStep^[j] 5711 = 1 := reachStep (stepEq 1 (by rfl) ⟨4283, by rfl⟩ : syracuseStep 5711 = 8567) R8567
theorem R5753 : ∃ j : ℕ, syracuseStep^[j] 5753 = 1 := reachStep (stepEq 2 (by rfl) ⟨2157, by rfl⟩ : syracuseStep 5753 = 4315) R4315
theorem R5757 : ∃ j : ℕ, syracuseStep^[j] 5757 = 1 := reachStep (stepEq 3 (by rfl) ⟨1079, by rfl⟩ : syracuseStep 5757 = 2159) R2159
theorem R5775 : ∃ j : ℕ, syracuseStep^[j] 5775 = 1 := reachStep (stepEq 1 (by rfl) ⟨4331, by rfl⟩ : syracuseStep 5775 = 8663) R8663
theorem R5863 : ∃ j : ℕ, syracuseStep^[j] 5863 = 1 := reachStep (stepEq 1 (by rfl) ⟨4397, by rfl⟩ : syracuseStep 5863 = 8795) R8795
theorem R42373 : ∃ j : ℕ, syracuseStep^[j] 42373 = 1 := reachStep (stepEq 4 (by rfl) ⟨3972, by rfl⟩ : syracuseStep 42373 = 7945) R7945
theorem R10979 : ∃ j : ℕ, syracuseStep^[j] 10979 = 1 := reachStep (stepEq 1 (by rfl) ⟨8234, by rfl⟩ : syracuseStep 10979 = 16469) R16469
theorem R11029 : ∃ j : ℕ, syracuseStep^[j] 11029 = 1 := reachStep (stepEq 6 (by rfl) ⟨258, by rfl⟩ : syracuseStep 11029 = 517) R517
theorem R11123 : ∃ j : ℕ, syracuseStep^[j] 11123 = 1 := reachStep (stepEq 1 (by rfl) ⟨8342, by rfl⟩ : syracuseStep 11123 = 16685) R16685
theorem R11171 : ∃ j : ℕ, syracuseStep^[j] 11171 = 1 := reachStep (stepEq 1 (by rfl) ⟨8378, by rfl⟩ : syracuseStep 11171 = 16757) R16757
theorem R11191 : ∃ j : ℕ, syracuseStep^[j] 11191 = 1 := reachStep (stepEq 1 (by rfl) ⟨8393, by rfl⟩ : syracuseStep 11191 = 16787) R16787
theorem R11333 : ∃ j : ℕ, syracuseStep^[j] 11333 = 1 := reachStep (stepEq 4 (by rfl) ⟨1062, by rfl⟩ : syracuseStep 11333 = 2125) R2125
theorem R11339 : ∃ j : ℕ, syracuseStep^[j] 11339 = 1 := reachStep (stepEq 1 (by rfl) ⟨8504, by rfl⟩ : syracuseStep 11339 = 17009) R17009
theorem R11357 : ∃ j : ℕ, syracuseStep^[j] 11357 = 1 := reachStep (stepEq 3 (by rfl) ⟨2129, by rfl⟩ : syracuseStep 11357 = 4259) R4259
theorem R11393 : ∃ j : ℕ, syracuseStep^[j] 11393 = 1 := reachStep (stepEq 2 (by rfl) ⟨4272, by rfl⟩ : syracuseStep 11393 = 8545) R8545
theorem R44225 : ∃ j : ℕ, syracuseStep^[j] 44225 = 1 := reachStep (stepEq 2 (by rfl) ⟨16584, by rfl⟩ : syracuseStep 44225 = 33169) R33169
theorem R45517 : ∃ j : ℕ, syracuseStep^[j] 45517 = 1 := reachStep (stepEq 3 (by rfl) ⟨8534, by rfl⟩ : syracuseStep 45517 = 17069) R17069
theorem R181763 : ∃ j : ℕ, syracuseStep^[j] 181763 = 1 := reachStep (stepEq 1 (by rfl) ⟨136322, by rfl⟩ : syracuseStep 181763 = 272645) R272645
theorem R708587 : ∃ j : ℕ, syracuseStep^[j] 708587 = 1 := reachStep (stepEq 1 (by rfl) ⟨531440, by rfl⟩ : syracuseStep 708587 = 1062881) R1062881
theorem R21683 : ∃ j : ℕ, syracuseStep^[j] 21683 = 1 := reachStep (stepEq 1 (by rfl) ⟨16262, by rfl⟩ : syracuseStep 21683 = 32525) R32525
theorem R22085 : ∃ j : ℕ, syracuseStep^[j] 22085 = 1 := reachStep (stepEq 4 (by rfl) ⟨2070, by rfl⟩ : syracuseStep 22085 = 4141) R4141
theorem R22679 : ∃ j : ℕ, syracuseStep^[j] 22679 = 1 := reachStep (stepEq 1 (by rfl) ⟨17009, by rfl⟩ : syracuseStep 22679 = 34019) R34019
theorem R22771 : ∃ j : ℕ, syracuseStep^[j] 22771 = 1 := reachStep (stepEq 1 (by rfl) ⟨17078, by rfl⟩ : syracuseStep 22771 = 34157) R34157
theorem R88573 : ∃ j : ℕ, syracuseStep^[j] 88573 = 1 := reachStep (stepEq 3 (by rfl) ⟨16607, by rfl⟩ : syracuseStep 88573 = 33215) R33215
theorem R23449 : ∃ j : ℕ, syracuseStep^[j] 23449 = 1 := reachStep (stepEq 2 (by rfl) ⟨8793, by rfl⟩ : syracuseStep 23449 = 17587) R17587
theorem R188527 : ∃ j : ℕ, syracuseStep^[j] 188527 = 1 := reachStep (stepEq 1 (by rfl) ⟨141395, by rfl⟩ : syracuseStep 188527 = 282791) R282791
theorem R354293 : ∃ j : ℕ, syracuseStep^[j] 354293 = 1 := reachStep (stepEq 5 (by rfl) ⟨16607, by rfl⟩ : syracuseStep 354293 = 33215) R33215
theorem R231 : ∃ j : ℕ, syracuseStep^[j] 231 = 1 := reachStep (stepEq 1 (by rfl) ⟨173, by rfl⟩ : syracuseStep 231 = 347) R347
theorem R235 : ∃ j : ℕ, syracuseStep^[j] 235 = 1 := reachStep (stepEq 1 (by rfl) ⟨176, by rfl⟩ : syracuseStep 235 = 353) R353
theorem R457 : ∃ j : ℕ, syracuseStep^[j] 457 = 1 := reachStep (stepEq 2 (by rfl) ⟨171, by rfl⟩ : syracuseStep 457 = 343) R343
theorem R459 : ∃ j : ℕ, syracuseStep^[j] 459 = 1 := reachStep (stepEq 1 (by rfl) ⟨344, by rfl⟩ : syracuseStep 459 = 689) R689
theorem R463 : ∃ j : ℕ, syracuseStep^[j] 463 = 1 := reachStep (stepEq 1 (by rfl) ⟨347, by rfl⟩ : syracuseStep 463 = 695) R695
theorem R471 : ∃ j : ℕ, syracuseStep^[j] 471 = 1 := reachStep (stepEq 1 (by rfl) ⟨353, by rfl⟩ : syracuseStep 471 = 707) R707
theorem R913 : ∃ j : ℕ, syracuseStep^[j] 913 = 1 := reachStep (stepEq 2 (by rfl) ⟨342, by rfl⟩ : syracuseStep 913 = 685) R685
theorem R915 : ∃ j : ℕ, syracuseStep^[j] 915 = 1 := reachStep (stepEq 1 (by rfl) ⟨686, by rfl⟩ : syracuseStep 915 = 1373) R1373
theorem R919 : ∃ j : ℕ, syracuseStep^[j] 919 = 1 := reachStep (stepEq 1 (by rfl) ⟨689, by rfl⟩ : syracuseStep 919 = 1379) R1379
theorem R921 : ∃ j : ℕ, syracuseStep^[j] 921 = 1 := reachStep (stepEq 2 (by rfl) ⟨345, by rfl⟩ : syracuseStep 921 = 691) R691
theorem R925 : ∃ j : ℕ, syracuseStep^[j] 925 = 1 := reachStep (stepEq 3 (by rfl) ⟨173, by rfl⟩ : syracuseStep 925 = 347) R347
theorem R929 : ∃ j : ℕ, syracuseStep^[j] 929 = 1 := reachStep (stepEq 2 (by rfl) ⟨348, by rfl⟩ : syracuseStep 929 = 697) R697
theorem R935 : ∃ j : ℕ, syracuseStep^[j] 935 = 1 := reachStep (stepEq 1 (by rfl) ⟨701, by rfl⟩ : syracuseStep 935 = 1403) R1403
theorem R941 : ∃ j : ℕ, syracuseStep^[j] 941 = 1 := reachStep (stepEq 3 (by rfl) ⟨176, by rfl⟩ : syracuseStep 941 = 353) R353
theorem R959 : ∃ j : ℕ, syracuseStep^[j] 959 = 1 := reachStep (stepEq 1 (by rfl) ⟨719, by rfl⟩ : syracuseStep 959 = 1439) R1439
theorem R1827 : ∃ j : ℕ, syracuseStep^[j] 1827 = 1 := reachStep (stepEq 1 (by rfl) ⟨1370, by rfl⟩ : syracuseStep 1827 = 2741) R2741
theorem R1829 : ∃ j : ℕ, syracuseStep^[j] 1829 = 1 := reachStep (stepEq 4 (by rfl) ⟨171, by rfl⟩ : syracuseStep 1829 = 343) R343
theorem R1835 : ∃ j : ℕ, syracuseStep^[j] 1835 = 1 := reachStep (stepEq 1 (by rfl) ⟨1376, by rfl⟩ : syracuseStep 1835 = 2753) R2753
theorem R1837 : ∃ j : ℕ, syracuseStep^[j] 1837 = 1 := reachStep (stepEq 3 (by rfl) ⟨344, by rfl⟩ : syracuseStep 1837 = 689) R689
theorem R1841 : ∃ j : ℕ, syracuseStep^[j] 1841 = 1 := reachStep (stepEq 2 (by rfl) ⟨690, by rfl⟩ : syracuseStep 1841 = 1381) R1381
theorem R1843 : ∃ j : ℕ, syracuseStep^[j] 1843 = 1 := reachStep (stepEq 1 (by rfl) ⟨1382, by rfl⟩ : syracuseStep 1843 = 2765) R2765
theorem R1851 : ∃ j : ℕ, syracuseStep^[j] 1851 = 1 := reachStep (stepEq 1 (by rfl) ⟨1388, by rfl⟩ : syracuseStep 1851 = 2777) R2777
theorem R1853 : ∃ j : ℕ, syracuseStep^[j] 1853 = 1 := reachStep (stepEq 3 (by rfl) ⟨347, by rfl⟩ : syracuseStep 1853 = 695) R695
theorem R1859 : ∃ j : ℕ, syracuseStep^[j] 1859 = 1 := reachStep (stepEq 1 (by rfl) ⟨1394, by rfl⟩ : syracuseStep 1859 = 2789) R2789
theorem R1871 : ∃ j : ℕ, syracuseStep^[j] 1871 = 1 := reachStep (stepEq 1 (by rfl) ⟨1403, by rfl⟩ : syracuseStep 1871 = 2807) R2807
theorem R1885 : ∃ j : ℕ, syracuseStep^[j] 1885 = 1 := reachStep (stepEq 3 (by rfl) ⟨353, by rfl⟩ : syracuseStep 1885 = 707) R707
theorem R1903 : ∃ j : ℕ, syracuseStep^[j] 1903 = 1 := reachStep (stepEq 1 (by rfl) ⟨1427, by rfl⟩ : syracuseStep 1903 = 2855) R2855
theorem R1919 : ∃ j : ℕ, syracuseStep^[j] 1919 = 1 := reachStep (stepEq 1 (by rfl) ⟨1439, by rfl⟩ : syracuseStep 1919 = 2879) R2879
theorem R3487 : ∃ j : ℕ, syracuseStep^[j] 3487 = 1 := reachStep (stepEq 1 (by rfl) ⟨2615, by rfl⟩ : syracuseStep 3487 = 5231) R5231
theorem R3499 : ∃ j : ℕ, syracuseStep^[j] 3499 = 1 := reachStep (stepEq 1 (by rfl) ⟨2624, by rfl⟩ : syracuseStep 3499 = 5249) R5249
theorem R3653 : ∃ j : ℕ, syracuseStep^[j] 3653 = 1 := reachStep (stepEq 4 (by rfl) ⟨342, by rfl⟩ : syracuseStep 3653 = 685) R685
theorem R3659 : ∃ j : ℕ, syracuseStep^[j] 3659 = 1 := reachStep (stepEq 1 (by rfl) ⟨2744, by rfl⟩ : syracuseStep 3659 = 5489) R5489
theorem R3661 : ∃ j : ℕ, syracuseStep^[j] 3661 = 1 := reachStep (stepEq 3 (by rfl) ⟨686, by rfl⟩ : syracuseStep 3661 = 1373) R1373
theorem R3671 : ∃ j : ℕ, syracuseStep^[j] 3671 = 1 := reachStep (stepEq 1 (by rfl) ⟨2753, by rfl⟩ : syracuseStep 3671 = 5507) R5507
theorem R3677 : ∃ j : ℕ, syracuseStep^[j] 3677 = 1 := reachStep (stepEq 3 (by rfl) ⟨689, by rfl⟩ : syracuseStep 3677 = 1379) R1379
theorem R3681 : ∃ j : ℕ, syracuseStep^[j] 3681 = 1 := reachStep (stepEq 2 (by rfl) ⟨1380, by rfl⟩ : syracuseStep 3681 = 2761) R2761
theorem R3683 : ∃ j : ℕ, syracuseStep^[j] 3683 = 1 := reachStep (stepEq 1 (by rfl) ⟨2762, by rfl⟩ : syracuseStep 3683 = 5525) R5525
theorem R3685 : ∃ j : ℕ, syracuseStep^[j] 3685 = 1 := reachStep (stepEq 4 (by rfl) ⟨345, by rfl⟩ : syracuseStep 3685 = 691) R691
theorem R3701 : ∃ j : ℕ, syracuseStep^[j] 3701 = 1 := reachStep (stepEq 5 (by rfl) ⟨173, by rfl⟩ : syracuseStep 3701 = 347) R347
theorem R3703 : ∃ j : ℕ, syracuseStep^[j] 3703 = 1 := reachStep (stepEq 1 (by rfl) ⟨2777, by rfl⟩ : syracuseStep 3703 = 5555) R5555
theorem R3707 : ∃ j : ℕ, syracuseStep^[j] 3707 = 1 := reachStep (stepEq 1 (by rfl) ⟨2780, by rfl⟩ : syracuseStep 3707 = 5561) R5561
theorem R3717 : ∃ j : ℕ, syracuseStep^[j] 3717 = 1 := reachStep (stepEq 4 (by rfl) ⟨348, by rfl⟩ : syracuseStep 3717 = 697) R697
theorem R3723 : ∃ j : ℕ, syracuseStep^[j] 3723 = 1 := reachStep (stepEq 1 (by rfl) ⟨2792, by rfl⟩ : syracuseStep 3723 = 5585) R5585
theorem R3741 : ∃ j : ℕ, syracuseStep^[j] 3741 = 1 := reachStep (stepEq 3 (by rfl) ⟨701, by rfl⟩ : syracuseStep 3741 = 1403) R1403
theorem R3765 : ∃ j : ℕ, syracuseStep^[j] 3765 = 1 := reachStep (stepEq 5 (by rfl) ⟨176, by rfl⟩ : syracuseStep 3765 = 353) R353
theorem R3777 : ∃ j : ℕ, syracuseStep^[j] 3777 = 1 := reachStep (stepEq 2 (by rfl) ⟨1416, by rfl⟩ : syracuseStep 3777 = 2833) R2833
theorem R3783 : ∃ j : ℕ, syracuseStep^[j] 3783 = 1 := reachStep (stepEq 1 (by rfl) ⟨2837, by rfl⟩ : syracuseStep 3783 = 5675) R5675
theorem R3785 : ∃ j : ℕ, syracuseStep^[j] 3785 = 1 := reachStep (stepEq 2 (by rfl) ⟨1419, by rfl⟩ : syracuseStep 3785 = 2839) R2839
theorem R3807 : ∃ j : ℕ, syracuseStep^[j] 3807 = 1 := reachStep (stepEq 1 (by rfl) ⟨2855, by rfl⟩ : syracuseStep 3807 = 5711) R5711
theorem R3835 : ∃ j : ℕ, syracuseStep^[j] 3835 = 1 := reachStep (stepEq 1 (by rfl) ⟨2876, by rfl⟩ : syracuseStep 3835 = 5753) R5753
theorem R3837 : ∃ j : ℕ, syracuseStep^[j] 3837 = 1 := reachStep (stepEq 3 (by rfl) ⟨719, by rfl⟩ : syracuseStep 3837 = 1439) R1439
theorem R3849 : ∃ j : ℕ, syracuseStep^[j] 3849 = 1 := reachStep (stepEq 2 (by rfl) ⟨1443, by rfl⟩ : syracuseStep 3849 = 2887) R2887
theorem R236195 : ∃ j : ℕ, syracuseStep^[j] 236195 = 1 := reachStep (stepEq 1 (by rfl) ⟨177146, by rfl⟩ : syracuseStep 236195 = 354293) R354293
theorem R7319 : ∃ j : ℕ, syracuseStep^[j] 7319 = 1 := reachStep (stepEq 1 (by rfl) ⟨5489, by rfl⟩ : syracuseStep 7319 = 10979) R10979
theorem R7349 : ∃ j : ℕ, syracuseStep^[j] 7349 = 1 := reachStep (stepEq 5 (by rfl) ⟨344, by rfl⟩ : syracuseStep 7349 = 689) R689
theorem R7361 : ∃ j : ℕ, syracuseStep^[j] 7361 = 1 := reachStep (stepEq 2 (by rfl) ⟨2760, by rfl⟩ : syracuseStep 7361 = 5521) R5521
theorem R7373 : ∃ j : ℕ, syracuseStep^[j] 7373 = 1 := reachStep (stepEq 3 (by rfl) ⟨1382, by rfl⟩ : syracuseStep 7373 = 2765) R2765
theorem R7409 : ∃ j : ℕ, syracuseStep^[j] 7409 = 1 := reachStep (stepEq 2 (by rfl) ⟨2778, by rfl⟩ : syracuseStep 7409 = 5557) R5557
theorem R7415 : ∃ j : ℕ, syracuseStep^[j] 7415 = 1 := reachStep (stepEq 1 (by rfl) ⟨5561, by rfl⟩ : syracuseStep 7415 = 11123) R11123
theorem R7447 : ∃ j : ℕ, syracuseStep^[j] 7447 = 1 := reachStep (stepEq 1 (by rfl) ⟨5585, by rfl⟩ : syracuseStep 7447 = 11171) R11171
theorem R7537 : ∃ j : ℕ, syracuseStep^[j] 7537 = 1 := reachStep (stepEq 2 (by rfl) ⟨2826, by rfl⟩ : syracuseStep 7537 = 5653) R5653
theorem R7541 : ∃ j : ℕ, syracuseStep^[j] 7541 = 1 := reachStep (stepEq 5 (by rfl) ⟨353, by rfl⟩ : syracuseStep 7541 = 707) R707
theorem R7553 : ∃ j : ℕ, syracuseStep^[j] 7553 = 1 := reachStep (stepEq 2 (by rfl) ⟨2832, by rfl⟩ : syracuseStep 7553 = 5665) R5665
theorem R7555 : ∃ j : ℕ, syracuseStep^[j] 7555 = 1 := reachStep (stepEq 1 (by rfl) ⟨5666, by rfl⟩ : syracuseStep 7555 = 11333) R11333
theorem R7559 : ∃ j : ℕ, syracuseStep^[j] 7559 = 1 := reachStep (stepEq 1 (by rfl) ⟨5669, by rfl⟩ : syracuseStep 7559 = 11339) R11339
theorem R7571 : ∃ j : ℕ, syracuseStep^[j] 7571 = 1 := reachStep (stepEq 1 (by rfl) ⟨5678, by rfl⟩ : syracuseStep 7571 = 11357) R11357
theorem R7595 : ∃ j : ℕ, syracuseStep^[j] 7595 = 1 := reachStep (stepEq 1 (by rfl) ⟨5696, by rfl⟩ : syracuseStep 7595 = 11393) R11393
theorem R7613 : ∃ j : ℕ, syracuseStep^[j] 7613 = 1 := reachStep (stepEq 3 (by rfl) ⟨1427, by rfl⟩ : syracuseStep 7613 = 2855) R2855
theorem R7817 : ∃ j : ℕ, syracuseStep^[j] 7817 = 1 := reachStep (stepEq 2 (by rfl) ⟨2931, by rfl⟩ : syracuseStep 7817 = 5863) R5863
theorem R472391 : ∃ j : ℕ, syracuseStep^[j] 472391 = 1 := reachStep (stepEq 1 (by rfl) ⟨354293, by rfl⟩ : syracuseStep 472391 = 708587) R708587
theorem R13949 : ∃ j : ℕ, syracuseStep^[j] 13949 = 1 := reachStep (stepEq 3 (by rfl) ⟨2615, by rfl⟩ : syracuseStep 13949 = 5231) R5231
theorem R14455 : ∃ j : ℕ, syracuseStep^[j] 14455 = 1 := reachStep (stepEq 1 (by rfl) ⟨10841, by rfl⟩ : syracuseStep 14455 = 21683) R21683
theorem R14705 : ∃ j : ℕ, syracuseStep^[j] 14705 = 1 := reachStep (stepEq 2 (by rfl) ⟨5514, by rfl⟩ : syracuseStep 14705 = 11029) R11029
theorem R14723 : ∃ j : ℕ, syracuseStep^[j] 14723 = 1 := reachStep (stepEq 1 (by rfl) ⟨11042, by rfl⟩ : syracuseStep 14723 = 22085) R22085
theorem R14741 : ∃ j : ℕ, syracuseStep^[j] 14741 = 1 := reachStep (stepEq 6 (by rfl) ⟨345, by rfl⟩ : syracuseStep 14741 = 691) R691
theorem R14813 : ∃ j : ℕ, syracuseStep^[j] 14813 = 1 := reachStep (stepEq 3 (by rfl) ⟨2777, by rfl⟩ : syracuseStep 14813 = 5555) R5555
theorem R14921 : ∃ j : ℕ, syracuseStep^[j] 14921 = 1 := reachStep (stepEq 2 (by rfl) ⟨5595, by rfl⟩ : syracuseStep 14921 = 11191) R11191
theorem R15119 : ∃ j : ℕ, syracuseStep^[j] 15119 = 1 := reachStep (stepEq 1 (by rfl) ⟨11339, by rfl⟩ : syracuseStep 15119 = 22679) R22679
theorem R15349 : ∃ j : ℕ, syracuseStep^[j] 15349 = 1 := reachStep (stepEq 5 (by rfl) ⟨719, by rfl⟩ : syracuseStep 15349 = 1439) R1439
theorem R118097 : ∃ j : ℕ, syracuseStep^[j] 118097 = 1 := reachStep (stepEq 2 (by rfl) ⟨44286, by rfl⟩ : syracuseStep 118097 = 88573) R88573
theorem R251369 : ∃ j : ℕ, syracuseStep^[j] 251369 = 1 := reachStep (stepEq 2 (by rfl) ⟨94263, by rfl⟩ : syracuseStep 251369 = 188527) R188527
theorem R121175 : ∃ j : ℕ, syracuseStep^[j] 121175 = 1 := reachStep (stepEq 1 (by rfl) ⟨90881, by rfl⟩ : syracuseStep 121175 = 181763) R181763
theorem R121445 : ∃ j : ℕ, syracuseStep^[j] 121445 = 1 := reachStep (stepEq 4 (by rfl) ⟨11385, by rfl⟩ : syracuseStep 121445 = 22771) R22771
theorem R56497 : ∃ j : ℕ, syracuseStep^[j] 56497 = 1 := reachStep (stepEq 2 (by rfl) ⟨21186, by rfl⟩ : syracuseStep 56497 = 42373) R42373
theorem R60689 : ∃ j : ℕ, syracuseStep^[j] 60689 = 1 := reachStep (stepEq 2 (by rfl) ⟨22758, by rfl⟩ : syracuseStep 60689 = 45517) R45517
theorem R29483 : ∃ j : ℕ, syracuseStep^[j] 29483 = 1 := reachStep (stepEq 1 (by rfl) ⟨22112, by rfl⟩ : syracuseStep 29483 = 44225) R44225
theorem R30709 : ∃ j : ℕ, syracuseStep^[j] 30709 = 1 := reachStep (stepEq 5 (by rfl) ⟨1439, by rfl⟩ : syracuseStep 30709 = 2879) R2879
theorem R31265 : ∃ j : ℕ, syracuseStep^[j] 31265 = 1 := reachStep (stepEq 2 (by rfl) ⟨11724, by rfl⟩ : syracuseStep 31265 = 23449) R23449
theorem R313 : ∃ j : ℕ, syracuseStep^[j] 313 = 1 := reachStep (stepEq 2 (by rfl) ⟨117, by rfl⟩ : syracuseStep 313 = 235) R235
theorem R609 : ∃ j : ℕ, syracuseStep^[j] 609 = 1 := reachStep (stepEq 2 (by rfl) ⟨228, by rfl⟩ : syracuseStep 609 = 457) R457
theorem R617 : ∃ j : ℕ, syracuseStep^[j] 617 = 1 := reachStep (stepEq 2 (by rfl) ⟨231, by rfl⟩ : syracuseStep 617 = 463) R463
theorem R619 : ∃ j : ℕ, syracuseStep^[j] 619 = 1 := reachStep (stepEq 1 (by rfl) ⟨464, by rfl⟩ : syracuseStep 619 = 929) R929
theorem R623 : ∃ j : ℕ, syracuseStep^[j] 623 = 1 := reachStep (stepEq 1 (by rfl) ⟨467, by rfl⟩ : syracuseStep 623 = 935) R935
theorem R627 : ∃ j : ℕ, syracuseStep^[j] 627 = 1 := reachStep (stepEq 1 (by rfl) ⟨470, by rfl⟩ : syracuseStep 627 = 941) R941
theorem R639 : ∃ j : ℕ, syracuseStep^[j] 639 = 1 := reachStep (stepEq 1 (by rfl) ⟨479, by rfl⟩ : syracuseStep 639 = 959) R959
theorem R1217 : ∃ j : ℕ, syracuseStep^[j] 1217 = 1 := reachStep (stepEq 2 (by rfl) ⟨456, by rfl⟩ : syracuseStep 1217 = 913) R913
theorem R1219 : ∃ j : ℕ, syracuseStep^[j] 1219 = 1 := reachStep (stepEq 1 (by rfl) ⟨914, by rfl⟩ : syracuseStep 1219 = 1829) R1829
theorem R1223 : ∃ j : ℕ, syracuseStep^[j] 1223 = 1 := reachStep (stepEq 1 (by rfl) ⟨917, by rfl⟩ : syracuseStep 1223 = 1835) R1835
theorem R1225 : ∃ j : ℕ, syracuseStep^[j] 1225 = 1 := reachStep (stepEq 2 (by rfl) ⟨459, by rfl⟩ : syracuseStep 1225 = 919) R919
theorem R1227 : ∃ j : ℕ, syracuseStep^[j] 1227 = 1 := reachStep (stepEq 1 (by rfl) ⟨920, by rfl⟩ : syracuseStep 1227 = 1841) R1841
theorem R1233 : ∃ j : ℕ, syracuseStep^[j] 1233 = 1 := reachStep (stepEq 2 (by rfl) ⟨462, by rfl⟩ : syracuseStep 1233 = 925) R925
theorem R1235 : ∃ j : ℕ, syracuseStep^[j] 1235 = 1 := reachStep (stepEq 1 (by rfl) ⟨926, by rfl⟩ : syracuseStep 1235 = 1853) R1853
theorem R1239 : ∃ j : ℕ, syracuseStep^[j] 1239 = 1 := reachStep (stepEq 1 (by rfl) ⟨929, by rfl⟩ : syracuseStep 1239 = 1859) R1859
theorem R1247 : ∃ j : ℕ, syracuseStep^[j] 1247 = 1 := reachStep (stepEq 1 (by rfl) ⟨935, by rfl⟩ : syracuseStep 1247 = 1871) R1871
theorem R1253 : ∃ j : ℕ, syracuseStep^[j] 1253 = 1 := reachStep (stepEq 4 (by rfl) ⟨117, by rfl⟩ : syracuseStep 1253 = 235) R235
theorem R1279 : ∃ j : ℕ, syracuseStep^[j] 1279 = 1 := reachStep (stepEq 1 (by rfl) ⟨959, by rfl⟩ : syracuseStep 1279 = 1919) R1919
theorem R2435 : ∃ j : ℕ, syracuseStep^[j] 2435 = 1 := reachStep (stepEq 1 (by rfl) ⟨1826, by rfl⟩ : syracuseStep 2435 = 3653) R3653
theorem R2437 : ∃ j : ℕ, syracuseStep^[j] 2437 = 1 := reachStep (stepEq 4 (by rfl) ⟨228, by rfl⟩ : syracuseStep 2437 = 457) R457
theorem R2439 : ∃ j : ℕ, syracuseStep^[j] 2439 = 1 := reachStep (stepEq 1 (by rfl) ⟨1829, by rfl⟩ : syracuseStep 2439 = 3659) R3659
theorem R2447 : ∃ j : ℕ, syracuseStep^[j] 2447 = 1 := reachStep (stepEq 1 (by rfl) ⟨1835, by rfl⟩ : syracuseStep 2447 = 3671) R3671
theorem R2449 : ∃ j : ℕ, syracuseStep^[j] 2449 = 1 := reachStep (stepEq 2 (by rfl) ⟨918, by rfl⟩ : syracuseStep 2449 = 1837) R1837
theorem R2451 : ∃ j : ℕ, syracuseStep^[j] 2451 = 1 := reachStep (stepEq 1 (by rfl) ⟨1838, by rfl⟩ : syracuseStep 2451 = 3677) R3677
theorem R2455 : ∃ j : ℕ, syracuseStep^[j] 2455 = 1 := reachStep (stepEq 1 (by rfl) ⟨1841, by rfl⟩ : syracuseStep 2455 = 3683) R3683
theorem R2457 : ∃ j : ℕ, syracuseStep^[j] 2457 = 1 := reachStep (stepEq 2 (by rfl) ⟨921, by rfl⟩ : syracuseStep 2457 = 1843) R1843
theorem R2467 : ∃ j : ℕ, syracuseStep^[j] 2467 = 1 := reachStep (stepEq 1 (by rfl) ⟨1850, by rfl⟩ : syracuseStep 2467 = 3701) R3701
theorem R2469 : ∃ j : ℕ, syracuseStep^[j] 2469 = 1 := reachStep (stepEq 4 (by rfl) ⟨231, by rfl⟩ : syracuseStep 2469 = 463) R463
theorem R2471 : ∃ j : ℕ, syracuseStep^[j] 2471 = 1 := reachStep (stepEq 1 (by rfl) ⟨1853, by rfl⟩ : syracuseStep 2471 = 3707) R3707
theorem R2477 : ∃ j : ℕ, syracuseStep^[j] 2477 = 1 := reachStep (stepEq 3 (by rfl) ⟨464, by rfl⟩ : syracuseStep 2477 = 929) R929
theorem R2493 : ∃ j : ℕ, syracuseStep^[j] 2493 = 1 := reachStep (stepEq 3 (by rfl) ⟨467, by rfl⟩ : syracuseStep 2493 = 935) R935
theorem R2509 : ∃ j : ℕ, syracuseStep^[j] 2509 = 1 := reachStep (stepEq 3 (by rfl) ⟨470, by rfl⟩ : syracuseStep 2509 = 941) R941
theorem R2513 : ∃ j : ℕ, syracuseStep^[j] 2513 = 1 := reachStep (stepEq 2 (by rfl) ⟨942, by rfl⟩ : syracuseStep 2513 = 1885) R1885
theorem R2523 : ∃ j : ℕ, syracuseStep^[j] 2523 = 1 := reachStep (stepEq 1 (by rfl) ⟨1892, by rfl⟩ : syracuseStep 2523 = 3785) R3785
theorem R2537 : ∃ j : ℕ, syracuseStep^[j] 2537 = 1 := reachStep (stepEq 2 (by rfl) ⟨951, by rfl⟩ : syracuseStep 2537 = 1903) R1903
theorem R2557 : ∃ j : ℕ, syracuseStep^[j] 2557 = 1 := reachStep (stepEq 3 (by rfl) ⟨479, by rfl⟩ : syracuseStep 2557 = 959) R959
theorem R167579 : ∃ j : ℕ, syracuseStep^[j] 167579 = 1 := reachStep (stepEq 1 (by rfl) ⟨125684, by rfl⟩ : syracuseStep 167579 = 251369) R251369
theorem R4649 : ∃ j : ℕ, syracuseStep^[j] 4649 = 1 := reachStep (stepEq 2 (by rfl) ⟨1743, by rfl⟩ : syracuseStep 4649 = 3487) R3487
theorem R4665 : ∃ j : ℕ, syracuseStep^[j] 4665 = 1 := reachStep (stepEq 2 (by rfl) ⟨1749, by rfl⟩ : syracuseStep 4665 = 3499) R3499
theorem R4869 : ∃ j : ℕ, syracuseStep^[j] 4869 = 1 := reachStep (stepEq 4 (by rfl) ⟨456, by rfl⟩ : syracuseStep 4869 = 913) R913
theorem R4877 : ∃ j : ℕ, syracuseStep^[j] 4877 = 1 := reachStep (stepEq 3 (by rfl) ⟨914, by rfl⟩ : syracuseStep 4877 = 1829) R1829
theorem R4879 : ∃ j : ℕ, syracuseStep^[j] 4879 = 1 := reachStep (stepEq 1 (by rfl) ⟨3659, by rfl⟩ : syracuseStep 4879 = 7319) R7319
theorem R4881 : ∃ j : ℕ, syracuseStep^[j] 4881 = 1 := reachStep (stepEq 2 (by rfl) ⟨1830, by rfl⟩ : syracuseStep 4881 = 3661) R3661
theorem R4893 : ∃ j : ℕ, syracuseStep^[j] 4893 = 1 := reachStep (stepEq 3 (by rfl) ⟨917, by rfl⟩ : syracuseStep 4893 = 1835) R1835
theorem R4899 : ∃ j : ℕ, syracuseStep^[j] 4899 = 1 := reachStep (stepEq 1 (by rfl) ⟨3674, by rfl⟩ : syracuseStep 4899 = 7349) R7349
theorem R4901 : ∃ j : ℕ, syracuseStep^[j] 4901 = 1 := reachStep (stepEq 4 (by rfl) ⟨459, by rfl⟩ : syracuseStep 4901 = 919) R919
theorem R4907 : ∃ j : ℕ, syracuseStep^[j] 4907 = 1 := reachStep (stepEq 1 (by rfl) ⟨3680, by rfl⟩ : syracuseStep 4907 = 7361) R7361
theorem R4909 : ∃ j : ℕ, syracuseStep^[j] 4909 = 1 := reachStep (stepEq 3 (by rfl) ⟨920, by rfl⟩ : syracuseStep 4909 = 1841) R1841
theorem R4913 : ∃ j : ℕ, syracuseStep^[j] 4913 = 1 := reachStep (stepEq 2 (by rfl) ⟨1842, by rfl⟩ : syracuseStep 4913 = 3685) R3685
theorem R4915 : ∃ j : ℕ, syracuseStep^[j] 4915 = 1 := reachStep (stepEq 1 (by rfl) ⟨3686, by rfl⟩ : syracuseStep 4915 = 7373) R7373
theorem R4933 : ∃ j : ℕ, syracuseStep^[j] 4933 = 1 := reachStep (stepEq 4 (by rfl) ⟨462, by rfl⟩ : syracuseStep 4933 = 925) R925
theorem R4937 : ∃ j : ℕ, syracuseStep^[j] 4937 = 1 := reachStep (stepEq 2 (by rfl) ⟨1851, by rfl⟩ : syracuseStep 4937 = 3703) R3703
theorem R4939 : ∃ j : ℕ, syracuseStep^[j] 4939 = 1 := reachStep (stepEq 1 (by rfl) ⟨3704, by rfl⟩ : syracuseStep 4939 = 7409) R7409
theorem R4941 : ∃ j : ℕ, syracuseStep^[j] 4941 = 1 := reachStep (stepEq 3 (by rfl) ⟨926, by rfl⟩ : syracuseStep 4941 = 1853) R1853
theorem R4943 : ∃ j : ℕ, syracuseStep^[j] 4943 = 1 := reachStep (stepEq 1 (by rfl) ⟨3707, by rfl⟩ : syracuseStep 4943 = 7415) R7415
theorem R4957 : ∃ j : ℕ, syracuseStep^[j] 4957 = 1 := reachStep (stepEq 3 (by rfl) ⟨929, by rfl⟩ : syracuseStep 4957 = 1859) R1859
theorem R4989 : ∃ j : ℕ, syracuseStep^[j] 4989 = 1 := reachStep (stepEq 3 (by rfl) ⟨935, by rfl⟩ : syracuseStep 4989 = 1871) R1871
theorem R5013 : ∃ j : ℕ, syracuseStep^[j] 5013 = 1 := reachStep (stepEq 6 (by rfl) ⟨117, by rfl⟩ : syracuseStep 5013 = 235) R235
theorem R5027 : ∃ j : ℕ, syracuseStep^[j] 5027 = 1 := reachStep (stepEq 1 (by rfl) ⟨3770, by rfl⟩ : syracuseStep 5027 = 7541) R7541
theorem R5035 : ∃ j : ℕ, syracuseStep^[j] 5035 = 1 := reachStep (stepEq 1 (by rfl) ⟨3776, by rfl⟩ : syracuseStep 5035 = 7553) R7553
theorem R5039 : ∃ j : ℕ, syracuseStep^[j] 5039 = 1 := reachStep (stepEq 1 (by rfl) ⟨3779, by rfl⟩ : syracuseStep 5039 = 7559) R7559
theorem R5047 : ∃ j : ℕ, syracuseStep^[j] 5047 = 1 := reachStep (stepEq 1 (by rfl) ⟨3785, by rfl⟩ : syracuseStep 5047 = 7571) R7571
theorem R5063 : ∃ j : ℕ, syracuseStep^[j] 5063 = 1 := reachStep (stepEq 1 (by rfl) ⟨3797, by rfl⟩ : syracuseStep 5063 = 7595) R7595
theorem R5075 : ∃ j : ℕ, syracuseStep^[j] 5075 = 1 := reachStep (stepEq 1 (by rfl) ⟨3806, by rfl⟩ : syracuseStep 5075 = 7613) R7613
theorem R5113 : ∃ j : ℕ, syracuseStep^[j] 5113 = 1 := reachStep (stepEq 2 (by rfl) ⟨1917, by rfl⟩ : syracuseStep 5113 = 3835) R3835
theorem R5117 : ∃ j : ℕ, syracuseStep^[j] 5117 = 1 := reachStep (stepEq 3 (by rfl) ⟨959, by rfl⟩ : syracuseStep 5117 = 1919) R1919
theorem R5211 : ∃ j : ℕ, syracuseStep^[j] 5211 = 1 := reachStep (stepEq 1 (by rfl) ⟨3908, by rfl⟩ : syracuseStep 5211 = 7817) R7817
theorem R40459 : ∃ j : ℕ, syracuseStep^[j] 40459 = 1 := reachStep (stepEq 1 (by rfl) ⟨30344, by rfl⟩ : syracuseStep 40459 = 60689) R60689
theorem R40945 : ∃ j : ℕ, syracuseStep^[j] 40945 = 1 := reachStep (stepEq 2 (by rfl) ⟨15354, by rfl⟩ : syracuseStep 40945 = 30709) R30709
theorem R9299 : ∃ j : ℕ, syracuseStep^[j] 9299 = 1 := reachStep (stepEq 1 (by rfl) ⟨6974, by rfl⟩ : syracuseStep 9299 = 13949) R13949
theorem R9749 : ∃ j : ℕ, syracuseStep^[j] 9749 = 1 := reachStep (stepEq 6 (by rfl) ⟨228, by rfl⟩ : syracuseStep 9749 = 457) R457
theorem R75329 : ∃ j : ℕ, syracuseStep^[j] 75329 = 1 := reachStep (stepEq 2 (by rfl) ⟨28248, by rfl⟩ : syracuseStep 75329 = 56497) R56497
theorem R9797 : ∃ j : ℕ, syracuseStep^[j] 9797 = 1 := reachStep (stepEq 4 (by rfl) ⟨918, by rfl⟩ : syracuseStep 9797 = 1837) R1837
theorem R9803 : ∃ j : ℕ, syracuseStep^[j] 9803 = 1 := reachStep (stepEq 1 (by rfl) ⟨7352, by rfl⟩ : syracuseStep 9803 = 14705) R14705
theorem R9815 : ∃ j : ℕ, syracuseStep^[j] 9815 = 1 := reachStep (stepEq 1 (by rfl) ⟨7361, by rfl⟩ : syracuseStep 9815 = 14723) R14723
theorem R9821 : ∃ j : ℕ, syracuseStep^[j] 9821 = 1 := reachStep (stepEq 3 (by rfl) ⟨1841, by rfl⟩ : syracuseStep 9821 = 3683) R3683
theorem R9827 : ∃ j : ℕ, syracuseStep^[j] 9827 = 1 := reachStep (stepEq 1 (by rfl) ⟨7370, by rfl⟩ : syracuseStep 9827 = 14741) R14741
theorem R9829 : ∃ j : ℕ, syracuseStep^[j] 9829 = 1 := reachStep (stepEq 4 (by rfl) ⟨921, by rfl⟩ : syracuseStep 9829 = 1843) R1843
theorem R9869 : ∃ j : ℕ, syracuseStep^[j] 9869 = 1 := reachStep (stepEq 3 (by rfl) ⟨1850, by rfl⟩ : syracuseStep 9869 = 3701) R3701
theorem R9875 : ∃ j : ℕ, syracuseStep^[j] 9875 = 1 := reachStep (stepEq 1 (by rfl) ⟨7406, by rfl⟩ : syracuseStep 9875 = 14813) R14813
theorem R9929 : ∃ j : ℕ, syracuseStep^[j] 9929 = 1 := reachStep (stepEq 2 (by rfl) ⟨3723, by rfl⟩ : syracuseStep 9929 = 7447) R7447
theorem R9947 : ∃ j : ℕ, syracuseStep^[j] 9947 = 1 := reachStep (stepEq 1 (by rfl) ⟨7460, by rfl⟩ : syracuseStep 9947 = 14921) R14921
theorem R10037 : ∃ j : ℕ, syracuseStep^[j] 10037 = 1 := reachStep (stepEq 5 (by rfl) ⟨470, by rfl⟩ : syracuseStep 10037 = 941) R941
theorem R10049 : ∃ j : ℕ, syracuseStep^[j] 10049 = 1 := reachStep (stepEq 2 (by rfl) ⟨3768, by rfl⟩ : syracuseStep 10049 = 7537) R7537
theorem R10073 : ∃ j : ℕ, syracuseStep^[j] 10073 = 1 := reachStep (stepEq 2 (by rfl) ⟨3777, by rfl⟩ : syracuseStep 10073 = 7555) R7555
theorem R10079 : ∃ j : ℕ, syracuseStep^[j] 10079 = 1 := reachStep (stepEq 1 (by rfl) ⟨7559, by rfl⟩ : syracuseStep 10079 = 15119) R15119
theorem R78731 : ∃ j : ℕ, syracuseStep^[j] 78731 = 1 := reachStep (stepEq 1 (by rfl) ⟨59048, by rfl⟩ : syracuseStep 78731 = 118097) R118097
theorem R80783 : ∃ j : ℕ, syracuseStep^[j] 80783 = 1 := reachStep (stepEq 1 (by rfl) ⟨60587, by rfl⟩ : syracuseStep 80783 = 121175) R121175
theorem R80963 : ∃ j : ℕ, syracuseStep^[j] 80963 = 1 := reachStep (stepEq 1 (by rfl) ⟨60722, by rfl⟩ : syracuseStep 80963 = 121445) R121445
theorem R19273 : ∃ j : ℕ, syracuseStep^[j] 19273 = 1 := reachStep (stepEq 2 (by rfl) ⟨7227, by rfl⟩ : syracuseStep 19273 = 14455) R14455
theorem R19655 : ∃ j : ℕ, syracuseStep^[j] 19655 = 1 := reachStep (stepEq 1 (by rfl) ⟨14741, by rfl⟩ : syracuseStep 19655 = 29483) R29483
theorem R314927 : ∃ j : ℕ, syracuseStep^[j] 314927 = 1 := reachStep (stepEq 1 (by rfl) ⟨236195, by rfl⟩ : syracuseStep 314927 = 472391) R472391
theorem R20141 : ∃ j : ℕ, syracuseStep^[j] 20141 = 1 := reachStep (stepEq 3 (by rfl) ⟨3776, by rfl⟩ : syracuseStep 20141 = 7553) R7553
theorem R20465 : ∃ j : ℕ, syracuseStep^[j] 20465 = 1 := reachStep (stepEq 2 (by rfl) ⟨7674, by rfl⟩ : syracuseStep 20465 = 15349) R15349
theorem R20843 : ∃ j : ℕ, syracuseStep^[j] 20843 = 1 := reachStep (stepEq 1 (by rfl) ⟨15632, by rfl⟩ : syracuseStep 20843 = 31265) R31265
theorem R157463 : ∃ j : ℕ, syracuseStep^[j] 157463 = 1 := reachStep (stepEq 1 (by rfl) ⟨118097, by rfl⟩ : syracuseStep 157463 = 236195) R236195
theorem R411 : ∃ j : ℕ, syracuseStep^[j] 411 = 1 := reachStep (stepEq 1 (by rfl) ⟨308, by rfl⟩ : syracuseStep 411 = 617) R617
theorem R415 : ∃ j : ℕ, syracuseStep^[j] 415 = 1 := reachStep (stepEq 1 (by rfl) ⟨311, by rfl⟩ : syracuseStep 415 = 623) R623
theorem R417 : ∃ j : ℕ, syracuseStep^[j] 417 = 1 := reachStep (stepEq 2 (by rfl) ⟨156, by rfl⟩ : syracuseStep 417 = 313) R313
theorem R811 : ∃ j : ℕ, syracuseStep^[j] 811 = 1 := reachStep (stepEq 1 (by rfl) ⟨608, by rfl⟩ : syracuseStep 811 = 1217) R1217
theorem R815 : ∃ j : ℕ, syracuseStep^[j] 815 = 1 := reachStep (stepEq 1 (by rfl) ⟨611, by rfl⟩ : syracuseStep 815 = 1223) R1223
theorem R823 : ∃ j : ℕ, syracuseStep^[j] 823 = 1 := reachStep (stepEq 1 (by rfl) ⟨617, by rfl⟩ : syracuseStep 823 = 1235) R1235
theorem R825 : ∃ j : ℕ, syracuseStep^[j] 825 = 1 := reachStep (stepEq 2 (by rfl) ⟨309, by rfl⟩ : syracuseStep 825 = 619) R619
theorem R831 : ∃ j : ℕ, syracuseStep^[j] 831 = 1 := reachStep (stepEq 1 (by rfl) ⟨623, by rfl⟩ : syracuseStep 831 = 1247) R1247
theorem R835 : ∃ j : ℕ, syracuseStep^[j] 835 = 1 := reachStep (stepEq 1 (by rfl) ⟨626, by rfl⟩ : syracuseStep 835 = 1253) R1253
theorem R1623 : ∃ j : ℕ, syracuseStep^[j] 1623 = 1 := reachStep (stepEq 1 (by rfl) ⟨1217, by rfl⟩ : syracuseStep 1623 = 2435) R2435
theorem R1625 : ∃ j : ℕ, syracuseStep^[j] 1625 = 1 := reachStep (stepEq 2 (by rfl) ⟨609, by rfl⟩ : syracuseStep 1625 = 1219) R1219
theorem R1631 : ∃ j : ℕ, syracuseStep^[j] 1631 = 1 := reachStep (stepEq 1 (by rfl) ⟨1223, by rfl⟩ : syracuseStep 1631 = 2447) R2447
theorem R1633 : ∃ j : ℕ, syracuseStep^[j] 1633 = 1 := reachStep (stepEq 2 (by rfl) ⟨612, by rfl⟩ : syracuseStep 1633 = 1225) R1225
theorem R1645 : ∃ j : ℕ, syracuseStep^[j] 1645 = 1 := reachStep (stepEq 3 (by rfl) ⟨308, by rfl⟩ : syracuseStep 1645 = 617) R617
theorem R1647 : ∃ j : ℕ, syracuseStep^[j] 1647 = 1 := reachStep (stepEq 1 (by rfl) ⟨1235, by rfl⟩ : syracuseStep 1647 = 2471) R2471
theorem R1651 : ∃ j : ℕ, syracuseStep^[j] 1651 = 1 := reachStep (stepEq 1 (by rfl) ⟨1238, by rfl⟩ : syracuseStep 1651 = 2477) R2477
theorem R1661 : ∃ j : ℕ, syracuseStep^[j] 1661 = 1 := reachStep (stepEq 3 (by rfl) ⟨311, by rfl⟩ : syracuseStep 1661 = 623) R623
theorem R1669 : ∃ j : ℕ, syracuseStep^[j] 1669 = 1 := reachStep (stepEq 4 (by rfl) ⟨156, by rfl⟩ : syracuseStep 1669 = 313) R313
theorem R1675 : ∃ j : ℕ, syracuseStep^[j] 1675 = 1 := reachStep (stepEq 1 (by rfl) ⟨1256, by rfl⟩ : syracuseStep 1675 = 2513) R2513
theorem R1691 : ∃ j : ℕ, syracuseStep^[j] 1691 = 1 := reachStep (stepEq 1 (by rfl) ⟨1268, by rfl⟩ : syracuseStep 1691 = 2537) R2537
theorem R1705 : ∃ j : ℕ, syracuseStep^[j] 1705 = 1 := reachStep (stepEq 2 (by rfl) ⟨639, by rfl⟩ : syracuseStep 1705 = 1279) R1279
theorem R3099 : ∃ j : ℕ, syracuseStep^[j] 3099 = 1 := reachStep (stepEq 1 (by rfl) ⟨2324, by rfl⟩ : syracuseStep 3099 = 4649) R4649
theorem R3245 : ∃ j : ℕ, syracuseStep^[j] 3245 = 1 := reachStep (stepEq 3 (by rfl) ⟨608, by rfl⟩ : syracuseStep 3245 = 1217) R1217
theorem R3249 : ∃ j : ℕ, syracuseStep^[j] 3249 = 1 := reachStep (stepEq 2 (by rfl) ⟨1218, by rfl⟩ : syracuseStep 3249 = 2437) R2437
theorem R3251 : ∃ j : ℕ, syracuseStep^[j] 3251 = 1 := reachStep (stepEq 1 (by rfl) ⟨2438, by rfl⟩ : syracuseStep 3251 = 4877) R4877
theorem R3261 : ∃ j : ℕ, syracuseStep^[j] 3261 = 1 := reachStep (stepEq 3 (by rfl) ⟨611, by rfl⟩ : syracuseStep 3261 = 1223) R1223
theorem R3265 : ∃ j : ℕ, syracuseStep^[j] 3265 = 1 := reachStep (stepEq 2 (by rfl) ⟨1224, by rfl⟩ : syracuseStep 3265 = 2449) R2449
theorem R3267 : ∃ j : ℕ, syracuseStep^[j] 3267 = 1 := reachStep (stepEq 1 (by rfl) ⟨2450, by rfl⟩ : syracuseStep 3267 = 4901) R4901
theorem R3271 : ∃ j : ℕ, syracuseStep^[j] 3271 = 1 := reachStep (stepEq 1 (by rfl) ⟨2453, by rfl⟩ : syracuseStep 3271 = 4907) R4907
theorem R3273 : ∃ j : ℕ, syracuseStep^[j] 3273 = 1 := reachStep (stepEq 2 (by rfl) ⟨1227, by rfl⟩ : syracuseStep 3273 = 2455) R2455
theorem R3275 : ∃ j : ℕ, syracuseStep^[j] 3275 = 1 := reachStep (stepEq 1 (by rfl) ⟨2456, by rfl⟩ : syracuseStep 3275 = 4913) R4913
theorem R3289 : ∃ j : ℕ, syracuseStep^[j] 3289 = 1 := reachStep (stepEq 2 (by rfl) ⟨1233, by rfl⟩ : syracuseStep 3289 = 2467) R2467
theorem R3291 : ∃ j : ℕ, syracuseStep^[j] 3291 = 1 := reachStep (stepEq 1 (by rfl) ⟨2468, by rfl⟩ : syracuseStep 3291 = 4937) R4937
theorem R3293 : ∃ j : ℕ, syracuseStep^[j] 3293 = 1 := reachStep (stepEq 3 (by rfl) ⟨617, by rfl⟩ : syracuseStep 3293 = 1235) R1235
theorem R3295 : ∃ j : ℕ, syracuseStep^[j] 3295 = 1 := reachStep (stepEq 1 (by rfl) ⟨2471, by rfl⟩ : syracuseStep 3295 = 4943) R4943
theorem R3301 : ∃ j : ℕ, syracuseStep^[j] 3301 = 1 := reachStep (stepEq 4 (by rfl) ⟨309, by rfl⟩ : syracuseStep 3301 = 619) R619
theorem R3325 : ∃ j : ℕ, syracuseStep^[j] 3325 = 1 := reachStep (stepEq 3 (by rfl) ⟨623, by rfl⟩ : syracuseStep 3325 = 1247) R1247
theorem R3341 : ∃ j : ℕ, syracuseStep^[j] 3341 = 1 := reachStep (stepEq 3 (by rfl) ⟨626, by rfl⟩ : syracuseStep 3341 = 1253) R1253
theorem R3345 : ∃ j : ℕ, syracuseStep^[j] 3345 = 1 := reachStep (stepEq 2 (by rfl) ⟨1254, by rfl⟩ : syracuseStep 3345 = 2509) R2509
theorem R3351 : ∃ j : ℕ, syracuseStep^[j] 3351 = 1 := reachStep (stepEq 1 (by rfl) ⟨2513, by rfl⟩ : syracuseStep 3351 = 5027) R5027
theorem R3359 : ∃ j : ℕ, syracuseStep^[j] 3359 = 1 := reachStep (stepEq 1 (by rfl) ⟨2519, by rfl⟩ : syracuseStep 3359 = 5039) R5039
theorem R3375 : ∃ j : ℕ, syracuseStep^[j] 3375 = 1 := reachStep (stepEq 1 (by rfl) ⟨2531, by rfl⟩ : syracuseStep 3375 = 5063) R5063
theorem R3383 : ∃ j : ℕ, syracuseStep^[j] 3383 = 1 := reachStep (stepEq 1 (by rfl) ⟨2537, by rfl⟩ : syracuseStep 3383 = 5075) R5075
theorem R3409 : ∃ j : ℕ, syracuseStep^[j] 3409 = 1 := reachStep (stepEq 2 (by rfl) ⟨1278, by rfl⟩ : syracuseStep 3409 = 2557) R2557
theorem R3411 : ∃ j : ℕ, syracuseStep^[j] 3411 = 1 := reachStep (stepEq 1 (by rfl) ⟨2558, by rfl⟩ : syracuseStep 3411 = 5117) R5117
theorem R6199 : ∃ j : ℕ, syracuseStep^[j] 6199 = 1 := reachStep (stepEq 1 (by rfl) ⟨4649, by rfl⟩ : syracuseStep 6199 = 9299) R9299
theorem R6493 : ∃ j : ℕ, syracuseStep^[j] 6493 = 1 := reachStep (stepEq 3 (by rfl) ⟨1217, by rfl⟩ : syracuseStep 6493 = 2435) R2435
theorem R6499 : ∃ j : ℕ, syracuseStep^[j] 6499 = 1 := reachStep (stepEq 1 (by rfl) ⟨4874, by rfl⟩ : syracuseStep 6499 = 9749) R9749
theorem R6501 : ∃ j : ℕ, syracuseStep^[j] 6501 = 1 := reachStep (stepEq 4 (by rfl) ⟨609, by rfl⟩ : syracuseStep 6501 = 1219) R1219
theorem R6505 : ∃ j : ℕ, syracuseStep^[j] 6505 = 1 := reachStep (stepEq 2 (by rfl) ⟨2439, by rfl⟩ : syracuseStep 6505 = 4879) R4879
theorem R6525 : ∃ j : ℕ, syracuseStep^[j] 6525 = 1 := reachStep (stepEq 3 (by rfl) ⟨1223, by rfl⟩ : syracuseStep 6525 = 2447) R2447
theorem R6531 : ∃ j : ℕ, syracuseStep^[j] 6531 = 1 := reachStep (stepEq 1 (by rfl) ⟨4898, by rfl⟩ : syracuseStep 6531 = 9797) R9797
theorem R6533 : ∃ j : ℕ, syracuseStep^[j] 6533 = 1 := reachStep (stepEq 4 (by rfl) ⟨612, by rfl⟩ : syracuseStep 6533 = 1225) R1225
theorem R6535 : ∃ j : ℕ, syracuseStep^[j] 6535 = 1 := reachStep (stepEq 1 (by rfl) ⟨4901, by rfl⟩ : syracuseStep 6535 = 9803) R9803
theorem R6543 : ∃ j : ℕ, syracuseStep^[j] 6543 = 1 := reachStep (stepEq 1 (by rfl) ⟨4907, by rfl⟩ : syracuseStep 6543 = 9815) R9815
theorem R6545 : ∃ j : ℕ, syracuseStep^[j] 6545 = 1 := reachStep (stepEq 2 (by rfl) ⟨2454, by rfl⟩ : syracuseStep 6545 = 4909) R4909
theorem R6547 : ∃ j : ℕ, syracuseStep^[j] 6547 = 1 := reachStep (stepEq 1 (by rfl) ⟨4910, by rfl⟩ : syracuseStep 6547 = 9821) R9821
theorem R6551 : ∃ j : ℕ, syracuseStep^[j] 6551 = 1 := reachStep (stepEq 1 (by rfl) ⟨4913, by rfl⟩ : syracuseStep 6551 = 9827) R9827
theorem R6553 : ∃ j : ℕ, syracuseStep^[j] 6553 = 1 := reachStep (stepEq 2 (by rfl) ⟨2457, by rfl⟩ : syracuseStep 6553 = 4915) R4915
theorem R6577 : ∃ j : ℕ, syracuseStep^[j] 6577 = 1 := reachStep (stepEq 2 (by rfl) ⟨2466, by rfl⟩ : syracuseStep 6577 = 4933) R4933
theorem R6579 : ∃ j : ℕ, syracuseStep^[j] 6579 = 1 := reachStep (stepEq 1 (by rfl) ⟨4934, by rfl⟩ : syracuseStep 6579 = 9869) R9869
theorem R6581 : ∃ j : ℕ, syracuseStep^[j] 6581 = 1 := reachStep (stepEq 5 (by rfl) ⟨308, by rfl⟩ : syracuseStep 6581 = 617) R617
theorem R6583 : ∃ j : ℕ, syracuseStep^[j] 6583 = 1 := reachStep (stepEq 1 (by rfl) ⟨4937, by rfl⟩ : syracuseStep 6583 = 9875) R9875
theorem R6585 : ∃ j : ℕ, syracuseStep^[j] 6585 = 1 := reachStep (stepEq 2 (by rfl) ⟨2469, by rfl⟩ : syracuseStep 6585 = 4939) R4939
theorem R6589 : ∃ j : ℕ, syracuseStep^[j] 6589 = 1 := reachStep (stepEq 3 (by rfl) ⟨1235, by rfl⟩ : syracuseStep 6589 = 2471) R2471
theorem R6605 : ∃ j : ℕ, syracuseStep^[j] 6605 = 1 := reachStep (stepEq 3 (by rfl) ⟨1238, by rfl⟩ : syracuseStep 6605 = 2477) R2477
theorem R6609 : ∃ j : ℕ, syracuseStep^[j] 6609 = 1 := reachStep (stepEq 2 (by rfl) ⟨2478, by rfl⟩ : syracuseStep 6609 = 4957) R4957
theorem R6619 : ∃ j : ℕ, syracuseStep^[j] 6619 = 1 := reachStep (stepEq 1 (by rfl) ⟨4964, by rfl⟩ : syracuseStep 6619 = 9929) R9929
theorem R6631 : ∃ j : ℕ, syracuseStep^[j] 6631 = 1 := reachStep (stepEq 1 (by rfl) ⟨4973, by rfl⟩ : syracuseStep 6631 = 9947) R9947
theorem R6645 : ∃ j : ℕ, syracuseStep^[j] 6645 = 1 := reachStep (stepEq 5 (by rfl) ⟨311, by rfl⟩ : syracuseStep 6645 = 623) R623
theorem R104975 : ∃ j : ℕ, syracuseStep^[j] 104975 = 1 := reachStep (stepEq 1 (by rfl) ⟨78731, by rfl⟩ : syracuseStep 104975 = 157463) R157463
theorem R6677 : ∃ j : ℕ, syracuseStep^[j] 6677 = 1 := reachStep (stepEq 6 (by rfl) ⟨156, by rfl⟩ : syracuseStep 6677 = 313) R313
theorem R6691 : ∃ j : ℕ, syracuseStep^[j] 6691 = 1 := reachStep (stepEq 1 (by rfl) ⟨5018, by rfl⟩ : syracuseStep 6691 = 10037) R10037
theorem R6699 : ∃ j : ℕ, syracuseStep^[j] 6699 = 1 := reachStep (stepEq 1 (by rfl) ⟨5024, by rfl⟩ : syracuseStep 6699 = 10049) R10049
theorem R6701 : ∃ j : ℕ, syracuseStep^[j] 6701 = 1 := reachStep (stepEq 3 (by rfl) ⟨1256, by rfl⟩ : syracuseStep 6701 = 2513) R2513
theorem R6713 : ∃ j : ℕ, syracuseStep^[j] 6713 = 1 := reachStep (stepEq 2 (by rfl) ⟨2517, by rfl⟩ : syracuseStep 6713 = 5035) R5035
theorem R6715 : ∃ j : ℕ, syracuseStep^[j] 6715 = 1 := reachStep (stepEq 1 (by rfl) ⟨5036, by rfl⟩ : syracuseStep 6715 = 10073) R10073
theorem R6719 : ∃ j : ℕ, syracuseStep^[j] 6719 = 1 := reachStep (stepEq 1 (by rfl) ⟨5039, by rfl⟩ : syracuseStep 6719 = 10079) R10079
theorem R6817 : ∃ j : ℕ, syracuseStep^[j] 6817 = 1 := reachStep (stepEq 2 (by rfl) ⟨2556, by rfl⟩ : syracuseStep 6817 = 5113) R5113
theorem R6821 : ∃ j : ℕ, syracuseStep^[j] 6821 = 1 := reachStep (stepEq 4 (by rfl) ⟨639, by rfl⟩ : syracuseStep 6821 = 1279) R1279
theorem R13061 : ∃ j : ℕ, syracuseStep^[j] 13061 = 1 := reachStep (stepEq 4 (by rfl) ⟨1224, by rfl⟩ : syracuseStep 13061 = 2449) R2449
theorem R13085 : ∃ j : ℕ, syracuseStep^[j] 13085 = 1 := reachStep (stepEq 3 (by rfl) ⟨2453, by rfl⟩ : syracuseStep 13085 = 4907) R4907
theorem R13103 : ∃ j : ℕ, syracuseStep^[j] 13103 = 1 := reachStep (stepEq 1 (by rfl) ⟨9827, by rfl⟩ : syracuseStep 13103 = 19655) R19655
theorem R13105 : ∃ j : ℕ, syracuseStep^[j] 13105 = 1 := reachStep (stepEq 2 (by rfl) ⟨4914, by rfl⟩ : syracuseStep 13105 = 9829) R9829
theorem R13157 : ∃ j : ℕ, syracuseStep^[j] 13157 = 1 := reachStep (stepEq 4 (by rfl) ⟨1233, by rfl⟩ : syracuseStep 13157 = 2467) R2467
theorem R13301 : ∃ j : ℕ, syracuseStep^[j] 13301 = 1 := reachStep (stepEq 5 (by rfl) ⟨623, by rfl⟩ : syracuseStep 13301 = 1247) R1247
theorem R209951 : ∃ j : ℕ, syracuseStep^[j] 209951 = 1 := reachStep (stepEq 1 (by rfl) ⟨157463, by rfl⟩ : syracuseStep 209951 = 314927) R314927
theorem R13405 : ∃ j : ℕ, syracuseStep^[j] 13405 = 1 := reachStep (stepEq 3 (by rfl) ⟨2513, by rfl⟩ : syracuseStep 13405 = 5027) R5027
theorem R111719 : ∃ j : ℕ, syracuseStep^[j] 111719 = 1 := reachStep (stepEq 1 (by rfl) ⟨83789, by rfl⟩ : syracuseStep 111719 = 167579) R167579
theorem R13427 : ∃ j : ℕ, syracuseStep^[j] 13427 = 1 := reachStep (stepEq 1 (by rfl) ⟨10070, by rfl⟩ : syracuseStep 13427 = 20141) R20141
theorem R13643 : ∃ j : ℕ, syracuseStep^[j] 13643 = 1 := reachStep (stepEq 1 (by rfl) ⟨10232, by rfl⟩ : syracuseStep 13643 = 20465) R20465
theorem R13895 : ∃ j : ℕ, syracuseStep^[j] 13895 = 1 := reachStep (stepEq 1 (by rfl) ⟨10421, by rfl⟩ : syracuseStep 13895 = 20843) R20843
theorem R50219 : ∃ j : ℕ, syracuseStep^[j] 50219 = 1 := reachStep (stepEq 1 (by rfl) ⟨37664, by rfl⟩ : syracuseStep 50219 = 75329) R75329
theorem R52487 : ∃ j : ℕ, syracuseStep^[j] 52487 = 1 := reachStep (stepEq 1 (by rfl) ⟨39365, by rfl⟩ : syracuseStep 52487 = 78731) R78731
theorem R53855 : ∃ j : ℕ, syracuseStep^[j] 53855 = 1 := reachStep (stepEq 1 (by rfl) ⟨40391, by rfl⟩ : syracuseStep 53855 = 80783) R80783
theorem R53945 : ∃ j : ℕ, syracuseStep^[j] 53945 = 1 := reachStep (stepEq 2 (by rfl) ⟨20229, by rfl⟩ : syracuseStep 53945 = 40459) R40459
theorem R53975 : ∃ j : ℕ, syracuseStep^[j] 53975 = 1 := reachStep (stepEq 1 (by rfl) ⟨40481, by rfl⟩ : syracuseStep 53975 = 80963) R80963
theorem R54593 : ∃ j : ℕ, syracuseStep^[j] 54593 = 1 := reachStep (stepEq 2 (by rfl) ⟨20472, by rfl⟩ : syracuseStep 54593 = 40945) R40945
theorem R25697 : ∃ j : ℕ, syracuseStep^[j] 25697 = 1 := reachStep (stepEq 2 (by rfl) ⟨9636, by rfl⟩ : syracuseStep 25697 = 19273) R19273
theorem R543 : ∃ j : ℕ, syracuseStep^[j] 543 = 1 := reachStep (stepEq 1 (by rfl) ⟨407, by rfl⟩ : syracuseStep 543 = 815) R815
theorem R553 : ∃ j : ℕ, syracuseStep^[j] 553 = 1 := reachStep (stepEq 2 (by rfl) ⟨207, by rfl⟩ : syracuseStep 553 = 415) R415
theorem R33479 : ∃ j : ℕ, syracuseStep^[j] 33479 = 1 := reachStep (stepEq 1 (by rfl) ⟨25109, by rfl⟩ : syracuseStep 33479 = 50219) R50219
theorem R1081 : ∃ j : ℕ, syracuseStep^[j] 1081 = 1 := reachStep (stepEq 2 (by rfl) ⟨405, by rfl⟩ : syracuseStep 1081 = 811) R811
theorem R1083 : ∃ j : ℕ, syracuseStep^[j] 1083 = 1 := reachStep (stepEq 1 (by rfl) ⟨812, by rfl⟩ : syracuseStep 1083 = 1625) R1625
theorem R1087 : ∃ j : ℕ, syracuseStep^[j] 1087 = 1 := reachStep (stepEq 1 (by rfl) ⟨815, by rfl⟩ : syracuseStep 1087 = 1631) R1631
theorem R1097 : ∃ j : ℕ, syracuseStep^[j] 1097 = 1 := reachStep (stepEq 2 (by rfl) ⟨411, by rfl⟩ : syracuseStep 1097 = 823) R823
theorem R1107 : ∃ j : ℕ, syracuseStep^[j] 1107 = 1 := reachStep (stepEq 1 (by rfl) ⟨830, by rfl⟩ : syracuseStep 1107 = 1661) R1661
theorem R1113 : ∃ j : ℕ, syracuseStep^[j] 1113 = 1 := reachStep (stepEq 2 (by rfl) ⟨417, by rfl⟩ : syracuseStep 1113 = 835) R835
theorem R1127 : ∃ j : ℕ, syracuseStep^[j] 1127 = 1 := reachStep (stepEq 1 (by rfl) ⟨845, by rfl⟩ : syracuseStep 1127 = 1691) R1691
theorem R2163 : ∃ j : ℕ, syracuseStep^[j] 2163 = 1 := reachStep (stepEq 1 (by rfl) ⟨1622, by rfl⟩ : syracuseStep 2163 = 3245) R3245
theorem R2167 : ∃ j : ℕ, syracuseStep^[j] 2167 = 1 := reachStep (stepEq 1 (by rfl) ⟨1625, by rfl⟩ : syracuseStep 2167 = 3251) R3251
theorem R2173 : ∃ j : ℕ, syracuseStep^[j] 2173 = 1 := reachStep (stepEq 3 (by rfl) ⟨407, by rfl⟩ : syracuseStep 2173 = 815) R815
theorem R2177 : ∃ j : ℕ, syracuseStep^[j] 2177 = 1 := reachStep (stepEq 2 (by rfl) ⟨816, by rfl⟩ : syracuseStep 2177 = 1633) R1633
theorem R2183 : ∃ j : ℕ, syracuseStep^[j] 2183 = 1 := reachStep (stepEq 1 (by rfl) ⟨1637, by rfl⟩ : syracuseStep 2183 = 3275) R3275
theorem R2193 : ∃ j : ℕ, syracuseStep^[j] 2193 = 1 := reachStep (stepEq 2 (by rfl) ⟨822, by rfl⟩ : syracuseStep 2193 = 1645) R1645
theorem R2195 : ∃ j : ℕ, syracuseStep^[j] 2195 = 1 := reachStep (stepEq 1 (by rfl) ⟨1646, by rfl⟩ : syracuseStep 2195 = 3293) R3293
theorem R2201 : ∃ j : ℕ, syracuseStep^[j] 2201 = 1 := reachStep (stepEq 2 (by rfl) ⟨825, by rfl⟩ : syracuseStep 2201 = 1651) R1651
theorem R2213 : ∃ j : ℕ, syracuseStep^[j] 2213 = 1 := reachStep (stepEq 4 (by rfl) ⟨207, by rfl⟩ : syracuseStep 2213 = 415) R415
theorem R34991 : ∃ j : ℕ, syracuseStep^[j] 34991 = 1 := reachStep (stepEq 1 (by rfl) ⟨26243, by rfl⟩ : syracuseStep 34991 = 52487) R52487
theorem R2225 : ∃ j : ℕ, syracuseStep^[j] 2225 = 1 := reachStep (stepEq 2 (by rfl) ⟨834, by rfl⟩ : syracuseStep 2225 = 1669) R1669
theorem R2227 : ∃ j : ℕ, syracuseStep^[j] 2227 = 1 := reachStep (stepEq 1 (by rfl) ⟨1670, by rfl⟩ : syracuseStep 2227 = 3341) R3341
theorem R2233 : ∃ j : ℕ, syracuseStep^[j] 2233 = 1 := reachStep (stepEq 2 (by rfl) ⟨837, by rfl⟩ : syracuseStep 2233 = 1675) R1675
theorem R2239 : ∃ j : ℕ, syracuseStep^[j] 2239 = 1 := reachStep (stepEq 1 (by rfl) ⟨1679, by rfl⟩ : syracuseStep 2239 = 3359) R3359
theorem R2255 : ∃ j : ℕ, syracuseStep^[j] 2255 = 1 := reachStep (stepEq 1 (by rfl) ⟨1691, by rfl⟩ : syracuseStep 2255 = 3383) R3383
theorem R2273 : ∃ j : ℕ, syracuseStep^[j] 2273 = 1 := reachStep (stepEq 2 (by rfl) ⟨852, by rfl⟩ : syracuseStep 2273 = 1705) R1705
theorem R68525 : ∃ j : ℕ, syracuseStep^[j] 68525 = 1 := reachStep (stepEq 3 (by rfl) ⟨12848, by rfl⟩ : syracuseStep 68525 = 25697) R25697
theorem R35903 : ∃ j : ℕ, syracuseStep^[j] 35903 = 1 := reachStep (stepEq 1 (by rfl) ⟨26927, by rfl⟩ : syracuseStep 35903 = 53855) R53855
theorem R35963 : ∃ j : ℕ, syracuseStep^[j] 35963 = 1 := reachStep (stepEq 1 (by rfl) ⟨26972, by rfl⟩ : syracuseStep 35963 = 53945) R53945
theorem R35983 : ∃ j : ℕ, syracuseStep^[j] 35983 = 1 := reachStep (stepEq 1 (by rfl) ⟨26987, by rfl⟩ : syracuseStep 35983 = 53975) R53975
theorem R36085 : ∃ j : ℕ, syracuseStep^[j] 36085 = 1 := reachStep (stepEq 5 (by rfl) ⟨1691, by rfl⟩ : syracuseStep 36085 = 3383) R3383
theorem R36395 : ∃ j : ℕ, syracuseStep^[j] 36395 = 1 := reachStep (stepEq 1 (by rfl) ⟨27296, by rfl⟩ : syracuseStep 36395 = 54593) R54593
theorem R4325 : ∃ j : ℕ, syracuseStep^[j] 4325 = 1 := reachStep (stepEq 4 (by rfl) ⟨405, by rfl⟩ : syracuseStep 4325 = 811) R811
theorem R4333 : ∃ j : ℕ, syracuseStep^[j] 4333 = 1 := reachStep (stepEq 3 (by rfl) ⟨812, by rfl⟩ : syracuseStep 4333 = 1625) R1625
theorem R4349 : ∃ j : ℕ, syracuseStep^[j] 4349 = 1 := reachStep (stepEq 3 (by rfl) ⟨815, by rfl⟩ : syracuseStep 4349 = 1631) R1631
theorem R4353 : ∃ j : ℕ, syracuseStep^[j] 4353 = 1 := reachStep (stepEq 2 (by rfl) ⟨1632, by rfl⟩ : syracuseStep 4353 = 3265) R3265
theorem R4355 : ∃ j : ℕ, syracuseStep^[j] 4355 = 1 := reachStep (stepEq 1 (by rfl) ⟨3266, by rfl⟩ : syracuseStep 4355 = 6533) R6533
theorem R69893 : ∃ j : ℕ, syracuseStep^[j] 69893 = 1 := reachStep (stepEq 4 (by rfl) ⟨6552, by rfl⟩ : syracuseStep 69893 = 13105) R13105
theorem R4361 : ∃ j : ℕ, syracuseStep^[j] 4361 = 1 := reachStep (stepEq 2 (by rfl) ⟨1635, by rfl⟩ : syracuseStep 4361 = 3271) R3271
theorem R4363 : ∃ j : ℕ, syracuseStep^[j] 4363 = 1 := reachStep (stepEq 1 (by rfl) ⟨3272, by rfl⟩ : syracuseStep 4363 = 6545) R6545
theorem R4367 : ∃ j : ℕ, syracuseStep^[j] 4367 = 1 := reachStep (stepEq 1 (by rfl) ⟨3275, by rfl⟩ : syracuseStep 4367 = 6551) R6551
theorem R4385 : ∃ j : ℕ, syracuseStep^[j] 4385 = 1 := reachStep (stepEq 2 (by rfl) ⟨1644, by rfl⟩ : syracuseStep 4385 = 3289) R3289
theorem R4387 : ∃ j : ℕ, syracuseStep^[j] 4387 = 1 := reachStep (stepEq 1 (by rfl) ⟨3290, by rfl⟩ : syracuseStep 4387 = 6581) R6581
theorem R4389 : ∃ j : ℕ, syracuseStep^[j] 4389 = 1 := reachStep (stepEq 4 (by rfl) ⟨411, by rfl⟩ : syracuseStep 4389 = 823) R823
theorem R4393 : ∃ j : ℕ, syracuseStep^[j] 4393 = 1 := reachStep (stepEq 2 (by rfl) ⟨1647, by rfl⟩ : syracuseStep 4393 = 3295) R3295
theorem R4401 : ∃ j : ℕ, syracuseStep^[j] 4401 = 1 := reachStep (stepEq 2 (by rfl) ⟨1650, by rfl⟩ : syracuseStep 4401 = 3301) R3301
theorem R4403 : ∃ j : ℕ, syracuseStep^[j] 4403 = 1 := reachStep (stepEq 1 (by rfl) ⟨3302, by rfl⟩ : syracuseStep 4403 = 6605) R6605
theorem R4429 : ∃ j : ℕ, syracuseStep^[j] 4429 = 1 := reachStep (stepEq 3 (by rfl) ⟨830, by rfl⟩ : syracuseStep 4429 = 1661) R1661
theorem R4433 : ∃ j : ℕ, syracuseStep^[j] 4433 = 1 := reachStep (stepEq 2 (by rfl) ⟨1662, by rfl⟩ : syracuseStep 4433 = 3325) R3325
theorem R69983 : ∃ j : ℕ, syracuseStep^[j] 69983 = 1 := reachStep (stepEq 1 (by rfl) ⟨52487, by rfl⟩ : syracuseStep 69983 = 104975) R104975
theorem R4451 : ∃ j : ℕ, syracuseStep^[j] 4451 = 1 := reachStep (stepEq 1 (by rfl) ⟨3338, by rfl⟩ : syracuseStep 4451 = 6677) R6677
theorem R4453 : ∃ j : ℕ, syracuseStep^[j] 4453 = 1 := reachStep (stepEq 4 (by rfl) ⟨417, by rfl⟩ : syracuseStep 4453 = 835) R835
theorem R4467 : ∃ j : ℕ, syracuseStep^[j] 4467 = 1 := reachStep (stepEq 1 (by rfl) ⟨3350, by rfl⟩ : syracuseStep 4467 = 6701) R6701
theorem R4475 : ∃ j : ℕ, syracuseStep^[j] 4475 = 1 := reachStep (stepEq 1 (by rfl) ⟨3356, by rfl⟩ : syracuseStep 4475 = 6713) R6713
theorem R4479 : ∃ j : ℕ, syracuseStep^[j] 4479 = 1 := reachStep (stepEq 1 (by rfl) ⟨3359, by rfl⟩ : syracuseStep 4479 = 6719) R6719
theorem R4509 : ∃ j : ℕ, syracuseStep^[j] 4509 = 1 := reachStep (stepEq 3 (by rfl) ⟨845, by rfl⟩ : syracuseStep 4509 = 1691) R1691
theorem R4545 : ∃ j : ℕ, syracuseStep^[j] 4545 = 1 := reachStep (stepEq 2 (by rfl) ⟨1704, by rfl⟩ : syracuseStep 4545 = 3409) R3409
theorem R4547 : ∃ j : ℕ, syracuseStep^[j] 4547 = 1 := reachStep (stepEq 1 (by rfl) ⟨3410, by rfl⟩ : syracuseStep 4547 = 6821) R6821
theorem R8653 : ∃ j : ℕ, syracuseStep^[j] 8653 = 1 := reachStep (stepEq 3 (by rfl) ⟨1622, by rfl⟩ : syracuseStep 8653 = 3245) R3245
theorem R8657 : ∃ j : ℕ, syracuseStep^[j] 8657 = 1 := reachStep (stepEq 2 (by rfl) ⟨3246, by rfl⟩ : syracuseStep 8657 = 6493) R6493
theorem R8669 : ∃ j : ℕ, syracuseStep^[j] 8669 = 1 := reachStep (stepEq 3 (by rfl) ⟨1625, by rfl⟩ : syracuseStep 8669 = 3251) R3251
theorem R8693 : ∃ j : ℕ, syracuseStep^[j] 8693 = 1 := reachStep (stepEq 5 (by rfl) ⟨407, by rfl⟩ : syracuseStep 8693 = 815) R815
theorem R8707 : ∃ j : ℕ, syracuseStep^[j] 8707 = 1 := reachStep (stepEq 1 (by rfl) ⟨6530, by rfl⟩ : syracuseStep 8707 = 13061) R13061
theorem R8723 : ∃ j : ℕ, syracuseStep^[j] 8723 = 1 := reachStep (stepEq 1 (by rfl) ⟨6542, by rfl⟩ : syracuseStep 8723 = 13085) R13085
theorem R8729 : ∃ j : ℕ, syracuseStep^[j] 8729 = 1 := reachStep (stepEq 2 (by rfl) ⟨3273, by rfl⟩ : syracuseStep 8729 = 6547) R6547
theorem R8735 : ∃ j : ℕ, syracuseStep^[j] 8735 = 1 := reachStep (stepEq 1 (by rfl) ⟨6551, by rfl⟩ : syracuseStep 8735 = 13103) R13103
theorem R8771 : ∃ j : ℕ, syracuseStep^[j] 8771 = 1 := reachStep (stepEq 1 (by rfl) ⟨6578, by rfl⟩ : syracuseStep 8771 = 13157) R13157
theorem R8777 : ∃ j : ℕ, syracuseStep^[j] 8777 = 1 := reachStep (stepEq 2 (by rfl) ⟨3291, by rfl⟩ : syracuseStep 8777 = 6583) R6583
theorem R8825 : ∃ j : ℕ, syracuseStep^[j] 8825 = 1 := reachStep (stepEq 2 (by rfl) ⟨3309, by rfl⟩ : syracuseStep 8825 = 6619) R6619
theorem R8867 : ∃ j : ℕ, syracuseStep^[j] 8867 = 1 := reachStep (stepEq 1 (by rfl) ⟨6650, by rfl⟩ : syracuseStep 8867 = 13301) R13301
theorem R139967 : ∃ j : ℕ, syracuseStep^[j] 139967 = 1 := reachStep (stepEq 1 (by rfl) ⟨104975, by rfl⟩ : syracuseStep 139967 = 209951) R209951
theorem R8909 : ∃ j : ℕ, syracuseStep^[j] 8909 = 1 := reachStep (stepEq 3 (by rfl) ⟨1670, by rfl⟩ : syracuseStep 8909 = 3341) R3341
theorem R8921 : ∃ j : ℕ, syracuseStep^[j] 8921 = 1 := reachStep (stepEq 2 (by rfl) ⟨3345, by rfl⟩ : syracuseStep 8921 = 6691) R6691
theorem R8933 : ∃ j : ℕ, syracuseStep^[j] 8933 = 1 := reachStep (stepEq 4 (by rfl) ⟨837, by rfl⟩ : syracuseStep 8933 = 1675) R1675
theorem R74479 : ∃ j : ℕ, syracuseStep^[j] 74479 = 1 := reachStep (stepEq 1 (by rfl) ⟨55859, by rfl⟩ : syracuseStep 74479 = 111719) R111719
theorem R8951 : ∃ j : ℕ, syracuseStep^[j] 8951 = 1 := reachStep (stepEq 1 (by rfl) ⟨6713, by rfl⟩ : syracuseStep 8951 = 13427) R13427
theorem R8953 : ∃ j : ℕ, syracuseStep^[j] 8953 = 1 := reachStep (stepEq 2 (by rfl) ⟨3357, by rfl⟩ : syracuseStep 8953 = 6715) R6715
theorem R8957 : ∃ j : ℕ, syracuseStep^[j] 8957 = 1 := reachStep (stepEq 3 (by rfl) ⟨1679, by rfl⟩ : syracuseStep 8957 = 3359) R3359
theorem R9089 : ∃ j : ℕ, syracuseStep^[j] 9089 = 1 := reachStep (stepEq 2 (by rfl) ⟨3408, by rfl⟩ : syracuseStep 9089 = 6817) R6817
theorem R9095 : ∃ j : ℕ, syracuseStep^[j] 9095 = 1 := reachStep (stepEq 1 (by rfl) ⟨6821, by rfl⟩ : syracuseStep 9095 = 13643) R13643
theorem R9263 : ∃ j : ℕ, syracuseStep^[j] 9263 = 1 := reachStep (stepEq 1 (by rfl) ⟨6947, by rfl⟩ : syracuseStep 9263 = 13895) R13895
theorem R144341 : ∃ j : ℕ, syracuseStep^[j] 144341 = 1 := reachStep (stepEq 7 (by rfl) ⟨1691, by rfl⟩ : syracuseStep 144341 = 3383) R3383
theorem R17131 : ∃ j : ℕ, syracuseStep^[j] 17131 = 1 := reachStep (stepEq 1 (by rfl) ⟨12848, by rfl⟩ : syracuseStep 17131 = 25697) R25697
theorem R17333 : ∃ j : ℕ, syracuseStep^[j] 17333 = 1 := reachStep (stepEq 5 (by rfl) ⟨812, by rfl⟩ : syracuseStep 17333 = 1625) R1625
theorem R17549 : ∃ j : ℕ, syracuseStep^[j] 17549 = 1 := reachStep (stepEq 3 (by rfl) ⟨3290, by rfl⟩ : syracuseStep 17549 = 6581) R6581
theorem R17873 : ∃ j : ℕ, syracuseStep^[j] 17873 = 1 := reachStep (stepEq 2 (by rfl) ⟨6702, by rfl⟩ : syracuseStep 17873 = 13405) R13405
theorem R731 : ∃ j : ℕ, syracuseStep^[j] 731 = 1 := reachStep (stepEq 1 (by rfl) ⟨548, by rfl⟩ : syracuseStep 731 = 1097) R1097
theorem R737 : ∃ j : ℕ, syracuseStep^[j] 737 = 1 := reachStep (stepEq 2 (by rfl) ⟨276, by rfl⟩ : syracuseStep 737 = 553) R553
theorem R751 : ∃ j : ℕ, syracuseStep^[j] 751 = 1 := reachStep (stepEq 1 (by rfl) ⟨563, by rfl⟩ : syracuseStep 751 = 1127) R1127
theorem R99305 : ∃ j : ℕ, syracuseStep^[j] 99305 = 1 := reachStep (stepEq 2 (by rfl) ⟨37239, by rfl⟩ : syracuseStep 99305 = 74479) R74479
theorem R1441 : ∃ j : ℕ, syracuseStep^[j] 1441 = 1 := reachStep (stepEq 2 (by rfl) ⟨540, by rfl⟩ : syracuseStep 1441 = 1081) R1081
theorem R1449 : ∃ j : ℕ, syracuseStep^[j] 1449 = 1 := reachStep (stepEq 2 (by rfl) ⟨543, by rfl⟩ : syracuseStep 1449 = 1087) R1087
theorem R1451 : ∃ j : ℕ, syracuseStep^[j] 1451 = 1 := reachStep (stepEq 1 (by rfl) ⟨1088, by rfl⟩ : syracuseStep 1451 = 2177) R2177
theorem R1455 : ∃ j : ℕ, syracuseStep^[j] 1455 = 1 := reachStep (stepEq 1 (by rfl) ⟨1091, by rfl⟩ : syracuseStep 1455 = 2183) R2183
theorem R1463 : ∃ j : ℕ, syracuseStep^[j] 1463 = 1 := reachStep (stepEq 1 (by rfl) ⟨1097, by rfl⟩ : syracuseStep 1463 = 2195) R2195
theorem R1467 : ∃ j : ℕ, syracuseStep^[j] 1467 = 1 := reachStep (stepEq 1 (by rfl) ⟨1100, by rfl⟩ : syracuseStep 1467 = 2201) R2201
theorem R1475 : ∃ j : ℕ, syracuseStep^[j] 1475 = 1 := reachStep (stepEq 1 (by rfl) ⟨1106, by rfl⟩ : syracuseStep 1475 = 2213) R2213
theorem R1483 : ∃ j : ℕ, syracuseStep^[j] 1483 = 1 := reachStep (stepEq 1 (by rfl) ⟨1112, by rfl⟩ : syracuseStep 1483 = 2225) R2225
theorem R1503 : ∃ j : ℕ, syracuseStep^[j] 1503 = 1 := reachStep (stepEq 1 (by rfl) ⟨1127, by rfl⟩ : syracuseStep 1503 = 2255) R2255
theorem R1515 : ∃ j : ℕ, syracuseStep^[j] 1515 = 1 := reachStep (stepEq 1 (by rfl) ⟨1136, by rfl⟩ : syracuseStep 1515 = 2273) R2273
theorem R2883 : ∃ j : ℕ, syracuseStep^[j] 2883 = 1 := reachStep (stepEq 1 (by rfl) ⟨2162, by rfl⟩ : syracuseStep 2883 = 4325) R4325
theorem R2889 : ∃ j : ℕ, syracuseStep^[j] 2889 = 1 := reachStep (stepEq 2 (by rfl) ⟨1083, by rfl⟩ : syracuseStep 2889 = 2167) R2167
theorem R2897 : ∃ j : ℕ, syracuseStep^[j] 2897 = 1 := reachStep (stepEq 2 (by rfl) ⟨1086, by rfl⟩ : syracuseStep 2897 = 2173) R2173
theorem R2899 : ∃ j : ℕ, syracuseStep^[j] 2899 = 1 := reachStep (stepEq 1 (by rfl) ⟨2174, by rfl⟩ : syracuseStep 2899 = 4349) R4349
theorem R2903 : ∃ j : ℕ, syracuseStep^[j] 2903 = 1 := reachStep (stepEq 1 (by rfl) ⟨2177, by rfl⟩ : syracuseStep 2903 = 4355) R4355
theorem R2907 : ∃ j : ℕ, syracuseStep^[j] 2907 = 1 := reachStep (stepEq 1 (by rfl) ⟨2180, by rfl⟩ : syracuseStep 2907 = 4361) R4361
theorem R2911 : ∃ j : ℕ, syracuseStep^[j] 2911 = 1 := reachStep (stepEq 1 (by rfl) ⟨2183, by rfl⟩ : syracuseStep 2911 = 4367) R4367
theorem R2923 : ∃ j : ℕ, syracuseStep^[j] 2923 = 1 := reachStep (stepEq 1 (by rfl) ⟨2192, by rfl⟩ : syracuseStep 2923 = 4385) R4385
theorem R2925 : ∃ j : ℕ, syracuseStep^[j] 2925 = 1 := reachStep (stepEq 3 (by rfl) ⟨548, by rfl⟩ : syracuseStep 2925 = 1097) R1097
theorem R2935 : ∃ j : ℕ, syracuseStep^[j] 2935 = 1 := reachStep (stepEq 1 (by rfl) ⟨2201, by rfl⟩ : syracuseStep 2935 = 4403) R4403
theorem R2949 : ∃ j : ℕ, syracuseStep^[j] 2949 = 1 := reachStep (stepEq 4 (by rfl) ⟨276, by rfl⟩ : syracuseStep 2949 = 553) R553
theorem R2955 : ∃ j : ℕ, syracuseStep^[j] 2955 = 1 := reachStep (stepEq 1 (by rfl) ⟨2216, by rfl⟩ : syracuseStep 2955 = 4433) R4433
theorem R2967 : ∃ j : ℕ, syracuseStep^[j] 2967 = 1 := reachStep (stepEq 1 (by rfl) ⟨2225, by rfl⟩ : syracuseStep 2967 = 4451) R4451
theorem R2969 : ∃ j : ℕ, syracuseStep^[j] 2969 = 1 := reachStep (stepEq 2 (by rfl) ⟨1113, by rfl⟩ : syracuseStep 2969 = 2227) R2227
theorem R2977 : ∃ j : ℕ, syracuseStep^[j] 2977 = 1 := reachStep (stepEq 2 (by rfl) ⟨1116, by rfl⟩ : syracuseStep 2977 = 2233) R2233
theorem R2983 : ∃ j : ℕ, syracuseStep^[j] 2983 = 1 := reachStep (stepEq 1 (by rfl) ⟨2237, by rfl⟩ : syracuseStep 2983 = 4475) R4475
theorem R2985 : ∃ j : ℕ, syracuseStep^[j] 2985 = 1 := reachStep (stepEq 2 (by rfl) ⟨1119, by rfl⟩ : syracuseStep 2985 = 2239) R2239
theorem R3005 : ∃ j : ℕ, syracuseStep^[j] 3005 = 1 := reachStep (stepEq 3 (by rfl) ⟨563, by rfl⟩ : syracuseStep 3005 = 1127) R1127
theorem R3031 : ∃ j : ℕ, syracuseStep^[j] 3031 = 1 := reachStep (stepEq 1 (by rfl) ⟨2273, by rfl⟩ : syracuseStep 3031 = 4547) R4547
theorem R5765 : ∃ j : ℕ, syracuseStep^[j] 5765 = 1 := reachStep (stepEq 4 (by rfl) ⟨540, by rfl⟩ : syracuseStep 5765 = 1081) R1081
theorem R5771 : ∃ j : ℕ, syracuseStep^[j] 5771 = 1 := reachStep (stepEq 1 (by rfl) ⟨4328, by rfl⟩ : syracuseStep 5771 = 8657) R8657
theorem R5777 : ∃ j : ℕ, syracuseStep^[j] 5777 = 1 := reachStep (stepEq 2 (by rfl) ⟨2166, by rfl⟩ : syracuseStep 5777 = 4333) R4333
theorem R5779 : ∃ j : ℕ, syracuseStep^[j] 5779 = 1 := reachStep (stepEq 1 (by rfl) ⟨4334, by rfl⟩ : syracuseStep 5779 = 8669) R8669
theorem R5795 : ∃ j : ℕ, syracuseStep^[j] 5795 = 1 := reachStep (stepEq 1 (by rfl) ⟨4346, by rfl⟩ : syracuseStep 5795 = 8693) R8693
theorem R5797 : ∃ j : ℕ, syracuseStep^[j] 5797 = 1 := reachStep (stepEq 4 (by rfl) ⟨543, by rfl⟩ : syracuseStep 5797 = 1087) R1087
theorem R5805 : ∃ j : ℕ, syracuseStep^[j] 5805 = 1 := reachStep (stepEq 3 (by rfl) ⟨1088, by rfl⟩ : syracuseStep 5805 = 2177) R2177
theorem R5815 : ∃ j : ℕ, syracuseStep^[j] 5815 = 1 := reachStep (stepEq 1 (by rfl) ⟨4361, by rfl⟩ : syracuseStep 5815 = 8723) R8723
theorem R5817 : ∃ j : ℕ, syracuseStep^[j] 5817 = 1 := reachStep (stepEq 2 (by rfl) ⟨2181, by rfl⟩ : syracuseStep 5817 = 4363) R4363
theorem R5819 : ∃ j : ℕ, syracuseStep^[j] 5819 = 1 := reachStep (stepEq 1 (by rfl) ⟨4364, by rfl⟩ : syracuseStep 5819 = 8729) R8729
theorem R5821 : ∃ j : ℕ, syracuseStep^[j] 5821 = 1 := reachStep (stepEq 3 (by rfl) ⟨1091, by rfl⟩ : syracuseStep 5821 = 2183) R2183
theorem R5823 : ∃ j : ℕ, syracuseStep^[j] 5823 = 1 := reachStep (stepEq 1 (by rfl) ⟨4367, by rfl⟩ : syracuseStep 5823 = 8735) R8735
theorem R5847 : ∃ j : ℕ, syracuseStep^[j] 5847 = 1 := reachStep (stepEq 1 (by rfl) ⟨4385, by rfl⟩ : syracuseStep 5847 = 8771) R8771
theorem R5849 : ∃ j : ℕ, syracuseStep^[j] 5849 = 1 := reachStep (stepEq 2 (by rfl) ⟨2193, by rfl⟩ : syracuseStep 5849 = 4387) R4387
theorem R5851 : ∃ j : ℕ, syracuseStep^[j] 5851 = 1 := reachStep (stepEq 1 (by rfl) ⟨4388, by rfl⟩ : syracuseStep 5851 = 8777) R8777
theorem R5853 : ∃ j : ℕ, syracuseStep^[j] 5853 = 1 := reachStep (stepEq 3 (by rfl) ⟨1097, by rfl⟩ : syracuseStep 5853 = 2195) R2195
theorem R5857 : ∃ j : ℕ, syracuseStep^[j] 5857 = 1 := reachStep (stepEq 2 (by rfl) ⟨2196, by rfl⟩ : syracuseStep 5857 = 4393) R4393
theorem R5869 : ∃ j : ℕ, syracuseStep^[j] 5869 = 1 := reachStep (stepEq 3 (by rfl) ⟨1100, by rfl⟩ : syracuseStep 5869 = 2201) R2201
theorem R5883 : ∃ j : ℕ, syracuseStep^[j] 5883 = 1 := reachStep (stepEq 1 (by rfl) ⟨4412, by rfl⟩ : syracuseStep 5883 = 8825) R8825
theorem R5901 : ∃ j : ℕ, syracuseStep^[j] 5901 = 1 := reachStep (stepEq 3 (by rfl) ⟨1106, by rfl⟩ : syracuseStep 5901 = 2213) R2213
theorem R5905 : ∃ j : ℕ, syracuseStep^[j] 5905 = 1 := reachStep (stepEq 2 (by rfl) ⟨2214, by rfl⟩ : syracuseStep 5905 = 4429) R4429
theorem R5911 : ∃ j : ℕ, syracuseStep^[j] 5911 = 1 := reachStep (stepEq 1 (by rfl) ⟨4433, by rfl⟩ : syracuseStep 5911 = 8867) R8867
theorem R5933 : ∃ j : ℕ, syracuseStep^[j] 5933 = 1 := reachStep (stepEq 3 (by rfl) ⟨1112, by rfl⟩ : syracuseStep 5933 = 2225) R2225
theorem R5937 : ∃ j : ℕ, syracuseStep^[j] 5937 = 1 := reachStep (stepEq 2 (by rfl) ⟨2226, by rfl⟩ : syracuseStep 5937 = 4453) R4453
theorem R5939 : ∃ j : ℕ, syracuseStep^[j] 5939 = 1 := reachStep (stepEq 1 (by rfl) ⟨4454, by rfl⟩ : syracuseStep 5939 = 8909) R8909
theorem R5947 : ∃ j : ℕ, syracuseStep^[j] 5947 = 1 := reachStep (stepEq 1 (by rfl) ⟨4460, by rfl⟩ : syracuseStep 5947 = 8921) R8921
theorem R5955 : ∃ j : ℕ, syracuseStep^[j] 5955 = 1 := reachStep (stepEq 1 (by rfl) ⟨4466, by rfl⟩ : syracuseStep 5955 = 8933) R8933
theorem R5967 : ∃ j : ℕ, syracuseStep^[j] 5967 = 1 := reachStep (stepEq 1 (by rfl) ⟨4475, by rfl⟩ : syracuseStep 5967 = 8951) R8951
theorem R5971 : ∃ j : ℕ, syracuseStep^[j] 5971 = 1 := reachStep (stepEq 1 (by rfl) ⟨4478, by rfl⟩ : syracuseStep 5971 = 8957) R8957
theorem R6013 : ∃ j : ℕ, syracuseStep^[j] 6013 = 1 := reachStep (stepEq 3 (by rfl) ⟨1127, by rfl⟩ : syracuseStep 6013 = 2255) R2255
theorem R6059 : ∃ j : ℕ, syracuseStep^[j] 6059 = 1 := reachStep (stepEq 1 (by rfl) ⟨4544, by rfl⟩ : syracuseStep 6059 = 9089) R9089
theorem R6061 : ∃ j : ℕ, syracuseStep^[j] 6061 = 1 := reachStep (stepEq 3 (by rfl) ⟨1136, by rfl⟩ : syracuseStep 6061 = 2273) R2273
theorem R6063 : ∃ j : ℕ, syracuseStep^[j] 6063 = 1 := reachStep (stepEq 1 (by rfl) ⟨4547, by rfl⟩ : syracuseStep 6063 = 9095) R9095
theorem R6175 : ∃ j : ℕ, syracuseStep^[j] 6175 = 1 := reachStep (stepEq 1 (by rfl) ⟨4631, by rfl⟩ : syracuseStep 6175 = 9263) R9263
theorem R11537 : ∃ j : ℕ, syracuseStep^[j] 11537 = 1 := reachStep (stepEq 2 (by rfl) ⟨4326, by rfl⟩ : syracuseStep 11537 = 8653) R8653
theorem R11555 : ∃ j : ℕ, syracuseStep^[j] 11555 = 1 := reachStep (stepEq 1 (by rfl) ⟨8666, by rfl⟩ : syracuseStep 11555 = 17333) R17333
theorem R11609 : ∃ j : ℕ, syracuseStep^[j] 11609 = 1 := reachStep (stepEq 2 (by rfl) ⟨4353, by rfl⟩ : syracuseStep 11609 = 8707) R8707
theorem R11645 : ∃ j : ℕ, syracuseStep^[j] 11645 = 1 := reachStep (stepEq 3 (by rfl) ⟨2183, by rfl⟩ : syracuseStep 11645 = 4367) R4367
theorem R11699 : ∃ j : ℕ, syracuseStep^[j] 11699 = 1 := reachStep (stepEq 1 (by rfl) ⟨8774, by rfl⟩ : syracuseStep 11699 = 17549) R17549
theorem R11915 : ∃ j : ℕ, syracuseStep^[j] 11915 = 1 := reachStep (stepEq 1 (by rfl) ⟨8936, by rfl⟩ : syracuseStep 11915 = 17873) R17873
theorem R11933 : ∃ j : ℕ, syracuseStep^[j] 11933 = 1 := reachStep (stepEq 3 (by rfl) ⟨2237, by rfl⟩ : syracuseStep 11933 = 4475) R4475
theorem R45683 : ∃ j : ℕ, syracuseStep^[j] 45683 = 1 := reachStep (stepEq 1 (by rfl) ⟨34262, by rfl⟩ : syracuseStep 45683 = 68525) R68525
theorem R46133 : ∃ j : ℕ, syracuseStep^[j] 46133 = 1 := reachStep (stepEq 5 (by rfl) ⟨2162, by rfl⟩ : syracuseStep 46133 = 4325) R4325
theorem R46595 : ∃ j : ℕ, syracuseStep^[j] 46595 = 1 := reachStep (stepEq 1 (by rfl) ⟨34946, by rfl⟩ : syracuseStep 46595 = 69893) R69893
theorem R46655 : ∃ j : ℕ, syracuseStep^[j] 46655 = 1 := reachStep (stepEq 1 (by rfl) ⟨34991, by rfl⟩ : syracuseStep 46655 = 69983) R69983
theorem R47749 : ∃ j : ℕ, syracuseStep^[j] 47749 = 1 := reachStep (stepEq 4 (by rfl) ⟨4476, by rfl⟩ : syracuseStep 47749 = 8953) R8953
theorem R48113 : ∃ j : ℕ, syracuseStep^[j] 48113 = 1 := reachStep (stepEq 2 (by rfl) ⟨18042, by rfl⟩ : syracuseStep 48113 = 36085) R36085
theorem R22319 : ∃ j : ℕ, syracuseStep^[j] 22319 = 1 := reachStep (stepEq 1 (by rfl) ⟨16739, by rfl⟩ : syracuseStep 22319 = 33479) R33479
theorem R22841 : ∃ j : ℕ, syracuseStep^[j] 22841 = 1 := reachStep (stepEq 2 (by rfl) ⟨8565, by rfl⟩ : syracuseStep 22841 = 17131) R17131
theorem R23327 : ∃ j : ℕ, syracuseStep^[j] 23327 = 1 := reachStep (stepEq 1 (by rfl) ⟨17495, by rfl⟩ : syracuseStep 23327 = 34991) R34991
theorem R23935 : ∃ j : ℕ, syracuseStep^[j] 23935 = 1 := reachStep (stepEq 1 (by rfl) ⟨17951, by rfl⟩ : syracuseStep 23935 = 35903) R35903
theorem R23975 : ∃ j : ℕ, syracuseStep^[j] 23975 = 1 := reachStep (stepEq 1 (by rfl) ⟨17981, by rfl⟩ : syracuseStep 23975 = 35963) R35963
theorem R24263 : ∃ j : ℕ, syracuseStep^[j] 24263 = 1 := reachStep (stepEq 1 (by rfl) ⟨18197, by rfl⟩ : syracuseStep 24263 = 36395) R36395
theorem R93311 : ∃ j : ℕ, syracuseStep^[j] 93311 = 1 := reachStep (stepEq 1 (by rfl) ⟨69983, by rfl⟩ : syracuseStep 93311 = 139967) R139967
theorem R191909 : ∃ j : ℕ, syracuseStep^[j] 191909 = 1 := reachStep (stepEq 4 (by rfl) ⟨17991, by rfl⟩ : syracuseStep 191909 = 35983) R35983
theorem R96227 : ∃ j : ℕ, syracuseStep^[j] 96227 = 1 := reachStep (stepEq 1 (by rfl) ⟨72170, by rfl⟩ : syracuseStep 96227 = 144341) R144341
theorem R487 : ∃ j : ℕ, syracuseStep^[j] 487 = 1 := reachStep (stepEq 1 (by rfl) ⟨365, by rfl⟩ : syracuseStep 487 = 731) R731
theorem R491 : ∃ j : ℕ, syracuseStep^[j] 491 = 1 := reachStep (stepEq 1 (by rfl) ⟨368, by rfl⟩ : syracuseStep 491 = 737) R737
theorem R66203 : ∃ j : ℕ, syracuseStep^[j] 66203 = 1 := reachStep (stepEq 1 (by rfl) ⟨49652, by rfl⟩ : syracuseStep 66203 = 99305) R99305
theorem R967 : ∃ j : ℕ, syracuseStep^[j] 967 = 1 := reachStep (stepEq 1 (by rfl) ⟨725, by rfl⟩ : syracuseStep 967 = 1451) R1451
theorem R975 : ∃ j : ℕ, syracuseStep^[j] 975 = 1 := reachStep (stepEq 1 (by rfl) ⟨731, by rfl⟩ : syracuseStep 975 = 1463) R1463
theorem R983 : ∃ j : ℕ, syracuseStep^[j] 983 = 1 := reachStep (stepEq 1 (by rfl) ⟨737, by rfl⟩ : syracuseStep 983 = 1475) R1475
theorem R1001 : ∃ j : ℕ, syracuseStep^[j] 1001 = 1 := reachStep (stepEq 2 (by rfl) ⟨375, by rfl⟩ : syracuseStep 1001 = 751) R751
theorem R1921 : ∃ j : ℕ, syracuseStep^[j] 1921 = 1 := reachStep (stepEq 2 (by rfl) ⟨720, by rfl⟩ : syracuseStep 1921 = 1441) R1441
theorem R1931 : ∃ j : ℕ, syracuseStep^[j] 1931 = 1 := reachStep (stepEq 1 (by rfl) ⟨1448, by rfl⟩ : syracuseStep 1931 = 2897) R2897
theorem R1935 : ∃ j : ℕ, syracuseStep^[j] 1935 = 1 := reachStep (stepEq 1 (by rfl) ⟨1451, by rfl⟩ : syracuseStep 1935 = 2903) R2903
theorem R1949 : ∃ j : ℕ, syracuseStep^[j] 1949 = 1 := reachStep (stepEq 3 (by rfl) ⟨365, by rfl⟩ : syracuseStep 1949 = 731) R731
theorem R1965 : ∃ j : ℕ, syracuseStep^[j] 1965 = 1 := reachStep (stepEq 3 (by rfl) ⟨368, by rfl⟩ : syracuseStep 1965 = 737) R737
theorem R1977 : ∃ j : ℕ, syracuseStep^[j] 1977 = 1 := reachStep (stepEq 2 (by rfl) ⟨741, by rfl⟩ : syracuseStep 1977 = 1483) R1483
theorem R1979 : ∃ j : ℕ, syracuseStep^[j] 1979 = 1 := reachStep (stepEq 1 (by rfl) ⟨1484, by rfl⟩ : syracuseStep 1979 = 2969) R2969
theorem R2003 : ∃ j : ℕ, syracuseStep^[j] 2003 = 1 := reachStep (stepEq 1 (by rfl) ⟨1502, by rfl⟩ : syracuseStep 2003 = 3005) R3005
theorem R3843 : ∃ j : ℕ, syracuseStep^[j] 3843 = 1 := reachStep (stepEq 1 (by rfl) ⟨2882, by rfl⟩ : syracuseStep 3843 = 5765) R5765
theorem R3847 : ∃ j : ℕ, syracuseStep^[j] 3847 = 1 := reachStep (stepEq 1 (by rfl) ⟨2885, by rfl⟩ : syracuseStep 3847 = 5771) R5771
theorem R3851 : ∃ j : ℕ, syracuseStep^[j] 3851 = 1 := reachStep (stepEq 1 (by rfl) ⟨2888, by rfl⟩ : syracuseStep 3851 = 5777) R5777
theorem R3863 : ∃ j : ℕ, syracuseStep^[j] 3863 = 1 := reachStep (stepEq 1 (by rfl) ⟨2897, by rfl⟩ : syracuseStep 3863 = 5795) R5795
theorem R3865 : ∃ j : ℕ, syracuseStep^[j] 3865 = 1 := reachStep (stepEq 2 (by rfl) ⟨1449, by rfl⟩ : syracuseStep 3865 = 2899) R2899
theorem R3869 : ∃ j : ℕ, syracuseStep^[j] 3869 = 1 := reachStep (stepEq 3 (by rfl) ⟨725, by rfl⟩ : syracuseStep 3869 = 1451) R1451
theorem R3879 : ∃ j : ℕ, syracuseStep^[j] 3879 = 1 := reachStep (stepEq 1 (by rfl) ⟨2909, by rfl⟩ : syracuseStep 3879 = 5819) R5819
theorem R3881 : ∃ j : ℕ, syracuseStep^[j] 3881 = 1 := reachStep (stepEq 2 (by rfl) ⟨1455, by rfl⟩ : syracuseStep 3881 = 2911) R2911
theorem R3897 : ∃ j : ℕ, syracuseStep^[j] 3897 = 1 := reachStep (stepEq 2 (by rfl) ⟨1461, by rfl⟩ : syracuseStep 3897 = 2923) R2923
theorem R3899 : ∃ j : ℕ, syracuseStep^[j] 3899 = 1 := reachStep (stepEq 1 (by rfl) ⟨2924, by rfl⟩ : syracuseStep 3899 = 5849) R5849
theorem R3901 : ∃ j : ℕ, syracuseStep^[j] 3901 = 1 := reachStep (stepEq 3 (by rfl) ⟨731, by rfl⟩ : syracuseStep 3901 = 1463) R1463
theorem R3913 : ∃ j : ℕ, syracuseStep^[j] 3913 = 1 := reachStep (stepEq 2 (by rfl) ⟨1467, by rfl⟩ : syracuseStep 3913 = 2935) R2935
theorem R3933 : ∃ j : ℕ, syracuseStep^[j] 3933 = 1 := reachStep (stepEq 3 (by rfl) ⟨737, by rfl⟩ : syracuseStep 3933 = 1475) R1475
theorem R3955 : ∃ j : ℕ, syracuseStep^[j] 3955 = 1 := reachStep (stepEq 1 (by rfl) ⟨2966, by rfl⟩ : syracuseStep 3955 = 5933) R5933
theorem R3959 : ∃ j : ℕ, syracuseStep^[j] 3959 = 1 := reachStep (stepEq 1 (by rfl) ⟨2969, by rfl⟩ : syracuseStep 3959 = 5939) R5939
theorem R3969 : ∃ j : ℕ, syracuseStep^[j] 3969 = 1 := reachStep (stepEq 2 (by rfl) ⟨1488, by rfl⟩ : syracuseStep 3969 = 2977) R2977
theorem R3977 : ∃ j : ℕ, syracuseStep^[j] 3977 = 1 := reachStep (stepEq 2 (by rfl) ⟨1491, by rfl⟩ : syracuseStep 3977 = 2983) R2983
theorem R4005 : ∃ j : ℕ, syracuseStep^[j] 4005 = 1 := reachStep (stepEq 4 (by rfl) ⟨375, by rfl⟩ : syracuseStep 4005 = 751) R751
theorem R4039 : ∃ j : ℕ, syracuseStep^[j] 4039 = 1 := reachStep (stepEq 1 (by rfl) ⟨3029, by rfl⟩ : syracuseStep 4039 = 6059) R6059
theorem R4041 : ∃ j : ℕ, syracuseStep^[j] 4041 = 1 := reachStep (stepEq 2 (by rfl) ⟨1515, by rfl⟩ : syracuseStep 4041 = 3031) R3031
theorem R7685 : ∃ j : ℕ, syracuseStep^[j] 7685 = 1 := reachStep (stepEq 4 (by rfl) ⟨720, by rfl⟩ : syracuseStep 7685 = 1441) R1441
theorem R7691 : ∃ j : ℕ, syracuseStep^[j] 7691 = 1 := reachStep (stepEq 1 (by rfl) ⟨5768, by rfl⟩ : syracuseStep 7691 = 11537) R11537
theorem R7703 : ∃ j : ℕ, syracuseStep^[j] 7703 = 1 := reachStep (stepEq 1 (by rfl) ⟨5777, by rfl⟩ : syracuseStep 7703 = 11555) R11555
theorem R7705 : ∃ j : ℕ, syracuseStep^[j] 7705 = 1 := reachStep (stepEq 2 (by rfl) ⟨2889, by rfl⟩ : syracuseStep 7705 = 5779) R5779
theorem R7739 : ∃ j : ℕ, syracuseStep^[j] 7739 = 1 := reachStep (stepEq 1 (by rfl) ⟨5804, by rfl⟩ : syracuseStep 7739 = 11609) R11609
theorem R7763 : ∃ j : ℕ, syracuseStep^[j] 7763 = 1 := reachStep (stepEq 1 (by rfl) ⟨5822, by rfl⟩ : syracuseStep 7763 = 11645) R11645
theorem R7799 : ∃ j : ℕ, syracuseStep^[j] 7799 = 1 := reachStep (stepEq 1 (by rfl) ⟨5849, by rfl⟩ : syracuseStep 7799 = 11699) R11699
theorem R7943 : ∃ j : ℕ, syracuseStep^[j] 7943 = 1 := reachStep (stepEq 1 (by rfl) ⟨5957, by rfl⟩ : syracuseStep 7943 = 11915) R11915
theorem R7955 : ∃ j : ℕ, syracuseStep^[j] 7955 = 1 := reachStep (stepEq 1 (by rfl) ⟨5966, by rfl⟩ : syracuseStep 7955 = 11933) R11933
theorem R7961 : ∃ j : ℕ, syracuseStep^[j] 7961 = 1 := reachStep (stepEq 2 (by rfl) ⟨2985, by rfl⟩ : syracuseStep 7961 = 5971) R5971
theorem R8081 : ∃ j : ℕ, syracuseStep^[j] 8081 = 1 := reachStep (stepEq 2 (by rfl) ⟨3030, by rfl⟩ : syracuseStep 8081 = 6061) R6061
theorem R14879 : ∃ j : ℕ, syracuseStep^[j] 14879 = 1 := reachStep (stepEq 1 (by rfl) ⟨11159, by rfl⟩ : syracuseStep 14879 = 22319) R22319
theorem R15227 : ∃ j : ℕ, syracuseStep^[j] 15227 = 1 := reachStep (stepEq 1 (by rfl) ⟨11420, by rfl⟩ : syracuseStep 15227 = 22841) R22841
theorem R15389 : ∃ j : ℕ, syracuseStep^[j] 15389 = 1 := reachStep (stepEq 3 (by rfl) ⟨2885, by rfl⟩ : syracuseStep 15389 = 5771) R5771
theorem R15461 : ∃ j : ℕ, syracuseStep^[j] 15461 = 1 := reachStep (stepEq 4 (by rfl) ⟨1449, by rfl⟩ : syracuseStep 15461 = 2899) R2899
theorem R15551 : ∃ j : ℕ, syracuseStep^[j] 15551 = 1 := reachStep (stepEq 1 (by rfl) ⟨11663, by rfl⟩ : syracuseStep 15551 = 23327) R23327
theorem R15605 : ∃ j : ℕ, syracuseStep^[j] 15605 = 1 := reachStep (stepEq 5 (by rfl) ⟨731, by rfl⟩ : syracuseStep 15605 = 1463) R1463
theorem R15653 : ∃ j : ℕ, syracuseStep^[j] 15653 = 1 := reachStep (stepEq 4 (by rfl) ⟨1467, by rfl⟩ : syracuseStep 15653 = 2935) R2935
theorem R15821 : ∃ j : ℕ, syracuseStep^[j] 15821 = 1 := reachStep (stepEq 3 (by rfl) ⟨2966, by rfl⟩ : syracuseStep 15821 = 5933) R5933
theorem R15983 : ∃ j : ℕ, syracuseStep^[j] 15983 = 1 := reachStep (stepEq 1 (by rfl) ⟨11987, by rfl⟩ : syracuseStep 15983 = 23975) R23975
theorem R16175 : ∃ j : ℕ, syracuseStep^[j] 16175 = 1 := reachStep (stepEq 1 (by rfl) ⟨12131, by rfl⟩ : syracuseStep 16175 = 24263) R24263
theorem R62207 : ∃ j : ℕ, syracuseStep^[j] 62207 = 1 := reachStep (stepEq 1 (by rfl) ⟨46655, by rfl⟩ : syracuseStep 62207 = 93311) R93311
theorem R127939 : ∃ j : ℕ, syracuseStep^[j] 127939 = 1 := reachStep (stepEq 1 (by rfl) ⟨95954, by rfl⟩ : syracuseStep 127939 = 191909) R191909
theorem R30455 : ∃ j : ℕ, syracuseStep^[j] 30455 = 1 := reachStep (stepEq 1 (by rfl) ⟨22841, by rfl⟩ : syracuseStep 30455 = 45683) R45683
theorem R30755 : ∃ j : ℕ, syracuseStep^[j] 30755 = 1 := reachStep (stepEq 1 (by rfl) ⟨23066, by rfl⟩ : syracuseStep 30755 = 46133) R46133
theorem R63665 : ∃ j : ℕ, syracuseStep^[j] 63665 = 1 := reachStep (stepEq 2 (by rfl) ⟨23874, by rfl⟩ : syracuseStep 63665 = 47749) R47749
theorem R31013 : ∃ j : ℕ, syracuseStep^[j] 31013 = 1 := reachStep (stepEq 4 (by rfl) ⟨2907, by rfl⟩ : syracuseStep 31013 = 5815) R5815
theorem R31063 : ∃ j : ℕ, syracuseStep^[j] 31063 = 1 := reachStep (stepEq 1 (by rfl) ⟨23297, by rfl⟩ : syracuseStep 31063 = 46595) R46595
theorem R31103 : ∃ j : ℕ, syracuseStep^[j] 31103 = 1 := reachStep (stepEq 1 (by rfl) ⟨23327, by rfl⟩ : syracuseStep 31103 = 46655) R46655
theorem R64151 : ∃ j : ℕ, syracuseStep^[j] 64151 = 1 := reachStep (stepEq 1 (by rfl) ⟨48113, by rfl⟩ : syracuseStep 64151 = 96227) R96227
theorem R31913 : ∃ j : ℕ, syracuseStep^[j] 31913 = 1 := reachStep (stepEq 2 (by rfl) ⟨11967, by rfl⟩ : syracuseStep 31913 = 23935) R23935
theorem R32075 : ∃ j : ℕ, syracuseStep^[j] 32075 = 1 := reachStep (stepEq 1 (by rfl) ⟨24056, by rfl⟩ : syracuseStep 32075 = 48113) R48113
theorem R327 : ∃ j : ℕ, syracuseStep^[j] 327 = 1 := reachStep (stepEq 1 (by rfl) ⟨245, by rfl⟩ : syracuseStep 327 = 491) R491
theorem R649 : ∃ j : ℕ, syracuseStep^[j] 649 = 1 := reachStep (stepEq 2 (by rfl) ⟨243, by rfl⟩ : syracuseStep 649 = 487) R487
theorem R655 : ∃ j : ℕ, syracuseStep^[j] 655 = 1 := reachStep (stepEq 1 (by rfl) ⟨491, by rfl⟩ : syracuseStep 655 = 983) R983
theorem R667 : ∃ j : ℕ, syracuseStep^[j] 667 = 1 := reachStep (stepEq 1 (by rfl) ⟨500, by rfl⟩ : syracuseStep 667 = 1001) R1001
theorem R1287 : ∃ j : ℕ, syracuseStep^[j] 1287 = 1 := reachStep (stepEq 1 (by rfl) ⟨965, by rfl⟩ : syracuseStep 1287 = 1931) R1931
theorem R1289 : ∃ j : ℕ, syracuseStep^[j] 1289 = 1 := reachStep (stepEq 2 (by rfl) ⟨483, by rfl⟩ : syracuseStep 1289 = 967) R967
theorem R1299 : ∃ j : ℕ, syracuseStep^[j] 1299 = 1 := reachStep (stepEq 1 (by rfl) ⟨974, by rfl⟩ : syracuseStep 1299 = 1949) R1949
theorem R1309 : ∃ j : ℕ, syracuseStep^[j] 1309 = 1 := reachStep (stepEq 3 (by rfl) ⟨245, by rfl⟩ : syracuseStep 1309 = 491) R491
theorem R1319 : ∃ j : ℕ, syracuseStep^[j] 1319 = 1 := reachStep (stepEq 1 (by rfl) ⟨989, by rfl⟩ : syracuseStep 1319 = 1979) R1979
theorem R1335 : ∃ j : ℕ, syracuseStep^[j] 1335 = 1 := reachStep (stepEq 1 (by rfl) ⟨1001, by rfl⟩ : syracuseStep 1335 = 2003) R2003
theorem R2561 : ∃ j : ℕ, syracuseStep^[j] 2561 = 1 := reachStep (stepEq 2 (by rfl) ⟨960, by rfl⟩ : syracuseStep 2561 = 1921) R1921
theorem R2567 : ∃ j : ℕ, syracuseStep^[j] 2567 = 1 := reachStep (stepEq 1 (by rfl) ⟨1925, by rfl⟩ : syracuseStep 2567 = 3851) R3851
theorem R2575 : ∃ j : ℕ, syracuseStep^[j] 2575 = 1 := reachStep (stepEq 1 (by rfl) ⟨1931, by rfl⟩ : syracuseStep 2575 = 3863) R3863
theorem R2579 : ∃ j : ℕ, syracuseStep^[j] 2579 = 1 := reachStep (stepEq 1 (by rfl) ⟨1934, by rfl⟩ : syracuseStep 2579 = 3869) R3869
theorem R2587 : ∃ j : ℕ, syracuseStep^[j] 2587 = 1 := reachStep (stepEq 1 (by rfl) ⟨1940, by rfl⟩ : syracuseStep 2587 = 3881) R3881
theorem R2597 : ∃ j : ℕ, syracuseStep^[j] 2597 = 1 := reachStep (stepEq 4 (by rfl) ⟨243, by rfl⟩ : syracuseStep 2597 = 487) R487
theorem R2599 : ∃ j : ℕ, syracuseStep^[j] 2599 = 1 := reachStep (stepEq 1 (by rfl) ⟨1949, by rfl⟩ : syracuseStep 2599 = 3899) R3899
theorem R2621 : ∃ j : ℕ, syracuseStep^[j] 2621 = 1 := reachStep (stepEq 3 (by rfl) ⟨491, by rfl⟩ : syracuseStep 2621 = 983) R983
theorem R2639 : ∃ j : ℕ, syracuseStep^[j] 2639 = 1 := reachStep (stepEq 1 (by rfl) ⟨1979, by rfl⟩ : syracuseStep 2639 = 3959) R3959
theorem R2651 : ∃ j : ℕ, syracuseStep^[j] 2651 = 1 := reachStep (stepEq 1 (by rfl) ⟨1988, by rfl⟩ : syracuseStep 2651 = 3977) R3977
theorem R2669 : ∃ j : ℕ, syracuseStep^[j] 2669 = 1 := reachStep (stepEq 3 (by rfl) ⟨500, by rfl⟩ : syracuseStep 2669 = 1001) R1001
theorem R5123 : ∃ j : ℕ, syracuseStep^[j] 5123 = 1 := reachStep (stepEq 1 (by rfl) ⟨3842, by rfl⟩ : syracuseStep 5123 = 7685) R7685
theorem R5127 : ∃ j : ℕ, syracuseStep^[j] 5127 = 1 := reachStep (stepEq 1 (by rfl) ⟨3845, by rfl⟩ : syracuseStep 5127 = 7691) R7691
theorem R5129 : ∃ j : ℕ, syracuseStep^[j] 5129 = 1 := reachStep (stepEq 2 (by rfl) ⟨1923, by rfl⟩ : syracuseStep 5129 = 3847) R3847
theorem R5135 : ∃ j : ℕ, syracuseStep^[j] 5135 = 1 := reachStep (stepEq 1 (by rfl) ⟨3851, by rfl⟩ : syracuseStep 5135 = 7703) R7703
theorem R5149 : ∃ j : ℕ, syracuseStep^[j] 5149 = 1 := reachStep (stepEq 3 (by rfl) ⟨965, by rfl⟩ : syracuseStep 5149 = 1931) R1931
theorem R5153 : ∃ j : ℕ, syracuseStep^[j] 5153 = 1 := reachStep (stepEq 2 (by rfl) ⟨1932, by rfl⟩ : syracuseStep 5153 = 3865) R3865
theorem R5157 : ∃ j : ℕ, syracuseStep^[j] 5157 = 1 := reachStep (stepEq 4 (by rfl) ⟨483, by rfl⟩ : syracuseStep 5157 = 967) R967
theorem R5159 : ∃ j : ℕ, syracuseStep^[j] 5159 = 1 := reachStep (stepEq 1 (by rfl) ⟨3869, by rfl⟩ : syracuseStep 5159 = 7739) R7739
theorem R5175 : ∃ j : ℕ, syracuseStep^[j] 5175 = 1 := reachStep (stepEq 1 (by rfl) ⟨3881, by rfl⟩ : syracuseStep 5175 = 7763) R7763
theorem R5197 : ∃ j : ℕ, syracuseStep^[j] 5197 = 1 := reachStep (stepEq 3 (by rfl) ⟨974, by rfl⟩ : syracuseStep 5197 = 1949) R1949
theorem R5199 : ∃ j : ℕ, syracuseStep^[j] 5199 = 1 := reachStep (stepEq 1 (by rfl) ⟨3899, by rfl⟩ : syracuseStep 5199 = 7799) R7799
theorem R5201 : ∃ j : ℕ, syracuseStep^[j] 5201 = 1 := reachStep (stepEq 2 (by rfl) ⟨1950, by rfl⟩ : syracuseStep 5201 = 3901) R3901
theorem R5217 : ∃ j : ℕ, syracuseStep^[j] 5217 = 1 := reachStep (stepEq 2 (by rfl) ⟨1956, by rfl⟩ : syracuseStep 5217 = 3913) R3913
theorem R5237 : ∃ j : ℕ, syracuseStep^[j] 5237 = 1 := reachStep (stepEq 5 (by rfl) ⟨245, by rfl⟩ : syracuseStep 5237 = 491) R491
theorem R5273 : ∃ j : ℕ, syracuseStep^[j] 5273 = 1 := reachStep (stepEq 2 (by rfl) ⟨1977, by rfl⟩ : syracuseStep 5273 = 3955) R3955
theorem R5277 : ∃ j : ℕ, syracuseStep^[j] 5277 = 1 := reachStep (stepEq 3 (by rfl) ⟨989, by rfl⟩ : syracuseStep 5277 = 1979) R1979
theorem R5295 : ∃ j : ℕ, syracuseStep^[j] 5295 = 1 := reachStep (stepEq 1 (by rfl) ⟨3971, by rfl⟩ : syracuseStep 5295 = 7943) R7943
theorem R5303 : ∃ j : ℕ, syracuseStep^[j] 5303 = 1 := reachStep (stepEq 1 (by rfl) ⟨3977, by rfl⟩ : syracuseStep 5303 = 7955) R7955
theorem R5307 : ∃ j : ℕ, syracuseStep^[j] 5307 = 1 := reachStep (stepEq 1 (by rfl) ⟨3980, by rfl⟩ : syracuseStep 5307 = 7961) R7961
theorem R5341 : ∃ j : ℕ, syracuseStep^[j] 5341 = 1 := reachStep (stepEq 3 (by rfl) ⟨1001, by rfl⟩ : syracuseStep 5341 = 2003) R2003
theorem R5385 : ∃ j : ℕ, syracuseStep^[j] 5385 = 1 := reachStep (stepEq 2 (by rfl) ⟨2019, by rfl⟩ : syracuseStep 5385 = 4039) R4039
theorem R5387 : ∃ j : ℕ, syracuseStep^[j] 5387 = 1 := reachStep (stepEq 1 (by rfl) ⟨4040, by rfl⟩ : syracuseStep 5387 = 8081) R8081
theorem R170585 : ∃ j : ℕ, syracuseStep^[j] 170585 = 1 := reachStep (stepEq 2 (by rfl) ⟨63969, by rfl⟩ : syracuseStep 170585 = 127939) R127939
theorem R41417 : ∃ j : ℕ, syracuseStep^[j] 41417 = 1 := reachStep (stepEq 2 (by rfl) ⟨15531, by rfl⟩ : syracuseStep 41417 = 31063) R31063
theorem R41471 : ∃ j : ℕ, syracuseStep^[j] 41471 = 1 := reachStep (stepEq 1 (by rfl) ⟨31103, by rfl⟩ : syracuseStep 41471 = 62207) R62207
theorem R42443 : ∃ j : ℕ, syracuseStep^[j] 42443 = 1 := reachStep (stepEq 1 (by rfl) ⟨31832, by rfl⟩ : syracuseStep 42443 = 63665) R63665
theorem R9919 : ∃ j : ℕ, syracuseStep^[j] 9919 = 1 := reachStep (stepEq 1 (by rfl) ⟨7439, by rfl⟩ : syracuseStep 9919 = 14879) R14879
theorem R42767 : ∃ j : ℕ, syracuseStep^[j] 42767 = 1 := reachStep (stepEq 1 (by rfl) ⟨32075, by rfl⟩ : syracuseStep 42767 = 64151) R64151
theorem R10151 : ∃ j : ℕ, syracuseStep^[j] 10151 = 1 := reachStep (stepEq 1 (by rfl) ⟨7613, by rfl⟩ : syracuseStep 10151 = 15227) R15227
theorem R10259 : ∃ j : ℕ, syracuseStep^[j] 10259 = 1 := reachStep (stepEq 1 (by rfl) ⟨7694, by rfl⟩ : syracuseStep 10259 = 15389) R15389
theorem R10273 : ∃ j : ℕ, syracuseStep^[j] 10273 = 1 := reachStep (stepEq 2 (by rfl) ⟨3852, by rfl⟩ : syracuseStep 10273 = 7705) R7705
theorem R10301 : ∃ j : ℕ, syracuseStep^[j] 10301 = 1 := reachStep (stepEq 3 (by rfl) ⟨1931, by rfl⟩ : syracuseStep 10301 = 3863) R3863
theorem R10307 : ∃ j : ℕ, syracuseStep^[j] 10307 = 1 := reachStep (stepEq 1 (by rfl) ⟨7730, by rfl⟩ : syracuseStep 10307 = 15461) R15461
theorem R10349 : ∃ j : ℕ, syracuseStep^[j] 10349 = 1 := reachStep (stepEq 3 (by rfl) ⟨1940, by rfl⟩ : syracuseStep 10349 = 3881) R3881
theorem R10367 : ∃ j : ℕ, syracuseStep^[j] 10367 = 1 := reachStep (stepEq 1 (by rfl) ⟨7775, by rfl⟩ : syracuseStep 10367 = 15551) R15551
theorem R10403 : ∃ j : ℕ, syracuseStep^[j] 10403 = 1 := reachStep (stepEq 1 (by rfl) ⟨7802, by rfl⟩ : syracuseStep 10403 = 15605) R15605
theorem R10435 : ∃ j : ℕ, syracuseStep^[j] 10435 = 1 := reachStep (stepEq 1 (by rfl) ⟨7826, by rfl⟩ : syracuseStep 10435 = 15653) R15653
theorem R10547 : ∃ j : ℕ, syracuseStep^[j] 10547 = 1 := reachStep (stepEq 1 (by rfl) ⟨7910, by rfl⟩ : syracuseStep 10547 = 15821) R15821
theorem R10655 : ∃ j : ℕ, syracuseStep^[j] 10655 = 1 := reachStep (stepEq 1 (by rfl) ⟨7991, by rfl⟩ : syracuseStep 10655 = 15983) R15983
theorem R10783 : ∃ j : ℕ, syracuseStep^[j] 10783 = 1 := reachStep (stepEq 1 (by rfl) ⟨8087, by rfl⟩ : syracuseStep 10783 = 16175) R16175
theorem R44135 : ∃ j : ℕ, syracuseStep^[j] 44135 = 1 := reachStep (stepEq 1 (by rfl) ⟨33101, by rfl⟩ : syracuseStep 44135 = 66203) R66203
theorem R20303 : ∃ j : ℕ, syracuseStep^[j] 20303 = 1 := reachStep (stepEq 1 (by rfl) ⟨15227, by rfl⟩ : syracuseStep 20303 = 30455) R30455
theorem R20503 : ∃ j : ℕ, syracuseStep^[j] 20503 = 1 := reachStep (stepEq 1 (by rfl) ⟨15377, by rfl⟩ : syracuseStep 20503 = 30755) R30755
theorem R20675 : ∃ j : ℕ, syracuseStep^[j] 20675 = 1 := reachStep (stepEq 1 (by rfl) ⟨15506, by rfl⟩ : syracuseStep 20675 = 31013) R31013
theorem R20735 : ∃ j : ℕ, syracuseStep^[j] 20735 = 1 := reachStep (stepEq 1 (by rfl) ⟨15551, by rfl⟩ : syracuseStep 20735 = 31103) R31103
theorem R20789 : ∃ j : ℕ, syracuseStep^[j] 20789 = 1 := reachStep (stepEq 5 (by rfl) ⟨974, by rfl⟩ : syracuseStep 20789 = 1949) R1949
theorem R21275 : ∃ j : ℕ, syracuseStep^[j] 21275 = 1 := reachStep (stepEq 1 (by rfl) ⟨15956, by rfl⟩ : syracuseStep 21275 = 31913) R31913
theorem R21383 : ∃ j : ℕ, syracuseStep^[j] 21383 = 1 := reachStep (stepEq 1 (by rfl) ⟨16037, by rfl⟩ : syracuseStep 21383 = 32075) R32075
theorem R859 : ∃ j : ℕ, syracuseStep^[j] 859 = 1 := reachStep (stepEq 1 (by rfl) ⟨644, by rfl⟩ : syracuseStep 859 = 1289) R1289
theorem R865 : ∃ j : ℕ, syracuseStep^[j] 865 = 1 := reachStep (stepEq 2 (by rfl) ⟨324, by rfl⟩ : syracuseStep 865 = 649) R649
theorem R873 : ∃ j : ℕ, syracuseStep^[j] 873 = 1 := reachStep (stepEq 2 (by rfl) ⟨327, by rfl⟩ : syracuseStep 873 = 655) R655
theorem R879 : ∃ j : ℕ, syracuseStep^[j] 879 = 1 := reachStep (stepEq 1 (by rfl) ⟨659, by rfl⟩ : syracuseStep 879 = 1319) R1319
theorem R889 : ∃ j : ℕ, syracuseStep^[j] 889 = 1 := reachStep (stepEq 2 (by rfl) ⟨333, by rfl⟩ : syracuseStep 889 = 667) R667
theorem R1707 : ∃ j : ℕ, syracuseStep^[j] 1707 = 1 := reachStep (stepEq 1 (by rfl) ⟨1280, by rfl⟩ : syracuseStep 1707 = 2561) R2561
theorem R1711 : ∃ j : ℕ, syracuseStep^[j] 1711 = 1 := reachStep (stepEq 1 (by rfl) ⟨1283, by rfl⟩ : syracuseStep 1711 = 2567) R2567
theorem R1719 : ∃ j : ℕ, syracuseStep^[j] 1719 = 1 := reachStep (stepEq 1 (by rfl) ⟨1289, by rfl⟩ : syracuseStep 1719 = 2579) R2579
theorem R1731 : ∃ j : ℕ, syracuseStep^[j] 1731 = 1 := reachStep (stepEq 1 (by rfl) ⟨1298, by rfl⟩ : syracuseStep 1731 = 2597) R2597
theorem R1745 : ∃ j : ℕ, syracuseStep^[j] 1745 = 1 := reachStep (stepEq 2 (by rfl) ⟨654, by rfl⟩ : syracuseStep 1745 = 1309) R1309
theorem R1747 : ∃ j : ℕ, syracuseStep^[j] 1747 = 1 := reachStep (stepEq 1 (by rfl) ⟨1310, by rfl⟩ : syracuseStep 1747 = 2621) R2621
theorem R1759 : ∃ j : ℕ, syracuseStep^[j] 1759 = 1 := reachStep (stepEq 1 (by rfl) ⟨1319, by rfl⟩ : syracuseStep 1759 = 2639) R2639
theorem R1767 : ∃ j : ℕ, syracuseStep^[j] 1767 = 1 := reachStep (stepEq 1 (by rfl) ⟨1325, by rfl⟩ : syracuseStep 1767 = 2651) R2651
theorem R1779 : ∃ j : ℕ, syracuseStep^[j] 1779 = 1 := reachStep (stepEq 1 (by rfl) ⟨1334, by rfl⟩ : syracuseStep 1779 = 2669) R2669
theorem R3415 : ∃ j : ℕ, syracuseStep^[j] 3415 = 1 := reachStep (stepEq 1 (by rfl) ⟨2561, by rfl⟩ : syracuseStep 3415 = 5123) R5123
theorem R3419 : ∃ j : ℕ, syracuseStep^[j] 3419 = 1 := reachStep (stepEq 1 (by rfl) ⟨2564, by rfl⟩ : syracuseStep 3419 = 5129) R5129
theorem R3423 : ∃ j : ℕ, syracuseStep^[j] 3423 = 1 := reachStep (stepEq 1 (by rfl) ⟨2567, by rfl⟩ : syracuseStep 3423 = 5135) R5135
theorem R3433 : ∃ j : ℕ, syracuseStep^[j] 3433 = 1 := reachStep (stepEq 2 (by rfl) ⟨1287, by rfl⟩ : syracuseStep 3433 = 2575) R2575
theorem R3435 : ∃ j : ℕ, syracuseStep^[j] 3435 = 1 := reachStep (stepEq 1 (by rfl) ⟨2576, by rfl⟩ : syracuseStep 3435 = 5153) R5153
theorem R3437 : ∃ j : ℕ, syracuseStep^[j] 3437 = 1 := reachStep (stepEq 3 (by rfl) ⟨644, by rfl⟩ : syracuseStep 3437 = 1289) R1289
theorem R3439 : ∃ j : ℕ, syracuseStep^[j] 3439 = 1 := reachStep (stepEq 1 (by rfl) ⟨2579, by rfl⟩ : syracuseStep 3439 = 5159) R5159
theorem R3449 : ∃ j : ℕ, syracuseStep^[j] 3449 = 1 := reachStep (stepEq 2 (by rfl) ⟨1293, by rfl⟩ : syracuseStep 3449 = 2587) R2587
theorem R3461 : ∃ j : ℕ, syracuseStep^[j] 3461 = 1 := reachStep (stepEq 4 (by rfl) ⟨324, by rfl⟩ : syracuseStep 3461 = 649) R649
theorem R3465 : ∃ j : ℕ, syracuseStep^[j] 3465 = 1 := reachStep (stepEq 2 (by rfl) ⟨1299, by rfl⟩ : syracuseStep 3465 = 2599) R2599
theorem R3467 : ∃ j : ℕ, syracuseStep^[j] 3467 = 1 := reachStep (stepEq 1 (by rfl) ⟨2600, by rfl⟩ : syracuseStep 3467 = 5201) R5201
theorem R3491 : ∃ j : ℕ, syracuseStep^[j] 3491 = 1 := reachStep (stepEq 1 (by rfl) ⟨2618, by rfl⟩ : syracuseStep 3491 = 5237) R5237
theorem R3493 : ∃ j : ℕ, syracuseStep^[j] 3493 = 1 := reachStep (stepEq 4 (by rfl) ⟨327, by rfl⟩ : syracuseStep 3493 = 655) R655
theorem R3515 : ∃ j : ℕ, syracuseStep^[j] 3515 = 1 := reachStep (stepEq 1 (by rfl) ⟨2636, by rfl⟩ : syracuseStep 3515 = 5273) R5273
theorem R3517 : ∃ j : ℕ, syracuseStep^[j] 3517 = 1 := reachStep (stepEq 3 (by rfl) ⟨659, by rfl⟩ : syracuseStep 3517 = 1319) R1319
theorem R3535 : ∃ j : ℕ, syracuseStep^[j] 3535 = 1 := reachStep (stepEq 1 (by rfl) ⟨2651, by rfl⟩ : syracuseStep 3535 = 5303) R5303
theorem R3557 : ∃ j : ℕ, syracuseStep^[j] 3557 = 1 := reachStep (stepEq 4 (by rfl) ⟨333, by rfl⟩ : syracuseStep 3557 = 667) R667
theorem R3591 : ∃ j : ℕ, syracuseStep^[j] 3591 = 1 := reachStep (stepEq 1 (by rfl) ⟨2693, by rfl⟩ : syracuseStep 3591 = 5387) R5387
theorem R6767 : ∃ j : ℕ, syracuseStep^[j] 6767 = 1 := reachStep (stepEq 1 (by rfl) ⟨5075, by rfl⟩ : syracuseStep 6767 = 10151) R10151
theorem R6839 : ∃ j : ℕ, syracuseStep^[j] 6839 = 1 := reachStep (stepEq 1 (by rfl) ⟨5129, by rfl⟩ : syracuseStep 6839 = 10259) R10259
theorem R6845 : ∃ j : ℕ, syracuseStep^[j] 6845 = 1 := reachStep (stepEq 3 (by rfl) ⟨1283, by rfl⟩ : syracuseStep 6845 = 2567) R2567
theorem R6871 : ∃ j : ℕ, syracuseStep^[j] 6871 = 1 := reachStep (stepEq 1 (by rfl) ⟨5153, by rfl⟩ : syracuseStep 6871 = 10307) R10307
theorem R6899 : ∃ j : ℕ, syracuseStep^[j] 6899 = 1 := reachStep (stepEq 1 (by rfl) ⟨5174, by rfl⟩ : syracuseStep 6899 = 10349) R10349
theorem R6911 : ∃ j : ℕ, syracuseStep^[j] 6911 = 1 := reachStep (stepEq 1 (by rfl) ⟨5183, by rfl⟩ : syracuseStep 6911 = 10367) R10367
theorem R6925 : ∃ j : ℕ, syracuseStep^[j] 6925 = 1 := reachStep (stepEq 3 (by rfl) ⟨1298, by rfl⟩ : syracuseStep 6925 = 2597) R2597
theorem R6929 : ∃ j : ℕ, syracuseStep^[j] 6929 = 1 := reachStep (stepEq 2 (by rfl) ⟨2598, by rfl⟩ : syracuseStep 6929 = 5197) R5197
theorem R6935 : ∃ j : ℕ, syracuseStep^[j] 6935 = 1 := reachStep (stepEq 1 (by rfl) ⟨5201, by rfl⟩ : syracuseStep 6935 = 10403) R10403
theorem R6989 : ∃ j : ℕ, syracuseStep^[j] 6989 = 1 := reachStep (stepEq 3 (by rfl) ⟨1310, by rfl⟩ : syracuseStep 6989 = 2621) R2621
theorem R7031 : ∃ j : ℕ, syracuseStep^[j] 7031 = 1 := reachStep (stepEq 1 (by rfl) ⟨5273, by rfl⟩ : syracuseStep 7031 = 10547) R10547
theorem R7037 : ∃ j : ℕ, syracuseStep^[j] 7037 = 1 := reachStep (stepEq 3 (by rfl) ⟨1319, by rfl⟩ : syracuseStep 7037 = 2639) R2639
theorem R7069 : ∃ j : ℕ, syracuseStep^[j] 7069 = 1 := reachStep (stepEq 3 (by rfl) ⟨1325, by rfl⟩ : syracuseStep 7069 = 2651) R2651
theorem R7103 : ∃ j : ℕ, syracuseStep^[j] 7103 = 1 := reachStep (stepEq 1 (by rfl) ⟨5327, by rfl⟩ : syracuseStep 7103 = 10655) R10655
theorem R7121 : ∃ j : ℕ, syracuseStep^[j] 7121 = 1 := reachStep (stepEq 2 (by rfl) ⟨2670, by rfl⟩ : syracuseStep 7121 = 5341) R5341
theorem R109349 : ∃ j : ℕ, syracuseStep^[j] 109349 = 1 := reachStep (stepEq 4 (by rfl) ⟨10251, by rfl⟩ : syracuseStep 109349 = 20503) R20503
theorem R13225 : ∃ j : ℕ, syracuseStep^[j] 13225 = 1 := reachStep (stepEq 2 (by rfl) ⟨4959, by rfl⟩ : syracuseStep 13225 = 9919) R9919
theorem R13535 : ∃ j : ℕ, syracuseStep^[j] 13535 = 1 := reachStep (stepEq 1 (by rfl) ⟨10151, by rfl⟩ : syracuseStep 13535 = 20303) R20303
theorem R13661 : ∃ j : ℕ, syracuseStep^[j] 13661 = 1 := reachStep (stepEq 3 (by rfl) ⟨2561, by rfl⟩ : syracuseStep 13661 = 5123) R5123
theorem R13697 : ∃ j : ℕ, syracuseStep^[j] 13697 = 1 := reachStep (stepEq 2 (by rfl) ⟨5136, by rfl⟩ : syracuseStep 13697 = 10273) R10273
theorem R13733 : ∃ j : ℕ, syracuseStep^[j] 13733 = 1 := reachStep (stepEq 4 (by rfl) ⟨1287, by rfl⟩ : syracuseStep 13733 = 2575) R2575
theorem R13783 : ∃ j : ℕ, syracuseStep^[j] 13783 = 1 := reachStep (stepEq 1 (by rfl) ⟨10337, by rfl⟩ : syracuseStep 13783 = 20675) R20675
theorem R13823 : ∃ j : ℕ, syracuseStep^[j] 13823 = 1 := reachStep (stepEq 1 (by rfl) ⟨10367, by rfl⟩ : syracuseStep 13823 = 20735) R20735
theorem R13859 : ∃ j : ℕ, syracuseStep^[j] 13859 = 1 := reachStep (stepEq 1 (by rfl) ⟨10394, by rfl⟩ : syracuseStep 13859 = 20789) R20789
theorem R13913 : ∃ j : ℕ, syracuseStep^[j] 13913 = 1 := reachStep (stepEq 2 (by rfl) ⟨5217, by rfl⟩ : syracuseStep 13913 = 10435) R10435
theorem R14183 : ∃ j : ℕ, syracuseStep^[j] 14183 = 1 := reachStep (stepEq 1 (by rfl) ⟨10637, by rfl⟩ : syracuseStep 14183 = 21275) R21275
theorem R14255 : ∃ j : ℕ, syracuseStep^[j] 14255 = 1 := reachStep (stepEq 1 (by rfl) ⟨10691, by rfl⟩ : syracuseStep 14255 = 21383) R21383
theorem R14377 : ∃ j : ℕ, syracuseStep^[j] 14377 = 1 := reachStep (stepEq 2 (by rfl) ⟨5391, by rfl⟩ : syracuseStep 14377 = 10783) R10783
theorem R113723 : ∃ j : ℕ, syracuseStep^[j] 113723 = 1 := reachStep (stepEq 1 (by rfl) ⟨85292, by rfl⟩ : syracuseStep 113723 = 170585) R170585
theorem R27337 : ∃ j : ℕ, syracuseStep^[j] 27337 = 1 := reachStep (stepEq 2 (by rfl) ⟨10251, by rfl⟩ : syracuseStep 27337 = 20503) R20503
theorem R27469 : ∃ j : ℕ, syracuseStep^[j] 27469 = 1 := reachStep (stepEq 3 (by rfl) ⟨5150, by rfl⟩ : syracuseStep 27469 = 10301) R10301
theorem R27611 : ∃ j : ℕ, syracuseStep^[j] 27611 = 1 := reachStep (stepEq 1 (by rfl) ⟨20708, by rfl⟩ : syracuseStep 27611 = 41417) R41417
theorem R27647 : ∃ j : ℕ, syracuseStep^[j] 27647 = 1 := reachStep (stepEq 1 (by rfl) ⟨20735, by rfl⟩ : syracuseStep 27647 = 41471) R41471
theorem R27701 : ∃ j : ℕ, syracuseStep^[j] 27701 = 1 := reachStep (stepEq 5 (by rfl) ⟨1298, by rfl⟩ : syracuseStep 27701 = 2597) R2597
theorem R28295 : ∃ j : ℕ, syracuseStep^[j] 28295 = 1 := reachStep (stepEq 1 (by rfl) ⟨21221, by rfl⟩ : syracuseStep 28295 = 42443) R42443
theorem R28511 : ∃ j : ℕ, syracuseStep^[j] 28511 = 1 := reachStep (stepEq 1 (by rfl) ⟨21383, by rfl⟩ : syracuseStep 28511 = 42767) R42767
theorem R29423 : ∃ j : ℕ, syracuseStep^[j] 29423 = 1 := reachStep (stepEq 1 (by rfl) ⟨22067, by rfl⟩ : syracuseStep 29423 = 44135) R44135
theorem R1145 : ∃ j : ℕ, syracuseStep^[j] 1145 = 1 := reachStep (stepEq 2 (by rfl) ⟨429, by rfl⟩ : syracuseStep 1145 = 859) R859
theorem R1153 : ∃ j : ℕ, syracuseStep^[j] 1153 = 1 := reachStep (stepEq 2 (by rfl) ⟨432, by rfl⟩ : syracuseStep 1153 = 865) R865
theorem R1163 : ∃ j : ℕ, syracuseStep^[j] 1163 = 1 := reachStep (stepEq 1 (by rfl) ⟨872, by rfl⟩ : syracuseStep 1163 = 1745) R1745
theorem R1185 : ∃ j : ℕ, syracuseStep^[j] 1185 = 1 := reachStep (stepEq 2 (by rfl) ⟨444, by rfl⟩ : syracuseStep 1185 = 889) R889
theorem R2279 : ∃ j : ℕ, syracuseStep^[j] 2279 = 1 := reachStep (stepEq 1 (by rfl) ⟨1709, by rfl⟩ : syracuseStep 2279 = 3419) R3419
theorem R2281 : ∃ j : ℕ, syracuseStep^[j] 2281 = 1 := reachStep (stepEq 2 (by rfl) ⟨855, by rfl⟩ : syracuseStep 2281 = 1711) R1711
theorem R2291 : ∃ j : ℕ, syracuseStep^[j] 2291 = 1 := reachStep (stepEq 1 (by rfl) ⟨1718, by rfl⟩ : syracuseStep 2291 = 3437) R3437
theorem R2299 : ∃ j : ℕ, syracuseStep^[j] 2299 = 1 := reachStep (stepEq 1 (by rfl) ⟨1724, by rfl⟩ : syracuseStep 2299 = 3449) R3449
theorem R2307 : ∃ j : ℕ, syracuseStep^[j] 2307 = 1 := reachStep (stepEq 1 (by rfl) ⟨1730, by rfl⟩ : syracuseStep 2307 = 3461) R3461
theorem R2311 : ∃ j : ℕ, syracuseStep^[j] 2311 = 1 := reachStep (stepEq 1 (by rfl) ⟨1733, by rfl⟩ : syracuseStep 2311 = 3467) R3467
theorem R2327 : ∃ j : ℕ, syracuseStep^[j] 2327 = 1 := reachStep (stepEq 1 (by rfl) ⟨1745, by rfl⟩ : syracuseStep 2327 = 3491) R3491
theorem R2329 : ∃ j : ℕ, syracuseStep^[j] 2329 = 1 := reachStep (stepEq 2 (by rfl) ⟨873, by rfl⟩ : syracuseStep 2329 = 1747) R1747
theorem R2343 : ∃ j : ℕ, syracuseStep^[j] 2343 = 1 := reachStep (stepEq 1 (by rfl) ⟨1757, by rfl⟩ : syracuseStep 2343 = 3515) R3515
theorem R2345 : ∃ j : ℕ, syracuseStep^[j] 2345 = 1 := reachStep (stepEq 2 (by rfl) ⟨879, by rfl⟩ : syracuseStep 2345 = 1759) R1759
theorem R2371 : ∃ j : ℕ, syracuseStep^[j] 2371 = 1 := reachStep (stepEq 1 (by rfl) ⟨1778, by rfl⟩ : syracuseStep 2371 = 3557) R3557
theorem R36449 : ∃ j : ℕ, syracuseStep^[j] 36449 = 1 := reachStep (stepEq 2 (by rfl) ⟨13668, by rfl⟩ : syracuseStep 36449 = 27337) R27337
theorem R36625 : ∃ j : ℕ, syracuseStep^[j] 36625 = 1 := reachStep (stepEq 2 (by rfl) ⟨13734, by rfl⟩ : syracuseStep 36625 = 27469) R27469
theorem R4511 : ∃ j : ℕ, syracuseStep^[j] 4511 = 1 := reachStep (stepEq 1 (by rfl) ⟨3383, by rfl⟩ : syracuseStep 4511 = 6767) R6767
theorem R4553 : ∃ j : ℕ, syracuseStep^[j] 4553 = 1 := reachStep (stepEq 2 (by rfl) ⟨1707, by rfl⟩ : syracuseStep 4553 = 3415) R3415
theorem R4559 : ∃ j : ℕ, syracuseStep^[j] 4559 = 1 := reachStep (stepEq 1 (by rfl) ⟨3419, by rfl⟩ : syracuseStep 4559 = 6839) R6839
theorem R4563 : ∃ j : ℕ, syracuseStep^[j] 4563 = 1 := reachStep (stepEq 1 (by rfl) ⟨3422, by rfl⟩ : syracuseStep 4563 = 6845) R6845
theorem R4577 : ∃ j : ℕ, syracuseStep^[j] 4577 = 1 := reachStep (stepEq 2 (by rfl) ⟨1716, by rfl⟩ : syracuseStep 4577 = 3433) R3433
theorem R4581 : ∃ j : ℕ, syracuseStep^[j] 4581 = 1 := reachStep (stepEq 4 (by rfl) ⟨429, by rfl⟩ : syracuseStep 4581 = 859) R859
theorem R4585 : ∃ j : ℕ, syracuseStep^[j] 4585 = 1 := reachStep (stepEq 2 (by rfl) ⟨1719, by rfl⟩ : syracuseStep 4585 = 3439) R3439
theorem R4599 : ∃ j : ℕ, syracuseStep^[j] 4599 = 1 := reachStep (stepEq 1 (by rfl) ⟨3449, by rfl⟩ : syracuseStep 4599 = 6899) R6899
theorem R4607 : ∃ j : ℕ, syracuseStep^[j] 4607 = 1 := reachStep (stepEq 1 (by rfl) ⟨3455, by rfl⟩ : syracuseStep 4607 = 6911) R6911
theorem R4613 : ∃ j : ℕ, syracuseStep^[j] 4613 = 1 := reachStep (stepEq 4 (by rfl) ⟨432, by rfl⟩ : syracuseStep 4613 = 865) R865
theorem R4619 : ∃ j : ℕ, syracuseStep^[j] 4619 = 1 := reachStep (stepEq 1 (by rfl) ⟨3464, by rfl⟩ : syracuseStep 4619 = 6929) R6929
theorem R4623 : ∃ j : ℕ, syracuseStep^[j] 4623 = 1 := reachStep (stepEq 1 (by rfl) ⟨3467, by rfl⟩ : syracuseStep 4623 = 6935) R6935
theorem R4653 : ∃ j : ℕ, syracuseStep^[j] 4653 = 1 := reachStep (stepEq 3 (by rfl) ⟨872, by rfl⟩ : syracuseStep 4653 = 1745) R1745
theorem R4657 : ∃ j : ℕ, syracuseStep^[j] 4657 = 1 := reachStep (stepEq 2 (by rfl) ⟨1746, by rfl⟩ : syracuseStep 4657 = 3493) R3493
theorem R4659 : ∃ j : ℕ, syracuseStep^[j] 4659 = 1 := reachStep (stepEq 1 (by rfl) ⟨3494, by rfl⟩ : syracuseStep 4659 = 6989) R6989
theorem R4687 : ∃ j : ℕ, syracuseStep^[j] 4687 = 1 := reachStep (stepEq 1 (by rfl) ⟨3515, by rfl⟩ : syracuseStep 4687 = 7031) R7031
theorem R4689 : ∃ j : ℕ, syracuseStep^[j] 4689 = 1 := reachStep (stepEq 2 (by rfl) ⟨1758, by rfl⟩ : syracuseStep 4689 = 3517) R3517
theorem R4691 : ∃ j : ℕ, syracuseStep^[j] 4691 = 1 := reachStep (stepEq 1 (by rfl) ⟨3518, by rfl⟩ : syracuseStep 4691 = 7037) R7037
theorem R4713 : ∃ j : ℕ, syracuseStep^[j] 4713 = 1 := reachStep (stepEq 2 (by rfl) ⟨1767, by rfl⟩ : syracuseStep 4713 = 3535) R3535
theorem R4735 : ∃ j : ℕ, syracuseStep^[j] 4735 = 1 := reachStep (stepEq 1 (by rfl) ⟨3551, by rfl⟩ : syracuseStep 4735 = 7103) R7103
theorem R4741 : ∃ j : ℕ, syracuseStep^[j] 4741 = 1 := reachStep (stepEq 4 (by rfl) ⟨444, by rfl⟩ : syracuseStep 4741 = 889) R889
theorem R4747 : ∃ j : ℕ, syracuseStep^[j] 4747 = 1 := reachStep (stepEq 1 (by rfl) ⟨3560, by rfl⟩ : syracuseStep 4747 = 7121) R7121
theorem R72899 : ∃ j : ℕ, syracuseStep^[j] 72899 = 1 := reachStep (stepEq 1 (by rfl) ⟨54674, by rfl⟩ : syracuseStep 72899 = 109349) R109349
theorem R9023 : ∃ j : ℕ, syracuseStep^[j] 9023 = 1 := reachStep (stepEq 1 (by rfl) ⟨6767, by rfl⟩ : syracuseStep 9023 = 13535) R13535
theorem R9107 : ∃ j : ℕ, syracuseStep^[j] 9107 = 1 := reachStep (stepEq 1 (by rfl) ⟨6830, by rfl⟩ : syracuseStep 9107 = 13661) R13661
theorem R9125 : ∃ j : ℕ, syracuseStep^[j] 9125 = 1 := reachStep (stepEq 4 (by rfl) ⟨855, by rfl⟩ : syracuseStep 9125 = 1711) R1711
theorem R9131 : ∃ j : ℕ, syracuseStep^[j] 9131 = 1 := reachStep (stepEq 1 (by rfl) ⟨6848, by rfl⟩ : syracuseStep 9131 = 13697) R13697
theorem R9155 : ∃ j : ℕ, syracuseStep^[j] 9155 = 1 := reachStep (stepEq 1 (by rfl) ⟨6866, by rfl⟩ : syracuseStep 9155 = 13733) R13733
theorem R9161 : ∃ j : ℕ, syracuseStep^[j] 9161 = 1 := reachStep (stepEq 2 (by rfl) ⟨3435, by rfl⟩ : syracuseStep 9161 = 6871) R6871
theorem R9197 : ∃ j : ℕ, syracuseStep^[j] 9197 = 1 := reachStep (stepEq 3 (by rfl) ⟨1724, by rfl⟩ : syracuseStep 9197 = 3449) R3449
theorem R9215 : ∃ j : ℕ, syracuseStep^[j] 9215 = 1 := reachStep (stepEq 1 (by rfl) ⟨6911, by rfl⟩ : syracuseStep 9215 = 13823) R13823
theorem R9233 : ∃ j : ℕ, syracuseStep^[j] 9233 = 1 := reachStep (stepEq 2 (by rfl) ⟨3462, by rfl⟩ : syracuseStep 9233 = 6925) R6925
theorem R9239 : ∃ j : ℕ, syracuseStep^[j] 9239 = 1 := reachStep (stepEq 1 (by rfl) ⟨6929, by rfl⟩ : syracuseStep 9239 = 13859) R13859
theorem R9245 : ∃ j : ℕ, syracuseStep^[j] 9245 = 1 := reachStep (stepEq 3 (by rfl) ⟨1733, by rfl⟩ : syracuseStep 9245 = 3467) R3467
theorem R9275 : ∃ j : ℕ, syracuseStep^[j] 9275 = 1 := reachStep (stepEq 1 (by rfl) ⟨6956, by rfl⟩ : syracuseStep 9275 = 13913) R13913
theorem R9317 : ∃ j : ℕ, syracuseStep^[j] 9317 = 1 := reachStep (stepEq 4 (by rfl) ⟨873, by rfl⟩ : syracuseStep 9317 = 1747) R1747
theorem R9425 : ∃ j : ℕ, syracuseStep^[j] 9425 = 1 := reachStep (stepEq 2 (by rfl) ⟨3534, by rfl⟩ : syracuseStep 9425 = 7069) R7069
theorem R9455 : ∃ j : ℕ, syracuseStep^[j] 9455 = 1 := reachStep (stepEq 1 (by rfl) ⟨7091, by rfl⟩ : syracuseStep 9455 = 14183) R14183
theorem R9485 : ∃ j : ℕ, syracuseStep^[j] 9485 = 1 := reachStep (stepEq 3 (by rfl) ⟨1778, by rfl⟩ : syracuseStep 9485 = 3557) R3557
theorem R9503 : ∃ j : ℕ, syracuseStep^[j] 9503 = 1 := reachStep (stepEq 1 (by rfl) ⟨7127, by rfl⟩ : syracuseStep 9503 = 14255) R14255
theorem R75815 : ∃ j : ℕ, syracuseStep^[j] 75815 = 1 := reachStep (stepEq 1 (by rfl) ⟨56861, by rfl⟩ : syracuseStep 75815 = 113723) R113723
theorem R17633 : ∃ j : ℕ, syracuseStep^[j] 17633 = 1 := reachStep (stepEq 2 (by rfl) ⟨6612, by rfl⟩ : syracuseStep 17633 = 13225) R13225
theorem R18377 : ∃ j : ℕ, syracuseStep^[j] 18377 = 1 := reachStep (stepEq 2 (by rfl) ⟨6891, by rfl⟩ : syracuseStep 18377 = 13783) R13783
theorem R18407 : ∃ j : ℕ, syracuseStep^[j] 18407 = 1 := reachStep (stepEq 1 (by rfl) ⟨13805, by rfl⟩ : syracuseStep 18407 = 27611) R27611
theorem R18431 : ∃ j : ℕ, syracuseStep^[j] 18431 = 1 := reachStep (stepEq 1 (by rfl) ⟨13823, by rfl⟩ : syracuseStep 18431 = 27647) R27647
theorem R18467 : ∃ j : ℕ, syracuseStep^[j] 18467 = 1 := reachStep (stepEq 1 (by rfl) ⟨13850, by rfl⟩ : syracuseStep 18467 = 27701) R27701
theorem R18629 : ∃ j : ℕ, syracuseStep^[j] 18629 = 1 := reachStep (stepEq 4 (by rfl) ⟨1746, by rfl⟩ : syracuseStep 18629 = 3493) R3493
theorem R18749 : ∃ j : ℕ, syracuseStep^[j] 18749 = 1 := reachStep (stepEq 3 (by rfl) ⟨3515, by rfl⟩ : syracuseStep 18749 = 7031) R7031
theorem R18863 : ∃ j : ℕ, syracuseStep^[j] 18863 = 1 := reachStep (stepEq 1 (by rfl) ⟨14147, by rfl⟩ : syracuseStep 18863 = 28295) R28295
theorem R19007 : ∃ j : ℕ, syracuseStep^[j] 19007 = 1 := reachStep (stepEq 1 (by rfl) ⟨14255, by rfl⟩ : syracuseStep 19007 = 28511) R28511
theorem R19169 : ∃ j : ℕ, syracuseStep^[j] 19169 = 1 := reachStep (stepEq 2 (by rfl) ⟨7188, by rfl⟩ : syracuseStep 19169 = 14377) R14377
theorem R19615 : ∃ j : ℕ, syracuseStep^[j] 19615 = 1 := reachStep (stepEq 1 (by rfl) ⟨14711, by rfl⟩ : syracuseStep 19615 = 29423) R29423
theorem R763 : ∃ j : ℕ, syracuseStep^[j] 763 = 1 := reachStep (stepEq 1 (by rfl) ⟨572, by rfl⟩ : syracuseStep 763 = 1145) R1145
theorem R775 : ∃ j : ℕ, syracuseStep^[j] 775 = 1 := reachStep (stepEq 1 (by rfl) ⟨581, by rfl⟩ : syracuseStep 775 = 1163) R1163
theorem R1519 : ∃ j : ℕ, syracuseStep^[j] 1519 = 1 := reachStep (stepEq 1 (by rfl) ⟨1139, by rfl⟩ : syracuseStep 1519 = 2279) R2279
theorem R1527 : ∃ j : ℕ, syracuseStep^[j] 1527 = 1 := reachStep (stepEq 1 (by rfl) ⟨1145, by rfl⟩ : syracuseStep 1527 = 2291) R2291
theorem R1537 : ∃ j : ℕ, syracuseStep^[j] 1537 = 1 := reachStep (stepEq 2 (by rfl) ⟨576, by rfl⟩ : syracuseStep 1537 = 1153) R1153
theorem R1551 : ∃ j : ℕ, syracuseStep^[j] 1551 = 1 := reachStep (stepEq 1 (by rfl) ⟨1163, by rfl⟩ : syracuseStep 1551 = 2327) R2327
theorem R1563 : ∃ j : ℕ, syracuseStep^[j] 1563 = 1 := reachStep (stepEq 1 (by rfl) ⟨1172, by rfl⟩ : syracuseStep 1563 = 2345) R2345
theorem R3007 : ∃ j : ℕ, syracuseStep^[j] 3007 = 1 := reachStep (stepEq 1 (by rfl) ⟨2255, by rfl⟩ : syracuseStep 3007 = 4511) R4511
theorem R3035 : ∃ j : ℕ, syracuseStep^[j] 3035 = 1 := reachStep (stepEq 1 (by rfl) ⟨2276, by rfl⟩ : syracuseStep 3035 = 4553) R4553
theorem R3039 : ∃ j : ℕ, syracuseStep^[j] 3039 = 1 := reachStep (stepEq 1 (by rfl) ⟨2279, by rfl⟩ : syracuseStep 3039 = 4559) R4559
theorem R3041 : ∃ j : ℕ, syracuseStep^[j] 3041 = 1 := reachStep (stepEq 2 (by rfl) ⟨1140, by rfl⟩ : syracuseStep 3041 = 2281) R2281
theorem R3051 : ∃ j : ℕ, syracuseStep^[j] 3051 = 1 := reachStep (stepEq 1 (by rfl) ⟨2288, by rfl⟩ : syracuseStep 3051 = 4577) R4577
theorem R3053 : ∃ j : ℕ, syracuseStep^[j] 3053 = 1 := reachStep (stepEq 3 (by rfl) ⟨572, by rfl⟩ : syracuseStep 3053 = 1145) R1145
theorem R3065 : ∃ j : ℕ, syracuseStep^[j] 3065 = 1 := reachStep (stepEq 2 (by rfl) ⟨1149, by rfl⟩ : syracuseStep 3065 = 2299) R2299
theorem R3071 : ∃ j : ℕ, syracuseStep^[j] 3071 = 1 := reachStep (stepEq 1 (by rfl) ⟨2303, by rfl⟩ : syracuseStep 3071 = 4607) R4607
theorem R3075 : ∃ j : ℕ, syracuseStep^[j] 3075 = 1 := reachStep (stepEq 1 (by rfl) ⟨2306, by rfl⟩ : syracuseStep 3075 = 4613) R4613
theorem R3079 : ∃ j : ℕ, syracuseStep^[j] 3079 = 1 := reachStep (stepEq 1 (by rfl) ⟨2309, by rfl⟩ : syracuseStep 3079 = 4619) R4619
theorem R3081 : ∃ j : ℕ, syracuseStep^[j] 3081 = 1 := reachStep (stepEq 2 (by rfl) ⟨1155, by rfl⟩ : syracuseStep 3081 = 2311) R2311
theorem R3101 : ∃ j : ℕ, syracuseStep^[j] 3101 = 1 := reachStep (stepEq 3 (by rfl) ⟨581, by rfl⟩ : syracuseStep 3101 = 1163) R1163
theorem R3105 : ∃ j : ℕ, syracuseStep^[j] 3105 = 1 := reachStep (stepEq 2 (by rfl) ⟨1164, by rfl⟩ : syracuseStep 3105 = 2329) R2329
theorem R3127 : ∃ j : ℕ, syracuseStep^[j] 3127 = 1 := reachStep (stepEq 1 (by rfl) ⟨2345, by rfl⟩ : syracuseStep 3127 = 4691) R4691
theorem R3161 : ∃ j : ℕ, syracuseStep^[j] 3161 = 1 := reachStep (stepEq 2 (by rfl) ⟨1185, by rfl⟩ : syracuseStep 3161 = 2371) R2371
theorem R6015 : ∃ j : ℕ, syracuseStep^[j] 6015 = 1 := reachStep (stepEq 1 (by rfl) ⟨4511, by rfl⟩ : syracuseStep 6015 = 9023) R9023
theorem R6071 : ∃ j : ℕ, syracuseStep^[j] 6071 = 1 := reachStep (stepEq 1 (by rfl) ⟨4553, by rfl⟩ : syracuseStep 6071 = 9107) R9107
theorem R6077 : ∃ j : ℕ, syracuseStep^[j] 6077 = 1 := reachStep (stepEq 3 (by rfl) ⟨1139, by rfl⟩ : syracuseStep 6077 = 2279) R2279
theorem R6083 : ∃ j : ℕ, syracuseStep^[j] 6083 = 1 := reachStep (stepEq 1 (by rfl) ⟨4562, by rfl⟩ : syracuseStep 6083 = 9125) R9125
theorem R6087 : ∃ j : ℕ, syracuseStep^[j] 6087 = 1 := reachStep (stepEq 1 (by rfl) ⟨4565, by rfl⟩ : syracuseStep 6087 = 9131) R9131
theorem R6103 : ∃ j : ℕ, syracuseStep^[j] 6103 = 1 := reachStep (stepEq 1 (by rfl) ⟨4577, by rfl⟩ : syracuseStep 6103 = 9155) R9155
theorem R6107 : ∃ j : ℕ, syracuseStep^[j] 6107 = 1 := reachStep (stepEq 1 (by rfl) ⟨4580, by rfl⟩ : syracuseStep 6107 = 9161) R9161
theorem R6109 : ∃ j : ℕ, syracuseStep^[j] 6109 = 1 := reachStep (stepEq 3 (by rfl) ⟨1145, by rfl⟩ : syracuseStep 6109 = 2291) R2291
theorem R6113 : ∃ j : ℕ, syracuseStep^[j] 6113 = 1 := reachStep (stepEq 2 (by rfl) ⟨2292, by rfl⟩ : syracuseStep 6113 = 4585) R4585
theorem R6131 : ∃ j : ℕ, syracuseStep^[j] 6131 = 1 := reachStep (stepEq 1 (by rfl) ⟨4598, by rfl⟩ : syracuseStep 6131 = 9197) R9197
theorem R6143 : ∃ j : ℕ, syracuseStep^[j] 6143 = 1 := reachStep (stepEq 1 (by rfl) ⟨4607, by rfl⟩ : syracuseStep 6143 = 9215) R9215
theorem R6149 : ∃ j : ℕ, syracuseStep^[j] 6149 = 1 := reachStep (stepEq 4 (by rfl) ⟨576, by rfl⟩ : syracuseStep 6149 = 1153) R1153
theorem R6155 : ∃ j : ℕ, syracuseStep^[j] 6155 = 1 := reachStep (stepEq 1 (by rfl) ⟨4616, by rfl⟩ : syracuseStep 6155 = 9233) R9233
theorem R6159 : ∃ j : ℕ, syracuseStep^[j] 6159 = 1 := reachStep (stepEq 1 (by rfl) ⟨4619, by rfl⟩ : syracuseStep 6159 = 9239) R9239
theorem R6163 : ∃ j : ℕ, syracuseStep^[j] 6163 = 1 := reachStep (stepEq 1 (by rfl) ⟨4622, by rfl⟩ : syracuseStep 6163 = 9245) R9245
theorem R6183 : ∃ j : ℕ, syracuseStep^[j] 6183 = 1 := reachStep (stepEq 1 (by rfl) ⟨4637, by rfl⟩ : syracuseStep 6183 = 9275) R9275
theorem R6205 : ∃ j : ℕ, syracuseStep^[j] 6205 = 1 := reachStep (stepEq 3 (by rfl) ⟨1163, by rfl⟩ : syracuseStep 6205 = 2327) R2327
theorem R6209 : ∃ j : ℕ, syracuseStep^[j] 6209 = 1 := reachStep (stepEq 2 (by rfl) ⟨2328, by rfl⟩ : syracuseStep 6209 = 4657) R4657
theorem R6211 : ∃ j : ℕ, syracuseStep^[j] 6211 = 1 := reachStep (stepEq 1 (by rfl) ⟨4658, by rfl⟩ : syracuseStep 6211 = 9317) R9317
theorem R6249 : ∃ j : ℕ, syracuseStep^[j] 6249 = 1 := reachStep (stepEq 2 (by rfl) ⟨2343, by rfl⟩ : syracuseStep 6249 = 4687) R4687
theorem R6253 : ∃ j : ℕ, syracuseStep^[j] 6253 = 1 := reachStep (stepEq 3 (by rfl) ⟨1172, by rfl⟩ : syracuseStep 6253 = 2345) R2345
theorem R6283 : ∃ j : ℕ, syracuseStep^[j] 6283 = 1 := reachStep (stepEq 1 (by rfl) ⟨4712, by rfl⟩ : syracuseStep 6283 = 9425) R9425
theorem R6303 : ∃ j : ℕ, syracuseStep^[j] 6303 = 1 := reachStep (stepEq 1 (by rfl) ⟨4727, by rfl⟩ : syracuseStep 6303 = 9455) R9455
theorem R6313 : ∃ j : ℕ, syracuseStep^[j] 6313 = 1 := reachStep (stepEq 2 (by rfl) ⟨2367, by rfl⟩ : syracuseStep 6313 = 4735) R4735
theorem R6321 : ∃ j : ℕ, syracuseStep^[j] 6321 = 1 := reachStep (stepEq 2 (by rfl) ⟨2370, by rfl⟩ : syracuseStep 6321 = 4741) R4741
theorem R6323 : ∃ j : ℕ, syracuseStep^[j] 6323 = 1 := reachStep (stepEq 1 (by rfl) ⟨4742, by rfl⟩ : syracuseStep 6323 = 9485) R9485
theorem R6329 : ∃ j : ℕ, syracuseStep^[j] 6329 = 1 := reachStep (stepEq 2 (by rfl) ⟨2373, by rfl⟩ : syracuseStep 6329 = 4747) R4747
theorem R6335 : ∃ j : ℕ, syracuseStep^[j] 6335 = 1 := reachStep (stepEq 1 (by rfl) ⟨4751, by rfl⟩ : syracuseStep 6335 = 9503) R9503
theorem R11755 : ∃ j : ℕ, syracuseStep^[j] 11755 = 1 := reachStep (stepEq 1 (by rfl) ⟨8816, by rfl⟩ : syracuseStep 11755 = 17633) R17633
theorem R12251 : ∃ j : ℕ, syracuseStep^[j] 12251 = 1 := reachStep (stepEq 1 (by rfl) ⟨9188, by rfl⟩ : syracuseStep 12251 = 18377) R18377
theorem R12271 : ∃ j : ℕ, syracuseStep^[j] 12271 = 1 := reachStep (stepEq 1 (by rfl) ⟨9203, by rfl⟩ : syracuseStep 12271 = 18407) R18407
theorem R12287 : ∃ j : ℕ, syracuseStep^[j] 12287 = 1 := reachStep (stepEq 1 (by rfl) ⟨9215, by rfl⟩ : syracuseStep 12287 = 18431) R18431
theorem R12311 : ∃ j : ℕ, syracuseStep^[j] 12311 = 1 := reachStep (stepEq 1 (by rfl) ⟨9233, by rfl⟩ : syracuseStep 12311 = 18467) R18467
theorem R12325 : ∃ j : ℕ, syracuseStep^[j] 12325 = 1 := reachStep (stepEq 4 (by rfl) ⟨1155, by rfl⟩ : syracuseStep 12325 = 2311) R2311
theorem R12419 : ∃ j : ℕ, syracuseStep^[j] 12419 = 1 := reachStep (stepEq 1 (by rfl) ⟨9314, by rfl⟩ : syracuseStep 12419 = 18629) R18629
theorem R12509 : ∃ j : ℕ, syracuseStep^[j] 12509 = 1 := reachStep (stepEq 3 (by rfl) ⟨2345, by rfl⟩ : syracuseStep 12509 = 4691) R4691
theorem R12575 : ∃ j : ℕ, syracuseStep^[j] 12575 = 1 := reachStep (stepEq 1 (by rfl) ⟨9431, by rfl⟩ : syracuseStep 12575 = 18863) R18863
theorem R12671 : ∃ j : ℕ, syracuseStep^[j] 12671 = 1 := reachStep (stepEq 1 (by rfl) ⟨9503, by rfl⟩ : syracuseStep 12671 = 19007) R19007
theorem R12779 : ∃ j : ℕ, syracuseStep^[j] 12779 = 1 := reachStep (stepEq 1 (by rfl) ⟨9584, by rfl⟩ : syracuseStep 12779 = 19169) R19169
theorem R48599 : ∃ j : ℕ, syracuseStep^[j] 48599 = 1 := reachStep (stepEq 1 (by rfl) ⟨36449, by rfl⟩ : syracuseStep 48599 = 72899) R72899
theorem R48833 : ∃ j : ℕ, syracuseStep^[j] 48833 = 1 := reachStep (stepEq 2 (by rfl) ⟨18312, by rfl⟩ : syracuseStep 48833 = 36625) R36625
theorem R49085 : ∃ j : ℕ, syracuseStep^[j] 49085 = 1 := reachStep (stepEq 3 (by rfl) ⟨9203, by rfl⟩ : syracuseStep 49085 = 18407) R18407
theorem R49997 : ∃ j : ℕ, syracuseStep^[j] 49997 = 1 := reachStep (stepEq 3 (by rfl) ⟨9374, by rfl⟩ : syracuseStep 49997 = 18749) R18749
theorem R50543 : ∃ j : ℕ, syracuseStep^[j] 50543 = 1 := reachStep (stepEq 1 (by rfl) ⟨37907, by rfl⟩ : syracuseStep 50543 = 75815) R75815
theorem R24299 : ∃ j : ℕ, syracuseStep^[j] 24299 = 1 := reachStep (stepEq 1 (by rfl) ⟨18224, by rfl⟩ : syracuseStep 24299 = 36449) R36449
theorem R26153 : ∃ j : ℕ, syracuseStep^[j] 26153 = 1 := reachStep (stepEq 2 (by rfl) ⟨9807, by rfl⟩ : syracuseStep 26153 = 19615) R19615
theorem R33533 : ∃ j : ℕ, syracuseStep^[j] 33533 = 1 := reachStep (stepEq 3 (by rfl) ⟨6287, by rfl⟩ : syracuseStep 33533 = 12575) R12575
theorem R33695 : ∃ j : ℕ, syracuseStep^[j] 33695 = 1 := reachStep (stepEq 1 (by rfl) ⟨25271, by rfl⟩ : syracuseStep 33695 = 50543) R50543
theorem R1017 : ∃ j : ℕ, syracuseStep^[j] 1017 = 1 := reachStep (stepEq 2 (by rfl) ⟨381, by rfl⟩ : syracuseStep 1017 = 763) R763
theorem R1033 : ∃ j : ℕ, syracuseStep^[j] 1033 = 1 := reachStep (stepEq 2 (by rfl) ⟨387, by rfl⟩ : syracuseStep 1033 = 775) R775
theorem R2023 : ∃ j : ℕ, syracuseStep^[j] 2023 = 1 := reachStep (stepEq 1 (by rfl) ⟨1517, by rfl⟩ : syracuseStep 2023 = 3035) R3035
theorem R2025 : ∃ j : ℕ, syracuseStep^[j] 2025 = 1 := reachStep (stepEq 2 (by rfl) ⟨759, by rfl⟩ : syracuseStep 2025 = 1519) R1519
theorem R2027 : ∃ j : ℕ, syracuseStep^[j] 2027 = 1 := reachStep (stepEq 1 (by rfl) ⟨1520, by rfl⟩ : syracuseStep 2027 = 3041) R3041
theorem R2035 : ∃ j : ℕ, syracuseStep^[j] 2035 = 1 := reachStep (stepEq 1 (by rfl) ⟨1526, by rfl⟩ : syracuseStep 2035 = 3053) R3053
theorem R2043 : ∃ j : ℕ, syracuseStep^[j] 2043 = 1 := reachStep (stepEq 1 (by rfl) ⟨1532, by rfl⟩ : syracuseStep 2043 = 3065) R3065
theorem R2047 : ∃ j : ℕ, syracuseStep^[j] 2047 = 1 := reachStep (stepEq 1 (by rfl) ⟨1535, by rfl⟩ : syracuseStep 2047 = 3071) R3071
theorem R2049 : ∃ j : ℕ, syracuseStep^[j] 2049 = 1 := reachStep (stepEq 2 (by rfl) ⟨768, by rfl⟩ : syracuseStep 2049 = 1537) R1537
theorem R2067 : ∃ j : ℕ, syracuseStep^[j] 2067 = 1 := reachStep (stepEq 1 (by rfl) ⟨1550, by rfl⟩ : syracuseStep 2067 = 3101) R3101
theorem R2107 : ∃ j : ℕ, syracuseStep^[j] 2107 = 1 := reachStep (stepEq 1 (by rfl) ⟨1580, by rfl⟩ : syracuseStep 2107 = 3161) R3161
theorem R133325 : ∃ j : ℕ, syracuseStep^[j] 133325 = 1 := reachStep (stepEq 3 (by rfl) ⟨24998, by rfl⟩ : syracuseStep 133325 = 49997) R49997
theorem R4009 : ∃ j : ℕ, syracuseStep^[j] 4009 = 1 := reachStep (stepEq 2 (by rfl) ⟨1503, by rfl⟩ : syracuseStep 4009 = 3007) R3007
theorem R4047 : ∃ j : ℕ, syracuseStep^[j] 4047 = 1 := reachStep (stepEq 1 (by rfl) ⟨3035, by rfl⟩ : syracuseStep 4047 = 6071) R6071
theorem R4051 : ∃ j : ℕ, syracuseStep^[j] 4051 = 1 := reachStep (stepEq 1 (by rfl) ⟨3038, by rfl⟩ : syracuseStep 4051 = 6077) R6077
theorem R4055 : ∃ j : ℕ, syracuseStep^[j] 4055 = 1 := reachStep (stepEq 1 (by rfl) ⟨3041, by rfl⟩ : syracuseStep 4055 = 6083) R6083
theorem R4069 : ∃ j : ℕ, syracuseStep^[j] 4069 = 1 := reachStep (stepEq 4 (by rfl) ⟨381, by rfl⟩ : syracuseStep 4069 = 763) R763
theorem R4071 : ∃ j : ℕ, syracuseStep^[j] 4071 = 1 := reachStep (stepEq 1 (by rfl) ⟨3053, by rfl⟩ : syracuseStep 4071 = 6107) R6107
theorem R4075 : ∃ j : ℕ, syracuseStep^[j] 4075 = 1 := reachStep (stepEq 1 (by rfl) ⟨3056, by rfl⟩ : syracuseStep 4075 = 6113) R6113
theorem R4087 : ∃ j : ℕ, syracuseStep^[j] 4087 = 1 := reachStep (stepEq 1 (by rfl) ⟨3065, by rfl⟩ : syracuseStep 4087 = 6131) R6131
theorem R4095 : ∃ j : ℕ, syracuseStep^[j] 4095 = 1 := reachStep (stepEq 1 (by rfl) ⟨3071, by rfl⟩ : syracuseStep 4095 = 6143) R6143
theorem R4099 : ∃ j : ℕ, syracuseStep^[j] 4099 = 1 := reachStep (stepEq 1 (by rfl) ⟨3074, by rfl⟩ : syracuseStep 4099 = 6149) R6149
theorem R4103 : ∃ j : ℕ, syracuseStep^[j] 4103 = 1 := reachStep (stepEq 1 (by rfl) ⟨3077, by rfl⟩ : syracuseStep 4103 = 6155) R6155
theorem R4105 : ∃ j : ℕ, syracuseStep^[j] 4105 = 1 := reachStep (stepEq 2 (by rfl) ⟨1539, by rfl⟩ : syracuseStep 4105 = 3079) R3079
theorem R4133 : ∃ j : ℕ, syracuseStep^[j] 4133 = 1 := reachStep (stepEq 4 (by rfl) ⟨387, by rfl⟩ : syracuseStep 4133 = 775) R775
theorem R4139 : ∃ j : ℕ, syracuseStep^[j] 4139 = 1 := reachStep (stepEq 1 (by rfl) ⟨3104, by rfl⟩ : syracuseStep 4139 = 6209) R6209
theorem R4169 : ∃ j : ℕ, syracuseStep^[j] 4169 = 1 := reachStep (stepEq 2 (by rfl) ⟨1563, by rfl⟩ : syracuseStep 4169 = 3127) R3127
theorem R4215 : ∃ j : ℕ, syracuseStep^[j] 4215 = 1 := reachStep (stepEq 1 (by rfl) ⟨3161, by rfl⟩ : syracuseStep 4215 = 6323) R6323
theorem R4219 : ∃ j : ℕ, syracuseStep^[j] 4219 = 1 := reachStep (stepEq 1 (by rfl) ⟨3164, by rfl⟩ : syracuseStep 4219 = 6329) R6329
theorem R4223 : ∃ j : ℕ, syracuseStep^[j] 4223 = 1 := reachStep (stepEq 1 (by rfl) ⟨3167, by rfl⟩ : syracuseStep 4223 = 6335) R6335
theorem R8093 : ∃ j : ℕ, syracuseStep^[j] 8093 = 1 := reachStep (stepEq 3 (by rfl) ⟨1517, by rfl⟩ : syracuseStep 8093 = 3035) R3035
theorem R8141 : ∃ j : ℕ, syracuseStep^[j] 8141 = 1 := reachStep (stepEq 3 (by rfl) ⟨1526, by rfl⟩ : syracuseStep 8141 = 3053) R3053
theorem R8167 : ∃ j : ℕ, syracuseStep^[j] 8167 = 1 := reachStep (stepEq 1 (by rfl) ⟨6125, by rfl⟩ : syracuseStep 8167 = 12251) R12251
theorem R8189 : ∃ j : ℕ, syracuseStep^[j] 8189 = 1 := reachStep (stepEq 3 (by rfl) ⟨1535, by rfl⟩ : syracuseStep 8189 = 3071) R3071
theorem R8191 : ∃ j : ℕ, syracuseStep^[j] 8191 = 1 := reachStep (stepEq 1 (by rfl) ⟨6143, by rfl⟩ : syracuseStep 8191 = 12287) R12287
theorem R8207 : ∃ j : ℕ, syracuseStep^[j] 8207 = 1 := reachStep (stepEq 1 (by rfl) ⟨6155, by rfl⟩ : syracuseStep 8207 = 12311) R12311
theorem R8273 : ∃ j : ℕ, syracuseStep^[j] 8273 = 1 := reachStep (stepEq 2 (by rfl) ⟨3102, by rfl⟩ : syracuseStep 8273 = 6205) R6205
theorem R8279 : ∃ j : ℕ, syracuseStep^[j] 8279 = 1 := reachStep (stepEq 1 (by rfl) ⟨6209, by rfl⟩ : syracuseStep 8279 = 12419) R12419
theorem R8339 : ∃ j : ℕ, syracuseStep^[j] 8339 = 1 := reachStep (stepEq 1 (by rfl) ⟨6254, by rfl⟩ : syracuseStep 8339 = 12509) R12509
theorem R8383 : ∃ j : ℕ, syracuseStep^[j] 8383 = 1 := reachStep (stepEq 1 (by rfl) ⟨6287, by rfl⟩ : syracuseStep 8383 = 12575) R12575
theorem R8417 : ∃ j : ℕ, syracuseStep^[j] 8417 = 1 := reachStep (stepEq 2 (by rfl) ⟨3156, by rfl⟩ : syracuseStep 8417 = 6313) R6313
theorem R8429 : ∃ j : ℕ, syracuseStep^[j] 8429 = 1 := reachStep (stepEq 3 (by rfl) ⟨1580, by rfl⟩ : syracuseStep 8429 = 3161) R3161
theorem R8447 : ∃ j : ℕ, syracuseStep^[j] 8447 = 1 := reachStep (stepEq 1 (by rfl) ⟨6335, by rfl⟩ : syracuseStep 8447 = 12671) R12671
theorem R8519 : ∃ j : ℕ, syracuseStep^[j] 8519 = 1 := reachStep (stepEq 1 (by rfl) ⟨6389, by rfl⟩ : syracuseStep 8519 = 12779) R12779
theorem R15673 : ∃ j : ℕ, syracuseStep^[j] 15673 = 1 := reachStep (stepEq 2 (by rfl) ⟨5877, by rfl⟩ : syracuseStep 15673 = 11755) R11755
theorem R16037 : ∃ j : ℕ, syracuseStep^[j] 16037 = 1 := reachStep (stepEq 4 (by rfl) ⟨1503, by rfl⟩ : syracuseStep 16037 = 3007) R3007
theorem R16199 : ∃ j : ℕ, syracuseStep^[j] 16199 = 1 := reachStep (stepEq 1 (by rfl) ⟨12149, by rfl⟩ : syracuseStep 16199 = 24299) R24299
theorem R16301 : ∃ j : ℕ, syracuseStep^[j] 16301 = 1 := reachStep (stepEq 3 (by rfl) ⟨3056, by rfl⟩ : syracuseStep 16301 = 6113) R6113
theorem R16361 : ∃ j : ℕ, syracuseStep^[j] 16361 = 1 := reachStep (stepEq 2 (by rfl) ⟨6135, by rfl⟩ : syracuseStep 16361 = 12271) R12271
theorem R16433 : ∃ j : ℕ, syracuseStep^[j] 16433 = 1 := reachStep (stepEq 2 (by rfl) ⟨6162, by rfl⟩ : syracuseStep 16433 = 12325) R12325
theorem R17435 : ∃ j : ℕ, syracuseStep^[j] 17435 = 1 := reachStep (stepEq 1 (by rfl) ⟨13076, by rfl⟩ : syracuseStep 17435 = 26153) R26153
theorem R62693 : ∃ j : ℕ, syracuseStep^[j] 62693 = 1 := reachStep (stepEq 4 (by rfl) ⟨5877, by rfl⟩ : syracuseStep 62693 = 11755) R11755
theorem R32399 : ∃ j : ℕ, syracuseStep^[j] 32399 = 1 := reachStep (stepEq 1 (by rfl) ⟨24299, by rfl⟩ : syracuseStep 32399 = 48599) R48599
theorem R32555 : ∃ j : ℕ, syracuseStep^[j] 32555 = 1 := reachStep (stepEq 1 (by rfl) ⟨24416, by rfl⟩ : syracuseStep 32555 = 48833) R48833
theorem R32669 : ∃ j : ℕ, syracuseStep^[j] 32669 = 1 := reachStep (stepEq 3 (by rfl) ⟨6125, by rfl⟩ : syracuseStep 32669 = 12251) R12251
theorem R32723 : ∃ j : ℕ, syracuseStep^[j] 32723 = 1 := reachStep (stepEq 1 (by rfl) ⟨24542, by rfl⟩ : syracuseStep 32723 = 49085) R49085
theorem R1351 : ∃ j : ℕ, syracuseStep^[j] 1351 = 1 := reachStep (stepEq 1 (by rfl) ⟨1013, by rfl⟩ : syracuseStep 1351 = 2027) R2027
theorem R1377 : ∃ j : ℕ, syracuseStep^[j] 1377 = 1 := reachStep (stepEq 2 (by rfl) ⟨516, by rfl⟩ : syracuseStep 1377 = 1033) R1033
theorem R2697 : ∃ j : ℕ, syracuseStep^[j] 2697 = 1 := reachStep (stepEq 2 (by rfl) ⟨1011, by rfl⟩ : syracuseStep 2697 = 2023) R2023
theorem R2703 : ∃ j : ℕ, syracuseStep^[j] 2703 = 1 := reachStep (stepEq 1 (by rfl) ⟨2027, by rfl⟩ : syracuseStep 2703 = 4055) R4055
theorem R2713 : ∃ j : ℕ, syracuseStep^[j] 2713 = 1 := reachStep (stepEq 2 (by rfl) ⟨1017, by rfl⟩ : syracuseStep 2713 = 2035) R2035
theorem R2729 : ∃ j : ℕ, syracuseStep^[j] 2729 = 1 := reachStep (stepEq 2 (by rfl) ⟨1023, by rfl⟩ : syracuseStep 2729 = 2047) R2047
theorem R2735 : ∃ j : ℕ, syracuseStep^[j] 2735 = 1 := reachStep (stepEq 1 (by rfl) ⟨2051, by rfl⟩ : syracuseStep 2735 = 4103) R4103
theorem R2755 : ∃ j : ℕ, syracuseStep^[j] 2755 = 1 := reachStep (stepEq 1 (by rfl) ⟨2066, by rfl⟩ : syracuseStep 2755 = 4133) R4133
theorem R2759 : ∃ j : ℕ, syracuseStep^[j] 2759 = 1 := reachStep (stepEq 1 (by rfl) ⟨2069, by rfl⟩ : syracuseStep 2759 = 4139) R4139
theorem R2779 : ∃ j : ℕ, syracuseStep^[j] 2779 = 1 := reachStep (stepEq 1 (by rfl) ⟨2084, by rfl⟩ : syracuseStep 2779 = 4169) R4169
theorem R2809 : ∃ j : ℕ, syracuseStep^[j] 2809 = 1 := reachStep (stepEq 2 (by rfl) ⟨1053, by rfl⟩ : syracuseStep 2809 = 2107) R2107
theorem R2815 : ∃ j : ℕ, syracuseStep^[j] 2815 = 1 := reachStep (stepEq 1 (by rfl) ⟨2111, by rfl⟩ : syracuseStep 2815 = 4223) R4223
theorem R5345 : ∃ j : ℕ, syracuseStep^[j] 5345 = 1 := reachStep (stepEq 2 (by rfl) ⟨2004, by rfl⟩ : syracuseStep 5345 = 4009) R4009
theorem R5395 : ∃ j : ℕ, syracuseStep^[j] 5395 = 1 := reachStep (stepEq 1 (by rfl) ⟨4046, by rfl⟩ : syracuseStep 5395 = 8093) R8093
theorem R5401 : ∃ j : ℕ, syracuseStep^[j] 5401 = 1 := reachStep (stepEq 2 (by rfl) ⟨2025, by rfl⟩ : syracuseStep 5401 = 4051) R4051
theorem R5405 : ∃ j : ℕ, syracuseStep^[j] 5405 = 1 := reachStep (stepEq 3 (by rfl) ⟨1013, by rfl⟩ : syracuseStep 5405 = 2027) R2027
theorem R5425 : ∃ j : ℕ, syracuseStep^[j] 5425 = 1 := reachStep (stepEq 2 (by rfl) ⟨2034, by rfl⟩ : syracuseStep 5425 = 4069) R4069
theorem R5427 : ∃ j : ℕ, syracuseStep^[j] 5427 = 1 := reachStep (stepEq 1 (by rfl) ⟨4070, by rfl⟩ : syracuseStep 5427 = 8141) R8141
theorem R5433 : ∃ j : ℕ, syracuseStep^[j] 5433 = 1 := reachStep (stepEq 2 (by rfl) ⟨2037, by rfl⟩ : syracuseStep 5433 = 4075) R4075
theorem R5449 : ∃ j : ℕ, syracuseStep^[j] 5449 = 1 := reachStep (stepEq 2 (by rfl) ⟨2043, by rfl⟩ : syracuseStep 5449 = 4087) R4087
theorem R5459 : ∃ j : ℕ, syracuseStep^[j] 5459 = 1 := reachStep (stepEq 1 (by rfl) ⟨4094, by rfl⟩ : syracuseStep 5459 = 8189) R8189
theorem R5465 : ∃ j : ℕ, syracuseStep^[j] 5465 = 1 := reachStep (stepEq 2 (by rfl) ⟨2049, by rfl⟩ : syracuseStep 5465 = 4099) R4099
theorem R5471 : ∃ j : ℕ, syracuseStep^[j] 5471 = 1 := reachStep (stepEq 1 (by rfl) ⟨4103, by rfl⟩ : syracuseStep 5471 = 8207) R8207
theorem R5473 : ∃ j : ℕ, syracuseStep^[j] 5473 = 1 := reachStep (stepEq 2 (by rfl) ⟨2052, by rfl⟩ : syracuseStep 5473 = 4105) R4105
theorem R5509 : ∃ j : ℕ, syracuseStep^[j] 5509 = 1 := reachStep (stepEq 4 (by rfl) ⟨516, by rfl⟩ : syracuseStep 5509 = 1033) R1033
theorem R5515 : ∃ j : ℕ, syracuseStep^[j] 5515 = 1 := reachStep (stepEq 1 (by rfl) ⟨4136, by rfl⟩ : syracuseStep 5515 = 8273) R8273
theorem R5519 : ∃ j : ℕ, syracuseStep^[j] 5519 = 1 := reachStep (stepEq 1 (by rfl) ⟨4139, by rfl⟩ : syracuseStep 5519 = 8279) R8279
theorem R5559 : ∃ j : ℕ, syracuseStep^[j] 5559 = 1 := reachStep (stepEq 1 (by rfl) ⟨4169, by rfl⟩ : syracuseStep 5559 = 8339) R8339
theorem R5611 : ∃ j : ℕ, syracuseStep^[j] 5611 = 1 := reachStep (stepEq 1 (by rfl) ⟨4208, by rfl⟩ : syracuseStep 5611 = 8417) R8417
theorem R5619 : ∃ j : ℕ, syracuseStep^[j] 5619 = 1 := reachStep (stepEq 1 (by rfl) ⟨4214, by rfl⟩ : syracuseStep 5619 = 8429) R8429
theorem R5625 : ∃ j : ℕ, syracuseStep^[j] 5625 = 1 := reachStep (stepEq 2 (by rfl) ⟨2109, by rfl⟩ : syracuseStep 5625 = 4219) R4219
theorem R5631 : ∃ j : ℕ, syracuseStep^[j] 5631 = 1 := reachStep (stepEq 1 (by rfl) ⟨4223, by rfl⟩ : syracuseStep 5631 = 8447) R8447
theorem R5679 : ∃ j : ℕ, syracuseStep^[j] 5679 = 1 := reachStep (stepEq 1 (by rfl) ⟨4259, by rfl⟩ : syracuseStep 5679 = 8519) R8519
theorem R41795 : ∃ j : ℕ, syracuseStep^[j] 41795 = 1 := reachStep (stepEq 1 (by rfl) ⟨31346, by rfl⟩ : syracuseStep 41795 = 62693) R62693
theorem R43253 : ∃ j : ℕ, syracuseStep^[j] 43253 = 1 := reachStep (stepEq 5 (by rfl) ⟨2027, by rfl⟩ : syracuseStep 43253 = 4055) R4055
theorem R10691 : ∃ j : ℕ, syracuseStep^[j] 10691 = 1 := reachStep (stepEq 1 (by rfl) ⟨8018, by rfl⟩ : syracuseStep 10691 = 16037) R16037
theorem R10799 : ∃ j : ℕ, syracuseStep^[j] 10799 = 1 := reachStep (stepEq 1 (by rfl) ⟨8099, by rfl⟩ : syracuseStep 10799 = 16199) R16199
theorem R10813 : ∃ j : ℕ, syracuseStep^[j] 10813 = 1 := reachStep (stepEq 3 (by rfl) ⟨2027, by rfl⟩ : syracuseStep 10813 = 4055) R4055
theorem R10853 : ∃ j : ℕ, syracuseStep^[j] 10853 = 1 := reachStep (stepEq 4 (by rfl) ⟨1017, by rfl⟩ : syracuseStep 10853 = 2035) R2035
theorem R10867 : ∃ j : ℕ, syracuseStep^[j] 10867 = 1 := reachStep (stepEq 1 (by rfl) ⟨8150, by rfl⟩ : syracuseStep 10867 = 16301) R16301
theorem R10889 : ∃ j : ℕ, syracuseStep^[j] 10889 = 1 := reachStep (stepEq 2 (by rfl) ⟨4083, by rfl⟩ : syracuseStep 10889 = 8167) R8167
theorem R10907 : ∃ j : ℕ, syracuseStep^[j] 10907 = 1 := reachStep (stepEq 1 (by rfl) ⟨8180, by rfl⟩ : syracuseStep 10907 = 16361) R16361
theorem R43685 : ∃ j : ℕ, syracuseStep^[j] 43685 = 1 := reachStep (stepEq 4 (by rfl) ⟨4095, by rfl⟩ : syracuseStep 43685 = 8191) R8191
theorem R10921 : ∃ j : ℕ, syracuseStep^[j] 10921 = 1 := reachStep (stepEq 2 (by rfl) ⟨4095, by rfl⟩ : syracuseStep 10921 = 8191) R8191
theorem R10955 : ∃ j : ℕ, syracuseStep^[j] 10955 = 1 := reachStep (stepEq 1 (by rfl) ⟨8216, by rfl⟩ : syracuseStep 10955 = 16433) R16433
theorem R11117 : ∃ j : ℕ, syracuseStep^[j] 11117 = 1 := reachStep (stepEq 3 (by rfl) ⟨2084, by rfl⟩ : syracuseStep 11117 = 4169) R4169
theorem R11177 : ∃ j : ℕ, syracuseStep^[j] 11177 = 1 := reachStep (stepEq 2 (by rfl) ⟨4191, by rfl⟩ : syracuseStep 11177 = 8383) R8383
theorem R11623 : ∃ j : ℕ, syracuseStep^[j] 11623 = 1 := reachStep (stepEq 1 (by rfl) ⟨8717, by rfl⟩ : syracuseStep 11623 = 17435) R17435
theorem R20897 : ∃ j : ℕ, syracuseStep^[j] 20897 = 1 := reachStep (stepEq 2 (by rfl) ⟨7836, by rfl⟩ : syracuseStep 20897 = 15673) R15673
theorem R86933 : ∃ j : ℕ, syracuseStep^[j] 86933 = 1 := reachStep (stepEq 6 (by rfl) ⟨2037, by rfl⟩ : syracuseStep 86933 = 4075) R4075
theorem R21599 : ∃ j : ℕ, syracuseStep^[j] 21599 = 1 := reachStep (stepEq 1 (by rfl) ⟨16199, by rfl⟩ : syracuseStep 21599 = 32399) R32399
theorem R21703 : ∃ j : ℕ, syracuseStep^[j] 21703 = 1 := reachStep (stepEq 1 (by rfl) ⟨16277, by rfl⟩ : syracuseStep 21703 = 32555) R32555
theorem R21779 : ∃ j : ℕ, syracuseStep^[j] 21779 = 1 := reachStep (stepEq 1 (by rfl) ⟨16334, by rfl⟩ : syracuseStep 21779 = 32669) R32669
theorem R21815 : ∃ j : ℕ, syracuseStep^[j] 21815 = 1 := reachStep (stepEq 1 (by rfl) ⟨16361, by rfl⟩ : syracuseStep 21815 = 32723) R32723
theorem R22355 : ∃ j : ℕ, syracuseStep^[j] 22355 = 1 := reachStep (stepEq 1 (by rfl) ⟨16766, by rfl⟩ : syracuseStep 22355 = 33533) R33533
theorem R22463 : ∃ j : ℕ, syracuseStep^[j] 22463 = 1 := reachStep (stepEq 1 (by rfl) ⟨16847, by rfl⟩ : syracuseStep 22463 = 33695) R33695
theorem R22477 : ∃ j : ℕ, syracuseStep^[j] 22477 = 1 := reachStep (stepEq 3 (by rfl) ⟨4214, by rfl⟩ : syracuseStep 22477 = 8429) R8429
theorem R88883 : ∃ j : ℕ, syracuseStep^[j] 88883 = 1 := reachStep (stepEq 1 (by rfl) ⟨66662, by rfl⟩ : syracuseStep 88883 = 133325) R133325
theorem R89909 : ∃ j : ℕ, syracuseStep^[j] 89909 = 1 := reachStep (stepEq 5 (by rfl) ⟨4214, by rfl⟩ : syracuseStep 89909 = 8429) R8429
theorem R1801 : ∃ j : ℕ, syracuseStep^[j] 1801 = 1 := reachStep (stepEq 2 (by rfl) ⟨675, by rfl⟩ : syracuseStep 1801 = 1351) R1351
theorem R1819 : ∃ j : ℕ, syracuseStep^[j] 1819 = 1 := reachStep (stepEq 1 (by rfl) ⟨1364, by rfl⟩ : syracuseStep 1819 = 2729) R2729
theorem R1823 : ∃ j : ℕ, syracuseStep^[j] 1823 = 1 := reachStep (stepEq 1 (by rfl) ⟨1367, by rfl⟩ : syracuseStep 1823 = 2735) R2735
theorem R1839 : ∃ j : ℕ, syracuseStep^[j] 1839 = 1 := reachStep (stepEq 1 (by rfl) ⟨1379, by rfl⟩ : syracuseStep 1839 = 2759) R2759
theorem R231821 : ∃ j : ℕ, syracuseStep^[j] 231821 = 1 := reachStep (stepEq 3 (by rfl) ⟨43466, by rfl⟩ : syracuseStep 231821 = 86933) R86933
theorem R3563 : ∃ j : ℕ, syracuseStep^[j] 3563 = 1 := reachStep (stepEq 1 (by rfl) ⟨2672, by rfl⟩ : syracuseStep 3563 = 5345) R5345
theorem R3603 : ∃ j : ℕ, syracuseStep^[j] 3603 = 1 := reachStep (stepEq 1 (by rfl) ⟨2702, by rfl⟩ : syracuseStep 3603 = 5405) R5405
theorem R3617 : ∃ j : ℕ, syracuseStep^[j] 3617 = 1 := reachStep (stepEq 2 (by rfl) ⟨1356, by rfl⟩ : syracuseStep 3617 = 2713) R2713
theorem R3639 : ∃ j : ℕ, syracuseStep^[j] 3639 = 1 := reachStep (stepEq 1 (by rfl) ⟨2729, by rfl⟩ : syracuseStep 3639 = 5459) R5459
theorem R3643 : ∃ j : ℕ, syracuseStep^[j] 3643 = 1 := reachStep (stepEq 1 (by rfl) ⟨2732, by rfl⟩ : syracuseStep 3643 = 5465) R5465
theorem R3647 : ∃ j : ℕ, syracuseStep^[j] 3647 = 1 := reachStep (stepEq 1 (by rfl) ⟨2735, by rfl⟩ : syracuseStep 3647 = 5471) R5471
theorem R3673 : ∃ j : ℕ, syracuseStep^[j] 3673 = 1 := reachStep (stepEq 2 (by rfl) ⟨1377, by rfl⟩ : syracuseStep 3673 = 2755) R2755
theorem R3679 : ∃ j : ℕ, syracuseStep^[j] 3679 = 1 := reachStep (stepEq 1 (by rfl) ⟨2759, by rfl⟩ : syracuseStep 3679 = 5519) R5519
theorem R3705 : ∃ j : ℕ, syracuseStep^[j] 3705 = 1 := reachStep (stepEq 2 (by rfl) ⟨1389, by rfl⟩ : syracuseStep 3705 = 2779) R2779
theorem R3745 : ∃ j : ℕ, syracuseStep^[j] 3745 = 1 := reachStep (stepEq 2 (by rfl) ⟨1404, by rfl⟩ : syracuseStep 3745 = 2809) R2809
theorem R3753 : ∃ j : ℕ, syracuseStep^[j] 3753 = 1 := reachStep (stepEq 2 (by rfl) ⟨1407, by rfl⟩ : syracuseStep 3753 = 2815) R2815
theorem R7127 : ∃ j : ℕ, syracuseStep^[j] 7127 = 1 := reachStep (stepEq 1 (by rfl) ⟨5345, by rfl⟩ : syracuseStep 7127 = 10691) R10691
theorem R7193 : ∃ j : ℕ, syracuseStep^[j] 7193 = 1 := reachStep (stepEq 2 (by rfl) ⟨2697, by rfl⟩ : syracuseStep 7193 = 5395) R5395
theorem R7199 : ∃ j : ℕ, syracuseStep^[j] 7199 = 1 := reachStep (stepEq 1 (by rfl) ⟨5399, by rfl⟩ : syracuseStep 7199 = 10799) R10799
theorem R7205 : ∃ j : ℕ, syracuseStep^[j] 7205 = 1 := reachStep (stepEq 4 (by rfl) ⟨675, by rfl⟩ : syracuseStep 7205 = 1351) R1351
theorem R7235 : ∃ j : ℕ, syracuseStep^[j] 7235 = 1 := reachStep (stepEq 1 (by rfl) ⟨5426, by rfl⟩ : syracuseStep 7235 = 10853) R10853
theorem R7259 : ∃ j : ℕ, syracuseStep^[j] 7259 = 1 := reachStep (stepEq 1 (by rfl) ⟨5444, by rfl⟩ : syracuseStep 7259 = 10889) R10889
theorem R7265 : ∃ j : ℕ, syracuseStep^[j] 7265 = 1 := reachStep (stepEq 2 (by rfl) ⟨2724, by rfl⟩ : syracuseStep 7265 = 5449) R5449
theorem R7271 : ∃ j : ℕ, syracuseStep^[j] 7271 = 1 := reachStep (stepEq 1 (by rfl) ⟨5453, by rfl⟩ : syracuseStep 7271 = 10907) R10907
theorem R7277 : ∃ j : ℕ, syracuseStep^[j] 7277 = 1 := reachStep (stepEq 3 (by rfl) ⟨1364, by rfl⟩ : syracuseStep 7277 = 2729) R2729
theorem R7303 : ∃ j : ℕ, syracuseStep^[j] 7303 = 1 := reachStep (stepEq 1 (by rfl) ⟨5477, by rfl⟩ : syracuseStep 7303 = 10955) R10955
theorem R7357 : ∃ j : ℕ, syracuseStep^[j] 7357 = 1 := reachStep (stepEq 3 (by rfl) ⟨1379, by rfl⟩ : syracuseStep 7357 = 2759) R2759
theorem R7411 : ∃ j : ℕ, syracuseStep^[j] 7411 = 1 := reachStep (stepEq 1 (by rfl) ⟨5558, by rfl⟩ : syracuseStep 7411 = 11117) R11117
theorem R7451 : ∃ j : ℕ, syracuseStep^[j] 7451 = 1 := reachStep (stepEq 1 (by rfl) ⟨5588, by rfl⟩ : syracuseStep 7451 = 11177) R11177
theorem R7481 : ∃ j : ℕ, syracuseStep^[j] 7481 = 1 := reachStep (stepEq 2 (by rfl) ⟨2805, by rfl⟩ : syracuseStep 7481 = 5611) R5611
theorem R13931 : ∃ j : ℕ, syracuseStep^[j] 13931 = 1 := reachStep (stepEq 1 (by rfl) ⟨10448, by rfl⟩ : syracuseStep 13931 = 20897) R20897
theorem R14399 : ∃ j : ℕ, syracuseStep^[j] 14399 = 1 := reachStep (stepEq 1 (by rfl) ⟨10799, by rfl⟩ : syracuseStep 14399 = 21599) R21599
theorem R14417 : ∃ j : ℕ, syracuseStep^[j] 14417 = 1 := reachStep (stepEq 2 (by rfl) ⟨5406, by rfl⟩ : syracuseStep 14417 = 10813) R10813
theorem R14489 : ∃ j : ℕ, syracuseStep^[j] 14489 = 1 := reachStep (stepEq 2 (by rfl) ⟨5433, by rfl⟩ : syracuseStep 14489 = 10867) R10867
theorem R14519 : ∃ j : ℕ, syracuseStep^[j] 14519 = 1 := reachStep (stepEq 1 (by rfl) ⟨10889, by rfl⟩ : syracuseStep 14519 = 21779) R21779
theorem R14543 : ∃ j : ℕ, syracuseStep^[j] 14543 = 1 := reachStep (stepEq 1 (by rfl) ⟨10907, by rfl⟩ : syracuseStep 14543 = 21815) R21815
theorem R14561 : ∃ j : ℕ, syracuseStep^[j] 14561 = 1 := reachStep (stepEq 2 (by rfl) ⟨5460, by rfl⟩ : syracuseStep 14561 = 10921) R10921
theorem R14717 : ∃ j : ℕ, syracuseStep^[j] 14717 = 1 := reachStep (stepEq 3 (by rfl) ⟨2759, by rfl⟩ : syracuseStep 14717 = 5519) R5519
theorem R14903 : ∃ j : ℕ, syracuseStep^[j] 14903 = 1 := reachStep (stepEq 1 (by rfl) ⟨11177, by rfl⟩ : syracuseStep 14903 = 22355) R22355
theorem R14975 : ∃ j : ℕ, syracuseStep^[j] 14975 = 1 := reachStep (stepEq 1 (by rfl) ⟨11231, by rfl⟩ : syracuseStep 14975 = 22463) R22463
theorem R15013 : ∃ j : ℕ, syracuseStep^[j] 15013 = 1 := reachStep (stepEq 4 (by rfl) ⟨1407, by rfl⟩ : syracuseStep 15013 = 2815) R2815
theorem R15497 : ∃ j : ℕ, syracuseStep^[j] 15497 = 1 := reachStep (stepEq 2 (by rfl) ⟨5811, by rfl⟩ : syracuseStep 15497 = 11623) R11623
theorem R58229 : ∃ j : ℕ, syracuseStep^[j] 58229 = 1 := reachStep (stepEq 5 (by rfl) ⟨2729, by rfl⟩ : syracuseStep 58229 = 5459) R5459
theorem R59255 : ∃ j : ℕ, syracuseStep^[j] 59255 = 1 := reachStep (stepEq 1 (by rfl) ⟨44441, by rfl⟩ : syracuseStep 59255 = 88883) R88883
theorem R59939 : ∃ j : ℕ, syracuseStep^[j] 59939 = 1 := reachStep (stepEq 1 (by rfl) ⟨44954, by rfl⟩ : syracuseStep 59939 = 89909) R89909
theorem R27863 : ∃ j : ℕ, syracuseStep^[j] 27863 = 1 := reachStep (stepEq 1 (by rfl) ⟨20897, by rfl⟩ : syracuseStep 27863 = 41795) R41795
theorem R28835 : ∃ j : ℕ, syracuseStep^[j] 28835 = 1 := reachStep (stepEq 1 (by rfl) ⟨21626, by rfl⟩ : syracuseStep 28835 = 43253) R43253
theorem R28937 : ∃ j : ℕ, syracuseStep^[j] 28937 = 1 := reachStep (stepEq 2 (by rfl) ⟨10851, by rfl⟩ : syracuseStep 28937 = 21703) R21703
theorem R29123 : ∃ j : ℕ, syracuseStep^[j] 29123 = 1 := reachStep (stepEq 1 (by rfl) ⟨21842, by rfl⟩ : syracuseStep 29123 = 43685) R43685
theorem R29645 : ∃ j : ℕ, syracuseStep^[j] 29645 = 1 := reachStep (stepEq 3 (by rfl) ⟨5558, by rfl⟩ : syracuseStep 29645 = 11117) R11117
theorem R29969 : ∃ j : ℕ, syracuseStep^[j] 29969 = 1 := reachStep (stepEq 2 (by rfl) ⟨11238, by rfl⟩ : syracuseStep 29969 = 22477) R22477
theorem R1215 : ∃ j : ℕ, syracuseStep^[j] 1215 = 1 := reachStep (stepEq 1 (by rfl) ⟨911, by rfl⟩ : syracuseStep 1215 = 1823) R1823
theorem R2375 : ∃ j : ℕ, syracuseStep^[j] 2375 = 1 := reachStep (stepEq 1 (by rfl) ⟨1781, by rfl⟩ : syracuseStep 2375 = 3563) R3563
theorem R2401 : ∃ j : ℕ, syracuseStep^[j] 2401 = 1 := reachStep (stepEq 2 (by rfl) ⟨900, by rfl⟩ : syracuseStep 2401 = 1801) R1801
theorem R2411 : ∃ j : ℕ, syracuseStep^[j] 2411 = 1 := reachStep (stepEq 1 (by rfl) ⟨1808, by rfl⟩ : syracuseStep 2411 = 3617) R3617
theorem R2425 : ∃ j : ℕ, syracuseStep^[j] 2425 = 1 := reachStep (stepEq 2 (by rfl) ⟨909, by rfl⟩ : syracuseStep 2425 = 1819) R1819
theorem R2431 : ∃ j : ℕ, syracuseStep^[j] 2431 = 1 := reachStep (stepEq 1 (by rfl) ⟨1823, by rfl⟩ : syracuseStep 2431 = 3647) R3647
theorem R4751 : ∃ j : ℕ, syracuseStep^[j] 4751 = 1 := reachStep (stepEq 1 (by rfl) ⟨3563, by rfl⟩ : syracuseStep 4751 = 7127) R7127
theorem R4795 : ∃ j : ℕ, syracuseStep^[j] 4795 = 1 := reachStep (stepEq 1 (by rfl) ⟨3596, by rfl⟩ : syracuseStep 4795 = 7193) R7193
theorem R4799 : ∃ j : ℕ, syracuseStep^[j] 4799 = 1 := reachStep (stepEq 1 (by rfl) ⟨3599, by rfl⟩ : syracuseStep 4799 = 7199) R7199
theorem R4803 : ∃ j : ℕ, syracuseStep^[j] 4803 = 1 := reachStep (stepEq 1 (by rfl) ⟨3602, by rfl⟩ : syracuseStep 4803 = 7205) R7205
theorem R4823 : ∃ j : ℕ, syracuseStep^[j] 4823 = 1 := reachStep (stepEq 1 (by rfl) ⟨3617, by rfl⟩ : syracuseStep 4823 = 7235) R7235
theorem R4839 : ∃ j : ℕ, syracuseStep^[j] 4839 = 1 := reachStep (stepEq 1 (by rfl) ⟨3629, by rfl⟩ : syracuseStep 4839 = 7259) R7259
theorem R4843 : ∃ j : ℕ, syracuseStep^[j] 4843 = 1 := reachStep (stepEq 1 (by rfl) ⟨3632, by rfl⟩ : syracuseStep 4843 = 7265) R7265
theorem R4847 : ∃ j : ℕ, syracuseStep^[j] 4847 = 1 := reachStep (stepEq 1 (by rfl) ⟨3635, by rfl⟩ : syracuseStep 4847 = 7271) R7271
theorem R4851 : ∃ j : ℕ, syracuseStep^[j] 4851 = 1 := reachStep (stepEq 1 (by rfl) ⟨3638, by rfl⟩ : syracuseStep 4851 = 7277) R7277
theorem R4857 : ∃ j : ℕ, syracuseStep^[j] 4857 = 1 := reachStep (stepEq 2 (by rfl) ⟨1821, by rfl⟩ : syracuseStep 4857 = 3643) R3643
theorem R4861 : ∃ j : ℕ, syracuseStep^[j] 4861 = 1 := reachStep (stepEq 3 (by rfl) ⟨911, by rfl⟩ : syracuseStep 4861 = 1823) R1823
theorem R4897 : ∃ j : ℕ, syracuseStep^[j] 4897 = 1 := reachStep (stepEq 2 (by rfl) ⟨1836, by rfl⟩ : syracuseStep 4897 = 3673) R3673
theorem R4905 : ∃ j : ℕ, syracuseStep^[j] 4905 = 1 := reachStep (stepEq 2 (by rfl) ⟨1839, by rfl⟩ : syracuseStep 4905 = 3679) R3679
theorem R4967 : ∃ j : ℕ, syracuseStep^[j] 4967 = 1 := reachStep (stepEq 1 (by rfl) ⟨3725, by rfl⟩ : syracuseStep 4967 = 7451) R7451
theorem R4987 : ∃ j : ℕ, syracuseStep^[j] 4987 = 1 := reachStep (stepEq 1 (by rfl) ⟨3740, by rfl⟩ : syracuseStep 4987 = 7481) R7481
theorem R4993 : ∃ j : ℕ, syracuseStep^[j] 4993 = 1 := reachStep (stepEq 2 (by rfl) ⟨1872, by rfl⟩ : syracuseStep 4993 = 3745) R3745
theorem R38819 : ∃ j : ℕ, syracuseStep^[j] 38819 = 1 := reachStep (stepEq 1 (by rfl) ⟨29114, by rfl⟩ : syracuseStep 38819 = 58229) R58229
theorem R39503 : ∃ j : ℕ, syracuseStep^[j] 39503 = 1 := reachStep (stepEq 1 (by rfl) ⟨29627, by rfl⟩ : syracuseStep 39503 = 59255) R59255
theorem R39959 : ∃ j : ℕ, syracuseStep^[j] 39959 = 1 := reachStep (stepEq 1 (by rfl) ⟨29969, by rfl⟩ : syracuseStep 39959 = 59939) R59939
theorem R9287 : ∃ j : ℕ, syracuseStep^[j] 9287 = 1 := reachStep (stepEq 1 (by rfl) ⟨6965, by rfl⟩ : syracuseStep 9287 = 13931) R13931
theorem R9599 : ∃ j : ℕ, syracuseStep^[j] 9599 = 1 := reachStep (stepEq 1 (by rfl) ⟨7199, by rfl⟩ : syracuseStep 9599 = 14399) R14399
theorem R9605 : ∃ j : ℕ, syracuseStep^[j] 9605 = 1 := reachStep (stepEq 4 (by rfl) ⟨900, by rfl⟩ : syracuseStep 9605 = 1801) R1801
theorem R9611 : ∃ j : ℕ, syracuseStep^[j] 9611 = 1 := reachStep (stepEq 1 (by rfl) ⟨7208, by rfl⟩ : syracuseStep 9611 = 14417) R14417
theorem R9659 : ∃ j : ℕ, syracuseStep^[j] 9659 = 1 := reachStep (stepEq 1 (by rfl) ⟨7244, by rfl⟩ : syracuseStep 9659 = 14489) R14489
theorem R9679 : ∃ j : ℕ, syracuseStep^[j] 9679 = 1 := reachStep (stepEq 1 (by rfl) ⟨7259, by rfl⟩ : syracuseStep 9679 = 14519) R14519
theorem R9695 : ∃ j : ℕ, syracuseStep^[j] 9695 = 1 := reachStep (stepEq 1 (by rfl) ⟨7271, by rfl⟩ : syracuseStep 9695 = 14543) R14543
theorem R9701 : ∃ j : ℕ, syracuseStep^[j] 9701 = 1 := reachStep (stepEq 4 (by rfl) ⟨909, by rfl⟩ : syracuseStep 9701 = 1819) R1819
theorem R9707 : ∃ j : ℕ, syracuseStep^[j] 9707 = 1 := reachStep (stepEq 1 (by rfl) ⟨7280, by rfl⟩ : syracuseStep 9707 = 14561) R14561
theorem R9725 : ∃ j : ℕ, syracuseStep^[j] 9725 = 1 := reachStep (stepEq 3 (by rfl) ⟨1823, by rfl⟩ : syracuseStep 9725 = 3647) R3647
theorem R9737 : ∃ j : ℕ, syracuseStep^[j] 9737 = 1 := reachStep (stepEq 2 (by rfl) ⟨3651, by rfl⟩ : syracuseStep 9737 = 7303) R7303
theorem R9809 : ∃ j : ℕ, syracuseStep^[j] 9809 = 1 := reachStep (stepEq 2 (by rfl) ⟨3678, by rfl⟩ : syracuseStep 9809 = 7357) R7357
theorem R9811 : ∃ j : ℕ, syracuseStep^[j] 9811 = 1 := reachStep (stepEq 1 (by rfl) ⟨7358, by rfl⟩ : syracuseStep 9811 = 14717) R14717
theorem R9881 : ∃ j : ℕ, syracuseStep^[j] 9881 = 1 := reachStep (stepEq 2 (by rfl) ⟨3705, by rfl⟩ : syracuseStep 9881 = 7411) R7411
theorem R9935 : ∃ j : ℕ, syracuseStep^[j] 9935 = 1 := reachStep (stepEq 1 (by rfl) ⟨7451, by rfl⟩ : syracuseStep 9935 = 14903) R14903
theorem R9983 : ∃ j : ℕ, syracuseStep^[j] 9983 = 1 := reachStep (stepEq 1 (by rfl) ⟨7487, by rfl⟩ : syracuseStep 9983 = 14975) R14975
theorem R10331 : ∃ j : ℕ, syracuseStep^[j] 10331 = 1 := reachStep (stepEq 1 (by rfl) ⟨7748, by rfl⟩ : syracuseStep 10331 = 15497) R15497
theorem R18575 : ∃ j : ℕ, syracuseStep^[j] 18575 = 1 := reachStep (stepEq 1 (by rfl) ⟨13931, by rfl⟩ : syracuseStep 18575 = 27863) R27863
theorem R19223 : ∃ j : ℕ, syracuseStep^[j] 19223 = 1 := reachStep (stepEq 1 (by rfl) ⟨14417, by rfl⟩ : syracuseStep 19223 = 28835) R28835
theorem R19291 : ∃ j : ℕ, syracuseStep^[j] 19291 = 1 := reachStep (stepEq 1 (by rfl) ⟨14468, by rfl⟩ : syracuseStep 19291 = 28937) R28937
theorem R19415 : ∃ j : ℕ, syracuseStep^[j] 19415 = 1 := reachStep (stepEq 1 (by rfl) ⟨14561, by rfl⟩ : syracuseStep 19415 = 29123) R29123
theorem R19763 : ∃ j : ℕ, syracuseStep^[j] 19763 = 1 := reachStep (stepEq 1 (by rfl) ⟨14822, by rfl⟩ : syracuseStep 19763 = 29645) R29645
theorem R19979 : ∃ j : ℕ, syracuseStep^[j] 19979 = 1 := reachStep (stepEq 1 (by rfl) ⟨14984, by rfl⟩ : syracuseStep 19979 = 29969) R29969
theorem R20017 : ∃ j : ℕ, syracuseStep^[j] 20017 = 1 := reachStep (stepEq 2 (by rfl) ⟨7506, by rfl⟩ : syracuseStep 20017 = 15013) R15013
theorem R154547 : ∃ j : ℕ, syracuseStep^[j] 154547 = 1 := reachStep (stepEq 1 (by rfl) ⟨115910, by rfl⟩ : syracuseStep 154547 = 231821) R231821
theorem R1583 : ∃ j : ℕ, syracuseStep^[j] 1583 = 1 := reachStep (stepEq 1 (by rfl) ⟨1187, by rfl⟩ : syracuseStep 1583 = 2375) R2375
theorem R1607 : ∃ j : ℕ, syracuseStep^[j] 1607 = 1 := reachStep (stepEq 1 (by rfl) ⟨1205, by rfl⟩ : syracuseStep 1607 = 2411) R2411
theorem R3167 : ∃ j : ℕ, syracuseStep^[j] 3167 = 1 := reachStep (stepEq 1 (by rfl) ⟨2375, by rfl⟩ : syracuseStep 3167 = 4751) R4751
theorem R3199 : ∃ j : ℕ, syracuseStep^[j] 3199 = 1 := reachStep (stepEq 1 (by rfl) ⟨2399, by rfl⟩ : syracuseStep 3199 = 4799) R4799
theorem R3201 : ∃ j : ℕ, syracuseStep^[j] 3201 = 1 := reachStep (stepEq 2 (by rfl) ⟨1200, by rfl⟩ : syracuseStep 3201 = 2401) R2401
theorem R3215 : ∃ j : ℕ, syracuseStep^[j] 3215 = 1 := reachStep (stepEq 1 (by rfl) ⟨2411, by rfl⟩ : syracuseStep 3215 = 4823) R4823
theorem R3231 : ∃ j : ℕ, syracuseStep^[j] 3231 = 1 := reachStep (stepEq 1 (by rfl) ⟨2423, by rfl⟩ : syracuseStep 3231 = 4847) R4847
theorem R3233 : ∃ j : ℕ, syracuseStep^[j] 3233 = 1 := reachStep (stepEq 2 (by rfl) ⟨1212, by rfl⟩ : syracuseStep 3233 = 2425) R2425
theorem R3241 : ∃ j : ℕ, syracuseStep^[j] 3241 = 1 := reachStep (stepEq 2 (by rfl) ⟨1215, by rfl⟩ : syracuseStep 3241 = 2431) R2431
theorem R3311 : ∃ j : ℕ, syracuseStep^[j] 3311 = 1 := reachStep (stepEq 1 (by rfl) ⟨2483, by rfl⟩ : syracuseStep 3311 = 4967) R4967
theorem R103031 : ∃ j : ℕ, syracuseStep^[j] 103031 = 1 := reachStep (stepEq 1 (by rfl) ⟨77273, by rfl⟩ : syracuseStep 103031 = 154547) R154547
theorem R6191 : ∃ j : ℕ, syracuseStep^[j] 6191 = 1 := reachStep (stepEq 1 (by rfl) ⟨4643, by rfl⟩ : syracuseStep 6191 = 9287) R9287
theorem R6333 : ∃ j : ℕ, syracuseStep^[j] 6333 = 1 := reachStep (stepEq 3 (by rfl) ⟨1187, by rfl⟩ : syracuseStep 6333 = 2375) R2375
theorem R6393 : ∃ j : ℕ, syracuseStep^[j] 6393 = 1 := reachStep (stepEq 2 (by rfl) ⟨2397, by rfl⟩ : syracuseStep 6393 = 4795) R4795
theorem R6399 : ∃ j : ℕ, syracuseStep^[j] 6399 = 1 := reachStep (stepEq 1 (by rfl) ⟨4799, by rfl⟩ : syracuseStep 6399 = 9599) R9599
theorem R6403 : ∃ j : ℕ, syracuseStep^[j] 6403 = 1 := reachStep (stepEq 1 (by rfl) ⟨4802, by rfl⟩ : syracuseStep 6403 = 9605) R9605
theorem R6407 : ∃ j : ℕ, syracuseStep^[j] 6407 = 1 := reachStep (stepEq 1 (by rfl) ⟨4805, by rfl⟩ : syracuseStep 6407 = 9611) R9611
theorem R6429 : ∃ j : ℕ, syracuseStep^[j] 6429 = 1 := reachStep (stepEq 3 (by rfl) ⟨1205, by rfl⟩ : syracuseStep 6429 = 2411) R2411
theorem R6439 : ∃ j : ℕ, syracuseStep^[j] 6439 = 1 := reachStep (stepEq 1 (by rfl) ⟨4829, by rfl⟩ : syracuseStep 6439 = 9659) R9659
theorem R6457 : ∃ j : ℕ, syracuseStep^[j] 6457 = 1 := reachStep (stepEq 2 (by rfl) ⟨2421, by rfl⟩ : syracuseStep 6457 = 4843) R4843
theorem R6463 : ∃ j : ℕ, syracuseStep^[j] 6463 = 1 := reachStep (stepEq 1 (by rfl) ⟨4847, by rfl⟩ : syracuseStep 6463 = 9695) R9695
theorem R6467 : ∃ j : ℕ, syracuseStep^[j] 6467 = 1 := reachStep (stepEq 1 (by rfl) ⟨4850, by rfl⟩ : syracuseStep 6467 = 9701) R9701
theorem R6471 : ∃ j : ℕ, syracuseStep^[j] 6471 = 1 := reachStep (stepEq 1 (by rfl) ⟨4853, by rfl⟩ : syracuseStep 6471 = 9707) R9707
theorem R6481 : ∃ j : ℕ, syracuseStep^[j] 6481 = 1 := reachStep (stepEq 2 (by rfl) ⟨2430, by rfl⟩ : syracuseStep 6481 = 4861) R4861
theorem R6483 : ∃ j : ℕ, syracuseStep^[j] 6483 = 1 := reachStep (stepEq 1 (by rfl) ⟨4862, by rfl⟩ : syracuseStep 6483 = 9725) R9725
theorem R6491 : ∃ j : ℕ, syracuseStep^[j] 6491 = 1 := reachStep (stepEq 1 (by rfl) ⟨4868, by rfl⟩ : syracuseStep 6491 = 9737) R9737
theorem R6529 : ∃ j : ℕ, syracuseStep^[j] 6529 = 1 := reachStep (stepEq 2 (by rfl) ⟨2448, by rfl⟩ : syracuseStep 6529 = 4897) R4897
theorem R6539 : ∃ j : ℕ, syracuseStep^[j] 6539 = 1 := reachStep (stepEq 1 (by rfl) ⟨4904, by rfl⟩ : syracuseStep 6539 = 9809) R9809
theorem R6587 : ∃ j : ℕ, syracuseStep^[j] 6587 = 1 := reachStep (stepEq 1 (by rfl) ⟨4940, by rfl⟩ : syracuseStep 6587 = 9881) R9881
theorem R6623 : ∃ j : ℕ, syracuseStep^[j] 6623 = 1 := reachStep (stepEq 1 (by rfl) ⟨4967, by rfl⟩ : syracuseStep 6623 = 9935) R9935
theorem R6649 : ∃ j : ℕ, syracuseStep^[j] 6649 = 1 := reachStep (stepEq 2 (by rfl) ⟨2493, by rfl⟩ : syracuseStep 6649 = 4987) R4987
theorem R6655 : ∃ j : ℕ, syracuseStep^[j] 6655 = 1 := reachStep (stepEq 1 (by rfl) ⟨4991, by rfl⟩ : syracuseStep 6655 = 9983) R9983
theorem R6657 : ∃ j : ℕ, syracuseStep^[j] 6657 = 1 := reachStep (stepEq 2 (by rfl) ⟨2496, by rfl⟩ : syracuseStep 6657 = 4993) R4993
theorem R6887 : ∃ j : ℕ, syracuseStep^[j] 6887 = 1 := reachStep (stepEq 1 (by rfl) ⟨5165, by rfl⟩ : syracuseStep 6887 = 10331) R10331
theorem R12383 : ∃ j : ℕ, syracuseStep^[j] 12383 = 1 := reachStep (stepEq 1 (by rfl) ⟨9287, by rfl⟩ : syracuseStep 12383 = 18575) R18575
theorem R12797 : ∃ j : ℕ, syracuseStep^[j] 12797 = 1 := reachStep (stepEq 3 (by rfl) ⟨2399, by rfl⟩ : syracuseStep 12797 = 4799) R4799
theorem R12815 : ∃ j : ℕ, syracuseStep^[j] 12815 = 1 := reachStep (stepEq 1 (by rfl) ⟨9611, by rfl⟩ : syracuseStep 12815 = 19223) R19223
theorem R12905 : ∃ j : ℕ, syracuseStep^[j] 12905 = 1 := reachStep (stepEq 2 (by rfl) ⟨4839, by rfl⟩ : syracuseStep 12905 = 9679) R9679
theorem R12943 : ∃ j : ℕ, syracuseStep^[j] 12943 = 1 := reachStep (stepEq 1 (by rfl) ⟨9707, by rfl⟩ : syracuseStep 12943 = 19415) R19415
theorem R13081 : ∃ j : ℕ, syracuseStep^[j] 13081 = 1 := reachStep (stepEq 2 (by rfl) ⟨4905, by rfl⟩ : syracuseStep 13081 = 9811) R9811
theorem R13175 : ∃ j : ℕ, syracuseStep^[j] 13175 = 1 := reachStep (stepEq 1 (by rfl) ⟨9881, by rfl⟩ : syracuseStep 13175 = 19763) R19763
theorem R13319 : ∃ j : ℕ, syracuseStep^[j] 13319 = 1 := reachStep (stepEq 1 (by rfl) ⟨9989, by rfl⟩ : syracuseStep 13319 = 19979) R19979
theorem R25721 : ∃ j : ℕ, syracuseStep^[j] 25721 = 1 := reachStep (stepEq 2 (by rfl) ⟨9645, by rfl⟩ : syracuseStep 25721 = 19291) R19291
theorem R25757 : ∃ j : ℕ, syracuseStep^[j] 25757 = 1 := reachStep (stepEq 3 (by rfl) ⟨4829, by rfl⟩ : syracuseStep 25757 = 9659) R9659
theorem R25879 : ∃ j : ℕ, syracuseStep^[j] 25879 = 1 := reachStep (stepEq 1 (by rfl) ⟨19409, by rfl⟩ : syracuseStep 25879 = 38819) R38819
theorem R26335 : ∃ j : ℕ, syracuseStep^[j] 26335 = 1 := reachStep (stepEq 1 (by rfl) ⟨19751, by rfl⟩ : syracuseStep 26335 = 39503) R39503
theorem R26639 : ∃ j : ℕ, syracuseStep^[j] 26639 = 1 := reachStep (stepEq 1 (by rfl) ⟨19979, by rfl⟩ : syracuseStep 26639 = 39959) R39959
theorem R26689 : ∃ j : ℕ, syracuseStep^[j] 26689 = 1 := reachStep (stepEq 2 (by rfl) ⟨10008, by rfl⟩ : syracuseStep 26689 = 20017) R20017
theorem R1055 : ∃ j : ℕ, syracuseStep^[j] 1055 = 1 := reachStep (stepEq 1 (by rfl) ⟨791, by rfl⟩ : syracuseStep 1055 = 1583) R1583
theorem R1071 : ∃ j : ℕ, syracuseStep^[j] 1071 = 1 := reachStep (stepEq 1 (by rfl) ⟨803, by rfl⟩ : syracuseStep 1071 = 1607) R1607
theorem R34505 : ∃ j : ℕ, syracuseStep^[j] 34505 = 1 := reachStep (stepEq 2 (by rfl) ⟨12939, by rfl⟩ : syracuseStep 34505 = 25879) R25879
theorem R2111 : ∃ j : ℕ, syracuseStep^[j] 2111 = 1 := reachStep (stepEq 1 (by rfl) ⟨1583, by rfl⟩ : syracuseStep 2111 = 3167) R3167
theorem R2143 : ∃ j : ℕ, syracuseStep^[j] 2143 = 1 := reachStep (stepEq 1 (by rfl) ⟨1607, by rfl⟩ : syracuseStep 2143 = 3215) R3215
theorem R2155 : ∃ j : ℕ, syracuseStep^[j] 2155 = 1 := reachStep (stepEq 1 (by rfl) ⟨1616, by rfl⟩ : syracuseStep 2155 = 3233) R3233
theorem R2207 : ∃ j : ℕ, syracuseStep^[j] 2207 = 1 := reachStep (stepEq 1 (by rfl) ⟨1655, by rfl⟩ : syracuseStep 2207 = 3311) R3311
theorem R35113 : ∃ j : ℕ, syracuseStep^[j] 35113 = 1 := reachStep (stepEq 2 (by rfl) ⟨13167, by rfl⟩ : syracuseStep 35113 = 26335) R26335
theorem R35585 : ∃ j : ℕ, syracuseStep^[j] 35585 = 1 := reachStep (stepEq 2 (by rfl) ⟨13344, by rfl⟩ : syracuseStep 35585 = 26689) R26689
theorem R68687 : ∃ j : ℕ, syracuseStep^[j] 68687 = 1 := reachStep (stepEq 1 (by rfl) ⟨51515, by rfl⟩ : syracuseStep 68687 = 103031) R103031
theorem R4127 : ∃ j : ℕ, syracuseStep^[j] 4127 = 1 := reachStep (stepEq 1 (by rfl) ⟨3095, by rfl⟩ : syracuseStep 4127 = 6191) R6191
theorem R4221 : ∃ j : ℕ, syracuseStep^[j] 4221 = 1 := reachStep (stepEq 3 (by rfl) ⟨791, by rfl⟩ : syracuseStep 4221 = 1583) R1583
theorem R4265 : ∃ j : ℕ, syracuseStep^[j] 4265 = 1 := reachStep (stepEq 2 (by rfl) ⟨1599, by rfl⟩ : syracuseStep 4265 = 3199) R3199
theorem R4271 : ∃ j : ℕ, syracuseStep^[j] 4271 = 1 := reachStep (stepEq 1 (by rfl) ⟨3203, by rfl⟩ : syracuseStep 4271 = 6407) R6407
theorem R4285 : ∃ j : ℕ, syracuseStep^[j] 4285 = 1 := reachStep (stepEq 3 (by rfl) ⟨803, by rfl⟩ : syracuseStep 4285 = 1607) R1607
theorem R4311 : ∃ j : ℕ, syracuseStep^[j] 4311 = 1 := reachStep (stepEq 1 (by rfl) ⟨3233, by rfl⟩ : syracuseStep 4311 = 6467) R6467
theorem R4321 : ∃ j : ℕ, syracuseStep^[j] 4321 = 1 := reachStep (stepEq 2 (by rfl) ⟨1620, by rfl⟩ : syracuseStep 4321 = 3241) R3241
theorem R4327 : ∃ j : ℕ, syracuseStep^[j] 4327 = 1 := reachStep (stepEq 1 (by rfl) ⟨3245, by rfl⟩ : syracuseStep 4327 = 6491) R6491
theorem R4359 : ∃ j : ℕ, syracuseStep^[j] 4359 = 1 := reachStep (stepEq 1 (by rfl) ⟨3269, by rfl⟩ : syracuseStep 4359 = 6539) R6539
theorem R4391 : ∃ j : ℕ, syracuseStep^[j] 4391 = 1 := reachStep (stepEq 1 (by rfl) ⟨3293, by rfl⟩ : syracuseStep 4391 = 6587) R6587
theorem R4415 : ∃ j : ℕ, syracuseStep^[j] 4415 = 1 := reachStep (stepEq 1 (by rfl) ⟨3311, by rfl⟩ : syracuseStep 4415 = 6623) R6623
theorem R4591 : ∃ j : ℕ, syracuseStep^[j] 4591 = 1 := reachStep (stepEq 1 (by rfl) ⟨3443, by rfl⟩ : syracuseStep 4591 = 6887) R6887
theorem R8255 : ∃ j : ℕ, syracuseStep^[j] 8255 = 1 := reachStep (stepEq 1 (by rfl) ⟨6191, by rfl⟩ : syracuseStep 8255 = 12383) R12383
theorem R8531 : ∃ j : ℕ, syracuseStep^[j] 8531 = 1 := reachStep (stepEq 1 (by rfl) ⟨6398, by rfl⟩ : syracuseStep 8531 = 12797) R12797
theorem R8537 : ∃ j : ℕ, syracuseStep^[j] 8537 = 1 := reachStep (stepEq 2 (by rfl) ⟨3201, by rfl⟩ : syracuseStep 8537 = 6403) R6403
theorem R8543 : ∃ j : ℕ, syracuseStep^[j] 8543 = 1 := reachStep (stepEq 1 (by rfl) ⟨6407, by rfl⟩ : syracuseStep 8543 = 12815) R12815
theorem R8573 : ∃ j : ℕ, syracuseStep^[j] 8573 = 1 := reachStep (stepEq 3 (by rfl) ⟨1607, by rfl⟩ : syracuseStep 8573 = 3215) R3215
theorem R8585 : ∃ j : ℕ, syracuseStep^[j] 8585 = 1 := reachStep (stepEq 2 (by rfl) ⟨3219, by rfl⟩ : syracuseStep 8585 = 6439) R6439
theorem R8603 : ∃ j : ℕ, syracuseStep^[j] 8603 = 1 := reachStep (stepEq 1 (by rfl) ⟨6452, by rfl⟩ : syracuseStep 8603 = 12905) R12905
theorem R8609 : ∃ j : ℕ, syracuseStep^[j] 8609 = 1 := reachStep (stepEq 2 (by rfl) ⟨3228, by rfl⟩ : syracuseStep 8609 = 6457) R6457
theorem R8621 : ∃ j : ℕ, syracuseStep^[j] 8621 = 1 := reachStep (stepEq 3 (by rfl) ⟨1616, by rfl⟩ : syracuseStep 8621 = 3233) R3233
theorem R8705 : ∃ j : ℕ, syracuseStep^[j] 8705 = 1 := reachStep (stepEq 2 (by rfl) ⟨3264, by rfl⟩ : syracuseStep 8705 = 6529) R6529
theorem R8783 : ∃ j : ℕ, syracuseStep^[j] 8783 = 1 := reachStep (stepEq 1 (by rfl) ⟨6587, by rfl⟩ : syracuseStep 8783 = 13175) R13175
theorem R8873 : ∃ j : ℕ, syracuseStep^[j] 8873 = 1 := reachStep (stepEq 2 (by rfl) ⟨3327, by rfl⟩ : syracuseStep 8873 = 6655) R6655
theorem R8879 : ∃ j : ℕ, syracuseStep^[j] 8879 = 1 := reachStep (stepEq 1 (by rfl) ⟨6659, by rfl⟩ : syracuseStep 8879 = 13319) R13319
theorem R17147 : ∃ j : ℕ, syracuseStep^[j] 17147 = 1 := reachStep (stepEq 1 (by rfl) ⟨12860, by rfl⟩ : syracuseStep 17147 = 25721) R25721
theorem R17171 : ∃ j : ℕ, syracuseStep^[j] 17171 = 1 := reachStep (stepEq 1 (by rfl) ⟨12878, by rfl⟩ : syracuseStep 17171 = 25757) R25757
theorem R17257 : ∃ j : ℕ, syracuseStep^[j] 17257 = 1 := reachStep (stepEq 2 (by rfl) ⟨6471, by rfl⟩ : syracuseStep 17257 = 12943) R12943
theorem R17441 : ∃ j : ℕ, syracuseStep^[j] 17441 = 1 := reachStep (stepEq 2 (by rfl) ⟨6540, by rfl⟩ : syracuseStep 17441 = 13081) R13081
theorem R17759 : ∃ j : ℕ, syracuseStep^[j] 17759 = 1 := reachStep (stepEq 1 (by rfl) ⟨13319, by rfl⟩ : syracuseStep 17759 = 26639) R26639
theorem R703 : ∃ j : ℕ, syracuseStep^[j] 703 = 1 := reachStep (stepEq 1 (by rfl) ⟨527, by rfl⟩ : syracuseStep 703 = 1055) R1055
theorem R1407 : ∃ j : ℕ, syracuseStep^[j] 1407 = 1 := reachStep (stepEq 1 (by rfl) ⟨1055, by rfl⟩ : syracuseStep 1407 = 2111) R2111
theorem R1471 : ∃ j : ℕ, syracuseStep^[j] 1471 = 1 := reachStep (stepEq 1 (by rfl) ⟨1103, by rfl⟩ : syracuseStep 1471 = 2207) R2207
theorem R2751 : ∃ j : ℕ, syracuseStep^[j] 2751 = 1 := reachStep (stepEq 1 (by rfl) ⟨2063, by rfl⟩ : syracuseStep 2751 = 4127) R4127
theorem R2813 : ∃ j : ℕ, syracuseStep^[j] 2813 = 1 := reachStep (stepEq 3 (by rfl) ⟨527, by rfl⟩ : syracuseStep 2813 = 1055) R1055
theorem R2843 : ∃ j : ℕ, syracuseStep^[j] 2843 = 1 := reachStep (stepEq 1 (by rfl) ⟨2132, by rfl⟩ : syracuseStep 2843 = 4265) R4265
theorem R2847 : ∃ j : ℕ, syracuseStep^[j] 2847 = 1 := reachStep (stepEq 1 (by rfl) ⟨2135, by rfl⟩ : syracuseStep 2847 = 4271) R4271
theorem R2857 : ∃ j : ℕ, syracuseStep^[j] 2857 = 1 := reachStep (stepEq 2 (by rfl) ⟨1071, by rfl⟩ : syracuseStep 2857 = 2143) R2143
theorem R2873 : ∃ j : ℕ, syracuseStep^[j] 2873 = 1 := reachStep (stepEq 2 (by rfl) ⟨1077, by rfl⟩ : syracuseStep 2873 = 2155) R2155
theorem R2927 : ∃ j : ℕ, syracuseStep^[j] 2927 = 1 := reachStep (stepEq 1 (by rfl) ⟨2195, by rfl⟩ : syracuseStep 2927 = 4391) R4391
theorem R2943 : ∃ j : ℕ, syracuseStep^[j] 2943 = 1 := reachStep (stepEq 1 (by rfl) ⟨2207, by rfl⟩ : syracuseStep 2943 = 4415) R4415
theorem R5503 : ∃ j : ℕ, syracuseStep^[j] 5503 = 1 := reachStep (stepEq 1 (by rfl) ⟨4127, by rfl⟩ : syracuseStep 5503 = 8255) R8255
theorem R5629 : ∃ j : ℕ, syracuseStep^[j] 5629 = 1 := reachStep (stepEq 3 (by rfl) ⟨1055, by rfl⟩ : syracuseStep 5629 = 2111) R2111
theorem R5687 : ∃ j : ℕ, syracuseStep^[j] 5687 = 1 := reachStep (stepEq 1 (by rfl) ⟨4265, by rfl⟩ : syracuseStep 5687 = 8531) R8531
theorem R5691 : ∃ j : ℕ, syracuseStep^[j] 5691 = 1 := reachStep (stepEq 1 (by rfl) ⟨4268, by rfl⟩ : syracuseStep 5691 = 8537) R8537
theorem R5695 : ∃ j : ℕ, syracuseStep^[j] 5695 = 1 := reachStep (stepEq 1 (by rfl) ⟨4271, by rfl⟩ : syracuseStep 5695 = 8543) R8543
theorem R5713 : ∃ j : ℕ, syracuseStep^[j] 5713 = 1 := reachStep (stepEq 2 (by rfl) ⟨2142, by rfl⟩ : syracuseStep 5713 = 4285) R4285
theorem R5715 : ∃ j : ℕ, syracuseStep^[j] 5715 = 1 := reachStep (stepEq 1 (by rfl) ⟨4286, by rfl⟩ : syracuseStep 5715 = 8573) R8573
theorem R5723 : ∃ j : ℕ, syracuseStep^[j] 5723 = 1 := reachStep (stepEq 1 (by rfl) ⟨4292, by rfl⟩ : syracuseStep 5723 = 8585) R8585
theorem R5735 : ∃ j : ℕ, syracuseStep^[j] 5735 = 1 := reachStep (stepEq 1 (by rfl) ⟨4301, by rfl⟩ : syracuseStep 5735 = 8603) R8603
theorem R5739 : ∃ j : ℕ, syracuseStep^[j] 5739 = 1 := reachStep (stepEq 1 (by rfl) ⟨4304, by rfl⟩ : syracuseStep 5739 = 8609) R8609
theorem R5747 : ∃ j : ℕ, syracuseStep^[j] 5747 = 1 := reachStep (stepEq 1 (by rfl) ⟨4310, by rfl⟩ : syracuseStep 5747 = 8621) R8621
theorem R5761 : ∃ j : ℕ, syracuseStep^[j] 5761 = 1 := reachStep (stepEq 2 (by rfl) ⟨2160, by rfl⟩ : syracuseStep 5761 = 4321) R4321
theorem R5769 : ∃ j : ℕ, syracuseStep^[j] 5769 = 1 := reachStep (stepEq 2 (by rfl) ⟨2163, by rfl⟩ : syracuseStep 5769 = 4327) R4327
theorem R5803 : ∃ j : ℕ, syracuseStep^[j] 5803 = 1 := reachStep (stepEq 1 (by rfl) ⟨4352, by rfl⟩ : syracuseStep 5803 = 8705) R8705
theorem R5855 : ∃ j : ℕ, syracuseStep^[j] 5855 = 1 := reachStep (stepEq 1 (by rfl) ⟨4391, by rfl⟩ : syracuseStep 5855 = 8783) R8783
theorem R5885 : ∃ j : ℕ, syracuseStep^[j] 5885 = 1 := reachStep (stepEq 3 (by rfl) ⟨1103, by rfl⟩ : syracuseStep 5885 = 2207) R2207
theorem R5915 : ∃ j : ℕ, syracuseStep^[j] 5915 = 1 := reachStep (stepEq 1 (by rfl) ⟨4436, by rfl⟩ : syracuseStep 5915 = 8873) R8873
theorem R5919 : ∃ j : ℕ, syracuseStep^[j] 5919 = 1 := reachStep (stepEq 1 (by rfl) ⟨4439, by rfl⟩ : syracuseStep 5919 = 8879) R8879
theorem R6121 : ∃ j : ℕ, syracuseStep^[j] 6121 = 1 := reachStep (stepEq 2 (by rfl) ⟨2295, by rfl⟩ : syracuseStep 6121 = 4591) R4591
theorem R11429 : ∃ j : ℕ, syracuseStep^[j] 11429 = 1 := reachStep (stepEq 4 (by rfl) ⟨1071, by rfl⟩ : syracuseStep 11429 = 2143) R2143
theorem R11431 : ∃ j : ℕ, syracuseStep^[j] 11431 = 1 := reachStep (stepEq 1 (by rfl) ⟨8573, by rfl⟩ : syracuseStep 11431 = 17147) R17147
theorem R11447 : ∃ j : ℕ, syracuseStep^[j] 11447 = 1 := reachStep (stepEq 1 (by rfl) ⟨8585, by rfl⟩ : syracuseStep 11447 = 17171) R17171
theorem R11627 : ∃ j : ℕ, syracuseStep^[j] 11627 = 1 := reachStep (stepEq 1 (by rfl) ⟨8720, by rfl⟩ : syracuseStep 11627 = 17441) R17441
theorem R11839 : ∃ j : ℕ, syracuseStep^[j] 11839 = 1 := reachStep (stepEq 1 (by rfl) ⟨8879, by rfl⟩ : syracuseStep 11839 = 17759) R17759
theorem R45791 : ∃ j : ℕ, syracuseStep^[j] 45791 = 1 := reachStep (stepEq 1 (by rfl) ⟨34343, by rfl⟩ : syracuseStep 45791 = 68687) R68687
theorem R46817 : ∃ j : ℕ, syracuseStep^[j] 46817 = 1 := reachStep (stepEq 2 (by rfl) ⟨17556, by rfl⟩ : syracuseStep 46817 = 35113) R35113
theorem R22517 : ∃ j : ℕ, syracuseStep^[j] 22517 = 1 := reachStep (stepEq 5 (by rfl) ⟨1055, by rfl⟩ : syracuseStep 22517 = 2111) R2111
theorem R22781 : ∃ j : ℕ, syracuseStep^[j] 22781 = 1 := reachStep (stepEq 3 (by rfl) ⟨4271, by rfl⟩ : syracuseStep 22781 = 8543) R8543
theorem R22861 : ∃ j : ℕ, syracuseStep^[j] 22861 = 1 := reachStep (stepEq 3 (by rfl) ⟨4286, by rfl⟩ : syracuseStep 22861 = 8573) R8573
theorem R23003 : ∃ j : ℕ, syracuseStep^[j] 23003 = 1 := reachStep (stepEq 1 (by rfl) ⟨17252, by rfl⟩ : syracuseStep 23003 = 34505) R34505
theorem R23009 : ∃ j : ℕ, syracuseStep^[j] 23009 = 1 := reachStep (stepEq 2 (by rfl) ⟨8628, by rfl⟩ : syracuseStep 23009 = 17257) R17257
theorem R23723 : ∃ j : ℕ, syracuseStep^[j] 23723 = 1 := reachStep (stepEq 1 (by rfl) ⟨17792, by rfl⟩ : syracuseStep 23723 = 35585) R35585
theorem R937 : ∃ j : ℕ, syracuseStep^[j] 937 = 1 := reachStep (stepEq 2 (by rfl) ⟨351, by rfl⟩ : syracuseStep 937 = 703) R703
theorem R1875 : ∃ j : ℕ, syracuseStep^[j] 1875 = 1 := reachStep (stepEq 1 (by rfl) ⟨1406, by rfl⟩ : syracuseStep 1875 = 2813) R2813
theorem R1895 : ∃ j : ℕ, syracuseStep^[j] 1895 = 1 := reachStep (stepEq 1 (by rfl) ⟨1421, by rfl⟩ : syracuseStep 1895 = 2843) R2843
theorem R1915 : ∃ j : ℕ, syracuseStep^[j] 1915 = 1 := reachStep (stepEq 1 (by rfl) ⟨1436, by rfl⟩ : syracuseStep 1915 = 2873) R2873
theorem R1951 : ∃ j : ℕ, syracuseStep^[j] 1951 = 1 := reachStep (stepEq 1 (by rfl) ⟨1463, by rfl⟩ : syracuseStep 1951 = 2927) R2927
theorem R1961 : ∃ j : ℕ, syracuseStep^[j] 1961 = 1 := reachStep (stepEq 2 (by rfl) ⟨735, by rfl⟩ : syracuseStep 1961 = 1471) R1471
theorem R3749 : ∃ j : ℕ, syracuseStep^[j] 3749 = 1 := reachStep (stepEq 4 (by rfl) ⟨351, by rfl⟩ : syracuseStep 3749 = 703) R703
theorem R3791 : ∃ j : ℕ, syracuseStep^[j] 3791 = 1 := reachStep (stepEq 1 (by rfl) ⟨2843, by rfl⟩ : syracuseStep 3791 = 5687) R5687
theorem R3809 : ∃ j : ℕ, syracuseStep^[j] 3809 = 1 := reachStep (stepEq 2 (by rfl) ⟨1428, by rfl⟩ : syracuseStep 3809 = 2857) R2857
theorem R3815 : ∃ j : ℕ, syracuseStep^[j] 3815 = 1 := reachStep (stepEq 1 (by rfl) ⟨2861, by rfl⟩ : syracuseStep 3815 = 5723) R5723
theorem R3823 : ∃ j : ℕ, syracuseStep^[j] 3823 = 1 := reachStep (stepEq 1 (by rfl) ⟨2867, by rfl⟩ : syracuseStep 3823 = 5735) R5735
theorem R3831 : ∃ j : ℕ, syracuseStep^[j] 3831 = 1 := reachStep (stepEq 1 (by rfl) ⟨2873, by rfl⟩ : syracuseStep 3831 = 5747) R5747
theorem R3903 : ∃ j : ℕ, syracuseStep^[j] 3903 = 1 := reachStep (stepEq 1 (by rfl) ⟨2927, by rfl⟩ : syracuseStep 3903 = 5855) R5855
theorem R3923 : ∃ j : ℕ, syracuseStep^[j] 3923 = 1 := reachStep (stepEq 1 (by rfl) ⟨2942, by rfl⟩ : syracuseStep 3923 = 5885) R5885
theorem R3943 : ∃ j : ℕ, syracuseStep^[j] 3943 = 1 := reachStep (stepEq 1 (by rfl) ⟨2957, by rfl⟩ : syracuseStep 3943 = 5915) R5915
theorem R7337 : ∃ j : ℕ, syracuseStep^[j] 7337 = 1 := reachStep (stepEq 2 (by rfl) ⟨2751, by rfl⟩ : syracuseStep 7337 = 5503) R5503
theorem R7501 : ∃ j : ℕ, syracuseStep^[j] 7501 = 1 := reachStep (stepEq 3 (by rfl) ⟨1406, by rfl⟩ : syracuseStep 7501 = 2813) R2813
theorem R7505 : ∃ j : ℕ, syracuseStep^[j] 7505 = 1 := reachStep (stepEq 2 (by rfl) ⟨2814, by rfl⟩ : syracuseStep 7505 = 5629) R5629
theorem R7619 : ∃ j : ℕ, syracuseStep^[j] 7619 = 1 := reachStep (stepEq 1 (by rfl) ⟨5714, by rfl⟩ : syracuseStep 7619 = 11429) R11429
theorem R7631 : ∃ j : ℕ, syracuseStep^[j] 7631 = 1 := reachStep (stepEq 1 (by rfl) ⟨5723, by rfl⟩ : syracuseStep 7631 = 11447) R11447
theorem R7661 : ∃ j : ℕ, syracuseStep^[j] 7661 = 1 := reachStep (stepEq 3 (by rfl) ⟨1436, by rfl⟩ : syracuseStep 7661 = 2873) R2873
theorem R7681 : ∃ j : ℕ, syracuseStep^[j] 7681 = 1 := reachStep (stepEq 2 (by rfl) ⟨2880, by rfl⟩ : syracuseStep 7681 = 5761) R5761
theorem R7751 : ∃ j : ℕ, syracuseStep^[j] 7751 = 1 := reachStep (stepEq 1 (by rfl) ⟨5813, by rfl⟩ : syracuseStep 7751 = 11627) R11627
theorem R7805 : ∃ j : ℕ, syracuseStep^[j] 7805 = 1 := reachStep (stepEq 3 (by rfl) ⟨1463, by rfl⟩ : syracuseStep 7805 = 2927) R2927
theorem R15011 : ∃ j : ℕ, syracuseStep^[j] 15011 = 1 := reachStep (stepEq 1 (by rfl) ⟨11258, by rfl⟩ : syracuseStep 15011 = 22517) R22517
theorem R15187 : ∃ j : ℕ, syracuseStep^[j] 15187 = 1 := reachStep (stepEq 1 (by rfl) ⟨11390, by rfl⟩ : syracuseStep 15187 = 22781) R22781
theorem R15241 : ∃ j : ℕ, syracuseStep^[j] 15241 = 1 := reachStep (stepEq 2 (by rfl) ⟨5715, by rfl⟩ : syracuseStep 15241 = 11431) R11431
theorem R15335 : ∃ j : ℕ, syracuseStep^[j] 15335 = 1 := reachStep (stepEq 1 (by rfl) ⟨11501, by rfl⟩ : syracuseStep 15335 = 23003) R23003
theorem R15785 : ∃ j : ℕ, syracuseStep^[j] 15785 = 1 := reachStep (stepEq 2 (by rfl) ⟨5919, by rfl⟩ : syracuseStep 15785 = 11839) R11839
theorem R15815 : ∃ j : ℕ, syracuseStep^[j] 15815 = 1 := reachStep (stepEq 1 (by rfl) ⟨11861, by rfl⟩ : syracuseStep 15815 = 23723) R23723
theorem R121925 : ∃ j : ℕ, syracuseStep^[j] 121925 = 1 := reachStep (stepEq 4 (by rfl) ⟨11430, by rfl⟩ : syracuseStep 121925 = 22861) R22861
theorem R61357 : ∃ j : ℕ, syracuseStep^[j] 61357 = 1 := reachStep (stepEq 3 (by rfl) ⟨11504, by rfl⟩ : syracuseStep 61357 = 23009) R23009
theorem R30527 : ∃ j : ℕ, syracuseStep^[j] 30527 = 1 := reachStep (stepEq 1 (by rfl) ⟨22895, by rfl⟩ : syracuseStep 30527 = 45791) R45791
theorem R31211 : ∃ j : ℕ, syracuseStep^[j] 31211 = 1 := reachStep (stepEq 1 (by rfl) ⟨23408, by rfl⟩ : syracuseStep 31211 = 46817) R46817
theorem R1249 : ∃ j : ℕ, syracuseStep^[j] 1249 = 1 := reachStep (stepEq 2 (by rfl) ⟨468, by rfl⟩ : syracuseStep 1249 = 937) R937
theorem R1263 : ∃ j : ℕ, syracuseStep^[j] 1263 = 1 := reachStep (stepEq 1 (by rfl) ⟨947, by rfl⟩ : syracuseStep 1263 = 1895) R1895
theorem R1307 : ∃ j : ℕ, syracuseStep^[j] 1307 = 1 := reachStep (stepEq 1 (by rfl) ⟨980, by rfl⟩ : syracuseStep 1307 = 1961) R1961
theorem R2499 : ∃ j : ℕ, syracuseStep^[j] 2499 = 1 := reachStep (stepEq 1 (by rfl) ⟨1874, by rfl⟩ : syracuseStep 2499 = 3749) R3749
theorem R2527 : ∃ j : ℕ, syracuseStep^[j] 2527 = 1 := reachStep (stepEq 1 (by rfl) ⟨1895, by rfl⟩ : syracuseStep 2527 = 3791) R3791
theorem R2539 : ∃ j : ℕ, syracuseStep^[j] 2539 = 1 := reachStep (stepEq 1 (by rfl) ⟨1904, by rfl⟩ : syracuseStep 2539 = 3809) R3809
theorem R2543 : ∃ j : ℕ, syracuseStep^[j] 2543 = 1 := reachStep (stepEq 1 (by rfl) ⟨1907, by rfl⟩ : syracuseStep 2543 = 3815) R3815
theorem R2553 : ∃ j : ℕ, syracuseStep^[j] 2553 = 1 := reachStep (stepEq 2 (by rfl) ⟨957, by rfl⟩ : syracuseStep 2553 = 1915) R1915
theorem R2601 : ∃ j : ℕ, syracuseStep^[j] 2601 = 1 := reachStep (stepEq 2 (by rfl) ⟨975, by rfl⟩ : syracuseStep 2601 = 1951) R1951
theorem R2615 : ∃ j : ℕ, syracuseStep^[j] 2615 = 1 := reachStep (stepEq 1 (by rfl) ⟨1961, by rfl⟩ : syracuseStep 2615 = 3923) R3923
theorem R4891 : ∃ j : ℕ, syracuseStep^[j] 4891 = 1 := reachStep (stepEq 1 (by rfl) ⟨3668, by rfl⟩ : syracuseStep 4891 = 7337) R7337
theorem R4997 : ∃ j : ℕ, syracuseStep^[j] 4997 = 1 := reachStep (stepEq 4 (by rfl) ⟨468, by rfl⟩ : syracuseStep 4997 = 937) R937
theorem R5003 : ∃ j : ℕ, syracuseStep^[j] 5003 = 1 := reachStep (stepEq 1 (by rfl) ⟨3752, by rfl⟩ : syracuseStep 5003 = 7505) R7505
theorem R5053 : ∃ j : ℕ, syracuseStep^[j] 5053 = 1 := reachStep (stepEq 3 (by rfl) ⟨947, by rfl⟩ : syracuseStep 5053 = 1895) R1895
theorem R5079 : ∃ j : ℕ, syracuseStep^[j] 5079 = 1 := reachStep (stepEq 1 (by rfl) ⟨3809, by rfl⟩ : syracuseStep 5079 = 7619) R7619
theorem R5087 : ∃ j : ℕ, syracuseStep^[j] 5087 = 1 := reachStep (stepEq 1 (by rfl) ⟨3815, by rfl⟩ : syracuseStep 5087 = 7631) R7631
theorem R5097 : ∃ j : ℕ, syracuseStep^[j] 5097 = 1 := reachStep (stepEq 2 (by rfl) ⟨1911, by rfl⟩ : syracuseStep 5097 = 3823) R3823
theorem R5107 : ∃ j : ℕ, syracuseStep^[j] 5107 = 1 := reachStep (stepEq 1 (by rfl) ⟨3830, by rfl⟩ : syracuseStep 5107 = 7661) R7661
theorem R5167 : ∃ j : ℕ, syracuseStep^[j] 5167 = 1 := reachStep (stepEq 1 (by rfl) ⟨3875, by rfl⟩ : syracuseStep 5167 = 7751) R7751
theorem R5203 : ∃ j : ℕ, syracuseStep^[j] 5203 = 1 := reachStep (stepEq 1 (by rfl) ⟨3902, by rfl⟩ : syracuseStep 5203 = 7805) R7805
theorem R5229 : ∃ j : ℕ, syracuseStep^[j] 5229 = 1 := reachStep (stepEq 3 (by rfl) ⟨980, by rfl⟩ : syracuseStep 5229 = 1961) R1961
theorem R5257 : ∃ j : ℕ, syracuseStep^[j] 5257 = 1 := reachStep (stepEq 2 (by rfl) ⟨1971, by rfl⟩ : syracuseStep 5257 = 3943) R3943
theorem R10001 : ∃ j : ℕ, syracuseStep^[j] 10001 = 1 := reachStep (stepEq 2 (by rfl) ⟨3750, by rfl⟩ : syracuseStep 10001 = 7501) R7501
theorem R10007 : ∃ j : ℕ, syracuseStep^[j] 10007 = 1 := reachStep (stepEq 1 (by rfl) ⟨7505, by rfl⟩ : syracuseStep 10007 = 15011) R15011
theorem R10223 : ∃ j : ℕ, syracuseStep^[j] 10223 = 1 := reachStep (stepEq 1 (by rfl) ⟨7667, by rfl⟩ : syracuseStep 10223 = 15335) R15335
theorem R10241 : ∃ j : ℕ, syracuseStep^[j] 10241 = 1 := reachStep (stepEq 2 (by rfl) ⟨3840, by rfl⟩ : syracuseStep 10241 = 7681) R7681
theorem R10523 : ∃ j : ℕ, syracuseStep^[j] 10523 = 1 := reachStep (stepEq 1 (by rfl) ⟨7892, by rfl⟩ : syracuseStep 10523 = 15785) R15785
theorem R10543 : ∃ j : ℕ, syracuseStep^[j] 10543 = 1 := reachStep (stepEq 1 (by rfl) ⟨7907, by rfl⟩ : syracuseStep 10543 = 15815) R15815
theorem R81809 : ∃ j : ℕ, syracuseStep^[j] 81809 = 1 := reachStep (stepEq 2 (by rfl) ⟨30678, by rfl⟩ : syracuseStep 81809 = 61357) R61357
theorem R20249 : ∃ j : ℕ, syracuseStep^[j] 20249 = 1 := reachStep (stepEq 2 (by rfl) ⟨7593, by rfl⟩ : syracuseStep 20249 = 15187) R15187
theorem R20321 : ∃ j : ℕ, syracuseStep^[j] 20321 = 1 := reachStep (stepEq 2 (by rfl) ⟨7620, by rfl⟩ : syracuseStep 20321 = 15241) R15241
theorem R20351 : ∃ j : ℕ, syracuseStep^[j] 20351 = 1 := reachStep (stepEq 1 (by rfl) ⟨15263, by rfl⟩ : syracuseStep 20351 = 30527) R30527
theorem R20807 : ∃ j : ℕ, syracuseStep^[j] 20807 = 1 := reachStep (stepEq 1 (by rfl) ⟨15605, by rfl⟩ : syracuseStep 20807 = 31211) R31211
theorem R325133 : ∃ j : ℕ, syracuseStep^[j] 325133 = 1 := reachStep (stepEq 3 (by rfl) ⟨60962, by rfl⟩ : syracuseStep 325133 = 121925) R121925
theorem R871 : ∃ j : ℕ, syracuseStep^[j] 871 = 1 := reachStep (stepEq 1 (by rfl) ⟨653, by rfl⟩ : syracuseStep 871 = 1307) R1307
theorem R1665 : ∃ j : ℕ, syracuseStep^[j] 1665 = 1 := reachStep (stepEq 2 (by rfl) ⟨624, by rfl⟩ : syracuseStep 1665 = 1249) R1249
theorem R1695 : ∃ j : ℕ, syracuseStep^[j] 1695 = 1 := reachStep (stepEq 1 (by rfl) ⟨1271, by rfl⟩ : syracuseStep 1695 = 2543) R2543
theorem R1743 : ∃ j : ℕ, syracuseStep^[j] 1743 = 1 := reachStep (stepEq 1 (by rfl) ⟨1307, by rfl⟩ : syracuseStep 1743 = 2615) R2615
theorem R3331 : ∃ j : ℕ, syracuseStep^[j] 3331 = 1 := reachStep (stepEq 1 (by rfl) ⟨2498, by rfl⟩ : syracuseStep 3331 = 4997) R4997
theorem R3335 : ∃ j : ℕ, syracuseStep^[j] 3335 = 1 := reachStep (stepEq 1 (by rfl) ⟨2501, by rfl⟩ : syracuseStep 3335 = 5003) R5003
theorem R3369 : ∃ j : ℕ, syracuseStep^[j] 3369 = 1 := reachStep (stepEq 2 (by rfl) ⟨1263, by rfl⟩ : syracuseStep 3369 = 2527) R2527
theorem R3385 : ∃ j : ℕ, syracuseStep^[j] 3385 = 1 := reachStep (stepEq 2 (by rfl) ⟨1269, by rfl⟩ : syracuseStep 3385 = 2539) R2539
theorem R3391 : ∃ j : ℕ, syracuseStep^[j] 3391 = 1 := reachStep (stepEq 1 (by rfl) ⟨2543, by rfl⟩ : syracuseStep 3391 = 5087) R5087
theorem R3485 : ∃ j : ℕ, syracuseStep^[j] 3485 = 1 := reachStep (stepEq 3 (by rfl) ⟨653, by rfl⟩ : syracuseStep 3485 = 1307) R1307
theorem R6521 : ∃ j : ℕ, syracuseStep^[j] 6521 = 1 := reachStep (stepEq 2 (by rfl) ⟨2445, by rfl⟩ : syracuseStep 6521 = 4891) R4891
theorem R6661 : ∃ j : ℕ, syracuseStep^[j] 6661 = 1 := reachStep (stepEq 4 (by rfl) ⟨624, by rfl⟩ : syracuseStep 6661 = 1249) R1249
theorem R6667 : ∃ j : ℕ, syracuseStep^[j] 6667 = 1 := reachStep (stepEq 1 (by rfl) ⟨5000, by rfl⟩ : syracuseStep 6667 = 10001) R10001
theorem R6671 : ∃ j : ℕ, syracuseStep^[j] 6671 = 1 := reachStep (stepEq 1 (by rfl) ⟨5003, by rfl⟩ : syracuseStep 6671 = 10007) R10007
theorem R6737 : ∃ j : ℕ, syracuseStep^[j] 6737 = 1 := reachStep (stepEq 2 (by rfl) ⟨2526, by rfl⟩ : syracuseStep 6737 = 5053) R5053
theorem R6781 : ∃ j : ℕ, syracuseStep^[j] 6781 = 1 := reachStep (stepEq 3 (by rfl) ⟨1271, by rfl⟩ : syracuseStep 6781 = 2543) R2543
theorem R6809 : ∃ j : ℕ, syracuseStep^[j] 6809 = 1 := reachStep (stepEq 2 (by rfl) ⟨2553, by rfl⟩ : syracuseStep 6809 = 5107) R5107
theorem R6815 : ∃ j : ℕ, syracuseStep^[j] 6815 = 1 := reachStep (stepEq 1 (by rfl) ⟨5111, by rfl⟩ : syracuseStep 6815 = 10223) R10223
theorem R6827 : ∃ j : ℕ, syracuseStep^[j] 6827 = 1 := reachStep (stepEq 1 (by rfl) ⟨5120, by rfl⟩ : syracuseStep 6827 = 10241) R10241
theorem R6889 : ∃ j : ℕ, syracuseStep^[j] 6889 = 1 := reachStep (stepEq 2 (by rfl) ⟨2583, by rfl⟩ : syracuseStep 6889 = 5167) R5167
theorem R7015 : ∃ j : ℕ, syracuseStep^[j] 7015 = 1 := reachStep (stepEq 1 (by rfl) ⟨5261, by rfl⟩ : syracuseStep 7015 = 10523) R10523
theorem R13499 : ∃ j : ℕ, syracuseStep^[j] 13499 = 1 := reachStep (stepEq 1 (by rfl) ⟨10124, by rfl⟩ : syracuseStep 13499 = 20249) R20249
theorem R13547 : ∃ j : ℕ, syracuseStep^[j] 13547 = 1 := reachStep (stepEq 1 (by rfl) ⟨10160, by rfl⟩ : syracuseStep 13547 = 20321) R20321
theorem R13567 : ∃ j : ℕ, syracuseStep^[j] 13567 = 1 := reachStep (stepEq 1 (by rfl) ⟨10175, by rfl⟩ : syracuseStep 13567 = 20351) R20351
theorem R13871 : ∃ j : ℕ, syracuseStep^[j] 13871 = 1 := reachStep (stepEq 1 (by rfl) ⟨10403, by rfl⟩ : syracuseStep 13871 = 20807) R20807
theorem R14057 : ∃ j : ℕ, syracuseStep^[j] 14057 = 1 := reachStep (stepEq 2 (by rfl) ⟨5271, by rfl⟩ : syracuseStep 14057 = 10543) R10543
theorem R216755 : ∃ j : ℕ, syracuseStep^[j] 216755 = 1 := reachStep (stepEq 1 (by rfl) ⟨162566, by rfl⟩ : syracuseStep 216755 = 325133) R325133
theorem R54539 : ∃ j : ℕ, syracuseStep^[j] 54539 = 1 := reachStep (stepEq 1 (by rfl) ⟨40904, by rfl⟩ : syracuseStep 54539 = 81809) R81809
theorem R27125 : ∃ j : ℕ, syracuseStep^[j] 27125 = 1 := reachStep (stepEq 5 (by rfl) ⟨1271, by rfl⟩ : syracuseStep 27125 = 2543) R2543
theorem R1161 : ∃ j : ℕ, syracuseStep^[j] 1161 = 1 := reachStep (stepEq 2 (by rfl) ⟨435, by rfl⟩ : syracuseStep 1161 = 871) R871
theorem R2223 : ∃ j : ℕ, syracuseStep^[j] 2223 = 1 := reachStep (stepEq 1 (by rfl) ⟨1667, by rfl⟩ : syracuseStep 2223 = 3335) R3335
theorem R2323 : ∃ j : ℕ, syracuseStep^[j] 2323 = 1 := reachStep (stepEq 1 (by rfl) ⟨1742, by rfl⟩ : syracuseStep 2323 = 3485) R3485
theorem R36359 : ∃ j : ℕ, syracuseStep^[j] 36359 = 1 := reachStep (stepEq 1 (by rfl) ⟨27269, by rfl⟩ : syracuseStep 36359 = 54539) R54539
theorem R4347 : ∃ j : ℕ, syracuseStep^[j] 4347 = 1 := reachStep (stepEq 1 (by rfl) ⟨3260, by rfl⟩ : syracuseStep 4347 = 6521) R6521
theorem R4441 : ∃ j : ℕ, syracuseStep^[j] 4441 = 1 := reachStep (stepEq 2 (by rfl) ⟨1665, by rfl⟩ : syracuseStep 4441 = 3331) R3331
theorem R4447 : ∃ j : ℕ, syracuseStep^[j] 4447 = 1 := reachStep (stepEq 1 (by rfl) ⟨3335, by rfl⟩ : syracuseStep 4447 = 6671) R6671
theorem R4491 : ∃ j : ℕ, syracuseStep^[j] 4491 = 1 := reachStep (stepEq 1 (by rfl) ⟨3368, by rfl⟩ : syracuseStep 4491 = 6737) R6737
theorem R4513 : ∃ j : ℕ, syracuseStep^[j] 4513 = 1 := reachStep (stepEq 2 (by rfl) ⟨1692, by rfl⟩ : syracuseStep 4513 = 3385) R3385
theorem R4521 : ∃ j : ℕ, syracuseStep^[j] 4521 = 1 := reachStep (stepEq 2 (by rfl) ⟨1695, by rfl⟩ : syracuseStep 4521 = 3391) R3391
theorem R4539 : ∃ j : ℕ, syracuseStep^[j] 4539 = 1 := reachStep (stepEq 1 (by rfl) ⟨3404, by rfl⟩ : syracuseStep 4539 = 6809) R6809
theorem R4543 : ∃ j : ℕ, syracuseStep^[j] 4543 = 1 := reachStep (stepEq 1 (by rfl) ⟨3407, by rfl⟩ : syracuseStep 4543 = 6815) R6815
theorem R4551 : ∃ j : ℕ, syracuseStep^[j] 4551 = 1 := reachStep (stepEq 1 (by rfl) ⟨3413, by rfl⟩ : syracuseStep 4551 = 6827) R6827
theorem R4645 : ∃ j : ℕ, syracuseStep^[j] 4645 = 1 := reachStep (stepEq 4 (by rfl) ⟨435, by rfl⟩ : syracuseStep 4645 = 871) R871
theorem R8999 : ∃ j : ℕ, syracuseStep^[j] 8999 = 1 := reachStep (stepEq 1 (by rfl) ⟨6749, by rfl⟩ : syracuseStep 8999 = 13499) R13499
theorem R9031 : ∃ j : ℕ, syracuseStep^[j] 9031 = 1 := reachStep (stepEq 1 (by rfl) ⟨6773, by rfl⟩ : syracuseStep 9031 = 13547) R13547
theorem R9041 : ∃ j : ℕ, syracuseStep^[j] 9041 = 1 := reachStep (stepEq 2 (by rfl) ⟨3390, by rfl⟩ : syracuseStep 9041 = 6781) R6781
theorem R9185 : ∃ j : ℕ, syracuseStep^[j] 9185 = 1 := reachStep (stepEq 2 (by rfl) ⟨3444, by rfl⟩ : syracuseStep 9185 = 6889) R6889
theorem R9247 : ∃ j : ℕ, syracuseStep^[j] 9247 = 1 := reachStep (stepEq 1 (by rfl) ⟨6935, by rfl⟩ : syracuseStep 9247 = 13871) R13871
theorem R9293 : ∃ j : ℕ, syracuseStep^[j] 9293 = 1 := reachStep (stepEq 3 (by rfl) ⟨1742, by rfl⟩ : syracuseStep 9293 = 3485) R3485
theorem R9353 : ∃ j : ℕ, syracuseStep^[j] 9353 = 1 := reachStep (stepEq 2 (by rfl) ⟨3507, by rfl⟩ : syracuseStep 9353 = 7015) R7015
theorem R9371 : ∃ j : ℕ, syracuseStep^[j] 9371 = 1 := reachStep (stepEq 1 (by rfl) ⟨7028, by rfl⟩ : syracuseStep 9371 = 14057) R14057
theorem R144503 : ∃ j : ℕ, syracuseStep^[j] 144503 = 1 := reachStep (stepEq 1 (by rfl) ⟨108377, by rfl⟩ : syracuseStep 144503 = 216755) R216755
theorem R17765 : ∃ j : ℕ, syracuseStep^[j] 17765 = 1 := reachStep (stepEq 4 (by rfl) ⟨1665, by rfl⟩ : syracuseStep 17765 = 3331) R3331
theorem R18083 : ∃ j : ℕ, syracuseStep^[j] 18083 = 1 := reachStep (stepEq 1 (by rfl) ⟨13562, by rfl⟩ : syracuseStep 18083 = 27125) R27125
theorem R18089 : ∃ j : ℕ, syracuseStep^[j] 18089 = 1 := reachStep (stepEq 2 (by rfl) ⟨6783, by rfl⟩ : syracuseStep 18089 = 13567) R13567
theorem R18157 : ∃ j : ℕ, syracuseStep^[j] 18157 = 1 := reachStep (stepEq 3 (by rfl) ⟨3404, by rfl⟩ : syracuseStep 18157 = 6809) R6809
theorem R3097 : ∃ j : ℕ, syracuseStep^[j] 3097 = 1 := reachStep (stepEq 2 (by rfl) ⟨1161, by rfl⟩ : syracuseStep 3097 = 2323) R2323
theorem R5921 : ∃ j : ℕ, syracuseStep^[j] 5921 = 1 := reachStep (stepEq 2 (by rfl) ⟨2220, by rfl⟩ : syracuseStep 5921 = 4441) R4441
theorem R5929 : ∃ j : ℕ, syracuseStep^[j] 5929 = 1 := reachStep (stepEq 2 (by rfl) ⟨2223, by rfl⟩ : syracuseStep 5929 = 4447) R4447
theorem R5999 : ∃ j : ℕ, syracuseStep^[j] 5999 = 1 := reachStep (stepEq 1 (by rfl) ⟨4499, by rfl⟩ : syracuseStep 5999 = 8999) R8999
theorem R6017 : ∃ j : ℕ, syracuseStep^[j] 6017 = 1 := reachStep (stepEq 2 (by rfl) ⟨2256, by rfl⟩ : syracuseStep 6017 = 4513) R4513
theorem R6027 : ∃ j : ℕ, syracuseStep^[j] 6027 = 1 := reachStep (stepEq 1 (by rfl) ⟨4520, by rfl⟩ : syracuseStep 6027 = 9041) R9041
theorem R6057 : ∃ j : ℕ, syracuseStep^[j] 6057 = 1 := reachStep (stepEq 2 (by rfl) ⟨2271, by rfl⟩ : syracuseStep 6057 = 4543) R4543
theorem R6123 : ∃ j : ℕ, syracuseStep^[j] 6123 = 1 := reachStep (stepEq 1 (by rfl) ⟨4592, by rfl⟩ : syracuseStep 6123 = 9185) R9185
theorem R6193 : ∃ j : ℕ, syracuseStep^[j] 6193 = 1 := reachStep (stepEq 2 (by rfl) ⟨2322, by rfl⟩ : syracuseStep 6193 = 4645) R4645
theorem R6195 : ∃ j : ℕ, syracuseStep^[j] 6195 = 1 := reachStep (stepEq 1 (by rfl) ⟨4646, by rfl⟩ : syracuseStep 6195 = 9293) R9293
theorem R6235 : ∃ j : ℕ, syracuseStep^[j] 6235 = 1 := reachStep (stepEq 1 (by rfl) ⟨4676, by rfl⟩ : syracuseStep 6235 = 9353) R9353
theorem R6247 : ∃ j : ℕ, syracuseStep^[j] 6247 = 1 := reachStep (stepEq 1 (by rfl) ⟨4685, by rfl⟩ : syracuseStep 6247 = 9371) R9371
theorem R11843 : ∃ j : ℕ, syracuseStep^[j] 11843 = 1 := reachStep (stepEq 1 (by rfl) ⟨8882, by rfl⟩ : syracuseStep 11843 = 17765) R17765
theorem R12041 : ∃ j : ℕ, syracuseStep^[j] 12041 = 1 := reachStep (stepEq 2 (by rfl) ⟨4515, by rfl⟩ : syracuseStep 12041 = 9031) R9031
theorem R12059 : ∃ j : ℕ, syracuseStep^[j] 12059 = 1 := reachStep (stepEq 1 (by rfl) ⟨9044, by rfl⟩ : syracuseStep 12059 = 18089) R18089
theorem R12329 : ∃ j : ℕ, syracuseStep^[j] 12329 = 1 := reachStep (stepEq 2 (by rfl) ⟨4623, by rfl⟩ : syracuseStep 12329 = 9247) R9247
theorem R48221 : ∃ j : ℕ, syracuseStep^[j] 48221 = 1 := reachStep (stepEq 3 (by rfl) ⟨9041, by rfl⟩ : syracuseStep 48221 = 18083) R18083
theorem R24209 : ∃ j : ℕ, syracuseStep^[j] 24209 = 1 := reachStep (stepEq 2 (by rfl) ⟨9078, by rfl⟩ : syracuseStep 24209 = 18157) R18157
theorem R24239 : ∃ j : ℕ, syracuseStep^[j] 24239 = 1 := reachStep (stepEq 1 (by rfl) ⟨18179, by rfl⟩ : syracuseStep 24239 = 36359) R36359
theorem R96335 : ∃ j : ℕ, syracuseStep^[j] 96335 = 1 := reachStep (stepEq 1 (by rfl) ⟨72251, by rfl⟩ : syracuseStep 96335 = 144503) R144503
theorem R3947 : ∃ j : ℕ, syracuseStep^[j] 3947 = 1 := reachStep (stepEq 1 (by rfl) ⟨2960, by rfl⟩ : syracuseStep 3947 = 5921) R5921
theorem R3999 : ∃ j : ℕ, syracuseStep^[j] 3999 = 1 := reachStep (stepEq 1 (by rfl) ⟨2999, by rfl⟩ : syracuseStep 3999 = 5999) R5999
theorem R4011 : ∃ j : ℕ, syracuseStep^[j] 4011 = 1 := reachStep (stepEq 1 (by rfl) ⟨3008, by rfl⟩ : syracuseStep 4011 = 6017) R6017
theorem R4129 : ∃ j : ℕ, syracuseStep^[j] 4129 = 1 := reachStep (stepEq 2 (by rfl) ⟨1548, by rfl⟩ : syracuseStep 4129 = 3097) R3097
theorem R7895 : ∃ j : ℕ, syracuseStep^[j] 7895 = 1 := reachStep (stepEq 1 (by rfl) ⟨5921, by rfl⟩ : syracuseStep 7895 = 11843) R11843
theorem R8027 : ∃ j : ℕ, syracuseStep^[j] 8027 = 1 := reachStep (stepEq 1 (by rfl) ⟨6020, by rfl⟩ : syracuseStep 8027 = 12041) R12041
theorem R8039 : ∃ j : ℕ, syracuseStep^[j] 8039 = 1 := reachStep (stepEq 1 (by rfl) ⟨6029, by rfl⟩ : syracuseStep 8039 = 12059) R12059
theorem R8219 : ∃ j : ℕ, syracuseStep^[j] 8219 = 1 := reachStep (stepEq 1 (by rfl) ⟨6164, by rfl⟩ : syracuseStep 8219 = 12329) R12329
theorem R8257 : ∃ j : ℕ, syracuseStep^[j] 8257 = 1 := reachStep (stepEq 2 (by rfl) ⟨3096, by rfl⟩ : syracuseStep 8257 = 6193) R6193
theorem R8329 : ∃ j : ℕ, syracuseStep^[j] 8329 = 1 := reachStep (stepEq 2 (by rfl) ⟨3123, by rfl⟩ : syracuseStep 8329 = 6247) R6247
theorem R15997 : ∃ j : ℕ, syracuseStep^[j] 15997 = 1 := reachStep (stepEq 3 (by rfl) ⟨2999, by rfl⟩ : syracuseStep 15997 = 5999) R5999
theorem R16139 : ∃ j : ℕ, syracuseStep^[j] 16139 = 1 := reachStep (stepEq 1 (by rfl) ⟨12104, by rfl⟩ : syracuseStep 16139 = 24209) R24209
theorem R16159 : ∃ j : ℕ, syracuseStep^[j] 16159 = 1 := reachStep (stepEq 1 (by rfl) ⟨12119, by rfl⟩ : syracuseStep 16159 = 24239) R24239
theorem R16517 : ∃ j : ℕ, syracuseStep^[j] 16517 = 1 := reachStep (stepEq 4 (by rfl) ⟨1548, by rfl⟩ : syracuseStep 16517 = 3097) R3097
theorem R64223 : ∃ j : ℕ, syracuseStep^[j] 64223 = 1 := reachStep (stepEq 1 (by rfl) ⟨48167, by rfl⟩ : syracuseStep 64223 = 96335) R96335
theorem R32147 : ∃ j : ℕ, syracuseStep^[j] 32147 = 1 := reachStep (stepEq 1 (by rfl) ⟨24110, by rfl⟩ : syracuseStep 32147 = 48221) R48221
theorem R2631 : ∃ j : ℕ, syracuseStep^[j] 2631 = 1 := reachStep (stepEq 1 (by rfl) ⟨1973, by rfl⟩ : syracuseStep 2631 = 3947) R3947
theorem R5263 : ∃ j : ℕ, syracuseStep^[j] 5263 = 1 := reachStep (stepEq 1 (by rfl) ⟨3947, by rfl⟩ : syracuseStep 5263 = 7895) R7895
theorem R5351 : ∃ j : ℕ, syracuseStep^[j] 5351 = 1 := reachStep (stepEq 1 (by rfl) ⟨4013, by rfl⟩ : syracuseStep 5351 = 8027) R8027
theorem R5359 : ∃ j : ℕ, syracuseStep^[j] 5359 = 1 := reachStep (stepEq 1 (by rfl) ⟨4019, by rfl⟩ : syracuseStep 5359 = 8039) R8039
theorem R5479 : ∃ j : ℕ, syracuseStep^[j] 5479 = 1 := reachStep (stepEq 1 (by rfl) ⟨4109, by rfl⟩ : syracuseStep 5479 = 8219) R8219
theorem R5505 : ∃ j : ℕ, syracuseStep^[j] 5505 = 1 := reachStep (stepEq 2 (by rfl) ⟨2064, by rfl⟩ : syracuseStep 5505 = 4129) R4129
theorem R42815 : ∃ j : ℕ, syracuseStep^[j] 42815 = 1 := reachStep (stepEq 1 (by rfl) ⟨32111, by rfl⟩ : syracuseStep 42815 = 64223) R64223
theorem R10525 : ∃ j : ℕ, syracuseStep^[j] 10525 = 1 := reachStep (stepEq 3 (by rfl) ⟨1973, by rfl⟩ : syracuseStep 10525 = 3947) R3947
theorem R10759 : ∃ j : ℕ, syracuseStep^[j] 10759 = 1 := reachStep (stepEq 1 (by rfl) ⟨8069, by rfl⟩ : syracuseStep 10759 = 16139) R16139
theorem R11009 : ∃ j : ℕ, syracuseStep^[j] 11009 = 1 := reachStep (stepEq 2 (by rfl) ⟨4128, by rfl⟩ : syracuseStep 11009 = 8257) R8257
theorem R11011 : ∃ j : ℕ, syracuseStep^[j] 11011 = 1 := reachStep (stepEq 1 (by rfl) ⟨8258, by rfl⟩ : syracuseStep 11011 = 16517) R16517
theorem R11105 : ∃ j : ℕ, syracuseStep^[j] 11105 = 1 := reachStep (stepEq 2 (by rfl) ⟨4164, by rfl⟩ : syracuseStep 11105 = 8329) R8329
theorem R21329 : ∃ j : ℕ, syracuseStep^[j] 21329 = 1 := reachStep (stepEq 2 (by rfl) ⟨7998, by rfl⟩ : syracuseStep 21329 = 15997) R15997
theorem R21431 : ∃ j : ℕ, syracuseStep^[j] 21431 = 1 := reachStep (stepEq 1 (by rfl) ⟨16073, by rfl⟩ : syracuseStep 21431 = 32147) R32147
theorem R21437 : ∃ j : ℕ, syracuseStep^[j] 21437 = 1 := reachStep (stepEq 3 (by rfl) ⟨4019, by rfl⟩ : syracuseStep 21437 = 8039) R8039
theorem R21545 : ∃ j : ℕ, syracuseStep^[j] 21545 = 1 := reachStep (stepEq 2 (by rfl) ⟨8079, by rfl⟩ : syracuseStep 21545 = 16159) R16159
theorem R3567 : ∃ j : ℕ, syracuseStep^[j] 3567 = 1 := reachStep (stepEq 1 (by rfl) ⟨2675, by rfl⟩ : syracuseStep 3567 = 5351) R5351
theorem R7145 : ∃ j : ℕ, syracuseStep^[j] 7145 = 1 := reachStep (stepEq 2 (by rfl) ⟨2679, by rfl⟩ : syracuseStep 7145 = 5359) R5359
theorem R7339 : ∃ j : ℕ, syracuseStep^[j] 7339 = 1 := reachStep (stepEq 1 (by rfl) ⟨5504, by rfl⟩ : syracuseStep 7339 = 11009) R11009
theorem R7403 : ∃ j : ℕ, syracuseStep^[j] 7403 = 1 := reachStep (stepEq 1 (by rfl) ⟨5552, by rfl⟩ : syracuseStep 7403 = 11105) R11105
theorem R14033 : ∃ j : ℕ, syracuseStep^[j] 14033 = 1 := reachStep (stepEq 2 (by rfl) ⟨5262, by rfl⟩ : syracuseStep 14033 = 10525) R10525
theorem R14219 : ∃ j : ℕ, syracuseStep^[j] 14219 = 1 := reachStep (stepEq 1 (by rfl) ⟨10664, by rfl⟩ : syracuseStep 14219 = 21329) R21329
theorem R14287 : ∃ j : ℕ, syracuseStep^[j] 14287 = 1 := reachStep (stepEq 1 (by rfl) ⟨10715, by rfl⟩ : syracuseStep 14287 = 21431) R21431
theorem R14291 : ∃ j : ℕ, syracuseStep^[j] 14291 = 1 := reachStep (stepEq 1 (by rfl) ⟨10718, by rfl⟩ : syracuseStep 14291 = 21437) R21437
theorem R14345 : ∃ j : ℕ, syracuseStep^[j] 14345 = 1 := reachStep (stepEq 2 (by rfl) ⟨5379, by rfl⟩ : syracuseStep 14345 = 10759) R10759
theorem R14363 : ∃ j : ℕ, syracuseStep^[j] 14363 = 1 := reachStep (stepEq 1 (by rfl) ⟨10772, by rfl⟩ : syracuseStep 14363 = 21545) R21545
theorem R14681 : ∃ j : ℕ, syracuseStep^[j] 14681 = 1 := reachStep (stepEq 2 (by rfl) ⟨5505, by rfl⟩ : syracuseStep 14681 = 11011) R11011
theorem R114173 : ∃ j : ℕ, syracuseStep^[j] 114173 = 1 := reachStep (stepEq 3 (by rfl) ⟨21407, by rfl⟩ : syracuseStep 114173 = 42815) R42815
theorem R37421 : ∃ j : ℕ, syracuseStep^[j] 37421 = 1 := reachStep (stepEq 3 (by rfl) ⟨7016, by rfl⟩ : syracuseStep 37421 = 14033) R14033
theorem R4763 : ∃ j : ℕ, syracuseStep^[j] 4763 = 1 := reachStep (stepEq 1 (by rfl) ⟨3572, by rfl⟩ : syracuseStep 4763 = 7145) R7145
theorem R4935 : ∃ j : ℕ, syracuseStep^[j] 4935 = 1 := reachStep (stepEq 1 (by rfl) ⟨3701, by rfl⟩ : syracuseStep 4935 = 7403) R7403
theorem R9355 : ∃ j : ℕ, syracuseStep^[j] 9355 = 1 := reachStep (stepEq 1 (by rfl) ⟨7016, by rfl⟩ : syracuseStep 9355 = 14033) R14033
theorem R9479 : ∃ j : ℕ, syracuseStep^[j] 9479 = 1 := reachStep (stepEq 1 (by rfl) ⟨7109, by rfl⟩ : syracuseStep 9479 = 14219) R14219
theorem R9527 : ∃ j : ℕ, syracuseStep^[j] 9527 = 1 := reachStep (stepEq 1 (by rfl) ⟨7145, by rfl⟩ : syracuseStep 9527 = 14291) R14291
theorem R9563 : ∃ j : ℕ, syracuseStep^[j] 9563 = 1 := reachStep (stepEq 1 (by rfl) ⟨7172, by rfl⟩ : syracuseStep 9563 = 14345) R14345
theorem R9575 : ∃ j : ℕ, syracuseStep^[j] 9575 = 1 := reachStep (stepEq 1 (by rfl) ⟨7181, by rfl⟩ : syracuseStep 9575 = 14363) R14363
theorem R9785 : ∃ j : ℕ, syracuseStep^[j] 9785 = 1 := reachStep (stepEq 2 (by rfl) ⟨3669, by rfl⟩ : syracuseStep 9785 = 7339) R7339
theorem R9787 : ∃ j : ℕ, syracuseStep^[j] 9787 = 1 := reachStep (stepEq 1 (by rfl) ⟨7340, by rfl⟩ : syracuseStep 9787 = 14681) R14681
theorem R76115 : ∃ j : ℕ, syracuseStep^[j] 76115 = 1 := reachStep (stepEq 1 (by rfl) ⟨57086, by rfl⟩ : syracuseStep 76115 = 114173) R114173
theorem R19049 : ∃ j : ℕ, syracuseStep^[j] 19049 = 1 := reachStep (stepEq 2 (by rfl) ⟨7143, by rfl⟩ : syracuseStep 19049 = 14287) R14287
theorem R3175 : ∃ j : ℕ, syracuseStep^[j] 3175 = 1 := reachStep (stepEq 1 (by rfl) ⟨2381, by rfl⟩ : syracuseStep 3175 = 4763) R4763
theorem R6319 : ∃ j : ℕ, syracuseStep^[j] 6319 = 1 := reachStep (stepEq 1 (by rfl) ⟨4739, by rfl⟩ : syracuseStep 6319 = 9479) R9479
theorem R6351 : ∃ j : ℕ, syracuseStep^[j] 6351 = 1 := reachStep (stepEq 1 (by rfl) ⟨4763, by rfl⟩ : syracuseStep 6351 = 9527) R9527
theorem R6375 : ∃ j : ℕ, syracuseStep^[j] 6375 = 1 := reachStep (stepEq 1 (by rfl) ⟨4781, by rfl⟩ : syracuseStep 6375 = 9563) R9563
theorem R6383 : ∃ j : ℕ, syracuseStep^[j] 6383 = 1 := reachStep (stepEq 1 (by rfl) ⟨4787, by rfl⟩ : syracuseStep 6383 = 9575) R9575
theorem R6523 : ∃ j : ℕ, syracuseStep^[j] 6523 = 1 := reachStep (stepEq 1 (by rfl) ⟨4892, by rfl⟩ : syracuseStep 6523 = 9785) R9785
theorem R12473 : ∃ j : ℕ, syracuseStep^[j] 12473 = 1 := reachStep (stepEq 2 (by rfl) ⟨4677, by rfl⟩ : syracuseStep 12473 = 9355) R9355
theorem R13049 : ∃ j : ℕ, syracuseStep^[j] 13049 = 1 := reachStep (stepEq 2 (by rfl) ⟨4893, by rfl⟩ : syracuseStep 13049 = 9787) R9787
theorem R50743 : ∃ j : ℕ, syracuseStep^[j] 50743 = 1 := reachStep (stepEq 1 (by rfl) ⟨38057, by rfl⟩ : syracuseStep 50743 = 76115) R76115
theorem R50797 : ∃ j : ℕ, syracuseStep^[j] 50797 = 1 := reachStep (stepEq 3 (by rfl) ⟨9524, by rfl⟩ : syracuseStep 50797 = 19049) R19049
theorem R24947 : ∃ j : ℕ, syracuseStep^[j] 24947 = 1 := reachStep (stepEq 1 (by rfl) ⟨18710, by rfl⟩ : syracuseStep 24947 = 37421) R37421
theorem R67657 : ∃ j : ℕ, syracuseStep^[j] 67657 = 1 := reachStep (stepEq 2 (by rfl) ⟨25371, by rfl⟩ : syracuseStep 67657 = 50743) R50743
theorem R67729 : ∃ j : ℕ, syracuseStep^[j] 67729 = 1 := reachStep (stepEq 2 (by rfl) ⟨25398, by rfl⟩ : syracuseStep 67729 = 50797) R50797
theorem R4233 : ∃ j : ℕ, syracuseStep^[j] 4233 = 1 := reachStep (stepEq 2 (by rfl) ⟨1587, by rfl⟩ : syracuseStep 4233 = 3175) R3175
theorem R4255 : ∃ j : ℕ, syracuseStep^[j] 4255 = 1 := reachStep (stepEq 1 (by rfl) ⟨3191, by rfl⟩ : syracuseStep 4255 = 6383) R6383
theorem R8315 : ∃ j : ℕ, syracuseStep^[j] 8315 = 1 := reachStep (stepEq 1 (by rfl) ⟨6236, by rfl⟩ : syracuseStep 8315 = 12473) R12473
theorem R8699 : ∃ j : ℕ, syracuseStep^[j] 8699 = 1 := reachStep (stepEq 1 (by rfl) ⟨6524, by rfl⟩ : syracuseStep 8699 = 13049) R13049
theorem R16631 : ∃ j : ℕ, syracuseStep^[j] 16631 = 1 := reachStep (stepEq 1 (by rfl) ⟨12473, by rfl⟩ : syracuseStep 16631 = 24947) R24947
theorem R5543 : ∃ j : ℕ, syracuseStep^[j] 5543 = 1 := reachStep (stepEq 1 (by rfl) ⟨4157, by rfl⟩ : syracuseStep 5543 = 8315) R8315
theorem R5673 : ∃ j : ℕ, syracuseStep^[j] 5673 = 1 := reachStep (stepEq 2 (by rfl) ⟨2127, by rfl⟩ : syracuseStep 5673 = 4255) R4255
theorem R5799 : ∃ j : ℕ, syracuseStep^[j] 5799 = 1 := reachStep (stepEq 1 (by rfl) ⟨4349, by rfl⟩ : syracuseStep 5799 = 8699) R8699
theorem R11087 : ∃ j : ℕ, syracuseStep^[j] 11087 = 1 := reachStep (stepEq 1 (by rfl) ⟨8315, by rfl⟩ : syracuseStep 11087 = 16631) R16631
theorem R90209 : ∃ j : ℕ, syracuseStep^[j] 90209 = 1 := reachStep (stepEq 2 (by rfl) ⟨33828, by rfl⟩ : syracuseStep 90209 = 67657) R67657
theorem R90305 : ∃ j : ℕ, syracuseStep^[j] 90305 = 1 := reachStep (stepEq 2 (by rfl) ⟨33864, by rfl⟩ : syracuseStep 90305 = 67729) R67729
theorem R3695 : ∃ j : ℕ, syracuseStep^[j] 3695 = 1 := reachStep (stepEq 1 (by rfl) ⟨2771, by rfl⟩ : syracuseStep 3695 = 5543) R5543
theorem R7391 : ∃ j : ℕ, syracuseStep^[j] 7391 = 1 := reachStep (stepEq 1 (by rfl) ⟨5543, by rfl⟩ : syracuseStep 7391 = 11087) R11087
theorem R60139 : ∃ j : ℕ, syracuseStep^[j] 60139 = 1 := reachStep (stepEq 1 (by rfl) ⟨45104, by rfl⟩ : syracuseStep 60139 = 90209) R90209
theorem R60203 : ∃ j : ℕ, syracuseStep^[j] 60203 = 1 := reachStep (stepEq 1 (by rfl) ⟨45152, by rfl⟩ : syracuseStep 60203 = 90305) R90305
theorem R2463 : ∃ j : ℕ, syracuseStep^[j] 2463 = 1 := reachStep (stepEq 1 (by rfl) ⟨1847, by rfl⟩ : syracuseStep 2463 = 3695) R3695
theorem R4927 : ∃ j : ℕ, syracuseStep^[j] 4927 = 1 := reachStep (stepEq 1 (by rfl) ⟨3695, by rfl⟩ : syracuseStep 4927 = 7391) R7391
theorem R80185 : ∃ j : ℕ, syracuseStep^[j] 80185 = 1 := reachStep (stepEq 2 (by rfl) ⟨30069, by rfl⟩ : syracuseStep 80185 = 60139) R60139
theorem R19709 : ∃ j : ℕ, syracuseStep^[j] 19709 = 1 := reachStep (stepEq 3 (by rfl) ⟨3695, by rfl⟩ : syracuseStep 19709 = 7391) R7391
theorem R160541 : ∃ j : ℕ, syracuseStep^[j] 160541 = 1 := reachStep (stepEq 3 (by rfl) ⟨30101, by rfl⟩ : syracuseStep 160541 = 60203) R60203
theorem R6569 : ∃ j : ℕ, syracuseStep^[j] 6569 = 1 := reachStep (stepEq 2 (by rfl) ⟨2463, by rfl⟩ : syracuseStep 6569 = 4927) R4927
theorem R106913 : ∃ j : ℕ, syracuseStep^[j] 106913 = 1 := reachStep (stepEq 2 (by rfl) ⟨40092, by rfl⟩ : syracuseStep 106913 = 80185) R80185
theorem R107027 : ∃ j : ℕ, syracuseStep^[j] 107027 = 1 := reachStep (stepEq 1 (by rfl) ⟨80270, by rfl⟩ : syracuseStep 107027 = 160541) R160541
theorem R13139 : ∃ j : ℕ, syracuseStep^[j] 13139 = 1 := reachStep (stepEq 1 (by rfl) ⟨9854, by rfl⟩ : syracuseStep 13139 = 19709) R19709
theorem R4379 : ∃ j : ℕ, syracuseStep^[j] 4379 = 1 := reachStep (stepEq 1 (by rfl) ⟨3284, by rfl⟩ : syracuseStep 4379 = 6569) R6569
theorem R71275 : ∃ j : ℕ, syracuseStep^[j] 71275 = 1 := reachStep (stepEq 1 (by rfl) ⟨53456, by rfl⟩ : syracuseStep 71275 = 106913) R106913
theorem R71351 : ∃ j : ℕ, syracuseStep^[j] 71351 = 1 := reachStep (stepEq 1 (by rfl) ⟨53513, by rfl⟩ : syracuseStep 71351 = 107027) R107027
theorem R8759 : ∃ j : ℕ, syracuseStep^[j] 8759 = 1 := reachStep (stepEq 1 (by rfl) ⟨6569, by rfl⟩ : syracuseStep 8759 = 13139) R13139
theorem R2919 : ∃ j : ℕ, syracuseStep^[j] 2919 = 1 := reachStep (stepEq 1 (by rfl) ⟨2189, by rfl⟩ : syracuseStep 2919 = 4379) R4379
theorem R5839 : ∃ j : ℕ, syracuseStep^[j] 5839 = 1 := reachStep (stepEq 1 (by rfl) ⟨4379, by rfl⟩ : syracuseStep 5839 = 8759) R8759
theorem R47567 : ∃ j : ℕ, syracuseStep^[j] 47567 = 1 := reachStep (stepEq 1 (by rfl) ⟨35675, by rfl⟩ : syracuseStep 47567 = 71351) R71351
theorem R95033 : ∃ j : ℕ, syracuseStep^[j] 95033 = 1 := reachStep (stepEq 2 (by rfl) ⟨35637, by rfl⟩ : syracuseStep 95033 = 71275) R71275
theorem R63355 : ∃ j : ℕ, syracuseStep^[j] 63355 = 1 := reachStep (stepEq 1 (by rfl) ⟨47516, by rfl⟩ : syracuseStep 63355 = 95033) R95033
theorem R31711 : ∃ j : ℕ, syracuseStep^[j] 31711 = 1 := reachStep (stepEq 1 (by rfl) ⟨23783, by rfl⟩ : syracuseStep 31711 = 47567) R47567
theorem R42281 : ∃ j : ℕ, syracuseStep^[j] 42281 = 1 := reachStep (stepEq 2 (by rfl) ⟨15855, by rfl⟩ : syracuseStep 42281 = 31711) R31711
theorem R84473 : ∃ j : ℕ, syracuseStep^[j] 84473 = 1 := reachStep (stepEq 2 (by rfl) ⟨31677, by rfl⟩ : syracuseStep 84473 = 63355) R63355
theorem R56315 : ∃ j : ℕ, syracuseStep^[j] 56315 = 1 := reachStep (stepEq 1 (by rfl) ⟨42236, by rfl⟩ : syracuseStep 56315 = 84473) R84473
theorem R28187 : ∃ j : ℕ, syracuseStep^[j] 28187 = 1 := reachStep (stepEq 1 (by rfl) ⟨21140, by rfl⟩ : syracuseStep 28187 = 42281) R42281
theorem R37543 : ∃ j : ℕ, syracuseStep^[j] 37543 = 1 := reachStep (stepEq 1 (by rfl) ⟨28157, by rfl⟩ : syracuseStep 37543 = 56315) R56315
theorem R18791 : ∃ j : ℕ, syracuseStep^[j] 18791 = 1 := reachStep (stepEq 1 (by rfl) ⟨14093, by rfl⟩ : syracuseStep 18791 = 28187) R28187
theorem R12527 : ∃ j : ℕ, syracuseStep^[j] 12527 = 1 := reachStep (stepEq 1 (by rfl) ⟨9395, by rfl⟩ : syracuseStep 12527 = 18791) R18791
theorem R50057 : ∃ j : ℕ, syracuseStep^[j] 50057 = 1 := reachStep (stepEq 2 (by rfl) ⟨18771, by rfl⟩ : syracuseStep 50057 = 37543) R37543
theorem R33371 : ∃ j : ℕ, syracuseStep^[j] 33371 = 1 := reachStep (stepEq 1 (by rfl) ⟨25028, by rfl⟩ : syracuseStep 33371 = 50057) R50057
theorem R8351 : ∃ j : ℕ, syracuseStep^[j] 8351 = 1 := reachStep (stepEq 1 (by rfl) ⟨6263, by rfl⟩ : syracuseStep 8351 = 12527) R12527
theorem R5567 : ∃ j : ℕ, syracuseStep^[j] 5567 = 1 := reachStep (stepEq 1 (by rfl) ⟨4175, by rfl⟩ : syracuseStep 5567 = 8351) R8351
theorem R22247 : ∃ j : ℕ, syracuseStep^[j] 22247 = 1 := reachStep (stepEq 1 (by rfl) ⟨16685, by rfl⟩ : syracuseStep 22247 = 33371) R33371
theorem R3711 : ∃ j : ℕ, syracuseStep^[j] 3711 = 1 := reachStep (stepEq 1 (by rfl) ⟨2783, by rfl⟩ : syracuseStep 3711 = 5567) R5567
theorem R14831 : ∃ j : ℕ, syracuseStep^[j] 14831 = 1 := reachStep (stepEq 1 (by rfl) ⟨11123, by rfl⟩ : syracuseStep 14831 = 22247) R22247
theorem R9887 : ∃ j : ℕ, syracuseStep^[j] 9887 = 1 := reachStep (stepEq 1 (by rfl) ⟨7415, by rfl⟩ : syracuseStep 9887 = 14831) R14831
theorem R6591 : ∃ j : ℕ, syracuseStep^[j] 6591 = 1 := reachStep (stepEq 1 (by rfl) ⟨4943, by rfl⟩ : syracuseStep 6591 = 9887) R9887
theorem R26365 : ∃ j : ℕ, syracuseStep^[j] 26365 = 1 := reachStep (stepEq 3 (by rfl) ⟨4943, by rfl⟩ : syracuseStep 26365 = 9887) R9887
theorem R35153 : ∃ j : ℕ, syracuseStep^[j] 35153 = 1 := reachStep (stepEq 2 (by rfl) ⟨13182, by rfl⟩ : syracuseStep 35153 = 26365) R26365
theorem R23435 : ∃ j : ℕ, syracuseStep^[j] 23435 = 1 := reachStep (stepEq 1 (by rfl) ⟨17576, by rfl⟩ : syracuseStep 23435 = 35153) R35153
theorem R15623 : ∃ j : ℕ, syracuseStep^[j] 15623 = 1 := reachStep (stepEq 1 (by rfl) ⟨11717, by rfl⟩ : syracuseStep 15623 = 23435) R23435
theorem R10415 : ∃ j : ℕ, syracuseStep^[j] 10415 = 1 := reachStep (stepEq 1 (by rfl) ⟨7811, by rfl⟩ : syracuseStep 10415 = 15623) R15623
theorem R6943 : ∃ j : ℕ, syracuseStep^[j] 6943 = 1 := reachStep (stepEq 1 (by rfl) ⟨5207, by rfl⟩ : syracuseStep 6943 = 10415) R10415
theorem R9257 : ∃ j : ℕ, syracuseStep^[j] 9257 = 1 := reachStep (stepEq 2 (by rfl) ⟨3471, by rfl⟩ : syracuseStep 9257 = 6943) R6943
theorem R6171 : ∃ j : ℕ, syracuseStep^[j] 6171 = 1 := reachStep (stepEq 1 (by rfl) ⟨4628, by rfl⟩ : syracuseStep 6171 = 9257) R9257

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 6724) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by
    obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  have hj : j ≤ 3361 := by omega
  interval_cases j
  · exact R1
  · exact R3
  · exact R5
  · exact R7
  · exact R9
  · exact R11
  · exact R13
  · exact R15
  · exact R17
  · exact R19
  · exact R21
  · exact R23
  · exact R25
  · exact R27
  · exact R29
  · exact R31
  · exact R33
  · exact R35
  · exact R37
  · exact R39
  · exact R41
  · exact R43
  · exact R45
  · exact R47
  · exact R49
  · exact R51
  · exact R53
  · exact R55
  · exact R57
  · exact R59
  · exact R61
  · exact R63
  · exact R65
  · exact R67
  · exact R69
  · exact R71
  · exact R73
  · exact R75
  · exact R77
  · exact R79
  · exact R81
  · exact R83
  · exact R85
  · exact R87
  · exact R89
  · exact R91
  · exact R93
  · exact R95
  · exact R97
  · exact R99
  · exact R101
  · exact R103
  · exact R105
  · exact R107
  · exact R109
  · exact R111
  · exact R113
  · exact R115
  · exact R117
  · exact R119
  · exact R121
  · exact R123
  · exact R125
  · exact R127
  · exact R129
  · exact R131
  · exact R133
  · exact R135
  · exact R137
  · exact R139
  · exact R141
  · exact R143
  · exact R145
  · exact R147
  · exact R149
  · exact R151
  · exact R153
  · exact R155
  · exact R157
  · exact R159
  · exact R161
  · exact R163
  · exact R165
  · exact R167
  · exact R169
  · exact R171
  · exact R173
  · exact R175
  · exact R177
  · exact R179
  · exact R181
  · exact R183
  · exact R185
  · exact R187
  · exact R189
  · exact R191
  · exact R193
  · exact R195
  · exact R197
  · exact R199
  · exact R201
  · exact R203
  · exact R205
  · exact R207
  · exact R209
  · exact R211
  · exact R213
  · exact R215
  · exact R217
  · exact R219
  · exact R221
  · exact R223
  · exact R225
  · exact R227
  · exact R229
  · exact R231
  · exact R233
  · exact R235
  · exact R237
  · exact R239
  · exact R241
  · exact R243
  · exact R245
  · exact R247
  · exact R249
  · exact R251
  · exact R253
  · exact R255
  · exact R257
  · exact R259
  · exact R261
  · exact R263
  · exact R265
  · exact R267
  · exact R269
  · exact R271
  · exact R273
  · exact R275
  · exact R277
  · exact R279
  · exact R281
  · exact R283
  · exact R285
  · exact R287
  · exact R289
  · exact R291
  · exact R293
  · exact R295
  · exact R297
  · exact R299
  · exact R301
  · exact R303
  · exact R305
  · exact R307
  · exact R309
  · exact R311
  · exact R313
  · exact R315
  · exact R317
  · exact R319
  · exact R321
  · exact R323
  · exact R325
  · exact R327
  · exact R329
  · exact R331
  · exact R333
  · exact R335
  · exact R337
  · exact R339
  · exact R341
  · exact R343
  · exact R345
  · exact R347
  · exact R349
  · exact R351
  · exact R353
  · exact R355
  · exact R357
  · exact R359
  · exact R361
  · exact R363
  · exact R365
  · exact R367
  · exact R369
  · exact R371
  · exact R373
  · exact R375
  · exact R377
  · exact R379
  · exact R381
  · exact R383
  · exact R385
  · exact R387
  · exact R389
  · exact R391
  · exact R393
  · exact R395
  · exact R397
  · exact R399
  · exact R401
  · exact R403
  · exact R405
  · exact R407
  · exact R409
  · exact R411
  · exact R413
  · exact R415
  · exact R417
  · exact R419
  · exact R421
  · exact R423
  · exact R425
  · exact R427
  · exact R429
  · exact R431
  · exact R433
  · exact R435
  · exact R437
  · exact R439
  · exact R441
  · exact R443
  · exact R445
  · exact R447
  · exact R449
  · exact R451
  · exact R453
  · exact R455
  · exact R457
  · exact R459
  · exact R461
  · exact R463
  · exact R465
  · exact R467
  · exact R469
  · exact R471
  · exact R473
  · exact R475
  · exact R477
  · exact R479
  · exact R481
  · exact R483
  · exact R485
  · exact R487
  · exact R489
  · exact R491
  · exact R493
  · exact R495
  · exact R497
  · exact R499
  · exact R501
  · exact R503
  · exact R505
  · exact R507
  · exact R509
  · exact R511
  · exact R513
  · exact R515
  · exact R517
  · exact R519
  · exact R521
  · exact R523
  · exact R525
  · exact R527
  · exact R529
  · exact R531
  · exact R533
  · exact R535
  · exact R537
  · exact R539
  · exact R541
  · exact R543
  · exact R545
  · exact R547
  · exact R549
  · exact R551
  · exact R553
  · exact R555
  · exact R557
  · exact R559
  · exact R561
  · exact R563
  · exact R565
  · exact R567
  · exact R569
  · exact R571
  · exact R573
  · exact R575
  · exact R577
  · exact R579
  · exact R581
  · exact R583
  · exact R585
  · exact R587
  · exact R589
  · exact R591
  · exact R593
  · exact R595
  · exact R597
  · exact R599
  · exact R601
  · exact R603
  · exact R605
  · exact R607
  · exact R609
  · exact R611
  · exact R613
  · exact R615
  · exact R617
  · exact R619
  · exact R621
  · exact R623
  · exact R625
  · exact R627
  · exact R629
  · exact R631
  · exact R633
  · exact R635
  · exact R637
  · exact R639
  · exact R641
  · exact R643
  · exact R645
  · exact R647
  · exact R649
  · exact R651
  · exact R653
  · exact R655
  · exact R657
  · exact R659
  · exact R661
  · exact R663
  · exact R665
  · exact R667
  · exact R669
  · exact R671
  · exact R673
  · exact R675
  · exact R677
  · exact R679
  · exact R681
  · exact R683
  · exact R685
  · exact R687
  · exact R689
  · exact R691
  · exact R693
  · exact R695
  · exact R697
  · exact R699
  · exact R701
  · exact R703
  · exact R705
  · exact R707
  · exact R709
  · exact R711
  · exact R713
  · exact R715
  · exact R717
  · exact R719
  · exact R721
  · exact R723
  · exact R725
  · exact R727
  · exact R729
  · exact R731
  · exact R733
  · exact R735
  · exact R737
  · exact R739
  · exact R741
  · exact R743
  · exact R745
  · exact R747
  · exact R749
  · exact R751
  · exact R753
  · exact R755
  · exact R757
  · exact R759
  · exact R761
  · exact R763
  · exact R765
  · exact R767
  · exact R769
  · exact R771
  · exact R773
  · exact R775
  · exact R777
  · exact R779
  · exact R781
  · exact R783
  · exact R785
  · exact R787
  · exact R789
  · exact R791
  · exact R793
  · exact R795
  · exact R797
  · exact R799
  · exact R801
  · exact R803
  · exact R805
  · exact R807
  · exact R809
  · exact R811
  · exact R813
  · exact R815
  · exact R817
  · exact R819
  · exact R821
  · exact R823
  · exact R825
  · exact R827
  · exact R829
  · exact R831
  · exact R833
  · exact R835
  · exact R837
  · exact R839
  · exact R841
  · exact R843
  · exact R845
  · exact R847
  · exact R849
  · exact R851
  · exact R853
  · exact R855
  · exact R857
  · exact R859
  · exact R861
  · exact R863
  · exact R865
  · exact R867
  · exact R869
  · exact R871
  · exact R873
  · exact R875
  · exact R877
  · exact R879
  · exact R881
  · exact R883
  · exact R885
  · exact R887
  · exact R889
  · exact R891
  · exact R893
  · exact R895
  · exact R897
  · exact R899
  · exact R901
  · exact R903
  · exact R905
  · exact R907
  · exact R909
  · exact R911
  · exact R913
  · exact R915
  · exact R917
  · exact R919
  · exact R921
  · exact R923
  · exact R925
  · exact R927
  · exact R929
  · exact R931
  · exact R933
  · exact R935
  · exact R937
  · exact R939
  · exact R941
  · exact R943
  · exact R945
  · exact R947
  · exact R949
  · exact R951
  · exact R953
  · exact R955
  · exact R957
  · exact R959
  · exact R961
  · exact R963
  · exact R965
  · exact R967
  · exact R969
  · exact R971
  · exact R973
  · exact R975
  · exact R977
  · exact R979
  · exact R981
  · exact R983
  · exact R985
  · exact R987
  · exact R989
  · exact R991
  · exact R993
  · exact R995
  · exact R997
  · exact R999
  · exact R1001
  · exact R1003
  · exact R1005
  · exact R1007
  · exact R1009
  · exact R1011
  · exact R1013
  · exact R1015
  · exact R1017
  · exact R1019
  · exact R1021
  · exact R1023
  · exact R1025
  · exact R1027
  · exact R1029
  · exact R1031
  · exact R1033
  · exact R1035
  · exact R1037
  · exact R1039
  · exact R1041
  · exact R1043
  · exact R1045
  · exact R1047
  · exact R1049
  · exact R1051
  · exact R1053
  · exact R1055
  · exact R1057
  · exact R1059
  · exact R1061
  · exact R1063
  · exact R1065
  · exact R1067
  · exact R1069
  · exact R1071
  · exact R1073
  · exact R1075
  · exact R1077
  · exact R1079
  · exact R1081
  · exact R1083
  · exact R1085
  · exact R1087
  · exact R1089
  · exact R1091
  · exact R1093
  · exact R1095
  · exact R1097
  · exact R1099
  · exact R1101
  · exact R1103
  · exact R1105
  · exact R1107
  · exact R1109
  · exact R1111
  · exact R1113
  · exact R1115
  · exact R1117
  · exact R1119
  · exact R1121
  · exact R1123
  · exact R1125
  · exact R1127
  · exact R1129
  · exact R1131
  · exact R1133
  · exact R1135
  · exact R1137
  · exact R1139
  · exact R1141
  · exact R1143
  · exact R1145
  · exact R1147
  · exact R1149
  · exact R1151
  · exact R1153
  · exact R1155
  · exact R1157
  · exact R1159
  · exact R1161
  · exact R1163
  · exact R1165
  · exact R1167
  · exact R1169
  · exact R1171
  · exact R1173
  · exact R1175
  · exact R1177
  · exact R1179
  · exact R1181
  · exact R1183
  · exact R1185
  · exact R1187
  · exact R1189
  · exact R1191
  · exact R1193
  · exact R1195
  · exact R1197
  · exact R1199
  · exact R1201
  · exact R1203
  · exact R1205
  · exact R1207
  · exact R1209
  · exact R1211
  · exact R1213
  · exact R1215
  · exact R1217
  · exact R1219
  · exact R1221
  · exact R1223
  · exact R1225
  · exact R1227
  · exact R1229
  · exact R1231
  · exact R1233
  · exact R1235
  · exact R1237
  · exact R1239
  · exact R1241
  · exact R1243
  · exact R1245
  · exact R1247
  · exact R1249
  · exact R1251
  · exact R1253
  · exact R1255
  · exact R1257
  · exact R1259
  · exact R1261
  · exact R1263
  · exact R1265
  · exact R1267
  · exact R1269
  · exact R1271
  · exact R1273
  · exact R1275
  · exact R1277
  · exact R1279
  · exact R1281
  · exact R1283
  · exact R1285
  · exact R1287
  · exact R1289
  · exact R1291
  · exact R1293
  · exact R1295
  · exact R1297
  · exact R1299
  · exact R1301
  · exact R1303
  · exact R1305
  · exact R1307
  · exact R1309
  · exact R1311
  · exact R1313
  · exact R1315
  · exact R1317
  · exact R1319
  · exact R1321
  · exact R1323
  · exact R1325
  · exact R1327
  · exact R1329
  · exact R1331
  · exact R1333
  · exact R1335
  · exact R1337
  · exact R1339
  · exact R1341
  · exact R1343
  · exact R1345
  · exact R1347
  · exact R1349
  · exact R1351
  · exact R1353
  · exact R1355
  · exact R1357
  · exact R1359
  · exact R1361
  · exact R1363
  · exact R1365
  · exact R1367
  · exact R1369
  · exact R1371
  · exact R1373
  · exact R1375
  · exact R1377
  · exact R1379
  · exact R1381
  · exact R1383
  · exact R1385
  · exact R1387
  · exact R1389
  · exact R1391
  · exact R1393
  · exact R1395
  · exact R1397
  · exact R1399
  · exact R1401
  · exact R1403
  · exact R1405
  · exact R1407
  · exact R1409
  · exact R1411
  · exact R1413
  · exact R1415
  · exact R1417
  · exact R1419
  · exact R1421
  · exact R1423
  · exact R1425
  · exact R1427
  · exact R1429
  · exact R1431
  · exact R1433
  · exact R1435
  · exact R1437
  · exact R1439
  · exact R1441
  · exact R1443
  · exact R1445
  · exact R1447
  · exact R1449
  · exact R1451
  · exact R1453
  · exact R1455
  · exact R1457
  · exact R1459
  · exact R1461
  · exact R1463
  · exact R1465
  · exact R1467
  · exact R1469
  · exact R1471
  · exact R1473
  · exact R1475
  · exact R1477
  · exact R1479
  · exact R1481
  · exact R1483
  · exact R1485
  · exact R1487
  · exact R1489
  · exact R1491
  · exact R1493
  · exact R1495
  · exact R1497
  · exact R1499
  · exact R1501
  · exact R1503
  · exact R1505
  · exact R1507
  · exact R1509
  · exact R1511
  · exact R1513
  · exact R1515
  · exact R1517
  · exact R1519
  · exact R1521
  · exact R1523
  · exact R1525
  · exact R1527
  · exact R1529
  · exact R1531
  · exact R1533
  · exact R1535
  · exact R1537
  · exact R1539
  · exact R1541
  · exact R1543
  · exact R1545
  · exact R1547
  · exact R1549
  · exact R1551
  · exact R1553
  · exact R1555
  · exact R1557
  · exact R1559
  · exact R1561
  · exact R1563
  · exact R1565
  · exact R1567
  · exact R1569
  · exact R1571
  · exact R1573
  · exact R1575
  · exact R1577
  · exact R1579
  · exact R1581
  · exact R1583
  · exact R1585
  · exact R1587
  · exact R1589
  · exact R1591
  · exact R1593
  · exact R1595
  · exact R1597
  · exact R1599
  · exact R1601
  · exact R1603
  · exact R1605
  · exact R1607
  · exact R1609
  · exact R1611
  · exact R1613
  · exact R1615
  · exact R1617
  · exact R1619
  · exact R1621
  · exact R1623
  · exact R1625
  · exact R1627
  · exact R1629
  · exact R1631
  · exact R1633
  · exact R1635
  · exact R1637
  · exact R1639
  · exact R1641
  · exact R1643
  · exact R1645
  · exact R1647
  · exact R1649
  · exact R1651
  · exact R1653
  · exact R1655
  · exact R1657
  · exact R1659
  · exact R1661
  · exact R1663
  · exact R1665
  · exact R1667
  · exact R1669
  · exact R1671
  · exact R1673
  · exact R1675
  · exact R1677
  · exact R1679
  · exact R1681
  · exact R1683
  · exact R1685
  · exact R1687
  · exact R1689
  · exact R1691
  · exact R1693
  · exact R1695
  · exact R1697
  · exact R1699
  · exact R1701
  · exact R1703
  · exact R1705
  · exact R1707
  · exact R1709
  · exact R1711
  · exact R1713
  · exact R1715
  · exact R1717
  · exact R1719
  · exact R1721
  · exact R1723
  · exact R1725
  · exact R1727
  · exact R1729
  · exact R1731
  · exact R1733
  · exact R1735
  · exact R1737
  · exact R1739
  · exact R1741
  · exact R1743
  · exact R1745
  · exact R1747
  · exact R1749
  · exact R1751
  · exact R1753
  · exact R1755
  · exact R1757
  · exact R1759
  · exact R1761
  · exact R1763
  · exact R1765
  · exact R1767
  · exact R1769
  · exact R1771
  · exact R1773
  · exact R1775
  · exact R1777
  · exact R1779
  · exact R1781
  · exact R1783
  · exact R1785
  · exact R1787
  · exact R1789
  · exact R1791
  · exact R1793
  · exact R1795
  · exact R1797
  · exact R1799
  · exact R1801
  · exact R1803
  · exact R1805
  · exact R1807
  · exact R1809
  · exact R1811
  · exact R1813
  · exact R1815
  · exact R1817
  · exact R1819
  · exact R1821
  · exact R1823
  · exact R1825
  · exact R1827
  · exact R1829
  · exact R1831
  · exact R1833
  · exact R1835
  · exact R1837
  · exact R1839
  · exact R1841
  · exact R1843
  · exact R1845
  · exact R1847
  · exact R1849
  · exact R1851
  · exact R1853
  · exact R1855
  · exact R1857
  · exact R1859
  · exact R1861
  · exact R1863
  · exact R1865
  · exact R1867
  · exact R1869
  · exact R1871
  · exact R1873
  · exact R1875
  · exact R1877
  · exact R1879
  · exact R1881
  · exact R1883
  · exact R1885
  · exact R1887
  · exact R1889
  · exact R1891
  · exact R1893
  · exact R1895
  · exact R1897
  · exact R1899
  · exact R1901
  · exact R1903
  · exact R1905
  · exact R1907
  · exact R1909
  · exact R1911
  · exact R1913
  · exact R1915
  · exact R1917
  · exact R1919
  · exact R1921
  · exact R1923
  · exact R1925
  · exact R1927
  · exact R1929
  · exact R1931
  · exact R1933
  · exact R1935
  · exact R1937
  · exact R1939
  · exact R1941
  · exact R1943
  · exact R1945
  · exact R1947
  · exact R1949
  · exact R1951
  · exact R1953
  · exact R1955
  · exact R1957
  · exact R1959
  · exact R1961
  · exact R1963
  · exact R1965
  · exact R1967
  · exact R1969
  · exact R1971
  · exact R1973
  · exact R1975
  · exact R1977
  · exact R1979
  · exact R1981
  · exact R1983
  · exact R1985
  · exact R1987
  · exact R1989
  · exact R1991
  · exact R1993
  · exact R1995
  · exact R1997
  · exact R1999
  · exact R2001
  · exact R2003
  · exact R2005
  · exact R2007
  · exact R2009
  · exact R2011
  · exact R2013
  · exact R2015
  · exact R2017
  · exact R2019
  · exact R2021
  · exact R2023
  · exact R2025
  · exact R2027
  · exact R2029
  · exact R2031
  · exact R2033
  · exact R2035
  · exact R2037
  · exact R2039
  · exact R2041
  · exact R2043
  · exact R2045
  · exact R2047
  · exact R2049
  · exact R2051
  · exact R2053
  · exact R2055
  · exact R2057
  · exact R2059
  · exact R2061
  · exact R2063
  · exact R2065
  · exact R2067
  · exact R2069
  · exact R2071
  · exact R2073
  · exact R2075
  · exact R2077
  · exact R2079
  · exact R2081
  · exact R2083
  · exact R2085
  · exact R2087
  · exact R2089
  · exact R2091
  · exact R2093
  · exact R2095
  · exact R2097
  · exact R2099
  · exact R2101
  · exact R2103
  · exact R2105
  · exact R2107
  · exact R2109
  · exact R2111
  · exact R2113
  · exact R2115
  · exact R2117
  · exact R2119
  · exact R2121
  · exact R2123
  · exact R2125
  · exact R2127
  · exact R2129
  · exact R2131
  · exact R2133
  · exact R2135
  · exact R2137
  · exact R2139
  · exact R2141
  · exact R2143
  · exact R2145
  · exact R2147
  · exact R2149
  · exact R2151
  · exact R2153
  · exact R2155
  · exact R2157
  · exact R2159
  · exact R2161
  · exact R2163
  · exact R2165
  · exact R2167
  · exact R2169
  · exact R2171
  · exact R2173
  · exact R2175
  · exact R2177
  · exact R2179
  · exact R2181
  · exact R2183
  · exact R2185
  · exact R2187
  · exact R2189
  · exact R2191
  · exact R2193
  · exact R2195
  · exact R2197
  · exact R2199
  · exact R2201
  · exact R2203
  · exact R2205
  · exact R2207
  · exact R2209
  · exact R2211
  · exact R2213
  · exact R2215
  · exact R2217
  · exact R2219
  · exact R2221
  · exact R2223
  · exact R2225
  · exact R2227
  · exact R2229
  · exact R2231
  · exact R2233
  · exact R2235
  · exact R2237
  · exact R2239
  · exact R2241
  · exact R2243
  · exact R2245
  · exact R2247
  · exact R2249
  · exact R2251
  · exact R2253
  · exact R2255
  · exact R2257
  · exact R2259
  · exact R2261
  · exact R2263
  · exact R2265
  · exact R2267
  · exact R2269
  · exact R2271
  · exact R2273
  · exact R2275
  · exact R2277
  · exact R2279
  · exact R2281
  · exact R2283
  · exact R2285
  · exact R2287
  · exact R2289
  · exact R2291
  · exact R2293
  · exact R2295
  · exact R2297
  · exact R2299
  · exact R2301
  · exact R2303
  · exact R2305
  · exact R2307
  · exact R2309
  · exact R2311
  · exact R2313
  · exact R2315
  · exact R2317
  · exact R2319
  · exact R2321
  · exact R2323
  · exact R2325
  · exact R2327
  · exact R2329
  · exact R2331
  · exact R2333
  · exact R2335
  · exact R2337
  · exact R2339
  · exact R2341
  · exact R2343
  · exact R2345
  · exact R2347
  · exact R2349
  · exact R2351
  · exact R2353
  · exact R2355
  · exact R2357
  · exact R2359
  · exact R2361
  · exact R2363
  · exact R2365
  · exact R2367
  · exact R2369
  · exact R2371
  · exact R2373
  · exact R2375
  · exact R2377
  · exact R2379
  · exact R2381
  · exact R2383
  · exact R2385
  · exact R2387
  · exact R2389
  · exact R2391
  · exact R2393
  · exact R2395
  · exact R2397
  · exact R2399
  · exact R2401
  · exact R2403
  · exact R2405
  · exact R2407
  · exact R2409
  · exact R2411
  · exact R2413
  · exact R2415
  · exact R2417
  · exact R2419
  · exact R2421
  · exact R2423
  · exact R2425
  · exact R2427
  · exact R2429
  · exact R2431
  · exact R2433
  · exact R2435
  · exact R2437
  · exact R2439
  · exact R2441
  · exact R2443
  · exact R2445
  · exact R2447
  · exact R2449
  · exact R2451
  · exact R2453
  · exact R2455
  · exact R2457
  · exact R2459
  · exact R2461
  · exact R2463
  · exact R2465
  · exact R2467
  · exact R2469
  · exact R2471
  · exact R2473
  · exact R2475
  · exact R2477
  · exact R2479
  · exact R2481
  · exact R2483
  · exact R2485
  · exact R2487
  · exact R2489
  · exact R2491
  · exact R2493
  · exact R2495
  · exact R2497
  · exact R2499
  · exact R2501
  · exact R2503
  · exact R2505
  · exact R2507
  · exact R2509
  · exact R2511
  · exact R2513
  · exact R2515
  · exact R2517
  · exact R2519
  · exact R2521
  · exact R2523
  · exact R2525
  · exact R2527
  · exact R2529
  · exact R2531
  · exact R2533
  · exact R2535
  · exact R2537
  · exact R2539
  · exact R2541
  · exact R2543
  · exact R2545
  · exact R2547
  · exact R2549
  · exact R2551
  · exact R2553
  · exact R2555
  · exact R2557
  · exact R2559
  · exact R2561
  · exact R2563
  · exact R2565
  · exact R2567
  · exact R2569
  · exact R2571
  · exact R2573
  · exact R2575
  · exact R2577
  · exact R2579
  · exact R2581
  · exact R2583
  · exact R2585
  · exact R2587
  · exact R2589
  · exact R2591
  · exact R2593
  · exact R2595
  · exact R2597
  · exact R2599
  · exact R2601
  · exact R2603
  · exact R2605
  · exact R2607
  · exact R2609
  · exact R2611
  · exact R2613
  · exact R2615
  · exact R2617
  · exact R2619
  · exact R2621
  · exact R2623
  · exact R2625
  · exact R2627
  · exact R2629
  · exact R2631
  · exact R2633
  · exact R2635
  · exact R2637
  · exact R2639
  · exact R2641
  · exact R2643
  · exact R2645
  · exact R2647
  · exact R2649
  · exact R2651
  · exact R2653
  · exact R2655
  · exact R2657
  · exact R2659
  · exact R2661
  · exact R2663
  · exact R2665
  · exact R2667
  · exact R2669
  · exact R2671
  · exact R2673
  · exact R2675
  · exact R2677
  · exact R2679
  · exact R2681
  · exact R2683
  · exact R2685
  · exact R2687
  · exact R2689
  · exact R2691
  · exact R2693
  · exact R2695
  · exact R2697
  · exact R2699
  · exact R2701
  · exact R2703
  · exact R2705
  · exact R2707
  · exact R2709
  · exact R2711
  · exact R2713
  · exact R2715
  · exact R2717
  · exact R2719
  · exact R2721
  · exact R2723
  · exact R2725
  · exact R2727
  · exact R2729
  · exact R2731
  · exact R2733
  · exact R2735
  · exact R2737
  · exact R2739
  · exact R2741
  · exact R2743
  · exact R2745
  · exact R2747
  · exact R2749
  · exact R2751
  · exact R2753
  · exact R2755
  · exact R2757
  · exact R2759
  · exact R2761
  · exact R2763
  · exact R2765
  · exact R2767
  · exact R2769
  · exact R2771
  · exact R2773
  · exact R2775
  · exact R2777
  · exact R2779
  · exact R2781
  · exact R2783
  · exact R2785
  · exact R2787
  · exact R2789
  · exact R2791
  · exact R2793
  · exact R2795
  · exact R2797
  · exact R2799
  · exact R2801
  · exact R2803
  · exact R2805
  · exact R2807
  · exact R2809
  · exact R2811
  · exact R2813
  · exact R2815
  · exact R2817
  · exact R2819
  · exact R2821
  · exact R2823
  · exact R2825
  · exact R2827
  · exact R2829
  · exact R2831
  · exact R2833
  · exact R2835
  · exact R2837
  · exact R2839
  · exact R2841
  · exact R2843
  · exact R2845
  · exact R2847
  · exact R2849
  · exact R2851
  · exact R2853
  · exact R2855
  · exact R2857
  · exact R2859
  · exact R2861
  · exact R2863
  · exact R2865
  · exact R2867
  · exact R2869
  · exact R2871
  · exact R2873
  · exact R2875
  · exact R2877
  · exact R2879
  · exact R2881
  · exact R2883
  · exact R2885
  · exact R2887
  · exact R2889
  · exact R2891
  · exact R2893
  · exact R2895
  · exact R2897
  · exact R2899
  · exact R2901
  · exact R2903
  · exact R2905
  · exact R2907
  · exact R2909
  · exact R2911
  · exact R2913
  · exact R2915
  · exact R2917
  · exact R2919
  · exact R2921
  · exact R2923
  · exact R2925
  · exact R2927
  · exact R2929
  · exact R2931
  · exact R2933
  · exact R2935
  · exact R2937
  · exact R2939
  · exact R2941
  · exact R2943
  · exact R2945
  · exact R2947
  · exact R2949
  · exact R2951
  · exact R2953
  · exact R2955
  · exact R2957
  · exact R2959
  · exact R2961
  · exact R2963
  · exact R2965
  · exact R2967
  · exact R2969
  · exact R2971
  · exact R2973
  · exact R2975
  · exact R2977
  · exact R2979
  · exact R2981
  · exact R2983
  · exact R2985
  · exact R2987
  · exact R2989
  · exact R2991
  · exact R2993
  · exact R2995
  · exact R2997
  · exact R2999
  · exact R3001
  · exact R3003
  · exact R3005
  · exact R3007
  · exact R3009
  · exact R3011
  · exact R3013
  · exact R3015
  · exact R3017
  · exact R3019
  · exact R3021
  · exact R3023
  · exact R3025
  · exact R3027
  · exact R3029
  · exact R3031
  · exact R3033
  · exact R3035
  · exact R3037
  · exact R3039
  · exact R3041
  · exact R3043
  · exact R3045
  · exact R3047
  · exact R3049
  · exact R3051
  · exact R3053
  · exact R3055
  · exact R3057
  · exact R3059
  · exact R3061
  · exact R3063
  · exact R3065
  · exact R3067
  · exact R3069
  · exact R3071
  · exact R3073
  · exact R3075
  · exact R3077
  · exact R3079
  · exact R3081
  · exact R3083
  · exact R3085
  · exact R3087
  · exact R3089
  · exact R3091
  · exact R3093
  · exact R3095
  · exact R3097
  · exact R3099
  · exact R3101
  · exact R3103
  · exact R3105
  · exact R3107
  · exact R3109
  · exact R3111
  · exact R3113
  · exact R3115
  · exact R3117
  · exact R3119
  · exact R3121
  · exact R3123
  · exact R3125
  · exact R3127
  · exact R3129
  · exact R3131
  · exact R3133
  · exact R3135
  · exact R3137
  · exact R3139
  · exact R3141
  · exact R3143
  · exact R3145
  · exact R3147
  · exact R3149
  · exact R3151
  · exact R3153
  · exact R3155
  · exact R3157
  · exact R3159
  · exact R3161
  · exact R3163
  · exact R3165
  · exact R3167
  · exact R3169
  · exact R3171
  · exact R3173
  · exact R3175
  · exact R3177
  · exact R3179
  · exact R3181
  · exact R3183
  · exact R3185
  · exact R3187
  · exact R3189
  · exact R3191
  · exact R3193
  · exact R3195
  · exact R3197
  · exact R3199
  · exact R3201
  · exact R3203
  · exact R3205
  · exact R3207
  · exact R3209
  · exact R3211
  · exact R3213
  · exact R3215
  · exact R3217
  · exact R3219
  · exact R3221
  · exact R3223
  · exact R3225
  · exact R3227
  · exact R3229
  · exact R3231
  · exact R3233
  · exact R3235
  · exact R3237
  · exact R3239
  · exact R3241
  · exact R3243
  · exact R3245
  · exact R3247
  · exact R3249
  · exact R3251
  · exact R3253
  · exact R3255
  · exact R3257
  · exact R3259
  · exact R3261
  · exact R3263
  · exact R3265
  · exact R3267
  · exact R3269
  · exact R3271
  · exact R3273
  · exact R3275
  · exact R3277
  · exact R3279
  · exact R3281
  · exact R3283
  · exact R3285
  · exact R3287
  · exact R3289
  · exact R3291
  · exact R3293
  · exact R3295
  · exact R3297
  · exact R3299
  · exact R3301
  · exact R3303
  · exact R3305
  · exact R3307
  · exact R3309
  · exact R3311
  · exact R3313
  · exact R3315
  · exact R3317
  · exact R3319
  · exact R3321
  · exact R3323
  · exact R3325
  · exact R3327
  · exact R3329
  · exact R3331
  · exact R3333
  · exact R3335
  · exact R3337
  · exact R3339
  · exact R3341
  · exact R3343
  · exact R3345
  · exact R3347
  · exact R3349
  · exact R3351
  · exact R3353
  · exact R3355
  · exact R3357
  · exact R3359
  · exact R3361
  · exact R3363
  · exact R3365
  · exact R3367
  · exact R3369
  · exact R3371
  · exact R3373
  · exact R3375
  · exact R3377
  · exact R3379
  · exact R3381
  · exact R3383
  · exact R3385
  · exact R3387
  · exact R3389
  · exact R3391
  · exact R3393
  · exact R3395
  · exact R3397
  · exact R3399
  · exact R3401
  · exact R3403
  · exact R3405
  · exact R3407
  · exact R3409
  · exact R3411
  · exact R3413
  · exact R3415
  · exact R3417
  · exact R3419
  · exact R3421
  · exact R3423
  · exact R3425
  · exact R3427
  · exact R3429
  · exact R3431
  · exact R3433
  · exact R3435
  · exact R3437
  · exact R3439
  · exact R3441
  · exact R3443
  · exact R3445
  · exact R3447
  · exact R3449
  · exact R3451
  · exact R3453
  · exact R3455
  · exact R3457
  · exact R3459
  · exact R3461
  · exact R3463
  · exact R3465
  · exact R3467
  · exact R3469
  · exact R3471
  · exact R3473
  · exact R3475
  · exact R3477
  · exact R3479
  · exact R3481
  · exact R3483
  · exact R3485
  · exact R3487
  · exact R3489
  · exact R3491
  · exact R3493
  · exact R3495
  · exact R3497
  · exact R3499
  · exact R3501
  · exact R3503
  · exact R3505
  · exact R3507
  · exact R3509
  · exact R3511
  · exact R3513
  · exact R3515
  · exact R3517
  · exact R3519
  · exact R3521
  · exact R3523
  · exact R3525
  · exact R3527
  · exact R3529
  · exact R3531
  · exact R3533
  · exact R3535
  · exact R3537
  · exact R3539
  · exact R3541
  · exact R3543
  · exact R3545
  · exact R3547
  · exact R3549
  · exact R3551
  · exact R3553
  · exact R3555
  · exact R3557
  · exact R3559
  · exact R3561
  · exact R3563
  · exact R3565
  · exact R3567
  · exact R3569
  · exact R3571
  · exact R3573
  · exact R3575
  · exact R3577
  · exact R3579
  · exact R3581
  · exact R3583
  · exact R3585
  · exact R3587
  · exact R3589
  · exact R3591
  · exact R3593
  · exact R3595
  · exact R3597
  · exact R3599
  · exact R3601
  · exact R3603
  · exact R3605
  · exact R3607
  · exact R3609
  · exact R3611
  · exact R3613
  · exact R3615
  · exact R3617
  · exact R3619
  · exact R3621
  · exact R3623
  · exact R3625
  · exact R3627
  · exact R3629
  · exact R3631
  · exact R3633
  · exact R3635
  · exact R3637
  · exact R3639
  · exact R3641
  · exact R3643
  · exact R3645
  · exact R3647
  · exact R3649
  · exact R3651
  · exact R3653
  · exact R3655
  · exact R3657
  · exact R3659
  · exact R3661
  · exact R3663
  · exact R3665
  · exact R3667
  · exact R3669
  · exact R3671
  · exact R3673
  · exact R3675
  · exact R3677
  · exact R3679
  · exact R3681
  · exact R3683
  · exact R3685
  · exact R3687
  · exact R3689
  · exact R3691
  · exact R3693
  · exact R3695
  · exact R3697
  · exact R3699
  · exact R3701
  · exact R3703
  · exact R3705
  · exact R3707
  · exact R3709
  · exact R3711
  · exact R3713
  · exact R3715
  · exact R3717
  · exact R3719
  · exact R3721
  · exact R3723
  · exact R3725
  · exact R3727
  · exact R3729
  · exact R3731
  · exact R3733
  · exact R3735
  · exact R3737
  · exact R3739
  · exact R3741
  · exact R3743
  · exact R3745
  · exact R3747
  · exact R3749
  · exact R3751
  · exact R3753
  · exact R3755
  · exact R3757
  · exact R3759
  · exact R3761
  · exact R3763
  · exact R3765
  · exact R3767
  · exact R3769
  · exact R3771
  · exact R3773
  · exact R3775
  · exact R3777
  · exact R3779
  · exact R3781
  · exact R3783
  · exact R3785
  · exact R3787
  · exact R3789
  · exact R3791
  · exact R3793
  · exact R3795
  · exact R3797
  · exact R3799
  · exact R3801
  · exact R3803
  · exact R3805
  · exact R3807
  · exact R3809
  · exact R3811
  · exact R3813
  · exact R3815
  · exact R3817
  · exact R3819
  · exact R3821
  · exact R3823
  · exact R3825
  · exact R3827
  · exact R3829
  · exact R3831
  · exact R3833
  · exact R3835
  · exact R3837
  · exact R3839
  · exact R3841
  · exact R3843
  · exact R3845
  · exact R3847
  · exact R3849
  · exact R3851
  · exact R3853
  · exact R3855
  · exact R3857
  · exact R3859
  · exact R3861
  · exact R3863
  · exact R3865
  · exact R3867
  · exact R3869
  · exact R3871
  · exact R3873
  · exact R3875
  · exact R3877
  · exact R3879
  · exact R3881
  · exact R3883
  · exact R3885
  · exact R3887
  · exact R3889
  · exact R3891
  · exact R3893
  · exact R3895
  · exact R3897
  · exact R3899
  · exact R3901
  · exact R3903
  · exact R3905
  · exact R3907
  · exact R3909
  · exact R3911
  · exact R3913
  · exact R3915
  · exact R3917
  · exact R3919
  · exact R3921
  · exact R3923
  · exact R3925
  · exact R3927
  · exact R3929
  · exact R3931
  · exact R3933
  · exact R3935
  · exact R3937
  · exact R3939
  · exact R3941
  · exact R3943
  · exact R3945
  · exact R3947
  · exact R3949
  · exact R3951
  · exact R3953
  · exact R3955
  · exact R3957
  · exact R3959
  · exact R3961
  · exact R3963
  · exact R3965
  · exact R3967
  · exact R3969
  · exact R3971
  · exact R3973
  · exact R3975
  · exact R3977
  · exact R3979
  · exact R3981
  · exact R3983
  · exact R3985
  · exact R3987
  · exact R3989
  · exact R3991
  · exact R3993
  · exact R3995
  · exact R3997
  · exact R3999
  · exact R4001
  · exact R4003
  · exact R4005
  · exact R4007
  · exact R4009
  · exact R4011
  · exact R4013
  · exact R4015
  · exact R4017
  · exact R4019
  · exact R4021
  · exact R4023
  · exact R4025
  · exact R4027
  · exact R4029
  · exact R4031
  · exact R4033
  · exact R4035
  · exact R4037
  · exact R4039
  · exact R4041
  · exact R4043
  · exact R4045
  · exact R4047
  · exact R4049
  · exact R4051
  · exact R4053
  · exact R4055
  · exact R4057
  · exact R4059
  · exact R4061
  · exact R4063
  · exact R4065
  · exact R4067
  · exact R4069
  · exact R4071
  · exact R4073
  · exact R4075
  · exact R4077
  · exact R4079
  · exact R4081
  · exact R4083
  · exact R4085
  · exact R4087
  · exact R4089
  · exact R4091
  · exact R4093
  · exact R4095
  · exact R4097
  · exact R4099
  · exact R4101
  · exact R4103
  · exact R4105
  · exact R4107
  · exact R4109
  · exact R4111
  · exact R4113
  · exact R4115
  · exact R4117
  · exact R4119
  · exact R4121
  · exact R4123
  · exact R4125
  · exact R4127
  · exact R4129
  · exact R4131
  · exact R4133
  · exact R4135
  · exact R4137
  · exact R4139
  · exact R4141
  · exact R4143
  · exact R4145
  · exact R4147
  · exact R4149
  · exact R4151
  · exact R4153
  · exact R4155
  · exact R4157
  · exact R4159
  · exact R4161
  · exact R4163
  · exact R4165
  · exact R4167
  · exact R4169
  · exact R4171
  · exact R4173
  · exact R4175
  · exact R4177
  · exact R4179
  · exact R4181
  · exact R4183
  · exact R4185
  · exact R4187
  · exact R4189
  · exact R4191
  · exact R4193
  · exact R4195
  · exact R4197
  · exact R4199
  · exact R4201
  · exact R4203
  · exact R4205
  · exact R4207
  · exact R4209
  · exact R4211
  · exact R4213
  · exact R4215
  · exact R4217
  · exact R4219
  · exact R4221
  · exact R4223
  · exact R4225
  · exact R4227
  · exact R4229
  · exact R4231
  · exact R4233
  · exact R4235
  · exact R4237
  · exact R4239
  · exact R4241
  · exact R4243
  · exact R4245
  · exact R4247
  · exact R4249
  · exact R4251
  · exact R4253
  · exact R4255
  · exact R4257
  · exact R4259
  · exact R4261
  · exact R4263
  · exact R4265
  · exact R4267
  · exact R4269
  · exact R4271
  · exact R4273
  · exact R4275
  · exact R4277
  · exact R4279
  · exact R4281
  · exact R4283
  · exact R4285
  · exact R4287
  · exact R4289
  · exact R4291
  · exact R4293
  · exact R4295
  · exact R4297
  · exact R4299
  · exact R4301
  · exact R4303
  · exact R4305
  · exact R4307
  · exact R4309
  · exact R4311
  · exact R4313
  · exact R4315
  · exact R4317
  · exact R4319
  · exact R4321
  · exact R4323
  · exact R4325
  · exact R4327
  · exact R4329
  · exact R4331
  · exact R4333
  · exact R4335
  · exact R4337
  · exact R4339
  · exact R4341
  · exact R4343
  · exact R4345
  · exact R4347
  · exact R4349
  · exact R4351
  · exact R4353
  · exact R4355
  · exact R4357
  · exact R4359
  · exact R4361
  · exact R4363
  · exact R4365
  · exact R4367
  · exact R4369
  · exact R4371
  · exact R4373
  · exact R4375
  · exact R4377
  · exact R4379
  · exact R4381
  · exact R4383
  · exact R4385
  · exact R4387
  · exact R4389
  · exact R4391
  · exact R4393
  · exact R4395
  · exact R4397
  · exact R4399
  · exact R4401
  · exact R4403
  · exact R4405
  · exact R4407
  · exact R4409
  · exact R4411
  · exact R4413
  · exact R4415
  · exact R4417
  · exact R4419
  · exact R4421
  · exact R4423
  · exact R4425
  · exact R4427
  · exact R4429
  · exact R4431
  · exact R4433
  · exact R4435
  · exact R4437
  · exact R4439
  · exact R4441
  · exact R4443
  · exact R4445
  · exact R4447
  · exact R4449
  · exact R4451
  · exact R4453
  · exact R4455
  · exact R4457
  · exact R4459
  · exact R4461
  · exact R4463
  · exact R4465
  · exact R4467
  · exact R4469
  · exact R4471
  · exact R4473
  · exact R4475
  · exact R4477
  · exact R4479
  · exact R4481
  · exact R4483
  · exact R4485
  · exact R4487
  · exact R4489
  · exact R4491
  · exact R4493
  · exact R4495
  · exact R4497
  · exact R4499
  · exact R4501
  · exact R4503
  · exact R4505
  · exact R4507
  · exact R4509
  · exact R4511
  · exact R4513
  · exact R4515
  · exact R4517
  · exact R4519
  · exact R4521
  · exact R4523
  · exact R4525
  · exact R4527
  · exact R4529
  · exact R4531
  · exact R4533
  · exact R4535
  · exact R4537
  · exact R4539
  · exact R4541
  · exact R4543
  · exact R4545
  · exact R4547
  · exact R4549
  · exact R4551
  · exact R4553
  · exact R4555
  · exact R4557
  · exact R4559
  · exact R4561
  · exact R4563
  · exact R4565
  · exact R4567
  · exact R4569
  · exact R4571
  · exact R4573
  · exact R4575
  · exact R4577
  · exact R4579
  · exact R4581
  · exact R4583
  · exact R4585
  · exact R4587
  · exact R4589
  · exact R4591
  · exact R4593
  · exact R4595
  · exact R4597
  · exact R4599
  · exact R4601
  · exact R4603
  · exact R4605
  · exact R4607
  · exact R4609
  · exact R4611
  · exact R4613
  · exact R4615
  · exact R4617
  · exact R4619
  · exact R4621
  · exact R4623
  · exact R4625
  · exact R4627
  · exact R4629
  · exact R4631
  · exact R4633
  · exact R4635
  · exact R4637
  · exact R4639
  · exact R4641
  · exact R4643
  · exact R4645
  · exact R4647
  · exact R4649
  · exact R4651
  · exact R4653
  · exact R4655
  · exact R4657
  · exact R4659
  · exact R4661
  · exact R4663
  · exact R4665
  · exact R4667
  · exact R4669
  · exact R4671
  · exact R4673
  · exact R4675
  · exact R4677
  · exact R4679
  · exact R4681
  · exact R4683
  · exact R4685
  · exact R4687
  · exact R4689
  · exact R4691
  · exact R4693
  · exact R4695
  · exact R4697
  · exact R4699
  · exact R4701
  · exact R4703
  · exact R4705
  · exact R4707
  · exact R4709
  · exact R4711
  · exact R4713
  · exact R4715
  · exact R4717
  · exact R4719
  · exact R4721
  · exact R4723
  · exact R4725
  · exact R4727
  · exact R4729
  · exact R4731
  · exact R4733
  · exact R4735
  · exact R4737
  · exact R4739
  · exact R4741
  · exact R4743
  · exact R4745
  · exact R4747
  · exact R4749
  · exact R4751
  · exact R4753
  · exact R4755
  · exact R4757
  · exact R4759
  · exact R4761
  · exact R4763
  · exact R4765
  · exact R4767
  · exact R4769
  · exact R4771
  · exact R4773
  · exact R4775
  · exact R4777
  · exact R4779
  · exact R4781
  · exact R4783
  · exact R4785
  · exact R4787
  · exact R4789
  · exact R4791
  · exact R4793
  · exact R4795
  · exact R4797
  · exact R4799
  · exact R4801
  · exact R4803
  · exact R4805
  · exact R4807
  · exact R4809
  · exact R4811
  · exact R4813
  · exact R4815
  · exact R4817
  · exact R4819
  · exact R4821
  · exact R4823
  · exact R4825
  · exact R4827
  · exact R4829
  · exact R4831
  · exact R4833
  · exact R4835
  · exact R4837
  · exact R4839
  · exact R4841
  · exact R4843
  · exact R4845
  · exact R4847
  · exact R4849
  · exact R4851
  · exact R4853
  · exact R4855
  · exact R4857
  · exact R4859
  · exact R4861
  · exact R4863
  · exact R4865
  · exact R4867
  · exact R4869
  · exact R4871
  · exact R4873
  · exact R4875
  · exact R4877
  · exact R4879
  · exact R4881
  · exact R4883
  · exact R4885
  · exact R4887
  · exact R4889
  · exact R4891
  · exact R4893
  · exact R4895
  · exact R4897
  · exact R4899
  · exact R4901
  · exact R4903
  · exact R4905
  · exact R4907
  · exact R4909
  · exact R4911
  · exact R4913
  · exact R4915
  · exact R4917
  · exact R4919
  · exact R4921
  · exact R4923
  · exact R4925
  · exact R4927
  · exact R4929
  · exact R4931
  · exact R4933
  · exact R4935
  · exact R4937
  · exact R4939
  · exact R4941
  · exact R4943
  · exact R4945
  · exact R4947
  · exact R4949
  · exact R4951
  · exact R4953
  · exact R4955
  · exact R4957
  · exact R4959
  · exact R4961
  · exact R4963
  · exact R4965
  · exact R4967
  · exact R4969
  · exact R4971
  · exact R4973
  · exact R4975
  · exact R4977
  · exact R4979
  · exact R4981
  · exact R4983
  · exact R4985
  · exact R4987
  · exact R4989
  · exact R4991
  · exact R4993
  · exact R4995
  · exact R4997
  · exact R4999
  · exact R5001
  · exact R5003
  · exact R5005
  · exact R5007
  · exact R5009
  · exact R5011
  · exact R5013
  · exact R5015
  · exact R5017
  · exact R5019
  · exact R5021
  · exact R5023
  · exact R5025
  · exact R5027
  · exact R5029
  · exact R5031
  · exact R5033
  · exact R5035
  · exact R5037
  · exact R5039
  · exact R5041
  · exact R5043
  · exact R5045
  · exact R5047
  · exact R5049
  · exact R5051
  · exact R5053
  · exact R5055
  · exact R5057
  · exact R5059
  · exact R5061
  · exact R5063
  · exact R5065
  · exact R5067
  · exact R5069
  · exact R5071
  · exact R5073
  · exact R5075
  · exact R5077
  · exact R5079
  · exact R5081
  · exact R5083
  · exact R5085
  · exact R5087
  · exact R5089
  · exact R5091
  · exact R5093
  · exact R5095
  · exact R5097
  · exact R5099
  · exact R5101
  · exact R5103
  · exact R5105
  · exact R5107
  · exact R5109
  · exact R5111
  · exact R5113
  · exact R5115
  · exact R5117
  · exact R5119
  · exact R5121
  · exact R5123
  · exact R5125
  · exact R5127
  · exact R5129
  · exact R5131
  · exact R5133
  · exact R5135
  · exact R5137
  · exact R5139
  · exact R5141
  · exact R5143
  · exact R5145
  · exact R5147
  · exact R5149
  · exact R5151
  · exact R5153
  · exact R5155
  · exact R5157
  · exact R5159
  · exact R5161
  · exact R5163
  · exact R5165
  · exact R5167
  · exact R5169
  · exact R5171
  · exact R5173
  · exact R5175
  · exact R5177
  · exact R5179
  · exact R5181
  · exact R5183
  · exact R5185
  · exact R5187
  · exact R5189
  · exact R5191
  · exact R5193
  · exact R5195
  · exact R5197
  · exact R5199
  · exact R5201
  · exact R5203
  · exact R5205
  · exact R5207
  · exact R5209
  · exact R5211
  · exact R5213
  · exact R5215
  · exact R5217
  · exact R5219
  · exact R5221
  · exact R5223
  · exact R5225
  · exact R5227
  · exact R5229
  · exact R5231
  · exact R5233
  · exact R5235
  · exact R5237
  · exact R5239
  · exact R5241
  · exact R5243
  · exact R5245
  · exact R5247
  · exact R5249
  · exact R5251
  · exact R5253
  · exact R5255
  · exact R5257
  · exact R5259
  · exact R5261
  · exact R5263
  · exact R5265
  · exact R5267
  · exact R5269
  · exact R5271
  · exact R5273
  · exact R5275
  · exact R5277
  · exact R5279
  · exact R5281
  · exact R5283
  · exact R5285
  · exact R5287
  · exact R5289
  · exact R5291
  · exact R5293
  · exact R5295
  · exact R5297
  · exact R5299
  · exact R5301
  · exact R5303
  · exact R5305
  · exact R5307
  · exact R5309
  · exact R5311
  · exact R5313
  · exact R5315
  · exact R5317
  · exact R5319
  · exact R5321
  · exact R5323
  · exact R5325
  · exact R5327
  · exact R5329
  · exact R5331
  · exact R5333
  · exact R5335
  · exact R5337
  · exact R5339
  · exact R5341
  · exact R5343
  · exact R5345
  · exact R5347
  · exact R5349
  · exact R5351
  · exact R5353
  · exact R5355
  · exact R5357
  · exact R5359
  · exact R5361
  · exact R5363
  · exact R5365
  · exact R5367
  · exact R5369
  · exact R5371
  · exact R5373
  · exact R5375
  · exact R5377
  · exact R5379
  · exact R5381
  · exact R5383
  · exact R5385
  · exact R5387
  · exact R5389
  · exact R5391
  · exact R5393
  · exact R5395
  · exact R5397
  · exact R5399
  · exact R5401
  · exact R5403
  · exact R5405
  · exact R5407
  · exact R5409
  · exact R5411
  · exact R5413
  · exact R5415
  · exact R5417
  · exact R5419
  · exact R5421
  · exact R5423
  · exact R5425
  · exact R5427
  · exact R5429
  · exact R5431
  · exact R5433
  · exact R5435
  · exact R5437
  · exact R5439
  · exact R5441
  · exact R5443
  · exact R5445
  · exact R5447
  · exact R5449
  · exact R5451
  · exact R5453
  · exact R5455
  · exact R5457
  · exact R5459
  · exact R5461
  · exact R5463
  · exact R5465
  · exact R5467
  · exact R5469
  · exact R5471
  · exact R5473
  · exact R5475
  · exact R5477
  · exact R5479
  · exact R5481
  · exact R5483
  · exact R5485
  · exact R5487
  · exact R5489
  · exact R5491
  · exact R5493
  · exact R5495
  · exact R5497
  · exact R5499
  · exact R5501
  · exact R5503
  · exact R5505
  · exact R5507
  · exact R5509
  · exact R5511
  · exact R5513
  · exact R5515
  · exact R5517
  · exact R5519
  · exact R5521
  · exact R5523
  · exact R5525
  · exact R5527
  · exact R5529
  · exact R5531
  · exact R5533
  · exact R5535
  · exact R5537
  · exact R5539
  · exact R5541
  · exact R5543
  · exact R5545
  · exact R5547
  · exact R5549
  · exact R5551
  · exact R5553
  · exact R5555
  · exact R5557
  · exact R5559
  · exact R5561
  · exact R5563
  · exact R5565
  · exact R5567
  · exact R5569
  · exact R5571
  · exact R5573
  · exact R5575
  · exact R5577
  · exact R5579
  · exact R5581
  · exact R5583
  · exact R5585
  · exact R5587
  · exact R5589
  · exact R5591
  · exact R5593
  · exact R5595
  · exact R5597
  · exact R5599
  · exact R5601
  · exact R5603
  · exact R5605
  · exact R5607
  · exact R5609
  · exact R5611
  · exact R5613
  · exact R5615
  · exact R5617
  · exact R5619
  · exact R5621
  · exact R5623
  · exact R5625
  · exact R5627
  · exact R5629
  · exact R5631
  · exact R5633
  · exact R5635
  · exact R5637
  · exact R5639
  · exact R5641
  · exact R5643
  · exact R5645
  · exact R5647
  · exact R5649
  · exact R5651
  · exact R5653
  · exact R5655
  · exact R5657
  · exact R5659
  · exact R5661
  · exact R5663
  · exact R5665
  · exact R5667
  · exact R5669
  · exact R5671
  · exact R5673
  · exact R5675
  · exact R5677
  · exact R5679
  · exact R5681
  · exact R5683
  · exact R5685
  · exact R5687
  · exact R5689
  · exact R5691
  · exact R5693
  · exact R5695
  · exact R5697
  · exact R5699
  · exact R5701
  · exact R5703
  · exact R5705
  · exact R5707
  · exact R5709
  · exact R5711
  · exact R5713
  · exact R5715
  · exact R5717
  · exact R5719
  · exact R5721
  · exact R5723
  · exact R5725
  · exact R5727
  · exact R5729
  · exact R5731
  · exact R5733
  · exact R5735
  · exact R5737
  · exact R5739
  · exact R5741
  · exact R5743
  · exact R5745
  · exact R5747
  · exact R5749
  · exact R5751
  · exact R5753
  · exact R5755
  · exact R5757
  · exact R5759
  · exact R5761
  · exact R5763
  · exact R5765
  · exact R5767
  · exact R5769
  · exact R5771
  · exact R5773
  · exact R5775
  · exact R5777
  · exact R5779
  · exact R5781
  · exact R5783
  · exact R5785
  · exact R5787
  · exact R5789
  · exact R5791
  · exact R5793
  · exact R5795
  · exact R5797
  · exact R5799
  · exact R5801
  · exact R5803
  · exact R5805
  · exact R5807
  · exact R5809
  · exact R5811
  · exact R5813
  · exact R5815
  · exact R5817
  · exact R5819
  · exact R5821
  · exact R5823
  · exact R5825
  · exact R5827
  · exact R5829
  · exact R5831
  · exact R5833
  · exact R5835
  · exact R5837
  · exact R5839
  · exact R5841
  · exact R5843
  · exact R5845
  · exact R5847
  · exact R5849
  · exact R5851
  · exact R5853
  · exact R5855
  · exact R5857
  · exact R5859
  · exact R5861
  · exact R5863
  · exact R5865
  · exact R5867
  · exact R5869
  · exact R5871
  · exact R5873
  · exact R5875
  · exact R5877
  · exact R5879
  · exact R5881
  · exact R5883
  · exact R5885
  · exact R5887
  · exact R5889
  · exact R5891
  · exact R5893
  · exact R5895
  · exact R5897
  · exact R5899
  · exact R5901
  · exact R5903
  · exact R5905
  · exact R5907
  · exact R5909
  · exact R5911
  · exact R5913
  · exact R5915
  · exact R5917
  · exact R5919
  · exact R5921
  · exact R5923
  · exact R5925
  · exact R5927
  · exact R5929
  · exact R5931
  · exact R5933
  · exact R5935
  · exact R5937
  · exact R5939
  · exact R5941
  · exact R5943
  · exact R5945
  · exact R5947
  · exact R5949
  · exact R5951
  · exact R5953
  · exact R5955
  · exact R5957
  · exact R5959
  · exact R5961
  · exact R5963
  · exact R5965
  · exact R5967
  · exact R5969
  · exact R5971
  · exact R5973
  · exact R5975
  · exact R5977
  · exact R5979
  · exact R5981
  · exact R5983
  · exact R5985
  · exact R5987
  · exact R5989
  · exact R5991
  · exact R5993
  · exact R5995
  · exact R5997
  · exact R5999
  · exact R6001
  · exact R6003
  · exact R6005
  · exact R6007
  · exact R6009
  · exact R6011
  · exact R6013
  · exact R6015
  · exact R6017
  · exact R6019
  · exact R6021
  · exact R6023
  · exact R6025
  · exact R6027
  · exact R6029
  · exact R6031
  · exact R6033
  · exact R6035
  · exact R6037
  · exact R6039
  · exact R6041
  · exact R6043
  · exact R6045
  · exact R6047
  · exact R6049
  · exact R6051
  · exact R6053
  · exact R6055
  · exact R6057
  · exact R6059
  · exact R6061
  · exact R6063
  · exact R6065
  · exact R6067
  · exact R6069
  · exact R6071
  · exact R6073
  · exact R6075
  · exact R6077
  · exact R6079
  · exact R6081
  · exact R6083
  · exact R6085
  · exact R6087
  · exact R6089
  · exact R6091
  · exact R6093
  · exact R6095
  · exact R6097
  · exact R6099
  · exact R6101
  · exact R6103
  · exact R6105
  · exact R6107
  · exact R6109
  · exact R6111
  · exact R6113
  · exact R6115
  · exact R6117
  · exact R6119
  · exact R6121
  · exact R6123
  · exact R6125
  · exact R6127
  · exact R6129
  · exact R6131
  · exact R6133
  · exact R6135
  · exact R6137
  · exact R6139
  · exact R6141
  · exact R6143
  · exact R6145
  · exact R6147
  · exact R6149
  · exact R6151
  · exact R6153
  · exact R6155
  · exact R6157
  · exact R6159
  · exact R6161
  · exact R6163
  · exact R6165
  · exact R6167
  · exact R6169
  · exact R6171
  · exact R6173
  · exact R6175
  · exact R6177
  · exact R6179
  · exact R6181
  · exact R6183
  · exact R6185
  · exact R6187
  · exact R6189
  · exact R6191
  · exact R6193
  · exact R6195
  · exact R6197
  · exact R6199
  · exact R6201
  · exact R6203
  · exact R6205
  · exact R6207
  · exact R6209
  · exact R6211
  · exact R6213
  · exact R6215
  · exact R6217
  · exact R6219
  · exact R6221
  · exact R6223
  · exact R6225
  · exact R6227
  · exact R6229
  · exact R6231
  · exact R6233
  · exact R6235
  · exact R6237
  · exact R6239
  · exact R6241
  · exact R6243
  · exact R6245
  · exact R6247
  · exact R6249
  · exact R6251
  · exact R6253
  · exact R6255
  · exact R6257
  · exact R6259
  · exact R6261
  · exact R6263
  · exact R6265
  · exact R6267
  · exact R6269
  · exact R6271
  · exact R6273
  · exact R6275
  · exact R6277
  · exact R6279
  · exact R6281
  · exact R6283
  · exact R6285
  · exact R6287
  · exact R6289
  · exact R6291
  · exact R6293
  · exact R6295
  · exact R6297
  · exact R6299
  · exact R6301
  · exact R6303
  · exact R6305
  · exact R6307
  · exact R6309
  · exact R6311
  · exact R6313
  · exact R6315
  · exact R6317
  · exact R6319
  · exact R6321
  · exact R6323
  · exact R6325
  · exact R6327
  · exact R6329
  · exact R6331
  · exact R6333
  · exact R6335
  · exact R6337
  · exact R6339
  · exact R6341
  · exact R6343
  · exact R6345
  · exact R6347
  · exact R6349
  · exact R6351
  · exact R6353
  · exact R6355
  · exact R6357
  · exact R6359
  · exact R6361
  · exact R6363
  · exact R6365
  · exact R6367
  · exact R6369
  · exact R6371
  · exact R6373
  · exact R6375
  · exact R6377
  · exact R6379
  · exact R6381
  · exact R6383
  · exact R6385
  · exact R6387
  · exact R6389
  · exact R6391
  · exact R6393
  · exact R6395
  · exact R6397
  · exact R6399
  · exact R6401
  · exact R6403
  · exact R6405
  · exact R6407
  · exact R6409
  · exact R6411
  · exact R6413
  · exact R6415
  · exact R6417
  · exact R6419
  · exact R6421
  · exact R6423
  · exact R6425
  · exact R6427
  · exact R6429
  · exact R6431
  · exact R6433
  · exact R6435
  · exact R6437
  · exact R6439
  · exact R6441
  · exact R6443
  · exact R6445
  · exact R6447
  · exact R6449
  · exact R6451
  · exact R6453
  · exact R6455
  · exact R6457
  · exact R6459
  · exact R6461
  · exact R6463
  · exact R6465
  · exact R6467
  · exact R6469
  · exact R6471
  · exact R6473
  · exact R6475
  · exact R6477
  · exact R6479
  · exact R6481
  · exact R6483
  · exact R6485
  · exact R6487
  · exact R6489
  · exact R6491
  · exact R6493
  · exact R6495
  · exact R6497
  · exact R6499
  · exact R6501
  · exact R6503
  · exact R6505
  · exact R6507
  · exact R6509
  · exact R6511
  · exact R6513
  · exact R6515
  · exact R6517
  · exact R6519
  · exact R6521
  · exact R6523
  · exact R6525
  · exact R6527
  · exact R6529
  · exact R6531
  · exact R6533
  · exact R6535
  · exact R6537
  · exact R6539
  · exact R6541
  · exact R6543
  · exact R6545
  · exact R6547
  · exact R6549
  · exact R6551
  · exact R6553
  · exact R6555
  · exact R6557
  · exact R6559
  · exact R6561
  · exact R6563
  · exact R6565
  · exact R6567
  · exact R6569
  · exact R6571
  · exact R6573
  · exact R6575
  · exact R6577
  · exact R6579
  · exact R6581
  · exact R6583
  · exact R6585
  · exact R6587
  · exact R6589
  · exact R6591
  · exact R6593
  · exact R6595
  · exact R6597
  · exact R6599
  · exact R6601
  · exact R6603
  · exact R6605
  · exact R6607
  · exact R6609
  · exact R6611
  · exact R6613
  · exact R6615
  · exact R6617
  · exact R6619
  · exact R6621
  · exact R6623
  · exact R6625
  · exact R6627
  · exact R6629
  · exact R6631
  · exact R6633
  · exact R6635
  · exact R6637
  · exact R6639
  · exact R6641
  · exact R6643
  · exact R6645
  · exact R6647
  · exact R6649
  · exact R6651
  · exact R6653
  · exact R6655
  · exact R6657
  · exact R6659
  · exact R6661
  · exact R6663
  · exact R6665
  · exact R6667
  · exact R6669
  · exact R6671
  · exact R6673
  · exact R6675
  · exact R6677
  · exact R6679
  · exact R6681
  · exact R6683
  · exact R6685
  · exact R6687
  · exact R6689
  · exact R6691
  · exact R6693
  · exact R6695
  · exact R6697
  · exact R6699
  · exact R6701
  · exact R6703
  · exact R6705
  · exact R6707
  · exact R6709
  · exact R6711
  · exact R6713
  · exact R6715
  · exact R6717
  · exact R6719
  · exact R6721
  · exact R6723
