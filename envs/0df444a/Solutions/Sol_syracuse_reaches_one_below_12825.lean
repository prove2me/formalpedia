-- Prove2me | solution 1 for syracuse_reaches_one_below_12825
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T04:26:32.666984+00:00
-- url     : https://prove2.me/submissions/e424a946-e148-4d93-88f8-0a25cf8553e1

import Mathlib
import Definitions.Def_syracuseStep

set_option maxHeartbeats 1000000

open Nat

abbrev Reach (n : ℕ) : Prop := ∃ j : ℕ, syracuseStep^[j] n = 1

theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]

theorem rs {x y : ℕ} (h : syracuseStep x = y) (hy : Reach y) : Reach x := by
  obtain ⟨j, hj⟩ := hy
  exact ⟨j + 1, by rw [Function.iterate_add_apply, Function.iterate_one, h]; exact hj⟩

theorem R1 : Reach 1 := ⟨0, rfl⟩
theorem R5 : Reach 5 := rs (se 4 (by rfl) ⟨0, by rfl⟩) R1
theorem R21 : Reach 21 := rs (se 6 (by rfl) ⟨0, by rfl⟩) R1
theorem R85 : Reach 85 := rs (se 8 (by rfl) ⟨0, by rfl⟩) R1
theorem R341 : Reach 341 := rs (se 10 (by rfl) ⟨0, by rfl⟩) R1
theorem R1365 : Reach 1365 := rs (se 12 (by rfl) ⟨0, by rfl⟩) R1
theorem R5461 : Reach 5461 := rs (se 14 (by rfl) ⟨0, by rfl⟩) R1
theorem R3 : Reach 3 := rs (se 1 (by rfl) ⟨2, by rfl⟩) R5
theorem R13 : Reach 13 := rs (se 3 (by rfl) ⟨2, by rfl⟩) R5
theorem R53 : Reach 53 := rs (se 5 (by rfl) ⟨2, by rfl⟩) R5
theorem R113 : Reach 113 := rs (se 2 (by rfl) ⟨42, by rfl⟩) R85
theorem R213 : Reach 213 := rs (se 7 (by rfl) ⟨2, by rfl⟩) R5
theorem R227 : Reach 227 := rs (se 1 (by rfl) ⟨170, by rfl⟩) R341
theorem R453 : Reach 453 := rs (se 4 (by rfl) ⟨42, by rfl⟩) R85
theorem R853 : Reach 853 := rs (se 9 (by rfl) ⟨2, by rfl⟩) R5
theorem R909 : Reach 909 := rs (se 3 (by rfl) ⟨170, by rfl⟩) R341
theorem R1813 : Reach 1813 := rs (se 6 (by rfl) ⟨42, by rfl⟩) R85
theorem R3413 : Reach 3413 := rs (se 11 (by rfl) ⟨2, by rfl⟩) R5
theorem R3637 : Reach 3637 := rs (se 5 (by rfl) ⟨170, by rfl⟩) R341
theorem R7253 : Reach 7253 := rs (se 8 (by rfl) ⟨42, by rfl⟩) R85
theorem R7281 : Reach 7281 := rs (se 2 (by rfl) ⟨2730, by rfl⟩) R5461
theorem R14549 : Reach 14549 := rs (se 7 (by rfl) ⟨170, by rfl⟩) R341
theorem R17 : Reach 17 := rs (se 2 (by rfl) ⟨6, by rfl⟩) R13
theorem R35 : Reach 35 := rs (se 1 (by rfl) ⟨26, by rfl⟩) R53
theorem R69 : Reach 69 := rs (se 4 (by rfl) ⟨6, by rfl⟩) R13
theorem R75 : Reach 75 := rs (se 1 (by rfl) ⟨56, by rfl⟩) R113
theorem R141 : Reach 141 := rs (se 3 (by rfl) ⟨26, by rfl⟩) R53
theorem R151 : Reach 151 := rs (se 1 (by rfl) ⟨113, by rfl⟩) R227
theorem R277 : Reach 277 := rs (se 6 (by rfl) ⟨6, by rfl⟩) R13
theorem R301 : Reach 301 := rs (se 3 (by rfl) ⟨56, by rfl⟩) R113
theorem R565 : Reach 565 := rs (se 5 (by rfl) ⟨26, by rfl⟩) R53
theorem R605 : Reach 605 := rs (se 3 (by rfl) ⟨113, by rfl⟩) R227
theorem R1109 : Reach 1109 := rs (se 8 (by rfl) ⟨6, by rfl⟩) R13
theorem R1137 : Reach 1137 := rs (se 2 (by rfl) ⟨426, by rfl⟩) R853
theorem R1205 : Reach 1205 := rs (se 5 (by rfl) ⟨56, by rfl⟩) R113
theorem R2261 : Reach 2261 := rs (se 7 (by rfl) ⟨26, by rfl⟩) R53
theorem R2275 : Reach 2275 := rs (se 1 (by rfl) ⟨1706, by rfl⟩) R3413
theorem R2417 : Reach 2417 := rs (se 2 (by rfl) ⟨906, by rfl⟩) R1813
theorem R2421 : Reach 2421 := rs (se 5 (by rfl) ⟨113, by rfl⟩) R227
theorem R4437 : Reach 4437 := rs (se 10 (by rfl) ⟨6, by rfl⟩) R13
theorem R4549 : Reach 4549 := rs (se 4 (by rfl) ⟨426, by rfl⟩) R853
theorem R4821 : Reach 4821 := rs (se 7 (by rfl) ⟨56, by rfl⟩) R113
theorem R4835 : Reach 4835 := rs (se 1 (by rfl) ⟨3626, by rfl⟩) R7253
theorem R4849 : Reach 4849 := rs (se 2 (by rfl) ⟨1818, by rfl⟩) R3637
theorem R9045 : Reach 9045 := rs (se 9 (by rfl) ⟨26, by rfl⟩) R53
theorem R9101 : Reach 9101 := rs (se 3 (by rfl) ⟨1706, by rfl⟩) R3413
theorem R9669 : Reach 9669 := rs (se 4 (by rfl) ⟨906, by rfl⟩) R1813
theorem R9685 : Reach 9685 := rs (se 7 (by rfl) ⟨113, by rfl⟩) R227
theorem R9699 : Reach 9699 := rs (se 1 (by rfl) ⟨7274, by rfl⟩) R14549
theorem R17749 : Reach 17749 := rs (se 12 (by rfl) ⟨6, by rfl⟩) R13
theorem R18197 : Reach 18197 := rs (se 6 (by rfl) ⟨426, by rfl⟩) R853
theorem R11 : Reach 11 := rs (se 1 (by rfl) ⟨8, by rfl⟩) R17
theorem R23 : Reach 23 := rs (se 1 (by rfl) ⟨17, by rfl⟩) R35
theorem R45 : Reach 45 := rs (se 3 (by rfl) ⟨8, by rfl⟩) R17
theorem R93 : Reach 93 := rs (se 3 (by rfl) ⟨17, by rfl⟩) R35
theorem R181 : Reach 181 := rs (se 5 (by rfl) ⟨8, by rfl⟩) R17
theorem R201 : Reach 201 := rs (se 2 (by rfl) ⟨75, by rfl⟩) R151
theorem R369 : Reach 369 := rs (se 2 (by rfl) ⟨138, by rfl⟩) R277
theorem R373 : Reach 373 := rs (se 5 (by rfl) ⟨17, by rfl⟩) R35
theorem R401 : Reach 401 := rs (se 2 (by rfl) ⟨150, by rfl⟩) R301
theorem R403 : Reach 403 := rs (se 1 (by rfl) ⟨302, by rfl⟩) R605
theorem R725 : Reach 725 := rs (se 7 (by rfl) ⟨8, by rfl⟩) R17
theorem R739 : Reach 739 := rs (se 1 (by rfl) ⟨554, by rfl⟩) R1109
theorem R753 : Reach 753 := rs (se 2 (by rfl) ⟨282, by rfl⟩) R565
theorem R803 : Reach 803 := rs (se 1 (by rfl) ⟨602, by rfl⟩) R1205
theorem R805 : Reach 805 := rs (se 4 (by rfl) ⟨75, by rfl⟩) R151
theorem R1477 : Reach 1477 := rs (se 4 (by rfl) ⟨138, by rfl⟩) R277
theorem R1493 : Reach 1493 := rs (se 7 (by rfl) ⟨17, by rfl⟩) R35
theorem R1507 : Reach 1507 := rs (se 1 (by rfl) ⟨1130, by rfl⟩) R2261
theorem R1605 : Reach 1605 := rs (se 4 (by rfl) ⟨150, by rfl⟩) R301
theorem R1611 : Reach 1611 := rs (se 1 (by rfl) ⟨1208, by rfl⟩) R2417
theorem R1613 : Reach 1613 := rs (se 3 (by rfl) ⟨302, by rfl⟩) R605
theorem R2901 : Reach 2901 := rs (se 9 (by rfl) ⟨8, by rfl⟩) R17
theorem R2957 : Reach 2957 := rs (se 3 (by rfl) ⟨554, by rfl⟩) R1109
theorem R3013 : Reach 3013 := rs (se 4 (by rfl) ⟨282, by rfl⟩) R565
theorem R3033 : Reach 3033 := rs (se 2 (by rfl) ⟨1137, by rfl⟩) R2275
theorem R3213 : Reach 3213 := rs (se 3 (by rfl) ⟨602, by rfl⟩) R1205
theorem R3221 : Reach 3221 := rs (se 6 (by rfl) ⟨75, by rfl⟩) R151
theorem R3223 : Reach 3223 := rs (se 1 (by rfl) ⟨2417, by rfl⟩) R4835
theorem R5909 : Reach 5909 := rs (se 6 (by rfl) ⟨138, by rfl⟩) R277
theorem R5973 : Reach 5973 := rs (se 9 (by rfl) ⟨17, by rfl⟩) R35
theorem R6029 : Reach 6029 := rs (se 3 (by rfl) ⟨1130, by rfl⟩) R2261
theorem R6065 : Reach 6065 := rs (se 2 (by rfl) ⟨2274, by rfl⟩) R4549
theorem R6067 : Reach 6067 := rs (se 1 (by rfl) ⟨4550, by rfl⟩) R9101
theorem R6421 : Reach 6421 := rs (se 6 (by rfl) ⟨150, by rfl⟩) R301
theorem R6445 : Reach 6445 := rs (se 3 (by rfl) ⟨1208, by rfl⟩) R2417
theorem R6453 : Reach 6453 := rs (se 5 (by rfl) ⟨302, by rfl⟩) R605
theorem R6465 : Reach 6465 := rs (se 2 (by rfl) ⟨2424, by rfl⟩) R4849
theorem R11605 : Reach 11605 := rs (se 11 (by rfl) ⟨8, by rfl⟩) R17
theorem R11829 : Reach 11829 := rs (se 5 (by rfl) ⟨554, by rfl⟩) R1109
theorem R12053 : Reach 12053 := rs (se 6 (by rfl) ⟨282, by rfl⟩) R565
theorem R12131 : Reach 12131 := rs (se 1 (by rfl) ⟨9098, by rfl⟩) R18197
theorem R12133 : Reach 12133 := rs (se 4 (by rfl) ⟨1137, by rfl⟩) R2275
theorem R12893 : Reach 12893 := rs (se 3 (by rfl) ⟨2417, by rfl⟩) R4835
theorem R47317 : Reach 47317 := rs (se 7 (by rfl) ⟨554, by rfl⟩) R1109
theorem R23665 : Reach 23665 := rs (se 2 (by rfl) ⟨8874, by rfl⟩) R17749
theorem R25685 : Reach 25685 := rs (se 8 (by rfl) ⟨150, by rfl⟩) R301
theorem R7 : Reach 7 := rs (se 1 (by rfl) ⟨5, by rfl⟩) R11
theorem R15 : Reach 15 := rs (se 1 (by rfl) ⟨11, by rfl⟩) R23
theorem R29 : Reach 29 := rs (se 3 (by rfl) ⟨5, by rfl⟩) R11
theorem R61 : Reach 61 := rs (se 3 (by rfl) ⟨11, by rfl⟩) R23
theorem R117 : Reach 117 := rs (se 5 (by rfl) ⟨5, by rfl⟩) R11
theorem R241 : Reach 241 := rs (se 2 (by rfl) ⟨90, by rfl⟩) R181
theorem R245 : Reach 245 := rs (se 5 (by rfl) ⟨11, by rfl⟩) R23
theorem R267 : Reach 267 := rs (se 1 (by rfl) ⟨200, by rfl⟩) R401
theorem R469 : Reach 469 := rs (se 7 (by rfl) ⟨5, by rfl⟩) R11
theorem R483 : Reach 483 := rs (se 1 (by rfl) ⟨362, by rfl⟩) R725
theorem R497 : Reach 497 := rs (se 2 (by rfl) ⟨186, by rfl⟩) R373
theorem R535 : Reach 535 := rs (se 1 (by rfl) ⟨401, by rfl⟩) R803
theorem R537 : Reach 537 := rs (se 2 (by rfl) ⟨201, by rfl⟩) R403
theorem R965 : Reach 965 := rs (se 4 (by rfl) ⟨90, by rfl⟩) R181
theorem R981 : Reach 981 := rs (se 7 (by rfl) ⟨11, by rfl⟩) R23
theorem R985 : Reach 985 := rs (se 2 (by rfl) ⟨369, by rfl⟩) R739
theorem R995 : Reach 995 := rs (se 1 (by rfl) ⟨746, by rfl⟩) R1493
theorem R1069 : Reach 1069 := rs (se 3 (by rfl) ⟨200, by rfl⟩) R401
theorem R1073 : Reach 1073 := rs (se 2 (by rfl) ⟨402, by rfl⟩) R805
theorem R1075 : Reach 1075 := rs (se 1 (by rfl) ⟨806, by rfl⟩) R1613
theorem R1877 : Reach 1877 := rs (se 9 (by rfl) ⟨5, by rfl⟩) R11
theorem R1933 : Reach 1933 := rs (se 3 (by rfl) ⟨362, by rfl⟩) R725
theorem R1969 : Reach 1969 := rs (se 2 (by rfl) ⟨738, by rfl⟩) R1477
theorem R1971 : Reach 1971 := rs (se 1 (by rfl) ⟨1478, by rfl⟩) R2957
theorem R1989 : Reach 1989 := rs (se 4 (by rfl) ⟨186, by rfl⟩) R373
theorem R2009 : Reach 2009 := rs (se 2 (by rfl) ⟨753, by rfl⟩) R1507
theorem R2141 : Reach 2141 := rs (se 3 (by rfl) ⟨401, by rfl⟩) R803
theorem R2147 : Reach 2147 := rs (se 1 (by rfl) ⟨1610, by rfl⟩) R3221
theorem R2149 : Reach 2149 := rs (se 4 (by rfl) ⟨201, by rfl⟩) R403
theorem R3861 : Reach 3861 := rs (se 6 (by rfl) ⟨90, by rfl⟩) R181
theorem R3925 : Reach 3925 := rs (se 9 (by rfl) ⟨11, by rfl⟩) R23
theorem R3939 : Reach 3939 := rs (se 1 (by rfl) ⟨2954, by rfl⟩) R5909
theorem R3941 : Reach 3941 := rs (se 4 (by rfl) ⟨369, by rfl⟩) R739
theorem R3981 : Reach 3981 := rs (se 3 (by rfl) ⟨746, by rfl⟩) R1493
theorem R4017 : Reach 4017 := rs (se 2 (by rfl) ⟨1506, by rfl⟩) R3013
theorem R4019 : Reach 4019 := rs (se 1 (by rfl) ⟨3014, by rfl⟩) R6029
theorem R4043 : Reach 4043 := rs (se 1 (by rfl) ⟨3032, by rfl⟩) R6065
theorem R4277 : Reach 4277 := rs (se 5 (by rfl) ⟨200, by rfl⟩) R401
theorem R4293 : Reach 4293 := rs (se 4 (by rfl) ⟨402, by rfl⟩) R805
theorem R4297 : Reach 4297 := rs (se 2 (by rfl) ⟨1611, by rfl⟩) R3223
theorem R4301 : Reach 4301 := rs (se 3 (by rfl) ⟨806, by rfl⟩) R1613
theorem R7509 : Reach 7509 := rs (se 11 (by rfl) ⟨5, by rfl⟩) R11
theorem R7733 : Reach 7733 := rs (se 5 (by rfl) ⟨362, by rfl⟩) R725
theorem R7877 : Reach 7877 := rs (se 4 (by rfl) ⟨738, by rfl⟩) R1477
theorem R7885 : Reach 7885 := rs (se 3 (by rfl) ⟨1478, by rfl⟩) R2957
theorem R7957 : Reach 7957 := rs (se 6 (by rfl) ⟨186, by rfl⟩) R373
theorem R8035 : Reach 8035 := rs (se 1 (by rfl) ⟨6026, by rfl⟩) R12053
theorem R8037 : Reach 8037 := rs (se 4 (by rfl) ⟨753, by rfl⟩) R1507
theorem R8087 : Reach 8087 := rs (se 1 (by rfl) ⟨6065, by rfl⟩) R12131
theorem R8089 : Reach 8089 := rs (se 2 (by rfl) ⟨3033, by rfl⟩) R6067
theorem R8561 : Reach 8561 := rs (se 2 (by rfl) ⟨3210, by rfl⟩) R6421
theorem R8565 : Reach 8565 := rs (se 5 (by rfl) ⟨401, by rfl⟩) R803
theorem R8589 : Reach 8589 := rs (se 3 (by rfl) ⟨1610, by rfl⟩) R3221
theorem R8593 : Reach 8593 := rs (se 2 (by rfl) ⟨3222, by rfl⟩) R6445
theorem R8595 : Reach 8595 := rs (se 1 (by rfl) ⟨6446, by rfl⟩) R12893
theorem R8597 : Reach 8597 := rs (se 6 (by rfl) ⟨201, by rfl⟩) R403
theorem R15473 : Reach 15473 := rs (se 2 (by rfl) ⟨5802, by rfl⟩) R11605
theorem R15701 : Reach 15701 := rs (se 11 (by rfl) ⟨11, by rfl⟩) R23
theorem R17123 : Reach 17123 := rs (se 1 (by rfl) ⟨12842, by rfl⟩) R25685
theorem R17189 : Reach 17189 := rs (se 4 (by rfl) ⟨1611, by rfl⟩) R3223
theorem R120149 : Reach 120149 := rs (se 15 (by rfl) ⟨5, by rfl⟩) R11
theorem R63089 : Reach 63089 := rs (se 2 (by rfl) ⟨23658, by rfl⟩) R47317
theorem R31553 : Reach 31553 := rs (se 2 (by rfl) ⟨11832, by rfl⟩) R23665
theorem R9 : Reach 9 := rs (se 2 (by rfl) ⟨3, by rfl⟩) R7
theorem R19 : Reach 19 := rs (se 1 (by rfl) ⟨14, by rfl⟩) R29
theorem R37 : Reach 37 := rs (se 4 (by rfl) ⟨3, by rfl⟩) R7
theorem R77 : Reach 77 := rs (se 3 (by rfl) ⟨14, by rfl⟩) R29
theorem R81 : Reach 81 := rs (se 2 (by rfl) ⟨30, by rfl⟩) R61
theorem R149 : Reach 149 := rs (se 6 (by rfl) ⟨3, by rfl⟩) R7
theorem R163 : Reach 163 := rs (se 1 (by rfl) ⟨122, by rfl⟩) R245
theorem R309 : Reach 309 := rs (se 5 (by rfl) ⟨14, by rfl⟩) R29
theorem R321 : Reach 321 := rs (se 2 (by rfl) ⟨120, by rfl⟩) R241
theorem R325 : Reach 325 := rs (se 4 (by rfl) ⟨30, by rfl⟩) R61
theorem R331 : Reach 331 := rs (se 1 (by rfl) ⟨248, by rfl⟩) R497
theorem R597 : Reach 597 := rs (se 8 (by rfl) ⟨3, by rfl⟩) R7
theorem R625 : Reach 625 := rs (se 2 (by rfl) ⟨234, by rfl⟩) R469
theorem R643 : Reach 643 := rs (se 1 (by rfl) ⟨482, by rfl⟩) R965
theorem R653 : Reach 653 := rs (se 3 (by rfl) ⟨122, by rfl⟩) R245
theorem R663 : Reach 663 := rs (se 1 (by rfl) ⟨497, by rfl⟩) R995
theorem R713 : Reach 713 := rs (se 2 (by rfl) ⟨267, by rfl⟩) R535
theorem R715 : Reach 715 := rs (se 1 (by rfl) ⟨536, by rfl⟩) R1073
theorem R164693 : Reach 164693 := rs (se 9 (by rfl) ⟨482, by rfl⟩) R965
theorem R1237 : Reach 1237 := rs (se 7 (by rfl) ⟨14, by rfl⟩) R29
theorem R1251 : Reach 1251 := rs (se 1 (by rfl) ⟨938, by rfl⟩) R1877
theorem R1285 : Reach 1285 := rs (se 4 (by rfl) ⟨120, by rfl⟩) R241
theorem R1301 : Reach 1301 := rs (se 6 (by rfl) ⟨30, by rfl⟩) R61
theorem R1313 : Reach 1313 := rs (se 2 (by rfl) ⟨492, by rfl⟩) R985
theorem R1325 : Reach 1325 := rs (se 3 (by rfl) ⟨248, by rfl⟩) R497
theorem R1339 : Reach 1339 := rs (se 1 (by rfl) ⟨1004, by rfl⟩) R2009
theorem R1425 : Reach 1425 := rs (se 2 (by rfl) ⟨534, by rfl⟩) R1069
theorem R1427 : Reach 1427 := rs (se 1 (by rfl) ⟨1070, by rfl⟩) R2141
theorem R1431 : Reach 1431 := rs (se 1 (by rfl) ⟨1073, by rfl⟩) R2147
theorem R1433 : Reach 1433 := rs (se 2 (by rfl) ⟨537, by rfl⟩) R1075
theorem R2389 : Reach 2389 := rs (se 10 (by rfl) ⟨3, by rfl⟩) R7
theorem R2501 : Reach 2501 := rs (se 4 (by rfl) ⟨234, by rfl⟩) R469
theorem R2573 : Reach 2573 := rs (se 3 (by rfl) ⟨482, by rfl⟩) R965
theorem R2577 : Reach 2577 := rs (se 2 (by rfl) ⟨966, by rfl⟩) R1933
theorem R2613 : Reach 2613 := rs (se 5 (by rfl) ⟨122, by rfl⟩) R245
theorem R2625 : Reach 2625 := rs (se 2 (by rfl) ⟨984, by rfl⟩) R1969
theorem R2627 : Reach 2627 := rs (se 1 (by rfl) ⟨1970, by rfl⟩) R3941
theorem R2653 : Reach 2653 := rs (se 3 (by rfl) ⟨497, by rfl⟩) R995
theorem R2679 : Reach 2679 := rs (se 1 (by rfl) ⟨2009, by rfl⟩) R4019
theorem R2695 : Reach 2695 := rs (se 1 (by rfl) ⟨2021, by rfl⟩) R4043
theorem R2851 : Reach 2851 := rs (se 1 (by rfl) ⟨2138, by rfl⟩) R4277
theorem R2853 : Reach 2853 := rs (se 4 (by rfl) ⟨267, by rfl⟩) R535
theorem R2861 : Reach 2861 := rs (se 3 (by rfl) ⟨536, by rfl⟩) R1073
theorem R2865 : Reach 2865 := rs (se 2 (by rfl) ⟨1074, by rfl⟩) R2149
theorem R2867 : Reach 2867 := rs (se 1 (by rfl) ⟨2150, by rfl⟩) R4301
theorem R4949 : Reach 4949 := rs (se 9 (by rfl) ⟨14, by rfl⟩) R29
theorem R5005 : Reach 5005 := rs (se 3 (by rfl) ⟨938, by rfl⟩) R1877
theorem R5141 : Reach 5141 := rs (se 6 (by rfl) ⟨120, by rfl⟩) R241
theorem R5155 : Reach 5155 := rs (se 1 (by rfl) ⟨3866, by rfl⟩) R7733
theorem R5205 : Reach 5205 := rs (se 8 (by rfl) ⟨30, by rfl⟩) R61
theorem R5233 : Reach 5233 := rs (se 2 (by rfl) ⟨1962, by rfl⟩) R3925
theorem R5251 : Reach 5251 := rs (se 1 (by rfl) ⟨3938, by rfl⟩) R7877
theorem R5253 : Reach 5253 := rs (se 4 (by rfl) ⟨492, by rfl⟩) R985
theorem R5301 : Reach 5301 := rs (se 5 (by rfl) ⟨248, by rfl⟩) R497
theorem R5357 : Reach 5357 := rs (se 3 (by rfl) ⟨1004, by rfl⟩) R2009
theorem R5391 : Reach 5391 := rs (se 1 (by rfl) ⟨4043, by rfl⟩) R8087
theorem R5701 : Reach 5701 := rs (se 4 (by rfl) ⟨534, by rfl⟩) R1069
theorem R5707 : Reach 5707 := rs (se 1 (by rfl) ⟨4280, by rfl⟩) R8561
theorem R5709 : Reach 5709 := rs (se 3 (by rfl) ⟨1070, by rfl⟩) R2141
theorem R5725 : Reach 5725 := rs (se 3 (by rfl) ⟨1073, by rfl⟩) R2147
theorem R5729 : Reach 5729 := rs (se 2 (by rfl) ⟨2148, by rfl⟩) R4297
theorem R5731 : Reach 5731 := rs (se 1 (by rfl) ⟨4298, by rfl⟩) R8597
theorem R5733 : Reach 5733 := rs (se 4 (by rfl) ⟨537, by rfl⟩) R1075
theorem R42059 : Reach 42059 := rs (se 1 (by rfl) ⟨31544, by rfl⟩) R63089
theorem R9557 : Reach 9557 := rs (se 12 (by rfl) ⟨3, by rfl⟩) R7
theorem R10005 : Reach 10005 := rs (se 6 (by rfl) ⟨234, by rfl⟩) R469
theorem R10293 : Reach 10293 := rs (se 5 (by rfl) ⟨482, by rfl⟩) R965
theorem R10309 : Reach 10309 := rs (se 4 (by rfl) ⟨966, by rfl⟩) R1933
theorem R10315 : Reach 10315 := rs (se 1 (by rfl) ⟨7736, by rfl⟩) R15473
theorem R10453 : Reach 10453 := rs (se 7 (by rfl) ⟨122, by rfl⟩) R245
theorem R10467 : Reach 10467 := rs (se 1 (by rfl) ⟨7850, by rfl⟩) R15701
theorem R10501 : Reach 10501 := rs (se 4 (by rfl) ⟨984, by rfl⟩) R1969
theorem R10509 : Reach 10509 := rs (se 3 (by rfl) ⟨1970, by rfl⟩) R3941
theorem R10513 : Reach 10513 := rs (se 2 (by rfl) ⟨3942, by rfl⟩) R7885
theorem R10609 : Reach 10609 := rs (se 2 (by rfl) ⟨3978, by rfl⟩) R7957
theorem R10613 : Reach 10613 := rs (se 5 (by rfl) ⟨497, by rfl⟩) R995
theorem R10713 : Reach 10713 := rs (se 2 (by rfl) ⟨4017, by rfl⟩) R8035
theorem R10717 : Reach 10717 := rs (se 3 (by rfl) ⟨2009, by rfl⟩) R4019
theorem R10781 : Reach 10781 := rs (se 3 (by rfl) ⟨2021, by rfl⟩) R4043
theorem R10785 : Reach 10785 := rs (se 2 (by rfl) ⟨4044, by rfl⟩) R8089
theorem R11405 : Reach 11405 := rs (se 3 (by rfl) ⟨2138, by rfl⟩) R4277
theorem R11413 : Reach 11413 := rs (se 6 (by rfl) ⟨267, by rfl⟩) R535
theorem R11415 : Reach 11415 := rs (se 1 (by rfl) ⟨8561, by rfl⟩) R17123
theorem R11445 : Reach 11445 := rs (se 5 (by rfl) ⟨536, by rfl⟩) R1073
theorem R11457 : Reach 11457 := rs (se 2 (by rfl) ⟨4296, by rfl⟩) R8593
theorem R11459 : Reach 11459 := rs (se 1 (by rfl) ⟨8594, by rfl⟩) R17189
theorem R11461 : Reach 11461 := rs (se 4 (by rfl) ⟨1074, by rfl⟩) R2149
theorem R11469 : Reach 11469 := rs (se 3 (by rfl) ⟨2150, by rfl⟩) R4301
theorem R45845 : Reach 45845 := rs (se 6 (by rfl) ⟨1074, by rfl⟩) R2149
theorem R80099 : Reach 80099 := rs (se 1 (by rfl) ⟨60074, by rfl⟩) R120149
theorem R20621 : Reach 20621 := rs (se 3 (by rfl) ⟨3866, by rfl⟩) R7733
theorem R20933 : Reach 20933 := rs (se 4 (by rfl) ⟨1962, by rfl⟩) R3925
theorem R21005 : Reach 21005 := rs (se 3 (by rfl) ⟨3938, by rfl⟩) R7877
theorem R21035 : Reach 21035 := rs (se 1 (by rfl) ⟨15776, by rfl⟩) R31553
theorem R22805 : Reach 22805 := rs (se 6 (by rfl) ⟨534, by rfl⟩) R1069
theorem R22901 : Reach 22901 := rs (se 5 (by rfl) ⟨1073, by rfl⟩) R2147
theorem R22933 : Reach 22933 := rs (se 6 (by rfl) ⟨537, by rfl⟩) R1075
theorem R25 : Reach 25 := rs (se 2 (by rfl) ⟨9, by rfl⟩) R19
theorem R49 : Reach 49 := rs (se 2 (by rfl) ⟨18, by rfl⟩) R37
theorem R51 : Reach 51 := rs (se 1 (by rfl) ⟨38, by rfl⟩) R77
theorem R99 : Reach 99 := rs (se 1 (by rfl) ⟨74, by rfl⟩) R149
theorem R101 : Reach 101 := rs (se 4 (by rfl) ⟨9, by rfl⟩) R19
theorem R197 : Reach 197 := rs (se 4 (by rfl) ⟨18, by rfl⟩) R37
theorem R205 : Reach 205 := rs (se 3 (by rfl) ⟨38, by rfl⟩) R77
theorem R217 : Reach 217 := rs (se 2 (by rfl) ⟨81, by rfl⟩) R163
theorem R397 : Reach 397 := rs (se 3 (by rfl) ⟨74, by rfl⟩) R149
theorem R405 : Reach 405 := rs (se 6 (by rfl) ⟨9, by rfl⟩) R19
theorem R433 : Reach 433 := rs (se 2 (by rfl) ⟨162, by rfl⟩) R325
theorem R435 : Reach 435 := rs (se 1 (by rfl) ⟨326, by rfl⟩) R653
theorem R441 : Reach 441 := rs (se 2 (by rfl) ⟨165, by rfl⟩) R331
theorem R475 : Reach 475 := rs (se 1 (by rfl) ⟨356, by rfl⟩) R713
theorem R789 : Reach 789 := rs (se 6 (by rfl) ⟨18, by rfl⟩) R37
theorem R821 : Reach 821 := rs (se 5 (by rfl) ⟨38, by rfl⟩) R77
theorem R833 : Reach 833 := rs (se 2 (by rfl) ⟨312, by rfl⟩) R625
theorem R857 : Reach 857 := rs (se 2 (by rfl) ⟨321, by rfl⟩) R643
theorem R867 : Reach 867 := rs (se 1 (by rfl) ⟨650, by rfl⟩) R1301
theorem R869 : Reach 869 := rs (se 4 (by rfl) ⟨81, by rfl⟩) R163
theorem R875 : Reach 875 := rs (se 1 (by rfl) ⟨656, by rfl⟩) R1313
theorem R883 : Reach 883 := rs (se 1 (by rfl) ⟨662, by rfl⟩) R1325
theorem R951 : Reach 951 := rs (se 1 (by rfl) ⟨713, by rfl⟩) R1427
theorem R953 : Reach 953 := rs (se 2 (by rfl) ⟨357, by rfl⟩) R715
theorem R955 : Reach 955 := rs (se 1 (by rfl) ⟨716, by rfl⟩) R1433
theorem R1589 : Reach 1589 := rs (se 5 (by rfl) ⟨74, by rfl⟩) R149
theorem R1621 : Reach 1621 := rs (se 8 (by rfl) ⟨9, by rfl⟩) R19
theorem R1649 : Reach 1649 := rs (se 2 (by rfl) ⟨618, by rfl⟩) R1237
theorem R1667 : Reach 1667 := rs (se 1 (by rfl) ⟨1250, by rfl⟩) R2501
theorem R1713 : Reach 1713 := rs (se 2 (by rfl) ⟨642, by rfl⟩) R1285
theorem R1715 : Reach 1715 := rs (se 1 (by rfl) ⟨1286, by rfl⟩) R2573
theorem R1733 : Reach 1733 := rs (se 4 (by rfl) ⟨162, by rfl⟩) R325
theorem R1741 : Reach 1741 := rs (se 3 (by rfl) ⟨326, by rfl⟩) R653
theorem R1751 : Reach 1751 := rs (se 1 (by rfl) ⟨1313, by rfl⟩) R2627
theorem R1765 : Reach 1765 := rs (se 4 (by rfl) ⟨165, by rfl⟩) R331
theorem R1785 : Reach 1785 := rs (se 2 (by rfl) ⟨669, by rfl⟩) R1339
theorem R1901 : Reach 1901 := rs (se 3 (by rfl) ⟨356, by rfl⟩) R713
theorem R1907 : Reach 1907 := rs (se 1 (by rfl) ⟨1430, by rfl⟩) R2861
theorem R1911 : Reach 1911 := rs (se 1 (by rfl) ⟨1433, by rfl⟩) R2867
theorem R3157 : Reach 3157 := rs (se 8 (by rfl) ⟨18, by rfl⟩) R37
theorem R3185 : Reach 3185 := rs (se 2 (by rfl) ⟨1194, by rfl⟩) R2389
theorem R3285 : Reach 3285 := rs (se 7 (by rfl) ⟨38, by rfl⟩) R77
theorem R3299 : Reach 3299 := rs (se 1 (by rfl) ⟨2474, by rfl⟩) R4949
theorem R3333 : Reach 3333 := rs (se 4 (by rfl) ⟨312, by rfl⟩) R625
theorem R3427 : Reach 3427 := rs (se 1 (by rfl) ⟨2570, by rfl⟩) R5141
theorem R3429 : Reach 3429 := rs (se 4 (by rfl) ⟨321, by rfl⟩) R643
theorem R3469 : Reach 3469 := rs (se 3 (by rfl) ⟨650, by rfl⟩) R1301
theorem R3477 : Reach 3477 := rs (se 6 (by rfl) ⟨81, by rfl⟩) R163
theorem R3501 : Reach 3501 := rs (se 3 (by rfl) ⟨656, by rfl⟩) R1313
theorem R3533 : Reach 3533 := rs (se 3 (by rfl) ⟨662, by rfl⟩) R1325
theorem R3537 : Reach 3537 := rs (se 2 (by rfl) ⟨1326, by rfl⟩) R2653
theorem R3571 : Reach 3571 := rs (se 1 (by rfl) ⟨2678, by rfl⟩) R5357
theorem R3593 : Reach 3593 := rs (se 2 (by rfl) ⟨1347, by rfl⟩) R2695
theorem R3801 : Reach 3801 := rs (se 2 (by rfl) ⟨1425, by rfl⟩) R2851
theorem R3805 : Reach 3805 := rs (se 3 (by rfl) ⟨713, by rfl⟩) R1427
theorem R3813 : Reach 3813 := rs (se 4 (by rfl) ⟨357, by rfl⟩) R715
theorem R3819 : Reach 3819 := rs (se 1 (by rfl) ⟨2864, by rfl⟩) R5729
theorem R3821 : Reach 3821 := rs (se 3 (by rfl) ⟨716, by rfl⟩) R1433
theorem R6357 : Reach 6357 := rs (se 7 (by rfl) ⟨74, by rfl⟩) R149
theorem R6371 : Reach 6371 := rs (se 1 (by rfl) ⟨4778, by rfl⟩) R9557
theorem R6485 : Reach 6485 := rs (se 10 (by rfl) ⟨9, by rfl⟩) R19
theorem R6597 : Reach 6597 := rs (se 4 (by rfl) ⟨618, by rfl⟩) R1237
theorem R6669 : Reach 6669 := rs (se 3 (by rfl) ⟨1250, by rfl⟩) R2501
theorem R6673 : Reach 6673 := rs (se 2 (by rfl) ⟨2502, by rfl⟩) R5005
theorem R6853 : Reach 6853 := rs (se 4 (by rfl) ⟨642, by rfl⟩) R1285
theorem R6861 : Reach 6861 := rs (se 3 (by rfl) ⟨1286, by rfl⟩) R2573
theorem R6873 : Reach 6873 := rs (se 2 (by rfl) ⟨2577, by rfl⟩) R5155
theorem R6933 : Reach 6933 := rs (se 6 (by rfl) ⟨162, by rfl⟩) R325
theorem R6965 : Reach 6965 := rs (se 5 (by rfl) ⟨326, by rfl⟩) R653
theorem R6977 : Reach 6977 := rs (se 2 (by rfl) ⟨2616, by rfl⟩) R5233
theorem R7001 : Reach 7001 := rs (se 2 (by rfl) ⟨2625, by rfl⟩) R5251
theorem R7005 : Reach 7005 := rs (se 3 (by rfl) ⟨1313, by rfl⟩) R2627
theorem R7061 : Reach 7061 := rs (se 6 (by rfl) ⟨165, by rfl⟩) R331
theorem R7075 : Reach 7075 := rs (se 1 (by rfl) ⟨5306, by rfl⟩) R10613
theorem R7141 : Reach 7141 := rs (se 4 (by rfl) ⟨669, by rfl⟩) R1339
theorem R7187 : Reach 7187 := rs (se 1 (by rfl) ⟨5390, by rfl⟩) R10781
theorem R7601 : Reach 7601 := rs (se 2 (by rfl) ⟨2850, by rfl⟩) R5701
theorem R7603 : Reach 7603 := rs (se 1 (by rfl) ⟨5702, by rfl⟩) R11405
theorem R7605 : Reach 7605 := rs (se 5 (by rfl) ⟨356, by rfl⟩) R713
theorem R7609 : Reach 7609 := rs (se 2 (by rfl) ⟨2853, by rfl⟩) R5707
theorem R7629 : Reach 7629 := rs (se 3 (by rfl) ⟨1430, by rfl⟩) R2861
theorem R7633 : Reach 7633 := rs (se 2 (by rfl) ⟨2862, by rfl⟩) R5725
theorem R7639 : Reach 7639 := rs (se 1 (by rfl) ⟨5729, by rfl⟩) R11459
theorem R7641 : Reach 7641 := rs (se 2 (by rfl) ⟨2865, by rfl⟩) R5731
theorem R7645 : Reach 7645 := rs (se 3 (by rfl) ⟨1433, by rfl⟩) R2867
theorem R109795 : Reach 109795 := rs (se 1 (by rfl) ⟨82346, by rfl⟩) R164693
theorem R12629 : Reach 12629 := rs (se 10 (by rfl) ⟨18, by rfl⟩) R37
theorem R12741 : Reach 12741 := rs (se 4 (by rfl) ⟨1194, by rfl⟩) R2389
theorem R13333 : Reach 13333 := rs (se 6 (by rfl) ⟨312, by rfl⟩) R625
theorem R13709 : Reach 13709 := rs (se 3 (by rfl) ⟨2570, by rfl⟩) R5141
theorem R13745 : Reach 13745 := rs (se 2 (by rfl) ⟨5154, by rfl⟩) R10309
theorem R13747 : Reach 13747 := rs (se 1 (by rfl) ⟨10310, by rfl⟩) R20621
theorem R13877 : Reach 13877 := rs (se 5 (by rfl) ⟨650, by rfl⟩) R1301
theorem R13909 : Reach 13909 := rs (se 8 (by rfl) ⟨81, by rfl⟩) R163
theorem R13937 : Reach 13937 := rs (se 2 (by rfl) ⟨5226, by rfl⟩) R10453
theorem R13955 : Reach 13955 := rs (se 1 (by rfl) ⟨10466, by rfl⟩) R20933
theorem R14003 : Reach 14003 := rs (se 1 (by rfl) ⟨10502, by rfl⟩) R21005
theorem R14017 : Reach 14017 := rs (se 2 (by rfl) ⟨5256, by rfl⟩) R10513
theorem R14023 : Reach 14023 := rs (se 1 (by rfl) ⟨10517, by rfl⟩) R21035
theorem R14285 : Reach 14285 := rs (se 3 (by rfl) ⟨2678, by rfl⟩) R5357
theorem R15203 : Reach 15203 := rs (se 1 (by rfl) ⟨11402, by rfl⟩) R22805
theorem R15221 : Reach 15221 := rs (se 5 (by rfl) ⟨713, by rfl⟩) R1427
theorem R15281 : Reach 15281 := rs (se 2 (by rfl) ⟨5730, by rfl⟩) R11461
theorem R53399 : Reach 53399 := rs (se 1 (by rfl) ⟨40049, by rfl⟩) R80099
theorem R26693 : Reach 26693 := rs (se 4 (by rfl) ⟨2502, by rfl⟩) R5005
theorem R27413 : Reach 27413 := rs (se 6 (by rfl) ⟨642, by rfl⟩) R1285
theorem R28021 : Reach 28021 := rs (se 5 (by rfl) ⟨1313, by rfl⟩) R2627
theorem R28039 : Reach 28039 := rs (se 1 (by rfl) ⟨21029, by rfl⟩) R42059
theorem R60869 : Reach 60869 := rs (se 4 (by rfl) ⟨5706, by rfl⟩) R11413
theorem R61069 : Reach 61069 := rs (se 3 (by rfl) ⟨11450, by rfl⟩) R22901
theorem R28565 : Reach 28565 := rs (se 6 (by rfl) ⟨669, by rfl⟩) R1339
theorem R30557 : Reach 30557 := rs (se 3 (by rfl) ⟨5729, by rfl⟩) R11459
theorem R30563 : Reach 30563 := rs (se 1 (by rfl) ⟨22922, by rfl⟩) R45845
theorem R30577 : Reach 30577 := rs (se 2 (by rfl) ⟨11466, by rfl⟩) R22933
theorem R33 : Reach 33 := rs (se 2 (by rfl) ⟨12, by rfl⟩) R25
theorem R65 : Reach 65 := rs (se 2 (by rfl) ⟨24, by rfl⟩) R49
theorem R67 : Reach 67 := rs (se 1 (by rfl) ⟨50, by rfl⟩) R101
theorem R131 : Reach 131 := rs (se 1 (by rfl) ⟨98, by rfl⟩) R197
theorem R133 : Reach 133 := rs (se 4 (by rfl) ⟨12, by rfl⟩) R25
theorem R261 : Reach 261 := rs (se 4 (by rfl) ⟨24, by rfl⟩) R49
theorem R269 : Reach 269 := rs (se 3 (by rfl) ⟨50, by rfl⟩) R101
theorem R273 : Reach 273 := rs (se 2 (by rfl) ⟨102, by rfl⟩) R205
theorem R289 : Reach 289 := rs (se 2 (by rfl) ⟨108, by rfl⟩) R217
theorem R525 : Reach 525 := rs (se 3 (by rfl) ⟨98, by rfl⟩) R197
theorem R529 : Reach 529 := rs (se 2 (by rfl) ⟨198, by rfl⟩) R397
theorem R533 : Reach 533 := rs (se 6 (by rfl) ⟨12, by rfl⟩) R25
theorem R547 : Reach 547 := rs (se 1 (by rfl) ⟨410, by rfl⟩) R821
theorem R555 : Reach 555 := rs (se 1 (by rfl) ⟨416, by rfl⟩) R833
theorem R571 : Reach 571 := rs (se 1 (by rfl) ⟨428, by rfl⟩) R857
theorem R577 : Reach 577 := rs (se 2 (by rfl) ⟨216, by rfl⟩) R433
theorem R579 : Reach 579 := rs (se 1 (by rfl) ⟨434, by rfl⟩) R869
theorem R583 : Reach 583 := rs (se 1 (by rfl) ⟨437, by rfl⟩) R875
theorem R633 : Reach 633 := rs (se 2 (by rfl) ⟨237, by rfl⟩) R475
theorem R635 : Reach 635 := rs (se 1 (by rfl) ⟨476, by rfl⟩) R953
theorem R33677 : Reach 33677 := rs (se 3 (by rfl) ⟨6314, by rfl⟩) R12629
theorem R1045 : Reach 1045 := rs (se 6 (by rfl) ⟨24, by rfl⟩) R49
theorem R1059 : Reach 1059 := rs (se 1 (by rfl) ⟨794, by rfl⟩) R1589
theorem R1077 : Reach 1077 := rs (se 5 (by rfl) ⟨50, by rfl⟩) R101
theorem R1093 : Reach 1093 := rs (se 4 (by rfl) ⟨102, by rfl⟩) R205
theorem R1099 : Reach 1099 := rs (se 1 (by rfl) ⟨824, by rfl⟩) R1649
theorem R1111 : Reach 1111 := rs (se 1 (by rfl) ⟨833, by rfl⟩) R1667
theorem R1143 : Reach 1143 := rs (se 1 (by rfl) ⟨857, by rfl⟩) R1715
theorem R1155 : Reach 1155 := rs (se 1 (by rfl) ⟨866, by rfl⟩) R1733
theorem R1157 : Reach 1157 := rs (se 4 (by rfl) ⟨108, by rfl⟩) R217
theorem R1167 : Reach 1167 := rs (se 1 (by rfl) ⟨875, by rfl⟩) R1751
theorem R1177 : Reach 1177 := rs (se 2 (by rfl) ⟨441, by rfl⟩) R883
theorem R1267 : Reach 1267 := rs (se 1 (by rfl) ⟨950, by rfl⟩) R1901
theorem R1271 : Reach 1271 := rs (se 1 (by rfl) ⟨953, by rfl⟩) R1907
theorem R1273 : Reach 1273 := rs (se 2 (by rfl) ⟨477, by rfl⟩) R955
theorem R2101 : Reach 2101 := rs (se 5 (by rfl) ⟨98, by rfl⟩) R197
theorem R2117 : Reach 2117 := rs (se 4 (by rfl) ⟨198, by rfl⟩) R397
theorem R2123 : Reach 2123 := rs (se 1 (by rfl) ⟨1592, by rfl⟩) R3185
theorem R2133 : Reach 2133 := rs (se 8 (by rfl) ⟨12, by rfl⟩) R25
theorem R2161 : Reach 2161 := rs (se 2 (by rfl) ⟨810, by rfl⟩) R1621
theorem R2189 : Reach 2189 := rs (se 3 (by rfl) ⟨410, by rfl⟩) R821
theorem R2199 : Reach 2199 := rs (se 1 (by rfl) ⟨1649, by rfl⟩) R3299
theorem R2221 : Reach 2221 := rs (se 3 (by rfl) ⟨416, by rfl⟩) R833
theorem R2285 : Reach 2285 := rs (se 3 (by rfl) ⟨428, by rfl⟩) R857
theorem R2309 : Reach 2309 := rs (se 4 (by rfl) ⟨216, by rfl⟩) R433
theorem R2317 : Reach 2317 := rs (se 3 (by rfl) ⟨434, by rfl⟩) R869
theorem R2321 : Reach 2321 := rs (se 2 (by rfl) ⟨870, by rfl⟩) R1741
theorem R2333 : Reach 2333 := rs (se 3 (by rfl) ⟨437, by rfl⟩) R875
theorem R2353 : Reach 2353 := rs (se 2 (by rfl) ⟨882, by rfl⟩) R1765
theorem R2355 : Reach 2355 := rs (se 1 (by rfl) ⟨1766, by rfl⟩) R3533
theorem R2395 : Reach 2395 := rs (se 1 (by rfl) ⟨1796, by rfl⟩) R3593
theorem R2533 : Reach 2533 := rs (se 4 (by rfl) ⟨237, by rfl⟩) R475
theorem R2541 : Reach 2541 := rs (se 3 (by rfl) ⟨476, by rfl⟩) R953
theorem R2547 : Reach 2547 := rs (se 1 (by rfl) ⟨1910, by rfl⟩) R3821
theorem R35599 : Reach 35599 := rs (se 1 (by rfl) ⟨26699, by rfl⟩) R53399
theorem R36557 : Reach 36557 := rs (se 3 (by rfl) ⟨6854, by rfl⟩) R13709
theorem R4181 : Reach 4181 := rs (se 8 (by rfl) ⟨24, by rfl⟩) R49
theorem R4209 : Reach 4209 := rs (se 2 (by rfl) ⟨1578, by rfl⟩) R3157
theorem R4237 : Reach 4237 := rs (se 3 (by rfl) ⟨794, by rfl⟩) R1589
theorem R4247 : Reach 4247 := rs (se 1 (by rfl) ⟨3185, by rfl⟩) R6371
theorem R4309 : Reach 4309 := rs (se 7 (by rfl) ⟨50, by rfl⟩) R101
theorem R4323 : Reach 4323 := rs (se 1 (by rfl) ⟨3242, by rfl⟩) R6485
theorem R4373 : Reach 4373 := rs (se 6 (by rfl) ⟨102, by rfl⟩) R205
theorem R4397 : Reach 4397 := rs (se 3 (by rfl) ⟨824, by rfl⟩) R1649
theorem R4445 : Reach 4445 := rs (se 3 (by rfl) ⟨833, by rfl⟩) R1667
theorem R4569 : Reach 4569 := rs (se 2 (by rfl) ⟨1713, by rfl⟩) R3427
theorem R4573 : Reach 4573 := rs (se 3 (by rfl) ⟨857, by rfl⟩) R1715
theorem R37361 : Reach 37361 := rs (se 2 (by rfl) ⟨14010, by rfl⟩) R28021
theorem R37385 : Reach 37385 := rs (se 2 (by rfl) ⟨14019, by rfl⟩) R28039
theorem R4621 : Reach 4621 := rs (se 3 (by rfl) ⟨866, by rfl⟩) R1733
theorem R4625 : Reach 4625 := rs (se 2 (by rfl) ⟨1734, by rfl⟩) R3469
theorem R4629 : Reach 4629 := rs (se 6 (by rfl) ⟨108, by rfl⟩) R217
theorem R4643 : Reach 4643 := rs (se 1 (by rfl) ⟨3482, by rfl⟩) R6965
theorem R4651 : Reach 4651 := rs (se 1 (by rfl) ⟨3488, by rfl⟩) R6977
theorem R4667 : Reach 4667 := rs (se 1 (by rfl) ⟨3500, by rfl⟩) R7001
theorem R4669 : Reach 4669 := rs (se 3 (by rfl) ⟨875, by rfl⟩) R1751
theorem R4707 : Reach 4707 := rs (se 1 (by rfl) ⟨3530, by rfl⟩) R7061
theorem R4709 : Reach 4709 := rs (se 4 (by rfl) ⟨441, by rfl⟩) R883
theorem R4761 : Reach 4761 := rs (se 2 (by rfl) ⟨1785, by rfl⟩) R3571
theorem R4791 : Reach 4791 := rs (se 1 (by rfl) ⟨3593, by rfl⟩) R7187
theorem R37685 : Reach 37685 := rs (se 5 (by rfl) ⟨1766, by rfl⟩) R3533
theorem R5067 : Reach 5067 := rs (se 1 (by rfl) ⟨3800, by rfl⟩) R7601
theorem R5069 : Reach 5069 := rs (se 3 (by rfl) ⟨950, by rfl⟩) R1901
theorem R5073 : Reach 5073 := rs (se 2 (by rfl) ⟨1902, by rfl⟩) R3805
theorem R5085 : Reach 5085 := rs (se 3 (by rfl) ⟨953, by rfl⟩) R1907
theorem R5093 : Reach 5093 := rs (se 4 (by rfl) ⟨477, by rfl⟩) R955
theorem R40661 : Reach 40661 := rs (se 7 (by rfl) ⟨476, by rfl⟩) R953
theorem R40769 : Reach 40769 := rs (se 2 (by rfl) ⟨15288, by rfl⟩) R30577
theorem R8405 : Reach 8405 := rs (se 7 (by rfl) ⟨98, by rfl⟩) R197
theorem R8419 : Reach 8419 := rs (se 1 (by rfl) ⟨6314, by rfl⟩) R12629
theorem R8469 : Reach 8469 := rs (se 6 (by rfl) ⟨198, by rfl⟩) R397
theorem R8493 : Reach 8493 := rs (se 3 (by rfl) ⟨1592, by rfl⟩) R3185
theorem R8533 : Reach 8533 := rs (se 10 (by rfl) ⟨12, by rfl⟩) R25
theorem R8645 : Reach 8645 := rs (se 4 (by rfl) ⟨810, by rfl⟩) R1621
theorem R8757 : Reach 8757 := rs (se 5 (by rfl) ⟨410, by rfl⟩) R821
theorem R8797 : Reach 8797 := rs (se 3 (by rfl) ⟨1649, by rfl⟩) R3299
theorem R8885 : Reach 8885 := rs (se 5 (by rfl) ⟨416, by rfl⟩) R833
theorem R8897 : Reach 8897 := rs (se 2 (by rfl) ⟨3336, by rfl⟩) R6673
theorem R9137 : Reach 9137 := rs (se 2 (by rfl) ⟨3426, by rfl⟩) R6853
theorem R9139 : Reach 9139 := rs (se 1 (by rfl) ⟨6854, by rfl⟩) R13709
theorem R9141 : Reach 9141 := rs (se 5 (by rfl) ⟨428, by rfl⟩) R857
theorem R9163 : Reach 9163 := rs (se 1 (by rfl) ⟨6872, by rfl⟩) R13745
theorem R9237 : Reach 9237 := rs (se 6 (by rfl) ⟨216, by rfl⟩) R433
theorem R9251 : Reach 9251 := rs (se 1 (by rfl) ⟨6938, by rfl⟩) R13877
theorem R9269 : Reach 9269 := rs (se 5 (by rfl) ⟨434, by rfl⟩) R869
theorem R9285 : Reach 9285 := rs (se 4 (by rfl) ⟨870, by rfl⟩) R1741
theorem R9291 : Reach 9291 := rs (se 1 (by rfl) ⟨6968, by rfl⟩) R13937
theorem R9303 : Reach 9303 := rs (se 1 (by rfl) ⟨6977, by rfl⟩) R13955
theorem R9333 : Reach 9333 := rs (se 5 (by rfl) ⟨437, by rfl⟩) R875
theorem R9335 : Reach 9335 := rs (se 1 (by rfl) ⟨7001, by rfl⟩) R14003
theorem R9413 : Reach 9413 := rs (se 4 (by rfl) ⟨882, by rfl⟩) R1765
theorem R9421 : Reach 9421 := rs (se 3 (by rfl) ⟨1766, by rfl⟩) R3533
theorem R9433 : Reach 9433 := rs (se 2 (by rfl) ⟨3537, by rfl⟩) R7075
theorem R9521 : Reach 9521 := rs (se 2 (by rfl) ⟨3570, by rfl⟩) R7141
theorem R9523 : Reach 9523 := rs (se 1 (by rfl) ⟨7142, by rfl⟩) R14285
theorem R9581 : Reach 9581 := rs (se 3 (by rfl) ⟨1796, by rfl⟩) R3593
theorem R10133 : Reach 10133 := rs (se 6 (by rfl) ⟨237, by rfl⟩) R475
theorem R10135 : Reach 10135 := rs (se 1 (by rfl) ⟨7601, by rfl⟩) R15203
theorem R10137 : Reach 10137 := rs (se 2 (by rfl) ⟨3801, by rfl⟩) R7603
theorem R10145 : Reach 10145 := rs (se 2 (by rfl) ⟨3804, by rfl⟩) R7609
theorem R10147 : Reach 10147 := rs (se 1 (by rfl) ⟨7610, by rfl⟩) R15221
theorem R10165 : Reach 10165 := rs (se 5 (by rfl) ⟨476, by rfl⟩) R953
theorem R10177 : Reach 10177 := rs (se 2 (by rfl) ⟨3816, by rfl⟩) R7633
theorem R10185 : Reach 10185 := rs (se 2 (by rfl) ⟨3819, by rfl⟩) R7639
theorem R10187 : Reach 10187 := rs (se 1 (by rfl) ⟨7640, by rfl⟩) R15281
theorem R10189 : Reach 10189 := rs (se 3 (by rfl) ⟨1910, by rfl⟩) R3821
theorem R10193 : Reach 10193 := rs (se 2 (by rfl) ⟨3822, by rfl⟩) R7645
theorem R142397 : Reach 142397 := rs (se 3 (by rfl) ⟨26699, by rfl⟩) R53399
theorem R146393 : Reach 146393 := rs (se 2 (by rfl) ⟨54897, by rfl⟩) R109795
theorem R81425 : Reach 81425 := rs (se 2 (by rfl) ⟨30534, by rfl⟩) R61069
theorem R16949 : Reach 16949 := rs (se 5 (by rfl) ⟨794, by rfl⟩) R1589
theorem R17237 : Reach 17237 := rs (se 9 (by rfl) ⟨50, by rfl⟩) R101
theorem R17293 : Reach 17293 := rs (se 3 (by rfl) ⟨3242, by rfl⟩) R6485
theorem R17777 : Reach 17777 := rs (se 2 (by rfl) ⟨6666, by rfl⟩) R13333
theorem R17795 : Reach 17795 := rs (se 1 (by rfl) ⟨13346, by rfl⟩) R26693
theorem R18275 : Reach 18275 := rs (se 1 (by rfl) ⟨13706, by rfl⟩) R27413
theorem R18293 : Reach 18293 := rs (se 5 (by rfl) ⟨857, by rfl⟩) R1715
theorem R18329 : Reach 18329 := rs (se 2 (by rfl) ⟨6873, by rfl⟩) R13747
theorem R18485 : Reach 18485 := rs (se 5 (by rfl) ⟨866, by rfl⟩) R1733
theorem R18545 : Reach 18545 := rs (se 2 (by rfl) ⟨6954, by rfl⟩) R13909
theorem R18605 : Reach 18605 := rs (se 3 (by rfl) ⟨3488, by rfl⟩) R6977
theorem R18677 : Reach 18677 := rs (se 5 (by rfl) ⟨875, by rfl⟩) R1751
theorem R18689 : Reach 18689 := rs (se 2 (by rfl) ⟨7008, by rfl⟩) R14017
theorem R18697 : Reach 18697 := rs (se 2 (by rfl) ⟨7011, by rfl⟩) R14023
theorem R18829 : Reach 18829 := rs (se 3 (by rfl) ⟨3530, by rfl⟩) R7061
theorem R19043 : Reach 19043 := rs (se 1 (by rfl) ⟨14282, by rfl⟩) R28565
theorem R19045 : Reach 19045 := rs (se 4 (by rfl) ⟨1785, by rfl⟩) R3571
theorem R20371 : Reach 20371 := rs (se 1 (by rfl) ⟨15278, by rfl⟩) R30557
theorem R20375 : Reach 20375 := rs (se 1 (by rfl) ⟨15281, by rfl⟩) R30563
theorem R162317 : Reach 162317 := rs (se 3 (by rfl) ⟨30434, by rfl⟩) R60869
theorem R43 : Reach 43 := rs (se 1 (by rfl) ⟨32, by rfl⟩) R65
theorem R87 : Reach 87 := rs (se 1 (by rfl) ⟨65, by rfl⟩) R131
theorem R89 : Reach 89 := rs (se 2 (by rfl) ⟨33, by rfl⟩) R67
theorem R173 : Reach 173 := rs (se 3 (by rfl) ⟨32, by rfl⟩) R65
theorem R177 : Reach 177 := rs (se 2 (by rfl) ⟨66, by rfl⟩) R133
theorem R179 : Reach 179 := rs (se 1 (by rfl) ⟨134, by rfl⟩) R269
theorem R349 : Reach 349 := rs (se 3 (by rfl) ⟨65, by rfl⟩) R131
theorem R355 : Reach 355 := rs (se 1 (by rfl) ⟨266, by rfl⟩) R533
theorem R357 : Reach 357 := rs (se 4 (by rfl) ⟨33, by rfl⟩) R67
theorem R385 : Reach 385 := rs (se 2 (by rfl) ⟨144, by rfl⟩) R289
theorem R423 : Reach 423 := rs (se 1 (by rfl) ⟨317, by rfl⟩) R635
theorem R693 : Reach 693 := rs (se 5 (by rfl) ⟨32, by rfl⟩) R65
theorem R705 : Reach 705 := rs (se 2 (by rfl) ⟨264, by rfl⟩) R529
theorem R709 : Reach 709 := rs (se 4 (by rfl) ⟨66, by rfl⟩) R133
theorem R717 : Reach 717 := rs (se 3 (by rfl) ⟨134, by rfl⟩) R269
theorem R729 : Reach 729 := rs (se 2 (by rfl) ⟨273, by rfl⟩) R547
theorem R761 : Reach 761 := rs (se 2 (by rfl) ⟨285, by rfl⟩) R571
theorem R769 : Reach 769 := rs (se 2 (by rfl) ⟨288, by rfl⟩) R577
theorem R771 : Reach 771 := rs (se 1 (by rfl) ⟨578, by rfl⟩) R1157
theorem R777 : Reach 777 := rs (se 2 (by rfl) ⟨291, by rfl⟩) R583
theorem R847 : Reach 847 := rs (se 1 (by rfl) ⟨635, by rfl⟩) R1271
theorem R1393 : Reach 1393 := rs (se 2 (by rfl) ⟨522, by rfl⟩) R1045
theorem R1397 : Reach 1397 := rs (se 5 (by rfl) ⟨65, by rfl⟩) R131
theorem R1411 : Reach 1411 := rs (se 1 (by rfl) ⟨1058, by rfl⟩) R2117
theorem R1415 : Reach 1415 := rs (se 1 (by rfl) ⟨1061, by rfl⟩) R2123
theorem R1421 : Reach 1421 := rs (se 3 (by rfl) ⟨266, by rfl⟩) R533
theorem R1429 : Reach 1429 := rs (se 6 (by rfl) ⟨33, by rfl⟩) R67
theorem R1457 : Reach 1457 := rs (se 2 (by rfl) ⟨546, by rfl⟩) R1093
theorem R1459 : Reach 1459 := rs (se 1 (by rfl) ⟨1094, by rfl⟩) R2189
theorem R1465 : Reach 1465 := rs (se 2 (by rfl) ⟨549, by rfl⟩) R1099
theorem R1481 : Reach 1481 := rs (se 2 (by rfl) ⟨555, by rfl⟩) R1111
theorem R1523 : Reach 1523 := rs (se 1 (by rfl) ⟨1142, by rfl⟩) R2285
theorem R1539 : Reach 1539 := rs (se 1 (by rfl) ⟨1154, by rfl⟩) R2309
theorem R1541 : Reach 1541 := rs (se 4 (by rfl) ⟨144, by rfl⟩) R289
theorem R1547 : Reach 1547 := rs (se 1 (by rfl) ⟨1160, by rfl⟩) R2321
theorem R1555 : Reach 1555 := rs (se 1 (by rfl) ⟨1166, by rfl⟩) R2333
theorem R1569 : Reach 1569 := rs (se 2 (by rfl) ⟨588, by rfl⟩) R1177
theorem R1689 : Reach 1689 := rs (se 2 (by rfl) ⟨633, by rfl⟩) R1267
theorem R1693 : Reach 1693 := rs (se 3 (by rfl) ⟨317, by rfl⟩) R635
theorem R1697 : Reach 1697 := rs (se 2 (by rfl) ⟨636, by rfl⟩) R1273
theorem R2773 : Reach 2773 := rs (se 7 (by rfl) ⟨32, by rfl⟩) R65
theorem R2787 : Reach 2787 := rs (se 1 (by rfl) ⟨2090, by rfl⟩) R4181
theorem R2801 : Reach 2801 := rs (se 2 (by rfl) ⟨1050, by rfl⟩) R2101
theorem R2821 : Reach 2821 := rs (se 4 (by rfl) ⟨264, by rfl⟩) R529
theorem R2831 : Reach 2831 := rs (se 1 (by rfl) ⟨2123, by rfl⟩) R4247
theorem R2837 : Reach 2837 := rs (se 6 (by rfl) ⟨66, by rfl⟩) R133
theorem R2869 : Reach 2869 := rs (se 5 (by rfl) ⟨134, by rfl⟩) R269
theorem R2881 : Reach 2881 := rs (se 2 (by rfl) ⟨1080, by rfl⟩) R2161
theorem R2915 : Reach 2915 := rs (se 1 (by rfl) ⟨2186, by rfl⟩) R4373
theorem R2917 : Reach 2917 := rs (se 4 (by rfl) ⟨273, by rfl⟩) R547
theorem R2931 : Reach 2931 := rs (se 1 (by rfl) ⟨2198, by rfl⟩) R4397
theorem R2961 : Reach 2961 := rs (se 2 (by rfl) ⟨1110, by rfl⟩) R2221
theorem R2963 : Reach 2963 := rs (se 1 (by rfl) ⟨2222, by rfl⟩) R4445
theorem R3045 : Reach 3045 := rs (se 4 (by rfl) ⟨285, by rfl⟩) R571
theorem R3077 : Reach 3077 := rs (se 4 (by rfl) ⟨288, by rfl⟩) R577
theorem R3083 : Reach 3083 := rs (se 1 (by rfl) ⟨2312, by rfl⟩) R4625
theorem R3085 : Reach 3085 := rs (se 3 (by rfl) ⟨578, by rfl⟩) R1157
theorem R3089 : Reach 3089 := rs (se 2 (by rfl) ⟨1158, by rfl⟩) R2317
theorem R3095 : Reach 3095 := rs (se 1 (by rfl) ⟨2321, by rfl⟩) R4643
theorem R3109 : Reach 3109 := rs (se 4 (by rfl) ⟨291, by rfl⟩) R583
theorem R3111 : Reach 3111 := rs (se 1 (by rfl) ⟨2333, by rfl⟩) R4667
theorem R3137 : Reach 3137 := rs (se 2 (by rfl) ⟨1176, by rfl⟩) R2353
theorem R3139 : Reach 3139 := rs (se 1 (by rfl) ⟨2354, by rfl⟩) R4709
theorem R3193 : Reach 3193 := rs (se 2 (by rfl) ⟨1197, by rfl⟩) R2395
theorem R101573 : Reach 101573 := rs (se 4 (by rfl) ⟨9522, by rfl⟩) R19045
theorem R3377 : Reach 3377 := rs (se 2 (by rfl) ⟨1266, by rfl⟩) R2533
theorem R3379 : Reach 3379 := rs (se 1 (by rfl) ⟨2534, by rfl⟩) R5069
theorem R3389 : Reach 3389 := rs (se 3 (by rfl) ⟨635, by rfl⟩) R1271
theorem R3395 : Reach 3395 := rs (se 1 (by rfl) ⟨2546, by rfl⟩) R5093
theorem R5573 : Reach 5573 := rs (se 4 (by rfl) ⟨522, by rfl⟩) R1045
theorem R5589 : Reach 5589 := rs (se 7 (by rfl) ⟨65, by rfl⟩) R131
theorem R5603 : Reach 5603 := rs (se 1 (by rfl) ⟨4202, by rfl⟩) R8405
theorem R5645 : Reach 5645 := rs (se 3 (by rfl) ⟨1058, by rfl⟩) R2117
theorem R5649 : Reach 5649 := rs (se 2 (by rfl) ⟨2118, by rfl⟩) R4237
theorem R5661 : Reach 5661 := rs (se 3 (by rfl) ⟨1061, by rfl⟩) R2123
theorem R5685 : Reach 5685 := rs (se 5 (by rfl) ⟨266, by rfl⟩) R533
theorem R5717 : Reach 5717 := rs (se 8 (by rfl) ⟨33, by rfl⟩) R67
theorem R5745 : Reach 5745 := rs (se 2 (by rfl) ⟨2154, by rfl⟩) R4309
theorem R5763 : Reach 5763 := rs (se 1 (by rfl) ⟨4322, by rfl⟩) R8645
theorem R5829 : Reach 5829 := rs (se 4 (by rfl) ⟨546, by rfl⟩) R1093
theorem R5837 : Reach 5837 := rs (se 3 (by rfl) ⟨1094, by rfl⟩) R2189
theorem R5861 : Reach 5861 := rs (se 4 (by rfl) ⟨549, by rfl⟩) R1099
theorem R5923 : Reach 5923 := rs (se 1 (by rfl) ⟨4442, by rfl⟩) R8885
theorem R5925 : Reach 5925 := rs (se 4 (by rfl) ⟨555, by rfl⟩) R1111
theorem R5931 : Reach 5931 := rs (se 1 (by rfl) ⟨4448, by rfl⟩) R8897
theorem R6091 : Reach 6091 := rs (se 1 (by rfl) ⟨4568, by rfl⟩) R9137
theorem R6093 : Reach 6093 := rs (se 3 (by rfl) ⟨1142, by rfl⟩) R2285
theorem R6097 : Reach 6097 := rs (se 2 (by rfl) ⟨2286, by rfl⟩) R4573
theorem R6157 : Reach 6157 := rs (se 3 (by rfl) ⟨1154, by rfl⟩) R2309
theorem R6161 : Reach 6161 := rs (se 2 (by rfl) ⟨2310, by rfl⟩) R4621
theorem R6165 : Reach 6165 := rs (se 6 (by rfl) ⟨144, by rfl⟩) R289
theorem R6167 : Reach 6167 := rs (se 1 (by rfl) ⟨4625, by rfl⟩) R9251
theorem R6179 : Reach 6179 := rs (se 1 (by rfl) ⟨4634, by rfl⟩) R9269
theorem R6189 : Reach 6189 := rs (se 3 (by rfl) ⟨1160, by rfl⟩) R2321
theorem R6201 : Reach 6201 := rs (se 2 (by rfl) ⟨2325, by rfl⟩) R4651
theorem R6221 : Reach 6221 := rs (se 3 (by rfl) ⟨1166, by rfl⟩) R2333
theorem R6223 : Reach 6223 := rs (se 1 (by rfl) ⟨4667, by rfl⟩) R9335
theorem R6225 : Reach 6225 := rs (se 2 (by rfl) ⟨2334, by rfl⟩) R4669
theorem R6275 : Reach 6275 := rs (se 1 (by rfl) ⟨4706, by rfl⟩) R9413
theorem R6277 : Reach 6277 := rs (se 4 (by rfl) ⟨588, by rfl⟩) R1177
theorem R6347 : Reach 6347 := rs (se 1 (by rfl) ⟨4760, by rfl⟩) R9521
theorem R6387 : Reach 6387 := rs (se 1 (by rfl) ⟨4790, by rfl⟩) R9581
theorem R6755 : Reach 6755 := rs (se 1 (by rfl) ⟨5066, by rfl⟩) R10133
theorem R6757 : Reach 6757 := rs (se 4 (by rfl) ⟨633, by rfl⟩) R1267
theorem R6763 : Reach 6763 := rs (se 1 (by rfl) ⟨5072, by rfl⟩) R10145
theorem R6773 : Reach 6773 := rs (se 5 (by rfl) ⟨317, by rfl⟩) R635
theorem R6789 : Reach 6789 := rs (se 4 (by rfl) ⟨636, by rfl⟩) R1273
theorem R6791 : Reach 6791 := rs (se 1 (by rfl) ⟨5093, by rfl⟩) R10187
theorem R6795 : Reach 6795 := rs (se 1 (by rfl) ⟨5096, by rfl⟩) R10193
theorem R108211 : Reach 108211 := rs (se 1 (by rfl) ⟨81158, by rfl⟩) R162317
theorem R11093 : Reach 11093 := rs (se 9 (by rfl) ⟨32, by rfl⟩) R65
theorem R11149 : Reach 11149 := rs (se 3 (by rfl) ⟨2090, by rfl⟩) R4181
theorem R11205 : Reach 11205 := rs (se 4 (by rfl) ⟨1050, by rfl⟩) R2101
theorem R11225 : Reach 11225 := rs (se 2 (by rfl) ⟨4209, by rfl⟩) R8419
theorem R11285 : Reach 11285 := rs (se 6 (by rfl) ⟨264, by rfl⟩) R529
theorem R11299 : Reach 11299 := rs (se 1 (by rfl) ⟨8474, by rfl⟩) R16949
theorem R11325 : Reach 11325 := rs (se 3 (by rfl) ⟨2123, by rfl⟩) R4247
theorem R11349 : Reach 11349 := rs (se 8 (by rfl) ⟨66, by rfl⟩) R133
theorem R11377 : Reach 11377 := rs (se 2 (by rfl) ⟨4266, by rfl⟩) R8533
theorem R11477 : Reach 11477 := rs (se 7 (by rfl) ⟨134, by rfl⟩) R269
theorem R11491 : Reach 11491 := rs (se 1 (by rfl) ⟨8618, by rfl⟩) R17237
theorem R11525 : Reach 11525 := rs (se 4 (by rfl) ⟨1080, by rfl⟩) R2161
theorem R11661 : Reach 11661 := rs (se 3 (by rfl) ⟨2186, by rfl⟩) R4373
theorem R11669 : Reach 11669 := rs (se 6 (by rfl) ⟨273, by rfl⟩) R547
theorem R11725 : Reach 11725 := rs (se 3 (by rfl) ⟨2198, by rfl⟩) R4397
theorem R11729 : Reach 11729 := rs (se 2 (by rfl) ⟨4398, by rfl⟩) R8797
theorem R11845 : Reach 11845 := rs (se 4 (by rfl) ⟨1110, by rfl⟩) R2221
theorem R11851 : Reach 11851 := rs (se 1 (by rfl) ⟨8888, by rfl⟩) R17777
theorem R11853 : Reach 11853 := rs (se 3 (by rfl) ⟨2222, by rfl⟩) R4445
theorem R11863 : Reach 11863 := rs (se 1 (by rfl) ⟨8897, by rfl⟩) R17795
theorem R12181 : Reach 12181 := rs (se 6 (by rfl) ⟨285, by rfl⟩) R571
theorem R12183 : Reach 12183 := rs (se 1 (by rfl) ⟨9137, by rfl⟩) R18275
theorem R12185 : Reach 12185 := rs (se 2 (by rfl) ⟨4569, by rfl⟩) R9139
theorem R12195 : Reach 12195 := rs (se 1 (by rfl) ⟨9146, by rfl⟩) R18293
theorem R12217 : Reach 12217 := rs (se 2 (by rfl) ⟨4581, by rfl⟩) R9163
theorem R12219 : Reach 12219 := rs (se 1 (by rfl) ⟨9164, by rfl⟩) R18329
theorem R12309 : Reach 12309 := rs (se 6 (by rfl) ⟨288, by rfl⟩) R577
theorem R12323 : Reach 12323 := rs (se 1 (by rfl) ⟨9242, by rfl⟩) R18485
theorem R12333 : Reach 12333 := rs (se 3 (by rfl) ⟨2312, by rfl⟩) R4625
theorem R12341 : Reach 12341 := rs (se 5 (by rfl) ⟨578, by rfl⟩) R1157
theorem R12357 : Reach 12357 := rs (se 4 (by rfl) ⟨1158, by rfl⟩) R2317
theorem R12363 : Reach 12363 := rs (se 1 (by rfl) ⟨9272, by rfl⟩) R18545
theorem R12381 : Reach 12381 := rs (se 3 (by rfl) ⟨2321, by rfl⟩) R4643
theorem R12403 : Reach 12403 := rs (se 1 (by rfl) ⟨9302, by rfl⟩) R18605
theorem R45197 : Reach 45197 := rs (se 3 (by rfl) ⟨8474, by rfl⟩) R16949
theorem R12437 : Reach 12437 := rs (se 6 (by rfl) ⟨291, by rfl⟩) R583
theorem R12445 : Reach 12445 := rs (se 3 (by rfl) ⟨2333, by rfl⟩) R4667
theorem R12451 : Reach 12451 := rs (se 1 (by rfl) ⟨9338, by rfl⟩) R18677
theorem R12459 : Reach 12459 := rs (se 1 (by rfl) ⟨9344, by rfl⟩) R18689
theorem R12549 : Reach 12549 := rs (se 4 (by rfl) ⟨1176, by rfl⟩) R2353
theorem R12557 : Reach 12557 := rs (se 3 (by rfl) ⟨2354, by rfl⟩) R4709
theorem R12561 : Reach 12561 := rs (se 2 (by rfl) ⟨4710, by rfl⟩) R9421
theorem R12577 : Reach 12577 := rs (se 2 (by rfl) ⟨4716, by rfl⟩) R9433
theorem R12695 : Reach 12695 := rs (se 1 (by rfl) ⟨9521, by rfl⟩) R19043
theorem R12697 : Reach 12697 := rs (se 2 (by rfl) ⟨4761, by rfl⟩) R9523
theorem R12773 : Reach 12773 := rs (se 4 (by rfl) ⟨1197, by rfl⟩) R2395
theorem R13513 : Reach 13513 := rs (se 2 (by rfl) ⟨5067, by rfl⟩) R10135
theorem R13517 : Reach 13517 := rs (se 3 (by rfl) ⟨2534, by rfl⟩) R5069
theorem R13529 : Reach 13529 := rs (se 2 (by rfl) ⟨5073, by rfl⟩) R10147
theorem R13553 : Reach 13553 := rs (se 2 (by rfl) ⟨5082, by rfl⟩) R10165
theorem R13583 : Reach 13583 := rs (se 1 (by rfl) ⟨10187, by rfl⟩) R20375
theorem R13585 : Reach 13585 := rs (se 2 (by rfl) ⟨5094, by rfl⟩) R10189
theorem R47465 : Reach 47465 := rs (se 2 (by rfl) ⟨17799, by rfl⟩) R35599
theorem R54053 : Reach 54053 := rs (se 4 (by rfl) ⟨5067, by rfl⟩) R10135
theorem R54283 : Reach 54283 := rs (se 1 (by rfl) ⟨40712, by rfl⟩) R81425
theorem R22451 : Reach 22451 := rs (se 1 (by rfl) ⟨16838, by rfl⟩) R33677
theorem R23057 : Reach 23057 := rs (se 2 (by rfl) ⟨8646, by rfl⟩) R17293
theorem R24371 : Reach 24371 := rs (se 1 (by rfl) ⟨18278, by rfl⟩) R36557
theorem R24389 : Reach 24389 := rs (se 4 (by rfl) ⟨2286, by rfl⟩) R4573
theorem R24893 : Reach 24893 := rs (se 3 (by rfl) ⟨4667, by rfl⟩) R9335
theorem R24907 : Reach 24907 := rs (se 1 (by rfl) ⟨18680, by rfl⟩) R37361
theorem R24923 : Reach 24923 := rs (se 1 (by rfl) ⟨18692, by rfl⟩) R37385
theorem R24929 : Reach 24929 := rs (se 2 (by rfl) ⟨9348, by rfl⟩) R18697
theorem R25105 : Reach 25105 := rs (se 2 (by rfl) ⟨9414, by rfl⟩) R18829
theorem R25109 : Reach 25109 := rs (se 6 (by rfl) ⟨588, by rfl⟩) R1177
theorem R25123 : Reach 25123 := rs (se 1 (by rfl) ⟨18842, by rfl⟩) R37685
theorem R25393 : Reach 25393 := rs (se 2 (by rfl) ⟨9522, by rfl⟩) R19045
theorem R27053 : Reach 27053 := rs (se 3 (by rfl) ⟨5072, by rfl⟩) R10145
theorem R27107 : Reach 27107 := rs (se 1 (by rfl) ⟨20330, by rfl⟩) R40661
theorem R27161 : Reach 27161 := rs (se 2 (by rfl) ⟨10185, by rfl⟩) R20371
theorem R27179 : Reach 27179 := rs (se 1 (by rfl) ⟨20384, by rfl⟩) R40769
theorem R94931 : Reach 94931 := rs (se 1 (by rfl) ⟨71198, by rfl⟩) R142397
theorem R97595 : Reach 97595 := rs (se 1 (by rfl) ⟨73196, by rfl⟩) R146393
theorem R57 : Reach 57 := rs (se 2 (by rfl) ⟨21, by rfl⟩) R43
theorem R59 : Reach 59 := rs (se 1 (by rfl) ⟨44, by rfl⟩) R89
theorem R115 : Reach 115 := rs (se 1 (by rfl) ⟨86, by rfl⟩) R173
theorem R32885 : Reach 32885 := rs (se 5 (by rfl) ⟨1541, by rfl⟩) R3083
theorem R119 : Reach 119 := rs (se 1 (by rfl) ⟨89, by rfl⟩) R179
theorem R229 : Reach 229 := rs (se 4 (by rfl) ⟨21, by rfl⟩) R43
theorem R237 : Reach 237 := rs (se 3 (by rfl) ⟨44, by rfl⟩) R89
theorem R33209 : Reach 33209 := rs (se 2 (by rfl) ⟨12453, by rfl⟩) R24907
theorem R461 : Reach 461 := rs (se 3 (by rfl) ⟨86, by rfl⟩) R173
theorem R465 : Reach 465 := rs (se 2 (by rfl) ⟨174, by rfl⟩) R349
theorem R473 : Reach 473 := rs (se 2 (by rfl) ⟨177, by rfl⟩) R355
theorem R477 : Reach 477 := rs (se 3 (by rfl) ⟨89, by rfl⟩) R179
theorem R507 : Reach 507 := rs (se 1 (by rfl) ⟨380, by rfl⟩) R761
theorem R513 : Reach 513 := rs (se 2 (by rfl) ⟨192, by rfl⟩) R385
theorem R33473 : Reach 33473 := rs (se 2 (by rfl) ⟨12552, by rfl⟩) R25105
theorem R33497 : Reach 33497 := rs (se 2 (by rfl) ⟨12561, by rfl⟩) R25123
theorem R917 : Reach 917 := rs (se 6 (by rfl) ⟨21, by rfl⟩) R43
theorem R931 : Reach 931 := rs (se 1 (by rfl) ⟨698, by rfl⟩) R1397
theorem R943 : Reach 943 := rs (se 1 (by rfl) ⟨707, by rfl⟩) R1415
theorem R945 : Reach 945 := rs (se 2 (by rfl) ⟨354, by rfl⟩) R709
theorem R947 : Reach 947 := rs (se 1 (by rfl) ⟨710, by rfl⟩) R1421
theorem R949 : Reach 949 := rs (se 5 (by rfl) ⟨44, by rfl⟩) R89
theorem R971 : Reach 971 := rs (se 1 (by rfl) ⟨728, by rfl⟩) R1457
theorem R987 : Reach 987 := rs (se 1 (by rfl) ⟨740, by rfl⟩) R1481
theorem R1015 : Reach 1015 := rs (se 1 (by rfl) ⟨761, by rfl⟩) R1523
theorem R1025 : Reach 1025 := rs (se 2 (by rfl) ⟨384, by rfl⟩) R769
theorem R1027 : Reach 1027 := rs (se 1 (by rfl) ⟨770, by rfl⟩) R1541
theorem R1031 : Reach 1031 := rs (se 1 (by rfl) ⟨773, by rfl⟩) R1547
theorem R33853 : Reach 33853 := rs (se 3 (by rfl) ⟨6347, by rfl⟩) R12695
theorem R33857 : Reach 33857 := rs (se 2 (by rfl) ⟨12696, by rfl⟩) R25393
theorem R1129 : Reach 1129 := rs (se 2 (by rfl) ⟨423, by rfl⟩) R847
theorem R1131 : Reach 1131 := rs (se 1 (by rfl) ⟨848, by rfl⟩) R1697
theorem R1845 : Reach 1845 := rs (se 5 (by rfl) ⟨86, by rfl⟩) R173
theorem R1857 : Reach 1857 := rs (se 2 (by rfl) ⟨696, by rfl⟩) R1393
theorem R1861 : Reach 1861 := rs (se 4 (by rfl) ⟨174, by rfl⟩) R349
theorem R1867 : Reach 1867 := rs (se 1 (by rfl) ⟨1400, by rfl⟩) R2801
theorem R1881 : Reach 1881 := rs (se 2 (by rfl) ⟨705, by rfl⟩) R1411
theorem R1887 : Reach 1887 := rs (se 1 (by rfl) ⟨1415, by rfl⟩) R2831
theorem R1891 : Reach 1891 := rs (se 1 (by rfl) ⟨1418, by rfl⟩) R2837
theorem R1893 : Reach 1893 := rs (se 4 (by rfl) ⟨177, by rfl⟩) R355
theorem R1905 : Reach 1905 := rs (se 2 (by rfl) ⟨714, by rfl⟩) R1429
theorem R1909 : Reach 1909 := rs (se 5 (by rfl) ⟨89, by rfl⟩) R179
theorem R1943 : Reach 1943 := rs (se 1 (by rfl) ⟨1457, by rfl⟩) R2915
theorem R1945 : Reach 1945 := rs (se 2 (by rfl) ⟨729, by rfl⟩) R1459
theorem R1953 : Reach 1953 := rs (se 2 (by rfl) ⟨732, by rfl⟩) R1465
theorem R1975 : Reach 1975 := rs (se 1 (by rfl) ⟨1481, by rfl⟩) R2963
theorem R2029 : Reach 2029 := rs (se 3 (by rfl) ⟨380, by rfl⟩) R761
theorem R2051 : Reach 2051 := rs (se 1 (by rfl) ⟨1538, by rfl⟩) R3077
theorem R2053 : Reach 2053 := rs (se 4 (by rfl) ⟨192, by rfl⟩) R385
theorem R2055 : Reach 2055 := rs (se 1 (by rfl) ⟨1541, by rfl⟩) R3083
theorem R2059 : Reach 2059 := rs (se 1 (by rfl) ⟨1544, by rfl⟩) R3089
theorem R2063 : Reach 2063 := rs (se 1 (by rfl) ⟨1547, by rfl⟩) R3095
theorem R2073 : Reach 2073 := rs (se 2 (by rfl) ⟨777, by rfl⟩) R1555
theorem R2091 : Reach 2091 := rs (se 1 (by rfl) ⟨1568, by rfl⟩) R3137
theorem R67715 : Reach 67715 := rs (se 1 (by rfl) ⟨50786, by rfl⟩) R101573
theorem R2251 : Reach 2251 := rs (se 1 (by rfl) ⟨1688, by rfl⟩) R3377
theorem R2257 : Reach 2257 := rs (se 2 (by rfl) ⟨846, by rfl⟩) R1693
theorem R2259 : Reach 2259 := rs (se 1 (by rfl) ⟨1694, by rfl⟩) R3389
theorem R2263 : Reach 2263 := rs (se 1 (by rfl) ⟨1697, by rfl⟩) R3395
theorem R36035 : Reach 36035 := rs (se 1 (by rfl) ⟨27026, by rfl⟩) R54053
theorem R3669 : Reach 3669 := rs (se 8 (by rfl) ⟨21, by rfl⟩) R43
theorem R3697 : Reach 3697 := rs (se 2 (by rfl) ⟨1386, by rfl⟩) R2773
theorem R3715 : Reach 3715 := rs (se 1 (by rfl) ⟨2786, by rfl⟩) R5573
theorem R3725 : Reach 3725 := rs (se 3 (by rfl) ⟨698, by rfl⟩) R1397
theorem R3735 : Reach 3735 := rs (se 1 (by rfl) ⟨2801, by rfl⟩) R5603
theorem R3761 : Reach 3761 := rs (se 2 (by rfl) ⟨1410, by rfl⟩) R2821
theorem R3763 : Reach 3763 := rs (se 1 (by rfl) ⟨2822, by rfl⟩) R5645
theorem R3773 : Reach 3773 := rs (se 3 (by rfl) ⟨707, by rfl⟩) R1415
theorem R3781 : Reach 3781 := rs (se 4 (by rfl) ⟨354, by rfl⟩) R709
theorem R3789 : Reach 3789 := rs (se 3 (by rfl) ⟨710, by rfl⟩) R1421
theorem R3797 : Reach 3797 := rs (se 7 (by rfl) ⟨44, by rfl⟩) R89
theorem R3811 : Reach 3811 := rs (se 1 (by rfl) ⟨2858, by rfl⟩) R5717
theorem R3825 : Reach 3825 := rs (se 2 (by rfl) ⟨1434, by rfl⟩) R2869
theorem R3841 : Reach 3841 := rs (se 2 (by rfl) ⟨1440, by rfl⟩) R2881
theorem R3885 : Reach 3885 := rs (se 3 (by rfl) ⟨728, by rfl⟩) R1457
theorem R3889 : Reach 3889 := rs (se 2 (by rfl) ⟨1458, by rfl⟩) R2917
theorem R3891 : Reach 3891 := rs (se 1 (by rfl) ⟨2918, by rfl⟩) R5837
theorem R3907 : Reach 3907 := rs (se 1 (by rfl) ⟨2930, by rfl⟩) R5861
theorem R3949 : Reach 3949 := rs (se 3 (by rfl) ⟨740, by rfl⟩) R1481
theorem R4061 : Reach 4061 := rs (se 3 (by rfl) ⟨761, by rfl⟩) R1523
theorem R4101 : Reach 4101 := rs (se 4 (by rfl) ⟨384, by rfl⟩) R769
theorem R4107 : Reach 4107 := rs (se 1 (by rfl) ⟨3080, by rfl⟩) R6161
theorem R4109 : Reach 4109 := rs (se 3 (by rfl) ⟨770, by rfl⟩) R1541
theorem R4111 : Reach 4111 := rs (se 1 (by rfl) ⟨3083, by rfl⟩) R6167
theorem R4113 : Reach 4113 := rs (se 2 (by rfl) ⟨1542, by rfl⟩) R3085
theorem R4119 : Reach 4119 := rs (se 1 (by rfl) ⟨3089, by rfl⟩) R6179
theorem R4125 : Reach 4125 := rs (se 3 (by rfl) ⟨773, by rfl⟩) R1547
theorem R4145 : Reach 4145 := rs (se 2 (by rfl) ⟨1554, by rfl⟩) R3109
theorem R4147 : Reach 4147 := rs (se 1 (by rfl) ⟨3110, by rfl⟩) R6221
theorem R4183 : Reach 4183 := rs (se 1 (by rfl) ⟨3137, by rfl⟩) R6275
theorem R4185 : Reach 4185 := rs (se 2 (by rfl) ⟨1569, by rfl⟩) R3139
theorem R4231 : Reach 4231 := rs (se 1 (by rfl) ⟨3173, by rfl⟩) R6347
theorem R4257 : Reach 4257 := rs (se 2 (by rfl) ⟨1596, by rfl⟩) R3193
theorem R4503 : Reach 4503 := rs (se 1 (by rfl) ⟨3377, by rfl⟩) R6755
theorem R4505 : Reach 4505 := rs (se 2 (by rfl) ⟨1689, by rfl⟩) R3379
theorem R4515 : Reach 4515 := rs (se 1 (by rfl) ⟨3386, by rfl⟩) R6773
theorem R4517 : Reach 4517 := rs (se 4 (by rfl) ⟨423, by rfl⟩) R847
theorem R4525 : Reach 4525 := rs (se 3 (by rfl) ⟨848, by rfl⟩) R1697
theorem R4527 : Reach 4527 := rs (se 1 (by rfl) ⟨3395, by rfl⟩) R6791
theorem R72377 : Reach 72377 := rs (se 2 (by rfl) ⟨27141, by rfl⟩) R54283
theorem R7381 : Reach 7381 := rs (se 7 (by rfl) ⟨86, by rfl⟩) R173
theorem R7395 : Reach 7395 := rs (se 1 (by rfl) ⟨5546, by rfl⟩) R11093
theorem R7429 : Reach 7429 := rs (se 4 (by rfl) ⟨696, by rfl⟩) R1393
theorem R7445 : Reach 7445 := rs (se 6 (by rfl) ⟨174, by rfl⟩) R349
theorem R7469 : Reach 7469 := rs (se 3 (by rfl) ⟨1400, by rfl⟩) R2801
theorem R7483 : Reach 7483 := rs (se 1 (by rfl) ⟨5612, by rfl⟩) R11225
theorem R7523 : Reach 7523 := rs (se 1 (by rfl) ⟨5642, by rfl⟩) R11285
theorem R7525 : Reach 7525 := rs (se 4 (by rfl) ⟨705, by rfl⟩) R1411
theorem R7549 : Reach 7549 := rs (se 3 (by rfl) ⟨1415, by rfl⟩) R2831
theorem R7565 : Reach 7565 := rs (se 3 (by rfl) ⟨1418, by rfl⟩) R2837
theorem R7573 : Reach 7573 := rs (se 6 (by rfl) ⟨177, by rfl⟩) R355
theorem R7621 : Reach 7621 := rs (se 4 (by rfl) ⟨714, by rfl⟩) R1429
theorem R7637 : Reach 7637 := rs (se 7 (by rfl) ⟨89, by rfl⟩) R179
theorem R7651 : Reach 7651 := rs (se 1 (by rfl) ⟨5738, by rfl⟩) R11477
theorem R7683 : Reach 7683 := rs (se 1 (by rfl) ⟨5762, by rfl⟩) R11525
theorem R7773 : Reach 7773 := rs (se 3 (by rfl) ⟨1457, by rfl⟩) R2915
theorem R7779 : Reach 7779 := rs (se 1 (by rfl) ⟨5834, by rfl⟩) R11669
theorem R7781 : Reach 7781 := rs (se 4 (by rfl) ⟨729, by rfl⟩) R1459
theorem R7813 : Reach 7813 := rs (se 4 (by rfl) ⟨732, by rfl⟩) R1465
theorem R7819 : Reach 7819 := rs (se 1 (by rfl) ⟨5864, by rfl⟩) R11729
theorem R7897 : Reach 7897 := rs (se 2 (by rfl) ⟨2961, by rfl⟩) R5923
theorem R7901 : Reach 7901 := rs (se 3 (by rfl) ⟨1481, by rfl⟩) R2963
theorem R8117 : Reach 8117 := rs (se 5 (by rfl) ⟨380, by rfl⟩) R761
theorem R8121 : Reach 8121 := rs (se 2 (by rfl) ⟨3045, by rfl⟩) R6091
theorem R8123 : Reach 8123 := rs (se 1 (by rfl) ⟨6092, by rfl⟩) R12185
theorem R8129 : Reach 8129 := rs (se 2 (by rfl) ⟨3048, by rfl⟩) R6097
theorem R8205 : Reach 8205 := rs (se 3 (by rfl) ⟨1538, by rfl⟩) R3077
theorem R8209 : Reach 8209 := rs (se 2 (by rfl) ⟨3078, by rfl⟩) R6157
theorem R8213 : Reach 8213 := rs (se 6 (by rfl) ⟨192, by rfl⟩) R385
theorem R8215 : Reach 8215 := rs (se 1 (by rfl) ⟨6161, by rfl⟩) R12323
theorem R8221 : Reach 8221 := rs (se 3 (by rfl) ⟨1541, by rfl⟩) R3083
theorem R8227 : Reach 8227 := rs (se 1 (by rfl) ⟨6170, by rfl⟩) R12341
theorem R8237 : Reach 8237 := rs (se 3 (by rfl) ⟨1544, by rfl⟩) R3089
theorem R8253 : Reach 8253 := rs (se 3 (by rfl) ⟨1547, by rfl⟩) R3095
theorem R8291 : Reach 8291 := rs (se 1 (by rfl) ⟨6218, by rfl⟩) R12437
theorem R8293 : Reach 8293 := rs (se 4 (by rfl) ⟨777, by rfl⟩) R1555
theorem R8297 : Reach 8297 := rs (se 2 (by rfl) ⟨3111, by rfl⟩) R6223
theorem R8365 : Reach 8365 := rs (se 3 (by rfl) ⟨1568, by rfl⟩) R3137
theorem R8369 : Reach 8369 := rs (se 2 (by rfl) ⟨3138, by rfl⟩) R6277
theorem R8371 : Reach 8371 := rs (se 1 (by rfl) ⟨6278, by rfl⟩) R12557
theorem R8463 : Reach 8463 := rs (se 1 (by rfl) ⟨6347, by rfl⟩) R12695
theorem R8515 : Reach 8515 := rs (se 1 (by rfl) ⟨6386, by rfl⟩) R12773
theorem R9005 : Reach 9005 := rs (se 3 (by rfl) ⟨1688, by rfl⟩) R3377
theorem R9009 : Reach 9009 := rs (se 2 (by rfl) ⟨3378, by rfl⟩) R6757
theorem R9011 : Reach 9011 := rs (se 1 (by rfl) ⟨6758, by rfl⟩) R13517
theorem R9017 : Reach 9017 := rs (se 2 (by rfl) ⟨3381, by rfl⟩) R6763
theorem R9019 : Reach 9019 := rs (se 1 (by rfl) ⟨6764, by rfl⟩) R13529
theorem R9029 : Reach 9029 := rs (se 4 (by rfl) ⟨846, by rfl⟩) R1693
theorem R9035 : Reach 9035 := rs (se 1 (by rfl) ⟨6776, by rfl⟩) R13553
theorem R9037 : Reach 9037 := rs (se 3 (by rfl) ⟨1694, by rfl⟩) R3389
theorem R9053 : Reach 9053 := rs (se 3 (by rfl) ⟨1697, by rfl⟩) R3395
theorem R9055 : Reach 9055 := rs (se 1 (by rfl) ⟨6791, by rfl⟩) R13583
theorem R144281 : Reach 144281 := rs (se 2 (by rfl) ⟨54105, by rfl⟩) R108211
theorem R14789 : Reach 14789 := rs (se 4 (by rfl) ⟨1386, by rfl⟩) R2773
theorem R14861 : Reach 14861 := rs (se 3 (by rfl) ⟨2786, by rfl⟩) R5573
theorem R15053 : Reach 15053 := rs (se 3 (by rfl) ⟨2822, by rfl⟩) R5645
theorem R15065 : Reach 15065 := rs (se 2 (by rfl) ⟨5649, by rfl⟩) R11299
theorem R15125 : Reach 15125 := rs (se 6 (by rfl) ⟨354, by rfl⟩) R709
theorem R15157 : Reach 15157 := rs (se 5 (by rfl) ⟨710, by rfl⟩) R1421
theorem R15245 : Reach 15245 := rs (se 3 (by rfl) ⟨2858, by rfl⟩) R5717
theorem R15365 : Reach 15365 := rs (se 4 (by rfl) ⟨1440, by rfl⟩) R2881
theorem R15371 : Reach 15371 := rs (se 1 (by rfl) ⟨11528, by rfl⟩) R23057
theorem R15557 : Reach 15557 := rs (se 4 (by rfl) ⟨1458, by rfl⟩) R2917
theorem R15565 : Reach 15565 := rs (se 3 (by rfl) ⟨2918, by rfl⟩) R5837
theorem R15629 : Reach 15629 := rs (se 3 (by rfl) ⟨2930, by rfl⟩) R5861
theorem R15797 : Reach 15797 := rs (se 5 (by rfl) ⟨740, by rfl⟩) R1481
theorem R16241 : Reach 16241 := rs (se 2 (by rfl) ⟨6090, by rfl⟩) R12181
theorem R16247 : Reach 16247 := rs (se 1 (by rfl) ⟨12185, by rfl⟩) R24371
theorem R16259 : Reach 16259 := rs (se 1 (by rfl) ⟨12194, by rfl⟩) R24389
theorem R16289 : Reach 16289 := rs (se 2 (by rfl) ⟨6108, by rfl⟩) R12217
theorem R16429 : Reach 16429 := rs (se 3 (by rfl) ⟨3080, by rfl⟩) R6161
theorem R16445 : Reach 16445 := rs (se 3 (by rfl) ⟨3083, by rfl⟩) R6167
theorem R16537 : Reach 16537 := rs (se 2 (by rfl) ⟨6201, by rfl⟩) R12403
theorem R16589 : Reach 16589 := rs (se 3 (by rfl) ⟨3110, by rfl⟩) R6221
theorem R16595 : Reach 16595 := rs (se 1 (by rfl) ⟨12446, by rfl⟩) R24893
theorem R16601 : Reach 16601 := rs (se 2 (by rfl) ⟨6225, by rfl⟩) R12451
theorem R16615 : Reach 16615 := rs (se 1 (by rfl) ⟨12461, by rfl⟩) R24923
theorem R16619 : Reach 16619 := rs (se 1 (by rfl) ⟨12464, by rfl⟩) R24929
theorem R16733 : Reach 16733 := rs (se 3 (by rfl) ⟨3137, by rfl⟩) R6275
theorem R16739 : Reach 16739 := rs (se 1 (by rfl) ⟨12554, by rfl⟩) R25109
theorem R16769 : Reach 16769 := rs (se 2 (by rfl) ⟨6288, by rfl⟩) R12577
theorem R16925 : Reach 16925 := rs (se 3 (by rfl) ⟨3173, by rfl⟩) R6347
theorem R18017 : Reach 18017 := rs (se 2 (by rfl) ⟨6756, by rfl⟩) R13513
theorem R18035 : Reach 18035 := rs (se 1 (by rfl) ⟨13526, by rfl⟩) R27053
theorem R18071 : Reach 18071 := rs (se 1 (by rfl) ⟨13553, by rfl⟩) R27107
theorem R18101 : Reach 18101 := rs (se 5 (by rfl) ⟨848, by rfl⟩) R1697
theorem R18107 : Reach 18107 := rs (se 1 (by rfl) ⟨13580, by rfl⟩) R27161
theorem R18113 : Reach 18113 := rs (se 2 (by rfl) ⟨6792, by rfl⟩) R13585
theorem R18119 : Reach 18119 := rs (se 1 (by rfl) ⟨13589, by rfl⟩) R27179
theorem R59869 : Reach 59869 := rs (se 3 (by rfl) ⟨11225, by rfl⟩) R22451
theorem R29717 : Reach 29717 := rs (se 6 (by rfl) ⟨696, by rfl⟩) R1393
theorem R30131 : Reach 30131 := rs (se 1 (by rfl) ⟨22598, by rfl⟩) R45197
theorem R30293 : Reach 30293 := rs (se 8 (by rfl) ⟨177, by rfl⟩) R355
theorem R63287 : Reach 63287 := rs (se 1 (by rfl) ⟨47465, by rfl⟩) R94931
theorem R31589 : Reach 31589 := rs (se 4 (by rfl) ⟨2961, by rfl⟩) R5923
theorem R31643 : Reach 31643 := rs (se 1 (by rfl) ⟨23732, by rfl⟩) R47465
theorem R65063 : Reach 65063 := rs (se 1 (by rfl) ⟨48797, by rfl⟩) R97595
theorem R39 : Reach 39 := rs (se 1 (by rfl) ⟨29, by rfl⟩) R59
theorem R79 : Reach 79 := rs (se 1 (by rfl) ⟨59, by rfl⟩) R119
theorem R153 : Reach 153 := rs (se 2 (by rfl) ⟨57, by rfl⟩) R115
theorem R157 : Reach 157 := rs (se 3 (by rfl) ⟨29, by rfl⟩) R59
theorem R305 : Reach 305 := rs (se 2 (by rfl) ⟨114, by rfl⟩) R229
theorem R307 : Reach 307 := rs (se 1 (by rfl) ⟨230, by rfl⟩) R461
theorem R315 : Reach 315 := rs (se 1 (by rfl) ⟨236, by rfl⟩) R473
theorem R317 : Reach 317 := rs (se 3 (by rfl) ⟨59, by rfl⟩) R119
theorem R611 : Reach 611 := rs (se 1 (by rfl) ⟨458, by rfl⟩) R917
theorem R613 : Reach 613 := rs (se 4 (by rfl) ⟨57, by rfl⟩) R115
theorem R629 : Reach 629 := rs (se 5 (by rfl) ⟨29, by rfl⟩) R59
theorem R631 : Reach 631 := rs (se 1 (by rfl) ⟨473, by rfl⟩) R947
theorem R647 : Reach 647 := rs (se 1 (by rfl) ⟨485, by rfl⟩) R971
theorem R683 : Reach 683 := rs (se 1 (by rfl) ⟨512, by rfl⟩) R1025
theorem R687 : Reach 687 := rs (se 1 (by rfl) ⟨515, by rfl⟩) R1031
theorem R1221 : Reach 1221 := rs (se 4 (by rfl) ⟨114, by rfl⟩) R229
theorem R1229 : Reach 1229 := rs (se 3 (by rfl) ⟨230, by rfl⟩) R461
theorem R1241 : Reach 1241 := rs (se 2 (by rfl) ⟨465, by rfl⟩) R931
theorem R1257 : Reach 1257 := rs (se 2 (by rfl) ⟨471, by rfl⟩) R943
theorem R1261 : Reach 1261 := rs (se 3 (by rfl) ⟨236, by rfl⟩) R473
theorem R1265 : Reach 1265 := rs (se 2 (by rfl) ⟨474, by rfl⟩) R949
theorem R1269 : Reach 1269 := rs (se 5 (by rfl) ⟨59, by rfl⟩) R119
theorem R1295 : Reach 1295 := rs (se 1 (by rfl) ⟨971, by rfl⟩) R1943
theorem R1353 : Reach 1353 := rs (se 2 (by rfl) ⟨507, by rfl⟩) R1015
theorem R1367 : Reach 1367 := rs (se 1 (by rfl) ⟨1025, by rfl⟩) R2051
theorem R1369 : Reach 1369 := rs (se 2 (by rfl) ⟨513, by rfl⟩) R1027
theorem R1375 : Reach 1375 := rs (se 1 (by rfl) ⟨1031, by rfl⟩) R2063
theorem R1505 : Reach 1505 := rs (se 2 (by rfl) ⟨564, by rfl⟩) R1129
theorem R2445 : Reach 2445 := rs (se 3 (by rfl) ⟨458, by rfl⟩) R917
theorem R2453 : Reach 2453 := rs (se 6 (by rfl) ⟨57, by rfl⟩) R115
theorem R2481 : Reach 2481 := rs (se 2 (by rfl) ⟨930, by rfl⟩) R1861
theorem R2483 : Reach 2483 := rs (se 1 (by rfl) ⟨1862, by rfl⟩) R3725
theorem R2489 : Reach 2489 := rs (se 2 (by rfl) ⟨933, by rfl⟩) R1867
theorem R2507 : Reach 2507 := rs (se 1 (by rfl) ⟨1880, by rfl⟩) R3761
theorem R2515 : Reach 2515 := rs (se 1 (by rfl) ⟨1886, by rfl⟩) R3773
theorem R2517 : Reach 2517 := rs (se 7 (by rfl) ⟨29, by rfl⟩) R59
theorem R2521 : Reach 2521 := rs (se 2 (by rfl) ⟨945, by rfl⟩) R1891
theorem R2525 : Reach 2525 := rs (se 3 (by rfl) ⟨473, by rfl⟩) R947
theorem R2531 : Reach 2531 := rs (se 1 (by rfl) ⟨1898, by rfl⟩) R3797
theorem R2545 : Reach 2545 := rs (se 2 (by rfl) ⟨954, by rfl⟩) R1909
theorem R2589 : Reach 2589 := rs (se 3 (by rfl) ⟨485, by rfl⟩) R971
theorem R2593 : Reach 2593 := rs (se 2 (by rfl) ⟨972, by rfl⟩) R1945
theorem R2633 : Reach 2633 := rs (se 2 (by rfl) ⟨987, by rfl⟩) R1975
theorem R2705 : Reach 2705 := rs (se 2 (by rfl) ⟨1014, by rfl⟩) R2029
theorem R2707 : Reach 2707 := rs (se 1 (by rfl) ⟨2030, by rfl⟩) R4061
theorem R2733 : Reach 2733 := rs (se 3 (by rfl) ⟨512, by rfl⟩) R1025
theorem R2737 : Reach 2737 := rs (se 2 (by rfl) ⟨1026, by rfl⟩) R2053
theorem R2739 : Reach 2739 := rs (se 1 (by rfl) ⟨2054, by rfl⟩) R4109
theorem R2745 : Reach 2745 := rs (se 2 (by rfl) ⟨1029, by rfl⟩) R2059
theorem R2749 : Reach 2749 := rs (se 3 (by rfl) ⟨515, by rfl⟩) R1031
theorem R2763 : Reach 2763 := rs (se 1 (by rfl) ⟨2072, by rfl⟩) R4145
theorem R3001 : Reach 3001 := rs (se 2 (by rfl) ⟨1125, by rfl⟩) R2251
theorem R3003 : Reach 3003 := rs (se 1 (by rfl) ⟨2252, by rfl⟩) R4505
theorem R3009 : Reach 3009 := rs (se 2 (by rfl) ⟨1128, by rfl⟩) R2257
theorem R3011 : Reach 3011 := rs (se 1 (by rfl) ⟨2258, by rfl⟩) R4517
theorem R3017 : Reach 3017 := rs (se 2 (by rfl) ⟨1131, by rfl⟩) R2263
theorem R4885 : Reach 4885 := rs (se 6 (by rfl) ⟨114, by rfl⟩) R229
theorem R4917 : Reach 4917 := rs (se 5 (by rfl) ⟨230, by rfl⟩) R461
theorem R4929 : Reach 4929 := rs (se 2 (by rfl) ⟨1848, by rfl⟩) R3697
theorem R4953 : Reach 4953 := rs (se 2 (by rfl) ⟨1857, by rfl⟩) R3715
theorem R4963 : Reach 4963 := rs (se 1 (by rfl) ⟨3722, by rfl⟩) R7445
theorem R4965 : Reach 4965 := rs (se 4 (by rfl) ⟨465, by rfl⟩) R931
theorem R4979 : Reach 4979 := rs (se 1 (by rfl) ⟨3734, by rfl⟩) R7469
theorem R5015 : Reach 5015 := rs (se 1 (by rfl) ⟨3761, by rfl⟩) R7523
theorem R5017 : Reach 5017 := rs (se 2 (by rfl) ⟨1881, by rfl⟩) R3763
theorem R5029 : Reach 5029 := rs (se 4 (by rfl) ⟨471, by rfl⟩) R943
theorem R5041 : Reach 5041 := rs (se 2 (by rfl) ⟨1890, by rfl⟩) R3781
theorem R5043 : Reach 5043 := rs (se 1 (by rfl) ⟨3782, by rfl⟩) R7565
theorem R5045 : Reach 5045 := rs (se 5 (by rfl) ⟨236, by rfl⟩) R473
theorem R5061 : Reach 5061 := rs (se 4 (by rfl) ⟨474, by rfl⟩) R949
theorem R5077 : Reach 5077 := rs (se 7 (by rfl) ⟨59, by rfl⟩) R119
theorem R5081 : Reach 5081 := rs (se 2 (by rfl) ⟨1905, by rfl⟩) R3811
theorem R5091 : Reach 5091 := rs (se 1 (by rfl) ⟨3818, by rfl⟩) R7637
theorem R5121 : Reach 5121 := rs (se 2 (by rfl) ⟨1920, by rfl⟩) R3841
theorem R5181 : Reach 5181 := rs (se 3 (by rfl) ⟨971, by rfl⟩) R1943
theorem R5185 : Reach 5185 := rs (se 2 (by rfl) ⟨1944, by rfl⟩) R3889
theorem R5187 : Reach 5187 := rs (se 1 (by rfl) ⟨3890, by rfl⟩) R7781
theorem R5209 : Reach 5209 := rs (se 2 (by rfl) ⟨1953, by rfl⟩) R3907
theorem R5265 : Reach 5265 := rs (se 2 (by rfl) ⟨1974, by rfl⟩) R3949
theorem R5267 : Reach 5267 := rs (se 1 (by rfl) ⟨3950, by rfl⟩) R7901
theorem R5411 : Reach 5411 := rs (se 1 (by rfl) ⟨4058, by rfl⟩) R8117
theorem R5413 : Reach 5413 := rs (se 4 (by rfl) ⟨507, by rfl⟩) R1015
theorem R5415 : Reach 5415 := rs (se 1 (by rfl) ⟨4061, by rfl⟩) R8123
theorem R5419 : Reach 5419 := rs (se 1 (by rfl) ⟨4064, by rfl⟩) R8129
theorem R5469 : Reach 5469 := rs (se 3 (by rfl) ⟨1025, by rfl⟩) R2051
theorem R5475 : Reach 5475 := rs (se 1 (by rfl) ⟨4106, by rfl⟩) R8213
theorem R5477 : Reach 5477 := rs (se 4 (by rfl) ⟨513, by rfl⟩) R1027
theorem R5481 : Reach 5481 := rs (se 2 (by rfl) ⟨2055, by rfl⟩) R4111
theorem R5491 : Reach 5491 := rs (se 1 (by rfl) ⟨4118, by rfl⟩) R8237
theorem R5501 : Reach 5501 := rs (se 3 (by rfl) ⟨1031, by rfl⟩) R2063
theorem R5527 : Reach 5527 := rs (se 1 (by rfl) ⟨4145, by rfl⟩) R8291
theorem R5529 : Reach 5529 := rs (se 2 (by rfl) ⟨2073, by rfl⟩) R4147
theorem R5531 : Reach 5531 := rs (se 1 (by rfl) ⟨4148, by rfl⟩) R8297
theorem R5577 : Reach 5577 := rs (se 2 (by rfl) ⟨2091, by rfl⟩) R4183
theorem R5579 : Reach 5579 := rs (se 1 (by rfl) ⟨4184, by rfl⟩) R8369
theorem R5641 : Reach 5641 := rs (se 2 (by rfl) ⟨2115, by rfl⟩) R4231
theorem R6003 : Reach 6003 := rs (se 1 (by rfl) ⟨4502, by rfl⟩) R9005
theorem R6007 : Reach 6007 := rs (se 1 (by rfl) ⟨4505, by rfl⟩) R9011
theorem R6011 : Reach 6011 := rs (se 1 (by rfl) ⟨4508, by rfl⟩) R9017
theorem R6019 : Reach 6019 := rs (se 1 (by rfl) ⟨4514, by rfl⟩) R9029
theorem R6021 : Reach 6021 := rs (se 4 (by rfl) ⟨564, by rfl⟩) R1129
theorem R6023 : Reach 6023 := rs (se 1 (by rfl) ⟨4517, by rfl⟩) R9035
theorem R6033 : Reach 6033 := rs (se 2 (by rfl) ⟨2262, by rfl⟩) R4525
theorem R6035 : Reach 6035 := rs (se 1 (by rfl) ⟨4526, by rfl⟩) R9053
theorem R39365 : Reach 39365 := rs (se 4 (by rfl) ⟨3690, by rfl⟩) R7381
theorem R40277 : Reach 40277 := rs (se 11 (by rfl) ⟨29, by rfl⟩) R59
theorem R41485 : Reach 41485 := rs (se 3 (by rfl) ⟨7778, by rfl⟩) R15557
theorem R42191 : Reach 42191 := rs (se 1 (by rfl) ⟨31643, by rfl⟩) R63287
theorem R9781 : Reach 9781 := rs (se 5 (by rfl) ⟨458, by rfl⟩) R917
theorem R9813 : Reach 9813 := rs (se 8 (by rfl) ⟨57, by rfl⟩) R115
theorem R9841 : Reach 9841 := rs (se 2 (by rfl) ⟨3690, by rfl⟩) R7381
theorem R9859 : Reach 9859 := rs (se 1 (by rfl) ⟨7394, by rfl⟩) R14789
theorem R9905 : Reach 9905 := rs (se 2 (by rfl) ⟨3714, by rfl⟩) R7429
theorem R9907 : Reach 9907 := rs (se 1 (by rfl) ⟨7430, by rfl⟩) R14861
theorem R9925 : Reach 9925 := rs (se 4 (by rfl) ⟨930, by rfl⟩) R1861
theorem R9933 : Reach 9933 := rs (se 3 (by rfl) ⟨1862, by rfl⟩) R3725
theorem R9957 : Reach 9957 := rs (se 4 (by rfl) ⟨933, by rfl⟩) R1867
theorem R9977 : Reach 9977 := rs (se 2 (by rfl) ⟨3741, by rfl⟩) R7483
theorem R10029 : Reach 10029 := rs (se 3 (by rfl) ⟨1880, by rfl⟩) R3761
theorem R10033 : Reach 10033 := rs (se 2 (by rfl) ⟨3762, by rfl⟩) R7525
theorem R10035 : Reach 10035 := rs (se 1 (by rfl) ⟨7526, by rfl⟩) R15053
theorem R10043 : Reach 10043 := rs (se 1 (by rfl) ⟨7532, by rfl⟩) R15065
theorem R10061 : Reach 10061 := rs (se 3 (by rfl) ⟨1886, by rfl⟩) R3773
theorem R10065 : Reach 10065 := rs (se 2 (by rfl) ⟨3774, by rfl⟩) R7549
theorem R10069 : Reach 10069 := rs (se 9 (by rfl) ⟨29, by rfl⟩) R59
theorem R10083 : Reach 10083 := rs (se 1 (by rfl) ⟨7562, by rfl⟩) R15125
theorem R10085 : Reach 10085 := rs (se 4 (by rfl) ⟨945, by rfl⟩) R1891
theorem R10097 : Reach 10097 := rs (se 2 (by rfl) ⟨3786, by rfl⟩) R7573
theorem R10101 : Reach 10101 := rs (se 5 (by rfl) ⟨473, by rfl⟩) R947
theorem R10125 : Reach 10125 := rs (se 3 (by rfl) ⟨1898, by rfl⟩) R3797
theorem R10161 : Reach 10161 := rs (se 2 (by rfl) ⟨3810, by rfl⟩) R7621
theorem R10163 : Reach 10163 := rs (se 1 (by rfl) ⟨7622, by rfl⟩) R15245
theorem R10181 : Reach 10181 := rs (se 4 (by rfl) ⟨954, by rfl⟩) R1909
theorem R10201 : Reach 10201 := rs (se 2 (by rfl) ⟨3825, by rfl⟩) R7651
theorem R10243 : Reach 10243 := rs (se 1 (by rfl) ⟨7682, by rfl⟩) R15365
theorem R10247 : Reach 10247 := rs (se 1 (by rfl) ⟨7685, by rfl⟩) R15371
theorem R10357 : Reach 10357 := rs (se 5 (by rfl) ⟨485, by rfl⟩) R971
theorem R10371 : Reach 10371 := rs (se 1 (by rfl) ⟨7778, by rfl⟩) R15557
theorem R10373 : Reach 10373 := rs (se 4 (by rfl) ⟨972, by rfl⟩) R1945
theorem R10417 : Reach 10417 := rs (se 2 (by rfl) ⟨3906, by rfl⟩) R7813
theorem R10419 : Reach 10419 := rs (se 1 (by rfl) ⟨7814, by rfl⟩) R15629
theorem R10425 : Reach 10425 := rs (se 2 (by rfl) ⟨3909, by rfl⟩) R7819
theorem R10529 : Reach 10529 := rs (se 2 (by rfl) ⟨3948, by rfl⟩) R7897
theorem R10531 : Reach 10531 := rs (se 1 (by rfl) ⟨7898, by rfl⟩) R15797
theorem R10533 : Reach 10533 := rs (se 4 (by rfl) ⟨987, by rfl⟩) R1975
theorem R43375 : Reach 43375 := rs (se 1 (by rfl) ⟨32531, by rfl⟩) R65063
theorem R10821 : Reach 10821 := rs (se 4 (by rfl) ⟨1014, by rfl⟩) R2029
theorem R10827 : Reach 10827 := rs (se 1 (by rfl) ⟨8120, by rfl⟩) R16241
theorem R10829 : Reach 10829 := rs (se 3 (by rfl) ⟨2030, by rfl⟩) R4061
theorem R10831 : Reach 10831 := rs (se 1 (by rfl) ⟨8123, by rfl⟩) R16247
theorem R10839 : Reach 10839 := rs (se 1 (by rfl) ⟨8129, by rfl⟩) R16259
theorem R10859 : Reach 10859 := rs (se 1 (by rfl) ⟨8144, by rfl⟩) R16289
theorem R10933 : Reach 10933 := rs (se 5 (by rfl) ⟨512, by rfl⟩) R1025
theorem R10945 : Reach 10945 := rs (se 2 (by rfl) ⟨4104, by rfl⟩) R8209
theorem R10949 : Reach 10949 := rs (se 4 (by rfl) ⟨1026, by rfl⟩) R2053
theorem R10953 : Reach 10953 := rs (se 2 (by rfl) ⟨4107, by rfl⟩) R8215
theorem R10957 : Reach 10957 := rs (se 3 (by rfl) ⟨2054, by rfl⟩) R4109
theorem R10961 : Reach 10961 := rs (se 2 (by rfl) ⟨4110, by rfl⟩) R8221
theorem R10963 : Reach 10963 := rs (se 1 (by rfl) ⟨8222, by rfl⟩) R16445
theorem R10969 : Reach 10969 := rs (se 2 (by rfl) ⟨4113, by rfl⟩) R8227
theorem R10981 : Reach 10981 := rs (se 4 (by rfl) ⟨1029, by rfl⟩) R2059
theorem R10997 : Reach 10997 := rs (se 5 (by rfl) ⟨515, by rfl⟩) R1031
theorem R11053 : Reach 11053 := rs (se 3 (by rfl) ⟨2072, by rfl⟩) R4145
theorem R11057 : Reach 11057 := rs (se 2 (by rfl) ⟨4146, by rfl⟩) R8293
theorem R11059 : Reach 11059 := rs (se 1 (by rfl) ⟨8294, by rfl⟩) R16589
theorem R11063 : Reach 11063 := rs (se 1 (by rfl) ⟨8297, by rfl⟩) R16595
theorem R11067 : Reach 11067 := rs (se 1 (by rfl) ⟨8300, by rfl⟩) R16601
theorem R11079 : Reach 11079 := rs (se 1 (by rfl) ⟨8309, by rfl⟩) R16619
theorem R43877 : Reach 43877 := rs (se 4 (by rfl) ⟨4113, by rfl⟩) R8227
theorem R11153 : Reach 11153 := rs (se 2 (by rfl) ⟨4182, by rfl⟩) R8365
theorem R11155 : Reach 11155 := rs (se 1 (by rfl) ⟨8366, by rfl⟩) R16733
theorem R11159 : Reach 11159 := rs (se 1 (by rfl) ⟨8369, by rfl⟩) R16739
theorem R11161 : Reach 11161 := rs (se 2 (by rfl) ⟨4185, by rfl⟩) R8371
theorem R11179 : Reach 11179 := rs (se 1 (by rfl) ⟨8384, by rfl⟩) R16769
theorem R11283 : Reach 11283 := rs (se 1 (by rfl) ⟨8462, by rfl⟩) R16925
theorem R11353 : Reach 11353 := rs (se 2 (by rfl) ⟨4257, by rfl⟩) R8515
theorem R44621 : Reach 44621 := rs (se 3 (by rfl) ⟨8366, by rfl⟩) R16733
theorem R12005 : Reach 12005 := rs (se 4 (by rfl) ⟨1125, by rfl⟩) R2251
theorem R12011 : Reach 12011 := rs (se 1 (by rfl) ⟨9008, by rfl⟩) R18017
theorem R12013 : Reach 12013 := rs (se 3 (by rfl) ⟨2252, by rfl⟩) R4505
theorem R12023 : Reach 12023 := rs (se 1 (by rfl) ⟨9017, by rfl⟩) R18035
theorem R12025 : Reach 12025 := rs (se 2 (by rfl) ⟨4509, by rfl⟩) R9019
theorem R12037 : Reach 12037 := rs (se 4 (by rfl) ⟨1128, by rfl⟩) R2257
theorem R12045 : Reach 12045 := rs (se 3 (by rfl) ⟨2258, by rfl⟩) R4517
theorem R12047 : Reach 12047 := rs (se 1 (by rfl) ⟨9035, by rfl⟩) R18071
theorem R12049 : Reach 12049 := rs (se 2 (by rfl) ⟨4518, by rfl⟩) R9037
theorem R12067 : Reach 12067 := rs (se 1 (by rfl) ⟨9050, by rfl⟩) R18101
theorem R12069 : Reach 12069 := rs (se 4 (by rfl) ⟨1131, by rfl⟩) R2263
theorem R12071 : Reach 12071 := rs (se 1 (by rfl) ⟨9053, by rfl⟩) R18107
theorem R12073 : Reach 12073 := rs (se 2 (by rfl) ⟨4527, by rfl⟩) R9055
theorem R12075 : Reach 12075 := rs (se 1 (by rfl) ⟨9056, by rfl⟩) R18113
theorem R12079 : Reach 12079 := rs (se 1 (by rfl) ⟨9059, by rfl⟩) R18119
theorem R45137 : Reach 45137 := rs (se 2 (by rfl) ⟨16926, by rfl⟩) R33853
theorem R45143 : Reach 45143 := rs (se 1 (by rfl) ⟨33857, by rfl⟩) R67715
theorem R45413 : Reach 45413 := rs (se 4 (by rfl) ⟨4257, by rfl⟩) R8515
theorem R79825 : Reach 79825 := rs (se 2 (by rfl) ⟨29934, by rfl⟩) R59869
theorem R48053 : Reach 48053 := rs (se 5 (by rfl) ⟨2252, by rfl⟩) R4505
theorem R80837 : Reach 80837 := rs (se 4 (by rfl) ⟨7578, by rfl⟩) R15157
theorem R48251 : Reach 48251 := rs (se 1 (by rfl) ⟨36188, by rfl⟩) R72377
theorem R19541 : Reach 19541 := rs (se 8 (by rfl) ⟨114, by rfl⟩) R229
theorem R19669 : Reach 19669 := rs (se 7 (by rfl) ⟨230, by rfl⟩) R461
theorem R19811 : Reach 19811 := rs (se 1 (by rfl) ⟨14858, by rfl⟩) R29717
theorem R19853 : Reach 19853 := rs (se 3 (by rfl) ⟨3722, by rfl⟩) R7445
theorem R20069 : Reach 20069 := rs (se 4 (by rfl) ⟨1881, by rfl⟩) R3763
theorem R20087 : Reach 20087 := rs (se 1 (by rfl) ⟨15065, by rfl⟩) R30131
theorem R20195 : Reach 20195 := rs (se 1 (by rfl) ⟨15146, by rfl⟩) R30293
theorem R20209 : Reach 20209 := rs (se 2 (by rfl) ⟨7578, by rfl⟩) R15157
theorem R20245 : Reach 20245 := rs (se 6 (by rfl) ⟨474, by rfl⟩) R949
theorem R20749 : Reach 20749 := rs (se 3 (by rfl) ⟨3890, by rfl⟩) R7781
theorem R20753 : Reach 20753 := rs (se 2 (by rfl) ⟨7782, by rfl⟩) R15565
theorem R20837 : Reach 20837 := rs (se 4 (by rfl) ⟨1953, by rfl⟩) R3907
theorem R21059 : Reach 21059 := rs (se 1 (by rfl) ⟨15794, by rfl⟩) R31589
theorem R21061 : Reach 21061 := rs (se 4 (by rfl) ⟨1974, by rfl⟩) R3949
theorem R21095 : Reach 21095 := rs (se 1 (by rfl) ⟨15821, by rfl⟩) R31643
theorem R21653 : Reach 21653 := rs (se 6 (by rfl) ⟨507, by rfl⟩) R1015
theorem R21905 : Reach 21905 := rs (se 2 (by rfl) ⟨8214, by rfl⟩) R16429
theorem R21923 : Reach 21923 := rs (se 1 (by rfl) ⟨16442, by rfl⟩) R32885
theorem R22049 : Reach 22049 := rs (se 2 (by rfl) ⟨8268, by rfl⟩) R16537
theorem R22139 : Reach 22139 := rs (se 1 (by rfl) ⟨16604, by rfl⟩) R33209
theorem R22153 : Reach 22153 := rs (se 2 (by rfl) ⟨8307, by rfl⟩) R16615
theorem R22315 : Reach 22315 := rs (se 1 (by rfl) ⟨16736, by rfl⟩) R33473
theorem R22331 : Reach 22331 := rs (se 1 (by rfl) ⟨16748, by rfl⟩) R33497
theorem R22571 : Reach 22571 := rs (se 1 (by rfl) ⟨16928, by rfl⟩) R33857
theorem R24023 : Reach 24023 := rs (se 1 (by rfl) ⟨18017, by rfl⟩) R36035
theorem R24029 : Reach 24029 := rs (se 3 (by rfl) ⟨4505, by rfl⟩) R9011
theorem R24077 : Reach 24077 := rs (se 3 (by rfl) ⟨4514, by rfl⟩) R9029
theorem R24133 : Reach 24133 := rs (se 4 (by rfl) ⟨2262, by rfl⟩) R4525
theorem R96187 : Reach 96187 := rs (se 1 (by rfl) ⟨72140, by rfl⟩) R144281
theorem R105 : Reach 105 := rs (se 2 (by rfl) ⟨39, by rfl⟩) R79
theorem R203 : Reach 203 := rs (se 1 (by rfl) ⟨152, by rfl⟩) R305
theorem R209 : Reach 209 := rs (se 2 (by rfl) ⟨78, by rfl⟩) R157
theorem R211 : Reach 211 := rs (se 1 (by rfl) ⟨158, by rfl⟩) R317
theorem R407 : Reach 407 := rs (se 1 (by rfl) ⟨305, by rfl⟩) R611
theorem R409 : Reach 409 := rs (se 2 (by rfl) ⟨153, by rfl⟩) R307
theorem R419 : Reach 419 := rs (se 1 (by rfl) ⟨314, by rfl⟩) R629
theorem R421 : Reach 421 := rs (se 4 (by rfl) ⟨39, by rfl⟩) R79
theorem R431 : Reach 431 := rs (se 1 (by rfl) ⟨323, by rfl⟩) R647
theorem R455 : Reach 455 := rs (se 1 (by rfl) ⟨341, by rfl⟩) R683
theorem R813 : Reach 813 := rs (se 3 (by rfl) ⟨152, by rfl⟩) R305
theorem R817 : Reach 817 := rs (se 2 (by rfl) ⟨306, by rfl⟩) R613
theorem R819 : Reach 819 := rs (se 1 (by rfl) ⟨614, by rfl⟩) R1229
theorem R827 : Reach 827 := rs (se 1 (by rfl) ⟨620, by rfl⟩) R1241
theorem R837 : Reach 837 := rs (se 4 (by rfl) ⟨78, by rfl⟩) R157
theorem R841 : Reach 841 := rs (se 2 (by rfl) ⟨315, by rfl⟩) R631
theorem R843 : Reach 843 := rs (se 1 (by rfl) ⟨632, by rfl⟩) R1265
theorem R845 : Reach 845 := rs (se 3 (by rfl) ⟨158, by rfl⟩) R317
theorem R863 : Reach 863 := rs (se 1 (by rfl) ⟨647, by rfl⟩) R1295
theorem R911 : Reach 911 := rs (se 1 (by rfl) ⟨683, by rfl⟩) R1367
theorem R1003 : Reach 1003 := rs (se 1 (by rfl) ⟨752, by rfl⟩) R1505
theorem R1629 : Reach 1629 := rs (se 3 (by rfl) ⟨305, by rfl⟩) R611
theorem R1635 : Reach 1635 := rs (se 1 (by rfl) ⟨1226, by rfl⟩) R2453
theorem R1637 : Reach 1637 := rs (se 4 (by rfl) ⟨153, by rfl⟩) R307
theorem R1655 : Reach 1655 := rs (se 1 (by rfl) ⟨1241, by rfl⟩) R2483
theorem R1659 : Reach 1659 := rs (se 1 (by rfl) ⟨1244, by rfl⟩) R2489
theorem R1671 : Reach 1671 := rs (se 1 (by rfl) ⟨1253, by rfl⟩) R2507
theorem R1677 : Reach 1677 := rs (se 3 (by rfl) ⟨314, by rfl⟩) R629
theorem R1681 : Reach 1681 := rs (se 2 (by rfl) ⟨630, by rfl⟩) R1261
theorem R1683 : Reach 1683 := rs (se 1 (by rfl) ⟨1262, by rfl⟩) R2525
theorem R1685 : Reach 1685 := rs (se 6 (by rfl) ⟨39, by rfl⟩) R79
theorem R1687 : Reach 1687 := rs (se 1 (by rfl) ⟨1265, by rfl⟩) R2531
theorem R1725 : Reach 1725 := rs (se 3 (by rfl) ⟨323, by rfl⟩) R647
theorem R1755 : Reach 1755 := rs (se 1 (by rfl) ⟨1316, by rfl⟩) R2633
theorem R1803 : Reach 1803 := rs (se 1 (by rfl) ⟨1352, by rfl⟩) R2705
theorem R1821 : Reach 1821 := rs (se 3 (by rfl) ⟨341, by rfl⟩) R683
theorem R1825 : Reach 1825 := rs (se 2 (by rfl) ⟨684, by rfl⟩) R1369
theorem R1833 : Reach 1833 := rs (se 2 (by rfl) ⟨687, by rfl⟩) R1375
theorem R2007 : Reach 2007 := rs (se 1 (by rfl) ⟨1505, by rfl⟩) R3011
theorem R2011 : Reach 2011 := rs (se 1 (by rfl) ⟨1508, by rfl⟩) R3017
theorem R3253 : Reach 3253 := rs (se 5 (by rfl) ⟨152, by rfl⟩) R305
theorem R3269 : Reach 3269 := rs (se 4 (by rfl) ⟨306, by rfl⟩) R613
theorem R3277 : Reach 3277 := rs (se 3 (by rfl) ⟨614, by rfl⟩) R1229
theorem R3309 : Reach 3309 := rs (se 3 (by rfl) ⟨620, by rfl⟩) R1241
theorem R3319 : Reach 3319 := rs (se 1 (by rfl) ⟨2489, by rfl⟩) R4979
theorem R3343 : Reach 3343 := rs (se 1 (by rfl) ⟨2507, by rfl⟩) R5015
theorem R3349 : Reach 3349 := rs (se 6 (by rfl) ⟨78, by rfl⟩) R157
theorem R3353 : Reach 3353 := rs (se 2 (by rfl) ⟨1257, by rfl⟩) R2515
theorem R3361 : Reach 3361 := rs (se 2 (by rfl) ⟨1260, by rfl⟩) R2521
theorem R3363 : Reach 3363 := rs (se 1 (by rfl) ⟨2522, by rfl⟩) R5045
theorem R3365 : Reach 3365 := rs (se 4 (by rfl) ⟨315, by rfl⟩) R631
theorem R3373 : Reach 3373 := rs (se 3 (by rfl) ⟨632, by rfl⟩) R1265
theorem R3381 : Reach 3381 := rs (se 5 (by rfl) ⟨158, by rfl⟩) R317
theorem R3387 : Reach 3387 := rs (se 1 (by rfl) ⟨2540, by rfl⟩) R5081
theorem R3393 : Reach 3393 := rs (se 2 (by rfl) ⟨1272, by rfl⟩) R2545
theorem R3453 : Reach 3453 := rs (se 3 (by rfl) ⟨647, by rfl⟩) R1295
theorem R3457 : Reach 3457 := rs (se 2 (by rfl) ⟨1296, by rfl⟩) R2593
theorem R3511 : Reach 3511 := rs (se 1 (by rfl) ⟨2633, by rfl⟩) R5267
theorem R3607 : Reach 3607 := rs (se 1 (by rfl) ⟨2705, by rfl⟩) R5411
theorem R3609 : Reach 3609 := rs (se 2 (by rfl) ⟨1353, by rfl⟩) R2707
theorem R3645 : Reach 3645 := rs (se 3 (by rfl) ⟨683, by rfl⟩) R1367
theorem R3649 : Reach 3649 := rs (se 2 (by rfl) ⟨1368, by rfl⟩) R2737
theorem R3651 : Reach 3651 := rs (se 1 (by rfl) ⟨2738, by rfl⟩) R5477
theorem R3665 : Reach 3665 := rs (se 2 (by rfl) ⟨1374, by rfl⟩) R2749
theorem R3667 : Reach 3667 := rs (se 1 (by rfl) ⟨2750, by rfl⟩) R5501
theorem R3687 : Reach 3687 := rs (se 1 (by rfl) ⟨2765, by rfl⟩) R5531
theorem R3719 : Reach 3719 := rs (se 1 (by rfl) ⟨2789, by rfl⟩) R5579
theorem R4001 : Reach 4001 := rs (se 2 (by rfl) ⟨1500, by rfl⟩) R3001
theorem R4007 : Reach 4007 := rs (se 1 (by rfl) ⟨3005, by rfl⟩) R6011
theorem R4013 : Reach 4013 := rs (se 3 (by rfl) ⟨752, by rfl⟩) R1505
theorem R4015 : Reach 4015 := rs (se 1 (by rfl) ⟨3011, by rfl⟩) R6023
theorem R4023 : Reach 4023 := rs (se 1 (by rfl) ⟨3017, by rfl⟩) R6035
theorem R6513 : Reach 6513 := rs (se 2 (by rfl) ⟨2442, by rfl⟩) R4885
theorem R6517 : Reach 6517 := rs (se 5 (by rfl) ⟨305, by rfl⟩) R611
theorem R6541 : Reach 6541 := rs (se 3 (by rfl) ⟨1226, by rfl⟩) R2453
theorem R6549 : Reach 6549 := rs (se 6 (by rfl) ⟨153, by rfl⟩) R307
theorem R6603 : Reach 6603 := rs (se 1 (by rfl) ⟨4952, by rfl⟩) R9905
theorem R6617 : Reach 6617 := rs (se 2 (by rfl) ⟨2481, by rfl⟩) R4963
theorem R6621 : Reach 6621 := rs (se 3 (by rfl) ⟨1241, by rfl⟩) R2483
theorem R6637 : Reach 6637 := rs (se 3 (by rfl) ⟨1244, by rfl⟩) R2489
theorem R6651 : Reach 6651 := rs (se 1 (by rfl) ⟨4988, by rfl⟩) R9977
theorem R6685 : Reach 6685 := rs (se 3 (by rfl) ⟨1253, by rfl⟩) R2507
theorem R6689 : Reach 6689 := rs (se 2 (by rfl) ⟨2508, by rfl⟩) R5017
theorem R6695 : Reach 6695 := rs (se 1 (by rfl) ⟨5021, by rfl⟩) R10043
theorem R6705 : Reach 6705 := rs (se 2 (by rfl) ⟨2514, by rfl⟩) R5029
theorem R6707 : Reach 6707 := rs (se 1 (by rfl) ⟨5030, by rfl⟩) R10061
theorem R6709 : Reach 6709 := rs (se 5 (by rfl) ⟨314, by rfl⟩) R629
theorem R6721 : Reach 6721 := rs (se 2 (by rfl) ⟨2520, by rfl⟩) R5041
theorem R6723 : Reach 6723 := rs (se 1 (by rfl) ⟨5042, by rfl⟩) R10085
theorem R6725 : Reach 6725 := rs (se 4 (by rfl) ⟨630, by rfl⟩) R1261
theorem R6731 : Reach 6731 := rs (se 1 (by rfl) ⟨5048, by rfl⟩) R10097
theorem R6733 : Reach 6733 := rs (se 3 (by rfl) ⟨1262, by rfl⟩) R2525
theorem R6741 : Reach 6741 := rs (se 8 (by rfl) ⟨39, by rfl⟩) R79
theorem R6749 : Reach 6749 := rs (se 3 (by rfl) ⟨1265, by rfl⟩) R2531
theorem R6769 : Reach 6769 := rs (se 2 (by rfl) ⟨2538, by rfl⟩) R5077
theorem R6775 : Reach 6775 := rs (se 1 (by rfl) ⟨5081, by rfl⟩) R10163
theorem R6787 : Reach 6787 := rs (se 1 (by rfl) ⟨5090, by rfl⟩) R10181
theorem R6831 : Reach 6831 := rs (se 1 (by rfl) ⟨5123, by rfl⟩) R10247
theorem R6901 : Reach 6901 := rs (se 5 (by rfl) ⟨323, by rfl⟩) R647
theorem R6913 : Reach 6913 := rs (se 2 (by rfl) ⟨2592, by rfl⟩) R5185
theorem R6915 : Reach 6915 := rs (se 1 (by rfl) ⟨5186, by rfl⟩) R10373
theorem R6945 : Reach 6945 := rs (se 2 (by rfl) ⟨2604, by rfl⟩) R5209
theorem R7019 : Reach 7019 := rs (se 1 (by rfl) ⟨5264, by rfl⟩) R10529
theorem R7021 : Reach 7021 := rs (se 3 (by rfl) ⟨1316, by rfl⟩) R2633
theorem R7213 : Reach 7213 := rs (se 3 (by rfl) ⟨1352, by rfl⟩) R2705
theorem R7217 : Reach 7217 := rs (se 2 (by rfl) ⟨2706, by rfl⟩) R5413
theorem R7219 : Reach 7219 := rs (se 1 (by rfl) ⟨5414, by rfl⟩) R10829
theorem R7225 : Reach 7225 := rs (se 2 (by rfl) ⟨2709, by rfl⟩) R5419
theorem R7239 : Reach 7239 := rs (se 1 (by rfl) ⟨5429, by rfl⟩) R10859
theorem R7285 : Reach 7285 := rs (se 5 (by rfl) ⟨341, by rfl⟩) R683
theorem R7299 : Reach 7299 := rs (se 1 (by rfl) ⟨5474, by rfl⟩) R10949
theorem R7301 : Reach 7301 := rs (se 4 (by rfl) ⟨684, by rfl⟩) R1369
theorem R7307 : Reach 7307 := rs (se 1 (by rfl) ⟨5480, by rfl⟩) R10961
theorem R7321 : Reach 7321 := rs (se 2 (by rfl) ⟨2745, by rfl⟩) R5491
theorem R7331 : Reach 7331 := rs (se 1 (by rfl) ⟨5498, by rfl⟩) R10997
theorem R7333 : Reach 7333 := rs (se 4 (by rfl) ⟨687, by rfl⟩) R1375
theorem R7369 : Reach 7369 := rs (se 2 (by rfl) ⟨2763, by rfl⟩) R5527
theorem R7371 : Reach 7371 := rs (se 1 (by rfl) ⟨5528, by rfl⟩) R11057
theorem R7375 : Reach 7375 := rs (se 1 (by rfl) ⟨5531, by rfl⟩) R11063
theorem R7435 : Reach 7435 := rs (se 1 (by rfl) ⟨5576, by rfl⟩) R11153
theorem R7439 : Reach 7439 := rs (se 1 (by rfl) ⟨5579, by rfl⟩) R11159
theorem R7521 : Reach 7521 := rs (se 2 (by rfl) ⟨2820, by rfl⟩) R5641
theorem R8003 : Reach 8003 := rs (se 1 (by rfl) ⟨6002, by rfl⟩) R12005
theorem R8007 : Reach 8007 := rs (se 1 (by rfl) ⟨6005, by rfl⟩) R12011
theorem R8009 : Reach 8009 := rs (se 2 (by rfl) ⟨3003, by rfl⟩) R6007
theorem R8015 : Reach 8015 := rs (se 1 (by rfl) ⟨6011, by rfl⟩) R12023
theorem R8025 : Reach 8025 := rs (se 2 (by rfl) ⟨3009, by rfl⟩) R6019
theorem R8029 : Reach 8029 := rs (se 3 (by rfl) ⟨1505, by rfl⟩) R3011
theorem R8031 : Reach 8031 := rs (se 1 (by rfl) ⟨6023, by rfl⟩) R12047
theorem R8045 : Reach 8045 := rs (se 3 (by rfl) ⟨1508, by rfl⟩) R3017
theorem R8047 : Reach 8047 := rs (se 1 (by rfl) ⟨6035, by rfl⟩) R12071
theorem R106433 : Reach 106433 := rs (se 2 (by rfl) ⟨39912, by rfl⟩) R79825
theorem R107405 : Reach 107405 := rs (se 3 (by rfl) ⟨20138, by rfl⟩) R40277
theorem R13013 : Reach 13013 := rs (se 7 (by rfl) ⟨152, by rfl⟩) R305
theorem R13027 : Reach 13027 := rs (se 1 (by rfl) ⟨9770, by rfl⟩) R19541
theorem R13109 : Reach 13109 := rs (se 5 (by rfl) ⟨614, by rfl⟩) R1229
theorem R13121 : Reach 13121 := rs (se 2 (by rfl) ⟨4920, by rfl⟩) R9841
theorem R13145 : Reach 13145 := rs (se 2 (by rfl) ⟨4929, by rfl⟩) R9859
theorem R13207 : Reach 13207 := rs (se 1 (by rfl) ⟨9905, by rfl⟩) R19811
theorem R13235 : Reach 13235 := rs (se 1 (by rfl) ⟨9926, by rfl⟩) R19853
theorem R13277 : Reach 13277 := rs (se 3 (by rfl) ⟨2489, by rfl⟩) R4979
theorem R13373 : Reach 13373 := rs (se 3 (by rfl) ⟨2507, by rfl⟩) R5015
theorem R13379 : Reach 13379 := rs (se 1 (by rfl) ⟨10034, by rfl⟩) R20069
theorem R13391 : Reach 13391 := rs (se 1 (by rfl) ⟨10043, by rfl⟩) R20087
theorem R13397 : Reach 13397 := rs (se 8 (by rfl) ⟨78, by rfl⟩) R157
theorem R13445 : Reach 13445 := rs (se 4 (by rfl) ⟨1260, by rfl⟩) R2521
theorem R13463 : Reach 13463 := rs (se 1 (by rfl) ⟨10097, by rfl⟩) R20195
theorem R13493 : Reach 13493 := rs (se 5 (by rfl) ⟨632, by rfl⟩) R1265
theorem R13549 : Reach 13549 := rs (se 3 (by rfl) ⟨2540, by rfl⟩) R5081
theorem R13601 : Reach 13601 := rs (se 2 (by rfl) ⟨5100, by rfl⟩) R10201
theorem R13657 : Reach 13657 := rs (se 2 (by rfl) ⟨5121, by rfl⟩) R10243
theorem R13829 : Reach 13829 := rs (se 4 (by rfl) ⟨1296, by rfl⟩) R2593
theorem R13835 : Reach 13835 := rs (se 1 (by rfl) ⟨10376, by rfl⟩) R20753
theorem R13889 : Reach 13889 := rs (se 2 (by rfl) ⟨5208, by rfl⟩) R10417
theorem R13891 : Reach 13891 := rs (se 1 (by rfl) ⟨10418, by rfl⟩) R20837
theorem R14039 : Reach 14039 := rs (se 1 (by rfl) ⟨10529, by rfl⟩) R21059
theorem R14045 : Reach 14045 := rs (se 3 (by rfl) ⟨2633, by rfl⟩) R5267
theorem R14063 : Reach 14063 := rs (se 1 (by rfl) ⟨10547, by rfl⟩) R21095
theorem R14429 : Reach 14429 := rs (se 3 (by rfl) ⟨2705, by rfl⟩) R5411
theorem R14435 : Reach 14435 := rs (se 1 (by rfl) ⟨10826, by rfl⟩) R21653
theorem R14441 : Reach 14441 := rs (se 2 (by rfl) ⟨5415, by rfl⟩) R10831
theorem R14593 : Reach 14593 := rs (se 2 (by rfl) ⟨5472, by rfl⟩) R10945
theorem R14597 : Reach 14597 := rs (se 4 (by rfl) ⟨1368, by rfl⟩) R2737
theorem R14603 : Reach 14603 := rs (se 1 (by rfl) ⟨10952, by rfl⟩) R21905
theorem R14609 : Reach 14609 := rs (se 2 (by rfl) ⟨5478, by rfl⟩) R10957
theorem R14615 : Reach 14615 := rs (se 1 (by rfl) ⟨10961, by rfl⟩) R21923
theorem R14669 : Reach 14669 := rs (se 3 (by rfl) ⟨2750, by rfl⟩) R5501
theorem R14699 : Reach 14699 := rs (se 1 (by rfl) ⟨11024, by rfl⟩) R22049
theorem R14737 : Reach 14737 := rs (se 2 (by rfl) ⟨5526, by rfl⟩) R11053
theorem R14759 : Reach 14759 := rs (se 1 (by rfl) ⟨11069, by rfl⟩) R22139
theorem R14873 : Reach 14873 := rs (se 2 (by rfl) ⟨5577, by rfl⟩) R11155
theorem R15047 : Reach 15047 := rs (se 1 (by rfl) ⟨11285, by rfl⟩) R22571
theorem R15137 : Reach 15137 := rs (se 2 (by rfl) ⟨5676, by rfl⟩) R11353
theorem R16019 : Reach 16019 := rs (se 1 (by rfl) ⟨12014, by rfl⟩) R24029
theorem R16033 : Reach 16033 := rs (se 2 (by rfl) ⟨6012, by rfl⟩) R12025
theorem R16049 : Reach 16049 := rs (se 2 (by rfl) ⟨6018, by rfl⟩) R12037
theorem R16051 : Reach 16051 := rs (se 1 (by rfl) ⟨12038, by rfl⟩) R24077
theorem R16061 : Reach 16061 := rs (se 3 (by rfl) ⟨3011, by rfl⟩) R6023
theorem R16097 : Reach 16097 := rs (se 2 (by rfl) ⟨6036, by rfl⟩) R12073
theorem R16105 : Reach 16105 := rs (se 2 (by rfl) ⟨6039, by rfl⟩) R12079
theorem R52933 : Reach 52933 := rs (se 4 (by rfl) ⟨4962, by rfl⟩) R9925
theorem R53891 : Reach 53891 := rs (se 1 (by rfl) ⟨40418, by rfl⟩) R80837
theorem R55313 : Reach 55313 := rs (se 2 (by rfl) ⟨20742, by rfl⟩) R41485
theorem R55565 : Reach 55565 := rs (se 3 (by rfl) ⟨10418, by rfl⟩) R20837
theorem R57833 : Reach 57833 := rs (se 2 (by rfl) ⟨21687, by rfl⟩) R43375
theorem R26225 : Reach 26225 := rs (se 2 (by rfl) ⟨9834, by rfl⟩) R19669
theorem R26243 : Reach 26243 := rs (se 1 (by rfl) ⟨19682, by rfl⟩) R39365
theorem R26549 : Reach 26549 := rs (se 5 (by rfl) ⟨1244, by rfl⟩) R2489
theorem R59549 : Reach 59549 := rs (se 3 (by rfl) ⟨11165, by rfl⟩) R22331
theorem R26837 : Reach 26837 := rs (se 7 (by rfl) ⟨314, by rfl⟩) R629
theorem R26851 : Reach 26851 := rs (se 1 (by rfl) ⟨20138, by rfl⟩) R40277
theorem R26945 : Reach 26945 := rs (se 2 (by rfl) ⟨10104, by rfl⟩) R20209
theorem R26993 : Reach 26993 := rs (se 2 (by rfl) ⟨10122, by rfl⟩) R20245
theorem R27661 : Reach 27661 := rs (se 3 (by rfl) ⟨5186, by rfl⟩) R10373
theorem R27665 : Reach 27665 := rs (se 2 (by rfl) ⟨10374, by rfl⟩) R20749
theorem R28081 : Reach 28081 := rs (se 2 (by rfl) ⟨10530, by rfl⟩) R21061
theorem R28127 : Reach 28127 := rs (se 1 (by rfl) ⟨21095, by rfl⟩) R42191
theorem R28853 : Reach 28853 := rs (se 5 (by rfl) ⟨1352, by rfl⟩) R2705
theorem R28957 : Reach 28957 := rs (se 3 (by rfl) ⟨5429, by rfl⟩) R10859
theorem R29251 : Reach 29251 := rs (se 1 (by rfl) ⟨21938, by rfl⟩) R43877
theorem R29537 : Reach 29537 := rs (se 2 (by rfl) ⟨11076, by rfl⟩) R22153
theorem R29747 : Reach 29747 := rs (se 1 (by rfl) ⟨22310, by rfl⟩) R44621
theorem R29753 : Reach 29753 := rs (se 2 (by rfl) ⟨11157, by rfl⟩) R22315
theorem R128249 : Reach 128249 := rs (se 2 (by rfl) ⟨48093, by rfl⟩) R96187
theorem R30091 : Reach 30091 := rs (se 1 (by rfl) ⟨22568, by rfl⟩) R45137
theorem R30095 : Reach 30095 := rs (se 1 (by rfl) ⟨22571, by rfl⟩) R45143
theorem R30275 : Reach 30275 := rs (se 1 (by rfl) ⟨22706, by rfl⟩) R45413
theorem R64061 : Reach 64061 := rs (se 3 (by rfl) ⟨12011, by rfl⟩) R24023
theorem R32035 : Reach 32035 := rs (se 1 (by rfl) ⟨24026, by rfl⟩) R48053
theorem R32167 : Reach 32167 := rs (se 1 (by rfl) ⟨24125, by rfl⟩) R48251
theorem R32177 : Reach 32177 := rs (se 2 (by rfl) ⟨12066, by rfl⟩) R24133
theorem R135 : Reach 135 := rs (se 1 (by rfl) ⟨101, by rfl⟩) R203
theorem R139 : Reach 139 := rs (se 1 (by rfl) ⟨104, by rfl⟩) R209
theorem R271 : Reach 271 := rs (se 1 (by rfl) ⟨203, by rfl⟩) R407
theorem R279 : Reach 279 := rs (se 1 (by rfl) ⟨209, by rfl⟩) R419
theorem R281 : Reach 281 := rs (se 2 (by rfl) ⟨105, by rfl⟩) R211
theorem R287 : Reach 287 := rs (se 1 (by rfl) ⟨215, by rfl⟩) R431
theorem R303 : Reach 303 := rs (se 1 (by rfl) ⟨227, by rfl⟩) R455
theorem R541 : Reach 541 := rs (se 3 (by rfl) ⟨101, by rfl⟩) R203
theorem R545 : Reach 545 := rs (se 2 (by rfl) ⟨204, by rfl⟩) R409
theorem R551 : Reach 551 := rs (se 1 (by rfl) ⟨413, by rfl⟩) R827
theorem R557 : Reach 557 := rs (se 3 (by rfl) ⟨104, by rfl⟩) R209
theorem R561 : Reach 561 := rs (se 2 (by rfl) ⟨210, by rfl⟩) R421
theorem R563 : Reach 563 := rs (se 1 (by rfl) ⟨422, by rfl⟩) R845
theorem R575 : Reach 575 := rs (se 1 (by rfl) ⟨431, by rfl⟩) R863
theorem R607 : Reach 607 := rs (se 1 (by rfl) ⟨455, by rfl⟩) R911
theorem R1085 : Reach 1085 := rs (se 3 (by rfl) ⟨203, by rfl⟩) R407
theorem R1089 : Reach 1089 := rs (se 2 (by rfl) ⟨408, by rfl⟩) R817
theorem R1091 : Reach 1091 := rs (se 1 (by rfl) ⟨818, by rfl⟩) R1637
theorem R1103 : Reach 1103 := rs (se 1 (by rfl) ⟨827, by rfl⟩) R1655
theorem R1117 : Reach 1117 := rs (se 3 (by rfl) ⟨209, by rfl⟩) R419
theorem R1121 : Reach 1121 := rs (se 2 (by rfl) ⟨420, by rfl⟩) R841
theorem R1123 : Reach 1123 := rs (se 1 (by rfl) ⟨842, by rfl⟩) R1685
theorem R1125 : Reach 1125 := rs (se 4 (by rfl) ⟨105, by rfl⟩) R211
theorem R1149 : Reach 1149 := rs (se 3 (by rfl) ⟨215, by rfl⟩) R431
theorem R1213 : Reach 1213 := rs (se 3 (by rfl) ⟨227, by rfl⟩) R455
theorem R1337 : Reach 1337 := rs (se 2 (by rfl) ⟨501, by rfl⟩) R1003
theorem R34901 : Reach 34901 := rs (se 8 (by rfl) ⟨204, by rfl⟩) R409
theorem R2165 : Reach 2165 := rs (se 5 (by rfl) ⟨101, by rfl⟩) R203
theorem R2179 : Reach 2179 := rs (se 1 (by rfl) ⟨1634, by rfl⟩) R3269
theorem R2181 : Reach 2181 := rs (se 4 (by rfl) ⟨204, by rfl⟩) R409
theorem R2205 : Reach 2205 := rs (se 3 (by rfl) ⟨413, by rfl⟩) R827
theorem R2229 : Reach 2229 := rs (se 5 (by rfl) ⟨104, by rfl⟩) R209
theorem R2235 : Reach 2235 := rs (se 1 (by rfl) ⟨1676, by rfl⟩) R3353
theorem R2241 : Reach 2241 := rs (se 2 (by rfl) ⟨840, by rfl⟩) R1681
theorem R2243 : Reach 2243 := rs (se 1 (by rfl) ⟨1682, by rfl⟩) R3365
theorem R2245 : Reach 2245 := rs (se 4 (by rfl) ⟨210, by rfl⟩) R421
theorem R2249 : Reach 2249 := rs (se 2 (by rfl) ⟨843, by rfl⟩) R1687
theorem R2253 : Reach 2253 := rs (se 3 (by rfl) ⟨422, by rfl⟩) R845
theorem R2301 : Reach 2301 := rs (se 3 (by rfl) ⟨431, by rfl⟩) R863
theorem R2429 : Reach 2429 := rs (se 3 (by rfl) ⟨455, by rfl⟩) R911
theorem R2433 : Reach 2433 := rs (se 2 (by rfl) ⟨912, by rfl⟩) R1825
theorem R2443 : Reach 2443 := rs (se 1 (by rfl) ⟨1832, by rfl⟩) R3665
theorem R2479 : Reach 2479 := rs (se 1 (by rfl) ⟨1859, by rfl⟩) R3719
theorem R2667 : Reach 2667 := rs (se 1 (by rfl) ⟨2000, by rfl⟩) R4001
theorem R2671 : Reach 2671 := rs (se 1 (by rfl) ⟨2003, by rfl⟩) R4007
theorem R2675 : Reach 2675 := rs (se 1 (by rfl) ⟨2006, by rfl⟩) R4013
theorem R2681 : Reach 2681 := rs (se 2 (by rfl) ⟨1005, by rfl⟩) R2011
theorem R35653 : Reach 35653 := rs (se 4 (by rfl) ⟨3342, by rfl⟩) R6685
theorem R35801 : Reach 35801 := rs (se 2 (by rfl) ⟨13425, by rfl⟩) R26851
theorem R35909 : Reach 35909 := rs (se 4 (by rfl) ⟨3366, by rfl⟩) R6733
theorem R35927 : Reach 35927 := rs (se 1 (by rfl) ⟨26945, by rfl⟩) R53891
theorem R69461 : Reach 69461 := rs (se 9 (by rfl) ⟨203, by rfl⟩) R407
theorem R36875 : Reach 36875 := rs (se 1 (by rfl) ⟨27656, by rfl⟩) R55313
theorem R36881 : Reach 36881 := rs (se 2 (by rfl) ⟨13830, by rfl⟩) R27661
theorem R37043 : Reach 37043 := rs (se 1 (by rfl) ⟨27782, by rfl⟩) R55565
theorem R4337 : Reach 4337 := rs (se 2 (by rfl) ⟨1626, by rfl⟩) R3253
theorem R4341 : Reach 4341 := rs (se 5 (by rfl) ⟨203, by rfl⟩) R407
theorem R4357 : Reach 4357 := rs (se 4 (by rfl) ⟨408, by rfl⟩) R817
theorem R4365 : Reach 4365 := rs (se 3 (by rfl) ⟨818, by rfl⟩) R1637
theorem R4369 : Reach 4369 := rs (se 2 (by rfl) ⟨1638, by rfl⟩) R3277
theorem R4411 : Reach 4411 := rs (se 1 (by rfl) ⟨3308, by rfl⟩) R6617
theorem R4413 : Reach 4413 := rs (se 3 (by rfl) ⟨827, by rfl⟩) R1655
theorem R4425 : Reach 4425 := rs (se 2 (by rfl) ⟨1659, by rfl⟩) R3319
theorem R4457 : Reach 4457 := rs (se 2 (by rfl) ⟨1671, by rfl⟩) R3343
theorem R4459 : Reach 4459 := rs (se 1 (by rfl) ⟨3344, by rfl⟩) R6689
theorem R4463 : Reach 4463 := rs (se 1 (by rfl) ⟨3347, by rfl⟩) R6695
theorem R4465 : Reach 4465 := rs (se 2 (by rfl) ⟨1674, by rfl⟩) R3349
theorem R4469 : Reach 4469 := rs (se 5 (by rfl) ⟨209, by rfl⟩) R419
theorem R4471 : Reach 4471 := rs (se 1 (by rfl) ⟨3353, by rfl⟩) R6707
theorem R4481 : Reach 4481 := rs (se 2 (by rfl) ⟨1680, by rfl⟩) R3361
theorem R4483 : Reach 4483 := rs (se 1 (by rfl) ⟨3362, by rfl⟩) R6725
theorem R4485 : Reach 4485 := rs (se 4 (by rfl) ⟨420, by rfl⟩) R841
theorem R4487 : Reach 4487 := rs (se 1 (by rfl) ⟨3365, by rfl⟩) R6731
theorem R4493 : Reach 4493 := rs (se 3 (by rfl) ⟨842, by rfl⟩) R1685
theorem R4497 : Reach 4497 := rs (se 2 (by rfl) ⟨1686, by rfl⟩) R3373
theorem R4499 : Reach 4499 := rs (se 1 (by rfl) ⟨3374, by rfl⟩) R6749
theorem R4501 : Reach 4501 := rs (se 6 (by rfl) ⟨105, by rfl⟩) R211
theorem R4597 : Reach 4597 := rs (se 5 (by rfl) ⟨215, by rfl⟩) R431
theorem R4609 : Reach 4609 := rs (se 2 (by rfl) ⟨1728, by rfl⟩) R3457
theorem R37441 : Reach 37441 := rs (se 2 (by rfl) ⟨14040, by rfl⟩) R28081
theorem R4679 : Reach 4679 := rs (se 1 (by rfl) ⟨3509, by rfl⟩) R7019
theorem R4681 : Reach 4681 := rs (se 2 (by rfl) ⟨1755, by rfl⟩) R3511
theorem R4809 : Reach 4809 := rs (se 2 (by rfl) ⟨1803, by rfl⟩) R3607
theorem R4811 : Reach 4811 := rs (se 1 (by rfl) ⟨3608, by rfl⟩) R7217
theorem R4853 : Reach 4853 := rs (se 5 (by rfl) ⟨227, by rfl⟩) R455
theorem R4865 : Reach 4865 := rs (se 2 (by rfl) ⟨1824, by rfl⟩) R3649
theorem R4867 : Reach 4867 := rs (se 1 (by rfl) ⟨3650, by rfl⟩) R7301
theorem R4871 : Reach 4871 := rs (se 1 (by rfl) ⟨3653, by rfl⟩) R7307
theorem R4887 : Reach 4887 := rs (se 1 (by rfl) ⟨3665, by rfl⟩) R7331
theorem R4889 : Reach 4889 := rs (se 2 (by rfl) ⟨1833, by rfl⟩) R3667
theorem R4959 : Reach 4959 := rs (se 1 (by rfl) ⟨3719, by rfl⟩) R7439
theorem R70577 : Reach 70577 := rs (se 2 (by rfl) ⟨26466, by rfl⟩) R52933
theorem R5335 : Reach 5335 := rs (se 1 (by rfl) ⟨4001, by rfl⟩) R8003
theorem R5339 : Reach 5339 := rs (se 1 (by rfl) ⟨4004, by rfl⟩) R8009
theorem R5343 : Reach 5343 := rs (se 1 (by rfl) ⟨4007, by rfl⟩) R8015
theorem R5349 : Reach 5349 := rs (se 4 (by rfl) ⟨501, by rfl⟩) R1003
theorem R5353 : Reach 5353 := rs (se 2 (by rfl) ⟨2007, by rfl⟩) R4015
theorem R5363 : Reach 5363 := rs (se 1 (by rfl) ⟨4022, by rfl⟩) R8045
theorem R70955 : Reach 70955 := rs (se 1 (by rfl) ⟨53216, by rfl⟩) R106433
theorem R38501 : Reach 38501 := rs (se 4 (by rfl) ⟨3609, by rfl⟩) R7219
theorem R38555 : Reach 38555 := rs (se 1 (by rfl) ⟨28916, by rfl⟩) R57833
theorem R38609 : Reach 38609 := rs (se 2 (by rfl) ⟨14478, by rfl⟩) R28957
theorem R71603 : Reach 71603 := rs (se 1 (by rfl) ⟨53702, by rfl⟩) R107405
theorem R38933 : Reach 38933 := rs (se 6 (by rfl) ⟨912, by rfl⟩) R1825
theorem R39001 : Reach 39001 := rs (se 2 (by rfl) ⟨14625, by rfl⟩) R29251
theorem R40121 : Reach 40121 := rs (se 2 (by rfl) ⟨15045, by rfl⟩) R30091
theorem R8661 : Reach 8661 := rs (se 7 (by rfl) ⟨101, by rfl⟩) R203
theorem R8675 : Reach 8675 := rs (se 1 (by rfl) ⟨6506, by rfl⟩) R13013
theorem R8689 : Reach 8689 := rs (se 2 (by rfl) ⟨3258, by rfl⟩) R6517
theorem R8717 : Reach 8717 := rs (se 3 (by rfl) ⟨1634, by rfl⟩) R3269
theorem R8721 : Reach 8721 := rs (se 2 (by rfl) ⟨3270, by rfl⟩) R6541
theorem R8725 : Reach 8725 := rs (se 6 (by rfl) ⟨204, by rfl⟩) R409
theorem R8739 : Reach 8739 := rs (se 1 (by rfl) ⟨6554, by rfl⟩) R13109
theorem R8747 : Reach 8747 := rs (se 1 (by rfl) ⟨6560, by rfl⟩) R13121
theorem R8763 : Reach 8763 := rs (se 1 (by rfl) ⟨6572, by rfl⟩) R13145
theorem R8821 : Reach 8821 := rs (se 5 (by rfl) ⟨413, by rfl⟩) R827
theorem R8823 : Reach 8823 := rs (se 1 (by rfl) ⟨6617, by rfl⟩) R13235
theorem R8849 : Reach 8849 := rs (se 2 (by rfl) ⟨3318, by rfl⟩) R6637
theorem R8851 : Reach 8851 := rs (se 1 (by rfl) ⟨6638, by rfl⟩) R13277
theorem R8913 : Reach 8913 := rs (se 2 (by rfl) ⟨3342, by rfl⟩) R6685
theorem R8915 : Reach 8915 := rs (se 1 (by rfl) ⟨6686, by rfl⟩) R13373
theorem R8917 : Reach 8917 := rs (se 7 (by rfl) ⟨104, by rfl⟩) R209
theorem R8919 : Reach 8919 := rs (se 1 (by rfl) ⟨6689, by rfl⟩) R13379
theorem R8927 : Reach 8927 := rs (se 1 (by rfl) ⟨6695, by rfl⟩) R13391
theorem R8931 : Reach 8931 := rs (se 1 (by rfl) ⟨6698, by rfl⟩) R13397
theorem R8941 : Reach 8941 := rs (se 3 (by rfl) ⟨1676, by rfl⟩) R3353
theorem R8945 : Reach 8945 := rs (se 2 (by rfl) ⟨3354, by rfl⟩) R6709
theorem R8961 : Reach 8961 := rs (se 2 (by rfl) ⟨3360, by rfl⟩) R6721
theorem R8963 : Reach 8963 := rs (se 1 (by rfl) ⟨6722, by rfl⟩) R13445
theorem R8965 : Reach 8965 := rs (se 4 (by rfl) ⟨840, by rfl⟩) R1681
theorem R8973 : Reach 8973 := rs (se 3 (by rfl) ⟨1682, by rfl⟩) R3365
theorem R8975 : Reach 8975 := rs (se 1 (by rfl) ⟨6731, by rfl⟩) R13463
theorem R8977 : Reach 8977 := rs (se 2 (by rfl) ⟨3366, by rfl⟩) R6733
theorem R8981 : Reach 8981 := rs (se 6 (by rfl) ⟨210, by rfl⟩) R421
theorem R8995 : Reach 8995 := rs (se 1 (by rfl) ⟨6746, by rfl⟩) R13493
theorem R8997 : Reach 8997 := rs (se 4 (by rfl) ⟨843, by rfl⟩) R1687
theorem R9013 : Reach 9013 := rs (se 5 (by rfl) ⟨422, by rfl⟩) R845
theorem R9025 : Reach 9025 := rs (se 2 (by rfl) ⟨3384, by rfl⟩) R6769
theorem R9033 : Reach 9033 := rs (se 2 (by rfl) ⟨3387, by rfl⟩) R6775
theorem R9049 : Reach 9049 := rs (se 2 (by rfl) ⟨3393, by rfl⟩) R6787
theorem R9067 : Reach 9067 := rs (se 1 (by rfl) ⟨6800, by rfl⟩) R13601
theorem R9201 : Reach 9201 := rs (se 2 (by rfl) ⟨3450, by rfl⟩) R6901
theorem R9205 : Reach 9205 := rs (se 5 (by rfl) ⟨431, by rfl⟩) R863
theorem R9217 : Reach 9217 := rs (se 2 (by rfl) ⟨3456, by rfl⟩) R6913
theorem R9219 : Reach 9219 := rs (se 1 (by rfl) ⟨6914, by rfl⟩) R13829
theorem R9223 : Reach 9223 := rs (se 1 (by rfl) ⟨6917, by rfl⟩) R13835
theorem R9259 : Reach 9259 := rs (se 1 (by rfl) ⟨6944, by rfl⟩) R13889
theorem R9359 : Reach 9359 := rs (se 1 (by rfl) ⟨7019, by rfl⟩) R14039
theorem R9361 : Reach 9361 := rs (se 2 (by rfl) ⟨3510, by rfl⟩) R7021
theorem R9363 : Reach 9363 := rs (se 1 (by rfl) ⟨7022, by rfl⟩) R14045
theorem R9375 : Reach 9375 := rs (se 1 (by rfl) ⟨7031, by rfl⟩) R14063
theorem R9617 : Reach 9617 := rs (se 2 (by rfl) ⟨3606, by rfl⟩) R7213
theorem R9619 : Reach 9619 := rs (se 1 (by rfl) ⟨7214, by rfl⟩) R14429
theorem R9623 : Reach 9623 := rs (se 1 (by rfl) ⟨7217, by rfl⟩) R14435
theorem R9625 : Reach 9625 := rs (se 2 (by rfl) ⟨3609, by rfl⟩) R7219
theorem R9627 : Reach 9627 := rs (se 1 (by rfl) ⟨7220, by rfl⟩) R14441
theorem R9633 : Reach 9633 := rs (se 2 (by rfl) ⟨3612, by rfl⟩) R7225
theorem R9713 : Reach 9713 := rs (se 2 (by rfl) ⟨3642, by rfl⟩) R7285
theorem R9717 : Reach 9717 := rs (se 5 (by rfl) ⟨455, by rfl⟩) R911
theorem R9731 : Reach 9731 := rs (se 1 (by rfl) ⟨7298, by rfl⟩) R14597
theorem R9733 : Reach 9733 := rs (se 4 (by rfl) ⟨912, by rfl⟩) R1825
theorem R9735 : Reach 9735 := rs (se 1 (by rfl) ⟨7301, by rfl⟩) R14603
theorem R9739 : Reach 9739 := rs (se 1 (by rfl) ⟨7304, by rfl⟩) R14609
theorem R9743 : Reach 9743 := rs (se 1 (by rfl) ⟨7307, by rfl⟩) R14615
theorem R9761 : Reach 9761 := rs (se 2 (by rfl) ⟨3660, by rfl⟩) R7321
theorem R9773 : Reach 9773 := rs (se 3 (by rfl) ⟨1832, by rfl⟩) R3665
theorem R9777 : Reach 9777 := rs (se 2 (by rfl) ⟨3666, by rfl⟩) R7333
theorem R9779 : Reach 9779 := rs (se 1 (by rfl) ⟨7334, by rfl⟩) R14669
theorem R9799 : Reach 9799 := rs (se 1 (by rfl) ⟨7349, by rfl⟩) R14699
theorem R9825 : Reach 9825 := rs (se 2 (by rfl) ⟨3684, by rfl⟩) R7369
theorem R9833 : Reach 9833 := rs (se 2 (by rfl) ⟨3687, by rfl⟩) R7375
theorem R9839 : Reach 9839 := rs (se 1 (by rfl) ⟨7379, by rfl⟩) R14759
theorem R42677 : Reach 42677 := rs (se 5 (by rfl) ⟨2000, by rfl⟩) R4001
theorem R9913 : Reach 9913 := rs (se 2 (by rfl) ⟨3717, by rfl⟩) R7435
theorem R9915 : Reach 9915 := rs (se 1 (by rfl) ⟨7436, by rfl⟩) R14873
theorem R9917 : Reach 9917 := rs (se 3 (by rfl) ⟨1859, by rfl⟩) R3719
theorem R42707 : Reach 42707 := rs (se 1 (by rfl) ⟨32030, by rfl⟩) R64061
theorem R42713 : Reach 42713 := rs (se 2 (by rfl) ⟨16017, by rfl⟩) R32035
theorem R10031 : Reach 10031 := rs (se 1 (by rfl) ⟨7523, by rfl⟩) R15047
theorem R42821 : Reach 42821 := rs (se 4 (by rfl) ⟨4014, by rfl⟩) R8029
theorem R10091 : Reach 10091 := rs (se 1 (by rfl) ⟨7568, by rfl⟩) R15137
theorem R42889 : Reach 42889 := rs (se 2 (by rfl) ⟨16083, by rfl⟩) R32167
theorem R10669 : Reach 10669 := rs (se 3 (by rfl) ⟨2000, by rfl⟩) R4001
theorem R10679 : Reach 10679 := rs (se 1 (by rfl) ⟨8009, by rfl⟩) R16019
theorem R10685 : Reach 10685 := rs (se 3 (by rfl) ⟨2003, by rfl⟩) R4007
theorem R10699 : Reach 10699 := rs (se 1 (by rfl) ⟨8024, by rfl⟩) R16049
theorem R10701 : Reach 10701 := rs (se 3 (by rfl) ⟨2006, by rfl⟩) R4013
theorem R10705 : Reach 10705 := rs (se 2 (by rfl) ⟨4014, by rfl⟩) R8029
theorem R10707 : Reach 10707 := rs (se 1 (by rfl) ⟨8030, by rfl⟩) R16061
theorem R10725 : Reach 10725 := rs (se 4 (by rfl) ⟨1005, by rfl⟩) R2011
theorem R10729 : Reach 10729 := rs (se 2 (by rfl) ⟨4023, by rfl⟩) R8047
theorem R10731 : Reach 10731 := rs (se 1 (by rfl) ⟨8048, by rfl⟩) R16097
theorem R79325 : Reach 79325 := rs (se 3 (by rfl) ⟨14873, by rfl⟩) R29747
theorem R17369 : Reach 17369 := rs (se 2 (by rfl) ⟨6513, by rfl⟩) R13027
theorem R17429 : Reach 17429 := rs (se 6 (by rfl) ⟨408, by rfl⟩) R817
theorem R17477 : Reach 17477 := rs (se 4 (by rfl) ⟨1638, by rfl⟩) R3277
theorem R17483 : Reach 17483 := rs (se 1 (by rfl) ⟨13112, by rfl⟩) R26225
theorem R17495 : Reach 17495 := rs (se 1 (by rfl) ⟨13121, by rfl⟩) R26243
theorem R17609 : Reach 17609 := rs (se 2 (by rfl) ⟨6603, by rfl⟩) R13207
theorem R17645 : Reach 17645 := rs (se 3 (by rfl) ⟨3308, by rfl⟩) R6617
theorem R17699 : Reach 17699 := rs (se 1 (by rfl) ⟨13274, by rfl⟩) R26549
theorem R17837 : Reach 17837 := rs (se 3 (by rfl) ⟨3344, by rfl⟩) R6689
theorem R17861 : Reach 17861 := rs (se 4 (by rfl) ⟨1674, by rfl⟩) R3349
theorem R17885 : Reach 17885 := rs (se 3 (by rfl) ⟨3353, by rfl⟩) R6707
theorem R17891 : Reach 17891 := rs (se 1 (by rfl) ⟨13418, by rfl⟩) R26837
theorem R17933 : Reach 17933 := rs (se 3 (by rfl) ⟨3362, by rfl⟩) R6725
theorem R17941 : Reach 17941 := rs (se 6 (by rfl) ⟨420, by rfl⟩) R841
theorem R17963 : Reach 17963 := rs (se 1 (by rfl) ⟨13472, by rfl⟩) R26945
theorem R17995 : Reach 17995 := rs (se 1 (by rfl) ⟨13496, by rfl⟩) R26993
theorem R18005 : Reach 18005 := rs (se 8 (by rfl) ⟨105, by rfl⟩) R211
theorem R18065 : Reach 18065 := rs (se 2 (by rfl) ⟨6774, by rfl⟩) R13549
theorem R18209 : Reach 18209 := rs (se 2 (by rfl) ⟨6828, by rfl⟩) R13657
theorem R18389 : Reach 18389 := rs (se 7 (by rfl) ⟨215, by rfl⟩) R431
theorem R18437 : Reach 18437 := rs (se 4 (by rfl) ⟨1728, by rfl⟩) R3457
theorem R18443 : Reach 18443 := rs (se 1 (by rfl) ⟨13832, by rfl⟩) R27665
theorem R18521 : Reach 18521 := rs (se 2 (by rfl) ⟨6945, by rfl⟩) R13891
theorem R18725 : Reach 18725 := rs (se 4 (by rfl) ⟨1755, by rfl⟩) R3511
theorem R18751 : Reach 18751 := rs (se 1 (by rfl) ⟨14063, by rfl⟩) R28127
theorem R19235 : Reach 19235 := rs (se 1 (by rfl) ⟨14426, by rfl⟩) R28853
theorem R19237 : Reach 19237 := rs (se 4 (by rfl) ⟨1803, by rfl⟩) R3607
theorem R19457 : Reach 19457 := rs (se 2 (by rfl) ⟨7296, by rfl⟩) R14593
theorem R19649 : Reach 19649 := rs (se 2 (by rfl) ⟨7368, by rfl⟩) R14737
theorem R19691 : Reach 19691 := rs (se 1 (by rfl) ⟨14768, by rfl⟩) R29537
theorem R19831 : Reach 19831 := rs (se 1 (by rfl) ⟨14873, by rfl⟩) R29747
theorem R19835 : Reach 19835 := rs (se 1 (by rfl) ⟨14876, by rfl⟩) R29753
theorem R19837 : Reach 19837 := rs (se 3 (by rfl) ⟨3719, by rfl⟩) R7439
theorem R85499 : Reach 85499 := rs (se 1 (by rfl) ⟨64124, by rfl⟩) R128249
theorem R20063 : Reach 20063 := rs (se 1 (by rfl) ⟨15047, by rfl⟩) R30095
theorem R20183 : Reach 20183 := rs (se 1 (by rfl) ⟨15137, by rfl⟩) R30275
theorem R21377 : Reach 21377 := rs (se 2 (by rfl) ⟨8016, by rfl⟩) R16033
theorem R21397 : Reach 21397 := rs (se 6 (by rfl) ⟨501, by rfl⟩) R1003
theorem R21401 : Reach 21401 := rs (se 2 (by rfl) ⟨8025, by rfl⟩) R16051
theorem R21451 : Reach 21451 := rs (se 1 (by rfl) ⟨16088, by rfl⟩) R32177
theorem R21473 : Reach 21473 := rs (se 2 (by rfl) ⟨8052, by rfl⟩) R16105
theorem R158797 : Reach 158797 := rs (se 3 (by rfl) ⟨29774, by rfl⟩) R59549
theorem R185 : Reach 185 := rs (se 2 (by rfl) ⟨69, by rfl⟩) R139
theorem R187 : Reach 187 := rs (se 1 (by rfl) ⟨140, by rfl⟩) R281
theorem R191 : Reach 191 := rs (se 1 (by rfl) ⟨143, by rfl⟩) R287
theorem R361 : Reach 361 := rs (se 2 (by rfl) ⟨135, by rfl⟩) R271
theorem R363 : Reach 363 := rs (se 1 (by rfl) ⟨272, by rfl⟩) R545
theorem R367 : Reach 367 := rs (se 1 (by rfl) ⟨275, by rfl⟩) R551
theorem R371 : Reach 371 := rs (se 1 (by rfl) ⟨278, by rfl⟩) R557
theorem R375 : Reach 375 := rs (se 1 (by rfl) ⟨281, by rfl⟩) R563
theorem R383 : Reach 383 := rs (se 1 (by rfl) ⟨287, by rfl⟩) R575
theorem R721 : Reach 721 := rs (se 2 (by rfl) ⟨270, by rfl⟩) R541
theorem R723 : Reach 723 := rs (se 1 (by rfl) ⟨542, by rfl⟩) R1085
theorem R727 : Reach 727 := rs (se 1 (by rfl) ⟨545, by rfl⟩) R1091
theorem R735 : Reach 735 := rs (se 1 (by rfl) ⟨551, by rfl⟩) R1103
theorem R741 : Reach 741 := rs (se 4 (by rfl) ⟨69, by rfl⟩) R139
theorem R747 : Reach 747 := rs (se 1 (by rfl) ⟨560, by rfl⟩) R1121
theorem R749 : Reach 749 := rs (se 3 (by rfl) ⟨140, by rfl⟩) R281
theorem R765 : Reach 765 := rs (se 3 (by rfl) ⟨143, by rfl⟩) R287
theorem R809 : Reach 809 := rs (se 2 (by rfl) ⟨303, by rfl⟩) R607
theorem R891 : Reach 891 := rs (se 1 (by rfl) ⟨668, by rfl⟩) R1337
theorem R1443 : Reach 1443 := rs (se 1 (by rfl) ⟨1082, by rfl⟩) R2165
theorem R1445 : Reach 1445 := rs (se 4 (by rfl) ⟨135, by rfl⟩) R271
theorem R1453 : Reach 1453 := rs (se 3 (by rfl) ⟨272, by rfl⟩) R545
theorem R1469 : Reach 1469 := rs (se 3 (by rfl) ⟨275, by rfl⟩) R551
theorem R1485 : Reach 1485 := rs (se 3 (by rfl) ⟨278, by rfl⟩) R557
theorem R1489 : Reach 1489 := rs (se 2 (by rfl) ⟨558, by rfl⟩) R1117
theorem R1495 : Reach 1495 := rs (se 1 (by rfl) ⟨1121, by rfl⟩) R2243
theorem R1497 : Reach 1497 := rs (se 2 (by rfl) ⟨561, by rfl⟩) R1123
theorem R1499 : Reach 1499 := rs (se 1 (by rfl) ⟨1124, by rfl⟩) R2249
theorem R1501 : Reach 1501 := rs (se 3 (by rfl) ⟨281, by rfl⟩) R563
theorem R1533 : Reach 1533 := rs (se 3 (by rfl) ⟨287, by rfl⟩) R575
theorem R1617 : Reach 1617 := rs (se 2 (by rfl) ⟨606, by rfl⟩) R1213
theorem R1619 : Reach 1619 := rs (se 1 (by rfl) ⟨1214, by rfl⟩) R2429
theorem R1783 : Reach 1783 := rs (se 1 (by rfl) ⟨1337, by rfl⟩) R2675
theorem R1787 : Reach 1787 := rs (se 1 (by rfl) ⟨1340, by rfl⟩) R2681
theorem R2885 : Reach 2885 := rs (se 4 (by rfl) ⟨270, by rfl⟩) R541
theorem R2891 : Reach 2891 := rs (se 1 (by rfl) ⟨2168, by rfl⟩) R4337
theorem R2893 : Reach 2893 := rs (se 3 (by rfl) ⟨542, by rfl⟩) R1085
theorem R2905 : Reach 2905 := rs (se 2 (by rfl) ⟨1089, by rfl⟩) R2179
theorem R2909 : Reach 2909 := rs (se 3 (by rfl) ⟨545, by rfl⟩) R1091
theorem R2941 : Reach 2941 := rs (se 3 (by rfl) ⟨551, by rfl⟩) R1103
theorem R2965 : Reach 2965 := rs (se 6 (by rfl) ⟨69, by rfl⟩) R139
theorem R2971 : Reach 2971 := rs (se 1 (by rfl) ⟨2228, by rfl⟩) R4457
theorem R2975 : Reach 2975 := rs (se 1 (by rfl) ⟨2231, by rfl⟩) R4463
theorem R2979 : Reach 2979 := rs (se 1 (by rfl) ⟨2234, by rfl⟩) R4469
theorem R2987 : Reach 2987 := rs (se 1 (by rfl) ⟨2240, by rfl⟩) R4481
theorem R2989 : Reach 2989 := rs (se 3 (by rfl) ⟨560, by rfl⟩) R1121
theorem R2991 : Reach 2991 := rs (se 1 (by rfl) ⟨2243, by rfl⟩) R4487
theorem R2993 : Reach 2993 := rs (se 2 (by rfl) ⟨1122, by rfl⟩) R2245
theorem R2995 : Reach 2995 := rs (se 1 (by rfl) ⟨2246, by rfl⟩) R4493
theorem R2997 : Reach 2997 := rs (se 5 (by rfl) ⟨140, by rfl⟩) R281
theorem R2999 : Reach 2999 := rs (se 1 (by rfl) ⟨2249, by rfl⟩) R4499
theorem R3061 : Reach 3061 := rs (se 5 (by rfl) ⟨143, by rfl⟩) R287
theorem R199685 : Reach 199685 := rs (se 4 (by rfl) ⟨18720, by rfl⟩) R37441
theorem R3119 : Reach 3119 := rs (se 1 (by rfl) ⟨2339, by rfl⟩) R4679
theorem R3207 : Reach 3207 := rs (se 1 (by rfl) ⟨2405, by rfl⟩) R4811
theorem R3235 : Reach 3235 := rs (se 1 (by rfl) ⟨2426, by rfl⟩) R4853
theorem R3237 : Reach 3237 := rs (se 4 (by rfl) ⟨303, by rfl⟩) R607
theorem R3243 : Reach 3243 := rs (se 1 (by rfl) ⟨2432, by rfl⟩) R4865
theorem R3247 : Reach 3247 := rs (se 1 (by rfl) ⟨2435, by rfl⟩) R4871
theorem R3257 : Reach 3257 := rs (se 2 (by rfl) ⟨1221, by rfl⟩) R2443
theorem R3259 : Reach 3259 := rs (se 1 (by rfl) ⟨2444, by rfl⟩) R4889
theorem R3305 : Reach 3305 := rs (se 2 (by rfl) ⟨1239, by rfl⟩) R2479
theorem R3559 : Reach 3559 := rs (se 1 (by rfl) ⟨2669, by rfl⟩) R5339
theorem R3561 : Reach 3561 := rs (se 2 (by rfl) ⟨1335, by rfl⟩) R2671
theorem R3565 : Reach 3565 := rs (se 3 (by rfl) ⟨668, by rfl⟩) R1337
theorem R3575 : Reach 3575 := rs (se 1 (by rfl) ⟨2681, by rfl⟩) R5363
theorem R5773 : Reach 5773 := rs (se 3 (by rfl) ⟨1082, by rfl⟩) R2165
theorem R5781 : Reach 5781 := rs (se 6 (by rfl) ⟨135, by rfl⟩) R271
theorem R5783 : Reach 5783 := rs (se 1 (by rfl) ⟨4337, by rfl⟩) R8675
theorem R5809 : Reach 5809 := rs (se 2 (by rfl) ⟨2178, by rfl⟩) R4357
theorem R5811 : Reach 5811 := rs (se 1 (by rfl) ⟨4358, by rfl⟩) R8717
theorem R5813 : Reach 5813 := rs (se 5 (by rfl) ⟨272, by rfl⟩) R545
theorem R5825 : Reach 5825 := rs (se 2 (by rfl) ⟨2184, by rfl⟩) R4369
theorem R5831 : Reach 5831 := rs (se 1 (by rfl) ⟨4373, by rfl⟩) R8747
theorem R5877 : Reach 5877 := rs (se 5 (by rfl) ⟨275, by rfl⟩) R551
theorem R5881 : Reach 5881 := rs (se 2 (by rfl) ⟨2205, by rfl⟩) R4411
theorem R5899 : Reach 5899 := rs (se 1 (by rfl) ⟨4424, by rfl⟩) R8849
theorem R5941 : Reach 5941 := rs (se 5 (by rfl) ⟨278, by rfl⟩) R557
theorem R5943 : Reach 5943 := rs (se 1 (by rfl) ⟨4457, by rfl⟩) R8915
theorem R5945 : Reach 5945 := rs (se 2 (by rfl) ⟨2229, by rfl⟩) R4459
theorem R5951 : Reach 5951 := rs (se 1 (by rfl) ⟨4463, by rfl⟩) R8927
theorem R5953 : Reach 5953 := rs (se 2 (by rfl) ⟨2232, by rfl⟩) R4465
theorem R5957 : Reach 5957 := rs (se 4 (by rfl) ⟨558, by rfl⟩) R1117
theorem R5961 : Reach 5961 := rs (se 2 (by rfl) ⟨2235, by rfl⟩) R4471
theorem R5963 : Reach 5963 := rs (se 1 (by rfl) ⟨4472, by rfl⟩) R8945
theorem R5975 : Reach 5975 := rs (se 1 (by rfl) ⟨4481, by rfl⟩) R8963
theorem R5977 : Reach 5977 := rs (se 2 (by rfl) ⟨2241, by rfl⟩) R4483
theorem R5981 : Reach 5981 := rs (se 3 (by rfl) ⟨1121, by rfl⟩) R2243
theorem R5983 : Reach 5983 := rs (se 1 (by rfl) ⟨4487, by rfl⟩) R8975
theorem R5987 : Reach 5987 := rs (se 1 (by rfl) ⟨4490, by rfl⟩) R8981
theorem R5989 : Reach 5989 := rs (se 4 (by rfl) ⟨561, by rfl⟩) R1123
theorem R5997 : Reach 5997 := rs (se 3 (by rfl) ⟨1124, by rfl⟩) R2249
theorem R6001 : Reach 6001 := rs (se 2 (by rfl) ⟨2250, by rfl⟩) R4501
theorem R6005 : Reach 6005 := rs (se 5 (by rfl) ⟨281, by rfl⟩) R563
theorem R6129 : Reach 6129 := rs (se 2 (by rfl) ⟨2298, by rfl⟩) R4597
theorem R6133 : Reach 6133 := rs (se 5 (by rfl) ⟨287, by rfl⟩) R575
theorem R6145 : Reach 6145 := rs (se 2 (by rfl) ⟨2304, by rfl⟩) R4609
theorem R6239 : Reach 6239 := rs (se 1 (by rfl) ⟨4679, by rfl⟩) R9359
theorem R6241 : Reach 6241 := rs (se 2 (by rfl) ⟨2340, by rfl⟩) R4681
theorem R6411 : Reach 6411 := rs (se 1 (by rfl) ⟨4808, by rfl⟩) R9617
theorem R6415 : Reach 6415 := rs (se 1 (by rfl) ⟨4811, by rfl⟩) R9623
theorem R6469 : Reach 6469 := rs (se 4 (by rfl) ⟨606, by rfl⟩) R1213
theorem R6475 : Reach 6475 := rs (se 1 (by rfl) ⟨4856, by rfl⟩) R9713
theorem R6477 : Reach 6477 := rs (se 3 (by rfl) ⟨1214, by rfl⟩) R2429
theorem R6487 : Reach 6487 := rs (se 1 (by rfl) ⟨4865, by rfl⟩) R9731
theorem R6489 : Reach 6489 := rs (se 2 (by rfl) ⟨2433, by rfl⟩) R4867
theorem R6495 : Reach 6495 := rs (se 1 (by rfl) ⟨4871, by rfl⟩) R9743
theorem R6507 : Reach 6507 := rs (se 1 (by rfl) ⟨4880, by rfl⟩) R9761
theorem R6515 : Reach 6515 := rs (se 1 (by rfl) ⟨4886, by rfl⟩) R9773
theorem R6519 : Reach 6519 := rs (se 1 (by rfl) ⟨4889, by rfl⟩) R9779
theorem R6555 : Reach 6555 := rs (se 1 (by rfl) ⟨4916, by rfl⟩) R9833
theorem R6559 : Reach 6559 := rs (se 1 (by rfl) ⟨4919, by rfl⟩) R9839
theorem R104885 : Reach 104885 := rs (se 5 (by rfl) ⟨4916, by rfl⟩) R9833
theorem R6611 : Reach 6611 := rs (se 1 (by rfl) ⟨4958, by rfl⟩) R9917
theorem R6687 : Reach 6687 := rs (se 1 (by rfl) ⟨5015, by rfl⟩) R10031
theorem R6727 : Reach 6727 := rs (se 1 (by rfl) ⟨5045, by rfl⟩) R10091
theorem R7113 : Reach 7113 := rs (se 2 (by rfl) ⟨2667, by rfl⟩) R5335
theorem R7119 : Reach 7119 := rs (se 1 (by rfl) ⟨5339, by rfl⟩) R10679
theorem R7123 : Reach 7123 := rs (se 1 (by rfl) ⟨5342, by rfl⟩) R10685
theorem R7133 : Reach 7133 := rs (se 3 (by rfl) ⟨1337, by rfl⟩) R2675
theorem R7137 : Reach 7137 := rs (se 2 (by rfl) ⟨2676, by rfl⟩) R5353
theorem R7149 : Reach 7149 := rs (se 3 (by rfl) ⟨1340, by rfl⟩) R2681
theorem R11541 : Reach 11541 := rs (se 6 (by rfl) ⟨270, by rfl⟩) R541
theorem R11565 : Reach 11565 := rs (se 3 (by rfl) ⟨2168, by rfl⟩) R4337
theorem R11573 : Reach 11573 := rs (se 5 (by rfl) ⟨542, by rfl⟩) R1085
theorem R11579 : Reach 11579 := rs (se 1 (by rfl) ⟨8684, by rfl⟩) R17369
theorem R11585 : Reach 11585 := rs (se 2 (by rfl) ⟨4344, by rfl⟩) R8689
theorem R11619 : Reach 11619 := rs (se 1 (by rfl) ⟨8714, by rfl⟩) R17429
theorem R11621 : Reach 11621 := rs (se 4 (by rfl) ⟨1089, by rfl⟩) R2179
theorem R11633 : Reach 11633 := rs (se 2 (by rfl) ⟨4362, by rfl⟩) R8725
theorem R11637 : Reach 11637 := rs (se 5 (by rfl) ⟨545, by rfl⟩) R1091
theorem R11651 : Reach 11651 := rs (se 1 (by rfl) ⟨8738, by rfl⟩) R17477
theorem R11655 : Reach 11655 := rs (se 1 (by rfl) ⟨8741, by rfl⟩) R17483
theorem R11663 : Reach 11663 := rs (se 1 (by rfl) ⟨8747, by rfl⟩) R17495
theorem R11739 : Reach 11739 := rs (se 1 (by rfl) ⟨8804, by rfl⟩) R17609
theorem R11761 : Reach 11761 := rs (se 2 (by rfl) ⟨4410, by rfl⟩) R8821
theorem R11763 : Reach 11763 := rs (se 1 (by rfl) ⟨8822, by rfl⟩) R17645
theorem R11765 : Reach 11765 := rs (se 5 (by rfl) ⟨551, by rfl⟩) R1103
theorem R11799 : Reach 11799 := rs (se 1 (by rfl) ⟨8849, by rfl⟩) R17699
theorem R11801 : Reach 11801 := rs (se 2 (by rfl) ⟨4425, by rfl⟩) R8851
theorem R11861 : Reach 11861 := rs (se 8 (by rfl) ⟨69, by rfl⟩) R139
theorem R11885 : Reach 11885 := rs (se 3 (by rfl) ⟨2228, by rfl⟩) R4457
theorem R11889 : Reach 11889 := rs (se 2 (by rfl) ⟨4458, by rfl⟩) R8917
theorem R11891 : Reach 11891 := rs (se 1 (by rfl) ⟨8918, by rfl⟩) R17837
theorem R11901 : Reach 11901 := rs (se 3 (by rfl) ⟨2231, by rfl⟩) R4463
theorem R11907 : Reach 11907 := rs (se 1 (by rfl) ⟨8930, by rfl⟩) R17861
theorem R11917 : Reach 11917 := rs (se 3 (by rfl) ⟨2234, by rfl⟩) R4469
theorem R11921 : Reach 11921 := rs (se 2 (by rfl) ⟨4470, by rfl⟩) R8941
theorem R11923 : Reach 11923 := rs (se 1 (by rfl) ⟨8942, by rfl⟩) R17885
theorem R11927 : Reach 11927 := rs (se 1 (by rfl) ⟨8945, by rfl⟩) R17891
theorem R11949 : Reach 11949 := rs (se 3 (by rfl) ⟨2240, by rfl⟩) R4481
theorem R11953 : Reach 11953 := rs (se 2 (by rfl) ⟨4482, by rfl⟩) R8965
theorem R11955 : Reach 11955 := rs (se 1 (by rfl) ⟨8966, by rfl⟩) R17933
theorem R11957 : Reach 11957 := rs (se 5 (by rfl) ⟨560, by rfl⟩) R1121
theorem R11965 : Reach 11965 := rs (se 3 (by rfl) ⟨2243, by rfl⟩) R4487
theorem R11969 : Reach 11969 := rs (se 2 (by rfl) ⟨4488, by rfl⟩) R8977
theorem R11973 : Reach 11973 := rs (se 4 (by rfl) ⟨1122, by rfl⟩) R2245
theorem R11975 : Reach 11975 := rs (se 1 (by rfl) ⟨8981, by rfl⟩) R17963
theorem R11981 : Reach 11981 := rs (se 3 (by rfl) ⟨2246, by rfl⟩) R4493
theorem R11989 : Reach 11989 := rs (se 7 (by rfl) ⟨140, by rfl⟩) R281
theorem R11993 : Reach 11993 := rs (se 2 (by rfl) ⟨4497, by rfl⟩) R8995
theorem R11997 : Reach 11997 := rs (se 3 (by rfl) ⟨2249, by rfl⟩) R4499
theorem R12003 : Reach 12003 := rs (se 1 (by rfl) ⟨9002, by rfl⟩) R18005
theorem R12017 : Reach 12017 := rs (se 2 (by rfl) ⟨4506, by rfl⟩) R9013
theorem R12033 : Reach 12033 := rs (se 2 (by rfl) ⟨4512, by rfl⟩) R9025
theorem R12043 : Reach 12043 := rs (se 1 (by rfl) ⟨9032, by rfl⟩) R18065
theorem R12065 : Reach 12065 := rs (se 2 (by rfl) ⟨4524, by rfl⟩) R9049
theorem R12089 : Reach 12089 := rs (se 2 (by rfl) ⟨4533, by rfl⟩) R9067
theorem R12139 : Reach 12139 := rs (se 1 (by rfl) ⟨9104, by rfl⟩) R18209
theorem R12245 : Reach 12245 := rs (se 7 (by rfl) ⟨143, by rfl⟩) R287
theorem R12259 : Reach 12259 := rs (se 1 (by rfl) ⟨9194, by rfl⟩) R18389
theorem R12273 : Reach 12273 := rs (se 2 (by rfl) ⟨4602, by rfl⟩) R9205
theorem R12289 : Reach 12289 := rs (se 2 (by rfl) ⟨4608, by rfl⟩) R9217
theorem R12291 : Reach 12291 := rs (se 1 (by rfl) ⟨9218, by rfl⟩) R18437
theorem R12295 : Reach 12295 := rs (se 1 (by rfl) ⟨9221, by rfl⟩) R18443
theorem R12297 : Reach 12297 := rs (se 2 (by rfl) ⟨4611, by rfl⟩) R9223
theorem R12345 : Reach 12345 := rs (se 2 (by rfl) ⟨4629, by rfl⟩) R9259
theorem R12347 : Reach 12347 := rs (se 1 (by rfl) ⟨9260, by rfl⟩) R18521
theorem R12477 : Reach 12477 := rs (se 3 (by rfl) ⟨2339, by rfl⟩) R4679
theorem R12481 : Reach 12481 := rs (se 2 (by rfl) ⟨4680, by rfl⟩) R9361
theorem R12483 : Reach 12483 := rs (se 1 (by rfl) ⟨9362, by rfl⟩) R18725
theorem R12823 : Reach 12823 := rs (se 1 (by rfl) ⟨9617, by rfl⟩) R19235
theorem R12829 : Reach 12829 := rs (se 3 (by rfl) ⟨2405, by rfl⟩) R4811
theorem R12833 : Reach 12833 := rs (se 2 (by rfl) ⟨4812, by rfl⟩) R9625
theorem R12941 : Reach 12941 := rs (se 3 (by rfl) ⟨2426, by rfl⟩) R4853
theorem R12971 : Reach 12971 := rs (se 1 (by rfl) ⟨9728, by rfl⟩) R19457
theorem R12973 : Reach 12973 := rs (se 3 (by rfl) ⟨2432, by rfl⟩) R4865
theorem R12977 : Reach 12977 := rs (se 2 (by rfl) ⟨4866, by rfl⟩) R9733
theorem R12989 : Reach 12989 := rs (se 3 (by rfl) ⟨2435, by rfl⟩) R4871
theorem R13037 : Reach 13037 := rs (se 3 (by rfl) ⟨2444, by rfl⟩) R4889
theorem R13099 : Reach 13099 := rs (se 1 (by rfl) ⟨9824, by rfl⟩) R19649
theorem R13127 : Reach 13127 := rs (se 1 (by rfl) ⟨9845, by rfl⟩) R19691
theorem R13217 : Reach 13217 := rs (se 2 (by rfl) ⟨4956, by rfl⟩) R9913
theorem R13223 : Reach 13223 := rs (se 1 (by rfl) ⟨9917, by rfl⟩) R19835
theorem R13375 : Reach 13375 := rs (se 1 (by rfl) ⟨10031, by rfl⟩) R20063
theorem R46307 : Reach 46307 := rs (se 1 (by rfl) ⟨34730, by rfl⟩) R69461
theorem R14225 : Reach 14225 := rs (se 2 (by rfl) ⟨5334, by rfl⟩) R10669
theorem R14237 : Reach 14237 := rs (se 3 (by rfl) ⟨2669, by rfl⟩) R5339
theorem R14251 : Reach 14251 := rs (se 1 (by rfl) ⟨10688, by rfl⟩) R21377
theorem R14261 : Reach 14261 := rs (se 5 (by rfl) ⟨668, by rfl⟩) R1337
theorem R14267 : Reach 14267 := rs (se 1 (by rfl) ⟨10700, by rfl⟩) R21401
theorem R14273 : Reach 14273 := rs (se 2 (by rfl) ⟨5352, by rfl⟩) R10705
theorem R47051 : Reach 47051 := rs (se 1 (by rfl) ⟨35288, by rfl⟩) R70577
theorem R14305 : Reach 14305 := rs (se 2 (by rfl) ⟨5364, by rfl⟩) R10729
theorem R14315 : Reach 14315 := rs (se 1 (by rfl) ⟨10736, by rfl⟩) R21473
theorem R47303 : Reach 47303 := rs (se 1 (by rfl) ⟨35477, by rfl⟩) R70955
theorem R47537 : Reach 47537 := rs (se 2 (by rfl) ⟨17826, by rfl⟩) R35653
theorem R47735 : Reach 47735 := rs (se 1 (by rfl) ⟨35801, by rfl⟩) R71603
theorem R211729 : Reach 211729 := rs (se 2 (by rfl) ⟨79398, by rfl⟩) R158797
theorem R51293 : Reach 51293 := rs (se 3 (by rfl) ⟨9617, by rfl⟩) R19235
theorem R51941 : Reach 51941 := rs (se 4 (by rfl) ⟨4869, by rfl⟩) R9739
theorem R52001 : Reach 52001 := rs (se 2 (by rfl) ⟨19500, by rfl⟩) R39001
theorem R52397 : Reach 52397 := rs (se 3 (by rfl) ⟨9824, by rfl⟩) R19649
theorem R52883 : Reach 52883 := rs (se 1 (by rfl) ⟨39662, by rfl⟩) R79325
theorem R53821 : Reach 53821 := rs (se 3 (by rfl) ⟨10091, by rfl⟩) R20183
theorem R23093 : Reach 23093 := rs (se 5 (by rfl) ⟨1082, by rfl⟩) R2165
theorem R23125 : Reach 23125 := rs (se 8 (by rfl) ⟨135, by rfl⟩) R271
theorem R23237 : Reach 23237 := rs (se 4 (by rfl) ⟨2178, by rfl⟩) R4357
theorem R23267 : Reach 23267 := rs (se 1 (by rfl) ⟨17450, by rfl⟩) R34901
theorem R23525 : Reach 23525 := rs (se 4 (by rfl) ⟨2205, by rfl⟩) R4411
theorem R23597 : Reach 23597 := rs (se 3 (by rfl) ⟨4424, by rfl⟩) R8849
theorem R23773 : Reach 23773 := rs (se 3 (by rfl) ⟨4457, by rfl⟩) R8915
theorem R23813 : Reach 23813 := rs (se 4 (by rfl) ⟨2232, by rfl⟩) R4465
theorem R23867 : Reach 23867 := rs (se 1 (by rfl) ⟨17900, by rfl⟩) R35801
theorem R23921 : Reach 23921 := rs (se 2 (by rfl) ⟨8970, by rfl⟩) R17941
theorem R23939 : Reach 23939 := rs (se 1 (by rfl) ⟨17954, by rfl⟩) R35909
theorem R23951 : Reach 23951 := rs (se 1 (by rfl) ⟨17963, by rfl⟩) R35927
theorem R23957 : Reach 23957 := rs (se 6 (by rfl) ⟨561, by rfl⟩) R1123
theorem R23989 : Reach 23989 := rs (se 5 (by rfl) ⟨1124, by rfl⟩) R2249
theorem R23993 : Reach 23993 := rs (se 2 (by rfl) ⟨8997, by rfl⟩) R17995
theorem R56999 : Reach 56999 := rs (se 1 (by rfl) ⟨42749, by rfl⟩) R85499
theorem R57185 : Reach 57185 := rs (se 2 (by rfl) ⟨21444, by rfl⟩) R42889
theorem R24533 : Reach 24533 := rs (se 7 (by rfl) ⟨287, by rfl⟩) R575
theorem R24581 : Reach 24581 := rs (se 4 (by rfl) ⟨2304, by rfl⟩) R4609
theorem R24583 : Reach 24583 := rs (se 1 (by rfl) ⟨18437, by rfl⟩) R36875
theorem R24587 : Reach 24587 := rs (se 1 (by rfl) ⟨18440, by rfl⟩) R36881
theorem R24695 : Reach 24695 := rs (se 1 (by rfl) ⟨18521, by rfl⟩) R37043
theorem R24965 : Reach 24965 := rs (se 4 (by rfl) ⟨2340, by rfl⟩) R4681
theorem R25001 : Reach 25001 := rs (se 2 (by rfl) ⟨9375, by rfl⟩) R18751
theorem R25649 : Reach 25649 := rs (se 2 (by rfl) ⟨9618, by rfl⟩) R19237
theorem R25667 : Reach 25667 := rs (se 1 (by rfl) ⟨19250, by rfl⟩) R38501
theorem R25703 : Reach 25703 := rs (se 1 (by rfl) ⟨19277, by rfl⟩) R38555
theorem R25739 : Reach 25739 := rs (se 1 (by rfl) ⟨19304, by rfl⟩) R38609
theorem R25901 : Reach 25901 := rs (se 3 (by rfl) ⟨4856, by rfl⟩) R9713
theorem R25955 : Reach 25955 := rs (se 1 (by rfl) ⟨19466, by rfl⟩) R38933
theorem R26237 : Reach 26237 := rs (se 3 (by rfl) ⟨4919, by rfl⟩) R9839
theorem R26441 : Reach 26441 := rs (se 2 (by rfl) ⟨9915, by rfl⟩) R19831
theorem R26449 : Reach 26449 := rs (se 2 (by rfl) ⟨9918, by rfl⟩) R19837
theorem R26747 : Reach 26747 := rs (se 1 (by rfl) ⟨20060, by rfl⟩) R40121
theorem R26909 : Reach 26909 := rs (se 3 (by rfl) ⟨5045, by rfl⟩) R10091
theorem R28451 : Reach 28451 := rs (se 1 (by rfl) ⟨21338, by rfl⟩) R42677
theorem R28471 : Reach 28471 := rs (se 1 (by rfl) ⟨21353, by rfl⟩) R42707
theorem R28475 : Reach 28475 := rs (se 1 (by rfl) ⟨21356, by rfl⟩) R42713
theorem R28493 : Reach 28493 := rs (se 3 (by rfl) ⟨5342, by rfl⟩) R10685
theorem R28529 : Reach 28529 := rs (se 2 (by rfl) ⟨10698, by rfl⟩) R21397
theorem R28547 : Reach 28547 := rs (se 1 (by rfl) ⟨21410, by rfl⟩) R42821
theorem R28601 : Reach 28601 := rs (se 2 (by rfl) ⟨10725, by rfl⟩) R21451
theorem R32777 : Reach 32777 := rs (se 2 (by rfl) ⟨12291, by rfl⟩) R24583
theorem R65549 : Reach 65549 := rs (se 3 (by rfl) ⟨12290, by rfl⟩) R24581
theorem R123 : Reach 123 := rs (se 1 (by rfl) ⟨92, by rfl⟩) R185
theorem R127 : Reach 127 := rs (se 1 (by rfl) ⟨95, by rfl⟩) R191
theorem R247 : Reach 247 := rs (se 1 (by rfl) ⟨185, by rfl⟩) R371
theorem R249 : Reach 249 := rs (se 2 (by rfl) ⟨93, by rfl⟩) R187
theorem R255 : Reach 255 := rs (se 1 (by rfl) ⟨191, by rfl⟩) R383
theorem R481 : Reach 481 := rs (se 2 (by rfl) ⟨180, by rfl⟩) R361
theorem R489 : Reach 489 := rs (se 2 (by rfl) ⟨183, by rfl⟩) R367
theorem R493 : Reach 493 := rs (se 3 (by rfl) ⟨92, by rfl⟩) R185
theorem R499 : Reach 499 := rs (se 1 (by rfl) ⟨374, by rfl⟩) R749
theorem R509 : Reach 509 := rs (se 3 (by rfl) ⟨95, by rfl⟩) R191
theorem R539 : Reach 539 := rs (se 1 (by rfl) ⟨404, by rfl⟩) R809
theorem R961 : Reach 961 := rs (se 2 (by rfl) ⟨360, by rfl⟩) R721
theorem R963 : Reach 963 := rs (se 1 (by rfl) ⟨722, by rfl⟩) R1445
theorem R969 : Reach 969 := rs (se 2 (by rfl) ⟨363, by rfl⟩) R727
theorem R979 : Reach 979 := rs (se 1 (by rfl) ⟨734, by rfl⟩) R1469
theorem R989 : Reach 989 := rs (se 3 (by rfl) ⟨185, by rfl⟩) R371
theorem R997 : Reach 997 := rs (se 4 (by rfl) ⟨93, by rfl⟩) R187
theorem R999 : Reach 999 := rs (se 1 (by rfl) ⟨749, by rfl⟩) R1499
theorem R1021 : Reach 1021 := rs (se 3 (by rfl) ⟨191, by rfl⟩) R383
theorem R1079 : Reach 1079 := rs (se 1 (by rfl) ⟨809, by rfl⟩) R1619
theorem R1191 : Reach 1191 := rs (se 1 (by rfl) ⟨893, by rfl⟩) R1787
theorem R34195 : Reach 34195 := rs (se 1 (by rfl) ⟨25646, by rfl⟩) R51293
theorem R34627 : Reach 34627 := rs (se 1 (by rfl) ⟨25970, by rfl⟩) R51941
theorem R34667 : Reach 34667 := rs (se 1 (by rfl) ⟨26000, by rfl⟩) R52001
theorem R1923 : Reach 1923 := rs (se 1 (by rfl) ⟨1442, by rfl⟩) R2885
theorem R1925 : Reach 1925 := rs (se 4 (by rfl) ⟨180, by rfl⟩) R361
theorem R1927 : Reach 1927 := rs (se 1 (by rfl) ⟨1445, by rfl⟩) R2891
theorem R1937 : Reach 1937 := rs (se 2 (by rfl) ⟨726, by rfl⟩) R1453
theorem R1939 : Reach 1939 := rs (se 1 (by rfl) ⟨1454, by rfl⟩) R2909
theorem R1957 : Reach 1957 := rs (se 4 (by rfl) ⟨183, by rfl⟩) R367
theorem R1973 : Reach 1973 := rs (se 5 (by rfl) ⟨92, by rfl⟩) R185
theorem R1983 : Reach 1983 := rs (se 1 (by rfl) ⟨1487, by rfl⟩) R2975
theorem R1985 : Reach 1985 := rs (se 2 (by rfl) ⟨744, by rfl⟩) R1489
theorem R1991 : Reach 1991 := rs (se 1 (by rfl) ⟨1493, by rfl⟩) R2987
theorem R1993 : Reach 1993 := rs (se 2 (by rfl) ⟨747, by rfl⟩) R1495
theorem R1995 : Reach 1995 := rs (se 1 (by rfl) ⟨1496, by rfl⟩) R2993
theorem R1997 : Reach 1997 := rs (se 3 (by rfl) ⟨374, by rfl⟩) R749
theorem R1999 : Reach 1999 := rs (se 1 (by rfl) ⟨1499, by rfl⟩) R2999
theorem R2001 : Reach 2001 := rs (se 2 (by rfl) ⟨750, by rfl⟩) R1501
theorem R2037 : Reach 2037 := rs (se 5 (by rfl) ⟨95, by rfl⟩) R191
theorem R133123 : Reach 133123 := rs (se 1 (by rfl) ⟨99842, by rfl⟩) R199685
theorem R2079 : Reach 2079 := rs (se 1 (by rfl) ⟨1559, by rfl⟩) R3119
theorem R2157 : Reach 2157 := rs (se 3 (by rfl) ⟨404, by rfl⟩) R809
theorem R34931 : Reach 34931 := rs (se 1 (by rfl) ⟨26198, by rfl⟩) R52397
theorem R2171 : Reach 2171 := rs (se 1 (by rfl) ⟨1628, by rfl⟩) R3257
theorem R2203 : Reach 2203 := rs (se 1 (by rfl) ⟨1652, by rfl⟩) R3305
theorem R2377 : Reach 2377 := rs (se 2 (by rfl) ⟨891, by rfl⟩) R1783
theorem R2383 : Reach 2383 := rs (se 1 (by rfl) ⟨1787, by rfl⟩) R3575
theorem R35255 : Reach 35255 := rs (se 1 (by rfl) ⟨26441, by rfl⟩) R52883
theorem R35261 : Reach 35261 := rs (se 3 (by rfl) ⟨6611, by rfl⟩) R13223
theorem R3845 : Reach 3845 := rs (se 4 (by rfl) ⟨360, by rfl⟩) R721
theorem R3853 : Reach 3853 := rs (se 3 (by rfl) ⟨722, by rfl⟩) R1445
theorem R3855 : Reach 3855 := rs (se 1 (by rfl) ⟨2891, by rfl⟩) R5783
theorem R3857 : Reach 3857 := rs (se 2 (by rfl) ⟨1446, by rfl⟩) R2893
theorem R3873 : Reach 3873 := rs (se 2 (by rfl) ⟨1452, by rfl⟩) R2905
theorem R3875 : Reach 3875 := rs (se 1 (by rfl) ⟨2906, by rfl⟩) R5813
theorem R3877 : Reach 3877 := rs (se 4 (by rfl) ⟨363, by rfl⟩) R727
theorem R3883 : Reach 3883 := rs (se 1 (by rfl) ⟨2912, by rfl⟩) R5825
theorem R3887 : Reach 3887 := rs (se 1 (by rfl) ⟨2915, by rfl⟩) R5831
theorem R3917 : Reach 3917 := rs (se 3 (by rfl) ⟨734, by rfl⟩) R1469
theorem R3921 : Reach 3921 := rs (se 2 (by rfl) ⟨1470, by rfl⟩) R2941
theorem R3953 : Reach 3953 := rs (se 2 (by rfl) ⟨1482, by rfl⟩) R2965
theorem R3957 : Reach 3957 := rs (se 5 (by rfl) ⟨185, by rfl⟩) R371
theorem R3961 : Reach 3961 := rs (se 2 (by rfl) ⟨1485, by rfl⟩) R2971
theorem R3963 : Reach 3963 := rs (se 1 (by rfl) ⟨2972, by rfl⟩) R5945
theorem R3967 : Reach 3967 := rs (se 1 (by rfl) ⟨2975, by rfl⟩) R5951
theorem R3971 : Reach 3971 := rs (se 1 (by rfl) ⟨2978, by rfl⟩) R5957
theorem R3975 : Reach 3975 := rs (se 1 (by rfl) ⟨2981, by rfl⟩) R5963
theorem R3983 : Reach 3983 := rs (se 1 (by rfl) ⟨2987, by rfl⟩) R5975
theorem R3985 : Reach 3985 := rs (se 2 (by rfl) ⟨1494, by rfl⟩) R2989
theorem R3987 : Reach 3987 := rs (se 1 (by rfl) ⟨2990, by rfl⟩) R5981
theorem R3989 : Reach 3989 := rs (se 6 (by rfl) ⟨93, by rfl⟩) R187
theorem R3991 : Reach 3991 := rs (se 1 (by rfl) ⟨2993, by rfl⟩) R5987
theorem R3993 : Reach 3993 := rs (se 2 (by rfl) ⟨1497, by rfl⟩) R2995
theorem R3997 : Reach 3997 := rs (se 3 (by rfl) ⟨749, by rfl⟩) R1499
theorem R4003 : Reach 4003 := rs (se 1 (by rfl) ⟨3002, by rfl⟩) R6005
theorem R4081 : Reach 4081 := rs (se 2 (by rfl) ⟨1530, by rfl⟩) R3061
theorem R4085 : Reach 4085 := rs (se 5 (by rfl) ⟨191, by rfl⟩) R383
theorem R4159 : Reach 4159 := rs (se 1 (by rfl) ⟨3119, by rfl⟩) R6239
theorem R4313 : Reach 4313 := rs (se 2 (by rfl) ⟨1617, by rfl⟩) R3235
theorem R4317 : Reach 4317 := rs (se 3 (by rfl) ⟨809, by rfl⟩) R1619
theorem R4329 : Reach 4329 := rs (se 2 (by rfl) ⟨1623, by rfl⟩) R3247
theorem R4343 : Reach 4343 := rs (se 1 (by rfl) ⟨3257, by rfl⟩) R6515
theorem R4345 : Reach 4345 := rs (se 2 (by rfl) ⟨1629, by rfl⟩) R3259
theorem R69923 : Reach 69923 := rs (se 1 (by rfl) ⟨52442, by rfl⟩) R104885
theorem R4407 : Reach 4407 := rs (se 1 (by rfl) ⟨3305, by rfl⟩) R6611
theorem R4745 : Reach 4745 := rs (se 2 (by rfl) ⟨1779, by rfl⟩) R3559
theorem R4753 : Reach 4753 := rs (se 2 (by rfl) ⟨1782, by rfl⟩) R3565
theorem R4755 : Reach 4755 := rs (se 1 (by rfl) ⟨3566, by rfl⟩) R7133
theorem R4765 : Reach 4765 := rs (se 3 (by rfl) ⟨893, by rfl⟩) R1787
theorem R37961 : Reach 37961 := rs (se 2 (by rfl) ⟨14235, by rfl⟩) R28471
theorem R37999 : Reach 37999 := rs (se 1 (by rfl) ⟨28499, by rfl⟩) R56999
theorem R38029 : Reach 38029 := rs (se 3 (by rfl) ⟨7130, by rfl⟩) R14261
theorem R38123 : Reach 38123 := rs (se 1 (by rfl) ⟨28592, by rfl⟩) R57185
theorem R71761 : Reach 71761 := rs (se 2 (by rfl) ⟨26910, by rfl⟩) R53821
theorem R138509 : Reach 138509 := rs (se 3 (by rfl) ⟨25970, by rfl⟩) R51941
theorem R7693 : Reach 7693 := rs (se 3 (by rfl) ⟨1442, by rfl⟩) R2885
theorem R7697 : Reach 7697 := rs (se 2 (by rfl) ⟨2886, by rfl⟩) R5773
theorem R7701 : Reach 7701 := rs (se 6 (by rfl) ⟨180, by rfl⟩) R361
theorem R7709 : Reach 7709 := rs (se 3 (by rfl) ⟨1445, by rfl⟩) R2891
theorem R7715 : Reach 7715 := rs (se 1 (by rfl) ⟨5786, by rfl⟩) R11573
theorem R7719 : Reach 7719 := rs (se 1 (by rfl) ⟨5789, by rfl⟩) R11579
theorem R7723 : Reach 7723 := rs (se 1 (by rfl) ⟨5792, by rfl⟩) R11585
theorem R7745 : Reach 7745 := rs (se 2 (by rfl) ⟨2904, by rfl⟩) R5809
theorem R7747 : Reach 7747 := rs (se 1 (by rfl) ⟨5810, by rfl⟩) R11621
theorem R7749 : Reach 7749 := rs (se 4 (by rfl) ⟨726, by rfl⟩) R1453
theorem R7755 : Reach 7755 := rs (se 1 (by rfl) ⟨5816, by rfl⟩) R11633
theorem R7757 : Reach 7757 := rs (se 3 (by rfl) ⟨1454, by rfl⟩) R2909
theorem R7767 : Reach 7767 := rs (se 1 (by rfl) ⟨5825, by rfl⟩) R11651
theorem R7775 : Reach 7775 := rs (se 1 (by rfl) ⟨5831, by rfl⟩) R11663
theorem R7829 : Reach 7829 := rs (se 6 (by rfl) ⟨183, by rfl⟩) R367
theorem R7841 : Reach 7841 := rs (se 2 (by rfl) ⟨2940, by rfl⟩) R5881
theorem R7843 : Reach 7843 := rs (se 1 (by rfl) ⟨5882, by rfl⟩) R11765
theorem R7865 : Reach 7865 := rs (se 2 (by rfl) ⟨2949, by rfl⟩) R5899
theorem R7867 : Reach 7867 := rs (se 1 (by rfl) ⟨5900, by rfl⟩) R11801
theorem R7893 : Reach 7893 := rs (se 7 (by rfl) ⟨92, by rfl⟩) R185
theorem R7907 : Reach 7907 := rs (se 1 (by rfl) ⟨5930, by rfl⟩) R11861
theorem R7921 : Reach 7921 := rs (se 2 (by rfl) ⟨2970, by rfl⟩) R5941
theorem R7923 : Reach 7923 := rs (se 1 (by rfl) ⟨5942, by rfl⟩) R11885
theorem R7927 : Reach 7927 := rs (se 1 (by rfl) ⟨5945, by rfl⟩) R11891
theorem R7933 : Reach 7933 := rs (se 3 (by rfl) ⟨1487, by rfl⟩) R2975
theorem R7937 : Reach 7937 := rs (se 2 (by rfl) ⟨2976, by rfl⟩) R5953
theorem R7941 : Reach 7941 := rs (se 4 (by rfl) ⟨744, by rfl⟩) R1489
theorem R7947 : Reach 7947 := rs (se 1 (by rfl) ⟨5960, by rfl⟩) R11921
theorem R7951 : Reach 7951 := rs (se 1 (by rfl) ⟨5963, by rfl⟩) R11927
theorem R7965 : Reach 7965 := rs (se 3 (by rfl) ⟨1493, by rfl⟩) R2987
theorem R7969 : Reach 7969 := rs (se 2 (by rfl) ⟨2988, by rfl⟩) R5977
theorem R7971 : Reach 7971 := rs (se 1 (by rfl) ⟨5978, by rfl⟩) R11957
theorem R7973 : Reach 7973 := rs (se 4 (by rfl) ⟨747, by rfl⟩) R1495
theorem R7977 : Reach 7977 := rs (se 2 (by rfl) ⟨2991, by rfl⟩) R5983
theorem R7979 : Reach 7979 := rs (se 1 (by rfl) ⟨5984, by rfl⟩) R11969
theorem R7981 : Reach 7981 := rs (se 3 (by rfl) ⟨1496, by rfl⟩) R2993
theorem R7983 : Reach 7983 := rs (se 1 (by rfl) ⟨5987, by rfl⟩) R11975
theorem R7985 : Reach 7985 := rs (se 2 (by rfl) ⟨2994, by rfl⟩) R5989
theorem R7987 : Reach 7987 := rs (se 1 (by rfl) ⟨5990, by rfl⟩) R11981
theorem R7989 : Reach 7989 := rs (se 5 (by rfl) ⟨374, by rfl⟩) R749
theorem R7995 : Reach 7995 := rs (se 1 (by rfl) ⟨5996, by rfl⟩) R11993
theorem R7997 : Reach 7997 := rs (se 3 (by rfl) ⟨1499, by rfl⟩) R2999
theorem R8001 : Reach 8001 := rs (se 2 (by rfl) ⟨3000, by rfl⟩) R6001
theorem R8005 : Reach 8005 := rs (se 4 (by rfl) ⟨750, by rfl⟩) R1501
theorem R8011 : Reach 8011 := rs (se 1 (by rfl) ⟨6008, by rfl⟩) R12017
theorem R8043 : Reach 8043 := rs (se 1 (by rfl) ⟨6032, by rfl⟩) R12065
theorem R8059 : Reach 8059 := rs (se 1 (by rfl) ⟨6044, by rfl⟩) R12089
theorem R8149 : Reach 8149 := rs (se 7 (by rfl) ⟨95, by rfl⟩) R191
theorem R8163 : Reach 8163 := rs (se 1 (by rfl) ⟨6122, by rfl⟩) R12245
theorem R8177 : Reach 8177 := rs (se 2 (by rfl) ⟨3066, by rfl⟩) R6133
theorem R8193 : Reach 8193 := rs (se 2 (by rfl) ⟨3072, by rfl⟩) R6145
theorem R8231 : Reach 8231 := rs (se 1 (by rfl) ⟨6173, by rfl⟩) R12347
theorem R8317 : Reach 8317 := rs (se 3 (by rfl) ⟨1559, by rfl⟩) R3119
theorem R8321 : Reach 8321 := rs (se 2 (by rfl) ⟨3120, by rfl⟩) R6241
theorem R8553 : Reach 8553 := rs (se 2 (by rfl) ⟨3207, by rfl⟩) R6415
theorem R8555 : Reach 8555 := rs (se 1 (by rfl) ⟨6416, by rfl⟩) R12833
theorem R8625 : Reach 8625 := rs (se 2 (by rfl) ⟨3234, by rfl⟩) R6469
theorem R8627 : Reach 8627 := rs (se 1 (by rfl) ⟨6470, by rfl⟩) R12941
theorem R8629 : Reach 8629 := rs (se 5 (by rfl) ⟨404, by rfl⟩) R809
theorem R8633 : Reach 8633 := rs (se 2 (by rfl) ⟨3237, by rfl⟩) R6475
theorem R8647 : Reach 8647 := rs (se 1 (by rfl) ⟨6485, by rfl⟩) R12971
theorem R8649 : Reach 8649 := rs (se 2 (by rfl) ⟨3243, by rfl⟩) R6487
theorem R8651 : Reach 8651 := rs (se 1 (by rfl) ⟨6488, by rfl⟩) R12977
theorem R8659 : Reach 8659 := rs (se 1 (by rfl) ⟨6494, by rfl⟩) R12989
theorem R8685 : Reach 8685 := rs (se 3 (by rfl) ⟨1628, by rfl⟩) R3257
theorem R8691 : Reach 8691 := rs (se 1 (by rfl) ⟨6518, by rfl⟩) R13037
theorem R8745 : Reach 8745 := rs (se 2 (by rfl) ⟨3279, by rfl⟩) R6559
theorem R8751 : Reach 8751 := rs (se 1 (by rfl) ⟨6563, by rfl⟩) R13127
theorem R8811 : Reach 8811 := rs (se 1 (by rfl) ⟨6608, by rfl⟩) R13217
theorem R8813 : Reach 8813 := rs (se 3 (by rfl) ⟨1652, by rfl⟩) R3305
theorem R8815 : Reach 8815 := rs (se 1 (by rfl) ⟨6611, by rfl⟩) R13223
theorem R8969 : Reach 8969 := rs (se 2 (by rfl) ⟨3363, by rfl⟩) R6727
theorem R9483 : Reach 9483 := rs (se 1 (by rfl) ⟨7112, by rfl⟩) R14225
theorem R9491 : Reach 9491 := rs (se 1 (by rfl) ⟨7118, by rfl⟩) R14237
theorem R9497 : Reach 9497 := rs (se 2 (by rfl) ⟨3561, by rfl⟩) R7123
theorem R9507 : Reach 9507 := rs (se 1 (by rfl) ⟨7130, by rfl⟩) R14261
theorem R9509 : Reach 9509 := rs (se 4 (by rfl) ⟨891, by rfl⟩) R1783
theorem R9511 : Reach 9511 := rs (se 1 (by rfl) ⟨7133, by rfl⟩) R14267
theorem R9515 : Reach 9515 := rs (se 1 (by rfl) ⟨7136, by rfl⟩) R14273
theorem R9533 : Reach 9533 := rs (se 3 (by rfl) ⟨1787, by rfl⟩) R3575
theorem R9543 : Reach 9543 := rs (se 1 (by rfl) ⟨7157, by rfl⟩) R14315
theorem R141061 : Reach 141061 := rs (se 4 (by rfl) ⟨13224, by rfl⟩) R26449
theorem R15395 : Reach 15395 := rs (se 1 (by rfl) ⟨11546, by rfl⟩) R23093
theorem R15413 : Reach 15413 := rs (se 5 (by rfl) ⟨722, by rfl⟩) R1445
theorem R15491 : Reach 15491 := rs (se 1 (by rfl) ⟨11618, by rfl⟩) R23237
theorem R15509 : Reach 15509 := rs (se 6 (by rfl) ⟨363, by rfl⟩) R727
theorem R15511 : Reach 15511 := rs (se 1 (by rfl) ⟨11633, by rfl⟩) R23267
theorem R15533 : Reach 15533 := rs (se 3 (by rfl) ⟨2912, by rfl⟩) R5825
theorem R15683 : Reach 15683 := rs (se 1 (by rfl) ⟨11762, by rfl⟩) R23525
theorem R15731 : Reach 15731 := rs (se 1 (by rfl) ⟨11798, by rfl⟩) R23597
theorem R15845 : Reach 15845 := rs (se 4 (by rfl) ⟨1485, by rfl⟩) R2971
theorem R15869 : Reach 15869 := rs (se 3 (by rfl) ⟨2975, by rfl⟩) R5951
theorem R15875 : Reach 15875 := rs (se 1 (by rfl) ⟨11906, by rfl⟩) R23813
theorem R15889 : Reach 15889 := rs (se 2 (by rfl) ⟨5958, by rfl⟩) R11917
theorem R15911 : Reach 15911 := rs (se 1 (by rfl) ⟨11933, by rfl⟩) R23867
theorem R15941 : Reach 15941 := rs (se 4 (by rfl) ⟨1494, by rfl⟩) R2989
theorem R15947 : Reach 15947 := rs (se 1 (by rfl) ⟨11960, by rfl⟩) R23921
theorem R15953 : Reach 15953 := rs (se 2 (by rfl) ⟨5982, by rfl⟩) R11965
theorem R15959 : Reach 15959 := rs (se 1 (by rfl) ⟨11969, by rfl⟩) R23939
theorem R15965 : Reach 15965 := rs (se 3 (by rfl) ⟨2993, by rfl⟩) R5987
theorem R15967 : Reach 15967 := rs (se 1 (by rfl) ⟨11975, by rfl⟩) R23951
theorem R15971 : Reach 15971 := rs (se 1 (by rfl) ⟨11978, by rfl⟩) R23957
theorem R15989 : Reach 15989 := rs (se 5 (by rfl) ⟨749, by rfl⟩) R1499
theorem R15995 : Reach 15995 := rs (se 1 (by rfl) ⟨11996, by rfl⟩) R23993
theorem R16013 : Reach 16013 := rs (se 3 (by rfl) ⟨3002, by rfl⟩) R6005
theorem R16325 : Reach 16325 := rs (se 4 (by rfl) ⟨1530, by rfl⟩) R3061
theorem R16355 : Reach 16355 := rs (se 1 (by rfl) ⟨12266, by rfl⟩) R24533
theorem R16385 : Reach 16385 := rs (se 2 (by rfl) ⟨6144, by rfl⟩) R12289
theorem R16391 : Reach 16391 := rs (se 1 (by rfl) ⟨12293, by rfl⟩) R24587
theorem R16463 : Reach 16463 := rs (se 1 (by rfl) ⟨12347, by rfl⟩) R24695
theorem R16637 : Reach 16637 := rs (se 3 (by rfl) ⟨3119, by rfl⟩) R6239
theorem R16643 : Reach 16643 := rs (se 1 (by rfl) ⟨12482, by rfl⟩) R24965
theorem R16667 : Reach 16667 := rs (se 1 (by rfl) ⟨12500, by rfl⟩) R25001
theorem R17099 : Reach 17099 := rs (se 1 (by rfl) ⟨12824, by rfl⟩) R25649
theorem R17105 : Reach 17105 := rs (se 2 (by rfl) ⟨6414, by rfl⟩) R12829
theorem R17111 : Reach 17111 := rs (se 1 (by rfl) ⟨12833, by rfl⟩) R25667
theorem R17135 : Reach 17135 := rs (se 1 (by rfl) ⟨12851, by rfl⟩) R25703
theorem R17159 : Reach 17159 := rs (se 1 (by rfl) ⟨12869, by rfl⟩) R25739
theorem R17267 : Reach 17267 := rs (se 1 (by rfl) ⟨12950, by rfl⟩) R25901
theorem R17297 : Reach 17297 := rs (se 2 (by rfl) ⟨6486, by rfl⟩) R12973
theorem R17303 : Reach 17303 := rs (se 1 (by rfl) ⟨12977, by rfl⟩) R25955
theorem R17381 : Reach 17381 := rs (se 4 (by rfl) ⟨1629, by rfl⟩) R3259
theorem R17465 : Reach 17465 := rs (se 2 (by rfl) ⟨6549, by rfl⟩) R13099
theorem R17491 : Reach 17491 := rs (se 1 (by rfl) ⟨13118, by rfl⟩) R26237
theorem R17627 : Reach 17627 := rs (se 1 (by rfl) ⟨13220, by rfl⟩) R26441
theorem R17831 : Reach 17831 := rs (se 1 (by rfl) ⟨13373, by rfl⟩) R26747
theorem R17833 : Reach 17833 := rs (se 2 (by rfl) ⟨6687, by rfl⟩) R13375
theorem R17939 : Reach 17939 := rs (se 1 (by rfl) ⟨13454, by rfl⟩) R26909
theorem R18967 : Reach 18967 := rs (se 1 (by rfl) ⟨14225, by rfl⟩) R28451
theorem R18983 : Reach 18983 := rs (se 1 (by rfl) ⟨14237, by rfl⟩) R28475
theorem R18995 : Reach 18995 := rs (se 1 (by rfl) ⟨14246, by rfl⟩) R28493
theorem R19001 : Reach 19001 := rs (se 2 (by rfl) ⟨7125, by rfl⟩) R14251
theorem R19013 : Reach 19013 := rs (se 4 (by rfl) ⟨1782, by rfl⟩) R3565
theorem R19019 : Reach 19019 := rs (se 1 (by rfl) ⟨14264, by rfl⟩) R28529
theorem R19021 : Reach 19021 := rs (se 3 (by rfl) ⟨3566, by rfl⟩) R7133
theorem R19031 : Reach 19031 := rs (se 1 (by rfl) ⟨14273, by rfl⟩) R28547
theorem R19061 : Reach 19061 := rs (se 5 (by rfl) ⟨893, by rfl⟩) R1787
theorem R19067 : Reach 19067 := rs (se 1 (by rfl) ⟨14300, by rfl⟩) R28601
theorem R19073 : Reach 19073 := rs (se 2 (by rfl) ⟨7152, by rfl⟩) R14305
theorem R282305 : Reach 282305 := rs (se 2 (by rfl) ⟨105864, by rfl⟩) R211729
theorem R151733 : Reach 151733 := rs (se 5 (by rfl) ⟨7112, by rfl⟩) R14225
theorem R62045 : Reach 62045 := rs (se 3 (by rfl) ⟨11633, by rfl⟩) R23267
theorem R63317 : Reach 63317 := rs (se 9 (by rfl) ⟨185, by rfl⟩) R371
theorem R30833 : Reach 30833 := rs (se 2 (by rfl) ⟨11562, by rfl⟩) R23125
theorem R63605 : Reach 63605 := rs (se 5 (by rfl) ⟨2981, by rfl⟩) R5963
theorem R30871 : Reach 30871 := rs (se 1 (by rfl) ⟨23153, by rfl⟩) R46307
theorem R31367 : Reach 31367 := rs (se 1 (by rfl) ⟨23525, by rfl⟩) R47051
theorem R31373 : Reach 31373 := rs (se 3 (by rfl) ⟨5882, by rfl⟩) R11765
theorem R31535 : Reach 31535 := rs (se 1 (by rfl) ⟨23651, by rfl⟩) R47303
theorem R31691 : Reach 31691 := rs (se 1 (by rfl) ⟨23768, by rfl⟩) R47537
theorem R31697 : Reach 31697 := rs (se 2 (by rfl) ⟨11886, by rfl⟩) R23773
theorem R31789 : Reach 31789 := rs (se 3 (by rfl) ⟨5960, by rfl⟩) R11921
theorem R31805 : Reach 31805 := rs (se 3 (by rfl) ⟨5963, by rfl⟩) R11927
theorem R31823 : Reach 31823 := rs (se 1 (by rfl) ⟨23867, by rfl⟩) R47735
theorem R31909 : Reach 31909 := rs (se 4 (by rfl) ⟨2991, by rfl⟩) R5983
theorem R31985 : Reach 31985 := rs (se 2 (by rfl) ⟨11994, by rfl⟩) R23989
theorem R32021 : Reach 32021 := rs (se 6 (by rfl) ⟨750, by rfl⟩) R1501
theorem R32237 : Reach 32237 := rs (se 3 (by rfl) ⟨6044, by rfl⟩) R12089
theorem R169 : Reach 169 := rs (se 2 (by rfl) ⟨63, by rfl⟩) R127
theorem R329 : Reach 329 := rs (se 2 (by rfl) ⟨123, by rfl⟩) R247
theorem R339 : Reach 339 := rs (se 1 (by rfl) ⟨254, by rfl⟩) R509
theorem R359 : Reach 359 := rs (se 1 (by rfl) ⟨269, by rfl⟩) R539
theorem R641 : Reach 641 := rs (se 2 (by rfl) ⟨240, by rfl⟩) R481
theorem R657 : Reach 657 := rs (se 2 (by rfl) ⟨246, by rfl⟩) R493
theorem R659 : Reach 659 := rs (se 1 (by rfl) ⟨494, by rfl⟩) R989
theorem R665 : Reach 665 := rs (se 2 (by rfl) ⟨249, by rfl⟩) R499
theorem R677 : Reach 677 := rs (se 4 (by rfl) ⟨63, by rfl⟩) R127
theorem R719 : Reach 719 := rs (se 1 (by rfl) ⟨539, by rfl⟩) R1079
theorem R1281 : Reach 1281 := rs (se 2 (by rfl) ⟨480, by rfl⟩) R961
theorem R1283 : Reach 1283 := rs (se 1 (by rfl) ⟨962, by rfl⟩) R1925
theorem R1291 : Reach 1291 := rs (se 1 (by rfl) ⟨968, by rfl⟩) R1937
theorem R1305 : Reach 1305 := rs (se 2 (by rfl) ⟨489, by rfl⟩) R979
theorem R1315 : Reach 1315 := rs (se 1 (by rfl) ⟨986, by rfl⟩) R1973
theorem R1317 : Reach 1317 := rs (se 4 (by rfl) ⟨123, by rfl⟩) R247
theorem R1323 : Reach 1323 := rs (se 1 (by rfl) ⟨992, by rfl⟩) R1985
theorem R1327 : Reach 1327 := rs (se 1 (by rfl) ⟨995, by rfl⟩) R1991
theorem R1329 : Reach 1329 := rs (se 2 (by rfl) ⟨498, by rfl⟩) R997
theorem R1331 : Reach 1331 := rs (se 1 (by rfl) ⟨998, by rfl⟩) R1997
theorem R1357 : Reach 1357 := rs (se 3 (by rfl) ⟨254, by rfl⟩) R509
theorem R1361 : Reach 1361 := rs (se 2 (by rfl) ⟨510, by rfl⟩) R1021
theorem R1437 : Reach 1437 := rs (se 3 (by rfl) ⟨269, by rfl⟩) R539
theorem R1447 : Reach 1447 := rs (se 1 (by rfl) ⟨1085, by rfl⟩) R2171
theorem R2563 : Reach 2563 := rs (se 1 (by rfl) ⟨1922, by rfl⟩) R3845
theorem R2565 : Reach 2565 := rs (se 4 (by rfl) ⟨240, by rfl⟩) R481
theorem R2569 : Reach 2569 := rs (se 2 (by rfl) ⟨963, by rfl⟩) R1927
theorem R2571 : Reach 2571 := rs (se 1 (by rfl) ⟨1928, by rfl⟩) R3857
theorem R2583 : Reach 2583 := rs (se 1 (by rfl) ⟨1937, by rfl⟩) R3875
theorem R2585 : Reach 2585 := rs (se 2 (by rfl) ⟨969, by rfl⟩) R1939
theorem R2591 : Reach 2591 := rs (se 1 (by rfl) ⟨1943, by rfl⟩) R3887
theorem R2609 : Reach 2609 := rs (se 2 (by rfl) ⟨978, by rfl⟩) R1957
theorem R2611 : Reach 2611 := rs (se 1 (by rfl) ⟨1958, by rfl⟩) R3917
theorem R2629 : Reach 2629 := rs (se 4 (by rfl) ⟨246, by rfl⟩) R493
theorem R2635 : Reach 2635 := rs (se 1 (by rfl) ⟨1976, by rfl⟩) R3953
theorem R2637 : Reach 2637 := rs (se 3 (by rfl) ⟨494, by rfl⟩) R989
theorem R2647 : Reach 2647 := rs (se 1 (by rfl) ⟨1985, by rfl⟩) R3971
theorem R2655 : Reach 2655 := rs (se 1 (by rfl) ⟨1991, by rfl⟩) R3983
theorem R2657 : Reach 2657 := rs (se 2 (by rfl) ⟨996, by rfl⟩) R1993
theorem R2659 : Reach 2659 := rs (se 1 (by rfl) ⟨1994, by rfl⟩) R3989
theorem R2661 : Reach 2661 := rs (se 4 (by rfl) ⟨249, by rfl⟩) R499
theorem R2665 : Reach 2665 := rs (se 2 (by rfl) ⟨999, by rfl⟩) R1999
theorem R2709 : Reach 2709 := rs (se 6 (by rfl) ⟨63, by rfl⟩) R127
theorem R2723 : Reach 2723 := rs (se 1 (by rfl) ⟨2042, by rfl⟩) R4085
theorem R101155 : Reach 101155 := rs (se 1 (by rfl) ⟨75866, by rfl⟩) R151733
theorem R2875 : Reach 2875 := rs (se 1 (by rfl) ⟨2156, by rfl⟩) R4313
theorem R2877 : Reach 2877 := rs (se 3 (by rfl) ⟨539, by rfl⟩) R1079
theorem R2895 : Reach 2895 := rs (se 1 (by rfl) ⟨2171, by rfl⟩) R4343
theorem R2937 : Reach 2937 := rs (se 2 (by rfl) ⟨1101, by rfl⟩) R2203
theorem R3163 : Reach 3163 := rs (se 1 (by rfl) ⟨2372, by rfl⟩) R4745
theorem R3169 : Reach 3169 := rs (se 2 (by rfl) ⟨1188, by rfl⟩) R2377
theorem R3177 : Reach 3177 := rs (se 2 (by rfl) ⟨1191, by rfl⟩) R2383
theorem R5125 : Reach 5125 := rs (se 4 (by rfl) ⟨480, by rfl⟩) R961
theorem R5131 : Reach 5131 := rs (se 1 (by rfl) ⟨3848, by rfl⟩) R7697
theorem R5133 : Reach 5133 := rs (se 3 (by rfl) ⟨962, by rfl⟩) R1925
theorem R5137 : Reach 5137 := rs (se 2 (by rfl) ⟨1926, by rfl⟩) R3853
theorem R5139 : Reach 5139 := rs (se 1 (by rfl) ⟨3854, by rfl⟩) R7709
theorem R5143 : Reach 5143 := rs (se 1 (by rfl) ⟨3857, by rfl⟩) R7715
theorem R5163 : Reach 5163 := rs (se 1 (by rfl) ⟨3872, by rfl⟩) R7745
theorem R5165 : Reach 5165 := rs (se 3 (by rfl) ⟨968, by rfl⟩) R1937
theorem R5169 : Reach 5169 := rs (se 2 (by rfl) ⟨1938, by rfl⟩) R3877
theorem R5171 : Reach 5171 := rs (se 1 (by rfl) ⟨3878, by rfl⟩) R7757
theorem R5177 : Reach 5177 := rs (se 2 (by rfl) ⟨1941, by rfl⟩) R3883
theorem R5183 : Reach 5183 := rs (se 1 (by rfl) ⟨3887, by rfl⟩) R7775
theorem R5219 : Reach 5219 := rs (se 1 (by rfl) ⟨3914, by rfl⟩) R7829
theorem R5221 : Reach 5221 := rs (se 4 (by rfl) ⟨489, by rfl⟩) R979
theorem R5227 : Reach 5227 := rs (se 1 (by rfl) ⟨3920, by rfl⟩) R7841
theorem R5243 : Reach 5243 := rs (se 1 (by rfl) ⟨3932, by rfl⟩) R7865
theorem R5261 : Reach 5261 := rs (se 3 (by rfl) ⟨986, by rfl⟩) R1973
theorem R5269 : Reach 5269 := rs (se 6 (by rfl) ⟨123, by rfl⟩) R247
theorem R5271 : Reach 5271 := rs (se 1 (by rfl) ⟨3953, by rfl⟩) R7907
theorem R5281 : Reach 5281 := rs (se 2 (by rfl) ⟨1980, by rfl⟩) R3961
theorem R5289 : Reach 5289 := rs (se 2 (by rfl) ⟨1983, by rfl⟩) R3967
theorem R5291 : Reach 5291 := rs (se 1 (by rfl) ⟨3968, by rfl⟩) R7937
theorem R5293 : Reach 5293 := rs (se 3 (by rfl) ⟨992, by rfl⟩) R1985
theorem R5309 : Reach 5309 := rs (se 3 (by rfl) ⟨995, by rfl⟩) R1991
theorem R5313 : Reach 5313 := rs (se 2 (by rfl) ⟨1992, by rfl⟩) R3985
theorem R5315 : Reach 5315 := rs (se 1 (by rfl) ⟨3986, by rfl⟩) R7973
theorem R5317 : Reach 5317 := rs (se 4 (by rfl) ⟨498, by rfl⟩) R997
theorem R5319 : Reach 5319 := rs (se 1 (by rfl) ⟨3989, by rfl⟩) R7979
theorem R5321 : Reach 5321 := rs (se 2 (by rfl) ⟨1995, by rfl⟩) R3991
theorem R5323 : Reach 5323 := rs (se 1 (by rfl) ⟨3992, by rfl⟩) R7985
theorem R5325 : Reach 5325 := rs (se 3 (by rfl) ⟨998, by rfl⟩) R1997
theorem R5329 : Reach 5329 := rs (se 2 (by rfl) ⟨1998, by rfl⟩) R3997
theorem R5331 : Reach 5331 := rs (se 1 (by rfl) ⟨3998, by rfl⟩) R7997
theorem R5337 : Reach 5337 := rs (se 2 (by rfl) ⟨2001, by rfl⟩) R4003
theorem R5429 : Reach 5429 := rs (se 5 (by rfl) ⟨254, by rfl⟩) R509
theorem R5441 : Reach 5441 := rs (se 2 (by rfl) ⟨2040, by rfl⟩) R4081
theorem R5445 : Reach 5445 := rs (se 4 (by rfl) ⟨510, by rfl⟩) R1021
theorem R5451 : Reach 5451 := rs (se 1 (by rfl) ⟨4088, by rfl⟩) R8177
theorem R5487 : Reach 5487 := rs (se 1 (by rfl) ⟨4115, by rfl⟩) R8231
theorem R5545 : Reach 5545 := rs (se 2 (by rfl) ⟨2079, by rfl⟩) R4159
theorem R5547 : Reach 5547 := rs (se 1 (by rfl) ⟨4160, by rfl⟩) R8321
theorem R5703 : Reach 5703 := rs (se 1 (by rfl) ⟨4277, by rfl⟩) R8555
theorem R5749 : Reach 5749 := rs (se 5 (by rfl) ⟨269, by rfl⟩) R539
theorem R5751 : Reach 5751 := rs (se 1 (by rfl) ⟨4313, by rfl⟩) R8627
theorem R5755 : Reach 5755 := rs (se 1 (by rfl) ⟨4316, by rfl⟩) R8633
theorem R5767 : Reach 5767 := rs (se 1 (by rfl) ⟨4325, by rfl⟩) R8651
theorem R5789 : Reach 5789 := rs (se 3 (by rfl) ⟨1085, by rfl⟩) R2171
theorem R5793 : Reach 5793 := rs (se 2 (by rfl) ⟨2172, by rfl⟩) R4345
theorem R5875 : Reach 5875 := rs (se 1 (by rfl) ⟨4406, by rfl⟩) R8813
theorem R5979 : Reach 5979 := rs (se 1 (by rfl) ⟨4484, by rfl⟩) R8969
theorem R6327 : Reach 6327 := rs (se 1 (by rfl) ⟨4745, by rfl⟩) R9491
theorem R6331 : Reach 6331 := rs (se 1 (by rfl) ⟨4748, by rfl⟩) R9497
theorem R6337 : Reach 6337 := rs (se 2 (by rfl) ⟨2376, by rfl⟩) R4753
theorem R6339 : Reach 6339 := rs (se 1 (by rfl) ⟨4754, by rfl⟩) R9509
theorem R6343 : Reach 6343 := rs (se 1 (by rfl) ⟨4757, by rfl⟩) R9515
theorem R6353 : Reach 6353 := rs (se 2 (by rfl) ⟨2382, by rfl⟩) R4765
theorem R6355 : Reach 6355 := rs (se 1 (by rfl) ⟨4766, by rfl⟩) R9533
theorem R41161 : Reach 41161 := rs (se 2 (by rfl) ⟨15435, by rfl⟩) R30871
theorem R41309 : Reach 41309 := rs (se 3 (by rfl) ⟨7745, by rfl⟩) R15491
theorem R41363 : Reach 41363 := rs (se 1 (by rfl) ⟨31022, by rfl⟩) R62045
theorem R41957 : Reach 41957 := rs (se 4 (by rfl) ⟨3933, by rfl⟩) R7867
theorem R42211 : Reach 42211 := rs (se 1 (by rfl) ⟨31658, by rfl⟩) R63317
theorem R42277 : Reach 42277 := rs (se 4 (by rfl) ⟨3963, by rfl⟩) R7927
theorem R42385 : Reach 42385 := rs (se 2 (by rfl) ⟨15894, by rfl⟩) R31789
theorem R42403 : Reach 42403 := rs (se 1 (by rfl) ⟨31802, by rfl⟩) R63605
theorem R42545 : Reach 42545 := rs (se 2 (by rfl) ⟨15954, by rfl⟩) R31909
theorem R10253 : Reach 10253 := rs (se 3 (by rfl) ⟨1922, by rfl⟩) R3845
theorem R10257 : Reach 10257 := rs (se 2 (by rfl) ⟨3846, by rfl⟩) R7693
theorem R10261 : Reach 10261 := rs (se 6 (by rfl) ⟨240, by rfl⟩) R481
theorem R10263 : Reach 10263 := rs (se 1 (by rfl) ⟨7697, by rfl⟩) R15395
theorem R10275 : Reach 10275 := rs (se 1 (by rfl) ⟨7706, by rfl⟩) R15413
theorem R10277 : Reach 10277 := rs (se 4 (by rfl) ⟨963, by rfl⟩) R1927
theorem R10285 : Reach 10285 := rs (se 3 (by rfl) ⟨1928, by rfl⟩) R3857
theorem R10297 : Reach 10297 := rs (se 2 (by rfl) ⟨3861, by rfl⟩) R7723
theorem R10327 : Reach 10327 := rs (se 1 (by rfl) ⟨7745, by rfl⟩) R15491
theorem R10329 : Reach 10329 := rs (se 2 (by rfl) ⟨3873, by rfl⟩) R7747
theorem R10333 : Reach 10333 := rs (se 3 (by rfl) ⟨1937, by rfl⟩) R3875
theorem R10339 : Reach 10339 := rs (se 1 (by rfl) ⟨7754, by rfl⟩) R15509
theorem R10341 : Reach 10341 := rs (se 4 (by rfl) ⟨969, by rfl⟩) R1939
theorem R10355 : Reach 10355 := rs (se 1 (by rfl) ⟨7766, by rfl⟩) R15533
theorem R10365 : Reach 10365 := rs (se 3 (by rfl) ⟨1943, by rfl⟩) R3887
theorem R10437 : Reach 10437 := rs (se 4 (by rfl) ⟨978, by rfl⟩) R1957
theorem R10445 : Reach 10445 := rs (se 3 (by rfl) ⟨1958, by rfl⟩) R3917
theorem R10455 : Reach 10455 := rs (se 1 (by rfl) ⟨7841, by rfl⟩) R15683
theorem R10457 : Reach 10457 := rs (se 2 (by rfl) ⟨3921, by rfl⟩) R7843
theorem R10487 : Reach 10487 := rs (se 1 (by rfl) ⟨7865, by rfl⟩) R15731
theorem R10489 : Reach 10489 := rs (se 2 (by rfl) ⟨3933, by rfl⟩) R7867
theorem R10517 : Reach 10517 := rs (se 6 (by rfl) ⟨246, by rfl⟩) R493
theorem R10541 : Reach 10541 := rs (se 3 (by rfl) ⟨1976, by rfl⟩) R3953
theorem R10549 : Reach 10549 := rs (se 5 (by rfl) ⟨494, by rfl⟩) R989
theorem R10561 : Reach 10561 := rs (se 2 (by rfl) ⟨3960, by rfl⟩) R7921
theorem R10563 : Reach 10563 := rs (se 1 (by rfl) ⟨7922, by rfl⟩) R15845
theorem R10569 : Reach 10569 := rs (se 2 (by rfl) ⟨3963, by rfl⟩) R7927
theorem R10577 : Reach 10577 := rs (se 2 (by rfl) ⟨3966, by rfl⟩) R7933
theorem R10579 : Reach 10579 := rs (se 1 (by rfl) ⟨7934, by rfl⟩) R15869
theorem R10583 : Reach 10583 := rs (se 1 (by rfl) ⟨7937, by rfl⟩) R15875
theorem R10589 : Reach 10589 := rs (se 3 (by rfl) ⟨1985, by rfl⟩) R3971
theorem R10601 : Reach 10601 := rs (se 2 (by rfl) ⟨3975, by rfl⟩) R7951
theorem R10607 : Reach 10607 := rs (se 1 (by rfl) ⟨7955, by rfl⟩) R15911
theorem R10621 : Reach 10621 := rs (se 3 (by rfl) ⟨1991, by rfl⟩) R3983
theorem R10625 : Reach 10625 := rs (se 2 (by rfl) ⟨3984, by rfl⟩) R7969
theorem R10627 : Reach 10627 := rs (se 1 (by rfl) ⟨7970, by rfl⟩) R15941
theorem R10629 : Reach 10629 := rs (se 4 (by rfl) ⟨996, by rfl⟩) R1993
theorem R10631 : Reach 10631 := rs (se 1 (by rfl) ⟨7973, by rfl⟩) R15947
theorem R10635 : Reach 10635 := rs (se 1 (by rfl) ⟨7976, by rfl⟩) R15953
theorem R10637 : Reach 10637 := rs (se 3 (by rfl) ⟨1994, by rfl⟩) R3989
theorem R10639 : Reach 10639 := rs (se 1 (by rfl) ⟨7979, by rfl⟩) R15959
theorem R10641 : Reach 10641 := rs (se 2 (by rfl) ⟨3990, by rfl⟩) R7981
theorem R10643 : Reach 10643 := rs (se 1 (by rfl) ⟨7982, by rfl⟩) R15965
theorem R10645 : Reach 10645 := rs (se 6 (by rfl) ⟨249, by rfl⟩) R499
theorem R10647 : Reach 10647 := rs (se 1 (by rfl) ⟨7985, by rfl⟩) R15971
theorem R10649 : Reach 10649 := rs (se 2 (by rfl) ⟨3993, by rfl⟩) R7987
theorem R10659 : Reach 10659 := rs (se 1 (by rfl) ⟨7994, by rfl⟩) R15989
theorem R10661 : Reach 10661 := rs (se 4 (by rfl) ⟨999, by rfl⟩) R1999
theorem R10663 : Reach 10663 := rs (se 1 (by rfl) ⟨7997, by rfl⟩) R15995
theorem R10673 : Reach 10673 := rs (se 2 (by rfl) ⟨4002, by rfl⟩) R8005
theorem R10675 : Reach 10675 := rs (se 1 (by rfl) ⟨8006, by rfl⟩) R16013
theorem R10681 : Reach 10681 := rs (se 2 (by rfl) ⟨4005, by rfl⟩) R8011
theorem R10745 : Reach 10745 := rs (se 2 (by rfl) ⟨4029, by rfl⟩) R8059
theorem R43573 : Reach 43573 := rs (se 5 (by rfl) ⟨2042, by rfl⟩) R4085
theorem R10837 : Reach 10837 := rs (se 8 (by rfl) ⟨63, by rfl⟩) R127
theorem R10865 : Reach 10865 := rs (se 2 (by rfl) ⟨4074, by rfl⟩) R8149
theorem R10883 : Reach 10883 := rs (se 1 (by rfl) ⟨8162, by rfl⟩) R16325
theorem R10893 : Reach 10893 := rs (se 3 (by rfl) ⟨2042, by rfl⟩) R4085
theorem R10903 : Reach 10903 := rs (se 1 (by rfl) ⟨8177, by rfl⟩) R16355
theorem R10923 : Reach 10923 := rs (se 1 (by rfl) ⟨8192, by rfl⟩) R16385
theorem R10927 : Reach 10927 := rs (se 1 (by rfl) ⟨8195, by rfl⟩) R16391
theorem R43699 : Reach 43699 := rs (se 1 (by rfl) ⟨32774, by rfl⟩) R65549
theorem R10975 : Reach 10975 := rs (se 1 (by rfl) ⟨8231, by rfl⟩) R16463
theorem R11089 : Reach 11089 := rs (se 2 (by rfl) ⟨4158, by rfl⟩) R8317
theorem R11091 : Reach 11091 := rs (se 1 (by rfl) ⟨8318, by rfl⟩) R16637
theorem R11095 : Reach 11095 := rs (se 1 (by rfl) ⟨8321, by rfl⟩) R16643
theorem R11111 : Reach 11111 := rs (se 1 (by rfl) ⟨8333, by rfl⟩) R16667
theorem R43901 : Reach 43901 := rs (se 3 (by rfl) ⟨8231, by rfl⟩) R16463
theorem R11399 : Reach 11399 := rs (se 1 (by rfl) ⟨8549, by rfl⟩) R17099
theorem R11403 : Reach 11403 := rs (se 1 (by rfl) ⟨8552, by rfl⟩) R17105
theorem R11407 : Reach 11407 := rs (se 1 (by rfl) ⟨8555, by rfl⟩) R17111
theorem R11423 : Reach 11423 := rs (se 1 (by rfl) ⟨8567, by rfl⟩) R17135
theorem R11439 : Reach 11439 := rs (se 1 (by rfl) ⟨8579, by rfl⟩) R17159
theorem R11501 : Reach 11501 := rs (se 3 (by rfl) ⟨2156, by rfl⟩) R4313
theorem R11505 : Reach 11505 := rs (se 2 (by rfl) ⟨4314, by rfl⟩) R8629
theorem R11509 : Reach 11509 := rs (se 5 (by rfl) ⟨539, by rfl⟩) R1079
theorem R11511 : Reach 11511 := rs (se 1 (by rfl) ⟨8633, by rfl⟩) R17267
theorem R11529 : Reach 11529 := rs (se 2 (by rfl) ⟨4323, by rfl⟩) R8647
theorem R11531 : Reach 11531 := rs (se 1 (by rfl) ⟨8648, by rfl⟩) R17297
theorem R11535 : Reach 11535 := rs (se 1 (by rfl) ⟨8651, by rfl⟩) R17303
theorem R11545 : Reach 11545 := rs (se 2 (by rfl) ⟨4329, by rfl⟩) R8659
theorem R11581 : Reach 11581 := rs (se 3 (by rfl) ⟨2171, by rfl⟩) R4343
theorem R11587 : Reach 11587 := rs (se 1 (by rfl) ⟨8690, by rfl⟩) R17381
theorem R11643 : Reach 11643 := rs (se 1 (by rfl) ⟨8732, by rfl⟩) R17465
theorem R11749 : Reach 11749 := rs (se 4 (by rfl) ⟨1101, by rfl⟩) R2203
theorem R11751 : Reach 11751 := rs (se 1 (by rfl) ⟨8813, by rfl⟩) R17627
theorem R11753 : Reach 11753 := rs (se 2 (by rfl) ⟨4407, by rfl⟩) R8815
theorem R11887 : Reach 11887 := rs (se 1 (by rfl) ⟨8915, by rfl⟩) R17831
theorem R11959 : Reach 11959 := rs (se 1 (by rfl) ⟨8969, by rfl⟩) R17939
theorem R12653 : Reach 12653 := rs (se 3 (by rfl) ⟨2372, by rfl⟩) R4745
theorem R12655 : Reach 12655 := rs (se 1 (by rfl) ⟨9491, by rfl⟩) R18983
theorem R12663 : Reach 12663 := rs (se 1 (by rfl) ⟨9497, by rfl⟩) R18995
theorem R12667 : Reach 12667 := rs (se 1 (by rfl) ⟨9500, by rfl⟩) R19001
theorem R12675 : Reach 12675 := rs (se 1 (by rfl) ⟨9506, by rfl⟩) R19013
theorem R12677 : Reach 12677 := rs (se 4 (by rfl) ⟨1188, by rfl⟩) R2377
theorem R12679 : Reach 12679 := rs (se 1 (by rfl) ⟨9509, by rfl⟩) R19019
theorem R12681 : Reach 12681 := rs (se 2 (by rfl) ⟨4755, by rfl⟩) R9511
theorem R12687 : Reach 12687 := rs (se 1 (by rfl) ⟨9515, by rfl⟩) R19031
theorem R12707 : Reach 12707 := rs (se 1 (by rfl) ⟨9530, by rfl⟩) R19061
theorem R12709 : Reach 12709 := rs (se 4 (by rfl) ⟨1191, by rfl⟩) R2383
theorem R12711 : Reach 12711 := rs (se 1 (by rfl) ⟨9533, by rfl⟩) R19067
theorem R12715 : Reach 12715 := rs (se 1 (by rfl) ⟨9536, by rfl⟩) R19073
theorem R45593 : Reach 45593 := rs (se 2 (by rfl) ⟨17097, by rfl⟩) R34195
theorem R46169 : Reach 46169 := rs (se 2 (by rfl) ⟨17313, by rfl⟩) R34627
theorem R177497 : Reach 177497 := rs (se 2 (by rfl) ⟨66561, by rfl⟩) R133123
theorem R46615 : Reach 46615 := rs (se 1 (by rfl) ⟨34961, by rfl⟩) R69923
theorem R82133 : Reach 82133 := rs (se 7 (by rfl) ⟨962, by rfl⟩) R1925
theorem R50665 : Reach 50665 := rs (se 2 (by rfl) ⟨18999, by rfl⟩) R37999
theorem R50705 : Reach 50705 := rs (se 2 (by rfl) ⟨19014, by rfl⟩) R38029
theorem R85157 : Reach 85157 := rs (se 4 (by rfl) ⟨7983, by rfl⟩) R15967
theorem R20501 : Reach 20501 := rs (se 6 (by rfl) ⟨480, by rfl⟩) R961
theorem R20533 : Reach 20533 := rs (se 5 (by rfl) ⟨962, by rfl⟩) R1925
theorem R20549 : Reach 20549 := rs (se 4 (by rfl) ⟨1926, by rfl⟩) R3853
theorem R20555 : Reach 20555 := rs (se 1 (by rfl) ⟨15416, by rfl⟩) R30833
theorem R20573 : Reach 20573 := rs (se 3 (by rfl) ⟨3857, by rfl⟩) R7715
theorem R20681 : Reach 20681 := rs (se 2 (by rfl) ⟨7755, by rfl⟩) R15511
theorem R20911 : Reach 20911 := rs (se 1 (by rfl) ⟨15683, by rfl⟩) R31367
theorem R20915 : Reach 20915 := rs (se 1 (by rfl) ⟨15686, by rfl⟩) R31373
theorem R21023 : Reach 21023 := rs (se 1 (by rfl) ⟨15767, by rfl⟩) R31535
theorem R21077 : Reach 21077 := rs (se 8 (by rfl) ⟨123, by rfl⟩) R247
theorem R21127 : Reach 21127 := rs (se 1 (by rfl) ⟨15845, by rfl⟩) R31691
theorem R21131 : Reach 21131 := rs (se 1 (by rfl) ⟨15848, by rfl⟩) R31697
theorem R21185 : Reach 21185 := rs (se 2 (by rfl) ⟨7944, by rfl⟩) R15889
theorem R21203 : Reach 21203 := rs (se 1 (by rfl) ⟨15902, by rfl⟩) R31805
theorem R21215 : Reach 21215 := rs (se 1 (by rfl) ⟨15911, by rfl⟩) R31823
theorem R21269 : Reach 21269 := rs (se 6 (by rfl) ⟨498, by rfl⟩) R997
theorem R21289 : Reach 21289 := rs (se 2 (by rfl) ⟨7983, by rfl⟩) R15967
theorem R21293 : Reach 21293 := rs (se 3 (by rfl) ⟨3992, by rfl⟩) R7985
theorem R21323 : Reach 21323 := rs (se 1 (by rfl) ⟨15992, by rfl⟩) R31985
theorem R21347 : Reach 21347 := rs (se 1 (by rfl) ⟨16010, by rfl⟩) R32021
theorem R21491 : Reach 21491 := rs (se 1 (by rfl) ⟨16118, by rfl⟩) R32237
theorem R21851 : Reach 21851 := rs (se 1 (by rfl) ⟨16388, by rfl⟩) R32777
theorem R22189 : Reach 22189 := rs (se 3 (by rfl) ⟨4160, by rfl⟩) R8321
theorem R23021 : Reach 23021 := rs (se 3 (by rfl) ⟨4316, by rfl⟩) R8633
theorem R23111 : Reach 23111 := rs (se 1 (by rfl) ⟨17333, by rfl⟩) R34667
theorem R23287 : Reach 23287 := rs (se 1 (by rfl) ⟨17465, by rfl⟩) R34931
theorem R23321 : Reach 23321 := rs (se 2 (by rfl) ⟨8745, by rfl⟩) R17491
theorem R23503 : Reach 23503 := rs (se 1 (by rfl) ⟨17627, by rfl⟩) R35255
theorem R23507 : Reach 23507 := rs (se 1 (by rfl) ⟨17630, by rfl⟩) R35261
theorem R23777 : Reach 23777 := rs (se 2 (by rfl) ⟨8916, by rfl⟩) R17833
theorem R188081 : Reach 188081 := rs (se 2 (by rfl) ⟨70530, by rfl⟩) R141061
theorem R188203 : Reach 188203 := rs (se 1 (by rfl) ⟨141152, by rfl⟩) R282305
theorem R25289 : Reach 25289 := rs (se 2 (by rfl) ⟨9483, by rfl⟩) R18967
theorem R25307 : Reach 25307 := rs (se 1 (by rfl) ⟨18980, by rfl⟩) R37961
theorem R25325 : Reach 25325 := rs (se 3 (by rfl) ⟨4748, by rfl⟩) R9497
theorem R25361 : Reach 25361 := rs (se 2 (by rfl) ⟨9510, by rfl⟩) R19021
theorem R25373 : Reach 25373 := rs (se 3 (by rfl) ⟨4757, by rfl⟩) R9515
theorem R25415 : Reach 25415 := rs (se 1 (by rfl) ⟨19061, by rfl⟩) R38123
theorem R92339 : Reach 92339 := rs (se 1 (by rfl) ⟨69254, by rfl⟩) R138509
theorem R95681 : Reach 95681 := rs (se 2 (by rfl) ⟨35880, by rfl⟩) R71761
theorem R219 : Reach 219 := rs (se 1 (by rfl) ⟨164, by rfl⟩) R329
theorem R225 : Reach 225 := rs (se 2 (by rfl) ⟨84, by rfl⟩) R169
theorem R239 : Reach 239 := rs (se 1 (by rfl) ⟨179, by rfl⟩) R359
theorem R427 : Reach 427 := rs (se 1 (by rfl) ⟨320, by rfl⟩) R641
theorem R439 : Reach 439 := rs (se 1 (by rfl) ⟨329, by rfl⟩) R659
theorem R443 : Reach 443 := rs (se 1 (by rfl) ⟨332, by rfl⟩) R665
theorem R451 : Reach 451 := rs (se 1 (by rfl) ⟨338, by rfl⟩) R677
theorem R479 : Reach 479 := rs (se 1 (by rfl) ⟨359, by rfl⟩) R719
theorem R855 : Reach 855 := rs (se 1 (by rfl) ⟨641, by rfl⟩) R1283
theorem R877 : Reach 877 := rs (se 3 (by rfl) ⟨164, by rfl⟩) R329
theorem R887 : Reach 887 := rs (se 1 (by rfl) ⟨665, by rfl⟩) R1331
theorem R901 : Reach 901 := rs (se 4 (by rfl) ⟨84, by rfl⟩) R169
theorem R907 : Reach 907 := rs (se 1 (by rfl) ⟨680, by rfl⟩) R1361
theorem R957 : Reach 957 := rs (se 3 (by rfl) ⟨179, by rfl⟩) R359
theorem R33797 : Reach 33797 := rs (se 4 (by rfl) ⟨3168, by rfl⟩) R6337
theorem R33803 : Reach 33803 := rs (se 1 (by rfl) ⟨25352, by rfl⟩) R50705
theorem R1709 : Reach 1709 := rs (se 3 (by rfl) ⟨320, by rfl⟩) R641
theorem R1721 : Reach 1721 := rs (se 2 (by rfl) ⟨645, by rfl⟩) R1291
theorem R1723 : Reach 1723 := rs (se 1 (by rfl) ⟨1292, by rfl⟩) R2585
theorem R1727 : Reach 1727 := rs (se 1 (by rfl) ⟨1295, by rfl⟩) R2591
theorem R1739 : Reach 1739 := rs (se 1 (by rfl) ⟨1304, by rfl⟩) R2609
theorem R1753 : Reach 1753 := rs (se 2 (by rfl) ⟨657, by rfl⟩) R1315
theorem R1757 : Reach 1757 := rs (se 3 (by rfl) ⟨329, by rfl⟩) R659
theorem R1769 : Reach 1769 := rs (se 2 (by rfl) ⟨663, by rfl⟩) R1327
theorem R1771 : Reach 1771 := rs (se 1 (by rfl) ⟨1328, by rfl⟩) R2657
theorem R1773 : Reach 1773 := rs (se 3 (by rfl) ⟨332, by rfl⟩) R665
theorem R1805 : Reach 1805 := rs (se 3 (by rfl) ⟨338, by rfl⟩) R677
theorem R1809 : Reach 1809 := rs (se 2 (by rfl) ⟨678, by rfl⟩) R1357
theorem R1815 : Reach 1815 := rs (se 1 (by rfl) ⟨1361, by rfl⟩) R2723
theorem R1917 : Reach 1917 := rs (se 3 (by rfl) ⟨359, by rfl⟩) R719
theorem R1929 : Reach 1929 := rs (se 2 (by rfl) ⟨723, by rfl⟩) R1447
theorem R67553 : Reach 67553 := rs (se 2 (by rfl) ⟨25332, by rfl⟩) R50665
theorem R67661 : Reach 67661 := rs (se 3 (by rfl) ⟨12686, by rfl⟩) R25373
theorem R3417 : Reach 3417 := rs (se 2 (by rfl) ⟨1281, by rfl⟩) R2563
theorem R3421 : Reach 3421 := rs (se 3 (by rfl) ⟨641, by rfl⟩) R1283
theorem R3425 : Reach 3425 := rs (se 2 (by rfl) ⟨1284, by rfl⟩) R2569
theorem R3443 : Reach 3443 := rs (se 1 (by rfl) ⟨2582, by rfl⟩) R5165
theorem R3447 : Reach 3447 := rs (se 1 (by rfl) ⟨2585, by rfl⟩) R5171
theorem R3451 : Reach 3451 := rs (se 1 (by rfl) ⟨2588, by rfl⟩) R5177
theorem R3455 : Reach 3455 := rs (se 1 (by rfl) ⟨2591, by rfl⟩) R5183
theorem R3479 : Reach 3479 := rs (se 1 (by rfl) ⟨2609, by rfl⟩) R5219
theorem R3481 : Reach 3481 := rs (se 2 (by rfl) ⟨1305, by rfl⟩) R2611
theorem R3495 : Reach 3495 := rs (se 1 (by rfl) ⟨2621, by rfl⟩) R5243
theorem R3505 : Reach 3505 := rs (se 2 (by rfl) ⟨1314, by rfl⟩) R2629
theorem R3507 : Reach 3507 := rs (se 1 (by rfl) ⟨2630, by rfl⟩) R5261
theorem R3509 : Reach 3509 := rs (se 5 (by rfl) ⟨164, by rfl⟩) R329
theorem R3513 : Reach 3513 := rs (se 2 (by rfl) ⟨1317, by rfl⟩) R2635
theorem R3527 : Reach 3527 := rs (se 1 (by rfl) ⟨2645, by rfl⟩) R5291
theorem R3529 : Reach 3529 := rs (se 2 (by rfl) ⟨1323, by rfl⟩) R2647
theorem R3539 : Reach 3539 := rs (se 1 (by rfl) ⟨2654, by rfl⟩) R5309
theorem R3543 : Reach 3543 := rs (se 1 (by rfl) ⟨2657, by rfl⟩) R5315
theorem R3545 : Reach 3545 := rs (se 2 (by rfl) ⟨1329, by rfl⟩) R2659
theorem R3547 : Reach 3547 := rs (se 1 (by rfl) ⟨2660, by rfl⟩) R5321
theorem R3549 : Reach 3549 := rs (se 3 (by rfl) ⟨665, by rfl⟩) R1331
theorem R3553 : Reach 3553 := rs (se 2 (by rfl) ⟨1332, by rfl⟩) R2665
theorem R3605 : Reach 3605 := rs (se 6 (by rfl) ⟨84, by rfl⟩) R169
theorem R3619 : Reach 3619 := rs (se 1 (by rfl) ⟨2714, by rfl⟩) R5429
theorem R3627 : Reach 3627 := rs (se 1 (by rfl) ⟨2720, by rfl⟩) R5441
theorem R3629 : Reach 3629 := rs (se 3 (by rfl) ⟨680, by rfl⟩) R1361
theorem R134873 : Reach 134873 := rs (se 2 (by rfl) ⟨50577, by rfl⟩) R101155
theorem R3829 : Reach 3829 := rs (se 5 (by rfl) ⟨179, by rfl⟩) R359
theorem R3833 : Reach 3833 := rs (se 2 (by rfl) ⟨1437, by rfl⟩) R2875
theorem R3859 : Reach 3859 := rs (se 1 (by rfl) ⟨2894, by rfl⟩) R5789
theorem R4217 : Reach 4217 := rs (se 2 (by rfl) ⟨1581, by rfl⟩) R3163
theorem R4225 : Reach 4225 := rs (se 2 (by rfl) ⟨1584, by rfl⟩) R3169
theorem R4235 : Reach 4235 := rs (se 1 (by rfl) ⟨3176, by rfl⟩) R6353
theorem R6833 : Reach 6833 := rs (se 2 (by rfl) ⟨2562, by rfl⟩) R5125
theorem R6835 : Reach 6835 := rs (se 1 (by rfl) ⟨5126, by rfl⟩) R10253
theorem R6837 : Reach 6837 := rs (se 5 (by rfl) ⟨320, by rfl⟩) R641
theorem R6841 : Reach 6841 := rs (se 2 (by rfl) ⟨2565, by rfl⟩) R5131
theorem R6849 : Reach 6849 := rs (se 2 (by rfl) ⟨2568, by rfl⟩) R5137
theorem R6851 : Reach 6851 := rs (se 1 (by rfl) ⟨5138, by rfl⟩) R10277
theorem R6857 : Reach 6857 := rs (se 2 (by rfl) ⟨2571, by rfl⟩) R5143
theorem R6885 : Reach 6885 := rs (se 4 (by rfl) ⟨645, by rfl⟩) R1291
theorem R6893 : Reach 6893 := rs (se 3 (by rfl) ⟨1292, by rfl⟩) R2585
theorem R6903 : Reach 6903 := rs (se 1 (by rfl) ⟨5177, by rfl⟩) R10355
theorem R6909 : Reach 6909 := rs (se 3 (by rfl) ⟨1295, by rfl⟩) R2591
theorem R6957 : Reach 6957 := rs (se 3 (by rfl) ⟨1304, by rfl⟩) R2609
theorem R6961 : Reach 6961 := rs (se 2 (by rfl) ⟨2610, by rfl⟩) R5221
theorem R6963 : Reach 6963 := rs (se 1 (by rfl) ⟨5222, by rfl⟩) R10445
theorem R6969 : Reach 6969 := rs (se 2 (by rfl) ⟨2613, by rfl⟩) R5227
theorem R6971 : Reach 6971 := rs (se 1 (by rfl) ⟨5228, by rfl⟩) R10457
theorem R6991 : Reach 6991 := rs (se 1 (by rfl) ⟨5243, by rfl⟩) R10487
theorem R7011 : Reach 7011 := rs (se 1 (by rfl) ⟨5258, by rfl⟩) R10517
theorem R7013 : Reach 7013 := rs (se 4 (by rfl) ⟨657, by rfl⟩) R1315
theorem R7025 : Reach 7025 := rs (se 2 (by rfl) ⟨2634, by rfl⟩) R5269
theorem R7027 : Reach 7027 := rs (se 1 (by rfl) ⟨5270, by rfl⟩) R10541
theorem R7029 : Reach 7029 := rs (se 5 (by rfl) ⟨329, by rfl⟩) R659
theorem R7041 : Reach 7041 := rs (se 2 (by rfl) ⟨2640, by rfl⟩) R5281
theorem R7051 : Reach 7051 := rs (se 1 (by rfl) ⟨5288, by rfl⟩) R10577
theorem R7055 : Reach 7055 := rs (se 1 (by rfl) ⟨5291, by rfl⟩) R10583
theorem R7057 : Reach 7057 := rs (se 2 (by rfl) ⟨2646, by rfl⟩) R5293
theorem R7059 : Reach 7059 := rs (se 1 (by rfl) ⟨5294, by rfl⟩) R10589
theorem R7067 : Reach 7067 := rs (se 1 (by rfl) ⟨5300, by rfl⟩) R10601
theorem R7071 : Reach 7071 := rs (se 1 (by rfl) ⟨5303, by rfl⟩) R10607
theorem R7077 : Reach 7077 := rs (se 4 (by rfl) ⟨663, by rfl⟩) R1327
theorem R7083 : Reach 7083 := rs (se 1 (by rfl) ⟨5312, by rfl⟩) R10625
theorem R7085 : Reach 7085 := rs (se 3 (by rfl) ⟨1328, by rfl⟩) R2657
theorem R7087 : Reach 7087 := rs (se 1 (by rfl) ⟨5315, by rfl⟩) R10631
theorem R7089 : Reach 7089 := rs (se 2 (by rfl) ⟨2658, by rfl⟩) R5317
theorem R7091 : Reach 7091 := rs (se 1 (by rfl) ⟨5318, by rfl⟩) R10637
theorem R7093 : Reach 7093 := rs (se 5 (by rfl) ⟨332, by rfl⟩) R665
theorem R7095 : Reach 7095 := rs (se 1 (by rfl) ⟨5321, by rfl⟩) R10643
theorem R7097 : Reach 7097 := rs (se 2 (by rfl) ⟨2661, by rfl⟩) R5323
theorem R7099 : Reach 7099 := rs (se 1 (by rfl) ⟨5324, by rfl⟩) R10649
theorem R7105 : Reach 7105 := rs (se 2 (by rfl) ⟨2664, by rfl⟩) R5329
theorem R7107 : Reach 7107 := rs (se 1 (by rfl) ⟨5330, by rfl⟩) R10661
theorem R7115 : Reach 7115 := rs (se 1 (by rfl) ⟨5336, by rfl⟩) R10673
theorem R7163 : Reach 7163 := rs (se 1 (by rfl) ⟨5372, by rfl⟩) R10745
theorem R7221 : Reach 7221 := rs (se 5 (by rfl) ⟨338, by rfl⟩) R677
theorem R7237 : Reach 7237 := rs (se 4 (by rfl) ⟨678, by rfl⟩) R1357
theorem R7243 : Reach 7243 := rs (se 1 (by rfl) ⟨5432, by rfl⟩) R10865
theorem R7255 : Reach 7255 := rs (se 1 (by rfl) ⟨5441, by rfl⟩) R10883
theorem R7261 : Reach 7261 := rs (se 3 (by rfl) ⟨1361, by rfl⟩) R2723
theorem R7393 : Reach 7393 := rs (se 2 (by rfl) ⟨2772, by rfl⟩) R5545
theorem R7407 : Reach 7407 := rs (se 1 (by rfl) ⟨5555, by rfl⟩) R11111
theorem R7599 : Reach 7599 := rs (se 1 (by rfl) ⟨5699, by rfl⟩) R11399
theorem R7615 : Reach 7615 := rs (se 1 (by rfl) ⟨5711, by rfl⟩) R11423
theorem R7665 : Reach 7665 := rs (se 2 (by rfl) ⟨2874, by rfl⟩) R5749
theorem R7667 : Reach 7667 := rs (se 1 (by rfl) ⟨5750, by rfl⟩) R11501
theorem R7669 : Reach 7669 := rs (se 5 (by rfl) ⟨359, by rfl⟩) R719
theorem R7673 : Reach 7673 := rs (se 2 (by rfl) ⟨2877, by rfl⟩) R5755
theorem R7687 : Reach 7687 := rs (se 1 (by rfl) ⟨5765, by rfl⟩) R11531
theorem R7689 : Reach 7689 := rs (se 2 (by rfl) ⟨2883, by rfl⟩) R5767
theorem R7717 : Reach 7717 := rs (se 4 (by rfl) ⟨723, by rfl⟩) R1447
theorem R7833 : Reach 7833 := rs (se 2 (by rfl) ⟨2937, by rfl⟩) R5875
theorem R7835 : Reach 7835 := rs (se 1 (by rfl) ⟨5876, by rfl⟩) R11753
theorem R8435 : Reach 8435 := rs (se 1 (by rfl) ⟨6326, by rfl⟩) R12653
theorem R8441 : Reach 8441 := rs (se 2 (by rfl) ⟨3165, by rfl⟩) R6331
theorem R8449 : Reach 8449 := rs (se 2 (by rfl) ⟨3168, by rfl⟩) R6337
theorem R8451 : Reach 8451 := rs (se 1 (by rfl) ⟨6338, by rfl⟩) R12677
theorem R8457 : Reach 8457 := rs (se 2 (by rfl) ⟨3171, by rfl⟩) R6343
theorem R8471 : Reach 8471 := rs (se 1 (by rfl) ⟨6353, by rfl⟩) R12707
theorem R8473 : Reach 8473 := rs (se 2 (by rfl) ⟨3177, by rfl⟩) R6355
theorem R13667 : Reach 13667 := rs (se 1 (by rfl) ⟨10250, by rfl⟩) R20501
theorem R13685 : Reach 13685 := rs (se 5 (by rfl) ⟨641, by rfl⟩) R1283
theorem R13699 : Reach 13699 := rs (se 1 (by rfl) ⟨10274, by rfl⟩) R20549
theorem R13703 : Reach 13703 := rs (se 1 (by rfl) ⟨10277, by rfl⟩) R20555
theorem R13715 : Reach 13715 := rs (se 1 (by rfl) ⟨10286, by rfl⟩) R20573
theorem R13729 : Reach 13729 := rs (se 2 (by rfl) ⟨5148, by rfl⟩) R10297
theorem R13769 : Reach 13769 := rs (se 2 (by rfl) ⟨5163, by rfl⟩) R10327
theorem R13787 : Reach 13787 := rs (se 1 (by rfl) ⟨10340, by rfl⟩) R20681
theorem R13805 : Reach 13805 := rs (se 3 (by rfl) ⟨2588, by rfl⟩) R5177
theorem R13925 : Reach 13925 := rs (se 4 (by rfl) ⟨1305, by rfl⟩) R2611
theorem R13943 : Reach 13943 := rs (se 1 (by rfl) ⟨10457, by rfl⟩) R20915
theorem R13981 : Reach 13981 := rs (se 3 (by rfl) ⟨2621, by rfl⟩) R5243
theorem R13985 : Reach 13985 := rs (se 2 (by rfl) ⟨5244, by rfl⟩) R10489
theorem R14015 : Reach 14015 := rs (se 1 (by rfl) ⟨10511, by rfl⟩) R21023
theorem R14021 : Reach 14021 := rs (se 4 (by rfl) ⟨1314, by rfl⟩) R2629
theorem R14029 : Reach 14029 := rs (se 3 (by rfl) ⟨2630, by rfl⟩) R5261
theorem R14051 : Reach 14051 := rs (se 1 (by rfl) ⟨10538, by rfl⟩) R21077
theorem R14053 : Reach 14053 := rs (se 4 (by rfl) ⟨1317, by rfl⟩) R2635
theorem R14081 : Reach 14081 := rs (se 2 (by rfl) ⟨5280, by rfl⟩) R10561
theorem R14087 : Reach 14087 := rs (se 1 (by rfl) ⟨10565, by rfl⟩) R21131
theorem R14105 : Reach 14105 := rs (se 2 (by rfl) ⟨5289, by rfl⟩) R10579
theorem R14117 : Reach 14117 := rs (se 4 (by rfl) ⟨1323, by rfl⟩) R2647
theorem R14123 : Reach 14123 := rs (se 1 (by rfl) ⟨10592, by rfl⟩) R21185
theorem R14135 : Reach 14135 := rs (se 1 (by rfl) ⟨10601, by rfl⟩) R21203
theorem R14143 : Reach 14143 := rs (se 1 (by rfl) ⟨10607, by rfl⟩) R21215
theorem R14161 : Reach 14161 := rs (se 2 (by rfl) ⟨5310, by rfl⟩) R10621
theorem R14179 : Reach 14179 := rs (se 1 (by rfl) ⟨10634, by rfl⟩) R21269
theorem R14185 : Reach 14185 := rs (se 2 (by rfl) ⟨5319, by rfl⟩) R10639
theorem R14189 : Reach 14189 := rs (se 3 (by rfl) ⟨2660, by rfl⟩) R5321
theorem R14195 : Reach 14195 := rs (se 1 (by rfl) ⟨10646, by rfl⟩) R21293
theorem R14197 : Reach 14197 := rs (se 5 (by rfl) ⟨665, by rfl⟩) R1331
theorem R14213 : Reach 14213 := rs (se 4 (by rfl) ⟨1332, by rfl⟩) R2665
theorem R14215 : Reach 14215 := rs (se 1 (by rfl) ⟨10661, by rfl⟩) R21323
theorem R14231 : Reach 14231 := rs (se 1 (by rfl) ⟨10673, by rfl⟩) R21347
theorem R14233 : Reach 14233 := rs (se 2 (by rfl) ⟨5337, by rfl⟩) R10675
theorem R14327 : Reach 14327 := rs (se 1 (by rfl) ⟨10745, by rfl⟩) R21491
theorem R14477 : Reach 14477 := rs (se 3 (by rfl) ⟨2714, by rfl⟩) R5429
theorem R14509 : Reach 14509 := rs (se 3 (by rfl) ⟨2720, by rfl⟩) R5441
theorem R14537 : Reach 14537 := rs (se 2 (by rfl) ⟨5451, by rfl⟩) R10903
theorem R14567 : Reach 14567 := rs (se 1 (by rfl) ⟨10925, by rfl⟩) R21851
theorem R14633 : Reach 14633 := rs (se 2 (by rfl) ⟨5487, by rfl⟩) R10975
theorem R15209 : Reach 15209 := rs (se 2 (by rfl) ⟨5703, by rfl⟩) R11407
theorem R15317 : Reach 15317 := rs (se 7 (by rfl) ⟨179, by rfl⟩) R359
theorem R15347 : Reach 15347 := rs (se 1 (by rfl) ⟨11510, by rfl⟩) R23021
theorem R15407 : Reach 15407 := rs (se 1 (by rfl) ⟨11555, by rfl⟩) R23111
theorem R15437 : Reach 15437 := rs (se 3 (by rfl) ⟨2894, by rfl⟩) R5789
theorem R15449 : Reach 15449 := rs (se 2 (by rfl) ⟨5793, by rfl⟩) R11587
theorem R15547 : Reach 15547 := rs (se 1 (by rfl) ⟨11660, by rfl⟩) R23321
theorem R15665 : Reach 15665 := rs (se 2 (by rfl) ⟨5874, by rfl⟩) R11749
theorem R15671 : Reach 15671 := rs (se 1 (by rfl) ⟨11753, by rfl⟩) R23507
theorem R15851 : Reach 15851 := rs (se 1 (by rfl) ⟨11888, by rfl⟩) R23777
theorem R16859 : Reach 16859 := rs (se 1 (by rfl) ⟨12644, by rfl⟩) R25289
theorem R16871 : Reach 16871 := rs (se 1 (by rfl) ⟨12653, by rfl⟩) R25307
theorem R16883 : Reach 16883 := rs (se 1 (by rfl) ⟨12662, by rfl⟩) R25325
theorem R16889 : Reach 16889 := rs (se 2 (by rfl) ⟨6333, by rfl⟩) R12667
theorem R16901 : Reach 16901 := rs (se 4 (by rfl) ⟨1584, by rfl⟩) R3169
theorem R16907 : Reach 16907 := rs (se 1 (by rfl) ⟨12680, by rfl⟩) R25361
theorem R16915 : Reach 16915 := rs (se 1 (by rfl) ⟨12686, by rfl⟩) R25373
theorem R16943 : Reach 16943 := rs (se 1 (by rfl) ⟨12707, by rfl⟩) R25415
theorem R118331 : Reach 118331 := rs (se 1 (by rfl) ⟨88748, by rfl⟩) R177497
theorem R250937 : Reach 250937 := rs (se 2 (by rfl) ⟨94101, by rfl⟩) R188203
theorem R54755 : Reach 54755 := rs (se 1 (by rfl) ⟨41066, by rfl⟩) R82133
theorem R54881 : Reach 54881 := rs (se 2 (by rfl) ⟨20580, by rfl⟩) R41161
theorem R54917 : Reach 54917 := rs (se 4 (by rfl) ⟨5148, by rfl⟩) R10297
theorem R56213 : Reach 56213 := rs (se 6 (by rfl) ⟨1317, by rfl⟩) R2635
theorem R56369 : Reach 56369 := rs (se 2 (by rfl) ⟨21138, by rfl⟩) R42277
theorem R56513 : Reach 56513 := rs (se 2 (by rfl) ⟨21192, by rfl⟩) R42385
theorem R56537 : Reach 56537 := rs (se 2 (by rfl) ⟨21201, by rfl⟩) R42403
theorem R56771 : Reach 56771 := rs (se 1 (by rfl) ⟨42578, by rfl⟩) R85157
theorem R56861 : Reach 56861 := rs (se 3 (by rfl) ⟨10661, by rfl⟩) R21323
theorem R58097 : Reach 58097 := rs (se 2 (by rfl) ⟨21786, by rfl⟩) R43573
theorem R58265 : Reach 58265 := rs (se 2 (by rfl) ⟨21849, by rfl⟩) R43699
theorem R125387 : Reach 125387 := rs (se 1 (by rfl) ⟨94040, by rfl⟩) R188081
theorem R27341 : Reach 27341 := rs (se 3 (by rfl) ⟨5126, by rfl⟩) R10253
theorem R27377 : Reach 27377 := rs (se 2 (by rfl) ⟨10266, by rfl⟩) R20533
theorem R27539 : Reach 27539 := rs (se 1 (by rfl) ⟨20654, by rfl⟩) R41309
theorem R27575 : Reach 27575 := rs (se 1 (by rfl) ⟨20681, by rfl⟩) R41363
theorem R27845 : Reach 27845 := rs (se 4 (by rfl) ⟨2610, by rfl⟩) R5221
theorem R27877 : Reach 27877 := rs (se 4 (by rfl) ⟨2613, by rfl⟩) R5227
theorem R27881 : Reach 27881 := rs (se 2 (by rfl) ⟨10455, by rfl⟩) R20911
theorem R27965 : Reach 27965 := rs (se 3 (by rfl) ⟨5243, by rfl⟩) R10487
theorem R27971 : Reach 27971 := rs (se 1 (by rfl) ⟨20978, by rfl⟩) R41957
theorem R28169 : Reach 28169 := rs (se 2 (by rfl) ⟨10563, by rfl⟩) R21127
theorem R28205 : Reach 28205 := rs (se 3 (by rfl) ⟨5288, by rfl⟩) R10577
theorem R28309 : Reach 28309 := rs (se 6 (by rfl) ⟨663, by rfl⟩) R1327
theorem R28349 : Reach 28349 := rs (se 3 (by rfl) ⟨5315, by rfl⟩) R10631
theorem R28363 : Reach 28363 := rs (se 1 (by rfl) ⟨21272, by rfl⟩) R42545
theorem R28385 : Reach 28385 := rs (se 2 (by rfl) ⟨10644, by rfl⟩) R21289
theorem R28397 : Reach 28397 := rs (se 3 (by rfl) ⟨5324, by rfl⟩) R10649
theorem R28421 : Reach 28421 := rs (se 4 (by rfl) ⟨2664, by rfl⟩) R5329
theorem R225125 : Reach 225125 := rs (se 4 (by rfl) ⟨21105, by rfl⟩) R42211
theorem R61559 : Reach 61559 := rs (se 1 (by rfl) ⟨46169, by rfl⟩) R92339
theorem R29267 : Reach 29267 := rs (se 1 (by rfl) ⟨21950, by rfl⟩) R43901
theorem R62153 : Reach 62153 := rs (se 2 (by rfl) ⟨23307, by rfl⟩) R46615
theorem R29585 : Reach 29585 := rs (se 2 (by rfl) ⟨11094, by rfl⟩) R22189
theorem R30395 : Reach 30395 := rs (se 1 (by rfl) ⟨22796, by rfl⟩) R45593
theorem R30779 : Reach 30779 := rs (se 1 (by rfl) ⟨23084, by rfl⟩) R46169
theorem R63787 : Reach 63787 := rs (se 1 (by rfl) ⟨47840, by rfl⟩) R95681
theorem R31049 : Reach 31049 := rs (se 2 (by rfl) ⟨11643, by rfl⟩) R23287
theorem R31337 : Reach 31337 := rs (se 2 (by rfl) ⟨11751, by rfl⟩) R23503
theorem R159 : Reach 159 := rs (se 1 (by rfl) ⟨119, by rfl⟩) R239
theorem R295 : Reach 295 := rs (se 1 (by rfl) ⟨221, by rfl⟩) R443
theorem R319 : Reach 319 := rs (se 1 (by rfl) ⟨239, by rfl⟩) R479
theorem R569 : Reach 569 := rs (se 2 (by rfl) ⟨213, by rfl⟩) R427
theorem R585 : Reach 585 := rs (se 2 (by rfl) ⟨219, by rfl⟩) R439
theorem R591 : Reach 591 := rs (se 1 (by rfl) ⟨443, by rfl⟩) R887
theorem R601 : Reach 601 := rs (se 2 (by rfl) ⟨225, by rfl⟩) R451
theorem R637 : Reach 637 := rs (se 3 (by rfl) ⟨119, by rfl⟩) R239
theorem R1139 : Reach 1139 := rs (se 1 (by rfl) ⟨854, by rfl⟩) R1709
theorem R1147 : Reach 1147 := rs (se 1 (by rfl) ⟨860, by rfl⟩) R1721
theorem R1151 : Reach 1151 := rs (se 1 (by rfl) ⟨863, by rfl⟩) R1727
theorem R1159 : Reach 1159 := rs (se 1 (by rfl) ⟨869, by rfl⟩) R1739
theorem R1169 : Reach 1169 := rs (se 2 (by rfl) ⟨438, by rfl⟩) R877
theorem R1171 : Reach 1171 := rs (se 1 (by rfl) ⟨878, by rfl⟩) R1757
theorem R1179 : Reach 1179 := rs (se 1 (by rfl) ⟨884, by rfl⟩) R1769
theorem R1181 : Reach 1181 := rs (se 3 (by rfl) ⟨221, by rfl⟩) R443
theorem R1201 : Reach 1201 := rs (se 2 (by rfl) ⟨450, by rfl⟩) R901
theorem R1203 : Reach 1203 := rs (se 1 (by rfl) ⟨902, by rfl⟩) R1805
theorem R1209 : Reach 1209 := rs (se 2 (by rfl) ⟨453, by rfl⟩) R907
theorem R1277 : Reach 1277 := rs (se 3 (by rfl) ⟨239, by rfl⟩) R479
theorem R2277 : Reach 2277 := rs (se 4 (by rfl) ⟨213, by rfl⟩) R427
theorem R2283 : Reach 2283 := rs (se 1 (by rfl) ⟨1712, by rfl⟩) R3425
theorem R2295 : Reach 2295 := rs (se 1 (by rfl) ⟨1721, by rfl⟩) R3443
theorem R2297 : Reach 2297 := rs (se 2 (by rfl) ⟨861, by rfl⟩) R1723
theorem R2303 : Reach 2303 := rs (se 1 (by rfl) ⟨1727, by rfl⟩) R3455
theorem R2319 : Reach 2319 := rs (se 1 (by rfl) ⟨1739, by rfl⟩) R3479
theorem R2337 : Reach 2337 := rs (se 2 (by rfl) ⟨876, by rfl⟩) R1753
theorem R2339 : Reach 2339 := rs (se 1 (by rfl) ⟨1754, by rfl⟩) R3509
theorem R2341 : Reach 2341 := rs (se 4 (by rfl) ⟨219, by rfl⟩) R439
theorem R2351 : Reach 2351 := rs (se 1 (by rfl) ⟨1763, by rfl⟩) R3527
theorem R2359 : Reach 2359 := rs (se 1 (by rfl) ⟨1769, by rfl⟩) R3539
theorem R2361 : Reach 2361 := rs (se 2 (by rfl) ⟨885, by rfl⟩) R1771
theorem R2363 : Reach 2363 := rs (se 1 (by rfl) ⟨1772, by rfl⟩) R3545
theorem R2365 : Reach 2365 := rs (se 3 (by rfl) ⟨443, by rfl⟩) R887
theorem R2403 : Reach 2403 := rs (se 1 (by rfl) ⟨1802, by rfl⟩) R3605
theorem R2405 : Reach 2405 := rs (se 4 (by rfl) ⟨225, by rfl⟩) R451
theorem R2419 : Reach 2419 := rs (se 1 (by rfl) ⟨1814, by rfl⟩) R3629
theorem R2549 : Reach 2549 := rs (se 5 (by rfl) ⟨119, by rfl⟩) R239
theorem R2555 : Reach 2555 := rs (se 1 (by rfl) ⟨1916, by rfl⟩) R3833
theorem R2811 : Reach 2811 := rs (se 1 (by rfl) ⟨2108, by rfl⟩) R4217
theorem R2823 : Reach 2823 := rs (se 1 (by rfl) ⟨2117, by rfl⟩) R4235
theorem R167291 : Reach 167291 := rs (se 1 (by rfl) ⟨125468, by rfl⟩) R250937
theorem R36445 : Reach 36445 := rs (se 3 (by rfl) ⟨6833, by rfl⟩) R13667
theorem R36503 : Reach 36503 := rs (se 1 (by rfl) ⟨27377, by rfl⟩) R54755
theorem R36541 : Reach 36541 := rs (se 3 (by rfl) ⟨6851, by rfl⟩) R13703
theorem R36587 : Reach 36587 := rs (se 1 (by rfl) ⟨27440, by rfl⟩) R54881
theorem R36611 : Reach 36611 := rs (se 1 (by rfl) ⟨27458, by rfl⟩) R54917
theorem R299285 : Reach 299285 := rs (se 6 (by rfl) ⟨7014, by rfl⟩) R14029
theorem R37169 : Reach 37169 := rs (se 2 (by rfl) ⟨13938, by rfl⟩) R27877
theorem R4555 : Reach 4555 := rs (se 1 (by rfl) ⟨3416, by rfl⟩) R6833
theorem R4557 : Reach 4557 := rs (se 3 (by rfl) ⟨854, by rfl⟩) R1709
theorem R4561 : Reach 4561 := rs (se 2 (by rfl) ⟨1710, by rfl⟩) R3421
theorem R4567 : Reach 4567 := rs (se 1 (by rfl) ⟨3425, by rfl⟩) R6851
theorem R4571 : Reach 4571 := rs (se 1 (by rfl) ⟨3428, by rfl⟩) R6857
theorem R4589 : Reach 4589 := rs (se 3 (by rfl) ⟨860, by rfl⟩) R1721
theorem R4595 : Reach 4595 := rs (se 1 (by rfl) ⟨3446, by rfl⟩) R6893
theorem R4601 : Reach 4601 := rs (se 2 (by rfl) ⟨1725, by rfl⟩) R3451
theorem R4605 : Reach 4605 := rs (se 3 (by rfl) ⟨863, by rfl⟩) R1727
theorem R4637 : Reach 4637 := rs (se 3 (by rfl) ⟨869, by rfl⟩) R1739
theorem R4641 : Reach 4641 := rs (se 2 (by rfl) ⟨1740, by rfl⟩) R3481
theorem R4647 : Reach 4647 := rs (se 1 (by rfl) ⟨3485, by rfl⟩) R6971
theorem R4673 : Reach 4673 := rs (se 2 (by rfl) ⟨1752, by rfl⟩) R3505
theorem R4675 : Reach 4675 := rs (se 1 (by rfl) ⟨3506, by rfl⟩) R7013
theorem R4677 : Reach 4677 := rs (se 4 (by rfl) ⟨438, by rfl⟩) R877
theorem R4683 : Reach 4683 := rs (se 1 (by rfl) ⟨3512, by rfl⟩) R7025
theorem R4685 : Reach 4685 := rs (se 3 (by rfl) ⟨878, by rfl⟩) R1757
theorem R4703 : Reach 4703 := rs (se 1 (by rfl) ⟨3527, by rfl⟩) R7055
theorem R4705 : Reach 4705 := rs (se 2 (by rfl) ⟨1764, by rfl⟩) R3529
theorem R37475 : Reach 37475 := rs (se 1 (by rfl) ⟨28106, by rfl⟩) R56213
theorem R4711 : Reach 4711 := rs (se 1 (by rfl) ⟨3533, by rfl⟩) R7067
theorem R4717 : Reach 4717 := rs (se 3 (by rfl) ⟨884, by rfl⟩) R1769
theorem R4723 : Reach 4723 := rs (se 1 (by rfl) ⟨3542, by rfl⟩) R7085
theorem R4725 : Reach 4725 := rs (se 5 (by rfl) ⟨221, by rfl⟩) R443
theorem R4727 : Reach 4727 := rs (se 1 (by rfl) ⟨3545, by rfl⟩) R7091
theorem R4729 : Reach 4729 := rs (se 2 (by rfl) ⟨1773, by rfl⟩) R3547
theorem R4731 : Reach 4731 := rs (se 1 (by rfl) ⟨3548, by rfl⟩) R7097
theorem R4737 : Reach 4737 := rs (se 2 (by rfl) ⟨1776, by rfl⟩) R3553
theorem R4743 : Reach 4743 := rs (se 1 (by rfl) ⟨3557, by rfl⟩) R7115
theorem R4775 : Reach 4775 := rs (se 1 (by rfl) ⟨3581, by rfl⟩) R7163
theorem R4805 : Reach 4805 := rs (se 4 (by rfl) ⟨450, by rfl⟩) R901
theorem R37579 : Reach 37579 := rs (se 1 (by rfl) ⟨28184, by rfl⟩) R56369
theorem R4813 : Reach 4813 := rs (se 3 (by rfl) ⟨902, by rfl⟩) R1805
theorem R4825 : Reach 4825 := rs (se 2 (by rfl) ⟨1809, by rfl⟩) R3619
theorem R4837 : Reach 4837 := rs (se 4 (by rfl) ⟨453, by rfl⟩) R907
theorem R37637 : Reach 37637 := rs (se 4 (by rfl) ⟨3528, by rfl⟩) R7057
theorem R37675 : Reach 37675 := rs (se 1 (by rfl) ⟨28256, by rfl⟩) R56513
theorem R37691 : Reach 37691 := rs (se 1 (by rfl) ⟨28268, by rfl⟩) R56537
theorem R299861 : Reach 299861 := rs (se 9 (by rfl) ⟨878, by rfl⟩) R1757
theorem R37745 : Reach 37745 := rs (se 2 (by rfl) ⟨14154, by rfl⟩) R28309
theorem R37817 : Reach 37817 := rs (se 2 (by rfl) ⟨14181, by rfl⟩) R28363
theorem R37829 : Reach 37829 := rs (se 4 (by rfl) ⟨3546, by rfl⟩) R7093
theorem R37847 : Reach 37847 := rs (se 1 (by rfl) ⟨28385, by rfl⟩) R56771
theorem R37853 : Reach 37853 := rs (se 3 (by rfl) ⟨7097, by rfl⟩) R14195
theorem R5105 : Reach 5105 := rs (se 2 (by rfl) ⟨1914, by rfl⟩) R3829
theorem R5109 : Reach 5109 := rs (se 5 (by rfl) ⟨239, by rfl⟩) R479
theorem R5111 : Reach 5111 := rs (se 1 (by rfl) ⟨3833, by rfl⟩) R7667
theorem R5115 : Reach 5115 := rs (se 1 (by rfl) ⟨3836, by rfl⟩) R7673
theorem R37907 : Reach 37907 := rs (se 1 (by rfl) ⟨28430, by rfl⟩) R56861
theorem R5145 : Reach 5145 := rs (se 2 (by rfl) ⟨1929, by rfl⟩) R3859
theorem R5223 : Reach 5223 := rs (se 1 (by rfl) ⟨3917, by rfl⟩) R7835
theorem R5623 : Reach 5623 := rs (se 1 (by rfl) ⟨4217, by rfl⟩) R8435
theorem R5627 : Reach 5627 := rs (se 1 (by rfl) ⟨4220, by rfl⟩) R8441
theorem R5633 : Reach 5633 := rs (se 2 (by rfl) ⟨2112, by rfl⟩) R4225
theorem R5647 : Reach 5647 := rs (se 1 (by rfl) ⟨4235, by rfl⟩) R8471
theorem R38731 : Reach 38731 := rs (se 1 (by rfl) ⟨29048, by rfl⟩) R58097
theorem R38843 : Reach 38843 := rs (se 1 (by rfl) ⟨29132, by rfl⟩) R58265
theorem R73061 : Reach 73061 := rs (se 4 (by rfl) ⟨6849, by rfl⟩) R13699
theorem R41039 : Reach 41039 := rs (se 1 (by rfl) ⟨30779, by rfl⟩) R61559
theorem R41435 : Reach 41435 := rs (se 1 (by rfl) ⟨31076, by rfl⟩) R62153
theorem R74357 : Reach 74357 := rs (se 5 (by rfl) ⟨3485, by rfl⟩) R6971
theorem R9109 : Reach 9109 := rs (se 6 (by rfl) ⟨213, by rfl⟩) R427
theorem R9111 : Reach 9111 := rs (se 1 (by rfl) ⟨6833, by rfl⟩) R13667
theorem R9113 : Reach 9113 := rs (se 2 (by rfl) ⟨3417, by rfl⟩) R6835
theorem R9121 : Reach 9121 := rs (se 2 (by rfl) ⟨3420, by rfl⟩) R6841
theorem R9123 : Reach 9123 := rs (se 1 (by rfl) ⟨6842, by rfl⟩) R13685
theorem R9133 : Reach 9133 := rs (se 3 (by rfl) ⟨1712, by rfl⟩) R3425
theorem R9135 : Reach 9135 := rs (se 1 (by rfl) ⟨6851, by rfl⟩) R13703
theorem R9143 : Reach 9143 := rs (se 1 (by rfl) ⟨6857, by rfl⟩) R13715
theorem R9179 : Reach 9179 := rs (se 1 (by rfl) ⟨6884, by rfl⟩) R13769
theorem R9181 : Reach 9181 := rs (se 3 (by rfl) ⟨1721, by rfl⟩) R3443
theorem R9189 : Reach 9189 := rs (se 4 (by rfl) ⟨861, by rfl⟩) R1723
theorem R9191 : Reach 9191 := rs (se 1 (by rfl) ⟨6893, by rfl⟩) R13787
theorem R9203 : Reach 9203 := rs (se 1 (by rfl) ⟨6902, by rfl⟩) R13805
theorem R9213 : Reach 9213 := rs (se 3 (by rfl) ⟨1727, by rfl⟩) R3455
theorem R9277 : Reach 9277 := rs (se 3 (by rfl) ⟨1739, by rfl⟩) R3479
theorem R9281 : Reach 9281 := rs (se 2 (by rfl) ⟨3480, by rfl⟩) R6961
theorem R9283 : Reach 9283 := rs (se 1 (by rfl) ⟨6962, by rfl⟩) R13925
theorem R9295 : Reach 9295 := rs (se 1 (by rfl) ⟨6971, by rfl⟩) R13943
theorem R74837 : Reach 74837 := rs (se 8 (by rfl) ⟨438, by rfl⟩) R877
theorem R9321 : Reach 9321 := rs (se 2 (by rfl) ⟨3495, by rfl⟩) R6991
theorem R9323 : Reach 9323 := rs (se 1 (by rfl) ⟨6992, by rfl⟩) R13985
theorem R9343 : Reach 9343 := rs (se 1 (by rfl) ⟨7007, by rfl⟩) R14015
theorem R9347 : Reach 9347 := rs (se 1 (by rfl) ⟨7010, by rfl⟩) R14021
theorem R9349 : Reach 9349 := rs (se 4 (by rfl) ⟨876, by rfl⟩) R1753
theorem R9357 : Reach 9357 := rs (se 3 (by rfl) ⟨1754, by rfl⟩) R3509
theorem R9365 : Reach 9365 := rs (se 6 (by rfl) ⟨219, by rfl⟩) R439
theorem R9367 : Reach 9367 := rs (se 1 (by rfl) ⟨7025, by rfl⟩) R14051
theorem R9369 : Reach 9369 := rs (se 2 (by rfl) ⟨3513, by rfl⟩) R7027
theorem R9387 : Reach 9387 := rs (se 1 (by rfl) ⟨7040, by rfl⟩) R14081
theorem R9391 : Reach 9391 := rs (se 1 (by rfl) ⟨7043, by rfl⟩) R14087
theorem R9401 : Reach 9401 := rs (se 2 (by rfl) ⟨3525, by rfl⟩) R7051
theorem R9403 : Reach 9403 := rs (se 1 (by rfl) ⟨7052, by rfl⟩) R14105
theorem R9405 : Reach 9405 := rs (se 3 (by rfl) ⟨1763, by rfl⟩) R3527
theorem R9409 : Reach 9409 := rs (se 2 (by rfl) ⟨3528, by rfl⟩) R7057
theorem R9411 : Reach 9411 := rs (se 1 (by rfl) ⟨7058, by rfl⟩) R14117
theorem R9415 : Reach 9415 := rs (se 1 (by rfl) ⟨7061, by rfl⟩) R14123
theorem R9423 : Reach 9423 := rs (se 1 (by rfl) ⟨7067, by rfl⟩) R14135
theorem R9437 : Reach 9437 := rs (se 3 (by rfl) ⟨1769, by rfl⟩) R3539
theorem R9445 : Reach 9445 := rs (se 4 (by rfl) ⟨885, by rfl⟩) R1771
theorem R9449 : Reach 9449 := rs (se 2 (by rfl) ⟨3543, by rfl⟩) R7087
theorem R9453 : Reach 9453 := rs (se 3 (by rfl) ⟨1772, by rfl⟩) R3545
theorem R9457 : Reach 9457 := rs (se 2 (by rfl) ⟨3546, by rfl⟩) R7093
theorem R9459 : Reach 9459 := rs (se 1 (by rfl) ⟨7094, by rfl⟩) R14189
theorem R9461 : Reach 9461 := rs (se 5 (by rfl) ⟨443, by rfl⟩) R887
theorem R9463 : Reach 9463 := rs (se 1 (by rfl) ⟨7097, by rfl⟩) R14195
theorem R9465 : Reach 9465 := rs (se 2 (by rfl) ⟨3549, by rfl⟩) R7099
theorem R9473 : Reach 9473 := rs (se 2 (by rfl) ⟨3552, by rfl⟩) R7105
theorem R9475 : Reach 9475 := rs (se 1 (by rfl) ⟨7106, by rfl⟩) R14213
theorem R9487 : Reach 9487 := rs (se 1 (by rfl) ⟨7115, by rfl⟩) R14231
theorem R9551 : Reach 9551 := rs (se 1 (by rfl) ⟨7163, by rfl⟩) R14327
theorem R9613 : Reach 9613 := rs (se 3 (by rfl) ⟨1802, by rfl⟩) R3605
theorem R9621 : Reach 9621 := rs (se 6 (by rfl) ⟨225, by rfl⟩) R451
theorem R9649 : Reach 9649 := rs (se 2 (by rfl) ⟨3618, by rfl⟩) R7237
theorem R9651 : Reach 9651 := rs (se 1 (by rfl) ⟨7238, by rfl⟩) R14477
theorem R9657 : Reach 9657 := rs (se 2 (by rfl) ⟨3621, by rfl⟩) R7243
theorem R9673 : Reach 9673 := rs (se 2 (by rfl) ⟨3627, by rfl⟩) R7255
theorem R9677 : Reach 9677 := rs (se 3 (by rfl) ⟨1814, by rfl⟩) R3629
theorem R9681 : Reach 9681 := rs (se 2 (by rfl) ⟨3630, by rfl⟩) R7261
theorem R9691 : Reach 9691 := rs (se 1 (by rfl) ⟨7268, by rfl⟩) R14537
theorem R9711 : Reach 9711 := rs (se 1 (by rfl) ⟨7283, by rfl⟩) R14567
theorem R9755 : Reach 9755 := rs (se 1 (by rfl) ⟨7316, by rfl⟩) R14633
theorem R9857 : Reach 9857 := rs (se 2 (by rfl) ⟨3696, by rfl⟩) R7393
theorem R10139 : Reach 10139 := rs (se 1 (by rfl) ⟨7604, by rfl⟩) R15209
theorem R10153 : Reach 10153 := rs (se 2 (by rfl) ⟨3807, by rfl⟩) R7615
theorem R75725 : Reach 75725 := rs (se 3 (by rfl) ⟨14198, by rfl⟩) R28397
theorem R10197 : Reach 10197 := rs (se 7 (by rfl) ⟨119, by rfl⟩) R239
theorem R10211 : Reach 10211 := rs (se 1 (by rfl) ⟨7658, by rfl⟩) R15317
theorem R10221 : Reach 10221 := rs (se 3 (by rfl) ⟨1916, by rfl⟩) R3833
theorem R10225 : Reach 10225 := rs (se 2 (by rfl) ⟨3834, by rfl⟩) R7669
theorem R10231 : Reach 10231 := rs (se 1 (by rfl) ⟨7673, by rfl⟩) R15347
theorem R10249 : Reach 10249 := rs (se 2 (by rfl) ⟨3843, by rfl⟩) R7687
theorem R10271 : Reach 10271 := rs (se 1 (by rfl) ⟨7703, by rfl⟩) R15407
theorem R10289 : Reach 10289 := rs (se 2 (by rfl) ⟨3858, by rfl⟩) R7717
theorem R10291 : Reach 10291 := rs (se 1 (by rfl) ⟨7718, by rfl⟩) R15437
theorem R10299 : Reach 10299 := rs (se 1 (by rfl) ⟨7724, by rfl⟩) R15449
theorem R10443 : Reach 10443 := rs (se 1 (by rfl) ⟨7832, by rfl⟩) R15665
theorem R10447 : Reach 10447 := rs (se 1 (by rfl) ⟨7835, by rfl⟩) R15671
theorem R10567 : Reach 10567 := rs (se 1 (by rfl) ⟨7925, by rfl⟩) R15851
theorem R11239 : Reach 11239 := rs (se 1 (by rfl) ⟨8429, by rfl⟩) R16859
theorem R11245 : Reach 11245 := rs (se 3 (by rfl) ⟨2108, by rfl⟩) R4217
theorem R11247 : Reach 11247 := rs (se 1 (by rfl) ⟨8435, by rfl⟩) R16871
theorem R11255 : Reach 11255 := rs (se 1 (by rfl) ⟨8441, by rfl⟩) R16883
theorem R11259 : Reach 11259 := rs (se 1 (by rfl) ⟨8444, by rfl⟩) R16889
theorem R11265 : Reach 11265 := rs (se 2 (by rfl) ⟨4224, by rfl⟩) R8449
theorem R11267 : Reach 11267 := rs (se 1 (by rfl) ⟨8450, by rfl⟩) R16901
theorem R11271 : Reach 11271 := rs (se 1 (by rfl) ⟨8453, by rfl⟩) R16907
theorem R11293 : Reach 11293 := rs (se 3 (by rfl) ⟨2117, by rfl⟩) R4235
theorem R11295 : Reach 11295 := rs (se 1 (by rfl) ⟨8471, by rfl⟩) R16943
theorem R11297 : Reach 11297 := rs (se 2 (by rfl) ⟨4236, by rfl⟩) R8473
theorem R44981 : Reach 44981 := rs (se 5 (by rfl) ⟨2108, by rfl⟩) R4217
theorem R45035 : Reach 45035 := rs (se 1 (by rfl) ⟨33776, by rfl⟩) R67553
theorem R45107 : Reach 45107 := rs (se 1 (by rfl) ⟨33830, by rfl⟩) R67661
theorem R78887 : Reach 78887 := rs (se 1 (by rfl) ⟨59165, by rfl⟩) R118331
theorem R82325 : Reach 82325 := rs (se 6 (by rfl) ⟨1929, by rfl⟩) R3859
theorem R83591 : Reach 83591 := rs (se 1 (by rfl) ⟨62693, by rfl⟩) R125387
theorem R18221 : Reach 18221 := rs (se 3 (by rfl) ⟨3416, by rfl⟩) R6833
theorem R18227 : Reach 18227 := rs (se 1 (by rfl) ⟨13670, by rfl⟩) R27341
theorem R18245 : Reach 18245 := rs (se 4 (by rfl) ⟨1710, by rfl⟩) R3421
theorem R18251 : Reach 18251 := rs (se 1 (by rfl) ⟨13688, by rfl⟩) R27377
theorem R18265 : Reach 18265 := rs (se 2 (by rfl) ⟨6849, by rfl⟩) R13699
theorem R18269 : Reach 18269 := rs (se 3 (by rfl) ⟨3425, by rfl⟩) R6851
theorem R18305 : Reach 18305 := rs (se 2 (by rfl) ⟨6864, by rfl⟩) R13729
theorem R18359 : Reach 18359 := rs (se 1 (by rfl) ⟨13769, by rfl⟩) R27539
theorem R18383 : Reach 18383 := rs (se 1 (by rfl) ⟨13787, by rfl⟩) R27575
theorem R18563 : Reach 18563 := rs (se 1 (by rfl) ⟨13922, by rfl⟩) R27845
theorem R18587 : Reach 18587 := rs (se 1 (by rfl) ⟨13940, by rfl⟩) R27881
theorem R18589 : Reach 18589 := rs (se 3 (by rfl) ⟨3485, by rfl⟩) R6971
theorem R18641 : Reach 18641 := rs (se 2 (by rfl) ⟨6990, by rfl⟩) R13981
theorem R18643 : Reach 18643 := rs (se 1 (by rfl) ⟨13982, by rfl⟩) R27965
theorem R18647 : Reach 18647 := rs (se 1 (by rfl) ⟨13985, by rfl⟩) R27971
theorem R18701 : Reach 18701 := rs (se 3 (by rfl) ⟨3506, by rfl⟩) R7013
theorem R18737 : Reach 18737 := rs (se 2 (by rfl) ⟨7026, by rfl⟩) R14053
theorem R18779 : Reach 18779 := rs (se 1 (by rfl) ⟨14084, by rfl⟩) R28169
theorem R18803 : Reach 18803 := rs (se 1 (by rfl) ⟨14102, by rfl⟩) R28205
theorem R18821 : Reach 18821 := rs (se 4 (by rfl) ⟨1764, by rfl⟩) R3529
theorem R18845 : Reach 18845 := rs (se 3 (by rfl) ⟨3533, by rfl⟩) R7067
theorem R18857 : Reach 18857 := rs (se 2 (by rfl) ⟨7071, by rfl⟩) R14143
theorem R18869 : Reach 18869 := rs (se 5 (by rfl) ⟨884, by rfl⟩) R1769
theorem R18881 : Reach 18881 := rs (se 2 (by rfl) ⟨7080, by rfl⟩) R14161
theorem R18893 : Reach 18893 := rs (se 3 (by rfl) ⟨3542, by rfl⟩) R7085
theorem R18899 : Reach 18899 := rs (se 1 (by rfl) ⟨14174, by rfl⟩) R28349
theorem R18905 : Reach 18905 := rs (se 2 (by rfl) ⟨7089, by rfl⟩) R14179
theorem R18913 : Reach 18913 := rs (se 2 (by rfl) ⟨7092, by rfl⟩) R14185
theorem R18917 : Reach 18917 := rs (se 4 (by rfl) ⟨1773, by rfl⟩) R3547
theorem R18923 : Reach 18923 := rs (se 1 (by rfl) ⟨14192, by rfl⟩) R28385
theorem R18929 : Reach 18929 := rs (se 2 (by rfl) ⟨7098, by rfl⟩) R14197
theorem R18947 : Reach 18947 := rs (se 1 (by rfl) ⟨14210, by rfl⟩) R28421
theorem R18949 : Reach 18949 := rs (se 4 (by rfl) ⟨1776, by rfl⟩) R3553
theorem R18953 : Reach 18953 := rs (se 2 (by rfl) ⟨7107, by rfl⟩) R14215
theorem R18977 : Reach 18977 := rs (se 2 (by rfl) ⟨7116, by rfl⟩) R14233
theorem R150083 : Reach 150083 := rs (se 1 (by rfl) ⟨112562, by rfl⟩) R225125
theorem R19345 : Reach 19345 := rs (se 2 (by rfl) ⟨7254, by rfl⟩) R14509
theorem R19349 : Reach 19349 := rs (se 6 (by rfl) ⟨453, by rfl⟩) R907
theorem R19511 : Reach 19511 := rs (se 1 (by rfl) ⟨14633, by rfl⟩) R29267
theorem R85049 : Reach 85049 := rs (se 2 (by rfl) ⟨31893, by rfl⟩) R63787
theorem R19723 : Reach 19723 := rs (se 1 (by rfl) ⟨14792, by rfl⟩) R29585
theorem R20263 : Reach 20263 := rs (se 1 (by rfl) ⟨15197, by rfl⟩) R30395
theorem R20519 : Reach 20519 := rs (se 1 (by rfl) ⟨15389, by rfl⟩) R30779
theorem R20699 : Reach 20699 := rs (se 1 (by rfl) ⟨15524, by rfl⟩) R31049
theorem R20729 : Reach 20729 := rs (se 2 (by rfl) ⟨7773, by rfl⟩) R15547
theorem R20891 : Reach 20891 := rs (se 1 (by rfl) ⟨15668, by rfl⟩) R31337
theorem R22493 : Reach 22493 := rs (se 3 (by rfl) ⟨4217, by rfl⟩) R8435
theorem R22531 : Reach 22531 := rs (se 1 (by rfl) ⟨16898, by rfl⟩) R33797
theorem R22535 : Reach 22535 := rs (se 1 (by rfl) ⟨16901, by rfl⟩) R33803
theorem R22553 : Reach 22553 := rs (se 2 (by rfl) ⟨8457, by rfl⟩) R16915
theorem R22589 : Reach 22589 := rs (se 3 (by rfl) ⟨4235, by rfl⟩) R8471
theorem R89915 : Reach 89915 := rs (se 1 (by rfl) ⟨67436, by rfl⟩) R134873
theorem R379 : Reach 379 := rs (se 1 (by rfl) ⟨284, by rfl⟩) R569
theorem R393 : Reach 393 := rs (se 2 (by rfl) ⟨147, by rfl⟩) R295
theorem R425 : Reach 425 := rs (se 2 (by rfl) ⟨159, by rfl⟩) R319
theorem R759 : Reach 759 := rs (se 1 (by rfl) ⟨569, by rfl⟩) R1139
theorem R767 : Reach 767 := rs (se 1 (by rfl) ⟨575, by rfl⟩) R1151
theorem R779 : Reach 779 := rs (se 1 (by rfl) ⟨584, by rfl⟩) R1169
theorem R787 : Reach 787 := rs (se 1 (by rfl) ⟨590, by rfl⟩) R1181
theorem R801 : Reach 801 := rs (se 2 (by rfl) ⟨300, by rfl⟩) R601
theorem R849 : Reach 849 := rs (se 2 (by rfl) ⟨318, by rfl⟩) R637
theorem R851 : Reach 851 := rs (se 1 (by rfl) ⟨638, by rfl⟩) R1277
theorem R197909 : Reach 197909 := rs (se 6 (by rfl) ⟨4638, by rfl⟩) R9277
theorem R99733 : Reach 99733 := rs (se 6 (by rfl) ⟨2337, by rfl⟩) R4675
theorem R1517 : Reach 1517 := rs (se 3 (by rfl) ⟨284, by rfl⟩) R569
theorem R1529 : Reach 1529 := rs (se 2 (by rfl) ⟨573, by rfl⟩) R1147
theorem R1531 : Reach 1531 := rs (se 1 (by rfl) ⟨1148, by rfl⟩) R2297
theorem R1535 : Reach 1535 := rs (se 1 (by rfl) ⟨1151, by rfl⟩) R2303
theorem R1545 : Reach 1545 := rs (se 2 (by rfl) ⟨579, by rfl⟩) R1159
theorem R1559 : Reach 1559 := rs (se 1 (by rfl) ⟨1169, by rfl⟩) R2339
theorem R1561 : Reach 1561 := rs (se 2 (by rfl) ⟨585, by rfl⟩) R1171
theorem R1567 : Reach 1567 := rs (se 1 (by rfl) ⟨1175, by rfl⟩) R2351
theorem R1573 : Reach 1573 := rs (se 4 (by rfl) ⟨147, by rfl⟩) R295
theorem R1575 : Reach 1575 := rs (se 1 (by rfl) ⟨1181, by rfl⟩) R2363
theorem R1601 : Reach 1601 := rs (se 2 (by rfl) ⟨600, by rfl⟩) R1201
theorem R1603 : Reach 1603 := rs (se 1 (by rfl) ⟨1202, by rfl⟩) R2405
theorem R1699 : Reach 1699 := rs (se 1 (by rfl) ⟨1274, by rfl⟩) R2549
theorem R1701 : Reach 1701 := rs (se 4 (by rfl) ⟨159, by rfl⟩) R319
theorem R1703 : Reach 1703 := rs (se 1 (by rfl) ⟨1277, by rfl⟩) R2555
theorem R100055 : Reach 100055 := rs (se 1 (by rfl) ⟨75041, by rfl⟩) R150083
theorem R199523 : Reach 199523 := rs (se 1 (by rfl) ⟨149642, by rfl⟩) R299285
theorem R3037 : Reach 3037 := rs (se 3 (by rfl) ⟨569, by rfl⟩) R1139
theorem R3047 : Reach 3047 := rs (se 1 (by rfl) ⟨2285, by rfl⟩) R4571
theorem R3059 : Reach 3059 := rs (se 1 (by rfl) ⟨2294, by rfl⟩) R4589
theorem R3063 : Reach 3063 := rs (se 1 (by rfl) ⟨2297, by rfl⟩) R4595
theorem R3067 : Reach 3067 := rs (se 1 (by rfl) ⟨2300, by rfl⟩) R4601
theorem R3069 : Reach 3069 := rs (se 3 (by rfl) ⟨575, by rfl⟩) R1151
theorem R3091 : Reach 3091 := rs (se 1 (by rfl) ⟨2318, by rfl⟩) R4637
theorem R3115 : Reach 3115 := rs (se 1 (by rfl) ⟨2336, by rfl⟩) R4673
theorem R3117 : Reach 3117 := rs (se 3 (by rfl) ⟨584, by rfl⟩) R1169
theorem R3121 : Reach 3121 := rs (se 2 (by rfl) ⟨1170, by rfl⟩) R2341
theorem R3123 : Reach 3123 := rs (se 1 (by rfl) ⟨2342, by rfl⟩) R4685
theorem R3135 : Reach 3135 := rs (se 1 (by rfl) ⟨2351, by rfl⟩) R4703
theorem R3145 : Reach 3145 := rs (se 2 (by rfl) ⟨1179, by rfl⟩) R2359
theorem R3149 : Reach 3149 := rs (se 3 (by rfl) ⟨590, by rfl⟩) R1181
theorem R3151 : Reach 3151 := rs (se 1 (by rfl) ⟨2363, by rfl⟩) R4727
theorem R3153 : Reach 3153 := rs (se 2 (by rfl) ⟨1182, by rfl⟩) R2365
theorem R3183 : Reach 3183 := rs (se 1 (by rfl) ⟨2387, by rfl⟩) R4775
theorem R3203 : Reach 3203 := rs (se 1 (by rfl) ⟨2402, by rfl⟩) R4805
theorem R3205 : Reach 3205 := rs (se 4 (by rfl) ⟨300, by rfl⟩) R601
theorem R3225 : Reach 3225 := rs (se 2 (by rfl) ⟨1209, by rfl⟩) R2419
theorem R199907 : Reach 199907 := rs (se 1 (by rfl) ⟨149930, by rfl⟩) R299861
theorem R3397 : Reach 3397 := rs (se 4 (by rfl) ⟨318, by rfl⟩) R637
theorem R3403 : Reach 3403 := rs (se 1 (by rfl) ⟨2552, by rfl⟩) R5105
theorem R3405 : Reach 3405 := rs (se 3 (by rfl) ⟨638, by rfl⟩) R1277
theorem R3407 : Reach 3407 := rs (se 1 (by rfl) ⟨2555, by rfl⟩) R5111
theorem R3751 : Reach 3751 := rs (se 1 (by rfl) ⟨2813, by rfl⟩) R5627
theorem R3755 : Reach 3755 := rs (se 1 (by rfl) ⟨2816, by rfl⟩) R5633
theorem R6069 : Reach 6069 := rs (se 5 (by rfl) ⟨284, by rfl⟩) R569
theorem R6073 : Reach 6073 := rs (se 2 (by rfl) ⟨2277, by rfl⟩) R4555
theorem R6075 : Reach 6075 := rs (se 1 (by rfl) ⟨4556, by rfl⟩) R9113
theorem R6081 : Reach 6081 := rs (se 2 (by rfl) ⟨2280, by rfl⟩) R4561
theorem R6089 : Reach 6089 := rs (se 2 (by rfl) ⟨2283, by rfl⟩) R4567
theorem R6095 : Reach 6095 := rs (se 1 (by rfl) ⟨4571, by rfl⟩) R9143
theorem R6117 : Reach 6117 := rs (se 4 (by rfl) ⟨573, by rfl⟩) R1147
theorem R6119 : Reach 6119 := rs (se 1 (by rfl) ⟨4589, by rfl⟩) R9179
theorem R6125 : Reach 6125 := rs (se 3 (by rfl) ⟨1148, by rfl⟩) R2297
theorem R6127 : Reach 6127 := rs (se 1 (by rfl) ⟨4595, by rfl⟩) R9191
theorem R6135 : Reach 6135 := rs (se 1 (by rfl) ⟨4601, by rfl⟩) R9203
theorem R6141 : Reach 6141 := rs (se 3 (by rfl) ⟨1151, by rfl⟩) R2303
theorem R6181 : Reach 6181 := rs (se 4 (by rfl) ⟨579, by rfl⟩) R1159
theorem R6187 : Reach 6187 := rs (se 1 (by rfl) ⟨4640, by rfl⟩) R9281
theorem R6215 : Reach 6215 := rs (se 1 (by rfl) ⟨4661, by rfl⟩) R9323
theorem R6231 : Reach 6231 := rs (se 1 (by rfl) ⟨4673, by rfl⟩) R9347
theorem R6233 : Reach 6233 := rs (se 2 (by rfl) ⟨2337, by rfl⟩) R4675
theorem R6237 : Reach 6237 := rs (se 3 (by rfl) ⟨1169, by rfl⟩) R2339
theorem R6243 : Reach 6243 := rs (se 1 (by rfl) ⟨4682, by rfl⟩) R9365
theorem R6245 : Reach 6245 := rs (se 4 (by rfl) ⟨585, by rfl⟩) R1171
theorem R6267 : Reach 6267 := rs (se 1 (by rfl) ⟨4700, by rfl⟩) R9401
theorem R6269 : Reach 6269 := rs (se 3 (by rfl) ⟨1175, by rfl⟩) R2351
theorem R6273 : Reach 6273 := rs (se 2 (by rfl) ⟨2352, by rfl⟩) R4705
theorem R6281 : Reach 6281 := rs (se 2 (by rfl) ⟨2355, by rfl⟩) R4711
theorem R6289 : Reach 6289 := rs (se 2 (by rfl) ⟨2358, by rfl⟩) R4717
theorem R6291 : Reach 6291 := rs (se 1 (by rfl) ⟨4718, by rfl⟩) R9437
theorem R6293 : Reach 6293 := rs (se 6 (by rfl) ⟨147, by rfl⟩) R295
theorem R6297 : Reach 6297 := rs (se 2 (by rfl) ⟨2361, by rfl⟩) R4723
theorem R6299 : Reach 6299 := rs (se 1 (by rfl) ⟨4724, by rfl⟩) R9449
theorem R6301 : Reach 6301 := rs (se 3 (by rfl) ⟨1181, by rfl⟩) R2363
theorem R6305 : Reach 6305 := rs (se 2 (by rfl) ⟨2364, by rfl⟩) R4729
theorem R6307 : Reach 6307 := rs (se 1 (by rfl) ⟨4730, by rfl⟩) R9461
theorem R6315 : Reach 6315 := rs (se 1 (by rfl) ⟨4736, by rfl⟩) R9473
theorem R6367 : Reach 6367 := rs (se 1 (by rfl) ⟨4775, by rfl⟩) R9551
theorem R6405 : Reach 6405 := rs (se 4 (by rfl) ⟨600, by rfl⟩) R1201
theorem R6413 : Reach 6413 := rs (se 3 (by rfl) ⟨1202, by rfl⟩) R2405
theorem R6417 : Reach 6417 := rs (se 2 (by rfl) ⟨2406, by rfl⟩) R4813
theorem R6433 : Reach 6433 := rs (se 2 (by rfl) ⟨2412, by rfl⟩) R4825
theorem R6449 : Reach 6449 := rs (se 2 (by rfl) ⟨2418, by rfl⟩) R4837
theorem R6451 : Reach 6451 := rs (se 1 (by rfl) ⟨4838, by rfl⟩) R9677
theorem R6503 : Reach 6503 := rs (se 1 (by rfl) ⟨4877, by rfl⟩) R9755
theorem R6571 : Reach 6571 := rs (se 1 (by rfl) ⟨4928, by rfl⟩) R9857
theorem R6759 : Reach 6759 := rs (se 1 (by rfl) ⟨5069, by rfl⟩) R10139
theorem R6797 : Reach 6797 := rs (se 3 (by rfl) ⟨1274, by rfl⟩) R2549
theorem R6805 : Reach 6805 := rs (se 6 (by rfl) ⟨159, by rfl⟩) R319
theorem R6807 : Reach 6807 := rs (se 1 (by rfl) ⟨5105, by rfl⟩) R10211
theorem R6813 : Reach 6813 := rs (se 3 (by rfl) ⟨1277, by rfl⟩) R2555
theorem R6847 : Reach 6847 := rs (se 1 (by rfl) ⟨5135, by rfl⟩) R10271
theorem R6859 : Reach 6859 := rs (se 1 (by rfl) ⟨5144, by rfl⟩) R10289
theorem R7497 : Reach 7497 := rs (se 2 (by rfl) ⟨2811, by rfl⟩) R5623
theorem R7503 : Reach 7503 := rs (se 1 (by rfl) ⟨5627, by rfl⟩) R11255
theorem R7511 : Reach 7511 := rs (se 1 (by rfl) ⟨5633, by rfl⟩) R11267
theorem R7529 : Reach 7529 := rs (se 2 (by rfl) ⟨2823, by rfl⟩) R5647
theorem R7531 : Reach 7531 := rs (se 1 (by rfl) ⟨5648, by rfl⟩) R11297
theorem R239773 : Reach 239773 := rs (se 3 (by rfl) ⟨44957, by rfl⟩) R89915
theorem R12145 : Reach 12145 := rs (se 2 (by rfl) ⟨4554, by rfl⟩) R9109
theorem R12147 : Reach 12147 := rs (se 1 (by rfl) ⟨9110, by rfl⟩) R18221
theorem R12149 : Reach 12149 := rs (se 5 (by rfl) ⟨569, by rfl⟩) R1139
theorem R12151 : Reach 12151 := rs (se 1 (by rfl) ⟨9113, by rfl⟩) R18227
theorem R12161 : Reach 12161 := rs (se 2 (by rfl) ⟨4560, by rfl⟩) R9121
theorem R12163 : Reach 12163 := rs (se 1 (by rfl) ⟨9122, by rfl⟩) R18245
theorem R12167 : Reach 12167 := rs (se 1 (by rfl) ⟨9125, by rfl⟩) R18251
theorem R12177 : Reach 12177 := rs (se 2 (by rfl) ⟨4566, by rfl⟩) R9133
theorem R12179 : Reach 12179 := rs (se 1 (by rfl) ⟨9134, by rfl⟩) R18269
theorem R12189 : Reach 12189 := rs (se 3 (by rfl) ⟨2285, by rfl⟩) R4571
theorem R12203 : Reach 12203 := rs (se 1 (by rfl) ⟨9152, by rfl⟩) R18305
theorem R12237 : Reach 12237 := rs (se 3 (by rfl) ⟨2294, by rfl⟩) R4589
theorem R12239 : Reach 12239 := rs (se 1 (by rfl) ⟨9179, by rfl⟩) R18359
theorem R12241 : Reach 12241 := rs (se 2 (by rfl) ⟨4590, by rfl⟩) R9181
theorem R12253 : Reach 12253 := rs (se 3 (by rfl) ⟨2297, by rfl⟩) R4595
theorem R12255 : Reach 12255 := rs (se 1 (by rfl) ⟨9191, by rfl⟩) R18383
theorem R12269 : Reach 12269 := rs (se 3 (by rfl) ⟨2300, by rfl⟩) R4601
theorem R12277 : Reach 12277 := rs (se 5 (by rfl) ⟨575, by rfl⟩) R1151
theorem R12365 : Reach 12365 := rs (se 3 (by rfl) ⟨2318, by rfl⟩) R4637
theorem R12369 : Reach 12369 := rs (se 2 (by rfl) ⟨4638, by rfl⟩) R9277
theorem R12375 : Reach 12375 := rs (se 1 (by rfl) ⟨9281, by rfl⟩) R18563
theorem R12377 : Reach 12377 := rs (se 2 (by rfl) ⟨4641, by rfl⟩) R9283
theorem R12391 : Reach 12391 := rs (se 1 (by rfl) ⟨9293, by rfl⟩) R18587
theorem R12393 : Reach 12393 := rs (se 2 (by rfl) ⟨4647, by rfl⟩) R9295
theorem R12427 : Reach 12427 := rs (se 1 (by rfl) ⟨9320, by rfl⟩) R18641
theorem R12431 : Reach 12431 := rs (se 1 (by rfl) ⟨9323, by rfl⟩) R18647
theorem R12457 : Reach 12457 := rs (se 2 (by rfl) ⟨4671, by rfl⟩) R9343
theorem R12461 : Reach 12461 := rs (se 3 (by rfl) ⟨2336, by rfl⟩) R4673
theorem R12465 : Reach 12465 := rs (se 2 (by rfl) ⟨4674, by rfl⟩) R9349
theorem R12467 : Reach 12467 := rs (se 1 (by rfl) ⟨9350, by rfl⟩) R18701
theorem R12469 : Reach 12469 := rs (se 5 (by rfl) ⟨584, by rfl⟩) R1169
theorem R12485 : Reach 12485 := rs (se 4 (by rfl) ⟨1170, by rfl⟩) R2341
theorem R12489 : Reach 12489 := rs (se 2 (by rfl) ⟨4683, by rfl⟩) R9367
theorem R12491 : Reach 12491 := rs (se 1 (by rfl) ⟨9368, by rfl⟩) R18737
theorem R12493 : Reach 12493 := rs (se 3 (by rfl) ⟨2342, by rfl⟩) R4685
theorem R12519 : Reach 12519 := rs (se 1 (by rfl) ⟨9389, by rfl⟩) R18779
theorem R12521 : Reach 12521 := rs (se 2 (by rfl) ⟨4695, by rfl⟩) R9391
theorem R12535 : Reach 12535 := rs (se 1 (by rfl) ⟨9401, by rfl⟩) R18803
theorem R12537 : Reach 12537 := rs (se 2 (by rfl) ⟨4701, by rfl⟩) R9403
theorem R12541 : Reach 12541 := rs (se 3 (by rfl) ⟨2351, by rfl⟩) R4703
theorem R12545 : Reach 12545 := rs (se 2 (by rfl) ⟨4704, by rfl⟩) R9409
theorem R12547 : Reach 12547 := rs (se 1 (by rfl) ⟨9410, by rfl⟩) R18821
theorem R12553 : Reach 12553 := rs (se 2 (by rfl) ⟨4707, by rfl⟩) R9415
theorem R12563 : Reach 12563 := rs (se 1 (by rfl) ⟨9422, by rfl⟩) R18845
theorem R12571 : Reach 12571 := rs (se 1 (by rfl) ⟨9428, by rfl⟩) R18857
theorem R12579 : Reach 12579 := rs (se 1 (by rfl) ⟨9434, by rfl⟩) R18869
theorem R12581 : Reach 12581 := rs (se 4 (by rfl) ⟨1179, by rfl⟩) R2359
theorem R12587 : Reach 12587 := rs (se 1 (by rfl) ⟨9440, by rfl⟩) R18881
theorem R12593 : Reach 12593 := rs (se 2 (by rfl) ⟨4722, by rfl⟩) R9445
theorem R12595 : Reach 12595 := rs (se 1 (by rfl) ⟨9446, by rfl⟩) R18893
theorem R12597 : Reach 12597 := rs (se 5 (by rfl) ⟨590, by rfl⟩) R1181
theorem R12599 : Reach 12599 := rs (se 1 (by rfl) ⟨9449, by rfl⟩) R18899
theorem R12603 : Reach 12603 := rs (se 1 (by rfl) ⟨9452, by rfl⟩) R18905
theorem R12605 : Reach 12605 := rs (se 3 (by rfl) ⟨2363, by rfl⟩) R4727
theorem R12609 : Reach 12609 := rs (se 2 (by rfl) ⟨4728, by rfl⟩) R9457
theorem R12611 : Reach 12611 := rs (se 1 (by rfl) ⟨9458, by rfl⟩) R18917
theorem R12613 : Reach 12613 := rs (se 4 (by rfl) ⟨1182, by rfl⟩) R2365
theorem R12615 : Reach 12615 := rs (se 1 (by rfl) ⟨9461, by rfl⟩) R18923
theorem R12617 : Reach 12617 := rs (se 2 (by rfl) ⟨4731, by rfl⟩) R9463
theorem R12619 : Reach 12619 := rs (se 1 (by rfl) ⟨9464, by rfl⟩) R18929
theorem R12631 : Reach 12631 := rs (se 1 (by rfl) ⟨9473, by rfl⟩) R18947
theorem R12633 : Reach 12633 := rs (se 2 (by rfl) ⟨4737, by rfl⟩) R9475
theorem R12635 : Reach 12635 := rs (se 1 (by rfl) ⟨9476, by rfl⟩) R18953
theorem R12649 : Reach 12649 := rs (se 2 (by rfl) ⟨4743, by rfl⟩) R9487
theorem R12651 : Reach 12651 := rs (se 1 (by rfl) ⟨9488, by rfl⟩) R18977
theorem R12733 : Reach 12733 := rs (se 3 (by rfl) ⟨2387, by rfl⟩) R4775
theorem R12813 : Reach 12813 := rs (se 3 (by rfl) ⟨2402, by rfl⟩) R4805
theorem R12817 : Reach 12817 := rs (se 2 (by rfl) ⟨4806, by rfl⟩) R9613
theorem R12821 : Reach 12821 := rs (se 6 (by rfl) ⟨300, by rfl⟩) R601
theorem R12865 : Reach 12865 := rs (se 2 (by rfl) ⟨4824, by rfl⟩) R9649
theorem R12899 : Reach 12899 := rs (se 1 (by rfl) ⟨9674, by rfl⟩) R19349
theorem R12901 : Reach 12901 := rs (se 4 (by rfl) ⟨1209, by rfl⟩) R2419
theorem R13007 : Reach 13007 := rs (se 1 (by rfl) ⟨9755, by rfl⟩) R19511
theorem R111527 : Reach 111527 := rs (se 1 (by rfl) ⟨83645, by rfl⟩) R167291
theorem R13537 : Reach 13537 := rs (se 2 (by rfl) ⟨5076, by rfl⟩) R10153
theorem R13589 : Reach 13589 := rs (se 6 (by rfl) ⟨318, by rfl⟩) R637
theorem R13613 : Reach 13613 := rs (se 3 (by rfl) ⟨2552, by rfl⟩) R5105
theorem R13621 : Reach 13621 := rs (se 5 (by rfl) ⟨638, by rfl⟩) R1277
theorem R13679 : Reach 13679 := rs (se 1 (by rfl) ⟨10259, by rfl⟩) R20519
theorem R13721 : Reach 13721 := rs (se 2 (by rfl) ⟨5145, by rfl⟩) R10291
theorem R13799 : Reach 13799 := rs (se 1 (by rfl) ⟨10349, by rfl⟩) R20699
theorem R13819 : Reach 13819 := rs (se 1 (by rfl) ⟨10364, by rfl⟩) R20729
theorem R13927 : Reach 13927 := rs (se 1 (by rfl) ⟨10445, by rfl⟩) R20891
theorem R14089 : Reach 14089 := rs (se 2 (by rfl) ⟨5283, by rfl⟩) R10567
theorem R14993 : Reach 14993 := rs (se 2 (by rfl) ⟨5622, by rfl⟩) R11245
theorem R14995 : Reach 14995 := rs (se 1 (by rfl) ⟨11246, by rfl⟩) R22493
theorem R15005 : Reach 15005 := rs (se 3 (by rfl) ⟨2813, by rfl⟩) R5627
theorem R15023 : Reach 15023 := rs (se 1 (by rfl) ⟨11267, by rfl⟩) R22535
theorem R15035 : Reach 15035 := rs (se 1 (by rfl) ⟨11276, by rfl⟩) R22553
theorem R15059 : Reach 15059 := rs (se 1 (by rfl) ⟨11294, by rfl⟩) R22589
theorem R48593 : Reach 48593 := rs (se 2 (by rfl) ⟨18222, by rfl⟩) R36445
theorem R48707 : Reach 48707 := rs (se 1 (by rfl) ⟨36530, by rfl⟩) R73061
theorem R49565 : Reach 49565 := rs (se 3 (by rfl) ⟨9293, by rfl⟩) R18587
theorem R49571 : Reach 49571 := rs (se 1 (by rfl) ⟨37178, by rfl⟩) R74357
theorem R49709 : Reach 49709 := rs (se 3 (by rfl) ⟨9320, by rfl⟩) R18641
theorem R49891 : Reach 49891 := rs (se 1 (by rfl) ⟨37418, by rfl⟩) R74837
theorem R50105 : Reach 50105 := rs (se 2 (by rfl) ⟨18789, by rfl⟩) R37579
theorem R50165 : Reach 50165 := rs (se 5 (by rfl) ⟨2351, by rfl⟩) R4703
theorem R50233 : Reach 50233 := rs (se 2 (by rfl) ⟨18837, by rfl⟩) R37675
theorem R50381 : Reach 50381 := rs (se 3 (by rfl) ⟨9446, by rfl⟩) R18893
theorem R50483 : Reach 50483 := rs (se 1 (by rfl) ⟨37862, by rfl⟩) R75725
theorem R51641 : Reach 51641 := rs (se 2 (by rfl) ⟨19365, by rfl⟩) R38731
theorem R52591 : Reach 52591 := rs (se 1 (by rfl) ⟨39443, by rfl⟩) R78887
theorem R54883 : Reach 54883 := rs (se 1 (by rfl) ⟨41162, by rfl⟩) R82325
theorem R55727 : Reach 55727 := rs (se 1 (by rfl) ⟨41795, by rfl⟩) R83591
theorem R56699 : Reach 56699 := rs (se 1 (by rfl) ⟨42524, by rfl⟩) R85049
theorem R24293 : Reach 24293 := rs (se 4 (by rfl) ⟨2277, by rfl⟩) R4555
theorem R24335 : Reach 24335 := rs (se 1 (by rfl) ⟨18251, by rfl⟩) R36503
theorem R24353 : Reach 24353 := rs (se 2 (by rfl) ⟨9132, by rfl⟩) R18265
theorem R24391 : Reach 24391 := rs (se 1 (by rfl) ⟨18293, by rfl⟩) R36587
theorem R24407 : Reach 24407 := rs (se 1 (by rfl) ⟨18305, by rfl⟩) R36611
theorem R24725 : Reach 24725 := rs (se 6 (by rfl) ⟨579, by rfl⟩) R1159
theorem R24749 : Reach 24749 := rs (se 3 (by rfl) ⟨4640, by rfl⟩) R9281
theorem R24779 : Reach 24779 := rs (se 1 (by rfl) ⟨18584, by rfl⟩) R37169
theorem R24785 : Reach 24785 := rs (se 2 (by rfl) ⟨9294, by rfl⟩) R18589
theorem R24857 : Reach 24857 := rs (se 2 (by rfl) ⟨9321, by rfl⟩) R18643
theorem R24983 : Reach 24983 := rs (se 1 (by rfl) ⟨18737, by rfl⟩) R37475
theorem R25069 : Reach 25069 := rs (se 3 (by rfl) ⟨4700, by rfl⟩) R9401
theorem R25091 : Reach 25091 := rs (se 1 (by rfl) ⟨18818, by rfl⟩) R37637
theorem R25127 : Reach 25127 := rs (se 1 (by rfl) ⟨18845, by rfl⟩) R37691
theorem R25163 : Reach 25163 := rs (se 1 (by rfl) ⟨18872, by rfl⟩) R37745
theorem R25211 : Reach 25211 := rs (se 1 (by rfl) ⟨18908, by rfl⟩) R37817
theorem R25217 : Reach 25217 := rs (se 2 (by rfl) ⟨9456, by rfl⟩) R18913
theorem R25219 : Reach 25219 := rs (se 1 (by rfl) ⟨18914, by rfl⟩) R37829
theorem R25231 : Reach 25231 := rs (se 1 (by rfl) ⟨18923, by rfl⟩) R37847
theorem R25235 : Reach 25235 := rs (se 1 (by rfl) ⟨18926, by rfl⟩) R37853
theorem R25265 : Reach 25265 := rs (se 2 (by rfl) ⟨9474, by rfl⟩) R18949
theorem R25271 : Reach 25271 := rs (se 1 (by rfl) ⟨18953, by rfl⟩) R37907
theorem R25469 : Reach 25469 := rs (se 3 (by rfl) ⟨4775, by rfl⟩) R9551
theorem R25793 : Reach 25793 := rs (se 2 (by rfl) ⟨9672, by rfl⟩) R19345
theorem R25895 : Reach 25895 := rs (se 1 (by rfl) ⟨19421, by rfl⟩) R38843
theorem R26297 : Reach 26297 := rs (se 2 (by rfl) ⟨9861, by rfl⟩) R19723
theorem R27017 : Reach 27017 := rs (se 2 (by rfl) ⟨10131, by rfl⟩) R20263
theorem R27359 : Reach 27359 := rs (se 1 (by rfl) ⟨20519, by rfl⟩) R41039
theorem R27623 : Reach 27623 := rs (se 1 (by rfl) ⟨20717, by rfl⟩) R41435
theorem R29987 : Reach 29987 := rs (se 1 (by rfl) ⟨22490, by rfl⟩) R44981
theorem R30023 : Reach 30023 := rs (se 1 (by rfl) ⟨22517, by rfl⟩) R45035
theorem R30041 : Reach 30041 := rs (se 2 (by rfl) ⟨11265, by rfl⟩) R22531
theorem R30071 : Reach 30071 := rs (se 1 (by rfl) ⟨22553, by rfl⟩) R45107
theorem R194885 : Reach 194885 := rs (se 4 (by rfl) ⟨18270, by rfl⟩) R36541
theorem R98005 : Reach 98005 := rs (se 7 (by rfl) ⟨1148, by rfl⟩) R2297
theorem R33043 : Reach 33043 := rs (se 1 (by rfl) ⟨24782, by rfl⟩) R49565
theorem R33047 : Reach 33047 := rs (se 1 (by rfl) ⟨24785, by rfl⟩) R49571
theorem R283 : Reach 283 := rs (se 1 (by rfl) ⟨212, by rfl⟩) R425
theorem R33139 : Reach 33139 := rs (se 1 (by rfl) ⟨24854, by rfl⟩) R49709
theorem R505 : Reach 505 := rs (se 2 (by rfl) ⟨189, by rfl⟩) R379
theorem R511 : Reach 511 := rs (se 1 (by rfl) ⟨383, by rfl⟩) R767
theorem R519 : Reach 519 := rs (se 1 (by rfl) ⟨389, by rfl⟩) R779
theorem R33293 : Reach 33293 := rs (se 3 (by rfl) ⟨6242, by rfl⟩) R12485
theorem R567 : Reach 567 := rs (se 1 (by rfl) ⟨425, by rfl⟩) R851
theorem R33425 : Reach 33425 := rs (se 2 (by rfl) ⟨12534, by rfl⟩) R25069
theorem R33443 : Reach 33443 := rs (se 1 (by rfl) ⟨25082, by rfl⟩) R50165
theorem R33587 : Reach 33587 := rs (se 1 (by rfl) ⟨25190, by rfl⟩) R50381
theorem R33625 : Reach 33625 := rs (se 2 (by rfl) ⟨12609, by rfl⟩) R25219
theorem R131939 : Reach 131939 := rs (se 1 (by rfl) ⟨98954, by rfl⟩) R197909
theorem R33641 : Reach 33641 := rs (se 2 (by rfl) ⟨12615, by rfl⟩) R25231
theorem R33655 : Reach 33655 := rs (se 1 (by rfl) ⟨25241, by rfl⟩) R50483
theorem R66521 : Reach 66521 := rs (se 2 (by rfl) ⟨24945, by rfl⟩) R49891
theorem R1011 : Reach 1011 := rs (se 1 (by rfl) ⟨758, by rfl⟩) R1517
theorem R1019 : Reach 1019 := rs (se 1 (by rfl) ⟨764, by rfl⟩) R1529
theorem R1023 : Reach 1023 := rs (se 1 (by rfl) ⟨767, by rfl⟩) R1535
theorem R1039 : Reach 1039 := rs (se 1 (by rfl) ⟨779, by rfl⟩) R1559
theorem R66581 : Reach 66581 := rs (se 6 (by rfl) ⟨1560, by rfl⟩) R3121
theorem R1049 : Reach 1049 := rs (se 2 (by rfl) ⟨393, by rfl⟩) R787
theorem R1067 : Reach 1067 := rs (se 1 (by rfl) ⟨800, by rfl⟩) R1601
theorem R1133 : Reach 1133 := rs (se 3 (by rfl) ⟨212, by rfl⟩) R425
theorem R1135 : Reach 1135 := rs (se 1 (by rfl) ⟨851, by rfl⟩) R1703
theorem R66703 : Reach 66703 := rs (se 1 (by rfl) ⟨50027, by rfl⟩) R100055
theorem R66977 : Reach 66977 := rs (se 2 (by rfl) ⟨25116, by rfl⟩) R50233
theorem R34397 : Reach 34397 := rs (se 3 (by rfl) ⟨6449, by rfl⟩) R12899
theorem R34427 : Reach 34427 := rs (se 1 (by rfl) ⟨25820, by rfl⟩) R51641
theorem R67229 : Reach 67229 := rs (se 3 (by rfl) ⟨12605, by rfl⟩) R25211
theorem R132977 : Reach 132977 := rs (se 2 (by rfl) ⟨49866, by rfl⟩) R99733
theorem R133015 : Reach 133015 := rs (se 1 (by rfl) ⟨99761, by rfl⟩) R199523
theorem R2021 : Reach 2021 := rs (se 4 (by rfl) ⟨189, by rfl⟩) R379
theorem R2031 : Reach 2031 := rs (se 1 (by rfl) ⟨1523, by rfl⟩) R3047
theorem R2039 : Reach 2039 := rs (se 1 (by rfl) ⟨1529, by rfl⟩) R3059
theorem R2041 : Reach 2041 := rs (se 2 (by rfl) ⟨765, by rfl⟩) R1531
theorem R2045 : Reach 2045 := rs (se 3 (by rfl) ⟨383, by rfl⟩) R767
theorem R2077 : Reach 2077 := rs (se 3 (by rfl) ⟨389, by rfl⟩) R779
theorem R2081 : Reach 2081 := rs (se 2 (by rfl) ⟨780, by rfl⟩) R1561
theorem R2089 : Reach 2089 := rs (se 2 (by rfl) ⟨783, by rfl⟩) R1567
theorem R2097 : Reach 2097 := rs (se 2 (by rfl) ⟨786, by rfl⟩) R1573
theorem R2099 : Reach 2099 := rs (se 1 (by rfl) ⟨1574, by rfl⟩) R3149
theorem R2135 : Reach 2135 := rs (se 1 (by rfl) ⟨1601, by rfl⟩) R3203
theorem R2137 : Reach 2137 := rs (se 2 (by rfl) ⟨801, by rfl⟩) R1603
theorem R133271 : Reach 133271 := rs (se 1 (by rfl) ⟨99953, by rfl⟩) R199907
theorem R2265 : Reach 2265 := rs (se 2 (by rfl) ⟨849, by rfl⟩) R1699
theorem R2269 : Reach 2269 := rs (se 3 (by rfl) ⟨425, by rfl⟩) R851
theorem R2271 : Reach 2271 := rs (se 1 (by rfl) ⟨1703, by rfl⟩) R3407
theorem R35045 : Reach 35045 := rs (se 4 (by rfl) ⟨3285, by rfl⟩) R6571
theorem R2503 : Reach 2503 := rs (se 1 (by rfl) ⟨1877, by rfl⟩) R3755
theorem R133613 : Reach 133613 := rs (se 3 (by rfl) ⟨25052, by rfl⟩) R50105
theorem R68789 : Reach 68789 := rs (se 5 (by rfl) ⟨3224, by rfl⟩) R6449
theorem R36341 : Reach 36341 := rs (se 5 (by rfl) ⟨1703, by rfl⟩) R3407
theorem R4045 : Reach 4045 := rs (se 3 (by rfl) ⟨758, by rfl⟩) R1517
theorem R4049 : Reach 4049 := rs (se 2 (by rfl) ⟨1518, by rfl⟩) R3037
theorem R4059 : Reach 4059 := rs (se 1 (by rfl) ⟨3044, by rfl⟩) R6089
theorem R4063 : Reach 4063 := rs (se 1 (by rfl) ⟨3047, by rfl⟩) R6095
theorem R4077 : Reach 4077 := rs (se 3 (by rfl) ⟨764, by rfl⟩) R1529
theorem R4079 : Reach 4079 := rs (se 1 (by rfl) ⟨3059, by rfl⟩) R6119
theorem R4083 : Reach 4083 := rs (se 1 (by rfl) ⟨3062, by rfl⟩) R6125
theorem R4089 : Reach 4089 := rs (se 2 (by rfl) ⟨1533, by rfl⟩) R3067
theorem R4093 : Reach 4093 := rs (se 3 (by rfl) ⟨767, by rfl⟩) R1535
theorem R4121 : Reach 4121 := rs (se 2 (by rfl) ⟨1545, by rfl⟩) R3091
theorem R4143 : Reach 4143 := rs (se 1 (by rfl) ⟨3107, by rfl⟩) R6215
theorem R4153 : Reach 4153 := rs (se 2 (by rfl) ⟨1557, by rfl⟩) R3115
theorem R4155 : Reach 4155 := rs (se 1 (by rfl) ⟨3116, by rfl⟩) R6233
theorem R4157 : Reach 4157 := rs (se 3 (by rfl) ⟨779, by rfl⟩) R1559
theorem R4161 : Reach 4161 := rs (se 2 (by rfl) ⟨1560, by rfl⟩) R3121
theorem R4163 : Reach 4163 := rs (se 1 (by rfl) ⟨3122, by rfl⟩) R6245
theorem R4179 : Reach 4179 := rs (se 1 (by rfl) ⟨3134, by rfl⟩) R6269
theorem R4187 : Reach 4187 := rs (se 1 (by rfl) ⟨3140, by rfl⟩) R6281
theorem R4193 : Reach 4193 := rs (se 2 (by rfl) ⟨1572, by rfl⟩) R3145
theorem R4195 : Reach 4195 := rs (se 1 (by rfl) ⟨3146, by rfl⟩) R6293
theorem R4197 : Reach 4197 := rs (se 4 (by rfl) ⟨393, by rfl⟩) R787
theorem R4199 : Reach 4199 := rs (se 1 (by rfl) ⟨3149, by rfl⟩) R6299
theorem R4201 : Reach 4201 := rs (se 2 (by rfl) ⟨1575, by rfl⟩) R3151
theorem R4203 : Reach 4203 := rs (se 1 (by rfl) ⟨3152, by rfl⟩) R6305
theorem R4269 : Reach 4269 := rs (se 3 (by rfl) ⟨800, by rfl⟩) R1601
theorem R4273 : Reach 4273 := rs (se 2 (by rfl) ⟨1602, by rfl⟩) R3205
theorem R4275 : Reach 4275 := rs (se 1 (by rfl) ⟨3206, by rfl⟩) R6413
theorem R4299 : Reach 4299 := rs (se 1 (by rfl) ⟨3224, by rfl⟩) R6449
theorem R4335 : Reach 4335 := rs (se 1 (by rfl) ⟨3251, by rfl⟩) R6503
theorem R37151 : Reach 37151 := rs (se 1 (by rfl) ⟨27863, by rfl⟩) R55727
theorem R4529 : Reach 4529 := rs (se 2 (by rfl) ⟨1698, by rfl⟩) R3397
theorem R4531 : Reach 4531 := rs (se 1 (by rfl) ⟨3398, by rfl⟩) R6797
theorem R4533 : Reach 4533 := rs (se 5 (by rfl) ⟨212, by rfl⟩) R425
theorem R4537 : Reach 4537 := rs (se 2 (by rfl) ⟨1701, by rfl⟩) R3403
theorem R4541 : Reach 4541 := rs (se 3 (by rfl) ⟨851, by rfl⟩) R1703
theorem R70121 : Reach 70121 := rs (se 2 (by rfl) ⟨26295, by rfl⟩) R52591
theorem R5001 : Reach 5001 := rs (se 2 (by rfl) ⟨1875, by rfl⟩) R3751
theorem R5007 : Reach 5007 := rs (se 1 (by rfl) ⟨3755, by rfl⟩) R7511
theorem R5019 : Reach 5019 := rs (se 1 (by rfl) ⟨3764, by rfl⟩) R7529
theorem R37799 : Reach 37799 := rs (se 1 (by rfl) ⟨28349, by rfl⟩) R56699
theorem R40013 : Reach 40013 := rs (se 3 (by rfl) ⟨7502, by rfl⟩) R15005
theorem R40061 : Reach 40061 := rs (se 3 (by rfl) ⟨7511, by rfl⟩) R15023
theorem R8085 : Reach 8085 := rs (se 6 (by rfl) ⟨189, by rfl⟩) R379
theorem R8097 : Reach 8097 := rs (se 2 (by rfl) ⟨3036, by rfl⟩) R6073
theorem R8099 : Reach 8099 := rs (se 1 (by rfl) ⟨6074, by rfl⟩) R12149
theorem R8107 : Reach 8107 := rs (se 1 (by rfl) ⟨6080, by rfl⟩) R12161
theorem R8111 : Reach 8111 := rs (se 1 (by rfl) ⟨6083, by rfl⟩) R12167
theorem R8119 : Reach 8119 := rs (se 1 (by rfl) ⟨6089, by rfl⟩) R12179
theorem R8125 : Reach 8125 := rs (se 3 (by rfl) ⟨1523, by rfl⟩) R3047
theorem R8135 : Reach 8135 := rs (se 1 (by rfl) ⟨6101, by rfl⟩) R12203
theorem R8157 : Reach 8157 := rs (se 3 (by rfl) ⟨1529, by rfl⟩) R3059
theorem R8159 : Reach 8159 := rs (se 1 (by rfl) ⟨6119, by rfl⟩) R12239
theorem R8165 : Reach 8165 := rs (se 4 (by rfl) ⟨765, by rfl⟩) R1531
theorem R8169 : Reach 8169 := rs (se 2 (by rfl) ⟨3063, by rfl⟩) R6127
theorem R8179 : Reach 8179 := rs (se 1 (by rfl) ⟨6134, by rfl⟩) R12269
theorem R8181 : Reach 8181 := rs (se 5 (by rfl) ⟨383, by rfl⟩) R767
theorem R8241 : Reach 8241 := rs (se 2 (by rfl) ⟨3090, by rfl⟩) R6181
theorem R8243 : Reach 8243 := rs (se 1 (by rfl) ⟨6182, by rfl⟩) R12365
theorem R8249 : Reach 8249 := rs (se 2 (by rfl) ⟨3093, by rfl⟩) R6187
theorem R8251 : Reach 8251 := rs (se 1 (by rfl) ⟨6188, by rfl⟩) R12377
theorem R8287 : Reach 8287 := rs (se 1 (by rfl) ⟨6215, by rfl⟩) R12431
theorem R8307 : Reach 8307 := rs (se 1 (by rfl) ⟨6230, by rfl⟩) R12461
theorem R8309 : Reach 8309 := rs (se 5 (by rfl) ⟨389, by rfl⟩) R779
theorem R8311 : Reach 8311 := rs (se 1 (by rfl) ⟨6233, by rfl⟩) R12467
theorem R8323 : Reach 8323 := rs (se 1 (by rfl) ⟨6242, by rfl⟩) R12485
theorem R8325 : Reach 8325 := rs (se 4 (by rfl) ⟨780, by rfl⟩) R1561
theorem R8327 : Reach 8327 := rs (se 1 (by rfl) ⟨6245, by rfl⟩) R12491
theorem R8347 : Reach 8347 := rs (se 1 (by rfl) ⟨6260, by rfl⟩) R12521
theorem R8357 : Reach 8357 := rs (se 4 (by rfl) ⟨783, by rfl⟩) R1567
theorem R8363 : Reach 8363 := rs (se 1 (by rfl) ⟨6272, by rfl⟩) R12545
theorem R8375 : Reach 8375 := rs (se 1 (by rfl) ⟨6281, by rfl⟩) R12563
theorem R8385 : Reach 8385 := rs (se 2 (by rfl) ⟨3144, by rfl⟩) R6289
theorem R8387 : Reach 8387 := rs (se 1 (by rfl) ⟨6290, by rfl⟩) R12581
theorem R8389 : Reach 8389 := rs (se 4 (by rfl) ⟨786, by rfl⟩) R1573
theorem R8391 : Reach 8391 := rs (se 1 (by rfl) ⟨6293, by rfl⟩) R12587
theorem R8395 : Reach 8395 := rs (se 1 (by rfl) ⟨6296, by rfl⟩) R12593
theorem R8397 : Reach 8397 := rs (se 3 (by rfl) ⟨1574, by rfl⟩) R3149
theorem R8399 : Reach 8399 := rs (se 1 (by rfl) ⟨6299, by rfl⟩) R12599
theorem R8401 : Reach 8401 := rs (se 2 (by rfl) ⟨3150, by rfl⟩) R6301
theorem R8403 : Reach 8403 := rs (se 1 (by rfl) ⟨6302, by rfl⟩) R12605
theorem R8407 : Reach 8407 := rs (se 1 (by rfl) ⟨6305, by rfl⟩) R12611
theorem R8409 : Reach 8409 := rs (se 2 (by rfl) ⟨3153, by rfl⟩) R6307
theorem R8411 : Reach 8411 := rs (se 1 (by rfl) ⟨6308, by rfl⟩) R12617
theorem R8423 : Reach 8423 := rs (se 1 (by rfl) ⟨6317, by rfl⟩) R12635
theorem R8489 : Reach 8489 := rs (se 2 (by rfl) ⟨3183, by rfl⟩) R6367
theorem R8541 : Reach 8541 := rs (se 3 (by rfl) ⟨1601, by rfl⟩) R3203
theorem R8547 : Reach 8547 := rs (se 1 (by rfl) ⟨6410, by rfl⟩) R12821
theorem R8549 : Reach 8549 := rs (se 4 (by rfl) ⟨801, by rfl⟩) R1603
theorem R8577 : Reach 8577 := rs (se 2 (by rfl) ⟨3216, by rfl⟩) R6433
theorem R8599 : Reach 8599 := rs (se 1 (by rfl) ⟨6449, by rfl⟩) R12899
theorem R8601 : Reach 8601 := rs (se 2 (by rfl) ⟨3225, by rfl⟩) R6451
theorem R8671 : Reach 8671 := rs (se 1 (by rfl) ⟨6503, by rfl⟩) R13007
theorem R8761 : Reach 8761 := rs (se 2 (by rfl) ⟨3285, by rfl⟩) R6571
theorem R74351 : Reach 74351 := rs (se 1 (by rfl) ⟨55763, by rfl⟩) R111527
theorem R9059 : Reach 9059 := rs (se 1 (by rfl) ⟨6794, by rfl⟩) R13589
theorem R9061 : Reach 9061 := rs (se 4 (by rfl) ⟨849, by rfl⟩) R1699
theorem R9073 : Reach 9073 := rs (se 2 (by rfl) ⟨3402, by rfl⟩) R6805
theorem R9075 : Reach 9075 := rs (se 1 (by rfl) ⟨6806, by rfl⟩) R13613
theorem R9077 : Reach 9077 := rs (se 5 (by rfl) ⟨425, by rfl⟩) R851
theorem R9085 : Reach 9085 := rs (se 3 (by rfl) ⟨1703, by rfl⟩) R3407
theorem R9119 : Reach 9119 := rs (se 1 (by rfl) ⟨6839, by rfl⟩) R13679
theorem R9129 : Reach 9129 := rs (se 2 (by rfl) ⟨3423, by rfl⟩) R6847
theorem R9145 : Reach 9145 := rs (se 2 (by rfl) ⟨3429, by rfl⟩) R6859
theorem R9147 : Reach 9147 := rs (se 1 (by rfl) ⟨6860, by rfl⟩) R13721
theorem R9199 : Reach 9199 := rs (se 1 (by rfl) ⟨6899, by rfl⟩) R13799
theorem R9995 : Reach 9995 := rs (se 1 (by rfl) ⟨7496, by rfl⟩) R14993
theorem R10003 : Reach 10003 := rs (se 1 (by rfl) ⟨7502, by rfl⟩) R15005
theorem R10013 : Reach 10013 := rs (se 3 (by rfl) ⟨1877, by rfl⟩) R3755
theorem R10015 : Reach 10015 := rs (se 1 (by rfl) ⟨7511, by rfl⟩) R15023
theorem R10023 : Reach 10023 := rs (se 1 (by rfl) ⟨7517, by rfl⟩) R15035
theorem R10039 : Reach 10039 := rs (se 1 (by rfl) ⟨7529, by rfl⟩) R15059
theorem R10041 : Reach 10041 := rs (se 2 (by rfl) ⟨3765, by rfl⟩) R7531
theorem R80189 : Reach 80189 := rs (se 3 (by rfl) ⟨15035, by rfl⟩) R30071
theorem R16181 : Reach 16181 := rs (se 5 (by rfl) ⟨758, by rfl⟩) R1517
theorem R16193 : Reach 16193 := rs (se 2 (by rfl) ⟨6072, by rfl⟩) R12145
theorem R16195 : Reach 16195 := rs (se 1 (by rfl) ⟨12146, by rfl⟩) R24293
theorem R16217 : Reach 16217 := rs (se 2 (by rfl) ⟨6081, by rfl⟩) R12163
theorem R16223 : Reach 16223 := rs (se 1 (by rfl) ⟨12167, by rfl⟩) R24335
theorem R16235 : Reach 16235 := rs (se 1 (by rfl) ⟨12176, by rfl⟩) R24353
theorem R16253 : Reach 16253 := rs (se 3 (by rfl) ⟨3047, by rfl⟩) R6095
theorem R16271 : Reach 16271 := rs (se 1 (by rfl) ⟨12203, by rfl⟩) R24407
theorem R16309 : Reach 16309 := rs (se 5 (by rfl) ⟨764, by rfl⟩) R1529
theorem R16321 : Reach 16321 := rs (se 2 (by rfl) ⟨6120, by rfl⟩) R12241
theorem R16337 : Reach 16337 := rs (se 2 (by rfl) ⟨6126, by rfl⟩) R12253
theorem R16357 : Reach 16357 := rs (se 4 (by rfl) ⟨1533, by rfl⟩) R3067
theorem R16373 : Reach 16373 := rs (se 5 (by rfl) ⟨767, by rfl⟩) R1535
theorem R16483 : Reach 16483 := rs (se 1 (by rfl) ⟨12362, by rfl⟩) R24725
theorem R16499 : Reach 16499 := rs (se 1 (by rfl) ⟨12374, by rfl⟩) R24749
theorem R16519 : Reach 16519 := rs (se 1 (by rfl) ⟨12389, by rfl⟩) R24779
theorem R16523 : Reach 16523 := rs (se 1 (by rfl) ⟨12392, by rfl⟩) R24785
theorem R16571 : Reach 16571 := rs (se 1 (by rfl) ⟨12428, by rfl⟩) R24857
theorem R16613 : Reach 16613 := rs (se 4 (by rfl) ⟨1557, by rfl⟩) R3115
theorem R16625 : Reach 16625 := rs (se 2 (by rfl) ⟨6234, by rfl⟩) R12469
theorem R16645 : Reach 16645 := rs (se 4 (by rfl) ⟨1560, by rfl⟩) R3121
theorem R16655 : Reach 16655 := rs (se 1 (by rfl) ⟨12491, by rfl⟩) R24983
theorem R16721 : Reach 16721 := rs (se 2 (by rfl) ⟨6270, by rfl⟩) R12541
theorem R16727 : Reach 16727 := rs (se 1 (by rfl) ⟨12545, by rfl⟩) R25091
theorem R16751 : Reach 16751 := rs (se 1 (by rfl) ⟨12563, by rfl⟩) R25127
theorem R16775 : Reach 16775 := rs (se 1 (by rfl) ⟨12581, by rfl⟩) R25163
theorem R16781 : Reach 16781 := rs (se 3 (by rfl) ⟨3146, by rfl⟩) R6293
theorem R16793 : Reach 16793 := rs (se 2 (by rfl) ⟨6297, by rfl⟩) R12595
theorem R16805 : Reach 16805 := rs (se 4 (by rfl) ⟨1575, by rfl⟩) R3151
theorem R16807 : Reach 16807 := rs (se 1 (by rfl) ⟨12605, by rfl⟩) R25211
theorem R16811 : Reach 16811 := rs (se 1 (by rfl) ⟨12608, by rfl⟩) R25217
theorem R16817 : Reach 16817 := rs (se 2 (by rfl) ⟨6306, by rfl⟩) R12613
theorem R16823 : Reach 16823 := rs (se 1 (by rfl) ⟨12617, by rfl⟩) R25235
theorem R16841 : Reach 16841 := rs (se 2 (by rfl) ⟨6315, by rfl⟩) R12631
theorem R16843 : Reach 16843 := rs (se 1 (by rfl) ⟨12632, by rfl⟩) R25265
theorem R16847 : Reach 16847 := rs (se 1 (by rfl) ⟨12635, by rfl⟩) R25271
theorem R16865 : Reach 16865 := rs (se 2 (by rfl) ⟨6324, by rfl⟩) R12649
theorem R16979 : Reach 16979 := rs (se 1 (by rfl) ⟨12734, by rfl⟩) R25469
theorem R17077 : Reach 17077 := rs (se 5 (by rfl) ⟨800, by rfl⟩) R1601
theorem R17093 : Reach 17093 := rs (se 4 (by rfl) ⟨1602, by rfl⟩) R3205
theorem R17101 : Reach 17101 := rs (se 3 (by rfl) ⟨3206, by rfl⟩) R6413
theorem R17153 : Reach 17153 := rs (se 2 (by rfl) ⟨6432, by rfl⟩) R12865
theorem R17195 : Reach 17195 := rs (se 1 (by rfl) ⟨12896, by rfl⟩) R25793
theorem R17197 : Reach 17197 := rs (se 3 (by rfl) ⟨3224, by rfl⟩) R6449
theorem R17201 : Reach 17201 := rs (se 2 (by rfl) ⟨6450, by rfl⟩) R12901
theorem R17263 : Reach 17263 := rs (se 1 (by rfl) ⟨12947, by rfl⟩) R25895
theorem R17531 : Reach 17531 := rs (se 1 (by rfl) ⟨13148, by rfl⟩) R26297
theorem R18011 : Reach 18011 := rs (se 1 (by rfl) ⟨13508, by rfl⟩) R27017
theorem R18049 : Reach 18049 := rs (se 2 (by rfl) ⟨6768, by rfl⟩) R13537
theorem R18125 : Reach 18125 := rs (se 3 (by rfl) ⟨3398, by rfl⟩) R6797
theorem R18149 : Reach 18149 := rs (se 4 (by rfl) ⟨1701, by rfl⟩) R3403
theorem R18161 : Reach 18161 := rs (se 2 (by rfl) ⟨6810, by rfl⟩) R13621
theorem R18239 : Reach 18239 := rs (se 1 (by rfl) ⟨13679, by rfl⟩) R27359
theorem R18415 : Reach 18415 := rs (se 1 (by rfl) ⟨13811, by rfl⟩) R27623
theorem R18425 : Reach 18425 := rs (se 2 (by rfl) ⟨6909, by rfl⟩) R13819
theorem R18569 : Reach 18569 := rs (se 2 (by rfl) ⟨6963, by rfl⟩) R13927
theorem R18785 : Reach 18785 := rs (se 2 (by rfl) ⟨7044, by rfl⟩) R14089
theorem R19991 : Reach 19991 := rs (se 1 (by rfl) ⟨14993, by rfl⟩) R29987
theorem R19993 : Reach 19993 := rs (se 2 (by rfl) ⟨7497, by rfl⟩) R14995
theorem R20015 : Reach 20015 := rs (se 1 (by rfl) ⟨15011, by rfl⟩) R30023
theorem R20027 : Reach 20027 := rs (se 1 (by rfl) ⟨15020, by rfl⟩) R30041
theorem R20047 : Reach 20047 := rs (se 1 (by rfl) ⟨15035, by rfl⟩) R30071
theorem R319697 : Reach 319697 := rs (se 2 (by rfl) ⟨119886, by rfl⟩) R239773
theorem R292709 : Reach 292709 := rs (se 4 (by rfl) ⟨27441, by rfl⟩) R54883
theorem R129923 : Reach 129923 := rs (se 1 (by rfl) ⟨97442, by rfl⟩) R194885
theorem R130673 : Reach 130673 := rs (se 2 (by rfl) ⟨49002, by rfl⟩) R98005
theorem R32395 : Reach 32395 := rs (se 1 (by rfl) ⟨24296, by rfl⟩) R48593
theorem R32471 : Reach 32471 := rs (se 1 (by rfl) ⟨24353, by rfl⟩) R48707
theorem R32501 : Reach 32501 := rs (se 5 (by rfl) ⟨1523, by rfl⟩) R3047
theorem R32521 : Reach 32521 := rs (se 2 (by rfl) ⟨12195, by rfl⟩) R24391
theorem R377 : Reach 377 := rs (se 2 (by rfl) ⟨141, by rfl⟩) R283
theorem R673 : Reach 673 := rs (se 2 (by rfl) ⟨252, by rfl⟩) R505
theorem R679 : Reach 679 := rs (se 1 (by rfl) ⟨509, by rfl⟩) R1019
theorem R681 : Reach 681 := rs (se 2 (by rfl) ⟨255, by rfl⟩) R511
theorem R699 : Reach 699 := rs (se 1 (by rfl) ⟨524, by rfl⟩) R1049
theorem R711 : Reach 711 := rs (se 1 (by rfl) ⟨533, by rfl⟩) R1067
theorem R755 : Reach 755 := rs (se 1 (by rfl) ⟨566, by rfl⟩) R1133
theorem R1347 : Reach 1347 := rs (se 1 (by rfl) ⟨1010, by rfl⟩) R2021
theorem R1359 : Reach 1359 := rs (se 1 (by rfl) ⟨1019, by rfl⟩) R2039
theorem R1363 : Reach 1363 := rs (se 1 (by rfl) ⟨1022, by rfl⟩) R2045
theorem R1385 : Reach 1385 := rs (se 2 (by rfl) ⟨519, by rfl⟩) R1039
theorem R1387 : Reach 1387 := rs (se 1 (by rfl) ⟨1040, by rfl⟩) R2081
theorem R1399 : Reach 1399 := rs (se 1 (by rfl) ⟨1049, by rfl⟩) R2099
theorem R1423 : Reach 1423 := rs (se 1 (by rfl) ⟨1067, by rfl⟩) R2135
theorem R1509 : Reach 1509 := rs (se 4 (by rfl) ⟨141, by rfl⟩) R283
theorem R1513 : Reach 1513 := rs (se 2 (by rfl) ⟨567, by rfl⟩) R1135
theorem R2693 : Reach 2693 := rs (se 4 (by rfl) ⟨252, by rfl⟩) R505
theorem R2699 : Reach 2699 := rs (se 1 (by rfl) ⟨2024, by rfl⟩) R4049
theorem R2717 : Reach 2717 := rs (se 3 (by rfl) ⟨509, by rfl⟩) R1019
theorem R2719 : Reach 2719 := rs (se 1 (by rfl) ⟨2039, by rfl⟩) R4079
theorem R2721 : Reach 2721 := rs (se 2 (by rfl) ⟨1020, by rfl⟩) R2041
theorem R2725 : Reach 2725 := rs (se 4 (by rfl) ⟨255, by rfl⟩) R511
theorem R2747 : Reach 2747 := rs (se 1 (by rfl) ⟨2060, by rfl⟩) R4121
theorem R2769 : Reach 2769 := rs (se 2 (by rfl) ⟨1038, by rfl⟩) R2077
theorem R2771 : Reach 2771 := rs (se 1 (by rfl) ⟨2078, by rfl⟩) R4157
theorem R2775 : Reach 2775 := rs (se 1 (by rfl) ⟨2081, by rfl⟩) R4163
theorem R2785 : Reach 2785 := rs (se 2 (by rfl) ⟨1044, by rfl⟩) R2089
theorem R2791 : Reach 2791 := rs (se 1 (by rfl) ⟨2093, by rfl⟩) R4187
theorem R2795 : Reach 2795 := rs (se 1 (by rfl) ⟨2096, by rfl⟩) R4193
theorem R2797 : Reach 2797 := rs (se 3 (by rfl) ⟨524, by rfl⟩) R1049
theorem R2799 : Reach 2799 := rs (se 1 (by rfl) ⟨2099, by rfl⟩) R4199
theorem R2845 : Reach 2845 := rs (se 3 (by rfl) ⟨533, by rfl⟩) R1067
theorem R2849 : Reach 2849 := rs (se 2 (by rfl) ⟨1068, by rfl⟩) R2137
theorem R3019 : Reach 3019 := rs (se 1 (by rfl) ⟨2264, by rfl⟩) R4529
theorem R3021 : Reach 3021 := rs (se 3 (by rfl) ⟨566, by rfl⟩) R1133
theorem R3025 : Reach 3025 := rs (se 2 (by rfl) ⟨1134, by rfl⟩) R2269
theorem R3027 : Reach 3027 := rs (se 1 (by rfl) ⟨2270, by rfl⟩) R4541
theorem R3337 : Reach 3337 := rs (se 2 (by rfl) ⟨1251, by rfl⟩) R2503
theorem R5389 : Reach 5389 := rs (se 3 (by rfl) ⟨1010, by rfl⟩) R2021
theorem R5393 : Reach 5393 := rs (se 2 (by rfl) ⟨2022, by rfl⟩) R4045
theorem R5399 : Reach 5399 := rs (se 1 (by rfl) ⟨4049, by rfl⟩) R8099
theorem R5407 : Reach 5407 := rs (se 1 (by rfl) ⟨4055, by rfl⟩) R8111
theorem R5417 : Reach 5417 := rs (se 2 (by rfl) ⟨2031, by rfl⟩) R4063
theorem R5423 : Reach 5423 := rs (se 1 (by rfl) ⟨4067, by rfl⟩) R8135
theorem R5437 : Reach 5437 := rs (se 3 (by rfl) ⟨1019, by rfl⟩) R2039
theorem R5439 : Reach 5439 := rs (se 1 (by rfl) ⟨4079, by rfl⟩) R8159
theorem R5443 : Reach 5443 := rs (se 1 (by rfl) ⟨4082, by rfl⟩) R8165
theorem R5453 : Reach 5453 := rs (se 3 (by rfl) ⟨1022, by rfl⟩) R2045
theorem R5457 : Reach 5457 := rs (se 2 (by rfl) ⟨2046, by rfl⟩) R4093
theorem R5495 : Reach 5495 := rs (se 1 (by rfl) ⟨4121, by rfl⟩) R8243
theorem R5499 : Reach 5499 := rs (se 1 (by rfl) ⟨4124, by rfl⟩) R8249
theorem R5537 : Reach 5537 := rs (se 2 (by rfl) ⟨2076, by rfl⟩) R4153
theorem R5539 : Reach 5539 := rs (se 1 (by rfl) ⟨4154, by rfl⟩) R8309
theorem R5541 : Reach 5541 := rs (se 4 (by rfl) ⟨519, by rfl⟩) R1039
theorem R5549 : Reach 5549 := rs (se 3 (by rfl) ⟨1040, by rfl⟩) R2081
theorem R5551 : Reach 5551 := rs (se 1 (by rfl) ⟨4163, by rfl⟩) R8327
theorem R5571 : Reach 5571 := rs (se 1 (by rfl) ⟨4178, by rfl⟩) R8357
theorem R5575 : Reach 5575 := rs (se 1 (by rfl) ⟨4181, by rfl⟩) R8363
theorem R5583 : Reach 5583 := rs (se 1 (by rfl) ⟨4187, by rfl⟩) R8375
theorem R5591 : Reach 5591 := rs (se 1 (by rfl) ⟨4193, by rfl⟩) R8387
theorem R5593 : Reach 5593 := rs (se 2 (by rfl) ⟨2097, by rfl⟩) R4195
theorem R5597 : Reach 5597 := rs (se 3 (by rfl) ⟨1049, by rfl⟩) R2099
theorem R5599 : Reach 5599 := rs (se 1 (by rfl) ⟨4199, by rfl⟩) R8399
theorem R5601 : Reach 5601 := rs (se 2 (by rfl) ⟨2100, by rfl⟩) R4201
theorem R5607 : Reach 5607 := rs (se 1 (by rfl) ⟨4205, by rfl⟩) R8411
theorem R5615 : Reach 5615 := rs (se 1 (by rfl) ⟨4211, by rfl⟩) R8423
theorem R5659 : Reach 5659 := rs (se 1 (by rfl) ⟨4244, by rfl⟩) R8489
theorem R5693 : Reach 5693 := rs (se 3 (by rfl) ⟨1067, by rfl⟩) R2135
theorem R5697 : Reach 5697 := rs (se 2 (by rfl) ⟨2136, by rfl⟩) R4273
theorem R5699 : Reach 5699 := rs (se 1 (by rfl) ⟨4274, by rfl⟩) R8549
theorem R6037 : Reach 6037 := rs (se 6 (by rfl) ⟨141, by rfl⟩) R283
theorem R6039 : Reach 6039 := rs (se 1 (by rfl) ⟨4529, by rfl⟩) R9059
theorem R6041 : Reach 6041 := rs (se 2 (by rfl) ⟨2265, by rfl⟩) R4531
theorem R6049 : Reach 6049 := rs (se 2 (by rfl) ⟨2268, by rfl⟩) R4537
theorem R6051 : Reach 6051 := rs (se 1 (by rfl) ⟨4538, by rfl⟩) R9077
theorem R6053 : Reach 6053 := rs (se 4 (by rfl) ⟨567, by rfl⟩) R1135
theorem R6079 : Reach 6079 := rs (se 1 (by rfl) ⟨4559, by rfl⟩) R9119
theorem R366869 : Reach 366869 := rs (se 6 (by rfl) ⟨8598, by rfl⟩) R17197
theorem R6663 : Reach 6663 := rs (se 1 (by rfl) ⟨4997, by rfl⟩) R9995
theorem R6675 : Reach 6675 := rs (se 1 (by rfl) ⟨5006, by rfl⟩) R10013
theorem R106829 : Reach 106829 := rs (se 3 (by rfl) ⟨20030, by rfl⟩) R40061
theorem R43193 : Reach 43193 := rs (se 2 (by rfl) ⟨16197, by rfl⟩) R32395
theorem R43361 : Reach 43361 := rs (se 2 (by rfl) ⟨16260, by rfl⟩) R32521
theorem R10773 : Reach 10773 := rs (se 6 (by rfl) ⟨252, by rfl⟩) R505
theorem R10787 : Reach 10787 := rs (se 1 (by rfl) ⟨8090, by rfl⟩) R16181
theorem R10795 : Reach 10795 := rs (se 1 (by rfl) ⟨8096, by rfl⟩) R16193
theorem R10797 : Reach 10797 := rs (se 3 (by rfl) ⟨2024, by rfl⟩) R4049
theorem R10809 : Reach 10809 := rs (se 2 (by rfl) ⟨4053, by rfl⟩) R8107
theorem R10811 : Reach 10811 := rs (se 1 (by rfl) ⟨8108, by rfl⟩) R16217
theorem R10815 : Reach 10815 := rs (se 1 (by rfl) ⟨8111, by rfl⟩) R16223
theorem R10823 : Reach 10823 := rs (se 1 (by rfl) ⟨8117, by rfl⟩) R16235
theorem R10825 : Reach 10825 := rs (se 2 (by rfl) ⟨4059, by rfl⟩) R8119
theorem R10833 : Reach 10833 := rs (se 2 (by rfl) ⟨4062, by rfl⟩) R8125
theorem R10835 : Reach 10835 := rs (se 1 (by rfl) ⟨8126, by rfl⟩) R16253
theorem R10847 : Reach 10847 := rs (se 1 (by rfl) ⟨8135, by rfl⟩) R16271
theorem R10869 : Reach 10869 := rs (se 5 (by rfl) ⟨509, by rfl⟩) R1019
theorem R10877 : Reach 10877 := rs (se 3 (by rfl) ⟨2039, by rfl⟩) R4079
theorem R10885 : Reach 10885 := rs (se 4 (by rfl) ⟨1020, by rfl⟩) R2041
theorem R10891 : Reach 10891 := rs (se 1 (by rfl) ⟨8168, by rfl⟩) R16337
theorem R10901 : Reach 10901 := rs (se 6 (by rfl) ⟨255, by rfl⟩) R511
theorem R10905 : Reach 10905 := rs (se 2 (by rfl) ⟨4089, by rfl⟩) R8179
theorem R10915 : Reach 10915 := rs (se 1 (by rfl) ⟨8186, by rfl⟩) R16373
theorem R10989 : Reach 10989 := rs (se 3 (by rfl) ⟨2060, by rfl⟩) R4121
theorem R10999 : Reach 10999 := rs (se 1 (by rfl) ⟨8249, by rfl⟩) R16499
theorem R11001 : Reach 11001 := rs (se 2 (by rfl) ⟨4125, by rfl⟩) R8251
theorem R11015 : Reach 11015 := rs (se 1 (by rfl) ⟨8261, by rfl⟩) R16523
theorem R11047 : Reach 11047 := rs (se 1 (by rfl) ⟨8285, by rfl⟩) R16571
theorem R11049 : Reach 11049 := rs (se 2 (by rfl) ⟨4143, by rfl⟩) R8287
theorem R11075 : Reach 11075 := rs (se 1 (by rfl) ⟨8306, by rfl⟩) R16613
theorem R11077 : Reach 11077 := rs (se 4 (by rfl) ⟨1038, by rfl⟩) R2077
theorem R11081 : Reach 11081 := rs (se 2 (by rfl) ⟨4155, by rfl⟩) R8311
theorem R11083 : Reach 11083 := rs (se 1 (by rfl) ⟨8312, by rfl⟩) R16625
theorem R11085 : Reach 11085 := rs (se 3 (by rfl) ⟨2078, by rfl⟩) R4157
theorem R11097 : Reach 11097 := rs (se 2 (by rfl) ⟨4161, by rfl⟩) R8323
theorem R11101 : Reach 11101 := rs (se 3 (by rfl) ⟨2081, by rfl⟩) R4163
theorem R11103 : Reach 11103 := rs (se 1 (by rfl) ⟨8327, by rfl⟩) R16655
theorem R11129 : Reach 11129 := rs (se 2 (by rfl) ⟨4173, by rfl⟩) R8347
theorem R11141 : Reach 11141 := rs (se 4 (by rfl) ⟨1044, by rfl⟩) R2089
theorem R11147 : Reach 11147 := rs (se 1 (by rfl) ⟨8360, by rfl⟩) R16721
theorem R11151 : Reach 11151 := rs (se 1 (by rfl) ⟨8363, by rfl⟩) R16727
theorem R11165 : Reach 11165 := rs (se 3 (by rfl) ⟨2093, by rfl⟩) R4187
theorem R11167 : Reach 11167 := rs (se 1 (by rfl) ⟨8375, by rfl⟩) R16751
theorem R11181 : Reach 11181 := rs (se 3 (by rfl) ⟨2096, by rfl⟩) R4193
theorem R11183 : Reach 11183 := rs (se 1 (by rfl) ⟨8387, by rfl⟩) R16775
theorem R11185 : Reach 11185 := rs (se 2 (by rfl) ⟨4194, by rfl⟩) R8389
theorem R11187 : Reach 11187 := rs (se 1 (by rfl) ⟨8390, by rfl⟩) R16781
theorem R11189 : Reach 11189 := rs (se 5 (by rfl) ⟨524, by rfl⟩) R1049
theorem R11193 : Reach 11193 := rs (se 2 (by rfl) ⟨4197, by rfl⟩) R8395
theorem R11195 : Reach 11195 := rs (se 1 (by rfl) ⟨8396, by rfl⟩) R16793
theorem R11197 : Reach 11197 := rs (se 3 (by rfl) ⟨2099, by rfl⟩) R4199
theorem R11201 : Reach 11201 := rs (se 2 (by rfl) ⟨4200, by rfl⟩) R8401
theorem R11203 : Reach 11203 := rs (se 1 (by rfl) ⟨8402, by rfl⟩) R16805
theorem R11207 : Reach 11207 := rs (se 1 (by rfl) ⟨8405, by rfl⟩) R16811
theorem R11209 : Reach 11209 := rs (se 2 (by rfl) ⟨4203, by rfl⟩) R8407
theorem R11211 : Reach 11211 := rs (se 1 (by rfl) ⟨8408, by rfl⟩) R16817
theorem R11215 : Reach 11215 := rs (se 1 (by rfl) ⟨8411, by rfl⟩) R16823
theorem R11227 : Reach 11227 := rs (se 1 (by rfl) ⟨8420, by rfl⟩) R16841
theorem R11231 : Reach 11231 := rs (se 1 (by rfl) ⟨8423, by rfl⟩) R16847
theorem R11243 : Reach 11243 := rs (se 1 (by rfl) ⟨8432, by rfl⟩) R16865
theorem R44057 : Reach 44057 := rs (se 2 (by rfl) ⟨16521, by rfl⟩) R33043
theorem R11319 : Reach 11319 := rs (se 1 (by rfl) ⟨8489, by rfl⟩) R16979
theorem R11381 : Reach 11381 := rs (se 5 (by rfl) ⟨533, by rfl⟩) R1067
theorem R11395 : Reach 11395 := rs (se 1 (by rfl) ⟨8546, by rfl⟩) R17093
theorem R11397 : Reach 11397 := rs (se 4 (by rfl) ⟨1068, by rfl⟩) R2137
theorem R44185 : Reach 44185 := rs (se 2 (by rfl) ⟨16569, by rfl⟩) R33139
theorem R11435 : Reach 11435 := rs (se 1 (by rfl) ⟨8576, by rfl⟩) R17153
theorem R11463 : Reach 11463 := rs (se 1 (by rfl) ⟨8597, by rfl⟩) R17195
theorem R11465 : Reach 11465 := rs (se 2 (by rfl) ⟨4299, by rfl⟩) R8599
theorem R11467 : Reach 11467 := rs (se 1 (by rfl) ⟨8600, by rfl⟩) R17201
theorem R11561 : Reach 11561 := rs (se 2 (by rfl) ⟨4335, by rfl⟩) R8671
theorem R44333 : Reach 44333 := rs (se 3 (by rfl) ⟨8312, by rfl⟩) R16625
theorem R44347 : Reach 44347 := rs (se 1 (by rfl) ⟨33260, by rfl⟩) R66521
theorem R44387 : Reach 44387 := rs (se 1 (by rfl) ⟨33290, by rfl⟩) R66581
theorem R11681 : Reach 11681 := rs (se 2 (by rfl) ⟨4380, by rfl⟩) R8761
theorem R11687 : Reach 11687 := rs (se 1 (by rfl) ⟨8765, by rfl⟩) R17531
theorem R44651 : Reach 44651 := rs (se 1 (by rfl) ⟨33488, by rfl⟩) R66977
theorem R12007 : Reach 12007 := rs (se 1 (by rfl) ⟨9005, by rfl⟩) R18011
theorem R44819 : Reach 44819 := rs (se 1 (by rfl) ⟨33614, by rfl⟩) R67229
theorem R44833 : Reach 44833 := rs (se 2 (by rfl) ⟨16812, by rfl⟩) R33625
theorem R12077 : Reach 12077 := rs (se 3 (by rfl) ⟨2264, by rfl⟩) R4529
theorem R12081 : Reach 12081 := rs (se 2 (by rfl) ⟨4530, by rfl⟩) R9061
theorem R12083 : Reach 12083 := rs (se 1 (by rfl) ⟨9062, by rfl⟩) R18125
theorem R12085 : Reach 12085 := rs (se 5 (by rfl) ⟨566, by rfl⟩) R1133
theorem R12097 : Reach 12097 := rs (se 2 (by rfl) ⟨4536, by rfl⟩) R9073
theorem R12099 : Reach 12099 := rs (se 1 (by rfl) ⟨9074, by rfl⟩) R18149
theorem R12101 : Reach 12101 := rs (se 4 (by rfl) ⟨1134, by rfl⟩) R2269
theorem R44873 : Reach 44873 := rs (se 2 (by rfl) ⟨16827, by rfl⟩) R33655
theorem R12107 : Reach 12107 := rs (se 1 (by rfl) ⟨9080, by rfl⟩) R18161
theorem R12109 : Reach 12109 := rs (se 3 (by rfl) ⟨2270, by rfl⟩) R4541
theorem R12113 : Reach 12113 := rs (se 2 (by rfl) ⟨4542, by rfl⟩) R9085
theorem R12159 : Reach 12159 := rs (se 1 (by rfl) ⟨9119, by rfl⟩) R18239
theorem R12193 : Reach 12193 := rs (se 2 (by rfl) ⟨4572, by rfl⟩) R9145
theorem R12265 : Reach 12265 := rs (se 2 (by rfl) ⟨4599, by rfl⟩) R9199
theorem R12283 : Reach 12283 := rs (se 1 (by rfl) ⟨9212, by rfl⟩) R18425
theorem R12379 : Reach 12379 := rs (se 1 (by rfl) ⟨9284, by rfl⟩) R18569
theorem R12523 : Reach 12523 := rs (se 1 (by rfl) ⟨9392, by rfl⟩) R18785
theorem R45859 : Reach 45859 := rs (se 1 (by rfl) ⟨34394, by rfl⟩) R68789
theorem R13327 : Reach 13327 := rs (se 1 (by rfl) ⟨9995, by rfl⟩) R19991
theorem R13337 : Reach 13337 := rs (se 2 (by rfl) ⟨5001, by rfl⟩) R10003
theorem R13343 : Reach 13343 := rs (se 1 (by rfl) ⟨10007, by rfl⟩) R20015
theorem R13349 : Reach 13349 := rs (se 4 (by rfl) ⟨1251, by rfl⟩) R2503
theorem R13351 : Reach 13351 := rs (se 1 (by rfl) ⟨10013, by rfl⟩) R20027
theorem R13385 : Reach 13385 := rs (se 2 (by rfl) ⟨5019, by rfl⟩) R10039
theorem R177353 : Reach 177353 := rs (se 2 (by rfl) ⟨66507, by rfl⟩) R133015
theorem R46747 : Reach 46747 := rs (se 1 (by rfl) ⟨35060, by rfl⟩) R70121
theorem R179333 : Reach 179333 := rs (se 4 (by rfl) ⟨16812, by rfl⟩) R33625
theorem R48397 : Reach 48397 := rs (se 3 (by rfl) ⟨9074, by rfl⟩) R18149
theorem R48437 : Reach 48437 := rs (se 5 (by rfl) ⟨2270, by rfl⟩) R4541
theorem R213131 : Reach 213131 := rs (se 1 (by rfl) ⟨159848, by rfl⟩) R319697
theorem R49517 : Reach 49517 := rs (se 3 (by rfl) ⟨9284, by rfl⟩) R18569
theorem R49567 : Reach 49567 := rs (se 1 (by rfl) ⟨37175, by rfl⟩) R74351
theorem R53459 : Reach 53459 := rs (se 1 (by rfl) ⟨40094, by rfl⟩) R80189
theorem R86615 : Reach 86615 := rs (se 1 (by rfl) ⟨64961, by rfl⟩) R129923
theorem R87115 : Reach 87115 := rs (se 1 (by rfl) ⟨65336, by rfl⟩) R130673
theorem R21593 : Reach 21593 := rs (se 2 (by rfl) ⟨8097, by rfl⟩) R16195
theorem R21647 : Reach 21647 := rs (se 1 (by rfl) ⟨16235, by rfl⟩) R32471
theorem R21667 : Reach 21667 := rs (se 1 (by rfl) ⟨16250, by rfl⟩) R32501
theorem R21745 : Reach 21745 := rs (se 2 (by rfl) ⟨8154, by rfl⟩) R16309
theorem R21761 : Reach 21761 := rs (se 2 (by rfl) ⟨8160, by rfl⟩) R16321
theorem R21809 : Reach 21809 := rs (se 2 (by rfl) ⟨8178, by rfl⟩) R16357
theorem R21829 : Reach 21829 := rs (se 4 (by rfl) ⟨2046, by rfl⟩) R4093
theorem R21977 : Reach 21977 := rs (se 2 (by rfl) ⟨8241, by rfl⟩) R16483
theorem R22025 : Reach 22025 := rs (se 2 (by rfl) ⟨8259, by rfl⟩) R16519
theorem R22031 : Reach 22031 := rs (se 1 (by rfl) ⟨16523, by rfl⟩) R33047
theorem R22157 : Reach 22157 := rs (se 3 (by rfl) ⟨4154, by rfl⟩) R8309
theorem R22193 : Reach 22193 := rs (se 2 (by rfl) ⟨8322, by rfl⟩) R16645
theorem R22195 : Reach 22195 := rs (se 1 (by rfl) ⟨16646, by rfl⟩) R33293
theorem R22283 : Reach 22283 := rs (se 1 (by rfl) ⟨16712, by rfl⟩) R33425
theorem R22285 : Reach 22285 := rs (se 3 (by rfl) ⟨4178, by rfl⟩) R8357
theorem R22295 : Reach 22295 := rs (se 1 (by rfl) ⟨16721, by rfl⟩) R33443
theorem R22301 : Reach 22301 := rs (se 3 (by rfl) ⟨4181, by rfl⟩) R8363
theorem R22333 : Reach 22333 := rs (se 3 (by rfl) ⟨4187, by rfl⟩) R8375
theorem R22373 : Reach 22373 := rs (se 4 (by rfl) ⟨2097, by rfl⟩) R4195
theorem R22391 : Reach 22391 := rs (se 1 (by rfl) ⟨16793, by rfl⟩) R33587
theorem R22409 : Reach 22409 := rs (se 2 (by rfl) ⟨8403, by rfl⟩) R16807
theorem R87959 : Reach 87959 := rs (se 1 (by rfl) ⟨65969, by rfl⟩) R131939
theorem R22427 : Reach 22427 := rs (se 1 (by rfl) ⟨16820, by rfl⟩) R33641
theorem R22457 : Reach 22457 := rs (se 2 (by rfl) ⟨8421, by rfl⟩) R16843
theorem R22769 : Reach 22769 := rs (se 2 (by rfl) ⟨8538, by rfl⟩) R17077
theorem R22801 : Reach 22801 := rs (se 2 (by rfl) ⟨8550, by rfl⟩) R17101
theorem R22931 : Reach 22931 := rs (se 1 (by rfl) ⟨17198, by rfl⟩) R34397
theorem R22951 : Reach 22951 := rs (se 1 (by rfl) ⟨17213, by rfl⟩) R34427
theorem R23017 : Reach 23017 := rs (se 2 (by rfl) ⟨8631, by rfl⟩) R17263
theorem R88651 : Reach 88651 := rs (se 1 (by rfl) ⟨66488, by rfl⟩) R132977
theorem R88847 : Reach 88847 := rs (se 1 (by rfl) ⟨66635, by rfl⟩) R133271
theorem R23363 : Reach 23363 := rs (se 1 (by rfl) ⟨17522, by rfl⟩) R35045
theorem R88937 : Reach 88937 := rs (se 2 (by rfl) ⟨33351, by rfl⟩) R66703
theorem R89075 : Reach 89075 := rs (se 1 (by rfl) ⟨66806, by rfl⟩) R133613
theorem R24065 : Reach 24065 := rs (se 2 (by rfl) ⟨9024, by rfl⟩) R18049
theorem R24227 : Reach 24227 := rs (se 1 (by rfl) ⟨18170, by rfl⟩) R36341
theorem R24317 : Reach 24317 := rs (se 3 (by rfl) ⟨4559, by rfl⟩) R9119
theorem R24553 : Reach 24553 := rs (se 2 (by rfl) ⟨9207, by rfl⟩) R18415
theorem R24767 : Reach 24767 := rs (se 1 (by rfl) ⟨18575, by rfl⟩) R37151
theorem R25199 : Reach 25199 := rs (se 1 (by rfl) ⟨18899, by rfl⟩) R37799
theorem R26657 : Reach 26657 := rs (se 2 (by rfl) ⟨9996, by rfl⟩) R19993
theorem R26675 : Reach 26675 := rs (se 1 (by rfl) ⟨20006, by rfl⟩) R40013
theorem R26729 : Reach 26729 := rs (se 2 (by rfl) ⟨10023, by rfl⟩) R20047
theorem R195139 : Reach 195139 := rs (se 1 (by rfl) ⟨146354, by rfl⟩) R292709
theorem R33011 : Reach 33011 := rs (se 1 (by rfl) ⟨24758, by rfl⟩) R49517
theorem R251 : Reach 251 := rs (se 1 (by rfl) ⟨188, by rfl⟩) R377
theorem R503 : Reach 503 := rs (se 1 (by rfl) ⟨377, by rfl⟩) R755
theorem R66089 : Reach 66089 := rs (se 2 (by rfl) ⟨24783, by rfl⟩) R49567
theorem R897 : Reach 897 := rs (se 2 (by rfl) ⟨336, by rfl⟩) R673
theorem R905 : Reach 905 := rs (se 2 (by rfl) ⟨339, by rfl⟩) R679
theorem R923 : Reach 923 := rs (se 1 (by rfl) ⟨692, by rfl⟩) R1385
theorem R1005 : Reach 1005 := rs (se 3 (by rfl) ⟨188, by rfl⟩) R377
theorem R1795 : Reach 1795 := rs (se 1 (by rfl) ⟨1346, by rfl⟩) R2693
theorem R1799 : Reach 1799 := rs (se 1 (by rfl) ⟨1349, by rfl⟩) R2699
theorem R1811 : Reach 1811 := rs (se 1 (by rfl) ⟨1358, by rfl⟩) R2717
theorem R1817 : Reach 1817 := rs (se 2 (by rfl) ⟨681, by rfl⟩) R1363
theorem R1831 : Reach 1831 := rs (se 1 (by rfl) ⟨1373, by rfl⟩) R2747
theorem R1847 : Reach 1847 := rs (se 1 (by rfl) ⟨1385, by rfl⟩) R2771
theorem R1849 : Reach 1849 := rs (se 2 (by rfl) ⟨693, by rfl⟩) R1387
theorem R1863 : Reach 1863 := rs (se 1 (by rfl) ⟨1397, by rfl⟩) R2795
theorem R1865 : Reach 1865 := rs (se 2 (by rfl) ⟨699, by rfl⟩) R1399
theorem R1897 : Reach 1897 := rs (se 2 (by rfl) ⟨711, by rfl⟩) R1423
theorem R1899 : Reach 1899 := rs (se 1 (by rfl) ⟨1424, by rfl⟩) R2849
theorem R2013 : Reach 2013 := rs (se 3 (by rfl) ⟨377, by rfl⟩) R755
theorem R2017 : Reach 2017 := rs (se 2 (by rfl) ⟨756, by rfl⟩) R1513
theorem R35639 : Reach 35639 := rs (se 1 (by rfl) ⟨26729, by rfl⟩) R53459
theorem R35693 : Reach 35693 := rs (se 3 (by rfl) ⟨6692, by rfl⟩) R13385
theorem R3589 : Reach 3589 := rs (se 4 (by rfl) ⟨336, by rfl⟩) R673
theorem R3595 : Reach 3595 := rs (se 1 (by rfl) ⟨2696, by rfl⟩) R5393
theorem R3599 : Reach 3599 := rs (se 1 (by rfl) ⟨2699, by rfl⟩) R5399
theorem R3611 : Reach 3611 := rs (se 1 (by rfl) ⟨2708, by rfl⟩) R5417
theorem R3615 : Reach 3615 := rs (se 1 (by rfl) ⟨2711, by rfl⟩) R5423
theorem R3621 : Reach 3621 := rs (se 4 (by rfl) ⟨339, by rfl⟩) R679
theorem R3625 : Reach 3625 := rs (se 2 (by rfl) ⟨1359, by rfl⟩) R2719
theorem R3633 : Reach 3633 := rs (se 2 (by rfl) ⟨1362, by rfl⟩) R2725
theorem R3635 : Reach 3635 := rs (se 1 (by rfl) ⟨2726, by rfl⟩) R5453
theorem R3663 : Reach 3663 := rs (se 1 (by rfl) ⟨2747, by rfl⟩) R5495
theorem R3691 : Reach 3691 := rs (se 1 (by rfl) ⟨2768, by rfl⟩) R5537
theorem R3693 : Reach 3693 := rs (se 3 (by rfl) ⟨692, by rfl⟩) R1385
theorem R3699 : Reach 3699 := rs (se 1 (by rfl) ⟨2774, by rfl⟩) R5549
theorem R3713 : Reach 3713 := rs (se 2 (by rfl) ⟨1392, by rfl⟩) R2785
theorem R3721 : Reach 3721 := rs (se 2 (by rfl) ⟨1395, by rfl⟩) R2791
theorem R3727 : Reach 3727 := rs (se 1 (by rfl) ⟨2795, by rfl⟩) R5591
theorem R3729 : Reach 3729 := rs (se 2 (by rfl) ⟨1398, by rfl⟩) R2797
theorem R3731 : Reach 3731 := rs (se 1 (by rfl) ⟨2798, by rfl⟩) R5597
theorem R3743 : Reach 3743 := rs (se 1 (by rfl) ⟨2807, by rfl⟩) R5615
theorem R3793 : Reach 3793 := rs (se 2 (by rfl) ⟨1422, by rfl⟩) R2845
theorem R3795 : Reach 3795 := rs (se 1 (by rfl) ⟨2846, by rfl⟩) R5693
theorem R3799 : Reach 3799 := rs (se 1 (by rfl) ⟨2849, by rfl⟩) R5699
theorem R4021 : Reach 4021 := rs (se 5 (by rfl) ⟨188, by rfl⟩) R377
theorem R4025 : Reach 4025 := rs (se 2 (by rfl) ⟨1509, by rfl⟩) R3019
theorem R4027 : Reach 4027 := rs (se 1 (by rfl) ⟨3020, by rfl⟩) R6041
theorem R4033 : Reach 4033 := rs (se 2 (by rfl) ⟨1512, by rfl⟩) R3025
theorem R4035 : Reach 4035 := rs (se 1 (by rfl) ⟨3026, by rfl⟩) R6053
theorem R4449 : Reach 4449 := rs (se 2 (by rfl) ⟨1668, by rfl⟩) R3337
theorem R71077 : Reach 71077 := rs (se 4 (by rfl) ⟨6663, by rfl⟩) R13327
theorem R71219 : Reach 71219 := rs (se 1 (by rfl) ⟨53414, by rfl⟩) R106829
theorem R7181 : Reach 7181 := rs (se 3 (by rfl) ⟨1346, by rfl⟩) R2693
theorem R7185 : Reach 7185 := rs (se 2 (by rfl) ⟨2694, by rfl⟩) R5389
theorem R7191 : Reach 7191 := rs (se 1 (by rfl) ⟨5393, by rfl⟩) R10787
theorem R7197 : Reach 7197 := rs (se 3 (by rfl) ⟨1349, by rfl⟩) R2699
theorem R7207 : Reach 7207 := rs (se 1 (by rfl) ⟨5405, by rfl⟩) R10811
theorem R7209 : Reach 7209 := rs (se 2 (by rfl) ⟨2703, by rfl⟩) R5407
theorem R7215 : Reach 7215 := rs (se 1 (by rfl) ⟨5411, by rfl⟩) R10823
theorem R7223 : Reach 7223 := rs (se 1 (by rfl) ⟨5417, by rfl⟩) R10835
theorem R7231 : Reach 7231 := rs (se 1 (by rfl) ⟨5423, by rfl⟩) R10847
theorem R7245 : Reach 7245 := rs (se 3 (by rfl) ⟨1358, by rfl⟩) R2717
theorem R7249 : Reach 7249 := rs (se 2 (by rfl) ⟨2718, by rfl⟩) R5437
theorem R7251 : Reach 7251 := rs (se 1 (by rfl) ⟨5438, by rfl⟩) R10877
theorem R7257 : Reach 7257 := rs (se 2 (by rfl) ⟨2721, by rfl⟩) R5443
theorem R7267 : Reach 7267 := rs (se 1 (by rfl) ⟨5450, by rfl⟩) R10901
theorem R7269 : Reach 7269 := rs (se 4 (by rfl) ⟨681, by rfl⟩) R1363
theorem R7325 : Reach 7325 := rs (se 3 (by rfl) ⟨1373, by rfl⟩) R2747
theorem R7343 : Reach 7343 := rs (se 1 (by rfl) ⟨5507, by rfl⟩) R11015
theorem R7383 : Reach 7383 := rs (se 1 (by rfl) ⟨5537, by rfl⟩) R11075
theorem R7385 : Reach 7385 := rs (se 2 (by rfl) ⟨2769, by rfl⟩) R5539
theorem R7387 : Reach 7387 := rs (se 1 (by rfl) ⟨5540, by rfl⟩) R11081
theorem R7389 : Reach 7389 := rs (se 3 (by rfl) ⟨1385, by rfl⟩) R2771
theorem R7397 : Reach 7397 := rs (se 4 (by rfl) ⟨693, by rfl⟩) R1387
theorem R7401 : Reach 7401 := rs (se 2 (by rfl) ⟨2775, by rfl⟩) R5551
theorem R7419 : Reach 7419 := rs (se 1 (by rfl) ⟨5564, by rfl⟩) R11129
theorem R7427 : Reach 7427 := rs (se 1 (by rfl) ⟨5570, by rfl⟩) R11141
theorem R7431 : Reach 7431 := rs (se 1 (by rfl) ⟨5573, by rfl⟩) R11147
theorem R7433 : Reach 7433 := rs (se 2 (by rfl) ⟨2787, by rfl⟩) R5575
theorem R7443 : Reach 7443 := rs (se 1 (by rfl) ⟨5582, by rfl⟩) R11165
theorem R7453 : Reach 7453 := rs (se 3 (by rfl) ⟨1397, by rfl⟩) R2795
theorem R7455 : Reach 7455 := rs (se 1 (by rfl) ⟨5591, by rfl⟩) R11183
theorem R7457 : Reach 7457 := rs (se 2 (by rfl) ⟨2796, by rfl⟩) R5593
theorem R7459 : Reach 7459 := rs (se 1 (by rfl) ⟨5594, by rfl⟩) R11189
theorem R7461 : Reach 7461 := rs (se 4 (by rfl) ⟨699, by rfl⟩) R1399
theorem R7463 : Reach 7463 := rs (se 1 (by rfl) ⟨5597, by rfl⟩) R11195
theorem R7465 : Reach 7465 := rs (se 2 (by rfl) ⟨2799, by rfl⟩) R5599
theorem R7467 : Reach 7467 := rs (se 1 (by rfl) ⟨5600, by rfl⟩) R11201
theorem R7471 : Reach 7471 := rs (se 1 (by rfl) ⟨5603, by rfl⟩) R11207
theorem R7487 : Reach 7487 := rs (se 1 (by rfl) ⟨5615, by rfl⟩) R11231
theorem R7495 : Reach 7495 := rs (se 1 (by rfl) ⟨5621, by rfl⟩) R11243
theorem R7545 : Reach 7545 := rs (se 2 (by rfl) ⟨2829, by rfl⟩) R5659
theorem R7587 : Reach 7587 := rs (se 1 (by rfl) ⟨5690, by rfl⟩) R11381
theorem R7589 : Reach 7589 := rs (se 4 (by rfl) ⟨711, by rfl⟩) R1423
theorem R7597 : Reach 7597 := rs (se 3 (by rfl) ⟨1424, by rfl⟩) R2849
theorem R7623 : Reach 7623 := rs (se 1 (by rfl) ⟨5717, by rfl⟩) R11435
theorem R7643 : Reach 7643 := rs (se 1 (by rfl) ⟨5732, by rfl⟩) R11465
theorem R7707 : Reach 7707 := rs (se 1 (by rfl) ⟨5780, by rfl⟩) R11561
theorem R7787 : Reach 7787 := rs (se 1 (by rfl) ⟨5840, by rfl⟩) R11681
theorem R7791 : Reach 7791 := rs (se 1 (by rfl) ⟨5843, by rfl⟩) R11687
theorem R8049 : Reach 8049 := rs (se 2 (by rfl) ⟨3018, by rfl⟩) R6037
theorem R8051 : Reach 8051 := rs (se 1 (by rfl) ⟨6038, by rfl⟩) R12077
theorem R8053 : Reach 8053 := rs (se 5 (by rfl) ⟨377, by rfl⟩) R755
theorem R8055 : Reach 8055 := rs (se 1 (by rfl) ⟨6041, by rfl⟩) R12083
theorem R8065 : Reach 8065 := rs (se 2 (by rfl) ⟨3024, by rfl⟩) R6049
theorem R8067 : Reach 8067 := rs (se 1 (by rfl) ⟨6050, by rfl⟩) R12101
theorem R8069 : Reach 8069 := rs (se 4 (by rfl) ⟨756, by rfl⟩) R1513
theorem R8071 : Reach 8071 := rs (se 1 (by rfl) ⟨6053, by rfl⟩) R12107
theorem R8075 : Reach 8075 := rs (se 1 (by rfl) ⟨6056, by rfl⟩) R12113
theorem R8105 : Reach 8105 := rs (se 2 (by rfl) ⟨3039, by rfl⟩) R6079
theorem R8891 : Reach 8891 := rs (se 1 (by rfl) ⟨6668, by rfl⟩) R13337
theorem R8895 : Reach 8895 := rs (se 1 (by rfl) ⟨6671, by rfl⟩) R13343
theorem R8899 : Reach 8899 := rs (se 1 (by rfl) ⟨6674, by rfl⟩) R13349
theorem R8923 : Reach 8923 := rs (se 1 (by rfl) ⟨6692, by rfl⟩) R13385
theorem R142087 : Reach 142087 := rs (se 1 (by rfl) ⟨106565, by rfl⟩) R213131
theorem R14357 : Reach 14357 := rs (se 6 (by rfl) ⟨336, by rfl⟩) R673
theorem R14381 : Reach 14381 := rs (se 3 (by rfl) ⟨2696, by rfl⟩) R5393
theorem R14393 : Reach 14393 := rs (se 2 (by rfl) ⟨5397, by rfl⟩) R10795
theorem R14395 : Reach 14395 := rs (se 1 (by rfl) ⟨10796, by rfl⟩) R21593
theorem R14431 : Reach 14431 := rs (se 1 (by rfl) ⟨10823, by rfl⟩) R21647
theorem R14485 : Reach 14485 := rs (se 6 (by rfl) ⟨339, by rfl⟩) R679
theorem R14501 : Reach 14501 := rs (se 4 (by rfl) ⟨1359, by rfl⟩) R2719
theorem R14507 : Reach 14507 := rs (se 1 (by rfl) ⟨10880, by rfl⟩) R21761
theorem R14513 : Reach 14513 := rs (se 2 (by rfl) ⟨5442, by rfl⟩) R10885
theorem R14539 : Reach 14539 := rs (se 1 (by rfl) ⟨10904, by rfl⟩) R21809
theorem R14651 : Reach 14651 := rs (se 1 (by rfl) ⟨10988, by rfl⟩) R21977
theorem R14683 : Reach 14683 := rs (se 1 (by rfl) ⟨11012, by rfl⟩) R22025
theorem R14687 : Reach 14687 := rs (se 1 (by rfl) ⟨11015, by rfl⟩) R22031
theorem R14729 : Reach 14729 := rs (se 2 (by rfl) ⟨5523, by rfl⟩) R11047
theorem R14765 : Reach 14765 := rs (se 3 (by rfl) ⟨2768, by rfl⟩) R5537
theorem R14771 : Reach 14771 := rs (se 1 (by rfl) ⟨11078, by rfl⟩) R22157
theorem R14777 : Reach 14777 := rs (se 2 (by rfl) ⟨5541, by rfl⟩) R11083
theorem R14795 : Reach 14795 := rs (se 1 (by rfl) ⟨11096, by rfl⟩) R22193
theorem R14801 : Reach 14801 := rs (se 2 (by rfl) ⟨5550, by rfl⟩) R11101
theorem R14855 : Reach 14855 := rs (se 1 (by rfl) ⟨11141, by rfl⟩) R22283
theorem R14863 : Reach 14863 := rs (se 1 (by rfl) ⟨11147, by rfl⟩) R22295
theorem R14867 : Reach 14867 := rs (se 1 (by rfl) ⟨11150, by rfl⟩) R22301
theorem R14885 : Reach 14885 := rs (se 4 (by rfl) ⟨1395, by rfl⟩) R2791
theorem R14909 : Reach 14909 := rs (se 3 (by rfl) ⟨2795, by rfl⟩) R5591
theorem R14915 : Reach 14915 := rs (se 1 (by rfl) ⟨11186, by rfl⟩) R22373
theorem R14917 : Reach 14917 := rs (se 4 (by rfl) ⟨1398, by rfl⟩) R2797
theorem R14927 : Reach 14927 := rs (se 1 (by rfl) ⟨11195, by rfl⟩) R22391
theorem R14939 : Reach 14939 := rs (se 1 (by rfl) ⟨11204, by rfl⟩) R22409
theorem R14945 : Reach 14945 := rs (se 2 (by rfl) ⟨5604, by rfl⟩) R11209
theorem R14951 : Reach 14951 := rs (se 1 (by rfl) ⟨11213, by rfl⟩) R22427
theorem R14969 : Reach 14969 := rs (se 2 (by rfl) ⟨5613, by rfl⟩) R11227
theorem R14971 : Reach 14971 := rs (se 1 (by rfl) ⟨11228, by rfl⟩) R22457
theorem R15173 : Reach 15173 := rs (se 4 (by rfl) ⟨1422, by rfl⟩) R2845
theorem R15179 : Reach 15179 := rs (se 1 (by rfl) ⟨11384, by rfl⟩) R22769
theorem R15197 : Reach 15197 := rs (se 3 (by rfl) ⟨2849, by rfl⟩) R5699
theorem R244579 : Reach 244579 := rs (se 1 (by rfl) ⟨183434, by rfl⟩) R366869
theorem R15287 : Reach 15287 := rs (se 1 (by rfl) ⟨11465, by rfl⟩) R22931
theorem R15575 : Reach 15575 := rs (se 1 (by rfl) ⟨11681, by rfl⟩) R23363
theorem R16043 : Reach 16043 := rs (se 1 (by rfl) ⟨12032, by rfl⟩) R24065
theorem R16085 : Reach 16085 := rs (se 7 (by rfl) ⟨188, by rfl⟩) R377
theorem R16109 : Reach 16109 := rs (se 3 (by rfl) ⟨3020, by rfl⟩) R6041
theorem R16129 : Reach 16129 := rs (se 2 (by rfl) ⟨6048, by rfl⟩) R12097
theorem R16133 : Reach 16133 := rs (se 4 (by rfl) ⟨1512, by rfl⟩) R3025
theorem R16141 : Reach 16141 := rs (se 3 (by rfl) ⟨3026, by rfl⟩) R6053
theorem R16145 : Reach 16145 := rs (se 2 (by rfl) ⟨6054, by rfl⟩) R12109
theorem R16151 : Reach 16151 := rs (se 1 (by rfl) ⟨12113, by rfl⟩) R24227
theorem R16211 : Reach 16211 := rs (se 1 (by rfl) ⟨12158, by rfl⟩) R24317
theorem R16505 : Reach 16505 := rs (se 2 (by rfl) ⟨6189, by rfl⟩) R12379
theorem R16511 : Reach 16511 := rs (se 1 (by rfl) ⟨12383, by rfl⟩) R24767
theorem R16697 : Reach 16697 := rs (se 2 (by rfl) ⟨6261, by rfl⟩) R12523
theorem R16799 : Reach 16799 := rs (se 1 (by rfl) ⟨12599, by rfl⟩) R25199
theorem R115181 : Reach 115181 := rs (se 3 (by rfl) ⟨21596, by rfl⟩) R43193
theorem R17771 : Reach 17771 := rs (se 1 (by rfl) ⟨13328, by rfl⟩) R26657
theorem R17783 : Reach 17783 := rs (se 1 (by rfl) ⟨13337, by rfl⟩) R26675
theorem R17801 : Reach 17801 := rs (se 2 (by rfl) ⟨6675, by rfl⟩) R13351
theorem R17819 : Reach 17819 := rs (se 1 (by rfl) ⟨13364, by rfl⟩) R26729
theorem R116153 : Reach 116153 := rs (se 2 (by rfl) ⟨43557, by rfl⟩) R87115
theorem R118201 : Reach 118201 := rs (se 2 (by rfl) ⟨44325, by rfl⟩) R88651
theorem R118235 : Reach 118235 := rs (se 1 (by rfl) ⟨88676, by rfl⟩) R177353
theorem R249317 : Reach 249317 := rs (se 4 (by rfl) ⟨23373, by rfl⟩) R46747
theorem R119555 : Reach 119555 := rs (se 1 (by rfl) ⟨89666, by rfl⟩) R179333
theorem R57743 : Reach 57743 := rs (se 1 (by rfl) ⟨43307, by rfl⟩) R86615
theorem R57781 : Reach 57781 := rs (se 5 (by rfl) ⟨2708, by rfl⟩) R5417
theorem R58157 : Reach 58157 := rs (se 3 (by rfl) ⟨10904, by rfl⟩) R21809
theorem R58639 : Reach 58639 := rs (se 1 (by rfl) ⟨43979, by rfl⟩) R87959
theorem R58913 : Reach 58913 := rs (se 2 (by rfl) ⟨22092, by rfl⟩) R44185
theorem R59129 : Reach 59129 := rs (se 2 (by rfl) ⟨22173, by rfl⟩) R44347
theorem R59231 : Reach 59231 := rs (se 1 (by rfl) ⟨44423, by rfl⟩) R88847
theorem R59291 : Reach 59291 := rs (se 1 (by rfl) ⟨44468, by rfl⟩) R88937
theorem R59383 : Reach 59383 := rs (se 1 (by rfl) ⟨44537, by rfl⟩) R89075
theorem R59413 : Reach 59413 := rs (se 6 (by rfl) ⟨1392, by rfl⟩) R2785
theorem R59453 : Reach 59453 := rs (se 3 (by rfl) ⟨11147, by rfl⟩) R22295
theorem R59717 : Reach 59717 := rs (se 4 (by rfl) ⟨5598, by rfl⟩) R11197
theorem R59777 : Reach 59777 := rs (se 2 (by rfl) ⟨22416, by rfl⟩) R44833
theorem R61145 : Reach 61145 := rs (se 2 (by rfl) ⟨22929, by rfl⟩) R45859
theorem R28795 : Reach 28795 := rs (se 1 (by rfl) ⟨21596, by rfl⟩) R43193
theorem R28889 : Reach 28889 := rs (se 2 (by rfl) ⟨10833, by rfl⟩) R21667
theorem R28907 : Reach 28907 := rs (se 1 (by rfl) ⟨21680, by rfl⟩) R43361
theorem R28993 : Reach 28993 := rs (se 2 (by rfl) ⟨10872, by rfl⟩) R21745
theorem R28997 : Reach 28997 := rs (se 4 (by rfl) ⟨2718, by rfl⟩) R5437
theorem R29069 : Reach 29069 := rs (se 3 (by rfl) ⟨5450, by rfl⟩) R10901
theorem R29105 : Reach 29105 := rs (se 2 (by rfl) ⟨10914, by rfl⟩) R21829
theorem R29371 : Reach 29371 := rs (se 1 (by rfl) ⟨22028, by rfl⟩) R44057
theorem R29555 : Reach 29555 := rs (se 1 (by rfl) ⟨22166, by rfl⟩) R44333
theorem R62329 : Reach 62329 := rs (se 2 (by rfl) ⟨23373, by rfl⟩) R46747
theorem R29591 : Reach 29591 := rs (se 1 (by rfl) ⟨22193, by rfl⟩) R44387
theorem R29593 : Reach 29593 := rs (se 2 (by rfl) ⟨11097, by rfl⟩) R22195
theorem R29605 : Reach 29605 := rs (se 4 (by rfl) ⟨2775, by rfl⟩) R5551
theorem R29713 : Reach 29713 := rs (se 2 (by rfl) ⟨11142, by rfl⟩) R22285
theorem R29767 : Reach 29767 := rs (se 1 (by rfl) ⟨22325, by rfl⟩) R44651
theorem R29777 : Reach 29777 := rs (se 2 (by rfl) ⟨11166, by rfl⟩) R22333
theorem R29813 : Reach 29813 := rs (se 5 (by rfl) ⟨1397, by rfl⟩) R2795
theorem R29821 : Reach 29821 := rs (se 3 (by rfl) ⟨5591, by rfl⟩) R11183
theorem R29861 : Reach 29861 := rs (se 4 (by rfl) ⟨2799, by rfl⟩) R5599
theorem R29879 : Reach 29879 := rs (se 1 (by rfl) ⟨22409, by rfl⟩) R44819
theorem R29915 : Reach 29915 := rs (se 1 (by rfl) ⟨22436, by rfl⟩) R44873
theorem R30401 : Reach 30401 := rs (se 2 (by rfl) ⟨11400, by rfl⟩) R22801
theorem R30601 : Reach 30601 := rs (se 2 (by rfl) ⟨11475, by rfl⟩) R22951
theorem R30689 : Reach 30689 := rs (se 2 (by rfl) ⟨11508, by rfl⟩) R23017
theorem R260185 : Reach 260185 := rs (se 2 (by rfl) ⟨97569, by rfl⟩) R195139
theorem R64529 : Reach 64529 := rs (se 2 (by rfl) ⟨24198, by rfl⟩) R48397
theorem R32197 : Reach 32197 := rs (se 4 (by rfl) ⟨3018, by rfl⟩) R6037
theorem R32213 : Reach 32213 := rs (se 7 (by rfl) ⟨377, by rfl⟩) R755
theorem R32291 : Reach 32291 := rs (se 1 (by rfl) ⟨24218, by rfl⟩) R48437
theorem R32737 : Reach 32737 := rs (se 2 (by rfl) ⟨12276, by rfl⟩) R24553
theorem R167 : Reach 167 := rs (se 1 (by rfl) ⟨125, by rfl⟩) R251
theorem R335 : Reach 335 := rs (se 1 (by rfl) ⟨251, by rfl⟩) R503
theorem R603 : Reach 603 := rs (se 1 (by rfl) ⟨452, by rfl⟩) R905
theorem R615 : Reach 615 := rs (se 1 (by rfl) ⟨461, by rfl⟩) R923
theorem R669 : Reach 669 := rs (se 3 (by rfl) ⟨125, by rfl⟩) R251
theorem R1199 : Reach 1199 := rs (se 1 (by rfl) ⟨899, by rfl⟩) R1799
theorem R1207 : Reach 1207 := rs (se 1 (by rfl) ⟨905, by rfl⟩) R1811
theorem R1211 : Reach 1211 := rs (se 1 (by rfl) ⟨908, by rfl⟩) R1817
theorem R1231 : Reach 1231 := rs (se 1 (by rfl) ⟨923, by rfl⟩) R1847
theorem R1243 : Reach 1243 := rs (se 1 (by rfl) ⟨932, by rfl⟩) R1865
theorem R1341 : Reach 1341 := rs (se 3 (by rfl) ⟨251, by rfl⟩) R503
theorem R166211 : Reach 166211 := rs (se 1 (by rfl) ⟨124658, by rfl⟩) R249317
theorem R2393 : Reach 2393 := rs (se 2 (by rfl) ⟨897, by rfl⟩) R1795
theorem R2399 : Reach 2399 := rs (se 1 (by rfl) ⟨1799, by rfl⟩) R3599
theorem R2407 : Reach 2407 := rs (se 1 (by rfl) ⟨1805, by rfl⟩) R3611
theorem R2413 : Reach 2413 := rs (se 3 (by rfl) ⟨452, by rfl⟩) R905
theorem R2423 : Reach 2423 := rs (se 1 (by rfl) ⟨1817, by rfl⟩) R3635
theorem R2441 : Reach 2441 := rs (se 2 (by rfl) ⟨915, by rfl⟩) R1831
theorem R2461 : Reach 2461 := rs (se 3 (by rfl) ⟨461, by rfl⟩) R923
theorem R2465 : Reach 2465 := rs (se 2 (by rfl) ⟨924, by rfl⟩) R1849
theorem R2475 : Reach 2475 := rs (se 1 (by rfl) ⟨1856, by rfl⟩) R3713
theorem R2487 : Reach 2487 := rs (se 1 (by rfl) ⟨1865, by rfl⟩) R3731
theorem R2495 : Reach 2495 := rs (se 1 (by rfl) ⟨1871, by rfl⟩) R3743
theorem R2529 : Reach 2529 := rs (se 2 (by rfl) ⟨948, by rfl⟩) R1897
theorem R2677 : Reach 2677 := rs (se 5 (by rfl) ⟨125, by rfl⟩) R251
theorem R2683 : Reach 2683 := rs (se 1 (by rfl) ⟨2012, by rfl⟩) R4025
theorem R2689 : Reach 2689 := rs (se 2 (by rfl) ⟨1008, by rfl⟩) R2017
theorem R4785 : Reach 4785 := rs (se 2 (by rfl) ⟨1794, by rfl⟩) R3589
theorem R4787 : Reach 4787 := rs (se 1 (by rfl) ⟨3590, by rfl⟩) R7181
theorem R4793 : Reach 4793 := rs (se 2 (by rfl) ⟨1797, by rfl⟩) R3595
theorem R4797 : Reach 4797 := rs (se 3 (by rfl) ⟨899, by rfl⟩) R1799
theorem R4815 : Reach 4815 := rs (se 1 (by rfl) ⟨3611, by rfl⟩) R7223
theorem R4829 : Reach 4829 := rs (se 3 (by rfl) ⟨905, by rfl⟩) R1811
theorem R4833 : Reach 4833 := rs (se 2 (by rfl) ⟨1812, by rfl⟩) R3625
theorem R4845 : Reach 4845 := rs (se 3 (by rfl) ⟨908, by rfl⟩) R1817
theorem R4883 : Reach 4883 := rs (se 1 (by rfl) ⟨3662, by rfl⟩) R7325
theorem R4895 : Reach 4895 := rs (se 1 (by rfl) ⟨3671, by rfl⟩) R7343
theorem R4921 : Reach 4921 := rs (se 2 (by rfl) ⟨1845, by rfl⟩) R3691
theorem R4923 : Reach 4923 := rs (se 1 (by rfl) ⟨3692, by rfl⟩) R7385
theorem R4925 : Reach 4925 := rs (se 3 (by rfl) ⟨923, by rfl⟩) R1847
theorem R4931 : Reach 4931 := rs (se 1 (by rfl) ⟨3698, by rfl⟩) R7397
theorem R4951 : Reach 4951 := rs (se 1 (by rfl) ⟨3713, by rfl⟩) R7427
theorem R4955 : Reach 4955 := rs (se 1 (by rfl) ⟨3716, by rfl⟩) R7433
theorem R4961 : Reach 4961 := rs (se 2 (by rfl) ⟨1860, by rfl⟩) R3721
theorem R4969 : Reach 4969 := rs (se 2 (by rfl) ⟨1863, by rfl⟩) R3727
theorem R4971 : Reach 4971 := rs (se 1 (by rfl) ⟨3728, by rfl⟩) R7457
theorem R4973 : Reach 4973 := rs (se 3 (by rfl) ⟨932, by rfl⟩) R1865
theorem R4975 : Reach 4975 := rs (se 1 (by rfl) ⟨3731, by rfl⟩) R7463
theorem R4991 : Reach 4991 := rs (se 1 (by rfl) ⟨3743, by rfl⟩) R7487
theorem R5057 : Reach 5057 := rs (se 2 (by rfl) ⟨1896, by rfl⟩) R3793
theorem R5059 : Reach 5059 := rs (se 1 (by rfl) ⟨3794, by rfl⟩) R7589
theorem R5065 : Reach 5065 := rs (se 2 (by rfl) ⟨1899, by rfl⟩) R3799
theorem R5095 : Reach 5095 := rs (se 1 (by rfl) ⟨3821, by rfl⟩) R7643
theorem R5191 : Reach 5191 := rs (se 1 (by rfl) ⟨3893, by rfl⟩) R7787
theorem R5361 : Reach 5361 := rs (se 2 (by rfl) ⟨2010, by rfl⟩) R4021
theorem R5365 : Reach 5365 := rs (se 5 (by rfl) ⟨251, by rfl⟩) R503
theorem R5367 : Reach 5367 := rs (se 1 (by rfl) ⟨4025, by rfl⟩) R8051
theorem R5369 : Reach 5369 := rs (se 2 (by rfl) ⟨2013, by rfl⟩) R4027
theorem R5377 : Reach 5377 := rs (se 2 (by rfl) ⟨2016, by rfl⟩) R4033
theorem R5379 : Reach 5379 := rs (se 1 (by rfl) ⟨4034, by rfl⟩) R8069
theorem R5383 : Reach 5383 := rs (se 1 (by rfl) ⟨4037, by rfl⟩) R8075
theorem R5403 : Reach 5403 := rs (se 1 (by rfl) ⟨4052, by rfl⟩) R8105
theorem R38285 : Reach 38285 := rs (se 3 (by rfl) ⟨7178, by rfl⟩) R14357
theorem R38393 : Reach 38393 := rs (se 2 (by rfl) ⟨14397, by rfl⟩) R28795
theorem R38495 : Reach 38495 := rs (se 1 (by rfl) ⟨28871, by rfl⟩) R57743
theorem R38657 : Reach 38657 := rs (se 2 (by rfl) ⟨14496, by rfl⟩) R28993
theorem R5927 : Reach 5927 := rs (se 1 (by rfl) ⟨4445, by rfl⟩) R8891
theorem R38771 : Reach 38771 := rs (se 1 (by rfl) ⟨29078, by rfl⟩) R58157
theorem R39161 : Reach 39161 := rs (se 2 (by rfl) ⟨14685, by rfl⟩) R29371
theorem R39275 : Reach 39275 := rs (se 1 (by rfl) ⟨29456, by rfl⟩) R58913
theorem R39419 : Reach 39419 := rs (se 1 (by rfl) ⟨29564, by rfl⟩) R59129
theorem R39457 : Reach 39457 := rs (se 2 (by rfl) ⟨14796, by rfl⟩) R29593
theorem R39469 : Reach 39469 := rs (se 3 (by rfl) ⟨7400, by rfl⟩) R14801
theorem R39473 : Reach 39473 := rs (se 2 (by rfl) ⟨14802, by rfl⟩) R29605
theorem R39487 : Reach 39487 := rs (se 1 (by rfl) ⟨29615, by rfl⟩) R59231
theorem R39527 : Reach 39527 := rs (se 1 (by rfl) ⟨29645, by rfl⟩) R59291
theorem R39617 : Reach 39617 := rs (se 2 (by rfl) ⟨14856, by rfl⟩) R29713
theorem R39635 : Reach 39635 := rs (se 1 (by rfl) ⟨29726, by rfl⟩) R59453
theorem R39689 : Reach 39689 := rs (se 2 (by rfl) ⟨14883, by rfl⟩) R29767
theorem R39761 : Reach 39761 := rs (se 2 (by rfl) ⟨14910, by rfl⟩) R29821
theorem R39797 : Reach 39797 := rs (se 5 (by rfl) ⟨1865, by rfl⟩) R3731
theorem R39811 : Reach 39811 := rs (se 1 (by rfl) ⟨29858, by rfl⟩) R59717
theorem R39845 : Reach 39845 := rs (se 4 (by rfl) ⟨3735, by rfl⟩) R7471
theorem R39851 : Reach 39851 := rs (se 1 (by rfl) ⟨29888, by rfl⟩) R59777
theorem R39973 : Reach 39973 := rs (se 4 (by rfl) ⟨3747, by rfl⟩) R7495
theorem R40763 : Reach 40763 := rs (se 1 (by rfl) ⟨30572, by rfl⟩) R61145
theorem R9571 : Reach 9571 := rs (se 1 (by rfl) ⟨7178, by rfl⟩) R14357
theorem R9573 : Reach 9573 := rs (se 4 (by rfl) ⟨897, by rfl⟩) R1795
theorem R9587 : Reach 9587 := rs (se 1 (by rfl) ⟨7190, by rfl⟩) R14381
theorem R9595 : Reach 9595 := rs (se 1 (by rfl) ⟨7196, by rfl⟩) R14393
theorem R9597 : Reach 9597 := rs (se 3 (by rfl) ⟨1799, by rfl⟩) R3599
theorem R9609 : Reach 9609 := rs (se 2 (by rfl) ⟨3603, by rfl⟩) R7207
theorem R9629 : Reach 9629 := rs (se 3 (by rfl) ⟨1805, by rfl⟩) R3611
theorem R9641 : Reach 9641 := rs (se 2 (by rfl) ⟨3615, by rfl⟩) R7231
theorem R9653 : Reach 9653 := rs (se 5 (by rfl) ⟨452, by rfl⟩) R905
theorem R9665 : Reach 9665 := rs (se 2 (by rfl) ⟨3624, by rfl⟩) R7249
theorem R9667 : Reach 9667 := rs (se 1 (by rfl) ⟨7250, by rfl⟩) R14501
theorem R9671 : Reach 9671 := rs (se 1 (by rfl) ⟨7253, by rfl⟩) R14507
theorem R9675 : Reach 9675 := rs (se 1 (by rfl) ⟨7256, by rfl⟩) R14513
theorem R9689 : Reach 9689 := rs (se 2 (by rfl) ⟨3633, by rfl⟩) R7267
theorem R9693 : Reach 9693 := rs (se 3 (by rfl) ⟨1817, by rfl⟩) R3635
theorem R9765 : Reach 9765 := rs (se 4 (by rfl) ⟨915, by rfl⟩) R1831
theorem R9767 : Reach 9767 := rs (se 1 (by rfl) ⟨7325, by rfl⟩) R14651
theorem R9791 : Reach 9791 := rs (se 1 (by rfl) ⟨7343, by rfl⟩) R14687
theorem R9819 : Reach 9819 := rs (se 1 (by rfl) ⟨7364, by rfl⟩) R14729
theorem R9843 : Reach 9843 := rs (se 1 (by rfl) ⟨7382, by rfl⟩) R14765
theorem R9845 : Reach 9845 := rs (se 5 (by rfl) ⟨461, by rfl⟩) R923
theorem R9847 : Reach 9847 := rs (se 1 (by rfl) ⟨7385, by rfl⟩) R14771
theorem R9849 : Reach 9849 := rs (se 2 (by rfl) ⟨3693, by rfl⟩) R7387
theorem R9851 : Reach 9851 := rs (se 1 (by rfl) ⟨7388, by rfl⟩) R14777
theorem R9861 : Reach 9861 := rs (se 4 (by rfl) ⟨924, by rfl⟩) R1849
theorem R9863 : Reach 9863 := rs (se 1 (by rfl) ⟨7397, by rfl⟩) R14795
theorem R9867 : Reach 9867 := rs (se 1 (by rfl) ⟨7400, by rfl⟩) R14801
theorem R9901 : Reach 9901 := rs (se 3 (by rfl) ⟨1856, by rfl⟩) R3713
theorem R9903 : Reach 9903 := rs (se 1 (by rfl) ⟨7427, by rfl⟩) R14855
theorem R9911 : Reach 9911 := rs (se 1 (by rfl) ⟨7433, by rfl⟩) R14867
theorem R9923 : Reach 9923 := rs (se 1 (by rfl) ⟨7442, by rfl⟩) R14885
theorem R9937 : Reach 9937 := rs (se 2 (by rfl) ⟨3726, by rfl⟩) R7453
theorem R9939 : Reach 9939 := rs (se 1 (by rfl) ⟨7454, by rfl⟩) R14909
theorem R9943 : Reach 9943 := rs (se 1 (by rfl) ⟨7457, by rfl⟩) R14915
theorem R9945 : Reach 9945 := rs (se 2 (by rfl) ⟨3729, by rfl⟩) R7459
theorem R9949 : Reach 9949 := rs (se 3 (by rfl) ⟨1865, by rfl⟩) R3731
theorem R9951 : Reach 9951 := rs (se 1 (by rfl) ⟨7463, by rfl⟩) R14927
theorem R9953 : Reach 9953 := rs (se 2 (by rfl) ⟨3732, by rfl⟩) R7465
theorem R9959 : Reach 9959 := rs (se 1 (by rfl) ⟨7469, by rfl⟩) R14939
theorem R9961 : Reach 9961 := rs (se 2 (by rfl) ⟨3735, by rfl⟩) R7471
theorem R9963 : Reach 9963 := rs (se 1 (by rfl) ⟨7472, by rfl⟩) R14945
theorem R9967 : Reach 9967 := rs (se 1 (by rfl) ⟨7475, by rfl⟩) R14951
theorem R9979 : Reach 9979 := rs (se 1 (by rfl) ⟨7484, by rfl⟩) R14969
theorem R9981 : Reach 9981 := rs (se 3 (by rfl) ⟨1871, by rfl⟩) R3743
theorem R9993 : Reach 9993 := rs (se 2 (by rfl) ⟨3747, by rfl⟩) R7495
theorem R10115 : Reach 10115 := rs (se 1 (by rfl) ⟨7586, by rfl⟩) R15173
theorem R10117 : Reach 10117 := rs (se 4 (by rfl) ⟨948, by rfl⟩) R1897
theorem R10119 : Reach 10119 := rs (se 1 (by rfl) ⟨7589, by rfl⟩) R15179
theorem R10129 : Reach 10129 := rs (se 2 (by rfl) ⟨3798, by rfl⟩) R7597
theorem R10131 : Reach 10131 := rs (se 1 (by rfl) ⟨7598, by rfl⟩) R15197
theorem R42929 : Reach 42929 := rs (se 2 (by rfl) ⟨16098, by rfl⟩) R32197
theorem R10191 : Reach 10191 := rs (se 1 (by rfl) ⟨7643, by rfl⟩) R15287
theorem R43019 : Reach 43019 := rs (se 1 (by rfl) ⟨32264, by rfl⟩) R64529
theorem R10383 : Reach 10383 := rs (se 1 (by rfl) ⟨7787, by rfl⟩) R15575
theorem R10695 : Reach 10695 := rs (se 1 (by rfl) ⟨8021, by rfl⟩) R16043
theorem R10709 : Reach 10709 := rs (se 7 (by rfl) ⟨125, by rfl⟩) R251
theorem R10723 : Reach 10723 := rs (se 1 (by rfl) ⟨8042, by rfl⟩) R16085
theorem R10733 : Reach 10733 := rs (se 3 (by rfl) ⟨2012, by rfl⟩) R4025
theorem R10737 : Reach 10737 := rs (se 2 (by rfl) ⟨4026, by rfl⟩) R8053
theorem R10739 : Reach 10739 := rs (se 1 (by rfl) ⟨8054, by rfl⟩) R16109
theorem R10753 : Reach 10753 := rs (se 2 (by rfl) ⟨4032, by rfl⟩) R8065
theorem R10755 : Reach 10755 := rs (se 1 (by rfl) ⟨8066, by rfl⟩) R16133
theorem R10757 : Reach 10757 := rs (se 4 (by rfl) ⟨1008, by rfl⟩) R2017
theorem R10761 : Reach 10761 := rs (se 2 (by rfl) ⟨4035, by rfl⟩) R8071
theorem R10763 : Reach 10763 := rs (se 1 (by rfl) ⟨8072, by rfl⟩) R16145
theorem R10767 : Reach 10767 := rs (se 1 (by rfl) ⟨8075, by rfl⟩) R16151
theorem R10807 : Reach 10807 := rs (se 1 (by rfl) ⟨8105, by rfl⟩) R16211
theorem R43649 : Reach 43649 := rs (se 2 (by rfl) ⟨16368, by rfl⟩) R32737
theorem R11003 : Reach 11003 := rs (se 1 (by rfl) ⟨8252, by rfl⟩) R16505
theorem R11007 : Reach 11007 := rs (se 1 (by rfl) ⟨8255, by rfl⟩) R16511
theorem R11131 : Reach 11131 := rs (se 1 (by rfl) ⟨8348, by rfl⟩) R16697
theorem R11199 : Reach 11199 := rs (se 1 (by rfl) ⟨8399, by rfl⟩) R16799
theorem R76787 : Reach 76787 := rs (se 1 (by rfl) ⟨57590, by rfl⟩) R115181
theorem R44059 : Reach 44059 := rs (se 1 (by rfl) ⟨33044, by rfl⟩) R66089
theorem R77041 : Reach 77041 := rs (se 2 (by rfl) ⟨28890, by rfl⟩) R57781
theorem R11847 : Reach 11847 := rs (se 1 (by rfl) ⟨8885, by rfl⟩) R17771
theorem R11855 : Reach 11855 := rs (se 1 (by rfl) ⟨8891, by rfl⟩) R17783
theorem R11865 : Reach 11865 := rs (se 2 (by rfl) ⟨4449, by rfl⟩) R8899
theorem R11867 : Reach 11867 := rs (se 1 (by rfl) ⟨8900, by rfl⟩) R17801
theorem R11879 : Reach 11879 := rs (se 1 (by rfl) ⟨8909, by rfl⟩) R17819
theorem R11897 : Reach 11897 := rs (se 2 (by rfl) ⟨4461, by rfl⟩) R8923
theorem R77435 : Reach 77435 := rs (se 1 (by rfl) ⟨58076, by rfl⟩) R116153
theorem R78185 : Reach 78185 := rs (se 2 (by rfl) ⟨29319, by rfl⟩) R58639
theorem R78823 : Reach 78823 := rs (se 1 (by rfl) ⟨59117, by rfl⟩) R118235
theorem R79177 : Reach 79177 := rs (se 2 (by rfl) ⟨29691, by rfl⟩) R59383
theorem R79217 : Reach 79217 := rs (se 2 (by rfl) ⟨29706, by rfl⟩) R59413
theorem R79703 : Reach 79703 := rs (se 1 (by rfl) ⟨59777, by rfl⟩) R119555
theorem R47479 : Reach 47479 := rs (se 1 (by rfl) ⟨35609, by rfl⟩) R71219
theorem R83105 : Reach 83105 := rs (se 2 (by rfl) ⟨31164, by rfl⟩) R62329
theorem R19193 : Reach 19193 := rs (se 2 (by rfl) ⟨7197, by rfl⟩) R14395
theorem R346913 : Reach 346913 := rs (se 2 (by rfl) ⟨130092, by rfl⟩) R260185
theorem R19241 : Reach 19241 := rs (se 2 (by rfl) ⟨7215, by rfl⟩) R14431
theorem R19259 : Reach 19259 := rs (se 1 (by rfl) ⟨14444, by rfl⟩) R28889
theorem R19271 : Reach 19271 := rs (se 1 (by rfl) ⟨14453, by rfl⟩) R28907
theorem R19313 : Reach 19313 := rs (se 2 (by rfl) ⟨7242, by rfl⟩) R14485
theorem R19331 : Reach 19331 := rs (se 1 (by rfl) ⟨14498, by rfl⟩) R28997
theorem R19379 : Reach 19379 := rs (se 1 (by rfl) ⟨14534, by rfl⟩) R29069
theorem R19385 : Reach 19385 := rs (se 2 (by rfl) ⟨7269, by rfl⟩) R14539
theorem R19403 : Reach 19403 := rs (se 1 (by rfl) ⟨14552, by rfl⟩) R29105
theorem R19577 : Reach 19577 := rs (se 2 (by rfl) ⟨7341, by rfl⟩) R14683
theorem R19703 : Reach 19703 := rs (se 1 (by rfl) ⟨14777, by rfl⟩) R29555
theorem R19727 : Reach 19727 := rs (se 1 (by rfl) ⟨14795, by rfl⟩) R29591
theorem R19817 : Reach 19817 := rs (se 2 (by rfl) ⟨7431, by rfl⟩) R14863
theorem R19885 : Reach 19885 := rs (se 3 (by rfl) ⟨3728, by rfl⟩) R7457
theorem R19889 : Reach 19889 := rs (se 2 (by rfl) ⟨7458, by rfl⟩) R14917
theorem R19907 : Reach 19907 := rs (se 1 (by rfl) ⟨14930, by rfl⟩) R29861
theorem R19919 : Reach 19919 := rs (se 1 (by rfl) ⟨14939, by rfl⟩) R29879
theorem R19943 : Reach 19943 := rs (se 1 (by rfl) ⟨14957, by rfl⟩) R29915
theorem R19961 : Reach 19961 := rs (se 2 (by rfl) ⟨7485, by rfl⟩) R14971
theorem R20267 : Reach 20267 := rs (se 1 (by rfl) ⟨15200, by rfl⟩) R30401
theorem R20459 : Reach 20459 := rs (se 1 (by rfl) ⟨15344, by rfl⟩) R30689
theorem R86021 : Reach 86021 := rs (se 4 (by rfl) ⟨8064, by rfl⟩) R16129
theorem R21475 : Reach 21475 := rs (se 1 (by rfl) ⟨16106, by rfl⟩) R32213
theorem R21505 : Reach 21505 := rs (se 2 (by rfl) ⟨8064, by rfl⟩) R16129
theorem R21509 : Reach 21509 := rs (se 4 (by rfl) ⟨2016, by rfl⟩) R4033
theorem R21521 : Reach 21521 := rs (se 2 (by rfl) ⟨8070, by rfl⟩) R16141
theorem R21527 : Reach 21527 := rs (se 1 (by rfl) ⟨16145, by rfl⟩) R32291
theorem R21613 : Reach 21613 := rs (se 3 (by rfl) ⟨4052, by rfl⟩) R8105
theorem R22007 : Reach 22007 := rs (se 1 (by rfl) ⟨16505, by rfl⟩) R33011
theorem R317621 : Reach 317621 := rs (se 5 (by rfl) ⟨14888, by rfl⟩) R29777
theorem R318005 : Reach 318005 := rs (se 5 (by rfl) ⟨14906, by rfl⟩) R29813
theorem R23759 : Reach 23759 := rs (se 1 (by rfl) ⟨17819, by rfl⟩) R35639
theorem R23795 : Reach 23795 := rs (se 1 (by rfl) ⟨17846, by rfl⟩) R35693
theorem R189449 : Reach 189449 := rs (se 2 (by rfl) ⟨71043, by rfl⟩) R142087
theorem R157601 : Reach 157601 := rs (se 2 (by rfl) ⟨59100, by rfl⟩) R118201
theorem R94769 : Reach 94769 := rs (se 2 (by rfl) ⟨35538, by rfl⟩) R71077
theorem R326105 : Reach 326105 := rs (se 2 (by rfl) ⟨122289, by rfl⟩) R244579
theorem R163205 : Reach 163205 := rs (se 4 (by rfl) ⟨15300, by rfl⟩) R30601
theorem R111 : Reach 111 := rs (se 1 (by rfl) ⟨83, by rfl⟩) R167
theorem R223 : Reach 223 := rs (se 1 (by rfl) ⟨167, by rfl⟩) R335
theorem R445 : Reach 445 := rs (se 3 (by rfl) ⟨83, by rfl⟩) R167
theorem R799 : Reach 799 := rs (se 1 (by rfl) ⟨599, by rfl⟩) R1199
theorem R807 : Reach 807 := rs (se 1 (by rfl) ⟨605, by rfl⟩) R1211
theorem R893 : Reach 893 := rs (se 3 (by rfl) ⟨167, by rfl⟩) R335
theorem R1595 : Reach 1595 := rs (se 1 (by rfl) ⟨1196, by rfl⟩) R2393
theorem R1599 : Reach 1599 := rs (se 1 (by rfl) ⟨1199, by rfl⟩) R2399
theorem R1609 : Reach 1609 := rs (se 2 (by rfl) ⟨603, by rfl⟩) R1207
theorem R1615 : Reach 1615 := rs (se 1 (by rfl) ⟨1211, by rfl⟩) R2423
theorem R1627 : Reach 1627 := rs (se 1 (by rfl) ⟨1220, by rfl⟩) R2441
theorem R1641 : Reach 1641 := rs (se 2 (by rfl) ⟨615, by rfl⟩) R1231
theorem R1643 : Reach 1643 := rs (se 1 (by rfl) ⟨1232, by rfl⟩) R2465
theorem R1657 : Reach 1657 := rs (se 2 (by rfl) ⟨621, by rfl⟩) R1243
theorem R1663 : Reach 1663 := rs (se 1 (by rfl) ⟨1247, by rfl⟩) R2495
theorem R1781 : Reach 1781 := rs (se 5 (by rfl) ⟨83, by rfl⟩) R167
theorem R231275 : Reach 231275 := rs (se 1 (by rfl) ⟨173456, by rfl⟩) R346913
theorem R3191 : Reach 3191 := rs (se 1 (by rfl) ⟨2393, by rfl⟩) R4787
theorem R3195 : Reach 3195 := rs (se 1 (by rfl) ⟨2396, by rfl⟩) R4793
theorem R3197 : Reach 3197 := rs (se 3 (by rfl) ⟨599, by rfl⟩) R1199
theorem R3209 : Reach 3209 := rs (se 2 (by rfl) ⟨1203, by rfl⟩) R2407
theorem R3217 : Reach 3217 := rs (se 2 (by rfl) ⟨1206, by rfl⟩) R2413
theorem R3219 : Reach 3219 := rs (se 1 (by rfl) ⟨2414, by rfl⟩) R4829
theorem R3229 : Reach 3229 := rs (se 3 (by rfl) ⟨605, by rfl⟩) R1211
theorem R3255 : Reach 3255 := rs (se 1 (by rfl) ⟨2441, by rfl⟩) R4883
theorem R3263 : Reach 3263 := rs (se 1 (by rfl) ⟨2447, by rfl⟩) R4895
theorem R3281 : Reach 3281 := rs (se 2 (by rfl) ⟨1230, by rfl⟩) R2461
theorem R3283 : Reach 3283 := rs (se 1 (by rfl) ⟨2462, by rfl⟩) R4925
theorem R3287 : Reach 3287 := rs (se 1 (by rfl) ⟨2465, by rfl⟩) R4931
theorem R3303 : Reach 3303 := rs (se 1 (by rfl) ⟨2477, by rfl⟩) R4955
theorem R3307 : Reach 3307 := rs (se 1 (by rfl) ⟨2480, by rfl⟩) R4961
theorem R3315 : Reach 3315 := rs (se 1 (by rfl) ⟨2486, by rfl⟩) R4973
theorem R3327 : Reach 3327 := rs (se 1 (by rfl) ⟨2495, by rfl⟩) R4991
theorem R3371 : Reach 3371 := rs (se 1 (by rfl) ⟨2528, by rfl⟩) R5057
theorem R3569 : Reach 3569 := rs (se 2 (by rfl) ⟨1338, by rfl⟩) R2677
theorem R3573 : Reach 3573 := rs (se 5 (by rfl) ⟨167, by rfl⟩) R335
theorem R3577 : Reach 3577 := rs (se 2 (by rfl) ⟨1341, by rfl⟩) R2683
theorem R3579 : Reach 3579 := rs (se 1 (by rfl) ⟨2684, by rfl⟩) R5369
theorem R3585 : Reach 3585 := rs (se 2 (by rfl) ⟨1344, by rfl⟩) R2689
theorem R3951 : Reach 3951 := rs (se 1 (by rfl) ⟨2963, by rfl⟩) R5927
theorem R102653 : Reach 102653 := rs (se 3 (by rfl) ⟨19247, by rfl⟩) R38495
theorem R102721 : Reach 102721 := rs (se 2 (by rfl) ⟨38520, by rfl⟩) R77041
theorem R103085 : Reach 103085 := rs (se 3 (by rfl) ⟨19328, by rfl⟩) R38657
theorem R104429 : Reach 104429 := rs (se 3 (by rfl) ⟨19580, by rfl⟩) R39161
theorem R6381 : Reach 6381 := rs (se 3 (by rfl) ⟨1196, by rfl⟩) R2393
theorem R6391 : Reach 6391 := rs (se 1 (by rfl) ⟨4793, by rfl⟩) R9587
theorem R6397 : Reach 6397 := rs (se 3 (by rfl) ⟨1199, by rfl⟩) R2399
theorem R6419 : Reach 6419 := rs (se 1 (by rfl) ⟨4814, by rfl⟩) R9629
theorem R6427 : Reach 6427 := rs (se 1 (by rfl) ⟨4820, by rfl⟩) R9641
theorem R6435 : Reach 6435 := rs (se 1 (by rfl) ⟨4826, by rfl⟩) R9653
theorem R6437 : Reach 6437 := rs (se 4 (by rfl) ⟨603, by rfl⟩) R1207
theorem R6443 : Reach 6443 := rs (se 1 (by rfl) ⟨4832, by rfl⟩) R9665
theorem R6447 : Reach 6447 := rs (se 1 (by rfl) ⟨4835, by rfl⟩) R9671
theorem R6459 : Reach 6459 := rs (se 1 (by rfl) ⟨4844, by rfl⟩) R9689
theorem R6461 : Reach 6461 := rs (se 3 (by rfl) ⟨1211, by rfl⟩) R2423
theorem R6509 : Reach 6509 := rs (se 3 (by rfl) ⟨1220, by rfl⟩) R2441
theorem R6511 : Reach 6511 := rs (se 1 (by rfl) ⟨4883, by rfl⟩) R9767
theorem R6527 : Reach 6527 := rs (se 1 (by rfl) ⟨4895, by rfl⟩) R9791
theorem R6561 : Reach 6561 := rs (se 2 (by rfl) ⟨2460, by rfl⟩) R4921
theorem R6563 : Reach 6563 := rs (se 1 (by rfl) ⟨4922, by rfl⟩) R9845
theorem R6565 : Reach 6565 := rs (se 4 (by rfl) ⟨615, by rfl⟩) R1231
theorem R6567 : Reach 6567 := rs (se 1 (by rfl) ⟨4925, by rfl⟩) R9851
theorem R6573 : Reach 6573 := rs (se 3 (by rfl) ⟨1232, by rfl⟩) R2465
theorem R6575 : Reach 6575 := rs (se 1 (by rfl) ⟨4931, by rfl⟩) R9863
theorem R6601 : Reach 6601 := rs (se 2 (by rfl) ⟨2475, by rfl⟩) R4951
theorem R6607 : Reach 6607 := rs (se 1 (by rfl) ⟨4955, by rfl⟩) R9911
theorem R6615 : Reach 6615 := rs (se 1 (by rfl) ⟨4961, by rfl⟩) R9923
theorem R6625 : Reach 6625 := rs (se 2 (by rfl) ⟨2484, by rfl⟩) R4969
theorem R6629 : Reach 6629 := rs (se 4 (by rfl) ⟨621, by rfl⟩) R1243
theorem R6633 : Reach 6633 := rs (se 2 (by rfl) ⟨2487, by rfl⟩) R4975
theorem R6635 : Reach 6635 := rs (se 1 (by rfl) ⟨4976, by rfl⟩) R9953
theorem R6639 : Reach 6639 := rs (se 1 (by rfl) ⟨4979, by rfl⟩) R9959
theorem R6653 : Reach 6653 := rs (se 3 (by rfl) ⟨1247, by rfl⟩) R2495
theorem R6743 : Reach 6743 := rs (se 1 (by rfl) ⟨5057, by rfl⟩) R10115
theorem R6745 : Reach 6745 := rs (se 2 (by rfl) ⟨2529, by rfl⟩) R5059
theorem R6753 : Reach 6753 := rs (se 2 (by rfl) ⟨2532, by rfl⟩) R5065
theorem R105067 : Reach 105067 := rs (se 1 (by rfl) ⟨78800, by rfl⟩) R157601
theorem R105097 : Reach 105097 := rs (se 2 (by rfl) ⟨39411, by rfl⟩) R78823
theorem R6793 : Reach 6793 := rs (se 2 (by rfl) ⟨2547, by rfl⟩) R5095
theorem R6921 : Reach 6921 := rs (se 2 (by rfl) ⟨2595, by rfl⟩) R5191
theorem R7125 : Reach 7125 := rs (se 7 (by rfl) ⟨83, by rfl⟩) R167
theorem R7139 : Reach 7139 := rs (se 1 (by rfl) ⟨5354, by rfl⟩) R10709
theorem R7153 : Reach 7153 := rs (se 2 (by rfl) ⟨2682, by rfl⟩) R5365
theorem R7155 : Reach 7155 := rs (se 1 (by rfl) ⟨5366, by rfl⟩) R10733
theorem R7159 : Reach 7159 := rs (se 1 (by rfl) ⟨5369, by rfl⟩) R10739
theorem R7169 : Reach 7169 := rs (se 2 (by rfl) ⟨2688, by rfl⟩) R5377
theorem R7171 : Reach 7171 := rs (se 1 (by rfl) ⟨5378, by rfl⟩) R10757
theorem R7175 : Reach 7175 := rs (se 1 (by rfl) ⟨5381, by rfl⟩) R10763
theorem R7177 : Reach 7177 := rs (se 2 (by rfl) ⟨2691, by rfl⟩) R5383
theorem R105569 : Reach 105569 := rs (se 2 (by rfl) ⟨39588, by rfl⟩) R79177
theorem R7335 : Reach 7335 := rs (se 1 (by rfl) ⟨5501, by rfl⟩) R11003
theorem R106069 : Reach 106069 := rs (se 8 (by rfl) ⟨621, by rfl⟩) R1243
theorem R7903 : Reach 7903 := rs (se 1 (by rfl) ⟨5927, by rfl⟩) R11855
theorem R7911 : Reach 7911 := rs (se 1 (by rfl) ⟨5933, by rfl⟩) R11867
theorem R7919 : Reach 7919 := rs (se 1 (by rfl) ⟨5939, by rfl⟩) R11879
theorem R7931 : Reach 7931 := rs (se 1 (by rfl) ⟨5948, by rfl⟩) R11897
theorem R108053 : Reach 108053 := rs (se 6 (by rfl) ⟨2532, by rfl⟩) R5065
theorem R108803 : Reach 108803 := rs (se 1 (by rfl) ⟨81602, by rfl⟩) R163205
theorem R110807 : Reach 110807 := rs (se 1 (by rfl) ⟨83105, by rfl⟩) R166211
theorem R12761 : Reach 12761 := rs (se 2 (by rfl) ⟨4785, by rfl⟩) R9571
theorem R12765 : Reach 12765 := rs (se 3 (by rfl) ⟨2393, by rfl⟩) R4787
theorem R12781 : Reach 12781 := rs (se 3 (by rfl) ⟨2396, by rfl⟩) R4793
theorem R12789 : Reach 12789 := rs (se 5 (by rfl) ⟨599, by rfl⟩) R1199
theorem R12793 : Reach 12793 := rs (se 2 (by rfl) ⟨4797, by rfl⟩) R9595
theorem R12795 : Reach 12795 := rs (se 1 (by rfl) ⟨9596, by rfl⟩) R19193
theorem R12827 : Reach 12827 := rs (se 1 (by rfl) ⟨9620, by rfl⟩) R19241
theorem R12839 : Reach 12839 := rs (se 1 (by rfl) ⟨9629, by rfl⟩) R19259
theorem R12847 : Reach 12847 := rs (se 1 (by rfl) ⟨9635, by rfl⟩) R19271
theorem R12869 : Reach 12869 := rs (se 4 (by rfl) ⟨1206, by rfl⟩) R2413
theorem R12875 : Reach 12875 := rs (se 1 (by rfl) ⟨9656, by rfl⟩) R19313
theorem R12887 : Reach 12887 := rs (se 1 (by rfl) ⟨9665, by rfl⟩) R19331
theorem R12889 : Reach 12889 := rs (se 2 (by rfl) ⟨4833, by rfl⟩) R9667
theorem R12917 : Reach 12917 := rs (se 5 (by rfl) ⟨605, by rfl⟩) R1211
theorem R12919 : Reach 12919 := rs (se 1 (by rfl) ⟨9689, by rfl⟩) R19379
theorem R12923 : Reach 12923 := rs (se 1 (by rfl) ⟨9692, by rfl⟩) R19385
theorem R12935 : Reach 12935 := rs (se 1 (by rfl) ⟨9701, by rfl⟩) R19403
theorem R13051 : Reach 13051 := rs (se 1 (by rfl) ⟨9788, by rfl⟩) R19577
theorem R13133 : Reach 13133 := rs (se 3 (by rfl) ⟨2462, by rfl⟩) R4925
theorem R13135 : Reach 13135 := rs (se 1 (by rfl) ⟨9851, by rfl⟩) R19703
theorem R13151 : Reach 13151 := rs (se 1 (by rfl) ⟨9863, by rfl⟩) R19727
theorem R13211 : Reach 13211 := rs (se 1 (by rfl) ⟨9908, by rfl⟩) R19817
theorem R13213 : Reach 13213 := rs (se 3 (by rfl) ⟨2477, by rfl⟩) R4955
theorem R13229 : Reach 13229 := rs (se 3 (by rfl) ⟨2480, by rfl⟩) R4961
theorem R13259 : Reach 13259 := rs (se 1 (by rfl) ⟨9944, by rfl⟩) R19889
theorem R13261 : Reach 13261 := rs (se 3 (by rfl) ⟨2486, by rfl⟩) R4973
theorem R13265 : Reach 13265 := rs (se 2 (by rfl) ⟨4974, by rfl⟩) R9949
theorem R13271 : Reach 13271 := rs (se 1 (by rfl) ⟨9953, by rfl⟩) R19907
theorem R13279 : Reach 13279 := rs (se 1 (by rfl) ⟨9959, by rfl⟩) R19919
theorem R13289 : Reach 13289 := rs (se 2 (by rfl) ⟨4983, by rfl⟩) R9967
theorem R13295 : Reach 13295 := rs (se 1 (by rfl) ⟨9971, by rfl⟩) R19943
theorem R13307 : Reach 13307 := rs (se 1 (by rfl) ⟨9980, by rfl⟩) R19961
theorem R13505 : Reach 13505 := rs (se 2 (by rfl) ⟨5064, by rfl⟩) R10129
theorem R13511 : Reach 13511 := rs (se 1 (by rfl) ⟨10133, by rfl⟩) R20267
theorem R13639 : Reach 13639 := rs (se 1 (by rfl) ⟨10229, by rfl⟩) R20459
theorem R14297 : Reach 14297 := rs (se 2 (by rfl) ⟨5361, by rfl⟩) R10723
theorem R14309 : Reach 14309 := rs (se 4 (by rfl) ⟨1341, by rfl⟩) R2683
theorem R14339 : Reach 14339 := rs (se 1 (by rfl) ⟨10754, by rfl⟩) R21509
theorem R14341 : Reach 14341 := rs (se 4 (by rfl) ⟨1344, by rfl⟩) R2689
theorem R14347 : Reach 14347 := rs (se 1 (by rfl) ⟨10760, by rfl⟩) R21521
theorem R14351 : Reach 14351 := rs (se 1 (by rfl) ⟨10763, by rfl⟩) R21527
theorem R14671 : Reach 14671 := rs (se 1 (by rfl) ⟨11003, by rfl⟩) R22007
theorem R211747 : Reach 211747 := rs (se 1 (by rfl) ⟨158810, by rfl⟩) R317621
theorem R212003 : Reach 212003 := rs (se 1 (by rfl) ⟨159002, by rfl⟩) R318005
theorem R15805 : Reach 15805 := rs (se 3 (by rfl) ⟨2963, by rfl⟩) R5927
theorem R15839 : Reach 15839 := rs (se 1 (by rfl) ⟨11879, by rfl⟩) R23759
theorem R15863 : Reach 15863 := rs (se 1 (by rfl) ⟨11897, by rfl⟩) R23795
theorem R51191 : Reach 51191 := rs (se 1 (by rfl) ⟨38393, by rfl⟩) R76787
theorem R51623 : Reach 51623 := rs (se 1 (by rfl) ⟨38717, by rfl⟩) R77435
theorem R51677 : Reach 51677 := rs (se 3 (by rfl) ⟨9689, by rfl⟩) R19379
theorem R52123 : Reach 52123 := rs (se 1 (by rfl) ⟨39092, by rfl⟩) R78185
theorem R52609 : Reach 52609 := rs (se 2 (by rfl) ⟨19728, by rfl⟩) R39457
theorem R52625 : Reach 52625 := rs (se 2 (by rfl) ⟨19734, by rfl⟩) R39469
theorem R52649 : Reach 52649 := rs (se 2 (by rfl) ⟨19743, by rfl⟩) R39487
theorem R52811 : Reach 52811 := rs (se 1 (by rfl) ⟨39608, by rfl⟩) R79217
theorem R53081 : Reach 53081 := rs (se 2 (by rfl) ⟨19905, by rfl⟩) R39811
theorem R53135 : Reach 53135 := rs (se 1 (by rfl) ⟨39851, by rfl⟩) R79703
theorem R53297 : Reach 53297 := rs (se 2 (by rfl) ⟨19986, by rfl⟩) R39973
theorem R217403 : Reach 217403 := rs (se 1 (by rfl) ⟨163052, by rfl⟩) R326105
theorem R55403 : Reach 55403 := rs (se 1 (by rfl) ⟨41552, by rfl⟩) R83105
theorem R57347 : Reach 57347 := rs (se 1 (by rfl) ⟨43010, by rfl⟩) R86021
theorem R25523 : Reach 25523 := rs (se 1 (by rfl) ⟨19142, by rfl⟩) R38285
theorem R25595 : Reach 25595 := rs (se 1 (by rfl) ⟨19196, by rfl⟩) R38393
theorem R25847 : Reach 25847 := rs (se 1 (by rfl) ⟨19385, by rfl⟩) R38771
theorem R58745 : Reach 58745 := rs (se 2 (by rfl) ⟨22029, by rfl⟩) R44059
theorem R26045 : Reach 26045 := rs (se 3 (by rfl) ⟨4883, by rfl⟩) R9767
theorem R26183 : Reach 26183 := rs (se 1 (by rfl) ⟨19637, by rfl⟩) R39275
theorem R26261 : Reach 26261 := rs (se 6 (by rfl) ⟨615, by rfl⟩) R1231
theorem R26279 : Reach 26279 := rs (se 1 (by rfl) ⟨19709, by rfl⟩) R39419
theorem R26315 : Reach 26315 := rs (se 1 (by rfl) ⟨19736, by rfl⟩) R39473
theorem R26351 : Reach 26351 := rs (se 1 (by rfl) ⟨19763, by rfl⟩) R39527
theorem R26405 : Reach 26405 := rs (se 4 (by rfl) ⟨2475, by rfl⟩) R4951
theorem R26411 : Reach 26411 := rs (se 1 (by rfl) ⟨19808, by rfl⟩) R39617
theorem R26423 : Reach 26423 := rs (se 1 (by rfl) ⟨19817, by rfl⟩) R39635
theorem R26459 : Reach 26459 := rs (se 1 (by rfl) ⟨19844, by rfl⟩) R39689
theorem R26507 : Reach 26507 := rs (se 1 (by rfl) ⟨19880, by rfl⟩) R39761
theorem R26513 : Reach 26513 := rs (se 2 (by rfl) ⟨9942, by rfl⟩) R19885
theorem R26531 : Reach 26531 := rs (se 1 (by rfl) ⟨19898, by rfl⟩) R39797
theorem R26563 : Reach 26563 := rs (se 1 (by rfl) ⟨19922, by rfl⟩) R39845
theorem R26567 : Reach 26567 := rs (se 1 (by rfl) ⟨19925, by rfl⟩) R39851
theorem R26981 : Reach 26981 := rs (se 4 (by rfl) ⟨2529, by rfl⟩) R5059
theorem R27013 : Reach 27013 := rs (se 4 (by rfl) ⟨2532, by rfl⟩) R5065
theorem R27175 : Reach 27175 := rs (se 1 (by rfl) ⟨20381, by rfl⟩) R40763
theorem R126299 : Reach 126299 := rs (se 1 (by rfl) ⟨94724, by rfl⟩) R189449
theorem R28613 : Reach 28613 := rs (se 4 (by rfl) ⟨2682, by rfl⟩) R5365
theorem R28619 : Reach 28619 := rs (se 1 (by rfl) ⟨21464, by rfl⟩) R42929
theorem R28633 : Reach 28633 := rs (se 2 (by rfl) ⟨10737, by rfl⟩) R21475
theorem R28637 : Reach 28637 := rs (se 3 (by rfl) ⟨5369, by rfl⟩) R10739
theorem R28673 : Reach 28673 := rs (se 2 (by rfl) ⟨10752, by rfl⟩) R21505
theorem R28679 : Reach 28679 := rs (se 1 (by rfl) ⟨21509, by rfl⟩) R43019
theorem R28709 : Reach 28709 := rs (se 4 (by rfl) ⟨2691, by rfl⟩) R5383
theorem R28817 : Reach 28817 := rs (se 2 (by rfl) ⟨10806, by rfl⟩) R21613
theorem R29099 : Reach 29099 := rs (se 1 (by rfl) ⟨21824, by rfl⟩) R43649
theorem R63179 : Reach 63179 := rs (se 1 (by rfl) ⟨47384, by rfl⟩) R94769
theorem R63305 : Reach 63305 := rs (se 2 (by rfl) ⟨23739, by rfl⟩) R47479
theorem R297 : Reach 297 := rs (se 2 (by rfl) ⟨111, by rfl⟩) R223
theorem R593 : Reach 593 := rs (se 2 (by rfl) ⟨222, by rfl⟩) R445
theorem R595 : Reach 595 := rs (se 1 (by rfl) ⟨446, by rfl⟩) R893
theorem R1063 : Reach 1063 := rs (se 1 (by rfl) ⟨797, by rfl⟩) R1595
theorem R1065 : Reach 1065 := rs (se 2 (by rfl) ⟨399, by rfl⟩) R799
theorem R1095 : Reach 1095 := rs (se 1 (by rfl) ⟨821, by rfl⟩) R1643
theorem R1187 : Reach 1187 := rs (se 1 (by rfl) ⟨890, by rfl⟩) R1781
theorem R1189 : Reach 1189 := rs (se 4 (by rfl) ⟨111, by rfl⟩) R223
theorem R34127 : Reach 34127 := rs (se 1 (by rfl) ⟨25595, by rfl⟩) R51191
theorem R34415 : Reach 34415 := rs (se 1 (by rfl) ⟨25811, by rfl⟩) R51623
theorem R34445 : Reach 34445 := rs (se 3 (by rfl) ⟨6458, by rfl⟩) R12917
theorem R34451 : Reach 34451 := rs (se 1 (by rfl) ⟨25838, by rfl⟩) R51677
theorem R34805 : Reach 34805 := rs (se 5 (by rfl) ⟨1631, by rfl⟩) R3263
theorem R2127 : Reach 2127 := rs (se 1 (by rfl) ⟨1595, by rfl⟩) R3191
theorem R2131 : Reach 2131 := rs (se 1 (by rfl) ⟨1598, by rfl⟩) R3197
theorem R2139 : Reach 2139 := rs (se 1 (by rfl) ⟨1604, by rfl⟩) R3209
theorem R2145 : Reach 2145 := rs (se 2 (by rfl) ⟨804, by rfl⟩) R1609
theorem R2153 : Reach 2153 := rs (se 2 (by rfl) ⟨807, by rfl⟩) R1615
theorem R2169 : Reach 2169 := rs (se 2 (by rfl) ⟨813, by rfl⟩) R1627
theorem R2175 : Reach 2175 := rs (se 1 (by rfl) ⟨1631, by rfl⟩) R3263
theorem R2187 : Reach 2187 := rs (se 1 (by rfl) ⟨1640, by rfl⟩) R3281
theorem R2191 : Reach 2191 := rs (se 1 (by rfl) ⟨1643, by rfl⟩) R3287
theorem R2209 : Reach 2209 := rs (se 2 (by rfl) ⟨828, by rfl⟩) R1657
theorem R2217 : Reach 2217 := rs (se 2 (by rfl) ⟨831, by rfl⟩) R1663
theorem R2247 : Reach 2247 := rs (se 1 (by rfl) ⟨1685, by rfl⟩) R3371
theorem R35083 : Reach 35083 := rs (se 1 (by rfl) ⟨26312, by rfl⟩) R52625
theorem R35099 : Reach 35099 := rs (se 1 (by rfl) ⟨26324, by rfl⟩) R52649
theorem R2373 : Reach 2373 := rs (se 4 (by rfl) ⟨222, by rfl⟩) R445
theorem R2379 : Reach 2379 := rs (se 1 (by rfl) ⟨1784, by rfl⟩) R3569
theorem R2381 : Reach 2381 := rs (se 3 (by rfl) ⟨446, by rfl⟩) R893
theorem R35207 : Reach 35207 := rs (se 1 (by rfl) ⟨26405, by rfl⟩) R52811
theorem R35387 : Reach 35387 := rs (se 1 (by rfl) ⟨26540, by rfl⟩) R53081
theorem R35417 : Reach 35417 := rs (se 2 (by rfl) ⟨13281, by rfl⟩) R26563
theorem R35423 : Reach 35423 := rs (se 1 (by rfl) ⟨26567, by rfl⟩) R53135
theorem R35437 : Reach 35437 := rs (se 3 (by rfl) ⟨6644, by rfl⟩) R13289
theorem R35477 : Reach 35477 := rs (se 6 (by rfl) ⟨831, by rfl⟩) R1663
theorem R35531 : Reach 35531 := rs (se 1 (by rfl) ⟨26648, by rfl⟩) R53297
theorem R68435 : Reach 68435 := rs (se 1 (by rfl) ⟨51326, by rfl⟩) R102653
theorem R68723 : Reach 68723 := rs (se 1 (by rfl) ⟨51542, by rfl⟩) R103085
theorem R35957 : Reach 35957 := rs (se 5 (by rfl) ⟨1685, by rfl⟩) R3371
theorem R36017 : Reach 36017 := rs (se 2 (by rfl) ⟨13506, by rfl⟩) R27013
theorem R36233 : Reach 36233 := rs (se 2 (by rfl) ⟨13587, by rfl⟩) R27175
theorem R69497 : Reach 69497 := rs (se 2 (by rfl) ⟨26061, by rfl⟩) R52123
theorem R69619 : Reach 69619 := rs (se 1 (by rfl) ⟨52214, by rfl⟩) R104429
theorem R36935 : Reach 36935 := rs (se 1 (by rfl) ⟨27701, by rfl⟩) R55403
theorem R4253 : Reach 4253 := rs (se 3 (by rfl) ⟨797, by rfl⟩) R1595
theorem R4261 : Reach 4261 := rs (se 4 (by rfl) ⟨399, by rfl⟩) R799
theorem R4279 : Reach 4279 := rs (se 1 (by rfl) ⟨3209, by rfl⟩) R6419
theorem R4289 : Reach 4289 := rs (se 2 (by rfl) ⟨1608, by rfl⟩) R3217
theorem R4291 : Reach 4291 := rs (se 1 (by rfl) ⟨3218, by rfl⟩) R6437
theorem R4295 : Reach 4295 := rs (se 1 (by rfl) ⟨3221, by rfl⟩) R6443
theorem R4305 : Reach 4305 := rs (se 2 (by rfl) ⟨1614, by rfl⟩) R3229
theorem R4307 : Reach 4307 := rs (se 1 (by rfl) ⟨3230, by rfl⟩) R6461
theorem R4339 : Reach 4339 := rs (se 1 (by rfl) ⟨3254, by rfl⟩) R6509
theorem R4351 : Reach 4351 := rs (se 1 (by rfl) ⟨3263, by rfl⟩) R6527
theorem R4375 : Reach 4375 := rs (se 1 (by rfl) ⟨3281, by rfl⟩) R6563
theorem R4377 : Reach 4377 := rs (se 2 (by rfl) ⟨1641, by rfl⟩) R3283
theorem R4381 : Reach 4381 := rs (se 3 (by rfl) ⟨821, by rfl⟩) R1643
theorem R4383 : Reach 4383 := rs (se 1 (by rfl) ⟨3287, by rfl⟩) R6575
theorem R4409 : Reach 4409 := rs (se 2 (by rfl) ⟨1653, by rfl⟩) R3307
theorem R4419 : Reach 4419 := rs (se 1 (by rfl) ⟨3314, by rfl⟩) R6629
theorem R4423 : Reach 4423 := rs (se 1 (by rfl) ⟨3317, by rfl⟩) R6635
theorem R4435 : Reach 4435 := rs (se 1 (by rfl) ⟨3326, by rfl⟩) R6653
theorem R4495 : Reach 4495 := rs (se 1 (by rfl) ⟨3371, by rfl⟩) R6743
theorem R70145 : Reach 70145 := rs (se 2 (by rfl) ⟨26304, by rfl⟩) R52609
theorem R4749 : Reach 4749 := rs (se 3 (by rfl) ⟨890, by rfl⟩) R1781
theorem R4757 : Reach 4757 := rs (se 6 (by rfl) ⟨111, by rfl⟩) R223
theorem R4759 : Reach 4759 := rs (se 1 (by rfl) ⟨3569, by rfl⟩) R7139
theorem R4769 : Reach 4769 := rs (se 2 (by rfl) ⟨1788, by rfl⟩) R3577
theorem R4779 : Reach 4779 := rs (se 1 (by rfl) ⟨3584, by rfl⟩) R7169
theorem R4783 : Reach 4783 := rs (se 1 (by rfl) ⟨3587, by rfl⟩) R7175
theorem R70379 : Reach 70379 := rs (se 1 (by rfl) ⟨52784, by rfl⟩) R105569
theorem R70429 : Reach 70429 := rs (se 3 (by rfl) ⟨13205, by rfl⟩) R26411
theorem R70469 : Reach 70469 := rs (se 4 (by rfl) ⟨6606, by rfl⟩) R13213
theorem R5279 : Reach 5279 := rs (se 1 (by rfl) ⟨3959, by rfl⟩) R7919
theorem R5287 : Reach 5287 := rs (se 1 (by rfl) ⟨3965, by rfl⟩) R7931
theorem R38069 : Reach 38069 := rs (se 5 (by rfl) ⟨1784, by rfl⟩) R3569
theorem R38177 : Reach 38177 := rs (se 2 (by rfl) ⟨14316, by rfl⟩) R28633
theorem R38231 : Reach 38231 := rs (se 1 (by rfl) ⟨28673, by rfl⟩) R57347
theorem R136961 : Reach 136961 := rs (se 2 (by rfl) ⟨51360, by rfl⟩) R102721
theorem R72035 : Reach 72035 := rs (se 1 (by rfl) ⟨54026, by rfl⟩) R108053
theorem R72535 : Reach 72535 := rs (se 1 (by rfl) ⟨54401, by rfl⟩) R108803
theorem R73871 : Reach 73871 := rs (se 1 (by rfl) ⟨55403, by rfl⟩) R110807
theorem R8507 : Reach 8507 := rs (se 1 (by rfl) ⟨6380, by rfl⟩) R12761
theorem R8509 : Reach 8509 := rs (se 3 (by rfl) ⟨1595, by rfl⟩) R3191
theorem R8521 : Reach 8521 := rs (se 2 (by rfl) ⟨3195, by rfl⟩) R6391
theorem R8525 : Reach 8525 := rs (se 3 (by rfl) ⟨1598, by rfl⟩) R3197
theorem R8529 : Reach 8529 := rs (se 2 (by rfl) ⟨3198, by rfl⟩) R6397
theorem R8551 : Reach 8551 := rs (se 1 (by rfl) ⟨6413, by rfl⟩) R12827
theorem R8557 : Reach 8557 := rs (se 3 (by rfl) ⟨1604, by rfl⟩) R3209
theorem R8559 : Reach 8559 := rs (se 1 (by rfl) ⟨6419, by rfl⟩) R12839
theorem R8569 : Reach 8569 := rs (se 2 (by rfl) ⟨3213, by rfl⟩) R6427
theorem R8579 : Reach 8579 := rs (se 1 (by rfl) ⟨6434, by rfl⟩) R12869
theorem R8581 : Reach 8581 := rs (se 4 (by rfl) ⟨804, by rfl⟩) R1609
theorem R8583 : Reach 8583 := rs (se 1 (by rfl) ⟨6437, by rfl⟩) R12875
theorem R8591 : Reach 8591 := rs (se 1 (by rfl) ⟨6443, by rfl⟩) R12887
theorem R8611 : Reach 8611 := rs (se 1 (by rfl) ⟨6458, by rfl⟩) R12917
theorem R8613 : Reach 8613 := rs (se 4 (by rfl) ⟨807, by rfl⟩) R1615
theorem R8615 : Reach 8615 := rs (se 1 (by rfl) ⟨6461, by rfl⟩) R12923
theorem R8623 : Reach 8623 := rs (se 1 (by rfl) ⟨6467, by rfl⟩) R12935
theorem R8677 : Reach 8677 := rs (se 4 (by rfl) ⟨813, by rfl⟩) R1627
theorem R8681 : Reach 8681 := rs (se 2 (by rfl) ⟨3255, by rfl⟩) R6511
theorem R8701 : Reach 8701 := rs (se 3 (by rfl) ⟨1631, by rfl⟩) R3263
theorem R8749 : Reach 8749 := rs (se 3 (by rfl) ⟨1640, by rfl⟩) R3281
theorem R8753 : Reach 8753 := rs (se 2 (by rfl) ⟨3282, by rfl⟩) R6565
theorem R8755 : Reach 8755 := rs (se 1 (by rfl) ⟨6566, by rfl⟩) R13133
theorem R8765 : Reach 8765 := rs (se 3 (by rfl) ⟨1643, by rfl⟩) R3287
theorem R8767 : Reach 8767 := rs (se 1 (by rfl) ⟨6575, by rfl⟩) R13151
theorem R8801 : Reach 8801 := rs (se 2 (by rfl) ⟨3300, by rfl⟩) R6601
theorem R8807 : Reach 8807 := rs (se 1 (by rfl) ⟨6605, by rfl⟩) R13211
theorem R8809 : Reach 8809 := rs (se 2 (by rfl) ⟨3303, by rfl⟩) R6607
theorem R8819 : Reach 8819 := rs (se 1 (by rfl) ⟨6614, by rfl⟩) R13229
theorem R8833 : Reach 8833 := rs (se 2 (by rfl) ⟨3312, by rfl⟩) R6625
theorem R8837 : Reach 8837 := rs (se 4 (by rfl) ⟨828, by rfl⟩) R1657
theorem R8839 : Reach 8839 := rs (se 1 (by rfl) ⟨6629, by rfl⟩) R13259
theorem R8843 : Reach 8843 := rs (se 1 (by rfl) ⟨6632, by rfl⟩) R13265
theorem R8847 : Reach 8847 := rs (se 1 (by rfl) ⟨6635, by rfl⟩) R13271
theorem R8859 : Reach 8859 := rs (se 1 (by rfl) ⟨6644, by rfl⟩) R13289
theorem R8863 : Reach 8863 := rs (se 1 (by rfl) ⟨6647, by rfl⟩) R13295
theorem R8869 : Reach 8869 := rs (se 4 (by rfl) ⟨831, by rfl⟩) R1663
theorem R8871 : Reach 8871 := rs (se 1 (by rfl) ⟨6653, by rfl⟩) R13307
theorem R8989 : Reach 8989 := rs (se 3 (by rfl) ⟨1685, by rfl⟩) R3371
theorem R8993 : Reach 8993 := rs (se 2 (by rfl) ⟨3372, by rfl⟩) R6745
theorem R9003 : Reach 9003 := rs (se 1 (by rfl) ⟨6752, by rfl⟩) R13505
theorem R9007 : Reach 9007 := rs (se 1 (by rfl) ⟨6755, by rfl⟩) R13511
theorem R140089 : Reach 140089 := rs (se 2 (by rfl) ⟨52533, by rfl⟩) R105067
theorem R140129 : Reach 140129 := rs (se 2 (by rfl) ⟨52548, by rfl⟩) R105097
theorem R9057 : Reach 9057 := rs (se 2 (by rfl) ⟨3396, by rfl⟩) R6793
theorem R42119 : Reach 42119 := rs (se 1 (by rfl) ⟨31589, by rfl⟩) R63179
theorem R42203 : Reach 42203 := rs (se 1 (by rfl) ⟨31652, by rfl⟩) R63305
theorem R9493 : Reach 9493 := rs (se 6 (by rfl) ⟨222, by rfl⟩) R445
theorem R9517 : Reach 9517 := rs (se 3 (by rfl) ⟨1784, by rfl⟩) R3569
theorem R9525 : Reach 9525 := rs (se 5 (by rfl) ⟨446, by rfl⟩) R893
theorem R9531 : Reach 9531 := rs (se 1 (by rfl) ⟨7148, by rfl⟩) R14297
theorem R9537 : Reach 9537 := rs (se 2 (by rfl) ⟨3576, by rfl⟩) R7153
theorem R9539 : Reach 9539 := rs (se 1 (by rfl) ⟨7154, by rfl⟩) R14309
theorem R9545 : Reach 9545 := rs (se 2 (by rfl) ⟨3579, by rfl⟩) R7159
theorem R9559 : Reach 9559 := rs (se 1 (by rfl) ⟨7169, by rfl⟩) R14339
theorem R9561 : Reach 9561 := rs (se 2 (by rfl) ⟨3585, by rfl⟩) R7171
theorem R9567 : Reach 9567 := rs (se 1 (by rfl) ⟨7175, by rfl⟩) R14351
theorem R9569 : Reach 9569 := rs (se 2 (by rfl) ⟨3588, by rfl⟩) R7177
theorem R141335 : Reach 141335 := rs (se 1 (by rfl) ⟨106001, by rfl⟩) R212003
theorem R141425 : Reach 141425 := rs (se 2 (by rfl) ⟨53034, by rfl⟩) R106069
theorem R10537 : Reach 10537 := rs (se 2 (by rfl) ⟨3951, by rfl⟩) R7903
theorem R10559 : Reach 10559 := rs (se 1 (by rfl) ⟨7919, by rfl⟩) R15839
theorem R10575 : Reach 10575 := rs (se 1 (by rfl) ⟨7931, by rfl⟩) R15863
theorem R76301 : Reach 76301 := rs (se 3 (by rfl) ⟨14306, by rfl⟩) R28613
theorem R76477 : Reach 76477 := rs (se 3 (by rfl) ⟨14339, by rfl⟩) R28679
theorem R78245 : Reach 78245 := rs (se 4 (by rfl) ⟨7335, by rfl⟩) R14671
theorem R144935 : Reach 144935 := rs (se 1 (by rfl) ⟨108701, by rfl⟩) R217403
theorem R17015 : Reach 17015 := rs (se 1 (by rfl) ⟨12761, by rfl⟩) R25523
theorem R17045 : Reach 17045 := rs (se 6 (by rfl) ⟨399, by rfl⟩) R799
theorem R17057 : Reach 17057 := rs (se 2 (by rfl) ⟨6396, by rfl⟩) R12793
theorem R17063 : Reach 17063 := rs (se 1 (by rfl) ⟨12797, by rfl⟩) R25595
theorem R17117 : Reach 17117 := rs (se 3 (by rfl) ⟨3209, by rfl⟩) R6419
theorem R17129 : Reach 17129 := rs (se 2 (by rfl) ⟨6423, by rfl⟩) R12847
theorem R17165 : Reach 17165 := rs (se 3 (by rfl) ⟨3218, by rfl⟩) R6437
theorem R17185 : Reach 17185 := rs (se 2 (by rfl) ⟨6444, by rfl⟩) R12889
theorem R17225 : Reach 17225 := rs (se 2 (by rfl) ⟨6459, by rfl⟩) R12919
theorem R17231 : Reach 17231 := rs (se 1 (by rfl) ⟨12923, by rfl⟩) R25847
theorem R17357 : Reach 17357 := rs (se 3 (by rfl) ⟨3254, by rfl⟩) R6509
theorem R17363 : Reach 17363 := rs (se 1 (by rfl) ⟨13022, by rfl⟩) R26045
theorem R17401 : Reach 17401 := rs (se 2 (by rfl) ⟨6525, by rfl⟩) R13051
theorem R17405 : Reach 17405 := rs (se 3 (by rfl) ⟨3263, by rfl⟩) R6527
theorem R17455 : Reach 17455 := rs (se 1 (by rfl) ⟨13091, by rfl⟩) R26183
theorem R17501 : Reach 17501 := rs (se 3 (by rfl) ⟨3281, by rfl⟩) R6563
theorem R17507 : Reach 17507 := rs (se 1 (by rfl) ⟨13130, by rfl⟩) R26261
theorem R17509 : Reach 17509 := rs (se 4 (by rfl) ⟨1641, by rfl⟩) R3283
theorem R17513 : Reach 17513 := rs (se 2 (by rfl) ⟨6567, by rfl⟩) R13135
theorem R17519 : Reach 17519 := rs (se 1 (by rfl) ⟨13139, by rfl⟩) R26279
theorem R17525 : Reach 17525 := rs (se 5 (by rfl) ⟨821, by rfl⟩) R1643
theorem R17543 : Reach 17543 := rs (se 1 (by rfl) ⟨13157, by rfl⟩) R26315
theorem R17567 : Reach 17567 := rs (se 1 (by rfl) ⟨13175, by rfl⟩) R26351
theorem R17603 : Reach 17603 := rs (se 1 (by rfl) ⟨13202, by rfl⟩) R26405
theorem R17615 : Reach 17615 := rs (se 1 (by rfl) ⟨13211, by rfl⟩) R26423
theorem R17617 : Reach 17617 := rs (se 2 (by rfl) ⟨6606, by rfl⟩) R13213
theorem R17639 : Reach 17639 := rs (se 1 (by rfl) ⟨13229, by rfl⟩) R26459
theorem R17671 : Reach 17671 := rs (se 1 (by rfl) ⟨13253, by rfl⟩) R26507
theorem R17675 : Reach 17675 := rs (se 1 (by rfl) ⟨13256, by rfl⟩) R26513
theorem R17681 : Reach 17681 := rs (se 2 (by rfl) ⟨6630, by rfl⟩) R13261
theorem R17687 : Reach 17687 := rs (se 1 (by rfl) ⟨13265, by rfl⟩) R26531
theorem R17693 : Reach 17693 := rs (se 3 (by rfl) ⟨3317, by rfl⟩) R6635
theorem R17705 : Reach 17705 := rs (se 2 (by rfl) ⟨6639, by rfl⟩) R13279
theorem R17711 : Reach 17711 := rs (se 1 (by rfl) ⟨13283, by rfl⟩) R26567
theorem R17741 : Reach 17741 := rs (se 3 (by rfl) ⟨3326, by rfl⟩) R6653
theorem R17981 : Reach 17981 := rs (se 3 (by rfl) ⟨3371, by rfl⟩) R6743
theorem R17987 : Reach 17987 := rs (se 1 (by rfl) ⟨13490, by rfl⟩) R26981
theorem R18185 : Reach 18185 := rs (se 2 (by rfl) ⟨6819, by rfl⟩) R13639
theorem R84199 : Reach 84199 := rs (se 1 (by rfl) ⟨63149, by rfl⟩) R126299
theorem R19037 : Reach 19037 := rs (se 3 (by rfl) ⟨3569, by rfl⟩) R7139
theorem R19075 : Reach 19075 := rs (se 1 (by rfl) ⟨14306, by rfl⟩) R28613
theorem R19079 : Reach 19079 := rs (se 1 (by rfl) ⟨14309, by rfl⟩) R28619
theorem R19091 : Reach 19091 := rs (se 1 (by rfl) ⟨14318, by rfl⟩) R28637
theorem R19115 : Reach 19115 := rs (se 1 (by rfl) ⟨14336, by rfl⟩) R28673
theorem R19121 : Reach 19121 := rs (se 2 (by rfl) ⟨7170, by rfl⟩) R14341
theorem R19129 : Reach 19129 := rs (se 2 (by rfl) ⟨7173, by rfl⟩) R14347
theorem R19133 : Reach 19133 := rs (se 3 (by rfl) ⟨3587, by rfl⟩) R7175
theorem R19139 : Reach 19139 := rs (se 1 (by rfl) ⟨14354, by rfl⟩) R28709
theorem R19211 : Reach 19211 := rs (se 1 (by rfl) ⟨14408, by rfl⟩) R28817
theorem R19399 : Reach 19399 := rs (se 1 (by rfl) ⟨14549, by rfl⟩) R29099
theorem R19561 : Reach 19561 := rs (se 2 (by rfl) ⟨7335, by rfl⟩) R14671
theorem R282329 : Reach 282329 := rs (se 2 (by rfl) ⟨105873, by rfl⟩) R211747
theorem R21073 : Reach 21073 := rs (se 2 (by rfl) ⟨7902, by rfl⟩) R15805
theorem R21149 : Reach 21149 := rs (se 3 (by rfl) ⟨3965, by rfl⟩) R7931
theorem R154183 : Reach 154183 := rs (se 1 (by rfl) ⟨115637, by rfl⟩) R231275
theorem R156653 : Reach 156653 := rs (se 3 (by rfl) ⟨29372, by rfl⟩) R58745
theorem R395 : Reach 395 := rs (se 1 (by rfl) ⟨296, by rfl⟩) R593
theorem R791 : Reach 791 := rs (se 1 (by rfl) ⟨593, by rfl⟩) R1187
theorem R793 : Reach 793 := rs (se 2 (by rfl) ⟨297, by rfl⟩) R595
theorem R1417 : Reach 1417 := rs (se 2 (by rfl) ⟨531, by rfl⟩) R1063
theorem R1435 : Reach 1435 := rs (se 1 (by rfl) ⟨1076, by rfl⟩) R2153
theorem R1581 : Reach 1581 := rs (se 3 (by rfl) ⟨296, by rfl⟩) R593
theorem R1585 : Reach 1585 := rs (se 2 (by rfl) ⟨594, by rfl⟩) R1189
theorem R1587 : Reach 1587 := rs (se 1 (by rfl) ⟨1190, by rfl⟩) R2381
theorem R2835 : Reach 2835 := rs (se 1 (by rfl) ⟨2126, by rfl⟩) R4253
theorem R2841 : Reach 2841 := rs (se 2 (by rfl) ⟨1065, by rfl⟩) R2131
theorem R2859 : Reach 2859 := rs (se 1 (by rfl) ⟨2144, by rfl⟩) R4289
theorem R2863 : Reach 2863 := rs (se 1 (by rfl) ⟨2147, by rfl⟩) R4295
theorem R2871 : Reach 2871 := rs (se 1 (by rfl) ⟨2153, by rfl⟩) R4307
theorem R2921 : Reach 2921 := rs (se 2 (by rfl) ⟨1095, by rfl⟩) R2191
theorem R2939 : Reach 2939 := rs (se 1 (by rfl) ⟨2204, by rfl⟩) R4409
theorem R2945 : Reach 2945 := rs (se 2 (by rfl) ⟨1104, by rfl⟩) R2209
theorem R3165 : Reach 3165 := rs (se 3 (by rfl) ⟨593, by rfl⟩) R1187
theorem R3171 : Reach 3171 := rs (se 1 (by rfl) ⟨2378, by rfl⟩) R4757
theorem R3173 : Reach 3173 := rs (se 4 (by rfl) ⟨297, by rfl⟩) R595
theorem R3179 : Reach 3179 := rs (se 1 (by rfl) ⟨2384, by rfl⟩) R4769
theorem R3519 : Reach 3519 := rs (se 1 (by rfl) ⟨2639, by rfl⟩) R5279
theorem R101969 : Reach 101969 := rs (se 2 (by rfl) ⟨38238, by rfl⟩) R76477
theorem R5669 : Reach 5669 := rs (se 4 (by rfl) ⟨531, by rfl⟩) R1063
theorem R5671 : Reach 5671 := rs (se 1 (by rfl) ⟨4253, by rfl⟩) R8507
theorem R5681 : Reach 5681 := rs (se 2 (by rfl) ⟨2130, by rfl⟩) R4261
theorem R5683 : Reach 5683 := rs (se 1 (by rfl) ⟨4262, by rfl⟩) R8525
theorem R5705 : Reach 5705 := rs (se 2 (by rfl) ⟨2139, by rfl⟩) R4279
theorem R5719 : Reach 5719 := rs (se 1 (by rfl) ⟨4289, by rfl⟩) R8579
theorem R5721 : Reach 5721 := rs (se 2 (by rfl) ⟨2145, by rfl⟩) R4291
theorem R5727 : Reach 5727 := rs (se 1 (by rfl) ⟨4295, by rfl⟩) R8591
theorem R5741 : Reach 5741 := rs (se 3 (by rfl) ⟨1076, by rfl⟩) R2153
theorem R5743 : Reach 5743 := rs (se 1 (by rfl) ⟨4307, by rfl⟩) R8615
theorem R5785 : Reach 5785 := rs (se 2 (by rfl) ⟨2169, by rfl⟩) R4339
theorem R5787 : Reach 5787 := rs (se 1 (by rfl) ⟨4340, by rfl⟩) R8681
theorem R5801 : Reach 5801 := rs (se 2 (by rfl) ⟨2175, by rfl⟩) R4351
theorem R5833 : Reach 5833 := rs (se 2 (by rfl) ⟨2187, by rfl⟩) R4375
theorem R5835 : Reach 5835 := rs (se 1 (by rfl) ⟨4376, by rfl⟩) R8753
theorem R5841 : Reach 5841 := rs (se 2 (by rfl) ⟨2190, by rfl⟩) R4381
theorem R5843 : Reach 5843 := rs (se 1 (by rfl) ⟨4382, by rfl⟩) R8765
theorem R5867 : Reach 5867 := rs (se 1 (by rfl) ⟨4400, by rfl⟩) R8801
theorem R5871 : Reach 5871 := rs (se 1 (by rfl) ⟨4403, by rfl⟩) R8807
theorem R5879 : Reach 5879 := rs (se 1 (by rfl) ⟨4409, by rfl⟩) R8819
theorem R5891 : Reach 5891 := rs (se 1 (by rfl) ⟨4418, by rfl⟩) R8837
theorem R5895 : Reach 5895 := rs (se 1 (by rfl) ⟨4421, by rfl⟩) R8843
theorem R5897 : Reach 5897 := rs (se 2 (by rfl) ⟨2211, by rfl⟩) R4423
theorem R5913 : Reach 5913 := rs (se 2 (by rfl) ⟨2217, by rfl⟩) R4435
theorem R5993 : Reach 5993 := rs (se 2 (by rfl) ⟨2247, by rfl⟩) R4495
theorem R5995 : Reach 5995 := rs (se 1 (by rfl) ⟨4496, by rfl⟩) R8993
theorem R104435 : Reach 104435 := rs (se 1 (by rfl) ⟨78326, by rfl⟩) R156653
theorem R6325 : Reach 6325 := rs (se 5 (by rfl) ⟨296, by rfl⟩) R593
theorem R6341 : Reach 6341 := rs (se 4 (by rfl) ⟨594, by rfl⟩) R1189
theorem R6345 : Reach 6345 := rs (se 2 (by rfl) ⟨2379, by rfl⟩) R4759
theorem R6349 : Reach 6349 := rs (se 3 (by rfl) ⟨1190, by rfl⟩) R2381
theorem R6359 : Reach 6359 := rs (se 1 (by rfl) ⟨4769, by rfl⟩) R9539
theorem R6363 : Reach 6363 := rs (se 1 (by rfl) ⟨4772, by rfl⟩) R9545
theorem R6377 : Reach 6377 := rs (se 2 (by rfl) ⟨2391, by rfl⟩) R4783
theorem R6379 : Reach 6379 := rs (se 1 (by rfl) ⟨4784, by rfl⟩) R9569
theorem R7039 : Reach 7039 := rs (se 1 (by rfl) ⟨5279, by rfl⟩) R10559
theorem R7049 : Reach 7049 := rs (se 2 (by rfl) ⟨2643, by rfl⟩) R5287
theorem R205577 : Reach 205577 := rs (se 2 (by rfl) ⟨77091, by rfl⟩) R154183
theorem R11341 : Reach 11341 := rs (se 3 (by rfl) ⟨2126, by rfl⟩) R4253
theorem R11343 : Reach 11343 := rs (se 1 (by rfl) ⟨8507, by rfl⟩) R17015
theorem R11345 : Reach 11345 := rs (se 2 (by rfl) ⟨4254, by rfl⟩) R8509
theorem R11361 : Reach 11361 := rs (se 2 (by rfl) ⟨4260, by rfl⟩) R8521
theorem R11363 : Reach 11363 := rs (se 1 (by rfl) ⟨8522, by rfl⟩) R17045
theorem R11365 : Reach 11365 := rs (se 4 (by rfl) ⟨1065, by rfl⟩) R2131
theorem R11371 : Reach 11371 := rs (se 1 (by rfl) ⟨8528, by rfl⟩) R17057
theorem R11375 : Reach 11375 := rs (se 1 (by rfl) ⟨8531, by rfl⟩) R17063
theorem R11401 : Reach 11401 := rs (se 2 (by rfl) ⟨4275, by rfl⟩) R8551
theorem R11409 : Reach 11409 := rs (se 2 (by rfl) ⟨4278, by rfl⟩) R8557
theorem R11411 : Reach 11411 := rs (se 1 (by rfl) ⟨8558, by rfl⟩) R17117
theorem R11419 : Reach 11419 := rs (se 1 (by rfl) ⟨8564, by rfl⟩) R17129
theorem R11425 : Reach 11425 := rs (se 2 (by rfl) ⟨4284, by rfl⟩) R8569
theorem R11437 : Reach 11437 := rs (se 3 (by rfl) ⟨2144, by rfl⟩) R4289
theorem R11441 : Reach 11441 := rs (se 2 (by rfl) ⟨4290, by rfl⟩) R8581
theorem R11443 : Reach 11443 := rs (se 1 (by rfl) ⟨8582, by rfl⟩) R17165
theorem R11453 : Reach 11453 := rs (se 3 (by rfl) ⟨2147, by rfl⟩) R4295
theorem R11481 : Reach 11481 := rs (se 2 (by rfl) ⟨4305, by rfl⟩) R8611
theorem R11483 : Reach 11483 := rs (se 1 (by rfl) ⟨8612, by rfl⟩) R17225
theorem R11485 : Reach 11485 := rs (se 3 (by rfl) ⟨2153, by rfl⟩) R4307
theorem R11487 : Reach 11487 := rs (se 1 (by rfl) ⟨8615, by rfl⟩) R17231
theorem R11497 : Reach 11497 := rs (se 2 (by rfl) ⟨4311, by rfl⟩) R8623
theorem R11569 : Reach 11569 := rs (se 2 (by rfl) ⟨4338, by rfl⟩) R8677
theorem R11571 : Reach 11571 := rs (se 1 (by rfl) ⟨8678, by rfl⟩) R17357
theorem R11575 : Reach 11575 := rs (se 1 (by rfl) ⟨8681, by rfl⟩) R17363
theorem R11601 : Reach 11601 := rs (se 2 (by rfl) ⟨4350, by rfl⟩) R8701
theorem R11603 : Reach 11603 := rs (se 1 (by rfl) ⟨8702, by rfl⟩) R17405
theorem R11665 : Reach 11665 := rs (se 2 (by rfl) ⟨4374, by rfl⟩) R8749
theorem R11667 : Reach 11667 := rs (se 1 (by rfl) ⟨8750, by rfl⟩) R17501
theorem R11671 : Reach 11671 := rs (se 1 (by rfl) ⟨8753, by rfl⟩) R17507
theorem R11673 : Reach 11673 := rs (se 2 (by rfl) ⟨4377, by rfl⟩) R8755
theorem R11675 : Reach 11675 := rs (se 1 (by rfl) ⟨8756, by rfl⟩) R17513
theorem R11679 : Reach 11679 := rs (se 1 (by rfl) ⟨8759, by rfl⟩) R17519
theorem R11683 : Reach 11683 := rs (se 1 (by rfl) ⟨8762, by rfl⟩) R17525
theorem R11685 : Reach 11685 := rs (se 4 (by rfl) ⟨1095, by rfl⟩) R2191
theorem R11689 : Reach 11689 := rs (se 2 (by rfl) ⟨4383, by rfl⟩) R8767
theorem R11695 : Reach 11695 := rs (se 1 (by rfl) ⟨8771, by rfl⟩) R17543
theorem R11711 : Reach 11711 := rs (se 1 (by rfl) ⟨8783, by rfl⟩) R17567
theorem R11735 : Reach 11735 := rs (se 1 (by rfl) ⟨8801, by rfl⟩) R17603
theorem R11743 : Reach 11743 := rs (se 1 (by rfl) ⟨8807, by rfl⟩) R17615
theorem R11745 : Reach 11745 := rs (se 2 (by rfl) ⟨4404, by rfl⟩) R8809
theorem R11757 : Reach 11757 := rs (se 3 (by rfl) ⟨2204, by rfl⟩) R4409
theorem R11759 : Reach 11759 := rs (se 1 (by rfl) ⟨8819, by rfl⟩) R17639
theorem R11777 : Reach 11777 := rs (se 2 (by rfl) ⟨4416, by rfl⟩) R8833
theorem R11781 : Reach 11781 := rs (se 4 (by rfl) ⟨1104, by rfl⟩) R2209
theorem R11783 : Reach 11783 := rs (se 1 (by rfl) ⟨8837, by rfl⟩) R17675
theorem R11785 : Reach 11785 := rs (se 2 (by rfl) ⟨4419, by rfl⟩) R8839
theorem R11787 : Reach 11787 := rs (se 1 (by rfl) ⟨8840, by rfl⟩) R17681
theorem R11791 : Reach 11791 := rs (se 1 (by rfl) ⟨8843, by rfl⟩) R17687
theorem R11795 : Reach 11795 := rs (se 1 (by rfl) ⟨8846, by rfl⟩) R17693
theorem R11803 : Reach 11803 := rs (se 1 (by rfl) ⟨8852, by rfl⟩) R17705
theorem R11807 : Reach 11807 := rs (se 1 (by rfl) ⟨8855, by rfl⟩) R17711
theorem R11817 : Reach 11817 := rs (se 2 (by rfl) ⟨4431, by rfl⟩) R8863
theorem R11825 : Reach 11825 := rs (se 2 (by rfl) ⟨4434, by rfl⟩) R8869
theorem R11827 : Reach 11827 := rs (se 1 (by rfl) ⟨8870, by rfl⟩) R17741
theorem R11985 : Reach 11985 := rs (se 2 (by rfl) ⟨4494, by rfl⟩) R8989
theorem R11987 : Reach 11987 := rs (se 1 (by rfl) ⟨8990, by rfl⟩) R17981
theorem R11991 : Reach 11991 := rs (se 1 (by rfl) ⟨8993, by rfl⟩) R17987
theorem R12009 : Reach 12009 := rs (se 2 (by rfl) ⟨4503, by rfl⟩) R9007
theorem R12123 : Reach 12123 := rs (se 1 (by rfl) ⟨9092, by rfl⟩) R18185
theorem R12657 : Reach 12657 := rs (se 2 (by rfl) ⟨4746, by rfl⟩) R9493
theorem R12661 : Reach 12661 := rs (se 5 (by rfl) ⟨593, by rfl⟩) R1187
theorem R12685 : Reach 12685 := rs (se 3 (by rfl) ⟨2378, by rfl⟩) R4757
theorem R12689 : Reach 12689 := rs (se 2 (by rfl) ⟨4758, by rfl⟩) R9517
theorem R12691 : Reach 12691 := rs (se 1 (by rfl) ⟨9518, by rfl⟩) R19037
theorem R12693 : Reach 12693 := rs (se 6 (by rfl) ⟨297, by rfl⟩) R595
theorem R12717 : Reach 12717 := rs (se 3 (by rfl) ⟨2384, by rfl⟩) R4769
theorem R12719 : Reach 12719 := rs (se 1 (by rfl) ⟨9539, by rfl⟩) R19079
theorem R12727 : Reach 12727 := rs (se 1 (by rfl) ⟨9545, by rfl⟩) R19091
theorem R12743 : Reach 12743 := rs (se 1 (by rfl) ⟨9557, by rfl⟩) R19115
theorem R12745 : Reach 12745 := rs (se 2 (by rfl) ⟨4779, by rfl⟩) R9559
theorem R12747 : Reach 12747 := rs (se 1 (by rfl) ⟨9560, by rfl⟩) R19121
theorem R12755 : Reach 12755 := rs (se 1 (by rfl) ⟨9566, by rfl⟩) R19133
theorem R12759 : Reach 12759 := rs (se 1 (by rfl) ⟨9569, by rfl⟩) R19139
theorem R12807 : Reach 12807 := rs (se 1 (by rfl) ⟨9605, by rfl⟩) R19211
theorem R45623 : Reach 45623 := rs (se 1 (by rfl) ⟨34217, by rfl⟩) R68435
theorem R45815 : Reach 45815 := rs (se 1 (by rfl) ⟨34361, by rfl⟩) R68723
theorem R46277 : Reach 46277 := rs (se 4 (by rfl) ⟨4338, by rfl⟩) R8677
theorem R46331 : Reach 46331 := rs (se 1 (by rfl) ⟨34748, by rfl⟩) R69497
theorem R112265 : Reach 112265 := rs (se 2 (by rfl) ⟨42099, by rfl⟩) R84199
theorem R46763 : Reach 46763 := rs (se 1 (by rfl) ⟨35072, by rfl⟩) R70145
theorem R46777 : Reach 46777 := rs (se 2 (by rfl) ⟨17541, by rfl⟩) R35083
theorem R14099 : Reach 14099 := rs (se 1 (by rfl) ⟨10574, by rfl⟩) R21149
theorem R46919 : Reach 46919 := rs (se 1 (by rfl) ⟨35189, by rfl⟩) R70379
theorem R46979 : Reach 46979 := rs (se 1 (by rfl) ⟨35234, by rfl⟩) R70469
theorem R47141 : Reach 47141 := rs (se 4 (by rfl) ⟨4419, by rfl⟩) R8839
theorem R47249 : Reach 47249 := rs (se 2 (by rfl) ⟨17718, by rfl⟩) R35437
theorem R48023 : Reach 48023 := rs (se 1 (by rfl) ⟨36017, by rfl⟩) R72035
theorem R49247 : Reach 49247 := rs (se 1 (by rfl) ⟨36935, by rfl⟩) R73871
theorem R50867 : Reach 50867 := rs (se 1 (by rfl) ⟨38150, by rfl⟩) R76301
theorem R52163 : Reach 52163 := rs (se 1 (by rfl) ⟨39122, by rfl⟩) R78245
theorem R22733 : Reach 22733 := rs (se 3 (by rfl) ⟨4262, by rfl⟩) R8525
theorem R22751 : Reach 22751 := rs (se 1 (by rfl) ⟨17063, by rfl⟩) R34127
theorem R22877 : Reach 22877 := rs (se 3 (by rfl) ⟨4289, by rfl⟩) R8579
theorem R22913 : Reach 22913 := rs (se 2 (by rfl) ⟨8592, by rfl⟩) R17185
theorem R22943 : Reach 22943 := rs (se 1 (by rfl) ⟨17207, by rfl⟩) R34415
theorem R186785 : Reach 186785 := rs (se 2 (by rfl) ⟨70044, by rfl⟩) R140089
theorem R22963 : Reach 22963 := rs (se 1 (by rfl) ⟨17222, by rfl⟩) R34445
theorem R22967 : Reach 22967 := rs (se 1 (by rfl) ⟨17225, by rfl⟩) R34451
theorem R23201 : Reach 23201 := rs (se 2 (by rfl) ⟨8700, by rfl⟩) R17401
theorem R23203 : Reach 23203 := rs (se 1 (by rfl) ⟨17402, by rfl⟩) R34805
theorem R23273 : Reach 23273 := rs (se 2 (by rfl) ⟨8727, by rfl⟩) R17455
theorem R23345 : Reach 23345 := rs (se 2 (by rfl) ⟨8754, by rfl⟩) R17509
theorem R23399 : Reach 23399 := rs (se 1 (by rfl) ⟨17549, by rfl⟩) R35099
theorem R23471 : Reach 23471 := rs (se 1 (by rfl) ⟨17603, by rfl⟩) R35207
theorem R23485 : Reach 23485 := rs (se 3 (by rfl) ⟨4403, by rfl⟩) R8807
theorem R23489 : Reach 23489 := rs (se 2 (by rfl) ⟨8808, by rfl⟩) R17617
theorem R23561 : Reach 23561 := rs (se 2 (by rfl) ⟨8835, by rfl⟩) R17671
theorem R23591 : Reach 23591 := rs (se 1 (by rfl) ⟨17693, by rfl⟩) R35387
theorem R23611 : Reach 23611 := rs (se 1 (by rfl) ⟨17708, by rfl⟩) R35417
theorem R23615 : Reach 23615 := rs (se 1 (by rfl) ⟨17711, by rfl⟩) R35423
theorem R23651 : Reach 23651 := rs (se 1 (by rfl) ⟨17738, by rfl⟩) R35477
theorem R23687 : Reach 23687 := rs (se 1 (by rfl) ⟨17765, by rfl⟩) R35531
theorem R23971 : Reach 23971 := rs (se 1 (by rfl) ⟨17978, by rfl⟩) R35957
theorem R24011 : Reach 24011 := rs (se 1 (by rfl) ⟨18008, by rfl⟩) R36017
theorem R24155 : Reach 24155 := rs (se 1 (by rfl) ⟨18116, by rfl⟩) R36233
theorem R188219 : Reach 188219 := rs (se 1 (by rfl) ⟨141164, by rfl⟩) R282329
theorem R24623 : Reach 24623 := rs (se 1 (by rfl) ⟨18467, by rfl⟩) R36935
theorem R25379 : Reach 25379 := rs (se 1 (by rfl) ⟨19034, by rfl⟩) R38069
theorem R25397 : Reach 25397 := rs (se 5 (by rfl) ⟨1190, by rfl⟩) R2381
theorem R25433 : Reach 25433 := rs (se 2 (by rfl) ⟨9537, by rfl⟩) R19075
theorem R25451 : Reach 25451 := rs (se 1 (by rfl) ⟨19088, by rfl⟩) R38177
theorem R25487 : Reach 25487 := rs (se 1 (by rfl) ⟨19115, by rfl⟩) R38231
theorem R25505 : Reach 25505 := rs (se 2 (by rfl) ⟨9564, by rfl⟩) R19129
theorem R91307 : Reach 91307 := rs (se 1 (by rfl) ⟨68480, by rfl⟩) R136961
theorem R25865 : Reach 25865 := rs (se 2 (by rfl) ⟨9699, by rfl⟩) R19399
theorem R26081 : Reach 26081 := rs (se 2 (by rfl) ⟨9780, by rfl⟩) R19561
theorem R91853 : Reach 91853 := rs (se 3 (by rfl) ⟨17222, by rfl⟩) R34445
theorem R92825 : Reach 92825 := rs (se 2 (by rfl) ⟨34809, by rfl⟩) R69619
theorem R93419 : Reach 93419 := rs (se 1 (by rfl) ⟨70064, by rfl⟩) R140129
theorem R28079 : Reach 28079 := rs (se 1 (by rfl) ⟨21059, by rfl⟩) R42119
theorem R28097 : Reach 28097 := rs (se 2 (by rfl) ⟨10536, by rfl⟩) R21073
theorem R28135 : Reach 28135 := rs (se 1 (by rfl) ⟨21101, by rfl⟩) R42203
theorem R93905 : Reach 93905 := rs (se 2 (by rfl) ⟨35214, by rfl⟩) R70429
theorem R94223 : Reach 94223 := rs (se 1 (by rfl) ⟨70667, by rfl⟩) R141335
theorem R94283 : Reach 94283 := rs (se 1 (by rfl) ⟨70712, by rfl⟩) R141425
theorem R94445 : Reach 94445 := rs (se 3 (by rfl) ⟨17708, by rfl⟩) R35417
theorem R96623 : Reach 96623 := rs (se 1 (by rfl) ⟨72467, by rfl⟩) R144935
theorem R96713 : Reach 96713 := rs (se 2 (by rfl) ⟨36267, by rfl⟩) R72535
theorem R32831 : Reach 32831 := rs (se 1 (by rfl) ⟨24623, by rfl⟩) R49247
theorem R263 : Reach 263 := rs (se 1 (by rfl) ⟨197, by rfl⟩) R395
theorem R527 : Reach 527 := rs (se 1 (by rfl) ⟨395, by rfl⟩) R791
theorem R33749 : Reach 33749 := rs (se 7 (by rfl) ⟨395, by rfl⟩) R791
theorem R1053 : Reach 1053 := rs (se 3 (by rfl) ⟨197, by rfl⟩) R395
theorem R1057 : Reach 1057 := rs (se 2 (by rfl) ⟨396, by rfl⟩) R793
theorem R33911 : Reach 33911 := rs (se 1 (by rfl) ⟨25433, by rfl⟩) R50867
theorem R34013 : Reach 34013 := rs (se 3 (by rfl) ⟨6377, by rfl⟩) R12755
theorem R1889 : Reach 1889 := rs (se 2 (by rfl) ⟨708, by rfl⟩) R1417
theorem R1913 : Reach 1913 := rs (se 2 (by rfl) ⟨717, by rfl⟩) R1435
theorem R1947 : Reach 1947 := rs (se 1 (by rfl) ⟨1460, by rfl⟩) R2921
theorem R1959 : Reach 1959 := rs (se 1 (by rfl) ⟨1469, by rfl⟩) R2939
theorem R1963 : Reach 1963 := rs (se 1 (by rfl) ⟨1472, by rfl⟩) R2945
theorem R34775 : Reach 34775 := rs (se 1 (by rfl) ⟨26081, by rfl⟩) R52163
theorem R2109 : Reach 2109 := rs (se 3 (by rfl) ⟨395, by rfl⟩) R791
theorem R2113 : Reach 2113 := rs (se 2 (by rfl) ⟨792, by rfl⟩) R1585
theorem R2115 : Reach 2115 := rs (se 1 (by rfl) ⟨1586, by rfl⟩) R3173
theorem R2119 : Reach 2119 := rs (se 1 (by rfl) ⟨1589, by rfl⟩) R3179
theorem R67979 : Reach 67979 := rs (se 1 (by rfl) ⟨50984, by rfl⟩) R101969
theorem R3779 : Reach 3779 := rs (se 1 (by rfl) ⟨2834, by rfl⟩) R5669
theorem R3787 : Reach 3787 := rs (se 1 (by rfl) ⟨2840, by rfl⟩) R5681
theorem R3803 : Reach 3803 := rs (se 1 (by rfl) ⟨2852, by rfl⟩) R5705
theorem R3817 : Reach 3817 := rs (se 2 (by rfl) ⟨1431, by rfl⟩) R2863
theorem R3827 : Reach 3827 := rs (se 1 (by rfl) ⟨2870, by rfl⟩) R5741
theorem R3867 : Reach 3867 := rs (se 1 (by rfl) ⟨2900, by rfl⟩) R5801
theorem R3895 : Reach 3895 := rs (se 1 (by rfl) ⟨2921, by rfl⟩) R5843
theorem R3911 : Reach 3911 := rs (se 1 (by rfl) ⟨2933, by rfl⟩) R5867
theorem R3919 : Reach 3919 := rs (se 1 (by rfl) ⟨2939, by rfl⟩) R5879
theorem R3927 : Reach 3927 := rs (se 1 (by rfl) ⟨2945, by rfl⟩) R5891
theorem R3931 : Reach 3931 := rs (se 1 (by rfl) ⟨2948, by rfl⟩) R5897
theorem R3995 : Reach 3995 := rs (se 1 (by rfl) ⟨2996, by rfl⟩) R5993
theorem R69623 : Reach 69623 := rs (se 1 (by rfl) ⟨52217, by rfl⟩) R104435
theorem R4213 : Reach 4213 := rs (se 5 (by rfl) ⟨197, by rfl⟩) R395
theorem R4227 : Reach 4227 := rs (se 1 (by rfl) ⟨3170, by rfl⟩) R6341
theorem R4229 : Reach 4229 := rs (se 4 (by rfl) ⟨396, by rfl⟩) R793
theorem R4239 : Reach 4239 := rs (se 1 (by rfl) ⟨3179, by rfl⟩) R6359
theorem R4251 : Reach 4251 := rs (se 1 (by rfl) ⟨3188, by rfl⟩) R6377
theorem R4699 : Reach 4699 := rs (se 1 (by rfl) ⟨3524, by rfl⟩) R7049
theorem R37513 : Reach 37513 := rs (se 2 (by rfl) ⟨14067, by rfl⟩) R28135
theorem R137051 : Reach 137051 := rs (se 1 (by rfl) ⟨102788, by rfl⟩) R205577
theorem R7557 : Reach 7557 := rs (se 4 (by rfl) ⟨708, by rfl⟩) R1417
theorem R7561 : Reach 7561 := rs (se 2 (by rfl) ⟨2835, by rfl⟩) R5671
theorem R7563 : Reach 7563 := rs (se 1 (by rfl) ⟨5672, by rfl⟩) R11345
theorem R7575 : Reach 7575 := rs (se 1 (by rfl) ⟨5681, by rfl⟩) R11363
theorem R7577 : Reach 7577 := rs (se 2 (by rfl) ⟨2841, by rfl⟩) R5683
theorem R7583 : Reach 7583 := rs (se 1 (by rfl) ⟨5687, by rfl⟩) R11375
theorem R7607 : Reach 7607 := rs (se 1 (by rfl) ⟨5705, by rfl⟩) R11411
theorem R7625 : Reach 7625 := rs (se 2 (by rfl) ⟨2859, by rfl⟩) R5719
theorem R7627 : Reach 7627 := rs (se 1 (by rfl) ⟨5720, by rfl⟩) R11441
theorem R7635 : Reach 7635 := rs (se 1 (by rfl) ⟨5726, by rfl⟩) R11453
theorem R7653 : Reach 7653 := rs (se 4 (by rfl) ⟨717, by rfl⟩) R1435
theorem R7655 : Reach 7655 := rs (se 1 (by rfl) ⟨5741, by rfl⟩) R11483
theorem R7657 : Reach 7657 := rs (se 2 (by rfl) ⟨2871, by rfl⟩) R5743
theorem R7713 : Reach 7713 := rs (se 2 (by rfl) ⟨2892, by rfl⟩) R5785
theorem R7735 : Reach 7735 := rs (se 1 (by rfl) ⟨5801, by rfl⟩) R11603
theorem R7777 : Reach 7777 := rs (se 2 (by rfl) ⟨2916, by rfl⟩) R5833
theorem R7783 : Reach 7783 := rs (se 1 (by rfl) ⟨5837, by rfl⟩) R11675
theorem R7789 : Reach 7789 := rs (se 3 (by rfl) ⟨1460, by rfl⟩) R2921
theorem R7807 : Reach 7807 := rs (se 1 (by rfl) ⟨5855, by rfl⟩) R11711
theorem R7823 : Reach 7823 := rs (se 1 (by rfl) ⟨5867, by rfl⟩) R11735
theorem R7837 : Reach 7837 := rs (se 3 (by rfl) ⟨1469, by rfl⟩) R2939
theorem R7839 : Reach 7839 := rs (se 1 (by rfl) ⟨5879, by rfl⟩) R11759
theorem R7851 : Reach 7851 := rs (se 1 (by rfl) ⟨5888, by rfl⟩) R11777
theorem R7853 : Reach 7853 := rs (se 3 (by rfl) ⟨1472, by rfl⟩) R2945
theorem R7855 : Reach 7855 := rs (se 1 (by rfl) ⟨5891, by rfl⟩) R11783
theorem R7863 : Reach 7863 := rs (se 1 (by rfl) ⟨5897, by rfl⟩) R11795
theorem R7871 : Reach 7871 := rs (se 1 (by rfl) ⟨5903, by rfl⟩) R11807
theorem R7883 : Reach 7883 := rs (se 1 (by rfl) ⟨5912, by rfl⟩) R11825
theorem R7991 : Reach 7991 := rs (se 1 (by rfl) ⟨5993, by rfl⟩) R11987
theorem R7993 : Reach 7993 := rs (se 2 (by rfl) ⟨2997, by rfl⟩) R5995
theorem R8433 : Reach 8433 := rs (se 2 (by rfl) ⟨3162, by rfl⟩) R6325
theorem R8437 : Reach 8437 := rs (se 5 (by rfl) ⟨395, by rfl⟩) R791
theorem R8453 : Reach 8453 := rs (se 4 (by rfl) ⟨792, by rfl⟩) R1585
theorem R8459 : Reach 8459 := rs (se 1 (by rfl) ⟨6344, by rfl⟩) R12689
theorem R8461 : Reach 8461 := rs (se 3 (by rfl) ⟨1586, by rfl⟩) R3173
theorem R8465 : Reach 8465 := rs (se 2 (by rfl) ⟨3174, by rfl⟩) R6349
theorem R8477 : Reach 8477 := rs (se 3 (by rfl) ⟨1589, by rfl⟩) R3179
theorem R8479 : Reach 8479 := rs (se 1 (by rfl) ⟨6359, by rfl⟩) R12719
theorem R8495 : Reach 8495 := rs (se 1 (by rfl) ⟨6371, by rfl⟩) R12743
theorem R8503 : Reach 8503 := rs (se 1 (by rfl) ⟨6377, by rfl⟩) R12755
theorem R8505 : Reach 8505 := rs (se 2 (by rfl) ⟨3189, by rfl⟩) R6379
theorem R74843 : Reach 74843 := rs (se 1 (by rfl) ⟨56132, by rfl⟩) R112265
theorem R9385 : Reach 9385 := rs (se 2 (by rfl) ⟨3519, by rfl⟩) R7039
theorem R9399 : Reach 9399 := rs (se 1 (by rfl) ⟨7049, by rfl⟩) R14099
theorem R15149 : Reach 15149 := rs (se 3 (by rfl) ⟨2840, by rfl⟩) R5681
theorem R15155 : Reach 15155 := rs (se 1 (by rfl) ⟨11366, by rfl⟩) R22733
theorem R15161 : Reach 15161 := rs (se 2 (by rfl) ⟨5685, by rfl⟩) R11371
theorem R15167 : Reach 15167 := rs (se 1 (by rfl) ⟨11375, by rfl⟩) R22751
theorem R15233 : Reach 15233 := rs (se 2 (by rfl) ⟨5712, by rfl⟩) R11425
theorem R15251 : Reach 15251 := rs (se 1 (by rfl) ⟨11438, by rfl⟩) R22877
theorem R15257 : Reach 15257 := rs (se 2 (by rfl) ⟨5721, by rfl⟩) R11443
theorem R15269 : Reach 15269 := rs (se 4 (by rfl) ⟨1431, by rfl⟩) R2863
theorem R15275 : Reach 15275 := rs (se 1 (by rfl) ⟨11456, by rfl⟩) R22913
theorem R15295 : Reach 15295 := rs (se 1 (by rfl) ⟨11471, by rfl⟩) R22943
theorem R15311 : Reach 15311 := rs (se 1 (by rfl) ⟨11483, by rfl⟩) R22967
theorem R15329 : Reach 15329 := rs (se 2 (by rfl) ⟨5748, by rfl⟩) R11497
theorem R15425 : Reach 15425 := rs (se 2 (by rfl) ⟨5784, by rfl⟩) R11569
theorem R15467 : Reach 15467 := rs (se 1 (by rfl) ⟨11600, by rfl⟩) R23201
theorem R15515 : Reach 15515 := rs (se 1 (by rfl) ⟨11636, by rfl⟩) R23273
theorem R15563 : Reach 15563 := rs (se 1 (by rfl) ⟨11672, by rfl⟩) R23345
theorem R15581 : Reach 15581 := rs (se 3 (by rfl) ⟨2921, by rfl⟩) R5843
theorem R15593 : Reach 15593 := rs (se 2 (by rfl) ⟨5847, by rfl⟩) R11695
theorem R15599 : Reach 15599 := rs (se 1 (by rfl) ⟨11699, by rfl⟩) R23399
theorem R15647 : Reach 15647 := rs (se 1 (by rfl) ⟨11735, by rfl⟩) R23471
theorem R15659 : Reach 15659 := rs (se 1 (by rfl) ⟨11744, by rfl⟩) R23489
theorem R15677 : Reach 15677 := rs (se 3 (by rfl) ⟨2939, by rfl⟩) R5879
theorem R15707 : Reach 15707 := rs (se 1 (by rfl) ⟨11780, by rfl⟩) R23561
theorem R15709 : Reach 15709 := rs (se 3 (by rfl) ⟨2945, by rfl⟩) R5891
theorem R15713 : Reach 15713 := rs (se 2 (by rfl) ⟨5892, by rfl⟩) R11785
theorem R15725 : Reach 15725 := rs (se 3 (by rfl) ⟨2948, by rfl⟩) R5897
theorem R15727 : Reach 15727 := rs (se 1 (by rfl) ⟨11795, by rfl⟩) R23591
theorem R15737 : Reach 15737 := rs (se 2 (by rfl) ⟨5901, by rfl⟩) R11803
theorem R15743 : Reach 15743 := rs (se 1 (by rfl) ⟨11807, by rfl⟩) R23615
theorem R15767 : Reach 15767 := rs (se 1 (by rfl) ⟨11825, by rfl⟩) R23651
theorem R15791 : Reach 15791 := rs (se 1 (by rfl) ⟨11843, by rfl⟩) R23687
theorem R16007 : Reach 16007 := rs (se 1 (by rfl) ⟨12005, by rfl⟩) R24011
theorem R16103 : Reach 16103 := rs (se 1 (by rfl) ⟨12077, by rfl⟩) R24155
theorem R16415 : Reach 16415 := rs (se 1 (by rfl) ⟨12311, by rfl⟩) R24623
theorem R16853 : Reach 16853 := rs (se 7 (by rfl) ⟨197, by rfl⟩) R395
theorem R16913 : Reach 16913 := rs (se 2 (by rfl) ⟨6342, by rfl⟩) R12685
theorem R16919 : Reach 16919 := rs (se 1 (by rfl) ⟨12689, by rfl⟩) R25379
theorem R16931 : Reach 16931 := rs (se 1 (by rfl) ⟨12698, by rfl⟩) R25397
theorem R16955 : Reach 16955 := rs (se 1 (by rfl) ⟨12716, by rfl⟩) R25433
theorem R16967 : Reach 16967 := rs (se 1 (by rfl) ⟨12725, by rfl⟩) R25451
theorem R16969 : Reach 16969 := rs (se 2 (by rfl) ⟨6363, by rfl⟩) R12727
theorem R16991 : Reach 16991 := rs (se 1 (by rfl) ⟨12743, by rfl⟩) R25487
theorem R17003 : Reach 17003 := rs (se 1 (by rfl) ⟨12752, by rfl⟩) R25505
theorem R17243 : Reach 17243 := rs (se 1 (by rfl) ⟨12932, by rfl⟩) R25865
theorem R17387 : Reach 17387 := rs (se 1 (by rfl) ⟨13040, by rfl⟩) R26081
theorem R18719 : Reach 18719 := rs (se 1 (by rfl) ⟨14039, by rfl⟩) R28079
theorem R18731 : Reach 18731 := rs (se 1 (by rfl) ⟨14048, by rfl⟩) R28097
theorem R18797 : Reach 18797 := rs (se 3 (by rfl) ⟨3524, by rfl⟩) R7049
theorem R121013 : Reach 121013 := rs (se 5 (by rfl) ⟨5672, by rfl⟩) R11345
theorem R124523 : Reach 124523 := rs (se 1 (by rfl) ⟨93392, by rfl⟩) R186785
theorem R125479 : Reach 125479 := rs (se 1 (by rfl) ⟨94109, by rfl⟩) R188219
theorem R60871 : Reach 60871 := rs (se 1 (by rfl) ⟨45653, by rfl⟩) R91307
theorem R61235 : Reach 61235 := rs (se 1 (by rfl) ⟨45926, by rfl⟩) R91853
theorem R61883 : Reach 61883 := rs (se 1 (by rfl) ⟨46412, by rfl⟩) R92825
theorem R62279 : Reach 62279 := rs (se 1 (by rfl) ⟨46709, by rfl⟩) R93419
theorem R62369 : Reach 62369 := rs (se 2 (by rfl) ⟨23388, by rfl⟩) R46777
theorem R62603 : Reach 62603 := rs (se 1 (by rfl) ⟨46952, by rfl⟩) R93905
theorem R488693 : Reach 488693 := rs (se 5 (by rfl) ⟨22907, by rfl⟩) R45815
theorem R62815 : Reach 62815 := rs (se 1 (by rfl) ⟨47111, by rfl⟩) R94223
theorem R62855 : Reach 62855 := rs (se 1 (by rfl) ⟨47141, by rfl⟩) R94283
theorem R62963 : Reach 62963 := rs (se 1 (by rfl) ⟨47222, by rfl⟩) R94445
theorem R30253 : Reach 30253 := rs (se 3 (by rfl) ⟨5672, by rfl⟩) R11345
theorem R30415 : Reach 30415 := rs (se 1 (by rfl) ⟨22811, by rfl⟩) R45623
theorem R30509 : Reach 30509 := rs (se 3 (by rfl) ⟨5720, by rfl⟩) R11441
theorem R30617 : Reach 30617 := rs (se 2 (by rfl) ⟨11481, by rfl⟩) R22963
theorem R30851 : Reach 30851 := rs (se 1 (by rfl) ⟨23138, by rfl⟩) R46277
theorem R30887 : Reach 30887 := rs (se 1 (by rfl) ⟨23165, by rfl⟩) R46331
theorem R30937 : Reach 30937 := rs (se 2 (by rfl) ⟨11601, by rfl⟩) R23203
theorem R30941 : Reach 30941 := rs (se 3 (by rfl) ⟨5801, by rfl⟩) R11603
theorem R31157 : Reach 31157 := rs (se 5 (by rfl) ⟨1460, by rfl⟩) R2921
theorem R31175 : Reach 31175 := rs (se 1 (by rfl) ⟨23381, by rfl⟩) R46763
theorem R31279 : Reach 31279 := rs (se 1 (by rfl) ⟨23459, by rfl⟩) R46919
theorem R31313 : Reach 31313 := rs (se 2 (by rfl) ⟨11742, by rfl⟩) R23485
theorem R31319 : Reach 31319 := rs (se 1 (by rfl) ⟨23489, by rfl⟩) R46979
theorem R31427 : Reach 31427 := rs (se 1 (by rfl) ⟨23570, by rfl⟩) R47141
theorem R31481 : Reach 31481 := rs (se 2 (by rfl) ⟨11805, by rfl⟩) R23611
theorem R31499 : Reach 31499 := rs (se 1 (by rfl) ⟨23624, by rfl⟩) R47249
theorem R64415 : Reach 64415 := rs (se 1 (by rfl) ⟨48311, by rfl⟩) R96623
theorem R64475 : Reach 64475 := rs (se 1 (by rfl) ⟨48356, by rfl⟩) R96713
theorem R31961 : Reach 31961 := rs (se 2 (by rfl) ⟨11985, by rfl⟩) R23971
theorem R32015 : Reach 32015 := rs (se 1 (by rfl) ⟨24011, by rfl⟩) R48023
theorem R175 : Reach 175 := rs (se 1 (by rfl) ⟨131, by rfl⟩) R263
theorem R351 : Reach 351 := rs (se 1 (by rfl) ⟨263, by rfl⟩) R527
theorem R701 : Reach 701 := rs (se 3 (by rfl) ⟨131, by rfl⟩) R263
theorem R1259 : Reach 1259 := rs (se 1 (by rfl) ⟨944, by rfl⟩) R1889
theorem R1275 : Reach 1275 := rs (se 1 (by rfl) ⟨956, by rfl⟩) R1913
theorem R1405 : Reach 1405 := rs (se 3 (by rfl) ⟨263, by rfl⟩) R527
theorem R1409 : Reach 1409 := rs (se 2 (by rfl) ⟨528, by rfl⟩) R1057
theorem R2519 : Reach 2519 := rs (se 1 (by rfl) ⟨1889, by rfl⟩) R3779
theorem R2535 : Reach 2535 := rs (se 1 (by rfl) ⟨1901, by rfl⟩) R3803
theorem R2551 : Reach 2551 := rs (se 1 (by rfl) ⟨1913, by rfl⟩) R3827
theorem R2607 : Reach 2607 := rs (se 1 (by rfl) ⟨1955, by rfl⟩) R3911
theorem R2617 : Reach 2617 := rs (se 2 (by rfl) ⟨981, by rfl⟩) R1963
theorem R2663 : Reach 2663 := rs (se 1 (by rfl) ⟨1997, by rfl⟩) R3995
theorem R2805 : Reach 2805 := rs (se 5 (by rfl) ⟨131, by rfl⟩) R263
theorem R2817 : Reach 2817 := rs (se 2 (by rfl) ⟨1056, by rfl⟩) R2113
theorem R2819 : Reach 2819 := rs (se 1 (by rfl) ⟨2114, by rfl⟩) R4229
theorem R2825 : Reach 2825 := rs (se 2 (by rfl) ⟨1059, by rfl⟩) R2119
theorem R167305 : Reach 167305 := rs (se 2 (by rfl) ⟨62739, by rfl⟩) R125479
theorem R5037 : Reach 5037 := rs (se 3 (by rfl) ⟨944, by rfl⟩) R1889
theorem R5049 : Reach 5049 := rs (se 2 (by rfl) ⟨1893, by rfl⟩) R3787
theorem R5051 : Reach 5051 := rs (se 1 (by rfl) ⟨3788, by rfl⟩) R7577
theorem R5055 : Reach 5055 := rs (se 1 (by rfl) ⟨3791, by rfl⟩) R7583
theorem R5071 : Reach 5071 := rs (se 1 (by rfl) ⟨3803, by rfl⟩) R7607
theorem R5083 : Reach 5083 := rs (se 1 (by rfl) ⟨3812, by rfl⟩) R7625
theorem R5089 : Reach 5089 := rs (se 2 (by rfl) ⟨1908, by rfl⟩) R3817
theorem R5101 : Reach 5101 := rs (se 3 (by rfl) ⟨956, by rfl⟩) R1913
theorem R5103 : Reach 5103 := rs (se 1 (by rfl) ⟨3827, by rfl⟩) R7655
theorem R5193 : Reach 5193 := rs (se 2 (by rfl) ⟨1947, by rfl⟩) R3895
theorem R5215 : Reach 5215 := rs (se 1 (by rfl) ⟨3911, by rfl⟩) R7823
theorem R5225 : Reach 5225 := rs (se 2 (by rfl) ⟨1959, by rfl⟩) R3919
theorem R5235 : Reach 5235 := rs (se 1 (by rfl) ⟨3926, by rfl⟩) R7853
theorem R5241 : Reach 5241 := rs (se 2 (by rfl) ⟨1965, by rfl⟩) R3931
theorem R5247 : Reach 5247 := rs (se 1 (by rfl) ⟨3935, by rfl⟩) R7871
theorem R5255 : Reach 5255 := rs (se 1 (by rfl) ⟨3941, by rfl⟩) R7883
theorem R5327 : Reach 5327 := rs (se 1 (by rfl) ⟨3995, by rfl⟩) R7991
theorem R5617 : Reach 5617 := rs (se 2 (by rfl) ⟨2106, by rfl⟩) R4213
theorem R5621 : Reach 5621 := rs (se 5 (by rfl) ⟨263, by rfl⟩) R527
theorem R5635 : Reach 5635 := rs (se 1 (by rfl) ⟨4226, by rfl⟩) R8453
theorem R5637 : Reach 5637 := rs (se 4 (by rfl) ⟨528, by rfl⟩) R1057
theorem R5639 : Reach 5639 := rs (se 1 (by rfl) ⟨4229, by rfl⟩) R8459
theorem R5643 : Reach 5643 := rs (se 1 (by rfl) ⟨4232, by rfl⟩) R8465
theorem R5651 : Reach 5651 := rs (se 1 (by rfl) ⟨4238, by rfl⟩) R8477
theorem R5663 : Reach 5663 := rs (se 1 (by rfl) ⟨4247, by rfl⟩) R8495
theorem R6265 : Reach 6265 := rs (se 2 (by rfl) ⟨2349, by rfl⟩) R4699
theorem R40337 : Reach 40337 := rs (se 2 (by rfl) ⟨15126, by rfl⟩) R30253
theorem R40445 : Reach 40445 := rs (se 3 (by rfl) ⟨7583, by rfl⟩) R15167
theorem R40553 : Reach 40553 := rs (se 2 (by rfl) ⟨15207, by rfl⟩) R30415
theorem R40733 : Reach 40733 := rs (se 3 (by rfl) ⟨7637, by rfl⟩) R15275
theorem R40823 : Reach 40823 := rs (se 1 (by rfl) ⟨30617, by rfl⟩) R61235
theorem R40877 : Reach 40877 := rs (se 3 (by rfl) ⟨7664, by rfl⟩) R15329
theorem R41249 : Reach 41249 := rs (se 2 (by rfl) ⟨15468, by rfl⟩) R30937
theorem R41255 : Reach 41255 := rs (se 1 (by rfl) ⟨30941, by rfl⟩) R61883
theorem R41519 : Reach 41519 := rs (se 1 (by rfl) ⟨31139, by rfl⟩) R62279
theorem R41579 : Reach 41579 := rs (se 1 (by rfl) ⟨31184, by rfl⟩) R62369
theorem R41705 : Reach 41705 := rs (se 2 (by rfl) ⟨15639, by rfl⟩) R31279
theorem R41735 : Reach 41735 := rs (se 1 (by rfl) ⟨31301, by rfl⟩) R62603
theorem R41903 : Reach 41903 := rs (se 1 (by rfl) ⟨31427, by rfl⟩) R62855
theorem R41975 : Reach 41975 := rs (se 1 (by rfl) ⟨31481, by rfl⟩) R62963
theorem R10077 : Reach 10077 := rs (se 3 (by rfl) ⟨1889, by rfl⟩) R3779
theorem R10081 : Reach 10081 := rs (se 2 (by rfl) ⟨3780, by rfl⟩) R7561
theorem R10099 : Reach 10099 := rs (se 1 (by rfl) ⟨7574, by rfl⟩) R15149
theorem R10103 : Reach 10103 := rs (se 1 (by rfl) ⟨7577, by rfl⟩) R15155
theorem R10107 : Reach 10107 := rs (se 1 (by rfl) ⟨7580, by rfl⟩) R15161
theorem R10111 : Reach 10111 := rs (se 1 (by rfl) ⟨7583, by rfl⟩) R15167
theorem R10141 : Reach 10141 := rs (se 3 (by rfl) ⟨1901, by rfl⟩) R3803
theorem R10155 : Reach 10155 := rs (se 1 (by rfl) ⟨7616, by rfl⟩) R15233
theorem R10167 : Reach 10167 := rs (se 1 (by rfl) ⟨7625, by rfl⟩) R15251
theorem R10169 : Reach 10169 := rs (se 2 (by rfl) ⟨3813, by rfl⟩) R7627
theorem R10171 : Reach 10171 := rs (se 1 (by rfl) ⟨7628, by rfl⟩) R15257
theorem R42943 : Reach 42943 := rs (se 1 (by rfl) ⟨32207, by rfl⟩) R64415
theorem R10179 : Reach 10179 := rs (se 1 (by rfl) ⟨7634, by rfl⟩) R15269
theorem R10183 : Reach 10183 := rs (se 1 (by rfl) ⟨7637, by rfl⟩) R15275
theorem R10205 : Reach 10205 := rs (se 3 (by rfl) ⟨1913, by rfl⟩) R3827
theorem R10207 : Reach 10207 := rs (se 1 (by rfl) ⟨7655, by rfl⟩) R15311
theorem R10209 : Reach 10209 := rs (se 2 (by rfl) ⟨3828, by rfl⟩) R7657
theorem R42983 : Reach 42983 := rs (se 1 (by rfl) ⟨32237, by rfl⟩) R64475
theorem R10219 : Reach 10219 := rs (se 1 (by rfl) ⟨7664, by rfl⟩) R15329
theorem R10283 : Reach 10283 := rs (se 1 (by rfl) ⟨7712, by rfl⟩) R15425
theorem R10311 : Reach 10311 := rs (se 1 (by rfl) ⟨7733, by rfl⟩) R15467
theorem R10313 : Reach 10313 := rs (se 2 (by rfl) ⟨3867, by rfl⟩) R7735
theorem R10343 : Reach 10343 := rs (se 1 (by rfl) ⟨7757, by rfl⟩) R15515
theorem R10369 : Reach 10369 := rs (se 2 (by rfl) ⟨3888, by rfl⟩) R7777
theorem R10375 : Reach 10375 := rs (se 1 (by rfl) ⟨7781, by rfl⟩) R15563
theorem R10377 : Reach 10377 := rs (se 2 (by rfl) ⟨3891, by rfl⟩) R7783
theorem R10385 : Reach 10385 := rs (se 2 (by rfl) ⟨3894, by rfl⟩) R7789
theorem R10387 : Reach 10387 := rs (se 1 (by rfl) ⟨7790, by rfl⟩) R15581
theorem R10395 : Reach 10395 := rs (se 1 (by rfl) ⟨7796, by rfl⟩) R15593
theorem R10399 : Reach 10399 := rs (se 1 (by rfl) ⟨7799, by rfl⟩) R15599
theorem R10409 : Reach 10409 := rs (se 2 (by rfl) ⟨3903, by rfl⟩) R7807
theorem R10429 : Reach 10429 := rs (se 3 (by rfl) ⟨1955, by rfl⟩) R3911
theorem R10431 : Reach 10431 := rs (se 1 (by rfl) ⟨7823, by rfl⟩) R15647
theorem R10439 : Reach 10439 := rs (se 1 (by rfl) ⟨7829, by rfl⟩) R15659
theorem R10449 : Reach 10449 := rs (se 2 (by rfl) ⟨3918, by rfl⟩) R7837
theorem R10451 : Reach 10451 := rs (se 1 (by rfl) ⟨7838, by rfl⟩) R15677
theorem R10469 : Reach 10469 := rs (se 4 (by rfl) ⟨981, by rfl⟩) R1963
theorem R10471 : Reach 10471 := rs (se 1 (by rfl) ⟨7853, by rfl⟩) R15707
theorem R10473 : Reach 10473 := rs (se 2 (by rfl) ⟨3927, by rfl⟩) R7855
theorem R10475 : Reach 10475 := rs (se 1 (by rfl) ⟨7856, by rfl⟩) R15713
theorem R10483 : Reach 10483 := rs (se 1 (by rfl) ⟨7862, by rfl⟩) R15725
theorem R10491 : Reach 10491 := rs (se 1 (by rfl) ⟨7868, by rfl⟩) R15737
theorem R10495 : Reach 10495 := rs (se 1 (by rfl) ⟨7871, by rfl⟩) R15743
theorem R10511 : Reach 10511 := rs (se 1 (by rfl) ⟨7883, by rfl⟩) R15767
theorem R10527 : Reach 10527 := rs (se 1 (by rfl) ⟨7895, by rfl⟩) R15791
theorem R10653 : Reach 10653 := rs (se 3 (by rfl) ⟨1997, by rfl⟩) R3995
theorem R10657 : Reach 10657 := rs (se 2 (by rfl) ⟨3996, by rfl⟩) R7993
theorem R10671 : Reach 10671 := rs (se 1 (by rfl) ⟨8003, by rfl⟩) R16007
theorem R10735 : Reach 10735 := rs (se 1 (by rfl) ⟨8051, by rfl⟩) R16103
theorem R10943 : Reach 10943 := rs (se 1 (by rfl) ⟨8207, by rfl⟩) R16415
theorem R11221 : Reach 11221 := rs (se 7 (by rfl) ⟨131, by rfl⟩) R263
theorem R11235 : Reach 11235 := rs (se 1 (by rfl) ⟨8426, by rfl⟩) R16853
theorem R11249 : Reach 11249 := rs (se 2 (by rfl) ⟨4218, by rfl⟩) R8437
theorem R11269 : Reach 11269 := rs (se 4 (by rfl) ⟨1056, by rfl⟩) R2113
theorem R11275 : Reach 11275 := rs (se 1 (by rfl) ⟨8456, by rfl⟩) R16913
theorem R11277 : Reach 11277 := rs (se 3 (by rfl) ⟨2114, by rfl⟩) R4229
theorem R11279 : Reach 11279 := rs (se 1 (by rfl) ⟨8459, by rfl⟩) R16919
theorem R11281 : Reach 11281 := rs (se 2 (by rfl) ⟨4230, by rfl⟩) R8461
theorem R11287 : Reach 11287 := rs (se 1 (by rfl) ⟨8465, by rfl⟩) R16931
theorem R11301 : Reach 11301 := rs (se 4 (by rfl) ⟨1059, by rfl⟩) R2119
theorem R11303 : Reach 11303 := rs (se 1 (by rfl) ⟨8477, by rfl⟩) R16955
theorem R11305 : Reach 11305 := rs (se 2 (by rfl) ⟨4239, by rfl⟩) R8479
theorem R11311 : Reach 11311 := rs (se 1 (by rfl) ⟨8483, by rfl⟩) R16967
theorem R11327 : Reach 11327 := rs (se 1 (by rfl) ⟨8495, by rfl⟩) R16991
theorem R11335 : Reach 11335 := rs (se 1 (by rfl) ⟨8501, by rfl⟩) R17003
theorem R11337 : Reach 11337 := rs (se 2 (by rfl) ⟨4251, by rfl⟩) R8503
theorem R11495 : Reach 11495 := rs (se 1 (by rfl) ⟨8621, by rfl⟩) R17243
theorem R11591 : Reach 11591 := rs (se 1 (by rfl) ⟨8693, by rfl⟩) R17387
theorem R12479 : Reach 12479 := rs (se 1 (by rfl) ⟨9359, by rfl⟩) R18719
theorem R12487 : Reach 12487 := rs (se 1 (by rfl) ⟨9365, by rfl⟩) R18731
theorem R12513 : Reach 12513 := rs (se 2 (by rfl) ⟨4692, by rfl⟩) R9385
theorem R12531 : Reach 12531 := rs (se 1 (by rfl) ⟨9398, by rfl⟩) R18797
theorem R45319 : Reach 45319 := rs (se 1 (by rfl) ⟨33989, by rfl⟩) R67979
theorem R46415 : Reach 46415 := rs (se 1 (by rfl) ⟨34811, by rfl⟩) R69623
theorem R80675 : Reach 80675 := rs (se 1 (by rfl) ⟨60506, by rfl⟩) R121013
theorem R80885 : Reach 80885 := rs (se 5 (by rfl) ⟨3791, by rfl⟩) R7583
theorem R81161 : Reach 81161 := rs (se 2 (by rfl) ⟨30435, by rfl⟩) R60871
theorem R49895 : Reach 49895 := rs (se 1 (by rfl) ⟨37421, by rfl⟩) R74843
theorem R50017 : Reach 50017 := rs (se 2 (by rfl) ⟨18756, by rfl⟩) R37513
theorem R83015 : Reach 83015 := rs (se 1 (by rfl) ⟨62261, by rfl⟩) R124523
theorem R181397 : Reach 181397 := rs (se 6 (by rfl) ⟨4251, by rfl⟩) R8503
theorem R83501 : Reach 83501 := rs (se 3 (by rfl) ⟨15656, by rfl⟩) R31313
theorem R83753 : Reach 83753 := rs (se 2 (by rfl) ⟨31407, by rfl⟩) R62815
theorem R20285 : Reach 20285 := rs (se 3 (by rfl) ⟨3803, by rfl⟩) R7607
theorem R20333 : Reach 20333 := rs (se 3 (by rfl) ⟨3812, by rfl⟩) R7625
theorem R20339 : Reach 20339 := rs (se 1 (by rfl) ⟨15254, by rfl⟩) R30509
theorem R20357 : Reach 20357 := rs (se 4 (by rfl) ⟨1908, by rfl⟩) R3817
theorem R20393 : Reach 20393 := rs (se 2 (by rfl) ⟨7647, by rfl⟩) R15295
theorem R20405 : Reach 20405 := rs (se 5 (by rfl) ⟨956, by rfl⟩) R1913
theorem R20411 : Reach 20411 := rs (se 1 (by rfl) ⟨15308, by rfl⟩) R30617
theorem R20567 : Reach 20567 := rs (se 1 (by rfl) ⟨15425, by rfl⟩) R30851
theorem R20591 : Reach 20591 := rs (se 1 (by rfl) ⟨15443, by rfl⟩) R30887
theorem R20627 : Reach 20627 := rs (se 1 (by rfl) ⟨15470, by rfl⟩) R30941
theorem R20771 : Reach 20771 := rs (se 1 (by rfl) ⟨15578, by rfl⟩) R31157
theorem R20783 : Reach 20783 := rs (se 1 (by rfl) ⟨15587, by rfl⟩) R31175
theorem R20861 : Reach 20861 := rs (se 3 (by rfl) ⟨3911, by rfl⟩) R7823
theorem R20879 : Reach 20879 := rs (se 1 (by rfl) ⟨15659, by rfl⟩) R31319
theorem R20945 : Reach 20945 := rs (se 2 (by rfl) ⟨7854, by rfl⟩) R15709
theorem R20951 : Reach 20951 := rs (se 1 (by rfl) ⟨15713, by rfl⟩) R31427
theorem R20965 : Reach 20965 := rs (se 4 (by rfl) ⟨1965, by rfl⟩) R3931
theorem R20969 : Reach 20969 := rs (se 2 (by rfl) ⟨7863, by rfl⟩) R15727
theorem R20987 : Reach 20987 := rs (se 1 (by rfl) ⟨15740, by rfl⟩) R31481
theorem R20989 : Reach 20989 := rs (se 3 (by rfl) ⟨3935, by rfl⟩) R7871
theorem R20999 : Reach 20999 := rs (se 1 (by rfl) ⟨15749, by rfl⟩) R31499
theorem R21307 : Reach 21307 := rs (se 1 (by rfl) ⟨15980, by rfl⟩) R31961
theorem R21343 : Reach 21343 := rs (se 1 (by rfl) ⟨16007, by rfl⟩) R32015
theorem R21887 : Reach 21887 := rs (se 1 (by rfl) ⟨16415, by rfl⟩) R32831
theorem R22499 : Reach 22499 := rs (se 1 (by rfl) ⟨16874, by rfl⟩) R33749
theorem R22607 : Reach 22607 := rs (se 1 (by rfl) ⟨16955, by rfl⟩) R33911
theorem R22625 : Reach 22625 := rs (se 2 (by rfl) ⟨8484, by rfl⟩) R16969
theorem R22675 : Reach 22675 := rs (se 1 (by rfl) ⟨17006, by rfl⟩) R34013
theorem R23183 : Reach 23183 := rs (se 1 (by rfl) ⟨17387, by rfl⟩) R34775
theorem R91367 : Reach 91367 := rs (se 1 (by rfl) ⟨68525, by rfl⟩) R137051
theorem R325795 : Reach 325795 := rs (se 1 (by rfl) ⟨244346, by rfl⟩) R488693
theorem R233 : Reach 233 := rs (se 2 (by rfl) ⟨87, by rfl⟩) R175
theorem R467 : Reach 467 := rs (se 1 (by rfl) ⟨350, by rfl⟩) R701
theorem R33263 : Reach 33263 := rs (se 1 (by rfl) ⟨24947, by rfl⟩) R49895
theorem R839 : Reach 839 := rs (se 1 (by rfl) ⟨629, by rfl⟩) R1259
theorem R933 : Reach 933 := rs (se 4 (by rfl) ⟨87, by rfl⟩) R175
theorem R939 : Reach 939 := rs (se 1 (by rfl) ⟨704, by rfl⟩) R1409
theorem R66689 : Reach 66689 := rs (se 2 (by rfl) ⟨25008, by rfl⟩) R50017
theorem R1679 : Reach 1679 := rs (se 1 (by rfl) ⟨1259, by rfl⟩) R2519
theorem R1775 : Reach 1775 := rs (se 1 (by rfl) ⟨1331, by rfl⟩) R2663
theorem R1869 : Reach 1869 := rs (se 3 (by rfl) ⟨350, by rfl⟩) R701
theorem R1873 : Reach 1873 := rs (se 2 (by rfl) ⟨702, by rfl⟩) R1405
theorem R1879 : Reach 1879 := rs (se 1 (by rfl) ⟨1409, by rfl⟩) R2819
theorem R1883 : Reach 1883 := rs (se 1 (by rfl) ⟨1412, by rfl⟩) R2825
theorem R3357 : Reach 3357 := rs (se 3 (by rfl) ⟨629, by rfl⟩) R1259
theorem R3367 : Reach 3367 := rs (se 1 (by rfl) ⟨2525, by rfl⟩) R5051
theorem R3401 : Reach 3401 := rs (se 2 (by rfl) ⟨1275, by rfl⟩) R2551
theorem R3483 : Reach 3483 := rs (se 1 (by rfl) ⟨2612, by rfl⟩) R5225
theorem R3489 : Reach 3489 := rs (se 2 (by rfl) ⟨1308, by rfl⟩) R2617
theorem R3503 : Reach 3503 := rs (se 1 (by rfl) ⟨2627, by rfl⟩) R5255
theorem R3551 : Reach 3551 := rs (se 1 (by rfl) ⟨2663, by rfl⟩) R5327
theorem R3733 : Reach 3733 := rs (se 6 (by rfl) ⟨87, by rfl⟩) R175
theorem R3747 : Reach 3747 := rs (se 1 (by rfl) ⟨2810, by rfl⟩) R5621
theorem R3757 : Reach 3757 := rs (se 3 (by rfl) ⟨704, by rfl⟩) R1409
theorem R3759 : Reach 3759 := rs (se 1 (by rfl) ⟨2819, by rfl⟩) R5639
theorem R3767 : Reach 3767 := rs (se 1 (by rfl) ⟨2825, by rfl⟩) R5651
theorem R3775 : Reach 3775 := rs (se 1 (by rfl) ⟨2831, by rfl⟩) R5663
theorem R6717 : Reach 6717 := rs (se 3 (by rfl) ⟨1259, by rfl⟩) R2519
theorem R6735 : Reach 6735 := rs (se 1 (by rfl) ⟨5051, by rfl⟩) R10103
theorem R6761 : Reach 6761 := rs (se 2 (by rfl) ⟨2535, by rfl⟩) R5071
theorem R6777 : Reach 6777 := rs (se 2 (by rfl) ⟨2541, by rfl⟩) R5083
theorem R6779 : Reach 6779 := rs (se 1 (by rfl) ⟨5084, by rfl⟩) R10169
theorem R6785 : Reach 6785 := rs (se 2 (by rfl) ⟨2544, by rfl⟩) R5089
theorem R6801 : Reach 6801 := rs (se 2 (by rfl) ⟨2550, by rfl⟩) R5101
theorem R6803 : Reach 6803 := rs (se 1 (by rfl) ⟨5102, by rfl⟩) R10205
theorem R6855 : Reach 6855 := rs (se 1 (by rfl) ⟨5141, by rfl⟩) R10283
theorem R6875 : Reach 6875 := rs (se 1 (by rfl) ⟨5156, by rfl⟩) R10313
theorem R6895 : Reach 6895 := rs (se 1 (by rfl) ⟨5171, by rfl⟩) R10343
theorem R6923 : Reach 6923 := rs (se 1 (by rfl) ⟨5192, by rfl⟩) R10385
theorem R6939 : Reach 6939 := rs (se 1 (by rfl) ⟨5204, by rfl⟩) R10409
theorem R6953 : Reach 6953 := rs (se 2 (by rfl) ⟨2607, by rfl⟩) R5215
theorem R6959 : Reach 6959 := rs (se 1 (by rfl) ⟨5219, by rfl⟩) R10439
theorem R6967 : Reach 6967 := rs (se 1 (by rfl) ⟨5225, by rfl⟩) R10451
theorem R6979 : Reach 6979 := rs (se 1 (by rfl) ⟨5234, by rfl⟩) R10469
theorem R6983 : Reach 6983 := rs (se 1 (by rfl) ⟨5237, by rfl⟩) R10475
theorem R7007 : Reach 7007 := rs (se 1 (by rfl) ⟨5255, by rfl⟩) R10511
theorem R7101 : Reach 7101 := rs (se 3 (by rfl) ⟨1331, by rfl⟩) R2663
theorem R7295 : Reach 7295 := rs (se 1 (by rfl) ⟨5471, by rfl⟩) R10943
theorem R7477 : Reach 7477 := rs (se 5 (by rfl) ⟨350, by rfl⟩) R701
theorem R7489 : Reach 7489 := rs (se 2 (by rfl) ⟨2808, by rfl⟩) R5617
theorem R7493 : Reach 7493 := rs (se 4 (by rfl) ⟨702, by rfl⟩) R1405
theorem R7499 : Reach 7499 := rs (se 1 (by rfl) ⟨5624, by rfl⟩) R11249
theorem R7513 : Reach 7513 := rs (se 2 (by rfl) ⟨2817, by rfl⟩) R5635
theorem R7517 : Reach 7517 := rs (se 3 (by rfl) ⟨1409, by rfl⟩) R2819
theorem R7519 : Reach 7519 := rs (se 1 (by rfl) ⟨5639, by rfl⟩) R11279
theorem R7533 : Reach 7533 := rs (se 3 (by rfl) ⟨1412, by rfl⟩) R2825
theorem R7535 : Reach 7535 := rs (se 1 (by rfl) ⟨5651, by rfl⟩) R11303
theorem R7551 : Reach 7551 := rs (se 1 (by rfl) ⟨5663, by rfl⟩) R11327
theorem R7663 : Reach 7663 := rs (se 1 (by rfl) ⟨5747, by rfl⟩) R11495
theorem R7727 : Reach 7727 := rs (se 1 (by rfl) ⟨5795, by rfl⟩) R11591
theorem R8319 : Reach 8319 := rs (se 1 (by rfl) ⟨6239, by rfl⟩) R12479
theorem R8353 : Reach 8353 := rs (se 2 (by rfl) ⟨3132, by rfl⟩) R6265
theorem R434393 : Reach 434393 := rs (se 2 (by rfl) ⟨162897, by rfl⟩) R325795
theorem R110717 : Reach 110717 := rs (se 3 (by rfl) ⟨20759, by rfl⟩) R41519
theorem R13429 : Reach 13429 := rs (se 5 (by rfl) ⟨629, by rfl⟩) R1259
theorem R13441 : Reach 13441 := rs (se 2 (by rfl) ⟨5040, by rfl⟩) R10081
theorem R13469 : Reach 13469 := rs (se 3 (by rfl) ⟨2525, by rfl⟩) R5051
theorem R13481 : Reach 13481 := rs (se 2 (by rfl) ⟨5055, by rfl⟩) R10111
theorem R13523 : Reach 13523 := rs (se 1 (by rfl) ⟨10142, by rfl⟩) R20285
theorem R13555 : Reach 13555 := rs (se 1 (by rfl) ⟨10166, by rfl⟩) R20333
theorem R13559 : Reach 13559 := rs (se 1 (by rfl) ⟨10169, by rfl⟩) R20339
theorem R13571 : Reach 13571 := rs (se 1 (by rfl) ⟨10178, by rfl⟩) R20357
theorem R13577 : Reach 13577 := rs (se 2 (by rfl) ⟨5091, by rfl⟩) R10183
theorem R13595 : Reach 13595 := rs (se 1 (by rfl) ⟨10196, by rfl⟩) R20393
theorem R13603 : Reach 13603 := rs (se 1 (by rfl) ⟨10202, by rfl⟩) R20405
theorem R13607 : Reach 13607 := rs (se 1 (by rfl) ⟨10205, by rfl⟩) R20411
theorem R13625 : Reach 13625 := rs (se 2 (by rfl) ⟨5109, by rfl⟩) R10219
theorem R13711 : Reach 13711 := rs (se 1 (by rfl) ⟨10283, by rfl⟩) R20567
theorem R13727 : Reach 13727 := rs (se 1 (by rfl) ⟨10295, by rfl⟩) R20591
theorem R13751 : Reach 13751 := rs (se 1 (by rfl) ⟨10313, by rfl⟩) R20627
theorem R13847 : Reach 13847 := rs (se 1 (by rfl) ⟨10385, by rfl⟩) R20771
theorem R13855 : Reach 13855 := rs (se 1 (by rfl) ⟨10391, by rfl⟩) R20783
theorem R13865 : Reach 13865 := rs (se 2 (by rfl) ⟨5199, by rfl⟩) R10399
theorem R13907 : Reach 13907 := rs (se 1 (by rfl) ⟨10430, by rfl⟩) R20861
theorem R13919 : Reach 13919 := rs (se 1 (by rfl) ⟨10439, by rfl⟩) R20879
theorem R13961 : Reach 13961 := rs (se 2 (by rfl) ⟨5235, by rfl⟩) R10471
theorem R13963 : Reach 13963 := rs (se 1 (by rfl) ⟨10472, by rfl⟩) R20945
theorem R13967 : Reach 13967 := rs (se 1 (by rfl) ⟨10475, by rfl⟩) R20951
theorem R13979 : Reach 13979 := rs (se 1 (by rfl) ⟨10484, by rfl⟩) R20969
theorem R13991 : Reach 13991 := rs (se 1 (by rfl) ⟨10493, by rfl⟩) R20987
theorem R13999 : Reach 13999 := rs (se 1 (by rfl) ⟨10499, by rfl⟩) R20999
theorem R14591 : Reach 14591 := rs (se 1 (by rfl) ⟨10943, by rfl⟩) R21887
theorem R14933 : Reach 14933 := rs (se 8 (by rfl) ⟨87, by rfl⟩) R175
theorem R14999 : Reach 14999 := rs (se 1 (by rfl) ⟨11249, by rfl⟩) R22499
theorem R15025 : Reach 15025 := rs (se 2 (by rfl) ⟨5634, by rfl⟩) R11269
theorem R15029 : Reach 15029 := rs (se 5 (by rfl) ⟨704, by rfl⟩) R1409
theorem R15041 : Reach 15041 := rs (se 2 (by rfl) ⟨5640, by rfl⟩) R11281
theorem R15071 : Reach 15071 := rs (se 1 (by rfl) ⟨11303, by rfl⟩) R22607
theorem R15083 : Reach 15083 := rs (se 1 (by rfl) ⟨11312, by rfl⟩) R22625
theorem R15101 : Reach 15101 := rs (se 3 (by rfl) ⟨2831, by rfl⟩) R5663
theorem R15113 : Reach 15113 := rs (se 2 (by rfl) ⟨5667, by rfl⟩) R11335
theorem R15455 : Reach 15455 := rs (se 1 (by rfl) ⟨11591, by rfl⟩) R23183
theorem R16649 : Reach 16649 := rs (se 2 (by rfl) ⟨6243, by rfl⟩) R12487
theorem R215693 : Reach 215693 := rs (se 3 (by rfl) ⟨40442, by rfl⟩) R80885
theorem R53783 : Reach 53783 := rs (se 1 (by rfl) ⟨40337, by rfl⟩) R80675
theorem R54107 : Reach 54107 := rs (se 1 (by rfl) ⟨40580, by rfl⟩) R81161
theorem R55343 : Reach 55343 := rs (se 1 (by rfl) ⟨41507, by rfl⟩) R83015
theorem R55667 : Reach 55667 := rs (se 1 (by rfl) ⟨41750, by rfl⟩) R83501
theorem R55835 : Reach 55835 := rs (se 1 (by rfl) ⟨41876, by rfl⟩) R83753
theorem R55997 : Reach 55997 := rs (se 3 (by rfl) ⟨10499, by rfl⟩) R20999
theorem R56821 : Reach 56821 := rs (se 5 (by rfl) ⟨2663, by rfl⟩) R5327
theorem R57257 : Reach 57257 := rs (se 2 (by rfl) ⟨21471, by rfl⟩) R42943
theorem R483725 : Reach 483725 := rs (se 3 (by rfl) ⟨90698, by rfl⟩) R181397
theorem R223073 : Reach 223073 := rs (se 2 (by rfl) ⟨83652, by rfl⟩) R167305
theorem R26891 : Reach 26891 := rs (se 1 (by rfl) ⟨20168, by rfl⟩) R40337
theorem R26963 : Reach 26963 := rs (se 1 (by rfl) ⟨20222, by rfl⟩) R40445
theorem R27035 : Reach 27035 := rs (se 1 (by rfl) ⟨20276, by rfl⟩) R40553
theorem R27155 : Reach 27155 := rs (se 1 (by rfl) ⟨20366, by rfl⟩) R40733
theorem R27215 : Reach 27215 := rs (se 1 (by rfl) ⟨20411, by rfl⟩) R40823
theorem R27251 : Reach 27251 := rs (se 1 (by rfl) ⟨20438, by rfl⟩) R40877
theorem R60101 : Reach 60101 := rs (se 4 (by rfl) ⟨5634, by rfl⟩) R11269
theorem R27499 : Reach 27499 := rs (se 1 (by rfl) ⟨20624, by rfl⟩) R41249
theorem R27503 : Reach 27503 := rs (se 1 (by rfl) ⟨20627, by rfl⟩) R41255
theorem R60425 : Reach 60425 := rs (se 2 (by rfl) ⟨22659, by rfl⟩) R45319
theorem R27719 : Reach 27719 := rs (se 1 (by rfl) ⟨20789, by rfl⟩) R41579
theorem R27803 : Reach 27803 := rs (se 1 (by rfl) ⟨20852, by rfl⟩) R41705
theorem R27823 : Reach 27823 := rs (se 1 (by rfl) ⟨20867, by rfl⟩) R41735
theorem R27917 : Reach 27917 := rs (se 3 (by rfl) ⟨5234, by rfl⟩) R10469
theorem R27935 : Reach 27935 := rs (se 1 (by rfl) ⟨20951, by rfl⟩) R41903
theorem R27953 : Reach 27953 := rs (se 2 (by rfl) ⟨10482, by rfl⟩) R20965
theorem R27983 : Reach 27983 := rs (se 1 (by rfl) ⟨20987, by rfl⟩) R41975
theorem R27985 : Reach 27985 := rs (se 2 (by rfl) ⟨10494, by rfl⟩) R20989
theorem R60911 : Reach 60911 := rs (se 1 (by rfl) ⟨45683, by rfl⟩) R91367
theorem R28409 : Reach 28409 := rs (se 2 (by rfl) ⟨10653, by rfl⟩) R21307
theorem R28457 : Reach 28457 := rs (se 2 (by rfl) ⟨10671, by rfl⟩) R21343
theorem R28655 : Reach 28655 := rs (se 1 (by rfl) ⟨21491, by rfl⟩) R42983
theorem R29909 : Reach 29909 := rs (se 7 (by rfl) ⟨350, by rfl⟩) R701
theorem R30077 : Reach 30077 := rs (se 3 (by rfl) ⟨5639, by rfl⟩) R11279
theorem R30233 : Reach 30233 := rs (se 2 (by rfl) ⟨11337, by rfl⟩) R22675
theorem R30943 : Reach 30943 := rs (se 1 (by rfl) ⟨23207, by rfl⟩) R46415
theorem R155 : Reach 155 := rs (se 1 (by rfl) ⟨116, by rfl⟩) R233
theorem R311 : Reach 311 := rs (se 1 (by rfl) ⟨233, by rfl⟩) R467
theorem R559 : Reach 559 := rs (se 1 (by rfl) ⟨419, by rfl⟩) R839
theorem R621 : Reach 621 := rs (se 3 (by rfl) ⟨116, by rfl⟩) R233
theorem R1119 : Reach 1119 := rs (se 1 (by rfl) ⟨839, by rfl⟩) R1679
theorem R1183 : Reach 1183 := rs (se 1 (by rfl) ⟨887, by rfl⟩) R1775
theorem R1245 : Reach 1245 := rs (se 3 (by rfl) ⟨233, by rfl⟩) R467
theorem R1255 : Reach 1255 := rs (se 1 (by rfl) ⟨941, by rfl⟩) R1883
theorem R2237 : Reach 2237 := rs (se 3 (by rfl) ⟨419, by rfl⟩) R839
theorem R2267 : Reach 2267 := rs (se 1 (by rfl) ⟨1700, by rfl⟩) R3401
theorem R2335 : Reach 2335 := rs (se 1 (by rfl) ⟨1751, by rfl⟩) R3503
theorem R2367 : Reach 2367 := rs (se 1 (by rfl) ⟨1775, by rfl⟩) R3551
theorem R2485 : Reach 2485 := rs (se 5 (by rfl) ⟨116, by rfl⟩) R233
theorem R2497 : Reach 2497 := rs (se 2 (by rfl) ⟨936, by rfl⟩) R1873
theorem R2505 : Reach 2505 := rs (se 2 (by rfl) ⟨939, by rfl⟩) R1879
theorem R2511 : Reach 2511 := rs (se 1 (by rfl) ⟨1883, by rfl⟩) R3767
theorem R35855 : Reach 35855 := rs (se 1 (by rfl) ⟨26891, by rfl⟩) R53783
theorem R36071 : Reach 36071 := rs (se 1 (by rfl) ⟨27053, by rfl⟩) R54107
theorem R36665 : Reach 36665 := rs (se 2 (by rfl) ⟨13749, by rfl⟩) R27499
theorem R36773 : Reach 36773 := rs (se 4 (by rfl) ⟨3447, by rfl⟩) R6895
theorem R36895 : Reach 36895 := rs (se 1 (by rfl) ⟨27671, by rfl⟩) R55343
theorem R37097 : Reach 37097 := rs (se 2 (by rfl) ⟨13911, by rfl⟩) R27823
theorem R37111 : Reach 37111 := rs (se 1 (by rfl) ⟨27833, by rfl⟩) R55667
theorem R37223 : Reach 37223 := rs (se 1 (by rfl) ⟨27917, by rfl⟩) R55835
theorem R4477 : Reach 4477 := rs (se 3 (by rfl) ⟨839, by rfl⟩) R1679
theorem R4489 : Reach 4489 := rs (se 2 (by rfl) ⟨1683, by rfl⟩) R3367
theorem R4507 : Reach 4507 := rs (se 1 (by rfl) ⟨3380, by rfl⟩) R6761
theorem R4519 : Reach 4519 := rs (se 1 (by rfl) ⟨3389, by rfl⟩) R6779
theorem R4523 : Reach 4523 := rs (se 1 (by rfl) ⟨3392, by rfl⟩) R6785
theorem R4535 : Reach 4535 := rs (se 1 (by rfl) ⟨3401, by rfl⟩) R6803
theorem R37313 : Reach 37313 := rs (se 2 (by rfl) ⟨13992, by rfl⟩) R27985
theorem R37331 : Reach 37331 := rs (se 1 (by rfl) ⟨27998, by rfl⟩) R55997
theorem R4583 : Reach 4583 := rs (se 1 (by rfl) ⟨3437, by rfl⟩) R6875
theorem R4615 : Reach 4615 := rs (se 1 (by rfl) ⟨3461, by rfl⟩) R6923
theorem R4635 : Reach 4635 := rs (se 1 (by rfl) ⟨3476, by rfl⟩) R6953
theorem R4639 : Reach 4639 := rs (se 1 (by rfl) ⟨3479, by rfl⟩) R6959
theorem R4655 : Reach 4655 := rs (se 1 (by rfl) ⟨3491, by rfl⟩) R6983
theorem R4671 : Reach 4671 := rs (se 1 (by rfl) ⟨3503, by rfl⟩) R7007
theorem R4733 : Reach 4733 := rs (se 3 (by rfl) ⟨887, by rfl⟩) R1775
theorem R4863 : Reach 4863 := rs (se 1 (by rfl) ⟨3647, by rfl⟩) R7295
theorem R4977 : Reach 4977 := rs (se 2 (by rfl) ⟨1866, by rfl⟩) R3733
theorem R4981 : Reach 4981 := rs (se 5 (by rfl) ⟨233, by rfl⟩) R467
theorem R4995 : Reach 4995 := rs (se 1 (by rfl) ⟨3746, by rfl⟩) R7493
theorem R4999 : Reach 4999 := rs (se 1 (by rfl) ⟨3749, by rfl⟩) R7499
theorem R5009 : Reach 5009 := rs (se 2 (by rfl) ⟨1878, by rfl⟩) R3757
theorem R5011 : Reach 5011 := rs (se 1 (by rfl) ⟨3758, by rfl⟩) R7517
theorem R5021 : Reach 5021 := rs (se 3 (by rfl) ⟨941, by rfl⟩) R1883
theorem R5023 : Reach 5023 := rs (se 1 (by rfl) ⟨3767, by rfl⟩) R7535
theorem R5033 : Reach 5033 := rs (se 2 (by rfl) ⟨1887, by rfl⟩) R3775
theorem R37877 : Reach 37877 := rs (se 5 (by rfl) ⟨1775, by rfl⟩) R3551
theorem R5151 : Reach 5151 := rs (se 1 (by rfl) ⟨3863, by rfl⟩) R7727
theorem R38171 : Reach 38171 := rs (se 1 (by rfl) ⟨28628, by rfl⟩) R57257
theorem R71621 : Reach 71621 := rs (se 4 (by rfl) ⟨6714, by rfl⟩) R13429
theorem R72413 : Reach 72413 := rs (se 3 (by rfl) ⟨13577, by rfl⟩) R27155
theorem R40067 : Reach 40067 := rs (se 1 (by rfl) ⟨30050, by rfl⟩) R60101
theorem R40085 : Reach 40085 := rs (se 6 (by rfl) ⟨939, by rfl⟩) R1879
theorem R40283 : Reach 40283 := rs (se 1 (by rfl) ⟨30212, by rfl⟩) R60425
theorem R40607 : Reach 40607 := rs (se 1 (by rfl) ⟨30455, by rfl⟩) R60911
theorem R73811 : Reach 73811 := rs (se 1 (by rfl) ⟨55358, by rfl⟩) R110717
theorem R41257 : Reach 41257 := rs (se 2 (by rfl) ⟨15471, by rfl⟩) R30943
theorem R8949 : Reach 8949 := rs (se 5 (by rfl) ⟨419, by rfl⟩) R839
theorem R8979 : Reach 8979 := rs (se 1 (by rfl) ⟨6734, by rfl⟩) R13469
theorem R8987 : Reach 8987 := rs (se 1 (by rfl) ⟨6740, by rfl⟩) R13481
theorem R9015 : Reach 9015 := rs (se 1 (by rfl) ⟨6761, by rfl⟩) R13523
theorem R9039 : Reach 9039 := rs (se 1 (by rfl) ⟨6779, by rfl⟩) R13559
theorem R9047 : Reach 9047 := rs (se 1 (by rfl) ⟨6785, by rfl⟩) R13571
theorem R9051 : Reach 9051 := rs (se 1 (by rfl) ⟨6788, by rfl⟩) R13577
theorem R9063 : Reach 9063 := rs (se 1 (by rfl) ⟨6797, by rfl⟩) R13595
theorem R9069 : Reach 9069 := rs (se 3 (by rfl) ⟨1700, by rfl⟩) R3401
theorem R9071 : Reach 9071 := rs (se 1 (by rfl) ⟨6803, by rfl⟩) R13607
theorem R9083 : Reach 9083 := rs (se 1 (by rfl) ⟨6812, by rfl⟩) R13625
theorem R74621 : Reach 74621 := rs (se 3 (by rfl) ⟨13991, by rfl⟩) R27983
theorem R9151 : Reach 9151 := rs (se 1 (by rfl) ⟨6863, by rfl⟩) R13727
theorem R9167 : Reach 9167 := rs (se 1 (by rfl) ⟨6875, by rfl⟩) R13751
theorem R9193 : Reach 9193 := rs (se 2 (by rfl) ⟨3447, by rfl⟩) R6895
theorem R9231 : Reach 9231 := rs (se 1 (by rfl) ⟨6923, by rfl⟩) R13847
theorem R9243 : Reach 9243 := rs (se 1 (by rfl) ⟨6932, by rfl⟩) R13865
theorem R9271 : Reach 9271 := rs (se 1 (by rfl) ⟨6953, by rfl⟩) R13907
theorem R9279 : Reach 9279 := rs (se 1 (by rfl) ⟨6959, by rfl⟩) R13919
theorem R9289 : Reach 9289 := rs (se 2 (by rfl) ⟨3483, by rfl⟩) R6967
theorem R9305 : Reach 9305 := rs (se 2 (by rfl) ⟨3489, by rfl⟩) R6979
theorem R9307 : Reach 9307 := rs (se 1 (by rfl) ⟨6980, by rfl⟩) R13961
theorem R9311 : Reach 9311 := rs (se 1 (by rfl) ⟨6983, by rfl⟩) R13967
theorem R9319 : Reach 9319 := rs (se 1 (by rfl) ⟨6989, by rfl⟩) R13979
theorem R9327 : Reach 9327 := rs (se 1 (by rfl) ⟨6995, by rfl⟩) R13991
theorem R9341 : Reach 9341 := rs (se 3 (by rfl) ⟨1751, by rfl⟩) R3503
theorem R9469 : Reach 9469 := rs (se 3 (by rfl) ⟨1775, by rfl⟩) R3551
theorem R9727 : Reach 9727 := rs (se 1 (by rfl) ⟨7295, by rfl⟩) R14591
theorem R9941 : Reach 9941 := rs (se 7 (by rfl) ⟨116, by rfl⟩) R233
theorem R9955 : Reach 9955 := rs (se 1 (by rfl) ⟨7466, by rfl⟩) R14933
theorem R9969 : Reach 9969 := rs (se 2 (by rfl) ⟨3738, by rfl⟩) R7477
theorem R9985 : Reach 9985 := rs (se 2 (by rfl) ⟨3744, by rfl⟩) R7489
theorem R9989 : Reach 9989 := rs (se 4 (by rfl) ⟨936, by rfl⟩) R1873
theorem R9999 : Reach 9999 := rs (se 1 (by rfl) ⟨7499, by rfl⟩) R14999
theorem R10017 : Reach 10017 := rs (se 2 (by rfl) ⟨3756, by rfl⟩) R7513
theorem R10019 : Reach 10019 := rs (se 1 (by rfl) ⟨7514, by rfl⟩) R15029
theorem R10021 : Reach 10021 := rs (se 4 (by rfl) ⟨939, by rfl⟩) R1879
theorem R10025 : Reach 10025 := rs (se 2 (by rfl) ⟨3759, by rfl⟩) R7519
theorem R10027 : Reach 10027 := rs (se 1 (by rfl) ⟨7520, by rfl⟩) R15041
theorem R10045 : Reach 10045 := rs (se 3 (by rfl) ⟨1883, by rfl⟩) R3767
theorem R10047 : Reach 10047 := rs (se 1 (by rfl) ⟨7535, by rfl⟩) R15071
theorem R10055 : Reach 10055 := rs (se 1 (by rfl) ⟨7541, by rfl⟩) R15083
theorem R10067 : Reach 10067 := rs (se 1 (by rfl) ⟨7550, by rfl⟩) R15101
theorem R10075 : Reach 10075 := rs (se 1 (by rfl) ⟨7556, by rfl⟩) R15113
theorem R10217 : Reach 10217 := rs (se 2 (by rfl) ⟨3831, by rfl⟩) R7663
theorem R75757 : Reach 75757 := rs (se 3 (by rfl) ⟨14204, by rfl⟩) R28409
theorem R75761 : Reach 75761 := rs (se 2 (by rfl) ⟨28410, by rfl⟩) R56821
theorem R10303 : Reach 10303 := rs (se 1 (by rfl) ⟨7727, by rfl⟩) R15455
theorem R11099 : Reach 11099 := rs (se 1 (by rfl) ⟨8324, by rfl⟩) R16649
theorem R11137 : Reach 11137 := rs (se 2 (by rfl) ⟨4176, by rfl⟩) R8353
theorem R44459 : Reach 44459 := rs (se 1 (by rfl) ⟨33344, by rfl⟩) R66689
theorem R44549 : Reach 44549 := rs (se 4 (by rfl) ⟨4176, by rfl⟩) R8353
theorem R143795 : Reach 143795 := rs (se 1 (by rfl) ⟨107846, by rfl⟩) R215693
theorem R148715 : Reach 148715 := rs (se 1 (by rfl) ⟨111536, by rfl⟩) R223073
theorem R17909 : Reach 17909 := rs (se 5 (by rfl) ⟨839, by rfl⟩) R1679
theorem R17921 : Reach 17921 := rs (se 2 (by rfl) ⟨6720, by rfl⟩) R13441
theorem R17927 : Reach 17927 := rs (se 1 (by rfl) ⟨13445, by rfl⟩) R26891
theorem R17957 : Reach 17957 := rs (se 4 (by rfl) ⟨1683, by rfl⟩) R3367
theorem R17975 : Reach 17975 := rs (se 1 (by rfl) ⟨13481, by rfl⟩) R26963
theorem R18023 : Reach 18023 := rs (se 1 (by rfl) ⟨13517, by rfl⟩) R27035
theorem R18029 : Reach 18029 := rs (se 3 (by rfl) ⟨3380, by rfl⟩) R6761
theorem R18073 : Reach 18073 := rs (se 2 (by rfl) ⟨6777, by rfl⟩) R13555
theorem R18077 : Reach 18077 := rs (se 3 (by rfl) ⟨3389, by rfl⟩) R6779
theorem R18103 : Reach 18103 := rs (se 1 (by rfl) ⟨13577, by rfl⟩) R27155
theorem R18137 : Reach 18137 := rs (se 2 (by rfl) ⟨6801, by rfl⟩) R13603
theorem R18143 : Reach 18143 := rs (se 1 (by rfl) ⟨13607, by rfl⟩) R27215
theorem R18167 : Reach 18167 := rs (se 1 (by rfl) ⟨13625, by rfl⟩) R27251
theorem R18281 : Reach 18281 := rs (se 2 (by rfl) ⟨6855, by rfl⟩) R13711
theorem R18335 : Reach 18335 := rs (se 1 (by rfl) ⟨13751, by rfl⟩) R27503
theorem R18461 : Reach 18461 := rs (se 3 (by rfl) ⟨3461, by rfl⟩) R6923
theorem R18473 : Reach 18473 := rs (se 2 (by rfl) ⟨6927, by rfl⟩) R13855
theorem R18479 : Reach 18479 := rs (se 1 (by rfl) ⟨13859, by rfl⟩) R27719
theorem R18535 : Reach 18535 := rs (se 1 (by rfl) ⟨13901, by rfl⟩) R27803
theorem R18557 : Reach 18557 := rs (se 3 (by rfl) ⟨3479, by rfl⟩) R6959
theorem R18611 : Reach 18611 := rs (se 1 (by rfl) ⟨13958, by rfl⟩) R27917
theorem R18617 : Reach 18617 := rs (se 2 (by rfl) ⟨6981, by rfl⟩) R13963
theorem R18623 : Reach 18623 := rs (se 1 (by rfl) ⟨13967, by rfl⟩) R27935
theorem R18635 : Reach 18635 := rs (se 1 (by rfl) ⟨13976, by rfl⟩) R27953
theorem R18665 : Reach 18665 := rs (se 2 (by rfl) ⟨6999, by rfl⟩) R13999
theorem R18971 : Reach 18971 := rs (se 1 (by rfl) ⟨14228, by rfl⟩) R28457
theorem R19103 : Reach 19103 := rs (se 1 (by rfl) ⟨14327, by rfl⟩) R28655
theorem R19453 : Reach 19453 := rs (se 3 (by rfl) ⟨3647, by rfl⟩) R7295
theorem R19925 : Reach 19925 := rs (se 7 (by rfl) ⟨233, by rfl⟩) R467
theorem R19939 : Reach 19939 := rs (se 1 (by rfl) ⟨14954, by rfl⟩) R29909
theorem R19997 : Reach 19997 := rs (se 3 (by rfl) ⟨3749, by rfl⟩) R7499
theorem R20033 : Reach 20033 := rs (se 2 (by rfl) ⟨7512, by rfl⟩) R15025
theorem R20051 : Reach 20051 := rs (se 1 (by rfl) ⟨15038, by rfl⟩) R30077
theorem R20093 : Reach 20093 := rs (se 3 (by rfl) ⟨3767, by rfl⟩) R7535
theorem R20155 : Reach 20155 := rs (se 1 (by rfl) ⟨15116, by rfl⟩) R30233
theorem R22175 : Reach 22175 := rs (se 1 (by rfl) ⟨16631, by rfl⟩) R33263
theorem R289595 : Reach 289595 := rs (se 1 (by rfl) ⟨217196, by rfl⟩) R434393
theorem R322483 : Reach 322483 := rs (se 1 (by rfl) ⟨241862, by rfl⟩) R483725
theorem R103 : Reach 103 := rs (se 1 (by rfl) ⟨77, by rfl⟩) R155
theorem R207 : Reach 207 := rs (se 1 (by rfl) ⟨155, by rfl⟩) R311
theorem R196829 : Reach 196829 := rs (se 3 (by rfl) ⟨36905, by rfl⟩) R73811
theorem R413 : Reach 413 := rs (se 3 (by rfl) ⟨77, by rfl⟩) R155
theorem R745 : Reach 745 := rs (se 2 (by rfl) ⟨279, by rfl⟩) R559
theorem R829 : Reach 829 := rs (se 3 (by rfl) ⟨155, by rfl⟩) R311
theorem R99143 : Reach 99143 := rs (se 1 (by rfl) ⟨74357, by rfl⟩) R148715
theorem R1491 : Reach 1491 := rs (se 1 (by rfl) ⟨1118, by rfl⟩) R2237
theorem R1511 : Reach 1511 := rs (se 1 (by rfl) ⟨1133, by rfl⟩) R2267
theorem R1577 : Reach 1577 := rs (se 2 (by rfl) ⟨591, by rfl⟩) R1183
theorem R1653 : Reach 1653 := rs (se 5 (by rfl) ⟨77, by rfl⟩) R155
theorem R1673 : Reach 1673 := rs (se 2 (by rfl) ⟨627, by rfl⟩) R1255
theorem R101009 : Reach 101009 := rs (se 2 (by rfl) ⟨37878, by rfl⟩) R75757
theorem R2981 : Reach 2981 := rs (se 4 (by rfl) ⟨279, by rfl⟩) R559
theorem R3015 : Reach 3015 := rs (se 1 (by rfl) ⟨2261, by rfl⟩) R4523
theorem R3023 : Reach 3023 := rs (se 1 (by rfl) ⟨2267, by rfl⟩) R4535
theorem R3055 : Reach 3055 := rs (se 1 (by rfl) ⟨2291, by rfl⟩) R4583
theorem R3103 : Reach 3103 := rs (se 1 (by rfl) ⟨2327, by rfl⟩) R4655
theorem R3113 : Reach 3113 := rs (se 2 (by rfl) ⟨1167, by rfl⟩) R2335
theorem R3155 : Reach 3155 := rs (se 1 (by rfl) ⟨2366, by rfl⟩) R4733
theorem R3313 : Reach 3313 := rs (se 2 (by rfl) ⟨1242, by rfl⟩) R2485
theorem R3317 : Reach 3317 := rs (se 5 (by rfl) ⟨155, by rfl⟩) R311
theorem R3329 : Reach 3329 := rs (se 2 (by rfl) ⟨1248, by rfl⟩) R2497
theorem R3339 : Reach 3339 := rs (se 1 (by rfl) ⟨2504, by rfl⟩) R5009
theorem R3347 : Reach 3347 := rs (se 1 (by rfl) ⟨2510, by rfl⟩) R5021
theorem R3355 : Reach 3355 := rs (se 1 (by rfl) ⟨2516, by rfl⟩) R5033
theorem R429977 : Reach 429977 := rs (se 2 (by rfl) ⟨161241, by rfl⟩) R322483
theorem R5965 : Reach 5965 := rs (se 3 (by rfl) ⟨1118, by rfl⟩) R2237
theorem R5969 : Reach 5969 := rs (se 2 (by rfl) ⟨2238, by rfl⟩) R4477
theorem R5985 : Reach 5985 := rs (se 2 (by rfl) ⟨2244, by rfl⟩) R4489
theorem R5991 : Reach 5991 := rs (se 1 (by rfl) ⟨4493, by rfl⟩) R8987
theorem R6009 : Reach 6009 := rs (se 2 (by rfl) ⟨2253, by rfl⟩) R4507
theorem R6025 : Reach 6025 := rs (se 2 (by rfl) ⟨2259, by rfl⟩) R4519
theorem R6031 : Reach 6031 := rs (se 1 (by rfl) ⟨4523, by rfl⟩) R9047
theorem R6045 : Reach 6045 := rs (se 3 (by rfl) ⟨1133, by rfl⟩) R2267
theorem R6047 : Reach 6047 := rs (se 1 (by rfl) ⟨4535, by rfl⟩) R9071
theorem R6055 : Reach 6055 := rs (se 1 (by rfl) ⟨4541, by rfl⟩) R9083
theorem R6111 : Reach 6111 := rs (se 1 (by rfl) ⟨4583, by rfl⟩) R9167
theorem R6153 : Reach 6153 := rs (se 2 (by rfl) ⟨2307, by rfl⟩) R4615
theorem R6185 : Reach 6185 := rs (se 2 (by rfl) ⟨2319, by rfl⟩) R4639
theorem R6203 : Reach 6203 := rs (se 1 (by rfl) ⟨4652, by rfl⟩) R9305
theorem R6207 : Reach 6207 := rs (se 1 (by rfl) ⟨4655, by rfl⟩) R9311
theorem R6227 : Reach 6227 := rs (se 1 (by rfl) ⟨4670, by rfl⟩) R9341
theorem R6309 : Reach 6309 := rs (se 4 (by rfl) ⟨591, by rfl⟩) R1183
theorem R6613 : Reach 6613 := rs (se 7 (by rfl) ⟨77, by rfl⟩) R155
theorem R6627 : Reach 6627 := rs (se 1 (by rfl) ⟨4970, by rfl⟩) R9941
theorem R6641 : Reach 6641 := rs (se 2 (by rfl) ⟨2490, by rfl⟩) R4981
theorem R6659 : Reach 6659 := rs (se 1 (by rfl) ⟨4994, by rfl⟩) R9989
theorem R6665 : Reach 6665 := rs (se 2 (by rfl) ⟨2499, by rfl⟩) R4999
theorem R6679 : Reach 6679 := rs (se 1 (by rfl) ⟨5009, by rfl⟩) R10019
theorem R6681 : Reach 6681 := rs (se 2 (by rfl) ⟨2505, by rfl⟩) R5011
theorem R6683 : Reach 6683 := rs (se 1 (by rfl) ⟨5012, by rfl⟩) R10025
theorem R6693 : Reach 6693 := rs (se 4 (by rfl) ⟨627, by rfl⟩) R1255
theorem R6697 : Reach 6697 := rs (se 2 (by rfl) ⟨2511, by rfl⟩) R5023
theorem R6703 : Reach 6703 := rs (se 1 (by rfl) ⟨5027, by rfl⟩) R10055
theorem R6711 : Reach 6711 := rs (se 1 (by rfl) ⟨5033, by rfl⟩) R10067
theorem R6811 : Reach 6811 := rs (se 1 (by rfl) ⟨5108, by rfl⟩) R10217
theorem R7399 : Reach 7399 := rs (se 1 (by rfl) ⟨5549, by rfl⟩) R11099
theorem R404021 : Reach 404021 := rs (se 5 (by rfl) ⟨18938, by rfl⟩) R37877
theorem R11925 : Reach 11925 := rs (se 6 (by rfl) ⟨279, by rfl⟩) R559
theorem R11939 : Reach 11939 := rs (se 1 (by rfl) ⟨8954, by rfl⟩) R17909
theorem R11947 : Reach 11947 := rs (se 1 (by rfl) ⟨8960, by rfl⟩) R17921
theorem R11951 : Reach 11951 := rs (se 1 (by rfl) ⟨8963, by rfl⟩) R17927
theorem R11971 : Reach 11971 := rs (se 1 (by rfl) ⟨8978, by rfl⟩) R17957
theorem R11983 : Reach 11983 := rs (se 1 (by rfl) ⟨8987, by rfl⟩) R17975
theorem R12015 : Reach 12015 := rs (se 1 (by rfl) ⟨9011, by rfl⟩) R18023
theorem R12019 : Reach 12019 := rs (se 1 (by rfl) ⟨9014, by rfl⟩) R18029
theorem R12051 : Reach 12051 := rs (se 1 (by rfl) ⟨9038, by rfl⟩) R18077
theorem R12061 : Reach 12061 := rs (se 3 (by rfl) ⟨2261, by rfl⟩) R4523
theorem R12091 : Reach 12091 := rs (se 1 (by rfl) ⟨9068, by rfl⟩) R18137
theorem R12093 : Reach 12093 := rs (se 3 (by rfl) ⟨2267, by rfl⟩) R4535
theorem R12095 : Reach 12095 := rs (se 1 (by rfl) ⟨9071, by rfl⟩) R18143
theorem R12111 : Reach 12111 := rs (se 1 (by rfl) ⟨9083, by rfl⟩) R18167
theorem R12187 : Reach 12187 := rs (se 1 (by rfl) ⟨9140, by rfl⟩) R18281
theorem R12201 : Reach 12201 := rs (se 2 (by rfl) ⟨4575, by rfl⟩) R9151
theorem R12221 : Reach 12221 := rs (se 3 (by rfl) ⟨2291, by rfl⟩) R4583
theorem R12223 : Reach 12223 := rs (se 1 (by rfl) ⟨9167, by rfl⟩) R18335
theorem R12257 : Reach 12257 := rs (se 2 (by rfl) ⟨4596, by rfl⟩) R9193
theorem R12307 : Reach 12307 := rs (se 1 (by rfl) ⟨9230, by rfl⟩) R18461
theorem R12315 : Reach 12315 := rs (se 1 (by rfl) ⟨9236, by rfl⟩) R18473
theorem R12319 : Reach 12319 := rs (se 1 (by rfl) ⟨9239, by rfl⟩) R18479
theorem R12361 : Reach 12361 := rs (se 2 (by rfl) ⟨4635, by rfl⟩) R9271
theorem R12371 : Reach 12371 := rs (se 1 (by rfl) ⟨9278, by rfl⟩) R18557
theorem R12385 : Reach 12385 := rs (se 2 (by rfl) ⟨4644, by rfl⟩) R9289
theorem R12407 : Reach 12407 := rs (se 1 (by rfl) ⟨9305, by rfl⟩) R18611
theorem R12409 : Reach 12409 := rs (se 2 (by rfl) ⟨4653, by rfl⟩) R9307
theorem R12411 : Reach 12411 := rs (se 1 (by rfl) ⟨9308, by rfl⟩) R18617
theorem R12413 : Reach 12413 := rs (se 3 (by rfl) ⟨2327, by rfl⟩) R4655
theorem R12415 : Reach 12415 := rs (se 1 (by rfl) ⟨9311, by rfl⟩) R18623
theorem R12423 : Reach 12423 := rs (se 1 (by rfl) ⟨9317, by rfl⟩) R18635
theorem R12425 : Reach 12425 := rs (se 2 (by rfl) ⟨4659, by rfl⟩) R9319
theorem R12443 : Reach 12443 := rs (se 1 (by rfl) ⟨9332, by rfl⟩) R18665
theorem R12453 : Reach 12453 := rs (se 4 (by rfl) ⟨1167, by rfl⟩) R2335
theorem R12621 : Reach 12621 := rs (se 3 (by rfl) ⟨2366, by rfl⟩) R4733
theorem R12625 : Reach 12625 := rs (se 2 (by rfl) ⟨4734, by rfl⟩) R9469
theorem R12647 : Reach 12647 := rs (se 1 (by rfl) ⟨9485, by rfl⟩) R18971
theorem R12735 : Reach 12735 := rs (se 1 (by rfl) ⟨9551, by rfl⟩) R19103
theorem R13253 : Reach 13253 := rs (se 4 (by rfl) ⟨1242, by rfl⟩) R2485
theorem R13283 : Reach 13283 := rs (se 1 (by rfl) ⟨9962, by rfl⟩) R19925
theorem R13313 : Reach 13313 := rs (se 2 (by rfl) ⟨4992, by rfl⟩) R9985
theorem R13331 : Reach 13331 := rs (se 1 (by rfl) ⟨9998, by rfl⟩) R19997
theorem R13355 : Reach 13355 := rs (se 1 (by rfl) ⟨10016, by rfl⟩) R20033
theorem R13361 : Reach 13361 := rs (se 2 (by rfl) ⟨5010, by rfl⟩) R10021
theorem R13367 : Reach 13367 := rs (se 1 (by rfl) ⟨10025, by rfl⟩) R20051
theorem R13369 : Reach 13369 := rs (se 2 (by rfl) ⟨5013, by rfl⟩) R10027
theorem R13421 : Reach 13421 := rs (se 3 (by rfl) ⟨2516, by rfl⟩) R5033
theorem R13433 : Reach 13433 := rs (se 2 (by rfl) ⟨5037, by rfl⟩) R10075
theorem R14783 : Reach 14783 := rs (se 1 (by rfl) ⟨11087, by rfl⟩) R22175
theorem R14849 : Reach 14849 := rs (se 2 (by rfl) ⟨5568, by rfl⟩) R11137
theorem R47747 : Reach 47747 := rs (se 1 (by rfl) ⟨35810, by rfl⟩) R71621
theorem R47789 : Reach 47789 := rs (se 3 (by rfl) ⟨8960, by rfl⟩) R17921
theorem R48275 : Reach 48275 := rs (se 1 (by rfl) ⟨36206, by rfl⟩) R72413
theorem R49193 : Reach 49193 := rs (se 2 (by rfl) ⟨18447, by rfl⟩) R36895
theorem R49207 : Reach 49207 := rs (se 1 (by rfl) ⟨36905, by rfl⟩) R73811
theorem R49481 : Reach 49481 := rs (se 2 (by rfl) ⟨18555, by rfl⟩) R37111
theorem R49747 : Reach 49747 := rs (se 1 (by rfl) ⟨37310, by rfl⟩) R74621
theorem R214325 : Reach 214325 := rs (se 5 (by rfl) ⟨10046, by rfl⟩) R20093
theorem R50507 : Reach 50507 := rs (se 1 (by rfl) ⟨37880, by rfl⟩) R75761
theorem R772253 : Reach 772253 := rs (se 3 (by rfl) ⟨144797, by rfl⟩) R289595
theorem R53581 : Reach 53581 := rs (se 3 (by rfl) ⟨10046, by rfl⟩) R20093
theorem R55009 : Reach 55009 := rs (se 2 (by rfl) ⟨20628, by rfl⟩) R41257
theorem R383453 : Reach 383453 := rs (se 3 (by rfl) ⟨71897, by rfl⟩) R143795
theorem R23903 : Reach 23903 := rs (se 1 (by rfl) ⟨17927, by rfl⟩) R35855
theorem R24047 : Reach 24047 := rs (se 1 (by rfl) ⟨18035, by rfl⟩) R36071
theorem R24097 : Reach 24097 := rs (se 2 (by rfl) ⟨9036, by rfl⟩) R18073
theorem R24101 : Reach 24101 := rs (se 4 (by rfl) ⟨2259, by rfl⟩) R4519
theorem R24137 : Reach 24137 := rs (se 2 (by rfl) ⟨9051, by rfl⟩) R18103
theorem R24443 : Reach 24443 := rs (se 1 (by rfl) ⟨18332, by rfl⟩) R36665
theorem R24515 : Reach 24515 := rs (se 1 (by rfl) ⟨18386, by rfl⟩) R36773
theorem R24713 : Reach 24713 := rs (se 2 (by rfl) ⟨9267, by rfl⟩) R18535
theorem R24731 : Reach 24731 := rs (se 1 (by rfl) ⟨18548, by rfl⟩) R37097
theorem R24815 : Reach 24815 := rs (se 1 (by rfl) ⟨18611, by rfl⟩) R37223
theorem R24875 : Reach 24875 := rs (se 1 (by rfl) ⟨18656, by rfl⟩) R37313
theorem R24887 : Reach 24887 := rs (se 1 (by rfl) ⟨18665, by rfl⟩) R37331
theorem R25447 : Reach 25447 := rs (se 1 (by rfl) ⟨19085, by rfl⟩) R38171
theorem R25937 : Reach 25937 := rs (se 2 (by rfl) ⟨9726, by rfl⟩) R19453
theorem R26585 : Reach 26585 := rs (se 2 (by rfl) ⟨9969, by rfl⟩) R19939
theorem R26711 : Reach 26711 := rs (se 1 (by rfl) ⟨20033, by rfl⟩) R40067
theorem R26723 : Reach 26723 := rs (se 1 (by rfl) ⟨20042, by rfl⟩) R40085
theorem R26855 : Reach 26855 := rs (se 1 (by rfl) ⟨20141, by rfl⟩) R40283
theorem R26873 : Reach 26873 := rs (se 2 (by rfl) ⟨10077, by rfl⟩) R20155
theorem R27071 : Reach 27071 := rs (se 1 (by rfl) ⟨20303, by rfl⟩) R40607
theorem R29639 : Reach 29639 := rs (se 1 (by rfl) ⟨22229, by rfl⟩) R44459
theorem R29699 : Reach 29699 := rs (se 1 (by rfl) ⟨22274, by rfl⟩) R44549
theorem R32795 : Reach 32795 := rs (se 1 (by rfl) ⟨24596, by rfl⟩) R49193
theorem R65609 : Reach 65609 := rs (se 2 (by rfl) ⟨24603, by rfl⟩) R49207
theorem R137 : Reach 137 := rs (se 2 (by rfl) ⟨51, by rfl⟩) R103
theorem R131219 : Reach 131219 := rs (se 1 (by rfl) ⟨98414, by rfl⟩) R196829
theorem R32987 : Reach 32987 := rs (se 1 (by rfl) ⟨24740, by rfl⟩) R49481
theorem R275 : Reach 275 := rs (se 1 (by rfl) ⟨206, by rfl⟩) R413
theorem R33101 : Reach 33101 := rs (se 3 (by rfl) ⟨6206, by rfl⟩) R12413
theorem R549 : Reach 549 := rs (se 4 (by rfl) ⟨51, by rfl⟩) R103
theorem R66095 : Reach 66095 := rs (se 1 (by rfl) ⟨49571, by rfl⟩) R99143
theorem R66329 : Reach 66329 := rs (se 2 (by rfl) ⟨24873, by rfl⟩) R49747
theorem R33671 : Reach 33671 := rs (se 1 (by rfl) ⟨25253, by rfl⟩) R50507
theorem R993 : Reach 993 := rs (se 2 (by rfl) ⟨372, by rfl⟩) R745
theorem R1007 : Reach 1007 := rs (se 1 (by rfl) ⟨755, by rfl⟩) R1511
theorem R1051 : Reach 1051 := rs (se 1 (by rfl) ⟨788, by rfl⟩) R1577
theorem R1101 : Reach 1101 := rs (se 3 (by rfl) ⟨206, by rfl⟩) R413
theorem R1105 : Reach 1105 := rs (se 2 (by rfl) ⟨414, by rfl⟩) R829
theorem R1115 : Reach 1115 := rs (se 1 (by rfl) ⟨836, by rfl⟩) R1673
theorem R33929 : Reach 33929 := rs (se 2 (by rfl) ⟨12723, by rfl⟩) R25447
theorem R67339 : Reach 67339 := rs (se 1 (by rfl) ⟨50504, by rfl⟩) R101009
theorem R1987 : Reach 1987 := rs (se 1 (by rfl) ⟨1490, by rfl⟩) R2981
theorem R2015 : Reach 2015 := rs (se 1 (by rfl) ⟨1511, by rfl⟩) R3023
theorem R2075 : Reach 2075 := rs (se 1 (by rfl) ⟨1556, by rfl⟩) R3113
theorem R2103 : Reach 2103 := rs (se 1 (by rfl) ⟨1577, by rfl⟩) R3155
theorem R2197 : Reach 2197 := rs (se 6 (by rfl) ⟨51, by rfl⟩) R103
theorem R2211 : Reach 2211 := rs (se 1 (by rfl) ⟨1658, by rfl⟩) R3317
theorem R2219 : Reach 2219 := rs (se 1 (by rfl) ⟨1664, by rfl⟩) R3329
theorem R2231 : Reach 2231 := rs (se 1 (by rfl) ⟨1673, by rfl⟩) R3347
theorem R3973 : Reach 3973 := rs (se 4 (by rfl) ⟨372, by rfl⟩) R745
theorem R3979 : Reach 3979 := rs (se 1 (by rfl) ⟨2984, by rfl⟩) R5969
theorem R4029 : Reach 4029 := rs (se 3 (by rfl) ⟨755, by rfl⟩) R1511
theorem R4031 : Reach 4031 := rs (se 1 (by rfl) ⟨3023, by rfl⟩) R6047
theorem R4073 : Reach 4073 := rs (se 2 (by rfl) ⟨1527, by rfl⟩) R3055
theorem R4123 : Reach 4123 := rs (se 1 (by rfl) ⟨3092, by rfl⟩) R6185
theorem R4135 : Reach 4135 := rs (se 1 (by rfl) ⟨3101, by rfl⟩) R6203
theorem R4137 : Reach 4137 := rs (se 2 (by rfl) ⟨1551, by rfl⟩) R3103
theorem R4151 : Reach 4151 := rs (se 1 (by rfl) ⟨3113, by rfl⟩) R6227
theorem R4205 : Reach 4205 := rs (se 3 (by rfl) ⟨788, by rfl⟩) R1577
theorem R4405 : Reach 4405 := rs (se 5 (by rfl) ⟨206, by rfl⟩) R413
theorem R4417 : Reach 4417 := rs (se 2 (by rfl) ⟨1656, by rfl⟩) R3313
theorem R4421 : Reach 4421 := rs (se 4 (by rfl) ⟨414, by rfl⟩) R829
theorem R4427 : Reach 4427 := rs (se 1 (by rfl) ⟨3320, by rfl⟩) R6641
theorem R4439 : Reach 4439 := rs (se 1 (by rfl) ⟨3329, by rfl⟩) R6659
theorem R4443 : Reach 4443 := rs (se 1 (by rfl) ⟨3332, by rfl⟩) R6665
theorem R4455 : Reach 4455 := rs (se 1 (by rfl) ⟨3341, by rfl⟩) R6683
theorem R4461 : Reach 4461 := rs (se 3 (by rfl) ⟨836, by rfl⟩) R1673
theorem R4473 : Reach 4473 := rs (se 2 (by rfl) ⟨1677, by rfl⟩) R3355
theorem R71441 : Reach 71441 := rs (se 2 (by rfl) ⟨26790, by rfl⟩) R53581
theorem R269347 : Reach 269347 := rs (se 1 (by rfl) ⟨202010, by rfl⟩) R404021
theorem R73345 : Reach 73345 := rs (se 2 (by rfl) ⟨27504, by rfl⟩) R55009
theorem R7949 : Reach 7949 := rs (se 3 (by rfl) ⟨1490, by rfl⟩) R2981
theorem R7953 : Reach 7953 := rs (se 2 (by rfl) ⟨2982, by rfl⟩) R5965
theorem R7959 : Reach 7959 := rs (se 1 (by rfl) ⟨5969, by rfl⟩) R11939
theorem R7967 : Reach 7967 := rs (se 1 (by rfl) ⟨5975, by rfl⟩) R11951
theorem R8033 : Reach 8033 := rs (se 2 (by rfl) ⟨3012, by rfl⟩) R6025
theorem R8041 : Reach 8041 := rs (se 2 (by rfl) ⟨3015, by rfl⟩) R6031
theorem R8061 : Reach 8061 := rs (se 3 (by rfl) ⟨1511, by rfl⟩) R3023
theorem R8063 : Reach 8063 := rs (se 1 (by rfl) ⟨6047, by rfl⟩) R12095
theorem R8073 : Reach 8073 := rs (se 2 (by rfl) ⟨3027, by rfl⟩) R6055
theorem R8147 : Reach 8147 := rs (se 1 (by rfl) ⟨6110, by rfl⟩) R12221
theorem R8171 : Reach 8171 := rs (se 1 (by rfl) ⟨6128, by rfl⟩) R12257
theorem R8247 : Reach 8247 := rs (se 1 (by rfl) ⟨6185, by rfl⟩) R12371
theorem R8271 : Reach 8271 := rs (se 1 (by rfl) ⟨6203, by rfl⟩) R12407
theorem R8275 : Reach 8275 := rs (se 1 (by rfl) ⟨6206, by rfl⟩) R12413
theorem R8283 : Reach 8283 := rs (se 1 (by rfl) ⟨6212, by rfl⟩) R12425
theorem R8295 : Reach 8295 := rs (se 1 (by rfl) ⟨6221, by rfl⟩) R12443
theorem R8301 : Reach 8301 := rs (se 3 (by rfl) ⟨1556, by rfl⟩) R3113
theorem R8413 : Reach 8413 := rs (se 3 (by rfl) ⟨1577, by rfl⟩) R3155
theorem R8431 : Reach 8431 := rs (se 1 (by rfl) ⟨6323, by rfl⟩) R12647
theorem R8789 : Reach 8789 := rs (se 8 (by rfl) ⟨51, by rfl⟩) R103
theorem R8817 : Reach 8817 := rs (se 2 (by rfl) ⟨3306, by rfl⟩) R6613
theorem R8835 : Reach 8835 := rs (se 1 (by rfl) ⟨6626, by rfl⟩) R13253
theorem R8845 : Reach 8845 := rs (se 3 (by rfl) ⟨1658, by rfl⟩) R3317
theorem R8855 : Reach 8855 := rs (se 1 (by rfl) ⟨6641, by rfl⟩) R13283
theorem R8875 : Reach 8875 := rs (se 1 (by rfl) ⟨6656, by rfl⟩) R13313
theorem R8877 : Reach 8877 := rs (se 3 (by rfl) ⟨1664, by rfl⟩) R3329
theorem R8887 : Reach 8887 := rs (se 1 (by rfl) ⟨6665, by rfl⟩) R13331
theorem R8903 : Reach 8903 := rs (se 1 (by rfl) ⟨6677, by rfl⟩) R13355
theorem R8905 : Reach 8905 := rs (se 2 (by rfl) ⟨3339, by rfl⟩) R6679
theorem R8907 : Reach 8907 := rs (se 1 (by rfl) ⟨6680, by rfl⟩) R13361
theorem R8911 : Reach 8911 := rs (se 1 (by rfl) ⟨6683, by rfl⟩) R13367
theorem R8925 : Reach 8925 := rs (se 3 (by rfl) ⟨1673, by rfl⟩) R3347
theorem R8929 : Reach 8929 := rs (se 2 (by rfl) ⟨3348, by rfl⟩) R6697
theorem R8937 : Reach 8937 := rs (se 2 (by rfl) ⟨3351, by rfl⟩) R6703
theorem R8947 : Reach 8947 := rs (se 1 (by rfl) ⟨6710, by rfl⟩) R13421
theorem R8955 : Reach 8955 := rs (se 1 (by rfl) ⟨6716, by rfl⟩) R13433
theorem R9081 : Reach 9081 := rs (se 2 (by rfl) ⟨3405, by rfl⟩) R6811
theorem R9855 : Reach 9855 := rs (se 1 (by rfl) ⟨7391, by rfl⟩) R14783
theorem R9865 : Reach 9865 := rs (se 2 (by rfl) ⟨3699, by rfl⟩) R7399
theorem R9899 : Reach 9899 := rs (se 1 (by rfl) ⟨7424, by rfl⟩) R14849
theorem R142883 : Reach 142883 := rs (se 1 (by rfl) ⟨107162, by rfl⟩) R214325
theorem R15893 : Reach 15893 := rs (se 6 (by rfl) ⟨372, by rfl⟩) R745
theorem R15917 : Reach 15917 := rs (se 3 (by rfl) ⟨2984, by rfl⟩) R5969
theorem R15929 : Reach 15929 := rs (se 2 (by rfl) ⟨5973, by rfl⟩) R11947
theorem R15935 : Reach 15935 := rs (se 1 (by rfl) ⟨11951, by rfl⟩) R23903
theorem R15977 : Reach 15977 := rs (se 2 (by rfl) ⟨5991, by rfl⟩) R11983
theorem R16025 : Reach 16025 := rs (se 2 (by rfl) ⟨6009, by rfl⟩) R12019
theorem R16031 : Reach 16031 := rs (se 1 (by rfl) ⟨12023, by rfl⟩) R24047
theorem R16067 : Reach 16067 := rs (se 1 (by rfl) ⟨12050, by rfl⟩) R24101
theorem R16091 : Reach 16091 := rs (se 1 (by rfl) ⟨12068, by rfl⟩) R24137
theorem R16121 : Reach 16121 := rs (se 2 (by rfl) ⟨6045, by rfl⟩) R12091
theorem R16249 : Reach 16249 := rs (se 2 (by rfl) ⟨6093, by rfl⟩) R12187
theorem R16295 : Reach 16295 := rs (se 1 (by rfl) ⟨12221, by rfl⟩) R24443
theorem R16343 : Reach 16343 := rs (se 1 (by rfl) ⟨12257, by rfl⟩) R24515
theorem R16409 : Reach 16409 := rs (se 2 (by rfl) ⟨6153, by rfl⟩) R12307
theorem R16475 : Reach 16475 := rs (se 1 (by rfl) ⟨12356, by rfl⟩) R24713
theorem R16481 : Reach 16481 := rs (se 2 (by rfl) ⟨6180, by rfl⟩) R12361
theorem R16487 : Reach 16487 := rs (se 1 (by rfl) ⟨12365, by rfl⟩) R24731
theorem R16493 : Reach 16493 := rs (se 3 (by rfl) ⟨3092, by rfl⟩) R6185
theorem R16541 : Reach 16541 := rs (se 3 (by rfl) ⟨3101, by rfl⟩) R6203
theorem R16543 : Reach 16543 := rs (se 1 (by rfl) ⟨12407, by rfl⟩) R24815
theorem R16553 : Reach 16553 := rs (se 2 (by rfl) ⟨6207, by rfl⟩) R12415
theorem R16583 : Reach 16583 := rs (se 1 (by rfl) ⟨12437, by rfl⟩) R24875
theorem R16591 : Reach 16591 := rs (se 1 (by rfl) ⟨12443, by rfl⟩) R24887
theorem R17291 : Reach 17291 := rs (se 1 (by rfl) ⟨12968, by rfl⟩) R25937
theorem R17621 : Reach 17621 := rs (se 7 (by rfl) ⟨206, by rfl⟩) R413
theorem R17669 : Reach 17669 := rs (se 4 (by rfl) ⟨1656, by rfl⟩) R3313
theorem R17723 : Reach 17723 := rs (se 1 (by rfl) ⟨13292, by rfl⟩) R26585
theorem R17807 : Reach 17807 := rs (se 1 (by rfl) ⟨13355, by rfl⟩) R26711
theorem R17815 : Reach 17815 := rs (se 1 (by rfl) ⟨13361, by rfl⟩) R26723
theorem R17825 : Reach 17825 := rs (se 2 (by rfl) ⟨6684, by rfl⟩) R13369
theorem R17903 : Reach 17903 := rs (se 1 (by rfl) ⟨13427, by rfl⟩) R26855
theorem R17915 : Reach 17915 := rs (se 1 (by rfl) ⟨13436, by rfl⟩) R26873
theorem R18047 : Reach 18047 := rs (se 1 (by rfl) ⟨13535, by rfl⟩) R27071
theorem R19759 : Reach 19759 := rs (se 1 (by rfl) ⟨14819, by rfl⟩) R29639
theorem R19799 : Reach 19799 := rs (se 1 (by rfl) ⟨14849, by rfl⟩) R29699
theorem R514835 : Reach 514835 := rs (se 1 (by rfl) ⟨386126, by rfl⟩) R772253
theorem R286651 : Reach 286651 := rs (se 1 (by rfl) ⟨214988, by rfl⟩) R429977
theorem R255635 : Reach 255635 := rs (se 1 (by rfl) ⟨191726, by rfl⟩) R383453
theorem R127325 : Reach 127325 := rs (se 3 (by rfl) ⟨23873, by rfl⟩) R47747
theorem R31859 : Reach 31859 := rs (se 1 (by rfl) ⟨23894, by rfl⟩) R47789
theorem R32129 : Reach 32129 := rs (se 2 (by rfl) ⟨12048, by rfl⟩) R24097
theorem R32183 : Reach 32183 := rs (se 1 (by rfl) ⟨24137, by rfl⟩) R48275
theorem R91 : Reach 91 := rs (se 1 (by rfl) ⟨68, by rfl⟩) R137
theorem R183 : Reach 183 := rs (se 1 (by rfl) ⟨137, by rfl⟩) R275
theorem R365 : Reach 365 := rs (se 3 (by rfl) ⟨68, by rfl⟩) R137
theorem R671 : Reach 671 := rs (se 1 (by rfl) ⟨503, by rfl⟩) R1007
theorem R733 : Reach 733 := rs (se 3 (by rfl) ⟨137, by rfl⟩) R275
theorem R743 : Reach 743 := rs (se 1 (by rfl) ⟨557, by rfl⟩) R1115
theorem R1343 : Reach 1343 := rs (se 1 (by rfl) ⟨1007, by rfl⟩) R2015
theorem R1383 : Reach 1383 := rs (se 1 (by rfl) ⟨1037, by rfl⟩) R2075
theorem R1401 : Reach 1401 := rs (se 2 (by rfl) ⟨525, by rfl⟩) R1051
theorem R1461 : Reach 1461 := rs (se 5 (by rfl) ⟨68, by rfl⟩) R137
theorem R1473 : Reach 1473 := rs (se 2 (by rfl) ⟨552, by rfl⟩) R1105
theorem R1479 : Reach 1479 := rs (se 1 (by rfl) ⟨1109, by rfl⟩) R2219
theorem R1487 : Reach 1487 := rs (se 1 (by rfl) ⟨1115, by rfl⟩) R2231
theorem R2649 : Reach 2649 := rs (se 2 (by rfl) ⟨993, by rfl⟩) R1987
theorem R2685 : Reach 2685 := rs (se 3 (by rfl) ⟨503, by rfl⟩) R1007
theorem R2687 : Reach 2687 := rs (se 1 (by rfl) ⟨2015, by rfl⟩) R4031
theorem R2715 : Reach 2715 := rs (se 1 (by rfl) ⟨2036, by rfl⟩) R4073
theorem R2767 : Reach 2767 := rs (se 1 (by rfl) ⟨2075, by rfl⟩) R4151
theorem R2803 : Reach 2803 := rs (se 1 (by rfl) ⟨2102, by rfl⟩) R4205
theorem R2929 : Reach 2929 := rs (se 2 (by rfl) ⟨1098, by rfl⟩) R2197
theorem R2933 : Reach 2933 := rs (se 5 (by rfl) ⟨137, by rfl⟩) R275
theorem R2947 : Reach 2947 := rs (se 1 (by rfl) ⟨2210, by rfl⟩) R4421
theorem R2951 : Reach 2951 := rs (se 1 (by rfl) ⟨2213, by rfl⟩) R4427
theorem R2959 : Reach 2959 := rs (se 1 (by rfl) ⟨2219, by rfl⟩) R4439
theorem R2973 : Reach 2973 := rs (se 3 (by rfl) ⟨557, by rfl⟩) R1115
theorem R5297 : Reach 5297 := rs (se 2 (by rfl) ⟨1986, by rfl⟩) R3973
theorem R5299 : Reach 5299 := rs (se 1 (by rfl) ⟨3974, by rfl⟩) R7949
theorem R5305 : Reach 5305 := rs (se 2 (by rfl) ⟨1989, by rfl⟩) R3979
theorem R5311 : Reach 5311 := rs (se 1 (by rfl) ⟨3983, by rfl⟩) R7967
theorem R5355 : Reach 5355 := rs (se 1 (by rfl) ⟨4016, by rfl⟩) R8033
theorem R5373 : Reach 5373 := rs (se 3 (by rfl) ⟨1007, by rfl⟩) R2015
theorem R5375 : Reach 5375 := rs (se 1 (by rfl) ⟨4031, by rfl⟩) R8063
theorem R5431 : Reach 5431 := rs (se 1 (by rfl) ⟨4073, by rfl⟩) R8147
theorem R5447 : Reach 5447 := rs (se 1 (by rfl) ⟨4085, by rfl⟩) R8171
theorem R5497 : Reach 5497 := rs (se 2 (by rfl) ⟨2061, by rfl⟩) R4123
theorem R5513 : Reach 5513 := rs (se 2 (by rfl) ⟨2067, by rfl⟩) R4135
theorem R5533 : Reach 5533 := rs (se 3 (by rfl) ⟨1037, by rfl⟩) R2075
theorem R5605 : Reach 5605 := rs (se 4 (by rfl) ⟨525, by rfl⟩) R1051
theorem R5845 : Reach 5845 := rs (se 7 (by rfl) ⟨68, by rfl⟩) R137
theorem R5859 : Reach 5859 := rs (se 1 (by rfl) ⟨4394, by rfl⟩) R8789
theorem R5873 : Reach 5873 := rs (se 2 (by rfl) ⟨2202, by rfl⟩) R4405
theorem R5889 : Reach 5889 := rs (se 2 (by rfl) ⟨2208, by rfl⟩) R4417
theorem R5893 : Reach 5893 := rs (se 4 (by rfl) ⟨552, by rfl⟩) R1105
theorem R5903 : Reach 5903 := rs (se 1 (by rfl) ⟨4427, by rfl⟩) R8855
theorem R5917 : Reach 5917 := rs (se 3 (by rfl) ⟨1109, by rfl⟩) R2219
theorem R5935 : Reach 5935 := rs (se 1 (by rfl) ⟨4451, by rfl⟩) R8903
theorem R5949 : Reach 5949 := rs (se 3 (by rfl) ⟨1115, by rfl⟩) R2231
theorem R170423 : Reach 170423 := rs (se 1 (by rfl) ⟨127817, by rfl⟩) R255635
theorem R6599 : Reach 6599 := rs (se 1 (by rfl) ⟨4949, by rfl⟩) R9899
theorem R42389 : Reach 42389 := rs (se 6 (by rfl) ⟨993, by rfl⟩) R1987
theorem R42493 : Reach 42493 := rs (se 3 (by rfl) ⟨7967, by rfl⟩) R15935
theorem R42605 : Reach 42605 := rs (se 3 (by rfl) ⟨7988, by rfl⟩) R15977
theorem R10595 : Reach 10595 := rs (se 1 (by rfl) ⟨7946, by rfl⟩) R15893
theorem R10597 : Reach 10597 := rs (se 4 (by rfl) ⟨993, by rfl⟩) R1987
theorem R10611 : Reach 10611 := rs (se 1 (by rfl) ⟨7958, by rfl⟩) R15917
theorem R10619 : Reach 10619 := rs (se 1 (by rfl) ⟨7964, by rfl⟩) R15929
theorem R10623 : Reach 10623 := rs (se 1 (by rfl) ⟨7967, by rfl⟩) R15935
theorem R10651 : Reach 10651 := rs (se 1 (by rfl) ⟨7988, by rfl⟩) R15977
theorem R10683 : Reach 10683 := rs (se 1 (by rfl) ⟨8012, by rfl⟩) R16025
theorem R10687 : Reach 10687 := rs (se 1 (by rfl) ⟨8015, by rfl⟩) R16031
theorem R10711 : Reach 10711 := rs (se 1 (by rfl) ⟨8033, by rfl⟩) R16067
theorem R10721 : Reach 10721 := rs (se 2 (by rfl) ⟨4020, by rfl⟩) R8041
theorem R10727 : Reach 10727 := rs (se 1 (by rfl) ⟨8045, by rfl⟩) R16091
theorem R10741 : Reach 10741 := rs (se 5 (by rfl) ⟨503, by rfl⟩) R1007
theorem R10747 : Reach 10747 := rs (se 1 (by rfl) ⟨8060, by rfl⟩) R16121
theorem R10749 : Reach 10749 := rs (se 3 (by rfl) ⟨2015, by rfl⟩) R4031
theorem R10861 : Reach 10861 := rs (se 3 (by rfl) ⟨2036, by rfl⟩) R4073
theorem R10863 : Reach 10863 := rs (se 1 (by rfl) ⟨8147, by rfl⟩) R16295
theorem R10895 : Reach 10895 := rs (se 1 (by rfl) ⟨8171, by rfl⟩) R16343
theorem R10939 : Reach 10939 := rs (se 1 (by rfl) ⟨8204, by rfl⟩) R16409
theorem R43739 : Reach 43739 := rs (se 1 (by rfl) ⟨32804, by rfl⟩) R65609
theorem R10983 : Reach 10983 := rs (se 1 (by rfl) ⟨8237, by rfl⟩) R16475
theorem R10987 : Reach 10987 := rs (se 1 (by rfl) ⟨8240, by rfl⟩) R16481
theorem R10991 : Reach 10991 := rs (se 1 (by rfl) ⟨8243, by rfl⟩) R16487
theorem R10995 : Reach 10995 := rs (se 1 (by rfl) ⟨8246, by rfl⟩) R16493
theorem R11027 : Reach 11027 := rs (se 1 (by rfl) ⟨8270, by rfl⟩) R16541
theorem R11033 : Reach 11033 := rs (se 2 (by rfl) ⟨4137, by rfl⟩) R8275
theorem R11035 : Reach 11035 := rs (se 1 (by rfl) ⟨8276, by rfl⟩) R16553
theorem R11055 : Reach 11055 := rs (se 1 (by rfl) ⟨8291, by rfl⟩) R16583
theorem R11069 : Reach 11069 := rs (se 3 (by rfl) ⟨2075, by rfl⟩) R4151
theorem R11213 : Reach 11213 := rs (se 3 (by rfl) ⟨2102, by rfl⟩) R4205
theorem R11217 : Reach 11217 := rs (se 2 (by rfl) ⟨4206, by rfl⟩) R8413
theorem R11241 : Reach 11241 := rs (se 2 (by rfl) ⟨4215, by rfl⟩) R8431
theorem R44063 : Reach 44063 := rs (se 1 (by rfl) ⟨33047, by rfl⟩) R66095
theorem R44219 : Reach 44219 := rs (se 1 (by rfl) ⟨33164, by rfl⟩) R66329
theorem R11527 : Reach 11527 := rs (se 1 (by rfl) ⟨8645, by rfl⟩) R17291
theorem R11717 : Reach 11717 := rs (se 4 (by rfl) ⟨1098, by rfl⟩) R2197
theorem R11733 : Reach 11733 := rs (se 7 (by rfl) ⟨137, by rfl⟩) R275
theorem R11747 : Reach 11747 := rs (se 1 (by rfl) ⟨8810, by rfl⟩) R17621
theorem R11779 : Reach 11779 := rs (se 1 (by rfl) ⟨8834, by rfl⟩) R17669
theorem R11789 : Reach 11789 := rs (se 3 (by rfl) ⟨2210, by rfl⟩) R4421
theorem R11793 : Reach 11793 := rs (se 2 (by rfl) ⟨4422, by rfl⟩) R8845
theorem R11805 : Reach 11805 := rs (se 3 (by rfl) ⟨2213, by rfl⟩) R4427
theorem R11815 : Reach 11815 := rs (se 1 (by rfl) ⟨8861, by rfl⟩) R17723
theorem R11833 : Reach 11833 := rs (se 2 (by rfl) ⟨4437, by rfl⟩) R8875
theorem R11837 : Reach 11837 := rs (se 3 (by rfl) ⟨2219, by rfl⟩) R4439
theorem R11849 : Reach 11849 := rs (se 2 (by rfl) ⟨4443, by rfl⟩) R8887
theorem R11871 : Reach 11871 := rs (se 1 (by rfl) ⟨8903, by rfl⟩) R17807
theorem R11873 : Reach 11873 := rs (se 2 (by rfl) ⟨4452, by rfl⟩) R8905
theorem R11881 : Reach 11881 := rs (se 2 (by rfl) ⟨4455, by rfl⟩) R8911
theorem R11883 : Reach 11883 := rs (se 1 (by rfl) ⟨8912, by rfl⟩) R17825
theorem R11893 : Reach 11893 := rs (se 5 (by rfl) ⟨557, by rfl⟩) R1115
theorem R11905 : Reach 11905 := rs (se 2 (by rfl) ⟨4464, by rfl⟩) R8929
theorem R11929 : Reach 11929 := rs (se 2 (by rfl) ⟨4473, by rfl⟩) R8947
theorem R11935 : Reach 11935 := rs (se 1 (by rfl) ⟨8951, by rfl⟩) R17903
theorem R11943 : Reach 11943 := rs (se 1 (by rfl) ⟨8957, by rfl⟩) R17915
theorem R12031 : Reach 12031 := rs (se 1 (by rfl) ⟨9023, by rfl⟩) R18047
theorem R13153 : Reach 13153 := rs (se 2 (by rfl) ⟨4932, by rfl⟩) R9865
theorem R13199 : Reach 13199 := rs (se 1 (by rfl) ⟨9899, by rfl⟩) R19799
theorem R46109 : Reach 46109 := rs (se 3 (by rfl) ⟨8645, by rfl⟩) R17291
theorem R47627 : Reach 47627 := rs (se 1 (by rfl) ⟨35720, by rfl⟩) R71441
theorem R47717 : Reach 47717 := rs (se 4 (by rfl) ⟨4473, by rfl⟩) R8947
theorem R343223 : Reach 343223 := rs (se 1 (by rfl) ⟨257417, by rfl⟩) R514835
theorem R84883 : Reach 84883 := rs (se 1 (by rfl) ⟨63662, by rfl⟩) R127325
theorem R21221 : Reach 21221 := rs (se 4 (by rfl) ⟨1989, by rfl⟩) R3979
theorem R21239 : Reach 21239 := rs (se 1 (by rfl) ⟨15929, by rfl⟩) R31859
theorem R21419 : Reach 21419 := rs (se 1 (by rfl) ⟨16064, by rfl⟩) R32129
theorem R21455 : Reach 21455 := rs (se 1 (by rfl) ⟨16091, by rfl⟩) R32183
theorem R21665 : Reach 21665 := rs (se 2 (by rfl) ⟨8124, by rfl⟩) R16249
theorem R21725 : Reach 21725 := rs (se 3 (by rfl) ⟨4073, by rfl⟩) R8147
theorem R382201 : Reach 382201 := rs (se 2 (by rfl) ⟨143325, by rfl⟩) R286651
theorem R21863 : Reach 21863 := rs (se 1 (by rfl) ⟨16397, by rfl⟩) R32795
theorem R87479 : Reach 87479 := rs (se 1 (by rfl) ⟨65609, by rfl⟩) R131219
theorem R21991 : Reach 21991 := rs (se 1 (by rfl) ⟨16493, by rfl⟩) R32987
theorem R22067 : Reach 22067 := rs (se 1 (by rfl) ⟨16550, by rfl⟩) R33101
theorem R22121 : Reach 22121 := rs (se 2 (by rfl) ⟨8295, by rfl⟩) R16591
theorem R22133 : Reach 22133 := rs (se 5 (by rfl) ⟨1037, by rfl⟩) R2075
theorem R87965 : Reach 87965 := rs (se 3 (by rfl) ⟨16493, by rfl⟩) R32987
theorem R22447 : Reach 22447 := rs (se 1 (by rfl) ⟨16835, by rfl⟩) R33671
theorem R22619 : Reach 22619 := rs (se 1 (by rfl) ⟨16964, by rfl⟩) R33929
theorem R88229 : Reach 88229 := rs (se 4 (by rfl) ⟨8271, by rfl⟩) R16543
theorem R23381 : Reach 23381 := rs (se 9 (by rfl) ⟨68, by rfl⟩) R137
theorem R23669 : Reach 23669 := rs (se 5 (by rfl) ⟨1109, by rfl⟩) R2219
theorem R23741 : Reach 23741 := rs (se 3 (by rfl) ⟨4451, by rfl⟩) R8903
theorem R23753 : Reach 23753 := rs (se 2 (by rfl) ⟨8907, by rfl⟩) R17815
theorem R89785 : Reach 89785 := rs (se 2 (by rfl) ⟨33669, by rfl⟩) R67339
theorem R26345 : Reach 26345 := rs (se 2 (by rfl) ⟨9879, by rfl⟩) R19759
theorem R95255 : Reach 95255 := rs (se 1 (by rfl) ⟨71441, by rfl⟩) R142883
theorem R359129 : Reach 359129 := rs (se 2 (by rfl) ⟨134673, by rfl⟩) R269347
theorem R97793 : Reach 97793 := rs (se 2 (by rfl) ⟨36672, by rfl⟩) R73345
theorem R121 : Reach 121 := rs (se 2 (by rfl) ⟨45, by rfl⟩) R91
theorem R243 : Reach 243 := rs (se 1 (by rfl) ⟨182, by rfl⟩) R365
theorem R447 : Reach 447 := rs (se 1 (by rfl) ⟨335, by rfl⟩) R671
theorem R485 : Reach 485 := rs (se 4 (by rfl) ⟨45, by rfl⟩) R91
theorem R495 : Reach 495 := rs (se 1 (by rfl) ⟨371, by rfl⟩) R743
theorem R895 : Reach 895 := rs (se 1 (by rfl) ⟨671, by rfl⟩) R1343
theorem R973 : Reach 973 := rs (se 3 (by rfl) ⟨182, by rfl⟩) R365
theorem R977 : Reach 977 := rs (se 2 (by rfl) ⟨366, by rfl⟩) R733
theorem R991 : Reach 991 := rs (se 1 (by rfl) ⟨743, by rfl⟩) R1487
theorem R1789 : Reach 1789 := rs (se 3 (by rfl) ⟨335, by rfl⟩) R671
theorem R1791 : Reach 1791 := rs (se 1 (by rfl) ⟨1343, by rfl⟩) R2687
theorem R1941 : Reach 1941 := rs (se 6 (by rfl) ⟨45, by rfl⟩) R91
theorem R1955 : Reach 1955 := rs (se 1 (by rfl) ⟨1466, by rfl⟩) R2933
theorem R1967 : Reach 1967 := rs (se 1 (by rfl) ⟨1475, by rfl⟩) R2951
theorem R1981 : Reach 1981 := rs (se 3 (by rfl) ⟨371, by rfl⟩) R743
theorem R3531 : Reach 3531 := rs (se 1 (by rfl) ⟨2648, by rfl⟩) R5297
theorem R3581 : Reach 3581 := rs (se 3 (by rfl) ⟨671, by rfl⟩) R1343
theorem R3583 : Reach 3583 := rs (se 1 (by rfl) ⟨2687, by rfl⟩) R5375
theorem R3631 : Reach 3631 := rs (se 1 (by rfl) ⟨2723, by rfl⟩) R5447
theorem R3675 : Reach 3675 := rs (se 1 (by rfl) ⟨2756, by rfl⟩) R5513
theorem R3689 : Reach 3689 := rs (se 2 (by rfl) ⟨1383, by rfl⟩) R2767
theorem R3737 : Reach 3737 := rs (se 2 (by rfl) ⟨1401, by rfl⟩) R2803
theorem R3893 : Reach 3893 := rs (se 5 (by rfl) ⟨182, by rfl⟩) R365
theorem R3905 : Reach 3905 := rs (se 2 (by rfl) ⟨1464, by rfl⟩) R2929
theorem R3909 : Reach 3909 := rs (se 4 (by rfl) ⟨366, by rfl⟩) R733
theorem R3915 : Reach 3915 := rs (se 1 (by rfl) ⟨2936, by rfl⟩) R5873
theorem R3929 : Reach 3929 := rs (se 2 (by rfl) ⟨1473, by rfl⟩) R2947
theorem R3935 : Reach 3935 := rs (se 1 (by rfl) ⟨2951, by rfl⟩) R5903
theorem R3945 : Reach 3945 := rs (se 2 (by rfl) ⟨1479, by rfl⟩) R2959
theorem R3965 : Reach 3965 := rs (se 3 (by rfl) ⟨743, by rfl⟩) R1487
theorem R4399 : Reach 4399 := rs (se 1 (by rfl) ⟨3299, by rfl⟩) R6599
theorem R2038405 : Reach 2038405 := rs (se 4 (by rfl) ⟨191100, by rfl⟩) R382201
theorem R7063 : Reach 7063 := rs (se 1 (by rfl) ⟨5297, by rfl⟩) R10595
theorem R7065 : Reach 7065 := rs (se 2 (by rfl) ⟨2649, by rfl⟩) R5299
theorem R7073 : Reach 7073 := rs (se 2 (by rfl) ⟨2652, by rfl⟩) R5305
theorem R7079 : Reach 7079 := rs (se 1 (by rfl) ⟨5309, by rfl⟩) R10619
theorem R7081 : Reach 7081 := rs (se 2 (by rfl) ⟨2655, by rfl⟩) R5311
theorem R7147 : Reach 7147 := rs (se 1 (by rfl) ⟨5360, by rfl⟩) R10721
theorem R7151 : Reach 7151 := rs (se 1 (by rfl) ⟨5363, by rfl⟩) R10727
theorem R7157 : Reach 7157 := rs (se 5 (by rfl) ⟨335, by rfl⟩) R671
theorem R7165 : Reach 7165 := rs (se 3 (by rfl) ⟨1343, by rfl⟩) R2687
theorem R7241 : Reach 7241 := rs (se 2 (by rfl) ⟨2715, by rfl⟩) R5431
theorem R7263 : Reach 7263 := rs (se 1 (by rfl) ⟨5447, by rfl⟩) R10895
theorem R7327 : Reach 7327 := rs (se 1 (by rfl) ⟨5495, by rfl⟩) R10991
theorem R7329 : Reach 7329 := rs (se 2 (by rfl) ⟨2748, by rfl⟩) R5497
theorem R7351 : Reach 7351 := rs (se 1 (by rfl) ⟨5513, by rfl⟩) R11027
theorem R7355 : Reach 7355 := rs (se 1 (by rfl) ⟨5516, by rfl⟩) R11033
theorem R7377 : Reach 7377 := rs (se 2 (by rfl) ⟨2766, by rfl⟩) R5533
theorem R7379 : Reach 7379 := rs (se 1 (by rfl) ⟨5534, by rfl⟩) R11069
theorem R7473 : Reach 7473 := rs (se 2 (by rfl) ⟨2802, by rfl⟩) R5605
theorem R7475 : Reach 7475 := rs (se 1 (by rfl) ⟨5606, by rfl⟩) R11213
theorem R7765 : Reach 7765 := rs (se 8 (by rfl) ⟨45, by rfl⟩) R91
theorem R7793 : Reach 7793 := rs (se 2 (by rfl) ⟨2922, by rfl⟩) R5845
theorem R7811 : Reach 7811 := rs (se 1 (by rfl) ⟨5858, by rfl⟩) R11717
theorem R7821 : Reach 7821 := rs (se 3 (by rfl) ⟨1466, by rfl⟩) R2933
theorem R7831 : Reach 7831 := rs (se 1 (by rfl) ⟨5873, by rfl⟩) R11747
theorem R7857 : Reach 7857 := rs (se 2 (by rfl) ⟨2946, by rfl⟩) R5893
theorem R7859 : Reach 7859 := rs (se 1 (by rfl) ⟨5894, by rfl⟩) R11789
theorem R7869 : Reach 7869 := rs (se 3 (by rfl) ⟨1475, by rfl⟩) R2951
theorem R7889 : Reach 7889 := rs (se 2 (by rfl) ⟨2958, by rfl⟩) R5917
theorem R7891 : Reach 7891 := rs (se 1 (by rfl) ⟨5918, by rfl⟩) R11837
theorem R7899 : Reach 7899 := rs (se 1 (by rfl) ⟨5924, by rfl⟩) R11849
theorem R7913 : Reach 7913 := rs (se 2 (by rfl) ⟨2967, by rfl⟩) R5935
theorem R7915 : Reach 7915 := rs (se 1 (by rfl) ⟨5936, by rfl⟩) R11873
theorem R7925 : Reach 7925 := rs (se 5 (by rfl) ⟨371, by rfl⟩) R743
theorem R8799 : Reach 8799 := rs (se 1 (by rfl) ⟨6599, by rfl⟩) R13199
theorem R239419 : Reach 239419 := rs (se 1 (by rfl) ⟨179564, by rfl⟩) R359129
theorem R14125 : Reach 14125 := rs (se 3 (by rfl) ⟨2648, by rfl⟩) R5297
theorem R14129 : Reach 14129 := rs (se 2 (by rfl) ⟨5298, by rfl⟩) R10597
theorem R14147 : Reach 14147 := rs (se 1 (by rfl) ⟨10610, by rfl⟩) R21221
theorem R14159 : Reach 14159 := rs (se 1 (by rfl) ⟨10619, by rfl⟩) R21239
theorem R14201 : Reach 14201 := rs (se 2 (by rfl) ⟨5325, by rfl⟩) R10651
theorem R14249 : Reach 14249 := rs (se 2 (by rfl) ⟨5343, by rfl⟩) R10687
theorem R14279 : Reach 14279 := rs (se 1 (by rfl) ⟨10709, by rfl⟩) R21419
theorem R14303 : Reach 14303 := rs (se 1 (by rfl) ⟨10727, by rfl⟩) R21455
theorem R14321 : Reach 14321 := rs (se 2 (by rfl) ⟨5370, by rfl⟩) R10741
theorem R14333 : Reach 14333 := rs (se 3 (by rfl) ⟨2687, by rfl⟩) R5375
theorem R14483 : Reach 14483 := rs (se 1 (by rfl) ⟨10862, by rfl⟩) R21725
theorem R14525 : Reach 14525 := rs (se 3 (by rfl) ⟨2723, by rfl⟩) R5447
theorem R14575 : Reach 14575 := rs (se 1 (by rfl) ⟨10931, by rfl⟩) R21863
theorem R14585 : Reach 14585 := rs (se 2 (by rfl) ⟨5469, by rfl⟩) R10939
theorem R14701 : Reach 14701 := rs (se 3 (by rfl) ⟨2756, by rfl⟩) R5513
theorem R14711 : Reach 14711 := rs (se 1 (by rfl) ⟨11033, by rfl⟩) R22067
theorem R14747 : Reach 14747 := rs (se 1 (by rfl) ⟨11060, by rfl⟩) R22121
theorem R14755 : Reach 14755 := rs (se 1 (by rfl) ⟨11066, by rfl⟩) R22133
theorem R113177 : Reach 113177 := rs (se 2 (by rfl) ⟨42441, by rfl⟩) R84883
theorem R15079 : Reach 15079 := rs (se 1 (by rfl) ⟨11309, by rfl⟩) R22619
theorem R113615 : Reach 113615 := rs (se 1 (by rfl) ⟨85211, by rfl⟩) R170423
theorem R15587 : Reach 15587 := rs (se 1 (by rfl) ⟨11690, by rfl⟩) R23381
theorem R15779 : Reach 15779 := rs (se 1 (by rfl) ⟨11834, by rfl⟩) R23669
theorem R15781 : Reach 15781 := rs (se 4 (by rfl) ⟨1479, by rfl⟩) R2959
theorem R15827 : Reach 15827 := rs (se 1 (by rfl) ⟨11870, by rfl⟩) R23741
theorem R15835 : Reach 15835 := rs (se 1 (by rfl) ⟨11876, by rfl⟩) R23753
theorem R15857 : Reach 15857 := rs (se 2 (by rfl) ⟨5946, by rfl⟩) R11893
theorem R15905 : Reach 15905 := rs (se 2 (by rfl) ⟨5964, by rfl⟩) R11929
theorem R15913 : Reach 15913 := rs (se 2 (by rfl) ⟨5967, by rfl⟩) R11935
theorem R17537 : Reach 17537 := rs (se 2 (by rfl) ⟨6576, by rfl⟩) R13153
theorem R17563 : Reach 17563 := rs (se 1 (by rfl) ⟨13172, by rfl⟩) R26345
theorem R17597 : Reach 17597 := rs (se 3 (by rfl) ⟨3299, by rfl⟩) R6599
theorem R119713 : Reach 119713 := rs (se 2 (by rfl) ⟨44892, by rfl⟩) R89785
theorem R119717 : Reach 119717 := rs (se 4 (by rfl) ⟨11223, by rfl⟩) R22447
theorem R56657 : Reach 56657 := rs (se 2 (by rfl) ⟨21246, by rfl⟩) R42493
theorem R57773 : Reach 57773 := rs (se 3 (by rfl) ⟨10832, by rfl⟩) R21665
theorem R58319 : Reach 58319 := rs (se 1 (by rfl) ⟨43739, by rfl⟩) R87479
theorem R58643 : Reach 58643 := rs (se 1 (by rfl) ⟨43982, by rfl⟩) R87965
theorem R58805 : Reach 58805 := rs (se 5 (by rfl) ⟨2756, by rfl⟩) R5513
theorem R58819 : Reach 58819 := rs (se 1 (by rfl) ⟨44114, by rfl⟩) R88229
theorem R28259 : Reach 28259 := rs (se 1 (by rfl) ⟨21194, by rfl⟩) R42389
theorem R28403 : Reach 28403 := rs (se 1 (by rfl) ⟨21302, by rfl⟩) R42605
theorem R29159 : Reach 29159 := rs (se 1 (by rfl) ⟨21869, by rfl⟩) R43739
theorem R29321 : Reach 29321 := rs (se 2 (by rfl) ⟨10995, by rfl⟩) R21991
theorem R29375 : Reach 29375 := rs (se 1 (by rfl) ⟨22031, by rfl⟩) R44063
theorem R29479 : Reach 29479 := rs (se 1 (by rfl) ⟨22109, by rfl⟩) R44219
theorem R29929 : Reach 29929 := rs (se 2 (by rfl) ⟨11223, by rfl⟩) R22447
theorem R63341 : Reach 63341 := rs (se 3 (by rfl) ⟨11876, by rfl⟩) R23753
theorem R63503 : Reach 63503 := rs (se 1 (by rfl) ⟨47627, by rfl⟩) R95255
theorem R30739 : Reach 30739 := rs (se 1 (by rfl) ⟨23054, by rfl⟩) R46109
theorem R31661 : Reach 31661 := rs (se 3 (by rfl) ⟨5936, by rfl⟩) R11873
theorem R31751 : Reach 31751 := rs (se 1 (by rfl) ⟨23813, by rfl⟩) R47627
theorem R31811 : Reach 31811 := rs (se 1 (by rfl) ⟨23858, by rfl⟩) R47717
theorem R228815 : Reach 228815 := rs (se 1 (by rfl) ⟨171611, by rfl⟩) R343223
theorem R65195 : Reach 65195 := rs (se 1 (by rfl) ⟨48896, by rfl⟩) R97793
theorem R161 : Reach 161 := rs (se 2 (by rfl) ⟨60, by rfl⟩) R121
theorem R323 : Reach 323 := rs (se 1 (by rfl) ⟨242, by rfl⟩) R485
theorem R645 : Reach 645 := rs (se 4 (by rfl) ⟨60, by rfl⟩) R121
theorem R651 : Reach 651 := rs (se 1 (by rfl) ⟨488, by rfl⟩) R977
theorem R1193 : Reach 1193 := rs (se 2 (by rfl) ⟨447, by rfl⟩) R895
theorem R1293 : Reach 1293 := rs (se 3 (by rfl) ⟨242, by rfl⟩) R485
theorem R1297 : Reach 1297 := rs (se 2 (by rfl) ⟨486, by rfl⟩) R973
theorem R1303 : Reach 1303 := rs (se 1 (by rfl) ⟨977, by rfl⟩) R1955
theorem R1311 : Reach 1311 := rs (se 1 (by rfl) ⟨983, by rfl⟩) R1967
theorem R1321 : Reach 1321 := rs (se 2 (by rfl) ⟨495, by rfl⟩) R991
theorem R2385 : Reach 2385 := rs (se 2 (by rfl) ⟨894, by rfl⟩) R1789
theorem R2387 : Reach 2387 := rs (se 1 (by rfl) ⟨1790, by rfl⟩) R3581
theorem R2459 : Reach 2459 := rs (se 1 (by rfl) ⟨1844, by rfl⟩) R3689
theorem R2491 : Reach 2491 := rs (se 1 (by rfl) ⟨1868, by rfl⟩) R3737
theorem R2581 : Reach 2581 := rs (se 6 (by rfl) ⟨60, by rfl⟩) R121
theorem R2595 : Reach 2595 := rs (se 1 (by rfl) ⟨1946, by rfl⟩) R3893
theorem R2603 : Reach 2603 := rs (se 1 (by rfl) ⟨1952, by rfl⟩) R3905
theorem R2605 : Reach 2605 := rs (se 3 (by rfl) ⟨488, by rfl⟩) R977
theorem R2619 : Reach 2619 := rs (se 1 (by rfl) ⟨1964, by rfl⟩) R3929
theorem R2623 : Reach 2623 := rs (se 1 (by rfl) ⟨1967, by rfl⟩) R3935
theorem R2641 : Reach 2641 := rs (se 2 (by rfl) ⟨990, by rfl⟩) R1981
theorem R2643 : Reach 2643 := rs (se 1 (by rfl) ⟨1982, by rfl⟩) R3965
theorem R4715 : Reach 4715 := rs (se 1 (by rfl) ⟨3536, by rfl⟩) R7073
theorem R4719 : Reach 4719 := rs (se 1 (by rfl) ⟨3539, by rfl⟩) R7079
theorem R4767 : Reach 4767 := rs (se 1 (by rfl) ⟨3575, by rfl⟩) R7151
theorem R4771 : Reach 4771 := rs (se 1 (by rfl) ⟨3578, by rfl⟩) R7157
theorem R4773 : Reach 4773 := rs (se 4 (by rfl) ⟨447, by rfl⟩) R895
theorem R4777 : Reach 4777 := rs (se 2 (by rfl) ⟨1791, by rfl⟩) R3583
theorem R4827 : Reach 4827 := rs (se 1 (by rfl) ⟨3620, by rfl⟩) R7241
theorem R4841 : Reach 4841 := rs (se 2 (by rfl) ⟨1815, by rfl⟩) R3631
theorem R4903 : Reach 4903 := rs (se 1 (by rfl) ⟨3677, by rfl⟩) R7355
theorem R4919 : Reach 4919 := rs (se 1 (by rfl) ⟨3689, by rfl⟩) R7379
theorem R4983 : Reach 4983 := rs (se 1 (by rfl) ⟨3737, by rfl⟩) R7475
theorem R5173 : Reach 5173 := rs (se 5 (by rfl) ⟨242, by rfl⟩) R485
theorem R5189 : Reach 5189 := rs (se 4 (by rfl) ⟨486, by rfl⟩) R973
theorem R5195 : Reach 5195 := rs (se 1 (by rfl) ⟨3896, by rfl⟩) R7793
theorem R5207 : Reach 5207 := rs (se 1 (by rfl) ⟨3905, by rfl⟩) R7811
theorem R5213 : Reach 5213 := rs (se 3 (by rfl) ⟨977, by rfl⟩) R1955
theorem R5239 : Reach 5239 := rs (se 1 (by rfl) ⟨3929, by rfl⟩) R7859
theorem R5245 : Reach 5245 := rs (se 3 (by rfl) ⟨983, by rfl⟩) R1967
theorem R5259 : Reach 5259 := rs (se 1 (by rfl) ⟨3944, by rfl⟩) R7889
theorem R5275 : Reach 5275 := rs (se 1 (by rfl) ⟨3956, by rfl⟩) R7913
theorem R5283 : Reach 5283 := rs (se 1 (by rfl) ⟨3962, by rfl⟩) R7925
theorem R5285 : Reach 5285 := rs (se 4 (by rfl) ⟨495, by rfl⟩) R991
theorem R38515 : Reach 38515 := rs (se 1 (by rfl) ⟨28886, by rfl⟩) R57773
theorem R5865 : Reach 5865 := rs (se 2 (by rfl) ⟨2199, by rfl⟩) R4399
theorem R38879 : Reach 38879 := rs (se 1 (by rfl) ⟨29159, by rfl⟩) R58319
theorem R38893 : Reach 38893 := rs (se 3 (by rfl) ⟨7292, by rfl⟩) R14585
theorem R39095 : Reach 39095 := rs (se 1 (by rfl) ⟨29321, by rfl⟩) R58643
theorem R39203 : Reach 39203 := rs (se 1 (by rfl) ⟨29402, by rfl⟩) R58805
theorem R39305 : Reach 39305 := rs (se 2 (by rfl) ⟨14739, by rfl⟩) R29479
theorem R301805 : Reach 301805 := rs (se 3 (by rfl) ⟨56588, by rfl⟩) R113177
theorem R39905 : Reach 39905 := rs (se 2 (by rfl) ⟨14964, by rfl⟩) R29929
theorem R40985 : Reach 40985 := rs (se 2 (by rfl) ⟨15369, by rfl⟩) R30739
theorem R41525 : Reach 41525 := rs (se 5 (by rfl) ⟨1946, by rfl⟩) R3893
theorem R9417 : Reach 9417 := rs (se 2 (by rfl) ⟨3531, by rfl⟩) R7063
theorem R9419 : Reach 9419 := rs (se 1 (by rfl) ⟨7064, by rfl⟩) R14129
theorem R9431 : Reach 9431 := rs (se 1 (by rfl) ⟨7073, by rfl⟩) R14147
theorem R9439 : Reach 9439 := rs (se 1 (by rfl) ⟨7079, by rfl⟩) R14159
theorem R9441 : Reach 9441 := rs (se 2 (by rfl) ⟨3540, by rfl⟩) R7081
theorem R42227 : Reach 42227 := rs (se 1 (by rfl) ⟨31670, by rfl⟩) R63341
theorem R9467 : Reach 9467 := rs (se 1 (by rfl) ⟨7100, by rfl⟩) R14201
theorem R9499 : Reach 9499 := rs (se 1 (by rfl) ⟨7124, by rfl⟩) R14249
theorem R9519 : Reach 9519 := rs (se 1 (by rfl) ⟨7139, by rfl⟩) R14279
theorem R9529 : Reach 9529 := rs (se 2 (by rfl) ⟨3573, by rfl⟩) R7147
theorem R9535 : Reach 9535 := rs (se 1 (by rfl) ⟨7151, by rfl⟩) R14303
theorem R9541 : Reach 9541 := rs (se 4 (by rfl) ⟨894, by rfl⟩) R1789
theorem R9547 : Reach 9547 := rs (se 1 (by rfl) ⟨7160, by rfl⟩) R14321
theorem R9549 : Reach 9549 := rs (se 3 (by rfl) ⟨1790, by rfl⟩) R3581
theorem R9553 : Reach 9553 := rs (se 2 (by rfl) ⟨3582, by rfl⟩) R7165
theorem R9555 : Reach 9555 := rs (se 1 (by rfl) ⟨7166, by rfl⟩) R14333
theorem R42335 : Reach 42335 := rs (se 1 (by rfl) ⟨31751, by rfl⟩) R63503
theorem R9655 : Reach 9655 := rs (se 1 (by rfl) ⟨7241, by rfl⟩) R14483
theorem R9683 : Reach 9683 := rs (se 1 (by rfl) ⟨7262, by rfl⟩) R14525
theorem R9723 : Reach 9723 := rs (se 1 (by rfl) ⟨7292, by rfl⟩) R14585
theorem R9769 : Reach 9769 := rs (se 2 (by rfl) ⟨3663, by rfl⟩) R7327
theorem R9801 : Reach 9801 := rs (se 2 (by rfl) ⟨3675, by rfl⟩) R7351
theorem R9807 : Reach 9807 := rs (se 1 (by rfl) ⟨7355, by rfl⟩) R14711
theorem R9831 : Reach 9831 := rs (se 1 (by rfl) ⟨7373, by rfl⟩) R14747
theorem R9837 : Reach 9837 := rs (se 3 (by rfl) ⟨1844, by rfl⟩) R3689
theorem R75451 : Reach 75451 := rs (se 1 (by rfl) ⟨56588, by rfl⟩) R113177
theorem R9965 : Reach 9965 := rs (se 3 (by rfl) ⟨1868, by rfl⟩) R3737
theorem R75743 : Reach 75743 := rs (se 1 (by rfl) ⟨56807, by rfl⟩) R113615
theorem R10325 : Reach 10325 := rs (se 8 (by rfl) ⟨60, by rfl⟩) R121
theorem R10353 : Reach 10353 := rs (se 2 (by rfl) ⟨3882, by rfl⟩) R7765
theorem R10381 : Reach 10381 := rs (se 3 (by rfl) ⟨1946, by rfl⟩) R3893
theorem R10391 : Reach 10391 := rs (se 1 (by rfl) ⟨7793, by rfl⟩) R15587
theorem R10413 : Reach 10413 := rs (se 3 (by rfl) ⟨1952, by rfl⟩) R3905
theorem R10421 : Reach 10421 := rs (se 5 (by rfl) ⟨488, by rfl⟩) R977
theorem R10441 : Reach 10441 := rs (se 2 (by rfl) ⟨3915, by rfl⟩) R7831
theorem R10477 : Reach 10477 := rs (se 3 (by rfl) ⟨1964, by rfl⟩) R3929
theorem R10493 : Reach 10493 := rs (se 3 (by rfl) ⟨1967, by rfl⟩) R3935
theorem R10519 : Reach 10519 := rs (se 1 (by rfl) ⟨7889, by rfl⟩) R15779
theorem R10521 : Reach 10521 := rs (se 2 (by rfl) ⟨3945, by rfl⟩) R7891
theorem R10551 : Reach 10551 := rs (se 1 (by rfl) ⟨7913, by rfl⟩) R15827
theorem R10553 : Reach 10553 := rs (se 2 (by rfl) ⟨3957, by rfl⟩) R7915
theorem R10565 : Reach 10565 := rs (se 4 (by rfl) ⟨990, by rfl⟩) R1981
theorem R10571 : Reach 10571 := rs (se 1 (by rfl) ⟨7928, by rfl⟩) R15857
theorem R10573 : Reach 10573 := rs (se 3 (by rfl) ⟨1982, by rfl⟩) R3965
theorem R10603 : Reach 10603 := rs (se 1 (by rfl) ⟨7952, by rfl⟩) R15905
theorem R43463 : Reach 43463 := rs (se 1 (by rfl) ⟨32597, by rfl⟩) R65195
theorem R11691 : Reach 11691 := rs (se 1 (by rfl) ⟨8768, by rfl⟩) R17537
theorem R11731 : Reach 11731 := rs (se 1 (by rfl) ⟨8798, by rfl⟩) R17597
theorem R78425 : Reach 78425 := rs (se 2 (by rfl) ⟨29409, by rfl⟩) R58819
theorem R79811 : Reach 79811 := rs (se 1 (by rfl) ⟨59858, by rfl⟩) R119717
theorem R18833 : Reach 18833 := rs (se 2 (by rfl) ⟨7062, by rfl⟩) R14125
theorem R18839 : Reach 18839 := rs (se 1 (by rfl) ⟨14129, by rfl⟩) R28259
theorem R18935 : Reach 18935 := rs (se 1 (by rfl) ⟨14201, by rfl⟩) R28403
theorem R19085 : Reach 19085 := rs (se 3 (by rfl) ⟨3578, by rfl⟩) R7157
theorem R19109 : Reach 19109 := rs (se 4 (by rfl) ⟨1791, by rfl⟩) R3583
theorem R84829 : Reach 84829 := rs (se 3 (by rfl) ⟨15905, by rfl⟩) R31811
theorem R19433 : Reach 19433 := rs (se 2 (by rfl) ⟨7287, by rfl⟩) R14575
theorem R19439 : Reach 19439 := rs (se 1 (by rfl) ⟨14579, by rfl⟩) R29159
theorem R19547 : Reach 19547 := rs (se 1 (by rfl) ⟨14660, by rfl⟩) R29321
theorem R19583 : Reach 19583 := rs (se 1 (by rfl) ⟨14687, by rfl⟩) R29375
theorem R19601 : Reach 19601 := rs (se 2 (by rfl) ⟨7350, by rfl⟩) R14701
theorem R19673 : Reach 19673 := rs (se 2 (by rfl) ⟨7377, by rfl⟩) R14755
theorem R151085 : Reach 151085 := rs (se 3 (by rfl) ⟨28328, by rfl⟩) R56657
theorem R20105 : Reach 20105 := rs (se 2 (by rfl) ⟨7539, by rfl⟩) R15079
theorem R21041 : Reach 21041 := rs (se 2 (by rfl) ⟨7890, by rfl⟩) R15781
theorem R21107 : Reach 21107 := rs (se 1 (by rfl) ⟨15830, by rfl⟩) R31661
theorem R21113 : Reach 21113 := rs (se 2 (by rfl) ⟨7917, by rfl⟩) R15835
theorem R21167 : Reach 21167 := rs (se 1 (by rfl) ⟨15875, by rfl⟩) R31751
theorem R21217 : Reach 21217 := rs (se 2 (by rfl) ⟨7956, by rfl⟩) R15913
theorem R152543 : Reach 152543 := rs (se 1 (by rfl) ⟨114407, by rfl⟩) R228815
theorem R23417 : Reach 23417 := rs (se 2 (by rfl) ⟨8781, by rfl⟩) R17563
theorem R159617 : Reach 159617 := rs (se 2 (by rfl) ⟨59856, by rfl⟩) R119713
theorem R2717873 : Reach 2717873 := rs (se 2 (by rfl) ⟨1019202, by rfl⟩) R2038405
theorem R1276901 : Reach 1276901 := rs (se 4 (by rfl) ⟨119709, by rfl⟩) R239419
theorem R107 : Reach 107 := rs (se 1 (by rfl) ⟨80, by rfl⟩) R161
theorem R215 : Reach 215 := rs (se 1 (by rfl) ⟨161, by rfl⟩) R323
theorem R429 : Reach 429 := rs (se 3 (by rfl) ⟨80, by rfl⟩) R161
theorem R795 : Reach 795 := rs (se 1 (by rfl) ⟨596, by rfl⟩) R1193
theorem R861 : Reach 861 := rs (se 3 (by rfl) ⟨161, by rfl⟩) R323
theorem R1591 : Reach 1591 := rs (se 1 (by rfl) ⟨1193, by rfl⟩) R2387
theorem R1639 : Reach 1639 := rs (se 1 (by rfl) ⟨1229, by rfl⟩) R2459
theorem R1717 : Reach 1717 := rs (se 5 (by rfl) ⟨80, by rfl⟩) R161
theorem R1729 : Reach 1729 := rs (se 2 (by rfl) ⟨648, by rfl⟩) R1297
theorem R1735 : Reach 1735 := rs (se 1 (by rfl) ⟨1301, by rfl⟩) R2603
theorem R1737 : Reach 1737 := rs (se 2 (by rfl) ⟨651, by rfl⟩) R1303
theorem R1761 : Reach 1761 := rs (se 2 (by rfl) ⟨660, by rfl⟩) R1321
theorem R100601 : Reach 100601 := rs (se 2 (by rfl) ⟨37725, by rfl⟩) R75451
theorem R100723 : Reach 100723 := rs (se 1 (by rfl) ⟨75542, by rfl⟩) R151085
theorem R3143 : Reach 3143 := rs (se 1 (by rfl) ⟨2357, by rfl⟩) R4715
theorem R3181 : Reach 3181 := rs (se 3 (by rfl) ⟨596, by rfl⟩) R1193
theorem R3227 : Reach 3227 := rs (se 1 (by rfl) ⟨2420, by rfl⟩) R4841
theorem R3279 : Reach 3279 := rs (se 1 (by rfl) ⟨2459, by rfl⟩) R4919
theorem R3321 : Reach 3321 := rs (se 2 (by rfl) ⟨1245, by rfl⟩) R2491
theorem R101695 : Reach 101695 := rs (se 1 (by rfl) ⟨76271, by rfl⟩) R152543
theorem R3441 : Reach 3441 := rs (se 2 (by rfl) ⟨1290, by rfl⟩) R2581
theorem R3445 : Reach 3445 := rs (se 5 (by rfl) ⟨161, by rfl⟩) R323
theorem R3459 : Reach 3459 := rs (se 1 (by rfl) ⟨2594, by rfl⟩) R5189
theorem R3463 : Reach 3463 := rs (se 1 (by rfl) ⟨2597, by rfl⟩) R5195
theorem R3471 : Reach 3471 := rs (se 1 (by rfl) ⟨2603, by rfl⟩) R5207
theorem R3473 : Reach 3473 := rs (se 2 (by rfl) ⟨1302, by rfl⟩) R2605
theorem R3475 : Reach 3475 := rs (se 1 (by rfl) ⟨2606, by rfl⟩) R5213
theorem R3497 : Reach 3497 := rs (se 2 (by rfl) ⟨1311, by rfl⟩) R2623
theorem R3521 : Reach 3521 := rs (se 2 (by rfl) ⟨1320, by rfl⟩) R2641
theorem R3523 : Reach 3523 := rs (se 1 (by rfl) ⟨2642, by rfl⟩) R5285
theorem R201203 : Reach 201203 := rs (se 1 (by rfl) ⟨150902, by rfl⟩) R301805
theorem R6279 : Reach 6279 := rs (se 1 (by rfl) ⟨4709, by rfl⟩) R9419
theorem R6287 : Reach 6287 := rs (se 1 (by rfl) ⟨4715, by rfl⟩) R9431
theorem R6311 : Reach 6311 := rs (se 1 (by rfl) ⟨4733, by rfl⟩) R9467
theorem R6361 : Reach 6361 := rs (se 2 (by rfl) ⟨2385, by rfl⟩) R4771
theorem R6365 : Reach 6365 := rs (se 3 (by rfl) ⟨1193, by rfl⟩) R2387
theorem R6369 : Reach 6369 := rs (se 2 (by rfl) ⟨2388, by rfl⟩) R4777
theorem R6455 : Reach 6455 := rs (se 1 (by rfl) ⟨4841, by rfl⟩) R9683
theorem R6537 : Reach 6537 := rs (se 2 (by rfl) ⟨2451, by rfl⟩) R4903
theorem R6557 : Reach 6557 := rs (se 3 (by rfl) ⟨1229, by rfl⟩) R2459
theorem R6643 : Reach 6643 := rs (se 1 (by rfl) ⟨4982, by rfl⟩) R9965
theorem R6869 : Reach 6869 := rs (se 7 (by rfl) ⟨80, by rfl⟩) R161
theorem R6883 : Reach 6883 := rs (se 1 (by rfl) ⟨5162, by rfl⟩) R10325
theorem R6897 : Reach 6897 := rs (se 2 (by rfl) ⟨2586, by rfl⟩) R5173
theorem R6917 : Reach 6917 := rs (se 4 (by rfl) ⟨648, by rfl⟩) R1297
theorem R6927 : Reach 6927 := rs (se 1 (by rfl) ⟨5195, by rfl⟩) R10391
theorem R6941 : Reach 6941 := rs (se 3 (by rfl) ⟨1301, by rfl⟩) R2603
theorem R6947 : Reach 6947 := rs (se 1 (by rfl) ⟨5210, by rfl⟩) R10421
theorem R6949 : Reach 6949 := rs (se 4 (by rfl) ⟨651, by rfl⟩) R1303
theorem R6985 : Reach 6985 := rs (se 2 (by rfl) ⟨2619, by rfl⟩) R5239
theorem R6993 : Reach 6993 := rs (se 2 (by rfl) ⟨2622, by rfl⟩) R5245
theorem R6995 : Reach 6995 := rs (se 1 (by rfl) ⟨5246, by rfl⟩) R10493
theorem R7033 : Reach 7033 := rs (se 2 (by rfl) ⟨2637, by rfl⟩) R5275
theorem R7035 : Reach 7035 := rs (se 1 (by rfl) ⟨5276, by rfl⟩) R10553
theorem R7043 : Reach 7043 := rs (se 1 (by rfl) ⟨5282, by rfl⟩) R10565
theorem R7045 : Reach 7045 := rs (se 4 (by rfl) ⟨660, by rfl⟩) R1321
theorem R7047 : Reach 7047 := rs (se 1 (by rfl) ⟨5285, by rfl⟩) R10571
theorem R1811915 : Reach 1811915 := rs (se 1 (by rfl) ⟨1358936, by rfl⟩) R2717873
theorem R206549 : Reach 206549 := rs (se 7 (by rfl) ⟨2420, by rfl⟩) R4841
theorem R12555 : Reach 12555 := rs (se 1 (by rfl) ⟨9416, by rfl⟩) R18833
theorem R12559 : Reach 12559 := rs (se 1 (by rfl) ⟨9419, by rfl⟩) R18839
theorem R12573 : Reach 12573 := rs (se 3 (by rfl) ⟨2357, by rfl⟩) R4715
theorem R12585 : Reach 12585 := rs (se 2 (by rfl) ⟨4719, by rfl⟩) R9439
theorem R12623 : Reach 12623 := rs (se 1 (by rfl) ⟨9467, by rfl⟩) R18935
theorem R12665 : Reach 12665 := rs (se 2 (by rfl) ⟨4749, by rfl⟩) R9499
theorem R12705 : Reach 12705 := rs (se 2 (by rfl) ⟨4764, by rfl⟩) R9529
theorem R12713 : Reach 12713 := rs (se 2 (by rfl) ⟨4767, by rfl⟩) R9535
theorem R12721 : Reach 12721 := rs (se 2 (by rfl) ⟨4770, by rfl⟩) R9541
theorem R12723 : Reach 12723 := rs (se 1 (by rfl) ⟨9542, by rfl⟩) R19085
theorem R12725 : Reach 12725 := rs (se 5 (by rfl) ⟨596, by rfl⟩) R1193
theorem R12729 : Reach 12729 := rs (se 2 (by rfl) ⟨4773, by rfl⟩) R9547
theorem R12737 : Reach 12737 := rs (se 2 (by rfl) ⟨4776, by rfl⟩) R9553
theorem R12739 : Reach 12739 := rs (se 1 (by rfl) ⟨9554, by rfl⟩) R19109
theorem R12955 : Reach 12955 := rs (se 1 (by rfl) ⟨9716, by rfl⟩) R19433
theorem R12959 : Reach 12959 := rs (se 1 (by rfl) ⟨9719, by rfl⟩) R19439
theorem R13025 : Reach 13025 := rs (se 2 (by rfl) ⟨4884, by rfl⟩) R9769
theorem R13031 : Reach 13031 := rs (se 1 (by rfl) ⟨9773, by rfl⟩) R19547
theorem R13055 : Reach 13055 := rs (se 1 (by rfl) ⟨9791, by rfl⟩) R19583
theorem R13067 : Reach 13067 := rs (se 1 (by rfl) ⟨9800, by rfl⟩) R19601
theorem R13115 : Reach 13115 := rs (se 1 (by rfl) ⟨9836, by rfl⟩) R19673
theorem R13117 : Reach 13117 := rs (se 3 (by rfl) ⟨2459, by rfl⟩) R4919
theorem R13403 : Reach 13403 := rs (se 1 (by rfl) ⟨10052, by rfl⟩) R20105
theorem R406781 : Reach 406781 := rs (se 3 (by rfl) ⟨76271, by rfl⟩) R152543
theorem R13765 : Reach 13765 := rs (se 4 (by rfl) ⟨1290, by rfl⟩) R2581
theorem R13781 : Reach 13781 := rs (se 7 (by rfl) ⟨161, by rfl⟩) R323
theorem R13837 : Reach 13837 := rs (se 3 (by rfl) ⟨2594, by rfl⟩) R5189
theorem R13841 : Reach 13841 := rs (se 2 (by rfl) ⟨5190, by rfl⟩) R10381
theorem R13853 : Reach 13853 := rs (se 3 (by rfl) ⟨2597, by rfl⟩) R5195
theorem R13901 : Reach 13901 := rs (se 3 (by rfl) ⟨2606, by rfl⟩) R5213
theorem R14027 : Reach 14027 := rs (se 1 (by rfl) ⟨10520, by rfl⟩) R21041
theorem R14071 : Reach 14071 := rs (se 1 (by rfl) ⟨10553, by rfl⟩) R21107
theorem R14075 : Reach 14075 := rs (se 1 (by rfl) ⟨10556, by rfl⟩) R21113
theorem R14093 : Reach 14093 := rs (se 3 (by rfl) ⟨2642, by rfl⟩) R5285
theorem R14111 : Reach 14111 := rs (se 1 (by rfl) ⟨10583, by rfl⟩) R21167
theorem R113105 : Reach 113105 := rs (se 2 (by rfl) ⟨42414, by rfl⟩) R84829
theorem R15611 : Reach 15611 := rs (se 1 (by rfl) ⟨11708, by rfl⟩) R23417
theorem R15641 : Reach 15641 := rs (se 2 (by rfl) ⟨5865, by rfl⟩) R11731
theorem R115901 : Reach 115901 := rs (se 3 (by rfl) ⟨21731, by rfl⟩) R43463
theorem R50495 : Reach 50495 := rs (se 1 (by rfl) ⟨37871, by rfl⟩) R75743
theorem R51353 : Reach 51353 := rs (se 2 (by rfl) ⟨19257, by rfl⟩) R38515
theorem R51857 : Reach 51857 := rs (se 2 (by rfl) ⟨19446, by rfl⟩) R38893
theorem R52283 : Reach 52283 := rs (se 1 (by rfl) ⟨39212, by rfl⟩) R78425
theorem R53207 : Reach 53207 := rs (se 1 (by rfl) ⟨39905, by rfl⟩) R79811
theorem R807893 : Reach 807893 := rs (se 7 (by rfl) ⟨9467, by rfl⟩) R18935
theorem R25919 : Reach 25919 := rs (se 1 (by rfl) ⟨19439, by rfl⟩) R38879
theorem R26063 : Reach 26063 := rs (se 1 (by rfl) ⟨19547, by rfl⟩) R39095
theorem R26135 : Reach 26135 := rs (se 1 (by rfl) ⟨19601, by rfl⟩) R39203
theorem R26203 : Reach 26203 := rs (se 1 (by rfl) ⟨19652, by rfl⟩) R39305
theorem R26603 : Reach 26603 := rs (se 1 (by rfl) ⟨19952, by rfl⟩) R39905
theorem R27323 : Reach 27323 := rs (se 1 (by rfl) ⟨20492, by rfl⟩) R40985
theorem R27683 : Reach 27683 := rs (se 1 (by rfl) ⟨20762, by rfl⟩) R41525
theorem R28133 : Reach 28133 := rs (se 4 (by rfl) ⟨2637, by rfl⟩) R5275
theorem R28151 : Reach 28151 := rs (se 1 (by rfl) ⟨21113, by rfl⟩) R42227
theorem R28181 : Reach 28181 := rs (se 6 (by rfl) ⟨660, by rfl⟩) R1321
theorem R28223 : Reach 28223 := rs (se 1 (by rfl) ⟨21167, by rfl⟩) R42335
theorem R28289 : Reach 28289 := rs (se 2 (by rfl) ⟨10608, by rfl⟩) R21217
theorem R851267 : Reach 851267 := rs (se 1 (by rfl) ⟨638450, by rfl⟩) R1276901
theorem R425645 : Reach 425645 := rs (se 3 (by rfl) ⟨79808, by rfl⟩) R159617
theorem R71 : Reach 71 := rs (se 1 (by rfl) ⟨53, by rfl⟩) R107
theorem R143 : Reach 143 := rs (se 1 (by rfl) ⟨107, by rfl⟩) R215
theorem R285 : Reach 285 := rs (se 3 (by rfl) ⟨53, by rfl⟩) R107
theorem R573 : Reach 573 := rs (se 3 (by rfl) ⟨107, by rfl⟩) R215
theorem R1141 : Reach 1141 := rs (se 5 (by rfl) ⟨53, by rfl⟩) R107
theorem R33965 : Reach 33965 := rs (se 3 (by rfl) ⟨6368, by rfl⟩) R12737
theorem R34235 : Reach 34235 := rs (se 1 (by rfl) ⟨25676, by rfl⟩) R51353
theorem R67067 : Reach 67067 := rs (se 1 (by rfl) ⟨50300, by rfl⟩) R100601
theorem R34571 : Reach 34571 := rs (se 1 (by rfl) ⟨25928, by rfl⟩) R51857
theorem R2095 : Reach 2095 := rs (se 1 (by rfl) ⟨1571, by rfl⟩) R3143
theorem R2121 : Reach 2121 := rs (se 2 (by rfl) ⟨795, by rfl⟩) R1591
theorem R2151 : Reach 2151 := rs (se 1 (by rfl) ⟨1613, by rfl⟩) R3227
theorem R34937 : Reach 34937 := rs (se 2 (by rfl) ⟨13101, by rfl⟩) R26203
theorem R2185 : Reach 2185 := rs (se 2 (by rfl) ⟨819, by rfl⟩) R1639
theorem R2289 : Reach 2289 := rs (se 2 (by rfl) ⟨858, by rfl⟩) R1717
theorem R2293 : Reach 2293 := rs (se 5 (by rfl) ⟨107, by rfl⟩) R215
theorem R2305 : Reach 2305 := rs (se 2 (by rfl) ⟨864, by rfl⟩) R1729
theorem R2313 : Reach 2313 := rs (se 2 (by rfl) ⟨867, by rfl⟩) R1735
theorem R2315 : Reach 2315 := rs (se 1 (by rfl) ⟨1736, by rfl⟩) R3473
theorem R2331 : Reach 2331 := rs (se 1 (by rfl) ⟨1748, by rfl⟩) R3497
theorem R2347 : Reach 2347 := rs (se 1 (by rfl) ⟨1760, by rfl⟩) R3521
theorem R35471 : Reach 35471 := rs (se 1 (by rfl) ⟨26603, by rfl⟩) R53207
theorem R134135 : Reach 134135 := rs (se 1 (by rfl) ⟨100601, by rfl⟩) R201203
theorem R134297 : Reach 134297 := rs (se 2 (by rfl) ⟨50361, by rfl⟩) R100723
theorem R4191 : Reach 4191 := rs (se 1 (by rfl) ⟨3143, by rfl⟩) R6287
theorem R4207 : Reach 4207 := rs (se 1 (by rfl) ⟨3155, by rfl⟩) R6311
theorem R4241 : Reach 4241 := rs (se 2 (by rfl) ⟨1590, by rfl⟩) R3181
theorem R4243 : Reach 4243 := rs (se 1 (by rfl) ⟨3182, by rfl⟩) R6365
theorem R37061 : Reach 37061 := rs (se 4 (by rfl) ⟨3474, by rfl⟩) R6949
theorem R4303 : Reach 4303 := rs (se 1 (by rfl) ⟨3227, by rfl⟩) R6455
theorem R4371 : Reach 4371 := rs (se 1 (by rfl) ⟨3278, by rfl⟩) R6557
theorem R135593 : Reach 135593 := rs (se 2 (by rfl) ⟨50847, by rfl⟩) R101695
theorem R4565 : Reach 4565 := rs (se 7 (by rfl) ⟨53, by rfl⟩) R107
theorem R4579 : Reach 4579 := rs (se 1 (by rfl) ⟨3434, by rfl⟩) R6869
theorem R4593 : Reach 4593 := rs (se 2 (by rfl) ⟨1722, by rfl⟩) R3445
theorem R4611 : Reach 4611 := rs (se 1 (by rfl) ⟨3458, by rfl⟩) R6917
theorem R4617 : Reach 4617 := rs (se 2 (by rfl) ⟨1731, by rfl⟩) R3463
theorem R4627 : Reach 4627 := rs (se 1 (by rfl) ⟨3470, by rfl⟩) R6941
theorem R4631 : Reach 4631 := rs (se 1 (by rfl) ⟨3473, by rfl⟩) R6947
theorem R4633 : Reach 4633 := rs (se 2 (by rfl) ⟨1737, by rfl⟩) R3475
theorem R4663 : Reach 4663 := rs (se 1 (by rfl) ⟨3497, by rfl⟩) R6995
theorem R4695 : Reach 4695 := rs (se 1 (by rfl) ⟨3521, by rfl⟩) R7043
theorem R4697 : Reach 4697 := rs (se 2 (by rfl) ⟨1761, by rfl⟩) R3523
theorem R137699 : Reach 137699 := rs (se 1 (by rfl) ⟨103274, by rfl⟩) R206549
theorem R139421 : Reach 139421 := rs (se 3 (by rfl) ⟨26141, by rfl⟩) R52283
theorem R8381 : Reach 8381 := rs (se 3 (by rfl) ⟨1571, by rfl⟩) R3143
theorem R8415 : Reach 8415 := rs (se 1 (by rfl) ⟨6311, by rfl⟩) R12623
theorem R8443 : Reach 8443 := rs (se 1 (by rfl) ⟨6332, by rfl⟩) R12665
theorem R8475 : Reach 8475 := rs (se 1 (by rfl) ⟨6356, by rfl⟩) R12713
theorem R8481 : Reach 8481 := rs (se 2 (by rfl) ⟨3180, by rfl⟩) R6361
theorem R8483 : Reach 8483 := rs (se 1 (by rfl) ⟨6362, by rfl⟩) R12725
theorem R8485 : Reach 8485 := rs (se 4 (by rfl) ⟨795, by rfl⟩) R1591
theorem R8491 : Reach 8491 := rs (se 1 (by rfl) ⟨6368, by rfl⟩) R12737
theorem R8605 : Reach 8605 := rs (se 3 (by rfl) ⟨1613, by rfl⟩) R3227
theorem R8639 : Reach 8639 := rs (se 1 (by rfl) ⟨6479, by rfl⟩) R12959
theorem R8683 : Reach 8683 := rs (se 1 (by rfl) ⟨6512, by rfl⟩) R13025
theorem R8687 : Reach 8687 := rs (se 1 (by rfl) ⟨6515, by rfl⟩) R13031
theorem R8703 : Reach 8703 := rs (se 1 (by rfl) ⟨6527, by rfl⟩) R13055
theorem R8711 : Reach 8711 := rs (se 1 (by rfl) ⟨6533, by rfl⟩) R13067
theorem R8741 : Reach 8741 := rs (se 4 (by rfl) ⟨819, by rfl⟩) R1639
theorem R8743 : Reach 8743 := rs (se 1 (by rfl) ⟨6557, by rfl⟩) R13115
theorem R8857 : Reach 8857 := rs (se 2 (by rfl) ⟨3321, by rfl⟩) R6643
theorem R8935 : Reach 8935 := rs (se 1 (by rfl) ⟨6701, by rfl⟩) R13403
theorem R271187 : Reach 271187 := rs (se 1 (by rfl) ⟨203390, by rfl⟩) R406781
theorem R2270045 : Reach 2270045 := rs (se 3 (by rfl) ⟨425633, by rfl⟩) R851267
theorem R9157 : Reach 9157 := rs (se 4 (by rfl) ⟨858, by rfl⟩) R1717
theorem R9173 : Reach 9173 := rs (se 7 (by rfl) ⟨107, by rfl⟩) R215
theorem R9177 : Reach 9177 := rs (se 2 (by rfl) ⟨3441, by rfl⟩) R6883
theorem R9187 : Reach 9187 := rs (se 1 (by rfl) ⟨6890, by rfl⟩) R13781
theorem R9221 : Reach 9221 := rs (se 4 (by rfl) ⟨864, by rfl⟩) R1729
theorem R9227 : Reach 9227 := rs (se 1 (by rfl) ⟨6920, by rfl⟩) R13841
theorem R9235 : Reach 9235 := rs (se 1 (by rfl) ⟨6926, by rfl⟩) R13853
theorem R9253 : Reach 9253 := rs (se 4 (by rfl) ⟨867, by rfl⟩) R1735
theorem R9261 : Reach 9261 := rs (se 3 (by rfl) ⟨1736, by rfl⟩) R3473
theorem R9265 : Reach 9265 := rs (se 2 (by rfl) ⟨3474, by rfl⟩) R6949
theorem R9267 : Reach 9267 := rs (se 1 (by rfl) ⟨6950, by rfl⟩) R13901
theorem R9313 : Reach 9313 := rs (se 2 (by rfl) ⟨3492, by rfl⟩) R6985
theorem R9325 : Reach 9325 := rs (se 3 (by rfl) ⟨1748, by rfl⟩) R3497
theorem R9351 : Reach 9351 := rs (se 1 (by rfl) ⟨7013, by rfl⟩) R14027
theorem R9377 : Reach 9377 := rs (se 2 (by rfl) ⟨3516, by rfl⟩) R7033
theorem R9383 : Reach 9383 := rs (se 1 (by rfl) ⟨7037, by rfl⟩) R14075
theorem R9389 : Reach 9389 := rs (se 3 (by rfl) ⟨1760, by rfl⟩) R3521
theorem R9393 : Reach 9393 := rs (se 2 (by rfl) ⟨3522, by rfl⟩) R7045
theorem R9395 : Reach 9395 := rs (se 1 (by rfl) ⟨7046, by rfl⟩) R14093
theorem R9407 : Reach 9407 := rs (se 1 (by rfl) ⟨7055, by rfl⟩) R14111
theorem R75403 : Reach 75403 := rs (se 1 (by rfl) ⟨56552, by rfl⟩) R113105
theorem R10407 : Reach 10407 := rs (se 1 (by rfl) ⟨7805, by rfl⟩) R15611
theorem R10427 : Reach 10427 := rs (se 1 (by rfl) ⟨7820, by rfl⟩) R15641
theorem R77267 : Reach 77267 := rs (se 1 (by rfl) ⟨57950, by rfl⟩) R115901
theorem R538595 : Reach 538595 := rs (se 1 (by rfl) ⟨403946, by rfl⟩) R807893
theorem R538613 : Reach 538613 := rs (se 5 (by rfl) ⟨25247, by rfl⟩) R50495
theorem R16745 : Reach 16745 := rs (se 2 (by rfl) ⟨6279, by rfl⟩) R12559
theorem R16829 : Reach 16829 := rs (se 3 (by rfl) ⟨3155, by rfl⟩) R6311
theorem R16961 : Reach 16961 := rs (se 2 (by rfl) ⟨6360, by rfl⟩) R12721
theorem R16973 : Reach 16973 := rs (se 3 (by rfl) ⟨3182, by rfl⟩) R6365
theorem R16985 : Reach 16985 := rs (se 2 (by rfl) ⟨6369, by rfl⟩) R12739
theorem R17213 : Reach 17213 := rs (se 3 (by rfl) ⟨3227, by rfl⟩) R6455
theorem R17273 : Reach 17273 := rs (se 2 (by rfl) ⟨6477, by rfl⟩) R12955
theorem R17279 : Reach 17279 := rs (se 1 (by rfl) ⟨12959, by rfl⟩) R25919
theorem R17375 : Reach 17375 := rs (se 1 (by rfl) ⟨13031, by rfl⟩) R26063
theorem R17423 : Reach 17423 := rs (se 1 (by rfl) ⟨13067, by rfl⟩) R26135
theorem R17489 : Reach 17489 := rs (se 2 (by rfl) ⟨6558, by rfl⟩) R13117
theorem R17735 : Reach 17735 := rs (se 1 (by rfl) ⟨13301, by rfl⟩) R26603
theorem R18215 : Reach 18215 := rs (se 1 (by rfl) ⟨13661, by rfl⟩) R27323
theorem R18317 : Reach 18317 := rs (se 3 (by rfl) ⟨3434, by rfl⟩) R6869
theorem R18353 : Reach 18353 := rs (se 2 (by rfl) ⟨6882, by rfl⟩) R13765
theorem R18373 : Reach 18373 := rs (se 4 (by rfl) ⟨1722, by rfl⟩) R3445
theorem R18449 : Reach 18449 := rs (se 2 (by rfl) ⟨6918, by rfl⟩) R13837
theorem R18455 : Reach 18455 := rs (se 1 (by rfl) ⟨13841, by rfl⟩) R27683
theorem R18509 : Reach 18509 := rs (se 3 (by rfl) ⟨3470, by rfl⟩) R6941
theorem R18533 : Reach 18533 := rs (se 4 (by rfl) ⟨1737, by rfl⟩) R3475
theorem R18653 : Reach 18653 := rs (se 3 (by rfl) ⟨3497, by rfl⟩) R6995
theorem R18755 : Reach 18755 := rs (se 1 (by rfl) ⟨14066, by rfl⟩) R28133
theorem R18761 : Reach 18761 := rs (se 2 (by rfl) ⟨7035, by rfl⟩) R14071
theorem R18767 : Reach 18767 := rs (se 1 (by rfl) ⟨14075, by rfl⟩) R28151
theorem R18787 : Reach 18787 := rs (se 1 (by rfl) ⟨14090, by rfl⟩) R28181
theorem R18815 : Reach 18815 := rs (se 1 (by rfl) ⟨14111, by rfl⟩) R28223
theorem R18859 : Reach 18859 := rs (se 1 (by rfl) ⟨14144, by rfl⟩) R28289
theorem R283763 : Reach 283763 := rs (se 1 (by rfl) ⟨212822, by rfl⟩) R425645
theorem R1207943 : Reach 1207943 := rs (se 1 (by rfl) ⟨905957, by rfl⟩) R1811915
theorem R47 : Reach 47 := rs (se 1 (by rfl) ⟨35, by rfl⟩) R71
theorem R95 : Reach 95 := rs (se 1 (by rfl) ⟨71, by rfl⟩) R143
theorem R189 : Reach 189 := rs (se 3 (by rfl) ⟨35, by rfl⟩) R71
theorem R381 : Reach 381 := rs (se 3 (by rfl) ⟨71, by rfl⟩) R143
theorem R757 : Reach 757 := rs (se 5 (by rfl) ⟨35, by rfl⟩) R71
theorem R1521 : Reach 1521 := rs (se 2 (by rfl) ⟨570, by rfl⟩) R1141
theorem R1525 : Reach 1525 := rs (se 5 (by rfl) ⟨71, by rfl⟩) R143
theorem R1543 : Reach 1543 := rs (se 1 (by rfl) ⟨1157, by rfl⟩) R2315
theorem R2793 : Reach 2793 := rs (se 2 (by rfl) ⟨1047, by rfl⟩) R2095
theorem R2827 : Reach 2827 := rs (se 1 (by rfl) ⟨2120, by rfl⟩) R4241
theorem R2913 : Reach 2913 := rs (se 2 (by rfl) ⟨1092, by rfl⟩) R2185
theorem R3029 : Reach 3029 := rs (se 7 (by rfl) ⟨35, by rfl⟩) R71
theorem R3043 : Reach 3043 := rs (se 1 (by rfl) ⟨2282, by rfl⟩) R4565
theorem R3057 : Reach 3057 := rs (se 2 (by rfl) ⟨1146, by rfl⟩) R2293
theorem R3073 : Reach 3073 := rs (se 2 (by rfl) ⟨1152, by rfl⟩) R2305
theorem R3087 : Reach 3087 := rs (se 1 (by rfl) ⟨2315, by rfl⟩) R4631
theorem R3129 : Reach 3129 := rs (se 2 (by rfl) ⟨1173, by rfl⟩) R2347
theorem R3131 : Reach 3131 := rs (se 1 (by rfl) ⟨2348, by rfl⟩) R4697
theorem R5587 : Reach 5587 := rs (se 1 (by rfl) ⟨4190, by rfl⟩) R8381
theorem R5609 : Reach 5609 := rs (se 2 (by rfl) ⟨2103, by rfl⟩) R4207
theorem R5655 : Reach 5655 := rs (se 1 (by rfl) ⟨4241, by rfl⟩) R8483
theorem R5657 : Reach 5657 := rs (se 2 (by rfl) ⟨2121, by rfl⟩) R4243
theorem R5737 : Reach 5737 := rs (se 2 (by rfl) ⟨2151, by rfl⟩) R4303
theorem R5759 : Reach 5759 := rs (se 1 (by rfl) ⟨4319, by rfl⟩) R8639
theorem R5791 : Reach 5791 := rs (se 1 (by rfl) ⟨4343, by rfl⟩) R8687
theorem R5807 : Reach 5807 := rs (se 1 (by rfl) ⟨4355, by rfl⟩) R8711
theorem R5827 : Reach 5827 := rs (se 1 (by rfl) ⟨4370, by rfl⟩) R8741
theorem R1513363 : Reach 1513363 := rs (se 1 (by rfl) ⟨1135022, by rfl⟩) R2270045
theorem R6085 : Reach 6085 := rs (se 4 (by rfl) ⟨570, by rfl⟩) R1141
theorem R6101 : Reach 6101 := rs (se 7 (by rfl) ⟨71, by rfl⟩) R143
theorem R6105 : Reach 6105 := rs (se 2 (by rfl) ⟨2289, by rfl⟩) R4579
theorem R6115 : Reach 6115 := rs (se 1 (by rfl) ⟨4586, by rfl⟩) R9173
theorem R6147 : Reach 6147 := rs (se 1 (by rfl) ⟨4610, by rfl⟩) R9221
theorem R6151 : Reach 6151 := rs (se 1 (by rfl) ⟨4613, by rfl⟩) R9227
theorem R6169 : Reach 6169 := rs (se 2 (by rfl) ⟨2313, by rfl⟩) R4627
theorem R6173 : Reach 6173 := rs (se 3 (by rfl) ⟨1157, by rfl⟩) R2315
theorem R6177 : Reach 6177 := rs (se 2 (by rfl) ⟨2316, by rfl⟩) R4633
theorem R6217 : Reach 6217 := rs (se 2 (by rfl) ⟨2331, by rfl⟩) R4663
theorem R6251 : Reach 6251 := rs (se 1 (by rfl) ⟨4688, by rfl⟩) R9377
theorem R6255 : Reach 6255 := rs (se 1 (by rfl) ⟨4691, by rfl⟩) R9383
theorem R6259 : Reach 6259 := rs (se 1 (by rfl) ⟨4694, by rfl⟩) R9389
theorem R6263 : Reach 6263 := rs (se 1 (by rfl) ⟨4697, by rfl⟩) R9395
theorem R6271 : Reach 6271 := rs (se 1 (by rfl) ⟨4703, by rfl⟩) R9407
theorem R6951 : Reach 6951 := rs (se 1 (by rfl) ⟨5213, by rfl⟩) R10427
theorem R402149 : Reach 402149 := rs (se 4 (by rfl) ⟨37701, by rfl⟩) R75403
theorem R11163 : Reach 11163 := rs (se 1 (by rfl) ⟨8372, by rfl⟩) R16745
theorem R11173 : Reach 11173 := rs (se 4 (by rfl) ⟨1047, by rfl⟩) R2095
theorem R11219 : Reach 11219 := rs (se 1 (by rfl) ⟨8414, by rfl⟩) R16829
theorem R11257 : Reach 11257 := rs (se 2 (by rfl) ⟨4221, by rfl⟩) R8443
theorem R11307 : Reach 11307 := rs (se 1 (by rfl) ⟨8480, by rfl⟩) R16961
theorem R11309 : Reach 11309 := rs (se 3 (by rfl) ⟨2120, by rfl⟩) R4241
theorem R11313 : Reach 11313 := rs (se 2 (by rfl) ⟨4242, by rfl⟩) R8485
theorem R11315 : Reach 11315 := rs (se 1 (by rfl) ⟨8486, by rfl⟩) R16973
theorem R11321 : Reach 11321 := rs (se 2 (by rfl) ⟨4245, by rfl⟩) R8491
theorem R11323 : Reach 11323 := rs (se 1 (by rfl) ⟨8492, by rfl⟩) R16985
theorem R11473 : Reach 11473 := rs (se 2 (by rfl) ⟨4302, by rfl⟩) R8605
theorem R11475 : Reach 11475 := rs (se 1 (by rfl) ⟨8606, by rfl⟩) R17213
theorem R11515 : Reach 11515 := rs (se 1 (by rfl) ⟨8636, by rfl⟩) R17273
theorem R11519 : Reach 11519 := rs (se 1 (by rfl) ⟨8639, by rfl⟩) R17279
theorem R11577 : Reach 11577 := rs (se 2 (by rfl) ⟨4341, by rfl⟩) R8683
theorem R11583 : Reach 11583 := rs (se 1 (by rfl) ⟨8687, by rfl⟩) R17375
theorem R11615 : Reach 11615 := rs (se 1 (by rfl) ⟨8711, by rfl⟩) R17423
theorem R11653 : Reach 11653 := rs (se 4 (by rfl) ⟨1092, by rfl⟩) R2185
theorem R11657 : Reach 11657 := rs (se 2 (by rfl) ⟨4371, by rfl⟩) R8743
theorem R11659 : Reach 11659 := rs (se 1 (by rfl) ⟨8744, by rfl⟩) R17489
theorem R11809 : Reach 11809 := rs (se 2 (by rfl) ⟨4428, by rfl⟩) R8857
theorem R11823 : Reach 11823 := rs (se 1 (by rfl) ⟨8867, by rfl⟩) R17735
theorem R11913 : Reach 11913 := rs (se 2 (by rfl) ⟨4467, by rfl⟩) R8935
theorem R44711 : Reach 44711 := rs (se 1 (by rfl) ⟨33533, by rfl⟩) R67067
theorem R12117 : Reach 12117 := rs (se 9 (by rfl) ⟨35, by rfl⟩) R71
theorem R12143 : Reach 12143 := rs (se 1 (by rfl) ⟨9107, by rfl⟩) R18215
theorem R12173 : Reach 12173 := rs (se 3 (by rfl) ⟨2282, by rfl⟩) R4565
theorem R12209 : Reach 12209 := rs (se 2 (by rfl) ⟨4578, by rfl⟩) R9157
theorem R12211 : Reach 12211 := rs (se 1 (by rfl) ⟨9158, by rfl⟩) R18317
theorem R12229 : Reach 12229 := rs (se 4 (by rfl) ⟨1146, by rfl⟩) R2293
theorem R12235 : Reach 12235 := rs (se 1 (by rfl) ⟨9176, by rfl⟩) R18353
theorem R12249 : Reach 12249 := rs (se 2 (by rfl) ⟨4593, by rfl⟩) R9187
theorem R12293 : Reach 12293 := rs (se 4 (by rfl) ⟨1152, by rfl⟩) R2305
theorem R12299 : Reach 12299 := rs (se 1 (by rfl) ⟨9224, by rfl⟩) R18449
theorem R12303 : Reach 12303 := rs (se 1 (by rfl) ⟨9227, by rfl⟩) R18455
theorem R12313 : Reach 12313 := rs (se 2 (by rfl) ⟨4617, by rfl⟩) R9235
theorem R12337 : Reach 12337 := rs (se 2 (by rfl) ⟨4626, by rfl⟩) R9253
theorem R12339 : Reach 12339 := rs (se 1 (by rfl) ⟨9254, by rfl⟩) R18509
theorem R12349 : Reach 12349 := rs (se 3 (by rfl) ⟨2315, by rfl⟩) R4631
theorem R12353 : Reach 12353 := rs (se 2 (by rfl) ⟨4632, by rfl⟩) R9265
theorem R12355 : Reach 12355 := rs (se 1 (by rfl) ⟨9266, by rfl⟩) R18533
theorem R12417 : Reach 12417 := rs (se 2 (by rfl) ⟨4656, by rfl⟩) R9313
theorem R12433 : Reach 12433 := rs (se 2 (by rfl) ⟨4662, by rfl⟩) R9325
theorem R12435 : Reach 12435 := rs (se 1 (by rfl) ⟨9326, by rfl⟩) R18653
theorem R12503 : Reach 12503 := rs (se 1 (by rfl) ⟨9377, by rfl⟩) R18755
theorem R12507 : Reach 12507 := rs (se 1 (by rfl) ⟨9380, by rfl⟩) R18761
theorem R12511 : Reach 12511 := rs (se 1 (by rfl) ⟨9383, by rfl⟩) R18767
theorem R12517 : Reach 12517 := rs (se 4 (by rfl) ⟨1173, by rfl⟩) R2347
theorem R12525 : Reach 12525 := rs (se 3 (by rfl) ⟨2348, by rfl⟩) R4697
theorem R12543 : Reach 12543 := rs (se 1 (by rfl) ⟨9407, by rfl⟩) R18815
theorem R180791 : Reach 180791 := rs (se 1 (by rfl) ⟨135593, by rfl⟩) R271187
theorem R49733 : Reach 49733 := rs (se 4 (by rfl) ⟨4662, by rfl⟩) R9325
theorem R51511 : Reach 51511 := rs (se 1 (by rfl) ⟨38633, by rfl⟩) R77267
theorem R805295 : Reach 805295 := rs (se 1 (by rfl) ⟨603971, by rfl⟩) R1207943
theorem R22349 : Reach 22349 := rs (se 3 (by rfl) ⟨4190, by rfl⟩) R8381
theorem R22643 : Reach 22643 := rs (se 1 (by rfl) ⟨16982, by rfl⟩) R33965
theorem R22823 : Reach 22823 := rs (se 1 (by rfl) ⟨17117, by rfl⟩) R34235
theorem R22949 : Reach 22949 := rs (se 4 (by rfl) ⟨2151, by rfl⟩) R4303
theorem R23047 : Reach 23047 := rs (se 1 (by rfl) ⟨17285, by rfl⟩) R34571
theorem R23165 : Reach 23165 := rs (se 3 (by rfl) ⟨4343, by rfl⟩) R8687
theorem R23291 : Reach 23291 := rs (se 1 (by rfl) ⟨17468, by rfl⟩) R34937
theorem R23309 : Reach 23309 := rs (se 3 (by rfl) ⟨4370, by rfl⟩) R8741
theorem R23647 : Reach 23647 := rs (se 1 (by rfl) ⟨17735, by rfl⟩) R35471
theorem R89423 : Reach 89423 := rs (se 1 (by rfl) ⟨67067, by rfl⟩) R134135
theorem R89531 : Reach 89531 := rs (se 1 (by rfl) ⟨67148, by rfl⟩) R134297
theorem R24421 : Reach 24421 := rs (se 4 (by rfl) ⟨2289, by rfl⟩) R4579
theorem R24461 : Reach 24461 := rs (se 3 (by rfl) ⟨4586, by rfl⟩) R9173
theorem R24497 : Reach 24497 := rs (se 2 (by rfl) ⟨9186, by rfl⟩) R18373
theorem R24605 : Reach 24605 := rs (se 3 (by rfl) ⟨4613, by rfl⟩) R9227
theorem R24677 : Reach 24677 := rs (se 4 (by rfl) ⟨2313, by rfl⟩) R4627
theorem R24707 : Reach 24707 := rs (se 1 (by rfl) ⟨18530, by rfl⟩) R37061
theorem R90395 : Reach 90395 := rs (se 1 (by rfl) ⟨67796, by rfl⟩) R135593
theorem R25037 : Reach 25037 := rs (se 3 (by rfl) ⟨4694, by rfl⟩) R9389
theorem R25049 : Reach 25049 := rs (se 2 (by rfl) ⟨9393, by rfl⟩) R18787
theorem R25085 : Reach 25085 := rs (se 3 (by rfl) ⟨4703, by rfl⟩) R9407
theorem R25145 : Reach 25145 := rs (se 2 (by rfl) ⟨9429, by rfl⟩) R18859
theorem R189175 : Reach 189175 := rs (se 1 (by rfl) ⟨141881, by rfl⟩) R283763
theorem R91799 : Reach 91799 := rs (se 1 (by rfl) ⟨68849, by rfl⟩) R137699
theorem R92947 : Reach 92947 := rs (se 1 (by rfl) ⟨69710, by rfl⟩) R139421
theorem R27805 : Reach 27805 := rs (se 3 (by rfl) ⟨5213, by rfl⟩) R10427
theorem R359063 : Reach 359063 := rs (se 1 (by rfl) ⟨269297, by rfl⟩) R538595
theorem R359075 : Reach 359075 := rs (se 1 (by rfl) ⟨269306, by rfl⟩) R538613
theorem R97685 : Reach 97685 := rs (se 6 (by rfl) ⟨2289, by rfl⟩) R4579
theorem R31 : Reach 31 := rs (se 1 (by rfl) ⟨23, by rfl⟩) R47
theorem R63 : Reach 63 := rs (se 1 (by rfl) ⟨47, by rfl⟩) R95
theorem R125 : Reach 125 := rs (se 3 (by rfl) ⟨23, by rfl⟩) R47
theorem R253 : Reach 253 := rs (se 3 (by rfl) ⟨47, by rfl⟩) R95
theorem R33155 : Reach 33155 := rs (se 1 (by rfl) ⟨24866, by rfl⟩) R49733
theorem R501 : Reach 501 := rs (se 5 (by rfl) ⟨23, by rfl⟩) R47
theorem R1009 : Reach 1009 := rs (se 2 (by rfl) ⟨378, by rfl⟩) R757
theorem R1013 : Reach 1013 := rs (se 5 (by rfl) ⟨47, by rfl⟩) R95
theorem R2005 : Reach 2005 := rs (se 7 (by rfl) ⟨23, by rfl⟩) R47
theorem R2019 : Reach 2019 := rs (se 1 (by rfl) ⟨1514, by rfl⟩) R3029
theorem R2033 : Reach 2033 := rs (se 2 (by rfl) ⟨762, by rfl⟩) R1525
theorem R2057 : Reach 2057 := rs (se 2 (by rfl) ⟨771, by rfl⟩) R1543
theorem R2087 : Reach 2087 := rs (se 1 (by rfl) ⟨1565, by rfl⟩) R3131
theorem R68681 : Reach 68681 := rs (se 2 (by rfl) ⟨25755, by rfl⟩) R51511
theorem R3739 : Reach 3739 := rs (se 1 (by rfl) ⟨2804, by rfl⟩) R5609
theorem R3769 : Reach 3769 := rs (se 2 (by rfl) ⟨1413, by rfl⟩) R2827
theorem R3771 : Reach 3771 := rs (se 1 (by rfl) ⟨2828, by rfl⟩) R5657
theorem R3839 : Reach 3839 := rs (se 1 (by rfl) ⟨2879, by rfl⟩) R5759
theorem R3871 : Reach 3871 := rs (se 1 (by rfl) ⟨2903, by rfl⟩) R5807
theorem R4037 : Reach 4037 := rs (se 4 (by rfl) ⟨378, by rfl⟩) R757
theorem R4053 : Reach 4053 := rs (se 7 (by rfl) ⟨47, by rfl⟩) R95
theorem R4057 : Reach 4057 := rs (se 2 (by rfl) ⟨1521, by rfl⟩) R3043
theorem R4067 : Reach 4067 := rs (se 1 (by rfl) ⟨3050, by rfl⟩) R6101
theorem R4097 : Reach 4097 := rs (se 2 (by rfl) ⟨1536, by rfl⟩) R3073
theorem R4115 : Reach 4115 := rs (se 1 (by rfl) ⟨3086, by rfl⟩) R6173
theorem R4167 : Reach 4167 := rs (se 1 (by rfl) ⟨3125, by rfl⟩) R6251
theorem R4175 : Reach 4175 := rs (se 1 (by rfl) ⟨3131, by rfl⟩) R6263
theorem R37073 : Reach 37073 := rs (se 2 (by rfl) ⟨13902, by rfl⟩) R27805
theorem R7449 : Reach 7449 := rs (se 2 (by rfl) ⟨2793, by rfl⟩) R5587
theorem R7479 : Reach 7479 := rs (se 1 (by rfl) ⟨5609, by rfl⟩) R11219
theorem R7539 : Reach 7539 := rs (se 1 (by rfl) ⟨5654, by rfl⟩) R11309
theorem R7543 : Reach 7543 := rs (se 1 (by rfl) ⟨5657, by rfl⟩) R11315
theorem R7547 : Reach 7547 := rs (se 1 (by rfl) ⟨5660, by rfl⟩) R11321
theorem R7649 : Reach 7649 := rs (se 2 (by rfl) ⟨2868, by rfl⟩) R5737
theorem R7679 : Reach 7679 := rs (se 1 (by rfl) ⟨5759, by rfl⟩) R11519
theorem R7721 : Reach 7721 := rs (se 2 (by rfl) ⟨2895, by rfl⟩) R5791
theorem R7743 : Reach 7743 := rs (se 1 (by rfl) ⟨5807, by rfl⟩) R11615
theorem R7769 : Reach 7769 := rs (se 2 (by rfl) ⟨2913, by rfl⟩) R5827
theorem R7771 : Reach 7771 := rs (se 1 (by rfl) ⟨5828, by rfl⟩) R11657
theorem R8021 : Reach 8021 := rs (se 9 (by rfl) ⟨23, by rfl⟩) R47
theorem R8077 : Reach 8077 := rs (se 3 (by rfl) ⟨1514, by rfl⟩) R3029
theorem R8095 : Reach 8095 := rs (se 1 (by rfl) ⟨6071, by rfl⟩) R12143
theorem R8113 : Reach 8113 := rs (se 2 (by rfl) ⟨3042, by rfl⟩) R6085
theorem R8115 : Reach 8115 := rs (se 1 (by rfl) ⟨6086, by rfl⟩) R12173
theorem R8133 : Reach 8133 := rs (se 4 (by rfl) ⟨762, by rfl⟩) R1525
theorem R8139 : Reach 8139 := rs (se 1 (by rfl) ⟨6104, by rfl⟩) R12209
theorem R8153 : Reach 8153 := rs (se 2 (by rfl) ⟨3057, by rfl⟩) R6115
theorem R8195 : Reach 8195 := rs (se 1 (by rfl) ⟨6146, by rfl⟩) R12293
theorem R8199 : Reach 8199 := rs (se 1 (by rfl) ⟨6149, by rfl⟩) R12299
theorem R8201 : Reach 8201 := rs (se 2 (by rfl) ⟨3075, by rfl⟩) R6151
theorem R8225 : Reach 8225 := rs (se 2 (by rfl) ⟨3084, by rfl⟩) R6169
theorem R8229 : Reach 8229 := rs (se 4 (by rfl) ⟨771, by rfl⟩) R1543
theorem R8235 : Reach 8235 := rs (se 1 (by rfl) ⟨6176, by rfl⟩) R12353
theorem R8289 : Reach 8289 := rs (se 2 (by rfl) ⟨3108, by rfl⟩) R6217
theorem R8335 : Reach 8335 := rs (se 1 (by rfl) ⟨6251, by rfl⟩) R12503
theorem R8345 : Reach 8345 := rs (se 2 (by rfl) ⟨3129, by rfl⟩) R6259
theorem R8349 : Reach 8349 := rs (se 3 (by rfl) ⟨1565, by rfl⟩) R3131
theorem R8361 : Reach 8361 := rs (se 2 (by rfl) ⟨3135, by rfl⟩) R6271
theorem R239375 : Reach 239375 := rs (se 1 (by rfl) ⟨179531, by rfl⟩) R359063
theorem R239383 : Reach 239383 := rs (se 1 (by rfl) ⟨179537, by rfl⟩) R359075
theorem R536863 : Reach 536863 := rs (se 1 (by rfl) ⟨402647, by rfl⟩) R805295
theorem R14897 : Reach 14897 := rs (se 2 (by rfl) ⟨5586, by rfl⟩) R11173
theorem R14899 : Reach 14899 := rs (se 1 (by rfl) ⟨11174, by rfl⟩) R22349
theorem R14957 : Reach 14957 := rs (se 3 (by rfl) ⟨2804, by rfl⟩) R5609
theorem R15077 : Reach 15077 := rs (se 4 (by rfl) ⟨1413, by rfl⟩) R2827
theorem R15095 : Reach 15095 := rs (se 1 (by rfl) ⟨11321, by rfl⟩) R22643
theorem R15215 : Reach 15215 := rs (se 1 (by rfl) ⟨11411, by rfl⟩) R22823
theorem R15299 : Reach 15299 := rs (se 1 (by rfl) ⟨11474, by rfl⟩) R22949
theorem R15353 : Reach 15353 := rs (se 2 (by rfl) ⟨5757, by rfl⟩) R11515
theorem R15443 : Reach 15443 := rs (se 1 (by rfl) ⟨11582, by rfl⟩) R23165
theorem R15485 : Reach 15485 := rs (se 3 (by rfl) ⟨2903, by rfl⟩) R5807
theorem R15527 : Reach 15527 := rs (se 1 (by rfl) ⟨11645, by rfl⟩) R23291
theorem R15539 : Reach 15539 := rs (se 1 (by rfl) ⟨11654, by rfl⟩) R23309
theorem R15545 : Reach 15545 := rs (se 2 (by rfl) ⟨5829, by rfl⟩) R11659
theorem R16213 : Reach 16213 := rs (se 9 (by rfl) ⟨47, by rfl⟩) R95
theorem R16229 : Reach 16229 := rs (se 4 (by rfl) ⟨1521, by rfl⟩) R3043
theorem R16307 : Reach 16307 := rs (se 1 (by rfl) ⟨12230, by rfl⟩) R24461
theorem R16313 : Reach 16313 := rs (se 2 (by rfl) ⟨6117, by rfl⟩) R12235
theorem R16331 : Reach 16331 := rs (se 1 (by rfl) ⟨12248, by rfl⟩) R24497
theorem R16403 : Reach 16403 := rs (se 1 (by rfl) ⟨12302, by rfl⟩) R24605
theorem R16451 : Reach 16451 := rs (se 1 (by rfl) ⟨12338, by rfl⟩) R24677
theorem R16471 : Reach 16471 := rs (se 1 (by rfl) ⟨12353, by rfl⟩) R24707
theorem R16577 : Reach 16577 := rs (se 2 (by rfl) ⟨6216, by rfl⟩) R12433
theorem R16691 : Reach 16691 := rs (se 1 (by rfl) ⟨12518, by rfl⟩) R25037
theorem R16699 : Reach 16699 := rs (se 1 (by rfl) ⟨12524, by rfl⟩) R25049
theorem R16723 : Reach 16723 := rs (se 1 (by rfl) ⟨12542, by rfl⟩) R25085
theorem R16763 : Reach 16763 := rs (se 1 (by rfl) ⟨12572, by rfl⟩) R25145
theorem R2017817 : Reach 2017817 := rs (se 2 (by rfl) ⟨756681, by rfl⟩) R1513363
theorem R120527 : Reach 120527 := rs (se 1 (by rfl) ⟨90395, by rfl⟩) R180791
theorem R252233 : Reach 252233 := rs (se 2 (by rfl) ⟨94587, by rfl⟩) R189175
theorem R1072397 : Reach 1072397 := rs (se 3 (by rfl) ⟨201074, by rfl⟩) R402149
theorem R122917 : Reach 122917 := rs (se 4 (by rfl) ⟨11523, by rfl⟩) R23047
theorem R123929 : Reach 123929 := rs (se 2 (by rfl) ⟨46473, by rfl⟩) R92947
theorem R59615 : Reach 59615 := rs (se 1 (by rfl) ⟨44711, by rfl⟩) R89423
theorem R59687 : Reach 59687 := rs (se 1 (by rfl) ⟨44765, by rfl⟩) R89531
theorem R60263 : Reach 60263 := rs (se 1 (by rfl) ⟨45197, by rfl⟩) R90395
theorem R61199 : Reach 61199 := rs (se 1 (by rfl) ⟨45899, by rfl⟩) R91799
theorem R29807 : Reach 29807 := rs (se 1 (by rfl) ⟨22355, by rfl⟩) R44711
theorem R31529 : Reach 31529 := rs (se 2 (by rfl) ⟨11823, by rfl⟩) R23647
theorem R32309 : Reach 32309 := rs (se 5 (by rfl) ⟨1514, by rfl⟩) R3029
theorem R65123 : Reach 65123 := rs (se 1 (by rfl) ⟨48842, by rfl⟩) R97685
theorem R32453 : Reach 32453 := rs (se 4 (by rfl) ⟨3042, by rfl⟩) R6085
theorem R32561 : Reach 32561 := rs (se 2 (by rfl) ⟨12210, by rfl⟩) R24421
theorem R41 : Reach 41 := rs (se 2 (by rfl) ⟨15, by rfl⟩) R31
theorem R163889 : Reach 163889 := rs (se 2 (by rfl) ⟨61458, by rfl⟩) R122917
theorem R83 : Reach 83 := rs (se 1 (by rfl) ⟨62, by rfl⟩) R125
theorem R165 : Reach 165 := rs (se 4 (by rfl) ⟨15, by rfl⟩) R31
theorem R333 : Reach 333 := rs (se 3 (by rfl) ⟨62, by rfl⟩) R125
theorem R337 : Reach 337 := rs (se 2 (by rfl) ⟨126, by rfl⟩) R253
theorem R661 : Reach 661 := rs (se 6 (by rfl) ⟨15, by rfl⟩) R31
theorem R675 : Reach 675 := rs (se 1 (by rfl) ⟨506, by rfl⟩) R1013
theorem R1333 : Reach 1333 := rs (se 5 (by rfl) ⟨62, by rfl⟩) R125
theorem R1345 : Reach 1345 := rs (se 2 (by rfl) ⟨504, by rfl⟩) R1009
theorem R1349 : Reach 1349 := rs (se 4 (by rfl) ⟨126, by rfl⟩) R253
theorem R1355 : Reach 1355 := rs (se 1 (by rfl) ⟨1016, by rfl⟩) R2033
theorem R1371 : Reach 1371 := rs (se 1 (by rfl) ⟨1028, by rfl⟩) R2057
theorem R1391 : Reach 1391 := rs (se 1 (by rfl) ⟨1043, by rfl⟩) R2087
theorem R1345211 : Reach 1345211 := rs (se 1 (by rfl) ⟨1008908, by rfl⟩) R2017817
theorem R2559 : Reach 2559 := rs (se 1 (by rfl) ⟨1919, by rfl⟩) R3839
theorem R2645 : Reach 2645 := rs (se 8 (by rfl) ⟨15, by rfl⟩) R31
theorem R2673 : Reach 2673 := rs (se 2 (by rfl) ⟨1002, by rfl⟩) R2005
theorem R2691 : Reach 2691 := rs (se 1 (by rfl) ⟨2018, by rfl⟩) R4037
theorem R2701 : Reach 2701 := rs (se 3 (by rfl) ⟨506, by rfl⟩) R1013
theorem R2711 : Reach 2711 := rs (se 1 (by rfl) ⟨2033, by rfl⟩) R4067
theorem R2731 : Reach 2731 := rs (se 1 (by rfl) ⟨2048, by rfl⟩) R4097
theorem R2743 : Reach 2743 := rs (se 1 (by rfl) ⟨2057, by rfl⟩) R4115
theorem R2783 : Reach 2783 := rs (se 1 (by rfl) ⟨2087, by rfl⟩) R4175
theorem R168155 : Reach 168155 := rs (se 1 (by rfl) ⟨126116, by rfl⟩) R252233
theorem R4985 : Reach 4985 := rs (se 2 (by rfl) ⟨1869, by rfl⟩) R3739
theorem R5025 : Reach 5025 := rs (se 2 (by rfl) ⟨1884, by rfl⟩) R3769
theorem R5031 : Reach 5031 := rs (se 1 (by rfl) ⟨3773, by rfl⟩) R7547
theorem R5099 : Reach 5099 := rs (se 1 (by rfl) ⟨3824, by rfl⟩) R7649
theorem R5119 : Reach 5119 := rs (se 1 (by rfl) ⟨3839, by rfl⟩) R7679
theorem R5147 : Reach 5147 := rs (se 1 (by rfl) ⟨3860, by rfl⟩) R7721
theorem R5161 : Reach 5161 := rs (se 2 (by rfl) ⟨1935, by rfl⟩) R3871
theorem R5179 : Reach 5179 := rs (se 1 (by rfl) ⟨3884, by rfl⟩) R7769
theorem R5333 : Reach 5333 := rs (se 7 (by rfl) ⟨62, by rfl⟩) R125
theorem R5347 : Reach 5347 := rs (se 1 (by rfl) ⟨4010, by rfl⟩) R8021
theorem R5381 : Reach 5381 := rs (se 4 (by rfl) ⟨504, by rfl⟩) R1009
theorem R5397 : Reach 5397 := rs (se 6 (by rfl) ⟨126, by rfl⟩) R253
theorem R5409 : Reach 5409 := rs (se 2 (by rfl) ⟨2028, by rfl⟩) R4057
theorem R5421 : Reach 5421 := rs (se 3 (by rfl) ⟨1016, by rfl⟩) R2033
theorem R5435 : Reach 5435 := rs (se 1 (by rfl) ⟨4076, by rfl⟩) R8153
theorem R5463 : Reach 5463 := rs (se 1 (by rfl) ⟨4097, by rfl⟩) R8195
theorem R5467 : Reach 5467 := rs (se 1 (by rfl) ⟨4100, by rfl⟩) R8201
theorem R5483 : Reach 5483 := rs (se 1 (by rfl) ⟨4112, by rfl⟩) R8225
theorem R5485 : Reach 5485 := rs (se 3 (by rfl) ⟨1028, by rfl⟩) R2057
theorem R5563 : Reach 5563 := rs (se 1 (by rfl) ⟨4172, by rfl⟩) R8345
theorem R5565 : Reach 5565 := rs (se 3 (by rfl) ⟨1043, by rfl⟩) R2087
theorem R39743 : Reach 39743 := rs (se 1 (by rfl) ⟨29807, by rfl⟩) R59615
theorem R39791 : Reach 39791 := rs (se 1 (by rfl) ⟨29843, by rfl⟩) R59687
theorem R40175 : Reach 40175 := rs (se 1 (by rfl) ⟨30131, by rfl⟩) R60263
theorem R40229 : Reach 40229 := rs (se 4 (by rfl) ⟨3771, by rfl⟩) R7543
theorem R40799 : Reach 40799 := rs (se 1 (by rfl) ⟨30599, by rfl⟩) R61199
theorem R2859725 : Reach 2859725 := rs (se 3 (by rfl) ⟨536198, by rfl⟩) R1072397
theorem R9931 : Reach 9931 := rs (se 1 (by rfl) ⟨7448, by rfl⟩) R14897
theorem R9971 : Reach 9971 := rs (se 1 (by rfl) ⟨7478, by rfl⟩) R14957
theorem R10051 : Reach 10051 := rs (se 1 (by rfl) ⟨7538, by rfl⟩) R15077
theorem R10057 : Reach 10057 := rs (se 2 (by rfl) ⟨3771, by rfl⟩) R7543
theorem R10063 : Reach 10063 := rs (se 1 (by rfl) ⟨7547, by rfl⟩) R15095
theorem R10143 : Reach 10143 := rs (se 1 (by rfl) ⟨7607, by rfl⟩) R15215
theorem R10199 : Reach 10199 := rs (se 1 (by rfl) ⟨7649, by rfl⟩) R15299
theorem R10235 : Reach 10235 := rs (se 1 (by rfl) ⟨7676, by rfl⟩) R15353
theorem R10237 : Reach 10237 := rs (se 3 (by rfl) ⟨1919, by rfl⟩) R3839
theorem R10295 : Reach 10295 := rs (se 1 (by rfl) ⟨7721, by rfl⟩) R15443
theorem R10323 : Reach 10323 := rs (se 1 (by rfl) ⟨7742, by rfl⟩) R15485
theorem R10351 : Reach 10351 := rs (se 1 (by rfl) ⟨7763, by rfl⟩) R15527
theorem R10359 : Reach 10359 := rs (se 1 (by rfl) ⟨7769, by rfl⟩) R15539
theorem R10361 : Reach 10361 := rs (se 2 (by rfl) ⟨3885, by rfl⟩) R7771
theorem R10363 : Reach 10363 := rs (se 1 (by rfl) ⟨7772, by rfl⟩) R15545
theorem R10581 : Reach 10581 := rs (se 10 (by rfl) ⟨15, by rfl⟩) R31
theorem R43415 : Reach 43415 := rs (se 1 (by rfl) ⟨32561, by rfl⟩) R65123
theorem R10693 : Reach 10693 := rs (se 4 (by rfl) ⟨1002, by rfl⟩) R2005
theorem R10765 : Reach 10765 := rs (se 3 (by rfl) ⟨2018, by rfl⟩) R4037
theorem R10769 : Reach 10769 := rs (se 2 (by rfl) ⟨4038, by rfl⟩) R8077
theorem R10793 : Reach 10793 := rs (se 2 (by rfl) ⟨4047, by rfl⟩) R8095
theorem R10805 : Reach 10805 := rs (se 5 (by rfl) ⟨506, by rfl⟩) R1013
theorem R10817 : Reach 10817 := rs (se 2 (by rfl) ⟨4056, by rfl⟩) R8113
theorem R10819 : Reach 10819 := rs (se 1 (by rfl) ⟨8114, by rfl⟩) R16229
theorem R10845 : Reach 10845 := rs (se 3 (by rfl) ⟨2033, by rfl⟩) R4067
theorem R10871 : Reach 10871 := rs (se 1 (by rfl) ⟨8153, by rfl⟩) R16307
theorem R10875 : Reach 10875 := rs (se 1 (by rfl) ⟨8156, by rfl⟩) R16313
theorem R10887 : Reach 10887 := rs (se 1 (by rfl) ⟨8165, by rfl⟩) R16331
theorem R10925 : Reach 10925 := rs (se 3 (by rfl) ⟨2048, by rfl⟩) R4097
theorem R10935 : Reach 10935 := rs (se 1 (by rfl) ⟨8201, by rfl⟩) R16403
theorem R10967 : Reach 10967 := rs (se 1 (by rfl) ⟨8225, by rfl⟩) R16451
theorem R10973 : Reach 10973 := rs (se 3 (by rfl) ⟨2057, by rfl⟩) R4115
theorem R11051 : Reach 11051 := rs (se 1 (by rfl) ⟨8288, by rfl⟩) R16577
theorem R11113 : Reach 11113 := rs (se 2 (by rfl) ⟨4167, by rfl⟩) R8335
theorem R11127 : Reach 11127 := rs (se 1 (by rfl) ⟨8345, by rfl⟩) R16691
theorem R11133 : Reach 11133 := rs (se 3 (by rfl) ⟨2087, by rfl⟩) R4175
theorem R11175 : Reach 11175 := rs (se 1 (by rfl) ⟨8381, by rfl⟩) R16763
theorem R45787 : Reach 45787 := rs (se 1 (by rfl) ⟨34340, by rfl⟩) R68681
theorem R80351 : Reach 80351 := rs (se 1 (by rfl) ⟨60263, by rfl⟩) R120527
theorem R82619 : Reach 82619 := rs (se 1 (by rfl) ⟨61964, by rfl⟩) R123929
theorem R84077 : Reach 84077 := rs (se 3 (by rfl) ⟨15764, by rfl⟩) R31529
theorem R19865 : Reach 19865 := rs (se 2 (by rfl) ⟨7449, by rfl⟩) R14899
theorem R19871 : Reach 19871 := rs (se 1 (by rfl) ⟨14903, by rfl⟩) R29807
theorem R20101 : Reach 20101 := rs (se 4 (by rfl) ⟨1884, by rfl⟩) R3769
theorem R20645 : Reach 20645 := rs (se 4 (by rfl) ⟨1935, by rfl⟩) R3871
theorem R20717 : Reach 20717 := rs (se 3 (by rfl) ⟨3884, by rfl⟩) R7769
theorem R21019 : Reach 21019 := rs (se 1 (by rfl) ⟨15764, by rfl⟩) R31529
theorem R21539 : Reach 21539 := rs (se 1 (by rfl) ⟨16154, by rfl⟩) R32309
theorem R21617 : Reach 21617 := rs (se 2 (by rfl) ⟨8106, by rfl⟩) R16213
theorem R21635 : Reach 21635 := rs (se 1 (by rfl) ⟨16226, by rfl⟩) R32453
theorem R21707 : Reach 21707 := rs (se 1 (by rfl) ⟨16280, by rfl⟩) R32561
theorem R21869 : Reach 21869 := rs (se 3 (by rfl) ⟨4100, by rfl⟩) R8201
theorem R21941 : Reach 21941 := rs (se 5 (by rfl) ⟨1028, by rfl⟩) R2057
theorem R21961 : Reach 21961 := rs (se 2 (by rfl) ⟨8235, by rfl⟩) R16471
theorem R22103 : Reach 22103 := rs (se 1 (by rfl) ⟨16577, by rfl⟩) R33155
theorem R22265 : Reach 22265 := rs (se 2 (by rfl) ⟨8349, by rfl⟩) R16699
theorem R89189 : Reach 89189 := rs (se 4 (by rfl) ⟨8361, by rfl⟩) R16723
theorem R319177 : Reach 319177 := rs (se 2 (by rfl) ⟨119691, by rfl⟩) R239383
theorem R24715 : Reach 24715 := rs (se 1 (by rfl) ⟨18536, by rfl⟩) R37073
theorem R715817 : Reach 715817 := rs (se 2 (by rfl) ⟨268431, by rfl⟩) R536863
theorem R159583 : Reach 159583 := rs (se 1 (by rfl) ⟨119687, by rfl⟩) R239375
theorem R27 : Reach 27 := rs (se 1 (by rfl) ⟨20, by rfl⟩) R41
theorem R55 : Reach 55 := rs (se 1 (by rfl) ⟨41, by rfl⟩) R83
theorem R109 : Reach 109 := rs (se 3 (by rfl) ⟨20, by rfl⟩) R41
theorem R221 : Reach 221 := rs (se 3 (by rfl) ⟨41, by rfl⟩) R83
theorem R437 : Reach 437 := rs (se 5 (by rfl) ⟨20, by rfl⟩) R41
theorem R449 : Reach 449 := rs (se 2 (by rfl) ⟨168, by rfl⟩) R337
theorem R131813 : Reach 131813 := rs (se 4 (by rfl) ⟨12357, by rfl⟩) R24715
theorem R881 : Reach 881 := rs (se 2 (by rfl) ⟨330, by rfl⟩) R661
theorem R885 : Reach 885 := rs (se 5 (by rfl) ⟨41, by rfl⟩) R83
theorem R899 : Reach 899 := rs (se 1 (by rfl) ⟨674, by rfl⟩) R1349
theorem R903 : Reach 903 := rs (se 1 (by rfl) ⟨677, by rfl⟩) R1355
theorem R927 : Reach 927 := rs (se 1 (by rfl) ⟨695, by rfl⟩) R1391
theorem R1749 : Reach 1749 := rs (se 7 (by rfl) ⟨20, by rfl⟩) R41
theorem R1763 : Reach 1763 := rs (se 1 (by rfl) ⟨1322, by rfl⟩) R2645
theorem R1777 : Reach 1777 := rs (se 2 (by rfl) ⟨666, by rfl⟩) R1333
theorem R1793 : Reach 1793 := rs (se 2 (by rfl) ⟨672, by rfl⟩) R1345
theorem R1797 : Reach 1797 := rs (se 4 (by rfl) ⟨168, by rfl⟩) R337
theorem R1807 : Reach 1807 := rs (se 1 (by rfl) ⟨1355, by rfl⟩) R2711
theorem R1855 : Reach 1855 := rs (se 1 (by rfl) ⟨1391, by rfl⟩) R2783
theorem R3323 : Reach 3323 := rs (se 1 (by rfl) ⟨2492, by rfl⟩) R4985
theorem R3399 : Reach 3399 := rs (se 1 (by rfl) ⟨2549, by rfl⟩) R5099
theorem R3431 : Reach 3431 := rs (se 1 (by rfl) ⟨2573, by rfl⟩) R5147
theorem R3525 : Reach 3525 := rs (se 4 (by rfl) ⟨330, by rfl⟩) R661
theorem R3541 : Reach 3541 := rs (se 7 (by rfl) ⟨41, by rfl⟩) R83
theorem R3555 : Reach 3555 := rs (se 1 (by rfl) ⟨2666, by rfl⟩) R5333
theorem R3587 : Reach 3587 := rs (se 1 (by rfl) ⟨2690, by rfl⟩) R5381
theorem R3597 : Reach 3597 := rs (se 3 (by rfl) ⟨674, by rfl⟩) R1349
theorem R3601 : Reach 3601 := rs (se 2 (by rfl) ⟨1350, by rfl⟩) R2701
theorem R3613 : Reach 3613 := rs (se 3 (by rfl) ⟨677, by rfl⟩) R1355
theorem R3623 : Reach 3623 := rs (se 1 (by rfl) ⟨2717, by rfl⟩) R5435
theorem R3641 : Reach 3641 := rs (se 2 (by rfl) ⟨1365, by rfl⟩) R2731
theorem R3655 : Reach 3655 := rs (se 1 (by rfl) ⟨2741, by rfl⟩) R5483
theorem R3657 : Reach 3657 := rs (se 2 (by rfl) ⟨1371, by rfl⟩) R2743
theorem R3709 : Reach 3709 := rs (se 3 (by rfl) ⟨695, by rfl⟩) R1391
theorem R6647 : Reach 6647 := rs (se 1 (by rfl) ⟨4985, by rfl⟩) R9971
theorem R6799 : Reach 6799 := rs (se 1 (by rfl) ⟨5099, by rfl⟩) R10199
theorem R6823 : Reach 6823 := rs (se 1 (by rfl) ⟨5117, by rfl⟩) R10235
theorem R6825 : Reach 6825 := rs (se 2 (by rfl) ⟨2559, by rfl⟩) R5119
theorem R6863 : Reach 6863 := rs (se 1 (by rfl) ⟨5147, by rfl⟩) R10295
theorem R6881 : Reach 6881 := rs (se 2 (by rfl) ⟨2580, by rfl⟩) R5161
theorem R6905 : Reach 6905 := rs (se 2 (by rfl) ⟨2589, by rfl⟩) R5179
theorem R6907 : Reach 6907 := rs (se 1 (by rfl) ⟨5180, by rfl⟩) R10361
theorem R6997 : Reach 6997 := rs (se 9 (by rfl) ⟨20, by rfl⟩) R41
theorem R7053 : Reach 7053 := rs (se 3 (by rfl) ⟨1322, by rfl⟩) R2645
theorem R7109 : Reach 7109 := rs (se 4 (by rfl) ⟨666, by rfl⟩) R1333
theorem R7129 : Reach 7129 := rs (se 2 (by rfl) ⟨2673, by rfl⟩) R5347
theorem R7173 : Reach 7173 := rs (se 4 (by rfl) ⟨672, by rfl⟩) R1345
theorem R7179 : Reach 7179 := rs (se 1 (by rfl) ⟨5384, by rfl⟩) R10769
theorem R7189 : Reach 7189 := rs (se 6 (by rfl) ⟨168, by rfl⟩) R337
theorem R7195 : Reach 7195 := rs (se 1 (by rfl) ⟨5396, by rfl⟩) R10793
theorem R7203 : Reach 7203 := rs (se 1 (by rfl) ⟨5402, by rfl⟩) R10805
theorem R7211 : Reach 7211 := rs (se 1 (by rfl) ⟨5408, by rfl⟩) R10817
theorem R7229 : Reach 7229 := rs (se 3 (by rfl) ⟨1355, by rfl⟩) R2711
theorem R7247 : Reach 7247 := rs (se 1 (by rfl) ⟨5435, by rfl⟩) R10871
theorem R7283 : Reach 7283 := rs (se 1 (by rfl) ⟨5462, by rfl⟩) R10925
theorem R7289 : Reach 7289 := rs (se 2 (by rfl) ⟨2733, by rfl⟩) R5467
theorem R7311 : Reach 7311 := rs (se 1 (by rfl) ⟨5483, by rfl⟩) R10967
theorem R7313 : Reach 7313 := rs (se 2 (by rfl) ⟨2742, by rfl⟩) R5485
theorem R7315 : Reach 7315 := rs (se 1 (by rfl) ⟨5486, by rfl⟩) R10973
theorem R7367 : Reach 7367 := rs (se 1 (by rfl) ⟨5525, by rfl⟩) R11051
theorem R7417 : Reach 7417 := rs (se 2 (by rfl) ⟨2781, by rfl⟩) R5563
theorem R7421 : Reach 7421 := rs (se 3 (by rfl) ⟨1391, by rfl⟩) R2783
theorem R109259 : Reach 109259 := rs (se 1 (by rfl) ⟨81944, by rfl⟩) R163889
theorem R896807 : Reach 896807 := rs (se 1 (by rfl) ⟨672605, by rfl⟩) R1345211
theorem R13241 : Reach 13241 := rs (se 2 (by rfl) ⟨4965, by rfl⟩) R9931
theorem R13243 : Reach 13243 := rs (se 1 (by rfl) ⟨9932, by rfl⟩) R19865
theorem R13247 : Reach 13247 := rs (se 1 (by rfl) ⟨9935, by rfl⟩) R19871
theorem R13409 : Reach 13409 := rs (se 2 (by rfl) ⟨5028, by rfl⟩) R10057
theorem R13649 : Reach 13649 := rs (se 2 (by rfl) ⟨5118, by rfl⟩) R10237
theorem R13763 : Reach 13763 := rs (se 1 (by rfl) ⟨10322, by rfl⟩) R20645
theorem R112103 : Reach 112103 := rs (se 1 (by rfl) ⟨84077, by rfl⟩) R168155
theorem R13801 : Reach 13801 := rs (se 2 (by rfl) ⟨5175, by rfl⟩) R10351
theorem R13811 : Reach 13811 := rs (se 1 (by rfl) ⟨10358, by rfl⟩) R20717
theorem R13817 : Reach 13817 := rs (se 2 (by rfl) ⟨5181, by rfl⟩) R10363
theorem R14165 : Reach 14165 := rs (se 9 (by rfl) ⟨41, by rfl⟩) R83
theorem R14359 : Reach 14359 := rs (se 1 (by rfl) ⟨10769, by rfl⟩) R21539
theorem R14389 : Reach 14389 := rs (se 5 (by rfl) ⟨674, by rfl⟩) R1349
theorem R14405 : Reach 14405 := rs (se 4 (by rfl) ⟨1350, by rfl⟩) R2701
theorem R14411 : Reach 14411 := rs (se 1 (by rfl) ⟨10808, by rfl⟩) R21617
theorem R14423 : Reach 14423 := rs (se 1 (by rfl) ⟨10817, by rfl⟩) R21635
theorem R14453 : Reach 14453 := rs (se 5 (by rfl) ⟨677, by rfl⟩) R1355
theorem R14471 : Reach 14471 := rs (se 1 (by rfl) ⟨10853, by rfl⟩) R21707
theorem R14579 : Reach 14579 := rs (se 1 (by rfl) ⟨10934, by rfl⟩) R21869
theorem R14621 : Reach 14621 := rs (se 3 (by rfl) ⟨2741, by rfl⟩) R5483
theorem R14627 : Reach 14627 := rs (se 1 (by rfl) ⟨10970, by rfl⟩) R21941
theorem R14735 : Reach 14735 := rs (se 1 (by rfl) ⟨11051, by rfl⟩) R22103
theorem R14837 : Reach 14837 := rs (se 5 (by rfl) ⟨695, by rfl⟩) R1391
theorem R14843 : Reach 14843 := rs (se 1 (by rfl) ⟨11132, by rfl⟩) R22265
theorem R212777 : Reach 212777 := rs (se 2 (by rfl) ⟨79791, by rfl⟩) R159583
theorem R477211 : Reach 477211 := rs (se 1 (by rfl) ⟨357908, by rfl⟩) R715817
theorem R52973 : Reach 52973 := rs (se 3 (by rfl) ⟨9932, by rfl⟩) R19865
theorem R53567 : Reach 53567 := rs (se 1 (by rfl) ⟨40175, by rfl⟩) R80351
theorem R55079 : Reach 55079 := rs (se 1 (by rfl) ⟨41309, by rfl⟩) R82619
theorem R56051 : Reach 56051 := rs (se 1 (by rfl) ⟨42038, by rfl⟩) R84077
theorem R7625933 : Reach 7625933 := rs (se 3 (by rfl) ⟨1429862, by rfl⟩) R2859725
theorem R26495 : Reach 26495 := rs (se 1 (by rfl) ⟨19871, by rfl⟩) R39743
theorem R26527 : Reach 26527 := rs (se 1 (by rfl) ⟨19895, by rfl⟩) R39791
theorem R59459 : Reach 59459 := rs (se 1 (by rfl) ⟨44594, by rfl⟩) R89189
theorem R26783 : Reach 26783 := rs (se 1 (by rfl) ⟨20087, by rfl⟩) R40175
theorem R26801 : Reach 26801 := rs (se 2 (by rfl) ⟨10050, by rfl⟩) R20101
theorem R26819 : Reach 26819 := rs (se 1 (by rfl) ⟨20114, by rfl⟩) R40229
theorem R27197 : Reach 27197 := rs (se 3 (by rfl) ⟨5099, by rfl⟩) R10199
theorem R27199 : Reach 27199 := rs (se 1 (by rfl) ⟨20399, by rfl⟩) R40799
theorem R27629 : Reach 27629 := rs (se 3 (by rfl) ⟨5180, by rfl⟩) R10361
theorem R27989 : Reach 27989 := rs (se 11 (by rfl) ⟨20, by rfl⟩) R41
theorem R28025 : Reach 28025 := rs (se 2 (by rfl) ⟨10509, by rfl⟩) R21019
theorem R61049 : Reach 61049 := rs (se 2 (by rfl) ⟨22893, by rfl⟩) R45787
theorem R28781 : Reach 28781 := rs (se 3 (by rfl) ⟨5396, by rfl⟩) R10793
theorem R28943 : Reach 28943 := rs (se 1 (by rfl) ⟨21707, by rfl⟩) R43415
theorem R29261 : Reach 29261 := rs (se 3 (by rfl) ⟨5486, by rfl⟩) R10973
theorem R29281 : Reach 29281 := rs (se 2 (by rfl) ⟨10980, by rfl⟩) R21961
theorem R425569 : Reach 425569 := rs (se 2 (by rfl) ⟨159588, by rfl⟩) R319177
theorem R73 : Reach 73 := rs (se 2 (by rfl) ⟨27, by rfl⟩) R55
theorem R145 : Reach 145 := rs (se 2 (by rfl) ⟨54, by rfl⟩) R109
theorem R147 : Reach 147 := rs (se 1 (by rfl) ⟨110, by rfl⟩) R221
theorem R291 : Reach 291 := rs (se 1 (by rfl) ⟨218, by rfl⟩) R437
theorem R293 : Reach 293 := rs (se 4 (by rfl) ⟨27, by rfl⟩) R55
theorem R299 : Reach 299 := rs (se 1 (by rfl) ⟨224, by rfl⟩) R449
theorem R581 : Reach 581 := rs (se 4 (by rfl) ⟨54, by rfl⟩) R109
theorem R587 : Reach 587 := rs (se 1 (by rfl) ⟨440, by rfl⟩) R881
theorem R589 : Reach 589 := rs (se 3 (by rfl) ⟨110, by rfl⟩) R221
theorem R599 : Reach 599 := rs (se 1 (by rfl) ⟨449, by rfl⟩) R899
theorem R1165 : Reach 1165 := rs (se 3 (by rfl) ⟨218, by rfl⟩) R437
theorem R1173 : Reach 1173 := rs (se 6 (by rfl) ⟨27, by rfl⟩) R55
theorem R1175 : Reach 1175 := rs (se 1 (by rfl) ⟨881, by rfl⟩) R1763
theorem R1195 : Reach 1195 := rs (se 1 (by rfl) ⟨896, by rfl⟩) R1793
theorem R1197 : Reach 1197 := rs (se 3 (by rfl) ⟨224, by rfl⟩) R449
theorem R2215 : Reach 2215 := rs (se 1 (by rfl) ⟨1661, by rfl⟩) R3323
theorem R2287 : Reach 2287 := rs (se 1 (by rfl) ⟨1715, by rfl⟩) R3431
theorem R2325 : Reach 2325 := rs (se 6 (by rfl) ⟨54, by rfl⟩) R109
theorem R2349 : Reach 2349 := rs (se 3 (by rfl) ⟨440, by rfl⟩) R881
theorem R2357 : Reach 2357 := rs (se 5 (by rfl) ⟨110, by rfl⟩) R221
theorem R2369 : Reach 2369 := rs (se 2 (by rfl) ⟨888, by rfl⟩) R1777
theorem R2391 : Reach 2391 := rs (se 1 (by rfl) ⟨1793, by rfl⟩) R3587
theorem R2397 : Reach 2397 := rs (se 3 (by rfl) ⟨449, by rfl⟩) R899
theorem R2409 : Reach 2409 := rs (se 2 (by rfl) ⟨903, by rfl⟩) R1807
theorem R2415 : Reach 2415 := rs (se 1 (by rfl) ⟨1811, by rfl⟩) R3623
theorem R2427 : Reach 2427 := rs (se 1 (by rfl) ⟨1820, by rfl⟩) R3641
theorem R2473 : Reach 2473 := rs (se 2 (by rfl) ⟨927, by rfl⟩) R1855
theorem R35315 : Reach 35315 := rs (se 1 (by rfl) ⟨26486, by rfl⟩) R52973
theorem R35369 : Reach 35369 := rs (se 2 (by rfl) ⟨13263, by rfl⟩) R26527
theorem R35711 : Reach 35711 := rs (se 1 (by rfl) ⟨26783, by rfl⟩) R53567
theorem R36389 : Reach 36389 := rs (se 4 (by rfl) ⟨3411, by rfl⟩) R6823
theorem R36701 : Reach 36701 := rs (se 3 (by rfl) ⟨6881, by rfl⟩) R13763
theorem R36719 : Reach 36719 := rs (se 1 (by rfl) ⟨27539, by rfl⟩) R55079
theorem R36845 : Reach 36845 := rs (se 3 (by rfl) ⟨6908, by rfl⟩) R13817
theorem R4431 : Reach 4431 := rs (se 1 (by rfl) ⟨3323, by rfl⟩) R6647
theorem R37205 : Reach 37205 := rs (se 10 (by rfl) ⟨54, by rfl⟩) R109
theorem R4575 : Reach 4575 := rs (se 1 (by rfl) ⟨3431, by rfl⟩) R6863
theorem R4587 : Reach 4587 := rs (se 1 (by rfl) ⟨3440, by rfl⟩) R6881
theorem R37367 : Reach 37367 := rs (se 1 (by rfl) ⟨28025, by rfl⟩) R56051
theorem R4603 : Reach 4603 := rs (se 1 (by rfl) ⟨3452, by rfl⟩) R6905
theorem R4661 : Reach 4661 := rs (se 5 (by rfl) ⟨218, by rfl⟩) R437
theorem R4693 : Reach 4693 := rs (se 8 (by rfl) ⟨27, by rfl⟩) R55
theorem R4701 : Reach 4701 := rs (se 3 (by rfl) ⟨881, by rfl⟩) R1763
theorem R4721 : Reach 4721 := rs (se 2 (by rfl) ⟨1770, by rfl⟩) R3541
theorem R4739 : Reach 4739 := rs (se 1 (by rfl) ⟨3554, by rfl⟩) R7109
theorem R4781 : Reach 4781 := rs (se 3 (by rfl) ⟨896, by rfl⟩) R1793
theorem R4789 : Reach 4789 := rs (se 5 (by rfl) ⟨224, by rfl⟩) R449
theorem R4801 : Reach 4801 := rs (se 2 (by rfl) ⟨1800, by rfl⟩) R3601
theorem R4807 : Reach 4807 := rs (se 1 (by rfl) ⟨3605, by rfl⟩) R7211
theorem R4817 : Reach 4817 := rs (se 2 (by rfl) ⟨1806, by rfl⟩) R3613
theorem R4819 : Reach 4819 := rs (se 1 (by rfl) ⟨3614, by rfl⟩) R7229
theorem R37589 : Reach 37589 := rs (se 7 (by rfl) ⟨440, by rfl⟩) R881
theorem R4831 : Reach 4831 := rs (se 1 (by rfl) ⟨3623, by rfl⟩) R7247
theorem R4855 : Reach 4855 := rs (se 1 (by rfl) ⟨3641, by rfl⟩) R7283
theorem R4859 : Reach 4859 := rs (se 1 (by rfl) ⟨3644, by rfl⟩) R7289
theorem R4873 : Reach 4873 := rs (se 2 (by rfl) ⟨1827, by rfl⟩) R3655
theorem R4875 : Reach 4875 := rs (se 1 (by rfl) ⟨3656, by rfl⟩) R7313
theorem R4911 : Reach 4911 := rs (se 1 (by rfl) ⟨3683, by rfl⟩) R7367
theorem R5083955 : Reach 5083955 := rs (se 1 (by rfl) ⟨3812966, by rfl⟩) R7625933
theorem R4945 : Reach 4945 := rs (se 2 (by rfl) ⟨1854, by rfl⟩) R3709
theorem R4947 : Reach 4947 := rs (se 1 (by rfl) ⟨3710, by rfl⟩) R7421
theorem R38341 : Reach 38341 := rs (se 4 (by rfl) ⟨3594, by rfl⟩) R7189
theorem R39041 : Reach 39041 := rs (se 2 (by rfl) ⟨14640, by rfl⟩) R29281
theorem R39581 : Reach 39581 := rs (se 3 (by rfl) ⟨7421, by rfl⟩) R14843
theorem R72839 : Reach 72839 := rs (se 1 (by rfl) ⟨54629, by rfl⟩) R109259
theorem R40699 : Reach 40699 := rs (se 1 (by rfl) ⟨30524, by rfl⟩) R61049
theorem R597871 : Reach 597871 := rs (se 1 (by rfl) ⟨448403, by rfl⟩) R896807
theorem R8827 : Reach 8827 := rs (se 1 (by rfl) ⟨6620, by rfl⟩) R13241
theorem R8831 : Reach 8831 := rs (se 1 (by rfl) ⟨6623, by rfl⟩) R13247
theorem R8861 : Reach 8861 := rs (se 3 (by rfl) ⟨1661, by rfl⟩) R3323
theorem R8939 : Reach 8939 := rs (se 1 (by rfl) ⟨6704, by rfl⟩) R13409
theorem R9065 : Reach 9065 := rs (se 2 (by rfl) ⟨3399, by rfl⟩) R6799
theorem R9097 : Reach 9097 := rs (se 2 (by rfl) ⟨3411, by rfl⟩) R6823
theorem R9099 : Reach 9099 := rs (se 1 (by rfl) ⟨6824, by rfl⟩) R13649
theorem R9149 : Reach 9149 := rs (se 3 (by rfl) ⟨1715, by rfl⟩) R3431
theorem R9175 : Reach 9175 := rs (se 1 (by rfl) ⟨6881, by rfl⟩) R13763
theorem R74735 : Reach 74735 := rs (se 1 (by rfl) ⟨56051, by rfl⟩) R112103
theorem R9207 : Reach 9207 := rs (se 1 (by rfl) ⟨6905, by rfl⟩) R13811
theorem R9209 : Reach 9209 := rs (se 2 (by rfl) ⟨3453, by rfl⟩) R6907
theorem R9211 : Reach 9211 := rs (se 1 (by rfl) ⟨6908, by rfl⟩) R13817
theorem R9301 : Reach 9301 := rs (se 8 (by rfl) ⟨54, by rfl⟩) R109
theorem R9329 : Reach 9329 := rs (se 2 (by rfl) ⟨3498, by rfl⟩) R6997
theorem R9397 : Reach 9397 := rs (se 5 (by rfl) ⟨440, by rfl⟩) R881
theorem R9429 : Reach 9429 := rs (se 7 (by rfl) ⟨110, by rfl⟩) R221
theorem R9443 : Reach 9443 := rs (se 1 (by rfl) ⟨7082, by rfl⟩) R14165
theorem R9477 : Reach 9477 := rs (se 4 (by rfl) ⟨888, by rfl⟩) R1777
theorem R9505 : Reach 9505 := rs (se 2 (by rfl) ⟨3564, by rfl⟩) R7129
theorem R9565 : Reach 9565 := rs (se 3 (by rfl) ⟨1793, by rfl⟩) R3587
theorem R9585 : Reach 9585 := rs (se 2 (by rfl) ⟨3594, by rfl⟩) R7189
theorem R9589 : Reach 9589 := rs (se 5 (by rfl) ⟨449, by rfl⟩) R899
theorem R9593 : Reach 9593 := rs (se 2 (by rfl) ⟨3597, by rfl⟩) R7195
theorem R9603 : Reach 9603 := rs (se 1 (by rfl) ⟨7202, by rfl⟩) R14405
theorem R9607 : Reach 9607 := rs (se 1 (by rfl) ⟨7205, by rfl⟩) R14411
theorem R9615 : Reach 9615 := rs (se 1 (by rfl) ⟨7211, by rfl⟩) R14423
theorem R9635 : Reach 9635 := rs (se 1 (by rfl) ⟨7226, by rfl⟩) R14453
theorem R9637 : Reach 9637 := rs (se 4 (by rfl) ⟨903, by rfl⟩) R1807
theorem R9647 : Reach 9647 := rs (se 1 (by rfl) ⟨7235, by rfl⟩) R14471
theorem R9661 : Reach 9661 := rs (se 3 (by rfl) ⟨1811, by rfl⟩) R3623
theorem R9709 : Reach 9709 := rs (se 3 (by rfl) ⟨1820, by rfl⟩) R3641
theorem R9719 : Reach 9719 := rs (se 1 (by rfl) ⟨7289, by rfl⟩) R14579
theorem R9747 : Reach 9747 := rs (se 1 (by rfl) ⟨7310, by rfl⟩) R14621
theorem R9751 : Reach 9751 := rs (se 1 (by rfl) ⟨7313, by rfl⟩) R14627
theorem R9753 : Reach 9753 := rs (se 2 (by rfl) ⟨3657, by rfl⟩) R7315
theorem R9823 : Reach 9823 := rs (se 1 (by rfl) ⟨7367, by rfl⟩) R14735
theorem R9889 : Reach 9889 := rs (se 2 (by rfl) ⟨3708, by rfl⟩) R7417
theorem R9891 : Reach 9891 := rs (se 1 (by rfl) ⟨7418, by rfl⟩) R14837
theorem R9893 : Reach 9893 := rs (se 4 (by rfl) ⟨927, by rfl⟩) R1855
theorem R9895 : Reach 9895 := rs (se 1 (by rfl) ⟨7421, by rfl⟩) R14843
theorem R567425 : Reach 567425 := rs (se 2 (by rfl) ⟨212784, by rfl⟩) R425569
theorem R141851 : Reach 141851 := rs (se 1 (by rfl) ⟨106388, by rfl⟩) R212777
theorem R306965 : Reach 306965 := rs (se 6 (by rfl) ⟨7194, by rfl⟩) R14389
theorem R636281 : Reach 636281 := rs (se 2 (by rfl) ⟨238605, by rfl⟩) R477211
theorem R145061 : Reach 145061 := rs (se 4 (by rfl) ⟨13599, by rfl⟩) R27199
theorem R17657 : Reach 17657 := rs (se 2 (by rfl) ⟨6621, by rfl⟩) R13243
theorem R17663 : Reach 17663 := rs (se 1 (by rfl) ⟨13247, by rfl⟩) R26495
theorem R17725 : Reach 17725 := rs (se 3 (by rfl) ⟨3323, by rfl⟩) R6647
theorem R17855 : Reach 17855 := rs (se 1 (by rfl) ⟨13391, by rfl⟩) R26783
theorem R17867 : Reach 17867 := rs (se 1 (by rfl) ⟨13400, by rfl⟩) R26801
theorem R17879 : Reach 17879 := rs (se 1 (by rfl) ⟨13409, by rfl⟩) R26819
theorem R18131 : Reach 18131 := rs (se 1 (by rfl) ⟨13598, by rfl⟩) R27197
theorem R18301 : Reach 18301 := rs (se 3 (by rfl) ⟨3431, by rfl⟩) R6863
theorem R18401 : Reach 18401 := rs (se 2 (by rfl) ⟨6900, by rfl⟩) R13801
theorem R18413 : Reach 18413 := rs (se 3 (by rfl) ⟨3452, by rfl⟩) R6905
theorem R18419 : Reach 18419 := rs (se 1 (by rfl) ⟨13814, by rfl⟩) R27629
theorem R18659 : Reach 18659 := rs (se 1 (by rfl) ⟨13994, by rfl⟩) R27989
theorem R18683 : Reach 18683 := rs (se 1 (by rfl) ⟨14012, by rfl⟩) R28025
theorem R18773 : Reach 18773 := rs (se 10 (by rfl) ⟨27, by rfl⟩) R55
theorem R18805 : Reach 18805 := rs (se 5 (by rfl) ⟨881, by rfl⟩) R1763
theorem R19145 : Reach 19145 := rs (se 2 (by rfl) ⟨7179, by rfl⟩) R14359
theorem R19157 : Reach 19157 := rs (se 7 (by rfl) ⟨224, by rfl⟩) R449
theorem R19187 : Reach 19187 := rs (se 1 (by rfl) ⟨14390, by rfl⟩) R28781
theorem R19205 : Reach 19205 := rs (se 4 (by rfl) ⟨1800, by rfl⟩) R3601
theorem R19229 : Reach 19229 := rs (se 3 (by rfl) ⟨3605, by rfl⟩) R7211
theorem R19277 : Reach 19277 := rs (se 3 (by rfl) ⟨3614, by rfl⟩) R7229
theorem R19295 : Reach 19295 := rs (se 1 (by rfl) ⟨14471, by rfl⟩) R28943
theorem R19325 : Reach 19325 := rs (se 3 (by rfl) ⟨3623, by rfl⟩) R7247
theorem R19421 : Reach 19421 := rs (se 3 (by rfl) ⟨3641, by rfl⟩) R7283
theorem R19493 : Reach 19493 := rs (se 4 (by rfl) ⟨1827, by rfl⟩) R3655
theorem R19507 : Reach 19507 := rs (se 1 (by rfl) ⟨14630, by rfl⟩) R29261
theorem R19781 : Reach 19781 := rs (se 4 (by rfl) ⟨1854, by rfl⟩) R3709
theorem R87875 : Reach 87875 := rs (se 1 (by rfl) ⟨65906, by rfl⟩) R131813
theorem R158557 : Reach 158557 := rs (se 3 (by rfl) ⟨29729, by rfl⟩) R59459
theorem R97 : Reach 97 := rs (se 2 (by rfl) ⟨36, by rfl⟩) R73
theorem R193 : Reach 193 := rs (se 2 (by rfl) ⟨72, by rfl⟩) R145
theorem R195 : Reach 195 := rs (se 1 (by rfl) ⟨146, by rfl⟩) R293
theorem R199 : Reach 199 := rs (se 1 (by rfl) ⟨149, by rfl⟩) R299
theorem R387 : Reach 387 := rs (se 1 (by rfl) ⟨290, by rfl⟩) R581
theorem R389 : Reach 389 := rs (se 4 (by rfl) ⟨36, by rfl⟩) R73
theorem R391 : Reach 391 := rs (se 1 (by rfl) ⟨293, by rfl⟩) R587
theorem R399 : Reach 399 := rs (se 1 (by rfl) ⟨299, by rfl⟩) R599
theorem R773 : Reach 773 := rs (se 4 (by rfl) ⟨72, by rfl⟩) R145
theorem R781 : Reach 781 := rs (se 3 (by rfl) ⟨146, by rfl⟩) R293
theorem R783 : Reach 783 := rs (se 1 (by rfl) ⟨587, by rfl⟩) R1175
theorem R785 : Reach 785 := rs (se 2 (by rfl) ⟨294, by rfl⟩) R589
theorem R797 : Reach 797 := rs (se 3 (by rfl) ⟨149, by rfl⟩) R299
theorem R1549 : Reach 1549 := rs (se 3 (by rfl) ⟨290, by rfl⟩) R581
theorem R1553 : Reach 1553 := rs (se 2 (by rfl) ⟨582, by rfl⟩) R1165
theorem R1557 : Reach 1557 := rs (se 6 (by rfl) ⟨36, by rfl⟩) R73
theorem R1565 : Reach 1565 := rs (se 3 (by rfl) ⟨293, by rfl⟩) R587
theorem R1571 : Reach 1571 := rs (se 1 (by rfl) ⟨1178, by rfl⟩) R2357
theorem R1579 : Reach 1579 := rs (se 1 (by rfl) ⟨1184, by rfl⟩) R2369
theorem R1593 : Reach 1593 := rs (se 2 (by rfl) ⟨597, by rfl⟩) R1195
theorem R1597 : Reach 1597 := rs (se 3 (by rfl) ⟨299, by rfl⟩) R599
theorem R100237 : Reach 100237 := rs (se 3 (by rfl) ⟨18794, by rfl⟩) R37589
theorem R2953 : Reach 2953 := rs (se 2 (by rfl) ⟨1107, by rfl⟩) R2215
theorem R3049 : Reach 3049 := rs (se 2 (by rfl) ⟨1143, by rfl⟩) R2287
theorem R3093 : Reach 3093 := rs (se 6 (by rfl) ⟨72, by rfl⟩) R145
theorem R3107 : Reach 3107 := rs (se 1 (by rfl) ⟨2330, by rfl⟩) R4661
theorem R3125 : Reach 3125 := rs (se 5 (by rfl) ⟨146, by rfl⟩) R293
theorem R3133 : Reach 3133 := rs (se 3 (by rfl) ⟨587, by rfl⟩) R1175
theorem R3141 : Reach 3141 := rs (se 4 (by rfl) ⟨294, by rfl⟩) R589
theorem R3147 : Reach 3147 := rs (se 1 (by rfl) ⟨2360, by rfl⟩) R4721
theorem R3159 : Reach 3159 := rs (se 1 (by rfl) ⟨2369, by rfl⟩) R4739
theorem R3187 : Reach 3187 := rs (se 1 (by rfl) ⟨2390, by rfl⟩) R4781
theorem R3189 : Reach 3189 := rs (se 5 (by rfl) ⟨149, by rfl⟩) R299
theorem R3211 : Reach 3211 := rs (se 1 (by rfl) ⟨2408, by rfl⟩) R4817
theorem R3239 : Reach 3239 := rs (se 1 (by rfl) ⟨2429, by rfl⟩) R4859
theorem R3297 : Reach 3297 := rs (se 2 (by rfl) ⟨1236, by rfl⟩) R2473
theorem R5887 : Reach 5887 := rs (se 1 (by rfl) ⟨4415, by rfl⟩) R8831
theorem R5907 : Reach 5907 := rs (se 1 (by rfl) ⟨4430, by rfl⟩) R8861
theorem R5959 : Reach 5959 := rs (se 1 (by rfl) ⟨4469, by rfl⟩) R8939
theorem R6043 : Reach 6043 := rs (se 1 (by rfl) ⟨4532, by rfl⟩) R9065
theorem R6099 : Reach 6099 := rs (se 1 (by rfl) ⟨4574, by rfl⟩) R9149
theorem R6137 : Reach 6137 := rs (se 2 (by rfl) ⟨2301, by rfl⟩) R4603
theorem R6139 : Reach 6139 := rs (se 1 (by rfl) ⟨4604, by rfl⟩) R9209
theorem R6197 : Reach 6197 := rs (se 5 (by rfl) ⟨290, by rfl⟩) R581
theorem R6213 : Reach 6213 := rs (se 4 (by rfl) ⟨582, by rfl⟩) R1165
theorem R6219 : Reach 6219 := rs (se 1 (by rfl) ⟨4664, by rfl⟩) R9329
theorem R6229 : Reach 6229 := rs (se 8 (by rfl) ⟨36, by rfl⟩) R73
theorem R6257 : Reach 6257 := rs (se 2 (by rfl) ⟨2346, by rfl⟩) R4693
theorem R6261 : Reach 6261 := rs (se 5 (by rfl) ⟨293, by rfl⟩) R587
theorem R6285 : Reach 6285 := rs (se 3 (by rfl) ⟨1178, by rfl⟩) R2357
theorem R6295 : Reach 6295 := rs (se 1 (by rfl) ⟨4721, by rfl⟩) R9443
theorem R6317 : Reach 6317 := rs (se 3 (by rfl) ⟨1184, by rfl⟩) R2369
theorem R6373 : Reach 6373 := rs (se 4 (by rfl) ⟨597, by rfl⟩) R1195
theorem R6385 : Reach 6385 := rs (se 2 (by rfl) ⟨2394, by rfl⟩) R4789
theorem R6389 : Reach 6389 := rs (se 5 (by rfl) ⟨299, by rfl⟩) R599
theorem R6395 : Reach 6395 := rs (se 1 (by rfl) ⟨4796, by rfl⟩) R9593
theorem R6401 : Reach 6401 := rs (se 2 (by rfl) ⟨2400, by rfl⟩) R4801
theorem R6409 : Reach 6409 := rs (se 2 (by rfl) ⟨2403, by rfl⟩) R4807
theorem R6423 : Reach 6423 := rs (se 1 (by rfl) ⟨4817, by rfl⟩) R9635
theorem R6425 : Reach 6425 := rs (se 2 (by rfl) ⟨2409, by rfl⟩) R4819
theorem R6431 : Reach 6431 := rs (se 1 (by rfl) ⟨4823, by rfl⟩) R9647
theorem R6441 : Reach 6441 := rs (se 2 (by rfl) ⟨2415, by rfl⟩) R4831
theorem R6473 : Reach 6473 := rs (se 2 (by rfl) ⟨2427, by rfl⟩) R4855
theorem R6479 : Reach 6479 := rs (se 1 (by rfl) ⟨4859, by rfl⟩) R9719
theorem R6497 : Reach 6497 := rs (se 2 (by rfl) ⟨2436, by rfl⟩) R4873
theorem R6593 : Reach 6593 := rs (se 2 (by rfl) ⟨2472, by rfl⟩) R4945
theorem R6595 : Reach 6595 := rs (se 1 (by rfl) ⟨4946, by rfl⟩) R9893
theorem R204643 : Reach 204643 := rs (se 1 (by rfl) ⟨153482, by rfl⟩) R306965
theorem R797161 : Reach 797161 := rs (se 2 (by rfl) ⟨298935, by rfl⟩) R597871
theorem R11769 : Reach 11769 := rs (se 2 (by rfl) ⟨4413, by rfl⟩) R8827
theorem R11771 : Reach 11771 := rs (se 1 (by rfl) ⟨8828, by rfl⟩) R17657
theorem R11775 : Reach 11775 := rs (se 1 (by rfl) ⟨8831, by rfl⟩) R17663
theorem R11813 : Reach 11813 := rs (se 4 (by rfl) ⟨1107, by rfl⟩) R2215
theorem R11903 : Reach 11903 := rs (se 1 (by rfl) ⟨8927, by rfl⟩) R17855
theorem R11911 : Reach 11911 := rs (se 1 (by rfl) ⟨8933, by rfl⟩) R17867
theorem R11919 : Reach 11919 := rs (se 1 (by rfl) ⟨8939, by rfl⟩) R17879
theorem R12087 : Reach 12087 := rs (se 1 (by rfl) ⟨9065, by rfl⟩) R18131
theorem R12129 : Reach 12129 := rs (se 2 (by rfl) ⟨4548, by rfl⟩) R9097
theorem R12197 : Reach 12197 := rs (se 4 (by rfl) ⟨1143, by rfl⟩) R2287
theorem R12233 : Reach 12233 := rs (se 2 (by rfl) ⟨4587, by rfl⟩) R9175
theorem R12267 : Reach 12267 := rs (se 1 (by rfl) ⟨9200, by rfl⟩) R18401
theorem R12275 : Reach 12275 := rs (se 1 (by rfl) ⟨9206, by rfl⟩) R18413
theorem R12279 : Reach 12279 := rs (se 1 (by rfl) ⟨9209, by rfl⟩) R18419
theorem R12281 : Reach 12281 := rs (se 2 (by rfl) ⟨4605, by rfl⟩) R9211
theorem R12373 : Reach 12373 := rs (se 8 (by rfl) ⟨72, by rfl⟩) R145
theorem R12401 : Reach 12401 := rs (se 2 (by rfl) ⟨4650, by rfl⟩) R9301
theorem R12429 : Reach 12429 := rs (se 3 (by rfl) ⟨2330, by rfl⟩) R4661
theorem R12439 : Reach 12439 := rs (se 1 (by rfl) ⟨9329, by rfl⟩) R18659
theorem R12455 : Reach 12455 := rs (se 1 (by rfl) ⟨9341, by rfl⟩) R18683
theorem R12501 : Reach 12501 := rs (se 7 (by rfl) ⟨146, by rfl⟩) R293
theorem R12515 : Reach 12515 := rs (se 1 (by rfl) ⟨9386, by rfl⟩) R18773
theorem R12529 : Reach 12529 := rs (se 2 (by rfl) ⟨4698, by rfl⟩) R9397
theorem R12533 : Reach 12533 := rs (se 5 (by rfl) ⟨587, by rfl⟩) R1175
theorem R12565 : Reach 12565 := rs (se 6 (by rfl) ⟨294, by rfl⟩) R589
theorem R12589 : Reach 12589 := rs (se 3 (by rfl) ⟨2360, by rfl⟩) R4721
theorem R12637 : Reach 12637 := rs (se 3 (by rfl) ⟨2369, by rfl⟩) R4739
theorem R12673 : Reach 12673 := rs (se 2 (by rfl) ⟨4752, by rfl⟩) R9505
theorem R12749 : Reach 12749 := rs (se 3 (by rfl) ⟨2390, by rfl⟩) R4781
theorem R12753 : Reach 12753 := rs (se 2 (by rfl) ⟨4782, by rfl⟩) R9565
theorem R12757 : Reach 12757 := rs (se 7 (by rfl) ⟨149, by rfl⟩) R299
theorem R12763 : Reach 12763 := rs (se 1 (by rfl) ⟨9572, by rfl⟩) R19145
theorem R12771 : Reach 12771 := rs (se 1 (by rfl) ⟨9578, by rfl⟩) R19157
theorem R12785 : Reach 12785 := rs (se 2 (by rfl) ⟨4794, by rfl⟩) R9589
theorem R12791 : Reach 12791 := rs (se 1 (by rfl) ⟨9593, by rfl⟩) R19187
theorem R12803 : Reach 12803 := rs (se 1 (by rfl) ⟨9602, by rfl⟩) R19205
theorem R12809 : Reach 12809 := rs (se 2 (by rfl) ⟨4803, by rfl⟩) R9607
theorem R12819 : Reach 12819 := rs (se 1 (by rfl) ⟨9614, by rfl⟩) R19229
theorem R12845 : Reach 12845 := rs (se 3 (by rfl) ⟨2408, by rfl⟩) R4817
theorem R12851 : Reach 12851 := rs (se 1 (by rfl) ⟨9638, by rfl⟩) R19277
theorem R12863 : Reach 12863 := rs (se 1 (by rfl) ⟨9647, by rfl⟩) R19295
theorem R12881 : Reach 12881 := rs (se 2 (by rfl) ⟨4830, by rfl⟩) R9661
theorem R12883 : Reach 12883 := rs (se 1 (by rfl) ⟨9662, by rfl⟩) R19325
theorem R12947 : Reach 12947 := rs (se 1 (by rfl) ⟨9710, by rfl⟩) R19421
theorem R12995 : Reach 12995 := rs (se 1 (by rfl) ⟨9746, by rfl⟩) R19493
theorem R13001 : Reach 13001 := rs (se 2 (by rfl) ⟨4875, by rfl⟩) R9751
theorem R13097 : Reach 13097 := rs (se 2 (by rfl) ⟨4911, by rfl⟩) R9823
theorem R13187 : Reach 13187 := rs (se 1 (by rfl) ⟨9890, by rfl⟩) R19781
theorem R13189 : Reach 13189 := rs (se 4 (by rfl) ⟨1236, by rfl⟩) R2473
theorem R13193 : Reach 13193 := rs (se 2 (by rfl) ⟨4947, by rfl⟩) R9895
theorem R3389303 : Reach 3389303 := rs (se 1 (by rfl) ⟨2541977, by rfl⟩) R5083955
theorem R211409 : Reach 211409 := rs (se 2 (by rfl) ⟨79278, by rfl⟩) R158557
theorem R48559 : Reach 48559 := rs (se 1 (by rfl) ⟨36419, by rfl⟩) R72839
theorem R49823 : Reach 49823 := rs (se 1 (by rfl) ⟨37367, by rfl⟩) R74735
theorem R378269 : Reach 378269 := rs (se 3 (by rfl) ⟨70925, by rfl⟩) R141851
theorem R378283 : Reach 378283 := rs (se 1 (by rfl) ⟨283712, by rfl⟩) R567425
theorem R51029 : Reach 51029 := rs (se 9 (by rfl) ⟨149, by rfl⟩) R299
theorem R51121 : Reach 51121 := rs (se 2 (by rfl) ⟨19170, by rfl⟩) R38341
theorem R54265 : Reach 54265 := rs (se 2 (by rfl) ⟨20349, by rfl⟩) R40699
theorem R23543 : Reach 23543 := rs (se 1 (by rfl) ⟨17657, by rfl⟩) R35315
theorem R23579 : Reach 23579 := rs (se 1 (by rfl) ⟨17684, by rfl⟩) R35369
theorem R23633 : Reach 23633 := rs (se 2 (by rfl) ⟨8862, by rfl⟩) R17725
theorem R23807 : Reach 23807 := rs (se 1 (by rfl) ⟨17855, by rfl⟩) R35711
theorem R24173 : Reach 24173 := rs (se 3 (by rfl) ⟨4532, by rfl⟩) R9065
theorem R24259 : Reach 24259 := rs (se 1 (by rfl) ⟨18194, by rfl⟩) R36389
theorem R24401 : Reach 24401 := rs (se 2 (by rfl) ⟨9150, by rfl⟩) R18301
theorem R24467 : Reach 24467 := rs (se 1 (by rfl) ⟨18350, by rfl⟩) R36701
theorem R24479 : Reach 24479 := rs (se 1 (by rfl) ⟨18359, by rfl⟩) R36719
theorem R24563 : Reach 24563 := rs (se 1 (by rfl) ⟨18422, by rfl⟩) R36845
theorem R24803 : Reach 24803 := rs (se 1 (by rfl) ⟨18602, by rfl⟩) R37205
theorem R24877 : Reach 24877 := rs (se 3 (by rfl) ⟨4664, by rfl⟩) R9329
theorem R24911 : Reach 24911 := rs (se 1 (by rfl) ⟨18683, by rfl⟩) R37367
theorem R25073 : Reach 25073 := rs (se 2 (by rfl) ⟨9402, by rfl⟩) R18805
theorem R25181 : Reach 25181 := rs (se 3 (by rfl) ⟨4721, by rfl⟩) R9443
theorem R25541 : Reach 25541 := rs (se 4 (by rfl) ⟨2394, by rfl⟩) R4789
theorem R58583 : Reach 58583 := rs (se 1 (by rfl) ⟨43937, by rfl⟩) R87875
theorem R26009 : Reach 26009 := rs (se 2 (by rfl) ⟨9753, by rfl⟩) R19507
theorem R26027 : Reach 26027 := rs (se 1 (by rfl) ⟨19520, by rfl⟩) R39041
theorem R26381 : Reach 26381 := rs (se 3 (by rfl) ⟨4946, by rfl⟩) R9893
theorem R26387 : Reach 26387 := rs (se 1 (by rfl) ⟨19790, by rfl⟩) R39581
theorem R424187 : Reach 424187 := rs (se 1 (by rfl) ⟨318140, by rfl⟩) R636281
theorem R96707 : Reach 96707 := rs (se 1 (by rfl) ⟨72530, by rfl⟩) R145061
theorem R129 : Reach 129 := rs (se 2 (by rfl) ⟨48, by rfl⟩) R97
theorem R257 : Reach 257 := rs (se 2 (by rfl) ⟨96, by rfl⟩) R193
theorem R259 : Reach 259 := rs (se 1 (by rfl) ⟨194, by rfl⟩) R389
theorem R265 : Reach 265 := rs (se 2 (by rfl) ⟨99, by rfl⟩) R199
theorem R33169 : Reach 33169 := rs (se 2 (by rfl) ⟨12438, by rfl⟩) R24877
theorem R33215 : Reach 33215 := rs (se 1 (by rfl) ⟨24911, by rfl⟩) R49823
theorem R515 : Reach 515 := rs (se 1 (by rfl) ⟨386, by rfl⟩) R773
theorem R517 : Reach 517 := rs (se 4 (by rfl) ⟨48, by rfl⟩) R97
theorem R521 : Reach 521 := rs (se 2 (by rfl) ⟨195, by rfl⟩) R391
theorem R523 : Reach 523 := rs (se 1 (by rfl) ⟨392, by rfl⟩) R785
theorem R531 : Reach 531 := rs (se 1 (by rfl) ⟨398, by rfl⟩) R797
theorem R1029 : Reach 1029 := rs (se 4 (by rfl) ⟨96, by rfl⟩) R193
theorem R1035 : Reach 1035 := rs (se 1 (by rfl) ⟨776, by rfl⟩) R1553
theorem R1037 : Reach 1037 := rs (se 3 (by rfl) ⟨194, by rfl⟩) R389
theorem R1041 : Reach 1041 := rs (se 2 (by rfl) ⟨390, by rfl⟩) R781
theorem R1043 : Reach 1043 := rs (se 1 (by rfl) ⟨782, by rfl⟩) R1565
theorem R1047 : Reach 1047 := rs (se 1 (by rfl) ⟨785, by rfl⟩) R1571
theorem R1061 : Reach 1061 := rs (se 4 (by rfl) ⟨99, by rfl⟩) R199
theorem R34019 : Reach 34019 := rs (se 1 (by rfl) ⟨25514, by rfl⟩) R51029
theorem R34141 : Reach 34141 := rs (se 3 (by rfl) ⟨6401, by rfl⟩) R12803
theorem R34157 : Reach 34157 := rs (se 3 (by rfl) ⟨6404, by rfl⟩) R12809
theorem R34181 : Reach 34181 := rs (se 4 (by rfl) ⟨3204, by rfl⟩) R6409
theorem R34253 : Reach 34253 := rs (se 3 (by rfl) ⟨6422, by rfl⟩) R12845
theorem R132677 : Reach 132677 := rs (se 4 (by rfl) ⟨12438, by rfl⟩) R24877
theorem R2061 : Reach 2061 := rs (se 3 (by rfl) ⟨386, by rfl⟩) R773
theorem R2065 : Reach 2065 := rs (se 2 (by rfl) ⟨774, by rfl⟩) R1549
theorem R2069 : Reach 2069 := rs (se 6 (by rfl) ⟨48, by rfl⟩) R97
theorem R2071 : Reach 2071 := rs (se 1 (by rfl) ⟨1553, by rfl⟩) R3107
theorem R2083 : Reach 2083 := rs (se 1 (by rfl) ⟨1562, by rfl⟩) R3125
theorem R2085 : Reach 2085 := rs (se 4 (by rfl) ⟨195, by rfl⟩) R391
theorem R2093 : Reach 2093 := rs (se 3 (by rfl) ⟨392, by rfl⟩) R785
theorem R2105 : Reach 2105 := rs (se 2 (by rfl) ⟨789, by rfl⟩) R1579
theorem R2125 : Reach 2125 := rs (se 3 (by rfl) ⟨398, by rfl⟩) R797
theorem R2129 : Reach 2129 := rs (se 2 (by rfl) ⟨798, by rfl⟩) R1597
theorem R2159 : Reach 2159 := rs (se 1 (by rfl) ⟨1619, by rfl⟩) R3239
theorem R133649 : Reach 133649 := rs (se 2 (by rfl) ⟨50118, by rfl⟩) R100237
theorem R68161 : Reach 68161 := rs (se 2 (by rfl) ⟨25560, by rfl⟩) R51121
theorem R3937 : Reach 3937 := rs (se 2 (by rfl) ⟨1476, by rfl⟩) R2953
theorem R4065 : Reach 4065 := rs (se 2 (by rfl) ⟨1524, by rfl⟩) R3049
theorem R4091 : Reach 4091 := rs (se 1 (by rfl) ⟨3068, by rfl⟩) R6137
theorem R4117 : Reach 4117 := rs (se 6 (by rfl) ⟨96, by rfl⟩) R193
theorem R4131 : Reach 4131 := rs (se 1 (by rfl) ⟨3098, by rfl⟩) R6197
theorem R4141 : Reach 4141 := rs (se 3 (by rfl) ⟨776, by rfl⟩) R1553
theorem R4149 : Reach 4149 := rs (se 5 (by rfl) ⟨194, by rfl⟩) R389
theorem R4165 : Reach 4165 := rs (se 4 (by rfl) ⟨390, by rfl⟩) R781
theorem R4171 : Reach 4171 := rs (se 1 (by rfl) ⟨3128, by rfl⟩) R6257
theorem R4173 : Reach 4173 := rs (se 3 (by rfl) ⟨782, by rfl⟩) R1565
theorem R4177 : Reach 4177 := rs (se 2 (by rfl) ⟨1566, by rfl⟩) R3133
theorem R4189 : Reach 4189 := rs (se 3 (by rfl) ⟨785, by rfl⟩) R1571
theorem R4211 : Reach 4211 := rs (se 1 (by rfl) ⟨3158, by rfl⟩) R6317
theorem R4245 : Reach 4245 := rs (se 6 (by rfl) ⟨99, by rfl⟩) R199
theorem R4249 : Reach 4249 := rs (se 2 (by rfl) ⟨1593, by rfl⟩) R3187
theorem R4259 : Reach 4259 := rs (se 1 (by rfl) ⟨3194, by rfl⟩) R6389
theorem R4263 : Reach 4263 := rs (se 1 (by rfl) ⟨3197, by rfl⟩) R6395
theorem R4267 : Reach 4267 := rs (se 1 (by rfl) ⟨3200, by rfl⟩) R6401
theorem R4281 : Reach 4281 := rs (se 2 (by rfl) ⟨1605, by rfl⟩) R3211
theorem R4283 : Reach 4283 := rs (se 1 (by rfl) ⟨3212, by rfl⟩) R6425
theorem R4287 : Reach 4287 := rs (se 1 (by rfl) ⟨3215, by rfl⟩) R6431
theorem R4315 : Reach 4315 := rs (se 1 (by rfl) ⟨3236, by rfl⟩) R6473
theorem R4319 : Reach 4319 := rs (se 1 (by rfl) ⟨3239, by rfl⟩) R6479
theorem R4331 : Reach 4331 := rs (se 1 (by rfl) ⟨3248, by rfl⟩) R6497
theorem R4395 : Reach 4395 := rs (se 1 (by rfl) ⟨3296, by rfl⟩) R6593
theorem R39055 : Reach 39055 := rs (se 1 (by rfl) ⟨29291, by rfl⟩) R58583
theorem R72353 : Reach 72353 := rs (se 2 (by rfl) ⟨27132, by rfl⟩) R54265
theorem R7847 : Reach 7847 := rs (se 1 (by rfl) ⟨5885, by rfl⟩) R11771
theorem R7849 : Reach 7849 := rs (se 2 (by rfl) ⟨2943, by rfl⟩) R5887
theorem R7875 : Reach 7875 := rs (se 1 (by rfl) ⟨5906, by rfl⟩) R11813
theorem R7935 : Reach 7935 := rs (se 1 (by rfl) ⟨5951, by rfl⟩) R11903
theorem R7945 : Reach 7945 := rs (se 2 (by rfl) ⟨2979, by rfl⟩) R5959
theorem R8057 : Reach 8057 := rs (se 2 (by rfl) ⟨3021, by rfl⟩) R6043
theorem R8131 : Reach 8131 := rs (se 1 (by rfl) ⟨6098, by rfl⟩) R12197
theorem R8155 : Reach 8155 := rs (se 1 (by rfl) ⟨6116, by rfl⟩) R12233
theorem R8183 : Reach 8183 := rs (se 1 (by rfl) ⟨6137, by rfl⟩) R12275
theorem R8185 : Reach 8185 := rs (se 2 (by rfl) ⟨3069, by rfl⟩) R6139
theorem R8187 : Reach 8187 := rs (se 1 (by rfl) ⟨6140, by rfl⟩) R12281
theorem R8245 : Reach 8245 := rs (se 5 (by rfl) ⟨386, by rfl⟩) R773
theorem R8261 : Reach 8261 := rs (se 4 (by rfl) ⟨774, by rfl⟩) R1549
theorem R8267 : Reach 8267 := rs (se 1 (by rfl) ⟨6200, by rfl⟩) R12401
theorem R8277 : Reach 8277 := rs (se 8 (by rfl) ⟨48, by rfl⟩) R97
theorem R8285 : Reach 8285 := rs (se 3 (by rfl) ⟨1553, by rfl⟩) R3107
theorem R8303 : Reach 8303 := rs (se 1 (by rfl) ⟨6227, by rfl⟩) R12455
theorem R8305 : Reach 8305 := rs (se 2 (by rfl) ⟨3114, by rfl⟩) R6229
theorem R8333 : Reach 8333 := rs (se 3 (by rfl) ⟨1562, by rfl⟩) R3125
theorem R8341 : Reach 8341 := rs (se 6 (by rfl) ⟨195, by rfl⟩) R391
theorem R8343 : Reach 8343 := rs (se 1 (by rfl) ⟨6257, by rfl⟩) R12515
theorem R8355 : Reach 8355 := rs (se 1 (by rfl) ⟨6266, by rfl⟩) R12533
theorem R8373 : Reach 8373 := rs (se 5 (by rfl) ⟨392, by rfl⟩) R785
theorem R8393 : Reach 8393 := rs (se 2 (by rfl) ⟨3147, by rfl⟩) R6295
theorem R8421 : Reach 8421 := rs (se 4 (by rfl) ⟨789, by rfl⟩) R1579
theorem R8497 : Reach 8497 := rs (se 2 (by rfl) ⟨3186, by rfl⟩) R6373
theorem R8499 : Reach 8499 := rs (se 1 (by rfl) ⟨6374, by rfl⟩) R12749
theorem R8501 : Reach 8501 := rs (se 5 (by rfl) ⟨398, by rfl⟩) R797
theorem R8513 : Reach 8513 := rs (se 2 (by rfl) ⟨3192, by rfl⟩) R6385
theorem R8517 : Reach 8517 := rs (se 4 (by rfl) ⟨798, by rfl⟩) R1597
theorem R8523 : Reach 8523 := rs (se 1 (by rfl) ⟨6392, by rfl⟩) R12785
theorem R8527 : Reach 8527 := rs (se 1 (by rfl) ⟨6395, by rfl⟩) R12791
theorem R8535 : Reach 8535 := rs (se 1 (by rfl) ⟨6401, by rfl⟩) R12803
theorem R8539 : Reach 8539 := rs (se 1 (by rfl) ⟨6404, by rfl⟩) R12809
theorem R8545 : Reach 8545 := rs (se 2 (by rfl) ⟨3204, by rfl⟩) R6409
theorem R8563 : Reach 8563 := rs (se 1 (by rfl) ⟨6422, by rfl⟩) R12845
theorem R8567 : Reach 8567 := rs (se 1 (by rfl) ⟨6425, by rfl⟩) R12851
theorem R8575 : Reach 8575 := rs (se 1 (by rfl) ⟨6431, by rfl⟩) R12863
theorem R8587 : Reach 8587 := rs (se 1 (by rfl) ⟨6440, by rfl⟩) R12881
theorem R8631 : Reach 8631 := rs (se 1 (by rfl) ⟨6473, by rfl⟩) R12947
theorem R8637 : Reach 8637 := rs (se 3 (by rfl) ⟨1619, by rfl⟩) R3239
theorem R8663 : Reach 8663 := rs (se 1 (by rfl) ⟨6497, by rfl⟩) R12995
theorem R8667 : Reach 8667 := rs (se 1 (by rfl) ⟨6500, by rfl⟩) R13001
theorem R8731 : Reach 8731 := rs (se 1 (by rfl) ⟨6548, by rfl⟩) R13097
theorem R8791 : Reach 8791 := rs (se 1 (by rfl) ⟨6593, by rfl⟩) R13187
theorem R8793 : Reach 8793 := rs (se 2 (by rfl) ⟨3297, by rfl⟩) R6595
theorem R8795 : Reach 8795 := rs (se 1 (by rfl) ⟨6596, by rfl⟩) R13193
theorem R140939 : Reach 140939 := rs (se 1 (by rfl) ⟨105704, by rfl⟩) R211409
theorem R272645 : Reach 272645 := rs (se 4 (by rfl) ⟨25560, by rfl⟩) R51121
theorem R272857 : Reach 272857 := rs (se 2 (by rfl) ⟨102321, by rfl⟩) R204643
theorem R504377 : Reach 504377 := rs (se 2 (by rfl) ⟨189141, by rfl⟩) R378283
theorem R1062881 : Reach 1062881 := rs (se 2 (by rfl) ⟨398580, by rfl⟩) R797161
theorem R15695 : Reach 15695 := rs (se 1 (by rfl) ⟨11771, by rfl⟩) R23543
theorem R15719 : Reach 15719 := rs (se 1 (by rfl) ⟨11789, by rfl⟩) R23579
theorem R15749 : Reach 15749 := rs (se 4 (by rfl) ⟨1476, by rfl⟩) R2953
theorem R15755 : Reach 15755 := rs (se 1 (by rfl) ⟨11816, by rfl⟩) R23633
theorem R15871 : Reach 15871 := rs (se 1 (by rfl) ⟨11903, by rfl⟩) R23807
theorem R15881 : Reach 15881 := rs (se 2 (by rfl) ⟨5955, by rfl⟩) R11911
theorem R16115 : Reach 16115 := rs (se 1 (by rfl) ⟨12086, by rfl⟩) R24173
theorem R16267 : Reach 16267 := rs (se 1 (by rfl) ⟨12200, by rfl⟩) R24401
theorem R16319 : Reach 16319 := rs (se 1 (by rfl) ⟨12239, by rfl⟩) R24479
theorem R16375 : Reach 16375 := rs (se 1 (by rfl) ⟨12281, by rfl⟩) R24563
theorem R16469 : Reach 16469 := rs (se 8 (by rfl) ⟨96, by rfl⟩) R193
theorem R16535 : Reach 16535 := rs (se 1 (by rfl) ⟨12401, by rfl⟩) R24803
theorem R16565 : Reach 16565 := rs (se 5 (by rfl) ⟨776, by rfl⟩) R1553
theorem R16607 : Reach 16607 := rs (se 1 (by rfl) ⟨12455, by rfl⟩) R24911
theorem R16661 : Reach 16661 := rs (se 6 (by rfl) ⟨390, by rfl⟩) R781
theorem R16685 : Reach 16685 := rs (se 3 (by rfl) ⟨3128, by rfl⟩) R6257
theorem R16709 : Reach 16709 := rs (se 4 (by rfl) ⟨1566, by rfl⟩) R3133
theorem R16715 : Reach 16715 := rs (se 1 (by rfl) ⟨12536, by rfl⟩) R25073
theorem R16753 : Reach 16753 := rs (se 2 (by rfl) ⟨6282, by rfl⟩) R12565
theorem R16757 : Reach 16757 := rs (se 5 (by rfl) ⟨785, by rfl⟩) R1571
theorem R16787 : Reach 16787 := rs (se 1 (by rfl) ⟨12590, by rfl⟩) R25181
theorem R16997 : Reach 16997 := rs (se 4 (by rfl) ⟨1593, by rfl⟩) R3187
theorem R17009 : Reach 17009 := rs (se 2 (by rfl) ⟨6378, by rfl⟩) R12757
theorem R17027 : Reach 17027 := rs (se 1 (by rfl) ⟨12770, by rfl⟩) R25541
theorem R17069 : Reach 17069 := rs (se 3 (by rfl) ⟨3200, by rfl⟩) R6401
theorem R17177 : Reach 17177 := rs (se 2 (by rfl) ⟨6441, by rfl⟩) R12883
theorem R17261 : Reach 17261 := rs (se 3 (by rfl) ⟨3236, by rfl⟩) R6473
theorem R17339 : Reach 17339 := rs (se 1 (by rfl) ⟨13004, by rfl⟩) R26009
theorem R17351 : Reach 17351 := rs (se 1 (by rfl) ⟨13013, by rfl⟩) R26027
theorem R17585 : Reach 17585 := rs (se 2 (by rfl) ⟨6594, by rfl⟩) R13189
theorem R17587 : Reach 17587 := rs (se 1 (by rfl) ⟨13190, by rfl⟩) R26381
theorem R17591 : Reach 17591 := rs (se 1 (by rfl) ⟨13193, by rfl⟩) R26387
theorem R282791 : Reach 282791 := rs (se 1 (by rfl) ⟨212093, by rfl⟩) R424187
theorem R252179 : Reach 252179 := rs (se 1 (by rfl) ⟨189134, by rfl⟩) R378269
theorem R9038141 : Reach 9038141 := rs (se 3 (by rfl) ⟨1694651, by rfl⟩) R3389303
theorem R64471 : Reach 64471 := rs (se 1 (by rfl) ⟨48353, by rfl⟩) R96707
theorem R64745 : Reach 64745 := rs (se 2 (by rfl) ⟨24279, by rfl⟩) R48559
theorem R32345 : Reach 32345 := rs (se 2 (by rfl) ⟨12129, by rfl⟩) R24259
theorem R65245 : Reach 65245 := rs (se 3 (by rfl) ⟨12233, by rfl⟩) R24467
theorem R32525 : Reach 32525 := rs (se 3 (by rfl) ⟨6098, by rfl⟩) R12197
theorem R171 : Reach 171 := rs (se 1 (by rfl) ⟨128, by rfl⟩) R257
theorem R343 : Reach 343 := rs (se 1 (by rfl) ⟨257, by rfl⟩) R515
theorem R345 : Reach 345 := rs (se 2 (by rfl) ⟨129, by rfl⟩) R259
theorem R347 : Reach 347 := rs (se 1 (by rfl) ⟨260, by rfl⟩) R521
theorem R353 : Reach 353 := rs (se 2 (by rfl) ⟨132, by rfl⟩) R265
theorem R685 : Reach 685 := rs (se 3 (by rfl) ⟨128, by rfl⟩) R257
theorem R689 : Reach 689 := rs (se 2 (by rfl) ⟨258, by rfl⟩) R517
theorem R691 : Reach 691 := rs (se 1 (by rfl) ⟨518, by rfl⟩) R1037
theorem R695 : Reach 695 := rs (se 1 (by rfl) ⟨521, by rfl⟩) R1043
theorem R697 : Reach 697 := rs (se 2 (by rfl) ⟨261, by rfl⟩) R523
theorem R707 : Reach 707 := rs (se 1 (by rfl) ⟨530, by rfl⟩) R1061
theorem R1373 : Reach 1373 := rs (se 3 (by rfl) ⟨257, by rfl⟩) R515
theorem R1379 : Reach 1379 := rs (se 1 (by rfl) ⟨1034, by rfl⟩) R2069
theorem R1381 : Reach 1381 := rs (se 4 (by rfl) ⟨129, by rfl⟩) R259
theorem R1389 : Reach 1389 := rs (se 3 (by rfl) ⟨260, by rfl⟩) R521
theorem R1395 : Reach 1395 := rs (se 1 (by rfl) ⟨1046, by rfl⟩) R2093
theorem R1403 : Reach 1403 := rs (se 1 (by rfl) ⟨1052, by rfl⟩) R2105
theorem R1413 : Reach 1413 := rs (se 4 (by rfl) ⟨132, by rfl⟩) R265
theorem R1419 : Reach 1419 := rs (se 1 (by rfl) ⟨1064, by rfl⟩) R2129
theorem R1439 : Reach 1439 := rs (se 1 (by rfl) ⟨1079, by rfl⟩) R2159
theorem R2727 : Reach 2727 := rs (se 1 (by rfl) ⟨2045, by rfl⟩) R4091
theorem R2741 : Reach 2741 := rs (se 5 (by rfl) ⟨128, by rfl⟩) R257
theorem R2753 : Reach 2753 := rs (se 2 (by rfl) ⟨1032, by rfl⟩) R2065
theorem R2757 : Reach 2757 := rs (se 4 (by rfl) ⟨258, by rfl⟩) R517
theorem R2761 : Reach 2761 := rs (se 2 (by rfl) ⟨1035, by rfl⟩) R2071
theorem R2765 : Reach 2765 := rs (se 3 (by rfl) ⟨518, by rfl⟩) R1037
theorem R2777 : Reach 2777 := rs (se 2 (by rfl) ⟨1041, by rfl⟩) R2083
theorem R2781 : Reach 2781 := rs (se 3 (by rfl) ⟨521, by rfl⟩) R1043
theorem R2789 : Reach 2789 := rs (se 4 (by rfl) ⟨261, by rfl⟩) R523
theorem R2807 : Reach 2807 := rs (se 1 (by rfl) ⟨2105, by rfl⟩) R4211
theorem R2829 : Reach 2829 := rs (se 3 (by rfl) ⟨530, by rfl⟩) R1061
theorem R2833 : Reach 2833 := rs (se 2 (by rfl) ⟨1062, by rfl⟩) R2125
theorem R2839 : Reach 2839 := rs (se 1 (by rfl) ⟨2129, by rfl⟩) R4259
theorem R2855 : Reach 2855 := rs (se 1 (by rfl) ⟨2141, by rfl⟩) R4283
theorem R2879 : Reach 2879 := rs (se 1 (by rfl) ⟨2159, by rfl⟩) R4319
theorem R2887 : Reach 2887 := rs (se 1 (by rfl) ⟨2165, by rfl⟩) R4331
theorem R363809 : Reach 363809 := rs (se 2 (by rfl) ⟨136428, by rfl⟩) R272857
theorem R168119 : Reach 168119 := rs (se 1 (by rfl) ⟨126089, by rfl⟩) R252179
theorem R5231 : Reach 5231 := rs (se 1 (by rfl) ⟨3923, by rfl⟩) R7847
theorem R5249 : Reach 5249 := rs (se 2 (by rfl) ⟨1968, by rfl⟩) R3937
theorem R5371 : Reach 5371 := rs (se 1 (by rfl) ⟨4028, by rfl⟩) R8057
theorem R5455 : Reach 5455 := rs (se 1 (by rfl) ⟨4091, by rfl⟩) R8183
theorem R5489 : Reach 5489 := rs (se 2 (by rfl) ⟨2058, by rfl⟩) R4117
theorem R5493 : Reach 5493 := rs (se 5 (by rfl) ⟨257, by rfl⟩) R515
theorem R5507 : Reach 5507 := rs (se 1 (by rfl) ⟨4130, by rfl⟩) R8261
theorem R5511 : Reach 5511 := rs (se 1 (by rfl) ⟨4133, by rfl⟩) R8267
theorem R5517 : Reach 5517 := rs (se 3 (by rfl) ⟨1034, by rfl⟩) R2069
theorem R5521 : Reach 5521 := rs (se 2 (by rfl) ⟨2070, by rfl⟩) R4141
theorem R5523 : Reach 5523 := rs (se 1 (by rfl) ⟨4142, by rfl⟩) R8285
theorem R5525 : Reach 5525 := rs (se 6 (by rfl) ⟨129, by rfl⟩) R259
theorem R5535 : Reach 5535 := rs (se 1 (by rfl) ⟨4151, by rfl⟩) R8303
theorem R5553 : Reach 5553 := rs (se 2 (by rfl) ⟨2082, by rfl⟩) R4165
theorem R5555 : Reach 5555 := rs (se 1 (by rfl) ⟨4166, by rfl⟩) R8333
theorem R5557 : Reach 5557 := rs (se 5 (by rfl) ⟨260, by rfl⟩) R521
theorem R5561 : Reach 5561 := rs (se 2 (by rfl) ⟨2085, by rfl⟩) R4171
theorem R5569 : Reach 5569 := rs (se 2 (by rfl) ⟨2088, by rfl⟩) R4177
theorem R5581 : Reach 5581 := rs (se 3 (by rfl) ⟨1046, by rfl⟩) R2093
theorem R5585 : Reach 5585 := rs (se 2 (by rfl) ⟨2094, by rfl⟩) R4189
theorem R5595 : Reach 5595 := rs (se 1 (by rfl) ⟨4196, by rfl⟩) R8393
theorem R5613 : Reach 5613 := rs (se 3 (by rfl) ⟨1052, by rfl⟩) R2105
theorem R5653 : Reach 5653 := rs (se 6 (by rfl) ⟨132, by rfl⟩) R265
theorem R5665 : Reach 5665 := rs (se 2 (by rfl) ⟨2124, by rfl⟩) R4249
theorem R5667 : Reach 5667 := rs (se 1 (by rfl) ⟨4250, by rfl⟩) R8501
theorem R5675 : Reach 5675 := rs (se 1 (by rfl) ⟨4256, by rfl⟩) R8513
theorem R5677 : Reach 5677 := rs (se 3 (by rfl) ⟨1064, by rfl⟩) R2129
theorem R5689 : Reach 5689 := rs (se 2 (by rfl) ⟨2133, by rfl⟩) R4267
theorem R5711 : Reach 5711 := rs (se 1 (by rfl) ⟨4283, by rfl⟩) R8567
theorem R5753 : Reach 5753 := rs (se 2 (by rfl) ⟨2157, by rfl⟩) R4315
theorem R5757 : Reach 5757 := rs (se 3 (by rfl) ⟨1079, by rfl⟩) R2159
theorem R5775 : Reach 5775 := rs (se 1 (by rfl) ⟨4331, by rfl⟩) R8663
theorem R5863 : Reach 5863 := rs (se 1 (by rfl) ⟨4397, by rfl⟩) R8795
theorem R336251 : Reach 336251 := rs (se 1 (by rfl) ⟨252188, by rfl⟩) R504377
theorem R41917 : Reach 41917 := rs (se 3 (by rfl) ⟨7859, by rfl⟩) R15719
theorem R42373 : Reach 42373 := rs (se 4 (by rfl) ⟨3972, by rfl⟩) R7945
theorem R43163 : Reach 43163 := rs (se 1 (by rfl) ⟨32372, by rfl⟩) R64745
theorem R10463 : Reach 10463 := rs (se 1 (by rfl) ⟨7847, by rfl⟩) R15695
theorem R10465 : Reach 10465 := rs (se 2 (by rfl) ⟨3924, by rfl⟩) R7849
theorem R10479 : Reach 10479 := rs (se 1 (by rfl) ⟨7859, by rfl⟩) R15719
theorem R10499 : Reach 10499 := rs (se 1 (by rfl) ⟨7874, by rfl⟩) R15749
theorem R10503 : Reach 10503 := rs (se 1 (by rfl) ⟨7877, by rfl⟩) R15755
theorem R10587 : Reach 10587 := rs (se 1 (by rfl) ⟨7940, by rfl⟩) R15881
theorem R10593 : Reach 10593 := rs (se 2 (by rfl) ⟨3972, by rfl⟩) R7945
theorem R10743 : Reach 10743 := rs (se 1 (by rfl) ⟨8057, by rfl⟩) R16115
theorem R10841 : Reach 10841 := rs (se 2 (by rfl) ⟨4065, by rfl⟩) R8131
theorem R10873 : Reach 10873 := rs (se 2 (by rfl) ⟨4077, by rfl⟩) R8155
theorem R10879 : Reach 10879 := rs (se 1 (by rfl) ⟨8159, by rfl⟩) R16319
theorem R10909 : Reach 10909 := rs (se 3 (by rfl) ⟨2045, by rfl⟩) R4091
theorem R10913 : Reach 10913 := rs (se 2 (by rfl) ⟨4092, by rfl⟩) R8185
theorem R10965 : Reach 10965 := rs (se 7 (by rfl) ⟨128, by rfl⟩) R257
theorem R10979 : Reach 10979 := rs (se 1 (by rfl) ⟨8234, by rfl⟩) R16469
theorem R10993 : Reach 10993 := rs (se 2 (by rfl) ⟨4122, by rfl⟩) R8245
theorem R11013 : Reach 11013 := rs (se 4 (by rfl) ⟨1032, by rfl⟩) R2065
theorem R11023 : Reach 11023 := rs (se 1 (by rfl) ⟨8267, by rfl⟩) R16535
theorem R11029 : Reach 11029 := rs (se 6 (by rfl) ⟨258, by rfl⟩) R517
theorem R11043 : Reach 11043 := rs (se 1 (by rfl) ⟨8282, by rfl⟩) R16565
theorem R11045 : Reach 11045 := rs (se 4 (by rfl) ⟨1035, by rfl⟩) R2071
theorem R11061 : Reach 11061 := rs (se 5 (by rfl) ⟨518, by rfl⟩) R1037
theorem R11071 : Reach 11071 := rs (se 1 (by rfl) ⟨8303, by rfl⟩) R16607
theorem R11073 : Reach 11073 := rs (se 2 (by rfl) ⟨4152, by rfl⟩) R8305
theorem R43861 : Reach 43861 := rs (se 9 (by rfl) ⟨128, by rfl⟩) R257
theorem R11107 : Reach 11107 := rs (se 1 (by rfl) ⟨8330, by rfl⟩) R16661
theorem R11109 : Reach 11109 := rs (se 4 (by rfl) ⟨1041, by rfl⟩) R2083
theorem R11121 : Reach 11121 := rs (se 2 (by rfl) ⟨4170, by rfl⟩) R8341
theorem R11123 : Reach 11123 := rs (se 1 (by rfl) ⟨8342, by rfl⟩) R16685
theorem R11125 : Reach 11125 := rs (se 5 (by rfl) ⟨521, by rfl⟩) R1043
theorem R11139 : Reach 11139 := rs (se 1 (by rfl) ⟨8354, by rfl⟩) R16709
theorem R11143 : Reach 11143 := rs (se 1 (by rfl) ⟨8357, by rfl⟩) R16715
theorem R11157 : Reach 11157 := rs (se 6 (by rfl) ⟨261, by rfl⟩) R523
theorem R11171 : Reach 11171 := rs (se 1 (by rfl) ⟨8378, by rfl⟩) R16757
theorem R11191 : Reach 11191 := rs (se 1 (by rfl) ⟨8393, by rfl⟩) R16787
theorem R43973 : Reach 43973 := rs (se 4 (by rfl) ⟨4122, by rfl⟩) R8245
theorem R11229 : Reach 11229 := rs (se 3 (by rfl) ⟨2105, by rfl⟩) R4211
theorem R11317 : Reach 11317 := rs (se 5 (by rfl) ⟨530, by rfl⟩) R1061
theorem R11329 : Reach 11329 := rs (se 2 (by rfl) ⟨4248, by rfl⟩) R8497
theorem R11331 : Reach 11331 := rs (se 1 (by rfl) ⟨8498, by rfl⟩) R16997
theorem R11333 : Reach 11333 := rs (se 4 (by rfl) ⟨1062, by rfl⟩) R2125
theorem R11339 : Reach 11339 := rs (se 1 (by rfl) ⟨8504, by rfl⟩) R17009
theorem R11351 : Reach 11351 := rs (se 1 (by rfl) ⟨8513, by rfl⟩) R17027
theorem R11357 : Reach 11357 := rs (se 3 (by rfl) ⟨2129, by rfl⟩) R4259
theorem R11369 : Reach 11369 := rs (se 2 (by rfl) ⟨4263, by rfl⟩) R8527
theorem R11379 : Reach 11379 := rs (se 1 (by rfl) ⟨8534, by rfl⟩) R17069
theorem R11385 : Reach 11385 := rs (se 2 (by rfl) ⟨4269, by rfl⟩) R8539
theorem R11393 : Reach 11393 := rs (se 2 (by rfl) ⟨4272, by rfl⟩) R8545
theorem R11417 : Reach 11417 := rs (se 2 (by rfl) ⟨4281, by rfl⟩) R8563
theorem R11421 : Reach 11421 := rs (se 3 (by rfl) ⟨2141, by rfl⟩) R4283
theorem R11433 : Reach 11433 := rs (se 2 (by rfl) ⟨4287, by rfl⟩) R8575
theorem R11449 : Reach 11449 := rs (se 2 (by rfl) ⟨4293, by rfl⟩) R8587
theorem R11451 : Reach 11451 := rs (se 1 (by rfl) ⟨8588, by rfl⟩) R17177
theorem R44225 : Reach 44225 := rs (se 2 (by rfl) ⟨16584, by rfl⟩) R33169
theorem R11507 : Reach 11507 := rs (se 1 (by rfl) ⟨8630, by rfl⟩) R17261
theorem R11517 : Reach 11517 := rs (se 3 (by rfl) ⟨2159, by rfl⟩) R4319
theorem R11549 : Reach 11549 := rs (se 3 (by rfl) ⟨2165, by rfl⟩) R4331
theorem R11559 : Reach 11559 := rs (se 1 (by rfl) ⟨8669, by rfl⟩) R17339
theorem R11567 : Reach 11567 := rs (se 1 (by rfl) ⟨8675, by rfl⟩) R17351
theorem R11641 : Reach 11641 := rs (se 2 (by rfl) ⟨4365, by rfl⟩) R8731
theorem R11721 : Reach 11721 := rs (se 2 (by rfl) ⟨4395, by rfl⟩) R8791
theorem R11723 : Reach 11723 := rs (se 1 (by rfl) ⟨8792, by rfl⟩) R17585
theorem R11727 : Reach 11727 := rs (se 1 (by rfl) ⟨8795, by rfl⟩) R17591
theorem R45517 : Reach 45517 := rs (se 3 (by rfl) ⟨8534, by rfl⟩) R17069
theorem R45521 : Reach 45521 := rs (se 2 (by rfl) ⟨17070, by rfl⟩) R34141
theorem R45805 : Reach 45805 := rs (se 3 (by rfl) ⟨8588, by rfl⟩) R17177
theorem R46565 : Reach 46565 := rs (se 4 (by rfl) ⟨4365, by rfl⟩) R8731
theorem R48235 : Reach 48235 := rs (se 1 (by rfl) ⟨36176, by rfl⟩) R72353
theorem R181763 : Reach 181763 := rs (se 1 (by rfl) ⟨136322, by rfl⟩) R272645
theorem R52073 : Reach 52073 := rs (se 2 (by rfl) ⟨19527, by rfl⟩) R39055
theorem R85961 : Reach 85961 := rs (se 2 (by rfl) ⟨32235, by rfl⟩) R64471
theorem R708587 : Reach 708587 := rs (se 1 (by rfl) ⟨531440, by rfl⟩) R1062881
theorem R21161 : Reach 21161 := rs (se 2 (by rfl) ⟨7935, by rfl⟩) R15871
theorem R86993 : Reach 86993 := rs (se 2 (by rfl) ⟨32622, by rfl⟩) R65245
theorem R21485 : Reach 21485 := rs (se 3 (by rfl) ⟨4028, by rfl⟩) R8057
theorem R21563 : Reach 21563 := rs (se 1 (by rfl) ⟨16172, by rfl⟩) R32345
theorem R21683 : Reach 21683 := rs (se 1 (by rfl) ⟨16262, by rfl⟩) R32525
theorem R21689 : Reach 21689 := rs (se 2 (by rfl) ⟨8133, by rfl⟩) R16267
theorem R21833 : Reach 21833 := rs (se 2 (by rfl) ⟨8187, by rfl⟩) R16375
theorem R21973 : Reach 21973 := rs (se 7 (by rfl) ⟨257, by rfl⟩) R515
theorem R22045 : Reach 22045 := rs (se 3 (by rfl) ⟨4133, by rfl⟩) R8267
theorem R22085 : Reach 22085 := rs (se 4 (by rfl) ⟨2070, by rfl⟩) R4141
theorem R22229 : Reach 22229 := rs (se 7 (by rfl) ⟨260, by rfl⟩) R521
theorem R22337 : Reach 22337 := rs (se 2 (by rfl) ⟨8376, by rfl⟩) R16753
theorem R22661 : Reach 22661 := rs (se 4 (by rfl) ⟨2124, by rfl⟩) R4249
theorem R22679 : Reach 22679 := rs (se 1 (by rfl) ⟨17009, by rfl⟩) R34019
theorem R22771 : Reach 22771 := rs (se 1 (by rfl) ⟨17078, by rfl⟩) R34157
theorem R22787 : Reach 22787 := rs (se 1 (by rfl) ⟨17090, by rfl⟩) R34181
theorem R22835 : Reach 22835 := rs (se 1 (by rfl) ⟨17126, by rfl⟩) R34253
theorem R88451 : Reach 88451 := rs (se 1 (by rfl) ⟨66338, by rfl⟩) R132677
theorem R88573 : Reach 88573 := rs (se 3 (by rfl) ⟨16607, by rfl⟩) R33215
theorem R23449 : Reach 23449 := rs (se 2 (by rfl) ⟨8793, by rfl⟩) R17587
theorem R23453 : Reach 23453 := rs (se 3 (by rfl) ⟨4397, by rfl⟩) R8795
theorem R89099 : Reach 89099 := rs (se 1 (by rfl) ⟨66824, by rfl⟩) R133649
theorem R188527 : Reach 188527 := rs (se 1 (by rfl) ⟨141395, by rfl⟩) R282791
theorem R90881 : Reach 90881 := rs (se 2 (by rfl) ⟨34080, by rfl⟩) R68161
theorem R354293 : Reach 354293 := rs (se 5 (by rfl) ⟨16607, by rfl⟩) R33215
theorem R93797 : Reach 93797 := rs (se 4 (by rfl) ⟨8793, by rfl⟩) R17587
theorem R93959 : Reach 93959 := rs (se 1 (by rfl) ⟨70469, by rfl⟩) R140939
theorem R6025427 : Reach 6025427 := rs (se 1 (by rfl) ⟨4519070, by rfl⟩) R9038141
theorem R231 : Reach 231 := rs (se 1 (by rfl) ⟨173, by rfl⟩) R347
theorem R235 : Reach 235 := rs (se 1 (by rfl) ⟨176, by rfl⟩) R353
theorem R457 : Reach 457 := rs (se 2 (by rfl) ⟨171, by rfl⟩) R343
theorem R459 : Reach 459 := rs (se 1 (by rfl) ⟨344, by rfl⟩) R689
theorem R463 : Reach 463 := rs (se 1 (by rfl) ⟨347, by rfl⟩) R695
theorem R471 : Reach 471 := rs (se 1 (by rfl) ⟨353, by rfl⟩) R707
theorem R913 : Reach 913 := rs (se 2 (by rfl) ⟨342, by rfl⟩) R685
theorem R915 : Reach 915 := rs (se 1 (by rfl) ⟨686, by rfl⟩) R1373
theorem R919 : Reach 919 := rs (se 1 (by rfl) ⟨689, by rfl⟩) R1379
theorem R921 : Reach 921 := rs (se 2 (by rfl) ⟨345, by rfl⟩) R691
theorem R925 : Reach 925 := rs (se 3 (by rfl) ⟨173, by rfl⟩) R347
theorem R929 : Reach 929 := rs (se 2 (by rfl) ⟨348, by rfl⟩) R697
theorem R935 : Reach 935 := rs (se 1 (by rfl) ⟨701, by rfl⟩) R1403
theorem R941 : Reach 941 := rs (se 3 (by rfl) ⟨176, by rfl⟩) R353
theorem R959 : Reach 959 := rs (se 1 (by rfl) ⟨719, by rfl⟩) R1439
theorem R1827 : Reach 1827 := rs (se 1 (by rfl) ⟨1370, by rfl⟩) R2741
theorem R1829 : Reach 1829 := rs (se 4 (by rfl) ⟨171, by rfl⟩) R343
theorem R1835 : Reach 1835 := rs (se 1 (by rfl) ⟨1376, by rfl⟩) R2753
theorem R1837 : Reach 1837 := rs (se 3 (by rfl) ⟨344, by rfl⟩) R689
theorem R1841 : Reach 1841 := rs (se 2 (by rfl) ⟨690, by rfl⟩) R1381
theorem R1843 : Reach 1843 := rs (se 1 (by rfl) ⟨1382, by rfl⟩) R2765
theorem R1851 : Reach 1851 := rs (se 1 (by rfl) ⟨1388, by rfl⟩) R2777
theorem R1853 : Reach 1853 := rs (se 3 (by rfl) ⟨347, by rfl⟩) R695
theorem R1859 : Reach 1859 := rs (se 1 (by rfl) ⟨1394, by rfl⟩) R2789
theorem R1871 : Reach 1871 := rs (se 1 (by rfl) ⟨1403, by rfl⟩) R2807
theorem R1885 : Reach 1885 := rs (se 3 (by rfl) ⟨353, by rfl⟩) R707
theorem R1903 : Reach 1903 := rs (se 1 (by rfl) ⟨1427, by rfl⟩) R2855
theorem R1919 : Reach 1919 := rs (se 1 (by rfl) ⟨1439, by rfl⟩) R2879
theorem R34715 : Reach 34715 := rs (se 1 (by rfl) ⟨26036, by rfl⟩) R52073
theorem R3487 : Reach 3487 := rs (se 1 (by rfl) ⟨2615, by rfl⟩) R5231
theorem R3499 : Reach 3499 := rs (se 1 (by rfl) ⟨2624, by rfl⟩) R5249
theorem R3653 : Reach 3653 := rs (se 4 (by rfl) ⟨342, by rfl⟩) R685
theorem R3659 : Reach 3659 := rs (se 1 (by rfl) ⟨2744, by rfl⟩) R5489
theorem R3661 : Reach 3661 := rs (se 3 (by rfl) ⟨686, by rfl⟩) R1373
theorem R3671 : Reach 3671 := rs (se 1 (by rfl) ⟨2753, by rfl⟩) R5507
theorem R3677 : Reach 3677 := rs (se 3 (by rfl) ⟨689, by rfl⟩) R1379
theorem R3681 : Reach 3681 := rs (se 2 (by rfl) ⟨1380, by rfl⟩) R2761
theorem R3683 : Reach 3683 := rs (se 1 (by rfl) ⟨2762, by rfl⟩) R5525
theorem R3685 : Reach 3685 := rs (se 4 (by rfl) ⟨345, by rfl⟩) R691
theorem R3701 : Reach 3701 := rs (se 5 (by rfl) ⟨173, by rfl⟩) R347
theorem R3703 : Reach 3703 := rs (se 1 (by rfl) ⟨2777, by rfl⟩) R5555
theorem R3707 : Reach 3707 := rs (se 1 (by rfl) ⟨2780, by rfl⟩) R5561
theorem R3717 : Reach 3717 := rs (se 4 (by rfl) ⟨348, by rfl⟩) R697
theorem R3723 : Reach 3723 := rs (se 1 (by rfl) ⟨2792, by rfl⟩) R5585
theorem R3741 : Reach 3741 := rs (se 3 (by rfl) ⟨701, by rfl⟩) R1403
theorem R3765 : Reach 3765 := rs (se 5 (by rfl) ⟨176, by rfl⟩) R353
theorem R3777 : Reach 3777 := rs (se 2 (by rfl) ⟨1416, by rfl⟩) R2833
theorem R3783 : Reach 3783 := rs (se 1 (by rfl) ⟨2837, by rfl⟩) R5675
theorem R3785 : Reach 3785 := rs (se 2 (by rfl) ⟨1419, by rfl⟩) R2839
theorem R3807 : Reach 3807 := rs (se 1 (by rfl) ⟨2855, by rfl⟩) R5711
theorem R3835 : Reach 3835 := rs (se 1 (by rfl) ⟨2876, by rfl⟩) R5753
theorem R3837 : Reach 3837 := rs (se 3 (by rfl) ⟨719, by rfl⟩) R1439
theorem R3849 : Reach 3849 := rs (se 2 (by rfl) ⟨1443, by rfl⟩) R2887
theorem R236195 : Reach 236195 := rs (se 1 (by rfl) ⟨177146, by rfl⟩) R354293
theorem R6975 : Reach 6975 := rs (se 1 (by rfl) ⟨5231, by rfl⟩) R10463
theorem R6999 : Reach 6999 := rs (se 1 (by rfl) ⟨5249, by rfl⟩) R10499
theorem R7161 : Reach 7161 := rs (se 2 (by rfl) ⟨2685, by rfl⟩) R5371
theorem R7227 : Reach 7227 := rs (se 1 (by rfl) ⟨5420, by rfl⟩) R10841
theorem R7273 : Reach 7273 := rs (se 2 (by rfl) ⟨2727, by rfl⟩) R5455
theorem R7275 : Reach 7275 := rs (se 1 (by rfl) ⟨5456, by rfl⟩) R10913
theorem R7309 : Reach 7309 := rs (se 3 (by rfl) ⟨1370, by rfl⟩) R2741
theorem R7317 : Reach 7317 := rs (se 6 (by rfl) ⟨171, by rfl⟩) R343
theorem R7319 : Reach 7319 := rs (se 1 (by rfl) ⟨5489, by rfl⟩) R10979
theorem R7341 : Reach 7341 := rs (se 3 (by rfl) ⟨1376, by rfl⟩) R2753
theorem R7349 : Reach 7349 := rs (se 5 (by rfl) ⟨344, by rfl⟩) R689
theorem R7361 : Reach 7361 := rs (se 2 (by rfl) ⟨2760, by rfl⟩) R5521
theorem R7363 : Reach 7363 := rs (se 1 (by rfl) ⟨5522, by rfl⟩) R11045
theorem R7365 : Reach 7365 := rs (se 4 (by rfl) ⟨690, by rfl⟩) R1381
theorem R7373 : Reach 7373 := rs (se 3 (by rfl) ⟨1382, by rfl⟩) R2765
theorem R7405 : Reach 7405 := rs (se 3 (by rfl) ⟨1388, by rfl⟩) R2777
theorem R7409 : Reach 7409 := rs (se 2 (by rfl) ⟨2778, by rfl⟩) R5557
theorem R7413 : Reach 7413 := rs (se 5 (by rfl) ⟨347, by rfl⟩) R695
theorem R7415 : Reach 7415 := rs (se 1 (by rfl) ⟨5561, by rfl⟩) R11123
theorem R7425 : Reach 7425 := rs (se 2 (by rfl) ⟨2784, by rfl⟩) R5569
theorem R7437 : Reach 7437 := rs (se 3 (by rfl) ⟨1394, by rfl⟩) R2789
theorem R7441 : Reach 7441 := rs (se 2 (by rfl) ⟨2790, by rfl⟩) R5581
theorem R7447 : Reach 7447 := rs (se 1 (by rfl) ⟨5585, by rfl⟩) R11171
theorem R7485 : Reach 7485 := rs (se 3 (by rfl) ⟨1403, by rfl⟩) R2807
theorem R7537 : Reach 7537 := rs (se 2 (by rfl) ⟨2826, by rfl⟩) R5653
theorem R7541 : Reach 7541 := rs (se 5 (by rfl) ⟨353, by rfl⟩) R707
theorem R7553 : Reach 7553 := rs (se 2 (by rfl) ⟨2832, by rfl⟩) R5665
theorem R7555 : Reach 7555 := rs (se 1 (by rfl) ⟨5666, by rfl⟩) R11333
theorem R7559 : Reach 7559 := rs (se 1 (by rfl) ⟨5669, by rfl⟩) R11339
theorem R7567 : Reach 7567 := rs (se 1 (by rfl) ⟨5675, by rfl⟩) R11351
theorem R7569 : Reach 7569 := rs (se 2 (by rfl) ⟨2838, by rfl⟩) R5677
theorem R7571 : Reach 7571 := rs (se 1 (by rfl) ⟨5678, by rfl⟩) R11357
theorem R7579 : Reach 7579 := rs (se 1 (by rfl) ⟨5684, by rfl⟩) R11369
theorem R7585 : Reach 7585 := rs (se 2 (by rfl) ⟨2844, by rfl⟩) R5689
theorem R7595 : Reach 7595 := rs (se 1 (by rfl) ⟨5696, by rfl⟩) R11393
theorem R7611 : Reach 7611 := rs (se 1 (by rfl) ⟨5708, by rfl⟩) R11417
theorem R7613 : Reach 7613 := rs (se 3 (by rfl) ⟨1427, by rfl⟩) R2855
theorem R7671 : Reach 7671 := rs (se 1 (by rfl) ⟨5753, by rfl⟩) R11507
theorem R7677 : Reach 7677 := rs (se 3 (by rfl) ⟨1439, by rfl⟩) R2879
theorem R7699 : Reach 7699 := rs (se 1 (by rfl) ⟨5774, by rfl⟩) R11549
theorem R7711 : Reach 7711 := rs (se 1 (by rfl) ⟨5783, by rfl⟩) R11567
theorem R7815 : Reach 7815 := rs (se 1 (by rfl) ⟨5861, by rfl⟩) R11723
theorem R7817 : Reach 7817 := rs (se 2 (by rfl) ⟨2931, by rfl⟩) R5863
theorem R472391 : Reach 472391 := rs (se 1 (by rfl) ⟨354293, by rfl⟩) R708587
theorem R112079 : Reach 112079 := rs (se 1 (by rfl) ⟨84059, by rfl⟩) R168119
theorem R13949 : Reach 13949 := rs (se 3 (by rfl) ⟨2615, by rfl⟩) R5231
theorem R13997 : Reach 13997 := rs (se 3 (by rfl) ⟨2624, by rfl⟩) R5249
theorem R14107 : Reach 14107 := rs (se 1 (by rfl) ⟨10580, by rfl⟩) R21161
theorem R14323 : Reach 14323 := rs (se 1 (by rfl) ⟨10742, by rfl⟩) R21485
theorem R14375 : Reach 14375 := rs (se 1 (by rfl) ⟨10781, by rfl⟩) R21563
theorem R14455 : Reach 14455 := rs (se 1 (by rfl) ⟨10841, by rfl⟩) R21683
theorem R14459 : Reach 14459 := rs (se 1 (by rfl) ⟨10844, by rfl⟩) R21689
theorem R14555 : Reach 14555 := rs (se 1 (by rfl) ⟨10916, by rfl⟩) R21833
theorem R14645 : Reach 14645 := rs (se 5 (by rfl) ⟨686, by rfl⟩) R1373
theorem R14657 : Reach 14657 := rs (se 2 (by rfl) ⟨5496, by rfl⟩) R10993
theorem R14705 : Reach 14705 := rs (se 2 (by rfl) ⟨5514, by rfl⟩) R11029
theorem R14723 : Reach 14723 := rs (se 1 (by rfl) ⟨11042, by rfl⟩) R22085
theorem R14741 : Reach 14741 := rs (se 6 (by rfl) ⟨345, by rfl⟩) R691
theorem R14809 : Reach 14809 := rs (se 2 (by rfl) ⟨5553, by rfl⟩) R11107
theorem R14813 : Reach 14813 := rs (se 3 (by rfl) ⟨2777, by rfl⟩) R5555
theorem R14819 : Reach 14819 := rs (se 1 (by rfl) ⟨11114, by rfl⟩) R22229
theorem R14833 : Reach 14833 := rs (se 2 (by rfl) ⟨5562, by rfl⟩) R11125
theorem R14891 : Reach 14891 := rs (se 1 (by rfl) ⟨11168, by rfl⟩) R22337
theorem R14921 : Reach 14921 := rs (se 2 (by rfl) ⟨5595, by rfl⟩) R11191
theorem R15061 : Reach 15061 := rs (se 7 (by rfl) ⟨176, by rfl⟩) R353
theorem R15089 : Reach 15089 := rs (se 2 (by rfl) ⟨5658, by rfl⟩) R11317
theorem R15107 : Reach 15107 := rs (se 1 (by rfl) ⟨11330, by rfl⟩) R22661
theorem R15119 : Reach 15119 := rs (se 1 (by rfl) ⟨11339, by rfl⟩) R22679
theorem R15133 : Reach 15133 := rs (se 3 (by rfl) ⟨2837, by rfl⟩) R5675
theorem R15191 : Reach 15191 := rs (se 1 (by rfl) ⟨11393, by rfl⟩) R22787
theorem R15223 : Reach 15223 := rs (se 1 (by rfl) ⟨11417, by rfl⟩) R22835
theorem R15341 : Reach 15341 := rs (se 3 (by rfl) ⟨2876, by rfl⟩) R5753
theorem R15349 : Reach 15349 := rs (se 5 (by rfl) ⟨719, by rfl⟩) R1439
theorem R15521 : Reach 15521 := rs (se 2 (by rfl) ⟨5820, by rfl⟩) R11641
theorem R15635 : Reach 15635 := rs (se 1 (by rfl) ⟨11726, by rfl⟩) R23453
theorem R4016951 : Reach 4016951 := rs (se 1 (by rfl) ⟨3012713, by rfl⟩) R6025427
theorem R118097 : Reach 118097 := rs (se 2 (by rfl) ⟨44286, by rfl⟩) R88573
theorem R970157 : Reach 970157 := rs (se 3 (by rfl) ⟨181904, by rfl⟩) R363809
theorem R251369 : Reach 251369 := rs (se 2 (by rfl) ⟨94263, by rfl⟩) R188527
theorem R121175 : Reach 121175 := rs (se 1 (by rfl) ⟨90881, by rfl⟩) R181763
theorem R55889 : Reach 55889 := rs (se 2 (by rfl) ⟨20958, by rfl⟩) R41917
theorem R121445 : Reach 121445 := rs (se 4 (by rfl) ⟨11385, by rfl⟩) R22771
theorem R56497 : Reach 56497 := rs (se 2 (by rfl) ⟨21186, by rfl⟩) R42373
theorem R57307 : Reach 57307 := rs (se 1 (by rfl) ⟨42980, by rfl⟩) R85961
theorem R57995 : Reach 57995 := rs (se 1 (by rfl) ⟨43496, by rfl⟩) R86993
theorem R58481 : Reach 58481 := rs (se 2 (by rfl) ⟨21930, by rfl⟩) R43861
theorem R58967 : Reach 58967 := rs (se 1 (by rfl) ⟨44225, by rfl⟩) R88451
theorem R59399 : Reach 59399 := rs (se 1 (by rfl) ⟨44549, by rfl⟩) R89099
theorem R224167 : Reach 224167 := rs (se 1 (by rfl) ⟨168125, by rfl⟩) R336251
theorem R60587 : Reach 60587 := rs (se 1 (by rfl) ⟨45440, by rfl⟩) R90881
theorem R60689 : Reach 60689 := rs (se 2 (by rfl) ⟨22758, by rfl⟩) R45517
theorem R61073 : Reach 61073 := rs (se 2 (by rfl) ⟨22902, by rfl⟩) R45805
theorem R61397 : Reach 61397 := rs (se 7 (by rfl) ⟨719, by rfl⟩) R1439
theorem R28775 : Reach 28775 := rs (se 1 (by rfl) ⟨21581, by rfl⟩) R43163
theorem R29297 : Reach 29297 := rs (se 2 (by rfl) ⟨10986, by rfl⟩) R21973
theorem R29315 : Reach 29315 := rs (se 1 (by rfl) ⟨21986, by rfl⟩) R43973
theorem R29393 : Reach 29393 := rs (se 2 (by rfl) ⟨11022, by rfl⟩) R22045
theorem R29483 : Reach 29483 := rs (se 1 (by rfl) ⟨22112, by rfl⟩) R44225
theorem R62531 : Reach 62531 := rs (se 1 (by rfl) ⟨46898, by rfl⟩) R93797
theorem R62639 : Reach 62639 := rs (se 1 (by rfl) ⟨46979, by rfl⟩) R93959
theorem R30269 : Reach 30269 := rs (se 3 (by rfl) ⟨5675, by rfl⟩) R11351
theorem R30347 : Reach 30347 := rs (se 1 (by rfl) ⟨22760, by rfl⟩) R45521
theorem R30709 : Reach 30709 := rs (se 5 (by rfl) ⟨1439, by rfl⟩) R2879
theorem R31043 : Reach 31043 := rs (se 1 (by rfl) ⟨23282, by rfl⟩) R46565
theorem R31265 : Reach 31265 := rs (se 2 (by rfl) ⟨11724, by rfl⟩) R23449
theorem R64313 : Reach 64313 := rs (se 2 (by rfl) ⟨24117, by rfl⟩) R48235
theorem R313 : Reach 313 := rs (se 2 (by rfl) ⟨117, by rfl⟩) R235
theorem R609 : Reach 609 := rs (se 2 (by rfl) ⟨228, by rfl⟩) R457
theorem R617 : Reach 617 := rs (se 2 (by rfl) ⟨231, by rfl⟩) R463
theorem R619 : Reach 619 := rs (se 1 (by rfl) ⟨464, by rfl⟩) R929
theorem R623 : Reach 623 := rs (se 1 (by rfl) ⟨467, by rfl⟩) R935
theorem R627 : Reach 627 := rs (se 1 (by rfl) ⟨470, by rfl⟩) R941
theorem R639 : Reach 639 := rs (se 1 (by rfl) ⟨479, by rfl⟩) R959
theorem R1217 : Reach 1217 := rs (se 2 (by rfl) ⟨456, by rfl⟩) R913
theorem R1219 : Reach 1219 := rs (se 1 (by rfl) ⟨914, by rfl⟩) R1829
theorem R1223 : Reach 1223 := rs (se 1 (by rfl) ⟨917, by rfl⟩) R1835
theorem R1225 : Reach 1225 := rs (se 2 (by rfl) ⟨459, by rfl⟩) R919
theorem R1227 : Reach 1227 := rs (se 1 (by rfl) ⟨920, by rfl⟩) R1841
theorem R1233 : Reach 1233 := rs (se 2 (by rfl) ⟨462, by rfl⟩) R925
theorem R1235 : Reach 1235 := rs (se 1 (by rfl) ⟨926, by rfl⟩) R1853
theorem R1239 : Reach 1239 := rs (se 1 (by rfl) ⟨929, by rfl⟩) R1859
theorem R1247 : Reach 1247 := rs (se 1 (by rfl) ⟨935, by rfl⟩) R1871
theorem R1253 : Reach 1253 := rs (se 4 (by rfl) ⟨117, by rfl⟩) R235
theorem R1279 : Reach 1279 := rs (se 1 (by rfl) ⟨959, by rfl⟩) R1919
theorem R2435 : Reach 2435 := rs (se 1 (by rfl) ⟨1826, by rfl⟩) R3653
theorem R2437 : Reach 2437 := rs (se 4 (by rfl) ⟨228, by rfl⟩) R457
theorem R2439 : Reach 2439 := rs (se 1 (by rfl) ⟨1829, by rfl⟩) R3659
theorem R2447 : Reach 2447 := rs (se 1 (by rfl) ⟨1835, by rfl⟩) R3671
theorem R2449 : Reach 2449 := rs (se 2 (by rfl) ⟨918, by rfl⟩) R1837
theorem R2451 : Reach 2451 := rs (se 1 (by rfl) ⟨1838, by rfl⟩) R3677
theorem R2455 : Reach 2455 := rs (se 1 (by rfl) ⟨1841, by rfl⟩) R3683
theorem R2457 : Reach 2457 := rs (se 2 (by rfl) ⟨921, by rfl⟩) R1843
theorem R2467 : Reach 2467 := rs (se 1 (by rfl) ⟨1850, by rfl⟩) R3701
theorem R2469 : Reach 2469 := rs (se 4 (by rfl) ⟨231, by rfl⟩) R463
theorem R2471 : Reach 2471 := rs (se 1 (by rfl) ⟨1853, by rfl⟩) R3707
theorem R2477 : Reach 2477 := rs (se 3 (by rfl) ⟨464, by rfl⟩) R929
theorem R2493 : Reach 2493 := rs (se 3 (by rfl) ⟨467, by rfl⟩) R935
theorem R2509 : Reach 2509 := rs (se 3 (by rfl) ⟨470, by rfl⟩) R941
theorem R2513 : Reach 2513 := rs (se 2 (by rfl) ⟨942, by rfl⟩) R1885
theorem R2523 : Reach 2523 := rs (se 1 (by rfl) ⟨1892, by rfl⟩) R3785
theorem R2537 : Reach 2537 := rs (se 2 (by rfl) ⟨951, by rfl⟩) R1903
theorem R2557 : Reach 2557 := rs (se 3 (by rfl) ⟨479, by rfl⟩) R959
theorem R167579 : Reach 167579 := rs (se 1 (by rfl) ⟨125684, by rfl⟩) R251369
theorem R298889 : Reach 298889 := rs (se 2 (by rfl) ⟨112083, by rfl⟩) R224167
theorem R37259 : Reach 37259 := rs (se 1 (by rfl) ⟨27944, by rfl⟩) R55889
theorem R4649 : Reach 4649 := rs (se 2 (by rfl) ⟨1743, by rfl⟩) R3487
theorem R4665 : Reach 4665 := rs (se 2 (by rfl) ⟨1749, by rfl⟩) R3499
theorem R4869 : Reach 4869 := rs (se 4 (by rfl) ⟨456, by rfl⟩) R913
theorem R4877 : Reach 4877 := rs (se 3 (by rfl) ⟨914, by rfl⟩) R1829
theorem R4879 : Reach 4879 := rs (se 1 (by rfl) ⟨3659, by rfl⟩) R7319
theorem R4881 : Reach 4881 := rs (se 2 (by rfl) ⟨1830, by rfl⟩) R3661
theorem R4893 : Reach 4893 := rs (se 3 (by rfl) ⟨917, by rfl⟩) R1835
theorem R4899 : Reach 4899 := rs (se 1 (by rfl) ⟨3674, by rfl⟩) R7349
theorem R4901 : Reach 4901 := rs (se 4 (by rfl) ⟨459, by rfl⟩) R919
theorem R4907 : Reach 4907 := rs (se 1 (by rfl) ⟨3680, by rfl⟩) R7361
theorem R4909 : Reach 4909 := rs (se 3 (by rfl) ⟨920, by rfl⟩) R1841
theorem R4913 : Reach 4913 := rs (se 2 (by rfl) ⟨1842, by rfl⟩) R3685
theorem R4915 : Reach 4915 := rs (se 1 (by rfl) ⟨3686, by rfl⟩) R7373
theorem R4933 : Reach 4933 := rs (se 4 (by rfl) ⟨462, by rfl⟩) R925
theorem R4937 : Reach 4937 := rs (se 2 (by rfl) ⟨1851, by rfl⟩) R3703
theorem R4939 : Reach 4939 := rs (se 1 (by rfl) ⟨3704, by rfl⟩) R7409
theorem R4941 : Reach 4941 := rs (se 3 (by rfl) ⟨926, by rfl⟩) R1853
theorem R4943 : Reach 4943 := rs (se 1 (by rfl) ⟨3707, by rfl⟩) R7415
theorem R4957 : Reach 4957 := rs (se 3 (by rfl) ⟨929, by rfl⟩) R1859
theorem R4989 : Reach 4989 := rs (se 3 (by rfl) ⟨935, by rfl⟩) R1871
theorem R5013 : Reach 5013 := rs (se 6 (by rfl) ⟨117, by rfl⟩) R235
theorem R5027 : Reach 5027 := rs (se 1 (by rfl) ⟨3770, by rfl⟩) R7541
theorem R5035 : Reach 5035 := rs (se 1 (by rfl) ⟨3776, by rfl⟩) R7553
theorem R5039 : Reach 5039 := rs (se 1 (by rfl) ⟨3779, by rfl⟩) R7559
theorem R5047 : Reach 5047 := rs (se 1 (by rfl) ⟨3785, by rfl⟩) R7571
theorem R5063 : Reach 5063 := rs (se 1 (by rfl) ⟨3797, by rfl⟩) R7595
theorem R5075 : Reach 5075 := rs (se 1 (by rfl) ⟨3806, by rfl⟩) R7613
theorem R5113 : Reach 5113 := rs (se 2 (by rfl) ⟨1917, by rfl⟩) R3835
theorem R5117 : Reach 5117 := rs (se 3 (by rfl) ⟨959, by rfl⟩) R1919
theorem R5211 : Reach 5211 := rs (se 1 (by rfl) ⟨3908, by rfl⟩) R7817
theorem R38333 : Reach 38333 := rs (se 3 (by rfl) ⟨7187, by rfl⟩) R14375
theorem R38663 : Reach 38663 := rs (se 1 (by rfl) ⟨28997, by rfl⟩) R57995
theorem R38789 : Reach 38789 := rs (se 4 (by rfl) ⟨3636, by rfl⟩) R7273
theorem R38987 : Reach 38987 := rs (se 1 (by rfl) ⟨29240, by rfl⟩) R58481
theorem R39311 : Reach 39311 := rs (se 1 (by rfl) ⟨29483, by rfl⟩) R58967
theorem R39509 : Reach 39509 := rs (se 8 (by rfl) ⟨231, by rfl⟩) R463
theorem R39599 : Reach 39599 := rs (se 1 (by rfl) ⟨29699, by rfl⟩) R59399
theorem R40391 : Reach 40391 := rs (se 1 (by rfl) ⟨30293, by rfl⟩) R60587
theorem R40459 : Reach 40459 := rs (se 1 (by rfl) ⟨30344, by rfl⟩) R60689
theorem R40715 : Reach 40715 := rs (se 1 (by rfl) ⟨30536, by rfl⟩) R61073
theorem R40931 : Reach 40931 := rs (se 1 (by rfl) ⟨30698, by rfl⟩) R61397
theorem R40945 : Reach 40945 := rs (se 2 (by rfl) ⟨15354, by rfl⟩) R30709
theorem R41687 : Reach 41687 := rs (se 1 (by rfl) ⟨31265, by rfl⟩) R62531
theorem R41759 : Reach 41759 := rs (se 1 (by rfl) ⟨31319, by rfl⟩) R62639
theorem R74719 : Reach 74719 := rs (se 1 (by rfl) ⟨56039, by rfl⟩) R112079
theorem R9299 : Reach 9299 := rs (se 1 (by rfl) ⟨6974, by rfl⟩) R13949
theorem R9331 : Reach 9331 := rs (se 1 (by rfl) ⟨6998, by rfl⟩) R13997
theorem R9583 : Reach 9583 := rs (se 1 (by rfl) ⟨7187, by rfl⟩) R14375
theorem R9639 : Reach 9639 := rs (se 1 (by rfl) ⟨7229, by rfl⟩) R14459
theorem R9697 : Reach 9697 := rs (se 2 (by rfl) ⟨3636, by rfl⟩) R7273
theorem R9703 : Reach 9703 := rs (se 1 (by rfl) ⟨7277, by rfl⟩) R14555
theorem R9741 : Reach 9741 := rs (se 3 (by rfl) ⟨1826, by rfl⟩) R3653
theorem R9745 : Reach 9745 := rs (se 2 (by rfl) ⟨3654, by rfl⟩) R7309
theorem R9749 : Reach 9749 := rs (se 6 (by rfl) ⟨228, by rfl⟩) R457
theorem R9757 : Reach 9757 := rs (se 3 (by rfl) ⟨1829, by rfl⟩) R3659
theorem R9763 : Reach 9763 := rs (se 1 (by rfl) ⟨7322, by rfl⟩) R14645
theorem R9771 : Reach 9771 := rs (se 1 (by rfl) ⟨7328, by rfl⟩) R14657
theorem R9789 : Reach 9789 := rs (se 3 (by rfl) ⟨1835, by rfl⟩) R3671
theorem R75329 : Reach 75329 := rs (se 2 (by rfl) ⟨28248, by rfl⟩) R56497
theorem R9797 : Reach 9797 := rs (se 4 (by rfl) ⟨918, by rfl⟩) R1837
theorem R9803 : Reach 9803 := rs (se 1 (by rfl) ⟨7352, by rfl⟩) R14705
theorem R9805 : Reach 9805 := rs (se 3 (by rfl) ⟨1838, by rfl⟩) R3677
theorem R9815 : Reach 9815 := rs (se 1 (by rfl) ⟨7361, by rfl⟩) R14723
theorem R9817 : Reach 9817 := rs (se 2 (by rfl) ⟨3681, by rfl⟩) R7363
theorem R9821 : Reach 9821 := rs (se 3 (by rfl) ⟨1841, by rfl⟩) R3683
theorem R9827 : Reach 9827 := rs (se 1 (by rfl) ⟨7370, by rfl⟩) R14741
theorem R9829 : Reach 9829 := rs (se 4 (by rfl) ⟨921, by rfl⟩) R1843
theorem R9869 : Reach 9869 := rs (se 3 (by rfl) ⟨1850, by rfl⟩) R3701
theorem R9873 : Reach 9873 := rs (se 2 (by rfl) ⟨3702, by rfl⟩) R7405
theorem R9875 : Reach 9875 := rs (se 1 (by rfl) ⟨7406, by rfl⟩) R14813
theorem R9877 : Reach 9877 := rs (se 6 (by rfl) ⟨231, by rfl⟩) R463
theorem R9879 : Reach 9879 := rs (se 1 (by rfl) ⟨7409, by rfl⟩) R14819
theorem R9885 : Reach 9885 := rs (se 3 (by rfl) ⟨1853, by rfl⟩) R3707
theorem R9909 : Reach 9909 := rs (se 5 (by rfl) ⟨464, by rfl⟩) R929
theorem R9921 : Reach 9921 := rs (se 2 (by rfl) ⟨3720, by rfl⟩) R7441
theorem R9927 : Reach 9927 := rs (se 1 (by rfl) ⟨7445, by rfl⟩) R14891
theorem R9929 : Reach 9929 := rs (se 2 (by rfl) ⟨3723, by rfl⟩) R7447
theorem R9947 : Reach 9947 := rs (se 1 (by rfl) ⟨7460, by rfl⟩) R14921
theorem R9973 : Reach 9973 := rs (se 5 (by rfl) ⟨467, by rfl⟩) R935
theorem R10037 : Reach 10037 := rs (se 5 (by rfl) ⟨470, by rfl⟩) R941
theorem R10049 : Reach 10049 := rs (se 2 (by rfl) ⟨3768, by rfl⟩) R7537
theorem R10053 : Reach 10053 := rs (se 4 (by rfl) ⟨942, by rfl⟩) R1885
theorem R10059 : Reach 10059 := rs (se 1 (by rfl) ⟨7544, by rfl⟩) R15089
theorem R10071 : Reach 10071 := rs (se 1 (by rfl) ⟨7553, by rfl⟩) R15107
theorem R10073 : Reach 10073 := rs (se 2 (by rfl) ⟨3777, by rfl⟩) R7555
theorem R10079 : Reach 10079 := rs (se 1 (by rfl) ⟨7559, by rfl⟩) R15119
theorem R10089 : Reach 10089 := rs (se 2 (by rfl) ⟨3783, by rfl⟩) R7567
theorem R10093 : Reach 10093 := rs (se 3 (by rfl) ⟨1892, by rfl⟩) R3785
theorem R10105 : Reach 10105 := rs (se 2 (by rfl) ⟨3789, by rfl⟩) R7579
theorem R42875 : Reach 42875 := rs (se 1 (by rfl) ⟨32156, by rfl⟩) R64313
theorem R10113 : Reach 10113 := rs (se 2 (by rfl) ⟨3792, by rfl⟩) R7585
theorem R10127 : Reach 10127 := rs (se 1 (by rfl) ⟨7595, by rfl⟩) R15191
theorem R10149 : Reach 10149 := rs (se 4 (by rfl) ⟨951, by rfl⟩) R1903
theorem R10227 : Reach 10227 := rs (se 1 (by rfl) ⟨7670, by rfl⟩) R15341
theorem R10229 : Reach 10229 := rs (se 5 (by rfl) ⟨479, by rfl⟩) R959
theorem R10265 : Reach 10265 := rs (se 2 (by rfl) ⟨3849, by rfl⟩) R7699
theorem R10281 : Reach 10281 := rs (se 2 (by rfl) ⟨3855, by rfl⟩) R7711
theorem R10347 : Reach 10347 := rs (se 1 (by rfl) ⟨7760, by rfl⟩) R15521
theorem R10423 : Reach 10423 := rs (se 1 (by rfl) ⟨7817, by rfl⟩) R15635
theorem R76409 : Reach 76409 := rs (se 2 (by rfl) ⟨28653, by rfl⟩) R57307
theorem R78731 : Reach 78731 := rs (se 1 (by rfl) ⟨59048, by rfl⟩) R118097
theorem R80783 : Reach 80783 := rs (se 1 (by rfl) ⟨60587, by rfl⟩) R121175
theorem R80963 : Reach 80963 := rs (se 1 (by rfl) ⟨60722, by rfl⟩) R121445
theorem R18809 : Reach 18809 := rs (se 2 (by rfl) ⟨7053, by rfl⟩) R14107
theorem R19097 : Reach 19097 := rs (se 2 (by rfl) ⟨7161, by rfl⟩) R14323
theorem R19183 : Reach 19183 := rs (se 1 (by rfl) ⟨14387, by rfl⟩) R28775
theorem R19273 : Reach 19273 := rs (se 2 (by rfl) ⟨7227, by rfl⟩) R14455
theorem R19531 : Reach 19531 := rs (se 1 (by rfl) ⟨14648, by rfl⟩) R29297
theorem R19543 : Reach 19543 := rs (se 1 (by rfl) ⟨14657, by rfl⟩) R29315
theorem R19595 : Reach 19595 := rs (se 1 (by rfl) ⟨14696, by rfl⟩) R29393
theorem R19637 : Reach 19637 := rs (se 5 (by rfl) ⟨920, by rfl⟩) R1841
theorem R19655 : Reach 19655 := rs (se 1 (by rfl) ⟨14741, by rfl⟩) R29483
theorem R19745 : Reach 19745 := rs (se 2 (by rfl) ⟨7404, by rfl⟩) R14809
theorem R19757 : Reach 19757 := rs (se 3 (by rfl) ⟨3704, by rfl⟩) R7409
theorem R19777 : Reach 19777 := rs (se 2 (by rfl) ⟨7416, by rfl⟩) R14833
theorem R314927 : Reach 314927 := rs (se 1 (by rfl) ⟨236195, by rfl⟩) R472391
theorem R20081 : Reach 20081 := rs (se 2 (by rfl) ⟨7530, by rfl⟩) R15061
theorem R20141 : Reach 20141 := rs (se 3 (by rfl) ⟨3776, by rfl⟩) R7553
theorem R20177 : Reach 20177 := rs (se 2 (by rfl) ⟨7566, by rfl⟩) R15133
theorem R20179 : Reach 20179 := rs (se 1 (by rfl) ⟨15134, by rfl⟩) R30269
theorem R20189 : Reach 20189 := rs (se 3 (by rfl) ⟨3785, by rfl⟩) R7571
theorem R20231 : Reach 20231 := rs (se 1 (by rfl) ⟨15173, by rfl⟩) R30347
theorem R20297 : Reach 20297 := rs (se 2 (by rfl) ⟨7611, by rfl⟩) R15223
theorem R20465 : Reach 20465 := rs (se 2 (by rfl) ⟨7674, by rfl⟩) R15349
theorem R20695 : Reach 20695 := rs (se 1 (by rfl) ⟨15521, by rfl⟩) R31043
theorem R20843 : Reach 20843 := rs (se 1 (by rfl) ⟨15632, by rfl⟩) R31265
theorem R20845 : Reach 20845 := rs (se 3 (by rfl) ⟨3908, by rfl⟩) R7817
theorem R2677967 : Reach 2677967 := rs (se 1 (by rfl) ⟨2008475, by rfl⟩) R4016951
theorem R157463 : Reach 157463 := rs (se 1 (by rfl) ⟨118097, by rfl⟩) R236195
theorem R92573 : Reach 92573 := rs (se 3 (by rfl) ⟨17357, by rfl⟩) R34715
theorem R161837 : Reach 161837 := rs (se 3 (by rfl) ⟨30344, by rfl⟩) R60689
theorem R2587085 : Reach 2587085 := rs (se 3 (by rfl) ⟨485078, by rfl⟩) R970157
theorem R411 : Reach 411 := rs (se 1 (by rfl) ⟨308, by rfl⟩) R617
theorem R415 : Reach 415 := rs (se 1 (by rfl) ⟨311, by rfl⟩) R623
theorem R417 : Reach 417 := rs (se 2 (by rfl) ⟨156, by rfl⟩) R313
theorem R811 : Reach 811 := rs (se 1 (by rfl) ⟨608, by rfl⟩) R1217
theorem R815 : Reach 815 := rs (se 1 (by rfl) ⟨611, by rfl⟩) R1223
theorem R823 : Reach 823 := rs (se 1 (by rfl) ⟨617, by rfl⟩) R1235
theorem R825 : Reach 825 := rs (se 2 (by rfl) ⟨309, by rfl⟩) R619
theorem R831 : Reach 831 := rs (se 1 (by rfl) ⟨623, by rfl⟩) R1247
theorem R835 : Reach 835 := rs (se 1 (by rfl) ⟨626, by rfl⟩) R1253
theorem R99625 : Reach 99625 := rs (se 2 (by rfl) ⟨37359, by rfl⟩) R74719
theorem R1623 : Reach 1623 := rs (se 1 (by rfl) ⟨1217, by rfl⟩) R2435
theorem R1625 : Reach 1625 := rs (se 2 (by rfl) ⟨609, by rfl⟩) R1219
theorem R1631 : Reach 1631 := rs (se 1 (by rfl) ⟨1223, by rfl⟩) R2447
theorem R1633 : Reach 1633 := rs (se 2 (by rfl) ⟨612, by rfl⟩) R1225
theorem R1645 : Reach 1645 := rs (se 3 (by rfl) ⟨308, by rfl⟩) R617
theorem R1647 : Reach 1647 := rs (se 1 (by rfl) ⟨1235, by rfl⟩) R2471
theorem R1651 : Reach 1651 := rs (se 1 (by rfl) ⟨1238, by rfl⟩) R2477
theorem R1661 : Reach 1661 := rs (se 3 (by rfl) ⟨311, by rfl⟩) R623
theorem R1669 : Reach 1669 := rs (se 4 (by rfl) ⟨156, by rfl⟩) R313
theorem R1675 : Reach 1675 := rs (se 1 (by rfl) ⟨1256, by rfl⟩) R2513
theorem R1691 : Reach 1691 := rs (se 1 (by rfl) ⟨1268, by rfl⟩) R2537
theorem R1705 : Reach 1705 := rs (se 2 (by rfl) ⟨639, by rfl⟩) R1279
theorem R199259 : Reach 199259 := rs (se 1 (by rfl) ⟨149444, by rfl⟩) R298889
theorem R3099 : Reach 3099 := rs (se 1 (by rfl) ⟨2324, by rfl⟩) R4649
theorem R3245 : Reach 3245 := rs (se 3 (by rfl) ⟨608, by rfl⟩) R1217
theorem R3249 : Reach 3249 := rs (se 2 (by rfl) ⟨1218, by rfl⟩) R2437
theorem R3251 : Reach 3251 := rs (se 1 (by rfl) ⟨2438, by rfl⟩) R4877
theorem R3261 : Reach 3261 := rs (se 3 (by rfl) ⟨611, by rfl⟩) R1223
theorem R3265 : Reach 3265 := rs (se 2 (by rfl) ⟨1224, by rfl⟩) R2449
theorem R3267 : Reach 3267 := rs (se 1 (by rfl) ⟨2450, by rfl⟩) R4901
theorem R3271 : Reach 3271 := rs (se 1 (by rfl) ⟨2453, by rfl⟩) R4907
theorem R3273 : Reach 3273 := rs (se 2 (by rfl) ⟨1227, by rfl⟩) R2455
theorem R3275 : Reach 3275 := rs (se 1 (by rfl) ⟨2456, by rfl⟩) R4913
theorem R3289 : Reach 3289 := rs (se 2 (by rfl) ⟨1233, by rfl⟩) R2467
theorem R3291 : Reach 3291 := rs (se 1 (by rfl) ⟨2468, by rfl⟩) R4937
theorem R3293 : Reach 3293 := rs (se 3 (by rfl) ⟨617, by rfl⟩) R1235
theorem R3295 : Reach 3295 := rs (se 1 (by rfl) ⟨2471, by rfl⟩) R4943
theorem R3301 : Reach 3301 := rs (se 4 (by rfl) ⟨309, by rfl⟩) R619
theorem R3325 : Reach 3325 := rs (se 3 (by rfl) ⟨623, by rfl⟩) R1247
theorem R3341 : Reach 3341 := rs (se 3 (by rfl) ⟨626, by rfl⟩) R1253
theorem R3345 : Reach 3345 := rs (se 2 (by rfl) ⟨1254, by rfl⟩) R2509
theorem R3351 : Reach 3351 := rs (se 1 (by rfl) ⟨2513, by rfl⟩) R5027
theorem R3359 : Reach 3359 := rs (se 1 (by rfl) ⟨2519, by rfl⟩) R5039
theorem R3375 : Reach 3375 := rs (se 1 (by rfl) ⟨2531, by rfl⟩) R5063
theorem R3383 : Reach 3383 := rs (se 1 (by rfl) ⟨2537, by rfl⟩) R5075
theorem R3409 : Reach 3409 := rs (se 2 (by rfl) ⟨1278, by rfl⟩) R2557
theorem R3411 : Reach 3411 := rs (se 1 (by rfl) ⟨2558, by rfl⟩) R5117
theorem R104165 : Reach 104165 := rs (se 4 (by rfl) ⟨9765, by rfl⟩) R19531
theorem R6199 : Reach 6199 := rs (se 1 (by rfl) ⟨4649, by rfl⟩) R9299
theorem R6493 : Reach 6493 := rs (se 3 (by rfl) ⟨1217, by rfl⟩) R2435
theorem R6499 : Reach 6499 := rs (se 1 (by rfl) ⟨4874, by rfl⟩) R9749
theorem R6501 : Reach 6501 := rs (se 4 (by rfl) ⟨609, by rfl⟩) R1219
theorem R6505 : Reach 6505 := rs (se 2 (by rfl) ⟨2439, by rfl⟩) R4879
theorem R6525 : Reach 6525 := rs (se 3 (by rfl) ⟨1223, by rfl⟩) R2447
theorem R6531 : Reach 6531 := rs (se 1 (by rfl) ⟨4898, by rfl⟩) R9797
theorem R6533 : Reach 6533 := rs (se 4 (by rfl) ⟨612, by rfl⟩) R1225
theorem R6535 : Reach 6535 := rs (se 1 (by rfl) ⟨4901, by rfl⟩) R9803
theorem R6543 : Reach 6543 := rs (se 1 (by rfl) ⟨4907, by rfl⟩) R9815
theorem R6545 : Reach 6545 := rs (se 2 (by rfl) ⟨2454, by rfl⟩) R4909
theorem R6547 : Reach 6547 := rs (se 1 (by rfl) ⟨4910, by rfl⟩) R9821
theorem R6551 : Reach 6551 := rs (se 1 (by rfl) ⟨4913, by rfl⟩) R9827
theorem R6553 : Reach 6553 := rs (se 2 (by rfl) ⟨2457, by rfl⟩) R4915
theorem R6577 : Reach 6577 := rs (se 2 (by rfl) ⟨2466, by rfl⟩) R4933
theorem R6579 : Reach 6579 := rs (se 1 (by rfl) ⟨4934, by rfl⟩) R9869
theorem R6581 : Reach 6581 := rs (se 5 (by rfl) ⟨308, by rfl⟩) R617
theorem R6583 : Reach 6583 := rs (se 1 (by rfl) ⟨4937, by rfl⟩) R9875
theorem R6585 : Reach 6585 := rs (se 2 (by rfl) ⟨2469, by rfl⟩) R4939
theorem R6589 : Reach 6589 := rs (se 3 (by rfl) ⟨1235, by rfl⟩) R2471
theorem R6605 : Reach 6605 := rs (se 3 (by rfl) ⟨1238, by rfl⟩) R2477
theorem R6609 : Reach 6609 := rs (se 2 (by rfl) ⟨2478, by rfl⟩) R4957
theorem R6619 : Reach 6619 := rs (se 1 (by rfl) ⟨4964, by rfl⟩) R9929
theorem R6631 : Reach 6631 := rs (se 1 (by rfl) ⟨4973, by rfl⟩) R9947
theorem R6645 : Reach 6645 := rs (se 5 (by rfl) ⟨311, by rfl⟩) R623
theorem R104975 : Reach 104975 := rs (se 1 (by rfl) ⟨78731, by rfl⟩) R157463
theorem R6677 : Reach 6677 := rs (se 6 (by rfl) ⟨156, by rfl⟩) R313
theorem R6691 : Reach 6691 := rs (se 1 (by rfl) ⟨5018, by rfl⟩) R10037
theorem R6699 : Reach 6699 := rs (se 1 (by rfl) ⟨5024, by rfl⟩) R10049
theorem R6701 : Reach 6701 := rs (se 3 (by rfl) ⟨1256, by rfl⟩) R2513
theorem R6713 : Reach 6713 := rs (se 2 (by rfl) ⟨2517, by rfl⟩) R5035
theorem R6715 : Reach 6715 := rs (se 1 (by rfl) ⟨5036, by rfl⟩) R10073
theorem R6719 : Reach 6719 := rs (se 1 (by rfl) ⟨5039, by rfl⟩) R10079
theorem R6729 : Reach 6729 := rs (se 2 (by rfl) ⟨2523, by rfl⟩) R5047
theorem R6751 : Reach 6751 := rs (se 1 (by rfl) ⟨5063, by rfl⟩) R10127
theorem R6765 : Reach 6765 := rs (se 3 (by rfl) ⟨1268, by rfl⟩) R2537
theorem R6817 : Reach 6817 := rs (se 2 (by rfl) ⟨2556, by rfl⟩) R5113
theorem R6819 : Reach 6819 := rs (se 1 (by rfl) ⟨5114, by rfl⟩) R10229
theorem R6821 : Reach 6821 := rs (se 4 (by rfl) ⟨639, by rfl⟩) R1279
theorem R6843 : Reach 6843 := rs (se 1 (by rfl) ⟨5132, by rfl⟩) R10265
theorem R107891 : Reach 107891 := rs (se 1 (by rfl) ⟨80918, by rfl⟩) R161837
theorem R12397 : Reach 12397 := rs (se 3 (by rfl) ⟨2324, by rfl⟩) R4649
theorem R12441 : Reach 12441 := rs (se 2 (by rfl) ⟨4665, by rfl⟩) R9331
theorem R12539 : Reach 12539 := rs (se 1 (by rfl) ⟨9404, by rfl⟩) R18809
theorem R12731 : Reach 12731 := rs (se 1 (by rfl) ⟨9548, by rfl⟩) R19097
theorem R12777 : Reach 12777 := rs (se 2 (by rfl) ⟨4791, by rfl⟩) R9583
theorem R12929 : Reach 12929 := rs (se 2 (by rfl) ⟨4848, by rfl⟩) R9697
theorem R12937 : Reach 12937 := rs (se 2 (by rfl) ⟨4851, by rfl⟩) R9703
theorem R12997 : Reach 12997 := rs (se 4 (by rfl) ⟨1218, by rfl⟩) R2437
theorem R13009 : Reach 13009 := rs (se 2 (by rfl) ⟨4878, by rfl⟩) R9757
theorem R13045 : Reach 13045 := rs (se 5 (by rfl) ⟨611, by rfl⟩) R1223
theorem R13061 : Reach 13061 := rs (se 4 (by rfl) ⟨1224, by rfl⟩) R2449
theorem R13063 : Reach 13063 := rs (se 1 (by rfl) ⟨9797, by rfl⟩) R19595
theorem R13073 : Reach 13073 := rs (se 2 (by rfl) ⟨4902, by rfl⟩) R9805
theorem R13085 : Reach 13085 := rs (se 3 (by rfl) ⟨2453, by rfl⟩) R4907
theorem R13091 : Reach 13091 := rs (se 1 (by rfl) ⟨9818, by rfl⟩) R19637
theorem R13103 : Reach 13103 := rs (se 1 (by rfl) ⟨9827, by rfl⟩) R19655
theorem R13105 : Reach 13105 := rs (se 2 (by rfl) ⟨4914, by rfl⟩) R9829
theorem R13157 : Reach 13157 := rs (se 4 (by rfl) ⟨1233, by rfl⟩) R2467
theorem R13163 : Reach 13163 := rs (se 1 (by rfl) ⟨9872, by rfl⟩) R19745
theorem R13169 : Reach 13169 := rs (se 2 (by rfl) ⟨4938, by rfl⟩) R9877
theorem R13171 : Reach 13171 := rs (se 1 (by rfl) ⟨9878, by rfl⟩) R19757
theorem R13181 : Reach 13181 := rs (se 3 (by rfl) ⟨2471, by rfl⟩) R4943
theorem R13205 : Reach 13205 := rs (se 6 (by rfl) ⟨309, by rfl⟩) R619
theorem R13297 : Reach 13297 := rs (se 2 (by rfl) ⟨4986, by rfl⟩) R9973
theorem R13301 : Reach 13301 := rs (se 5 (by rfl) ⟨623, by rfl⟩) R1247
theorem R209951 : Reach 209951 := rs (se 1 (by rfl) ⟨157463, by rfl⟩) R314927
theorem R13387 : Reach 13387 := rs (se 1 (by rfl) ⟨10040, by rfl⟩) R20081
theorem R13405 : Reach 13405 := rs (se 3 (by rfl) ⟨2513, by rfl⟩) R5027
theorem R111719 : Reach 111719 := rs (se 1 (by rfl) ⟨83789, by rfl⟩) R167579
theorem R13427 : Reach 13427 := rs (se 1 (by rfl) ⟨10070, by rfl⟩) R20141
theorem R13451 : Reach 13451 := rs (se 1 (by rfl) ⟨10088, by rfl⟩) R20177
theorem R13457 : Reach 13457 := rs (se 2 (by rfl) ⟨5046, by rfl⟩) R10093
theorem R13459 : Reach 13459 := rs (se 1 (by rfl) ⟨10094, by rfl⟩) R20189
theorem R13487 : Reach 13487 := rs (se 1 (by rfl) ⟨10115, by rfl⟩) R20231
theorem R13531 : Reach 13531 := rs (se 1 (by rfl) ⟨10148, by rfl⟩) R20297
theorem R13637 : Reach 13637 := rs (se 4 (by rfl) ⟨1278, by rfl⟩) R2557
theorem R13643 : Reach 13643 := rs (se 1 (by rfl) ⟨10232, by rfl⟩) R20465
theorem R13895 : Reach 13895 := rs (se 1 (by rfl) ⟨10421, by rfl⟩) R20843
theorem R1785311 : Reach 1785311 := rs (se 1 (by rfl) ⟨1338983, by rfl⟩) R2677967
theorem R50219 : Reach 50219 := rs (se 1 (by rfl) ⟨37664, by rfl⟩) R75329
theorem R50939 : Reach 50939 := rs (se 1 (by rfl) ⟨38204, by rfl⟩) R76409
theorem R52487 : Reach 52487 := rs (se 1 (by rfl) ⟨39365, by rfl⟩) R78731
theorem R1724723 : Reach 1724723 := rs (se 1 (by rfl) ⟨1293542, by rfl⟩) R2587085
theorem R53621 : Reach 53621 := rs (se 5 (by rfl) ⟨2513, by rfl⟩) R5027
theorem R53855 : Reach 53855 := rs (se 1 (by rfl) ⟨40391, by rfl⟩) R80783
theorem R53945 : Reach 53945 := rs (se 2 (by rfl) ⟨20229, by rfl⟩) R40459
theorem R53975 : Reach 53975 := rs (se 1 (by rfl) ⟨40481, by rfl⟩) R80963
theorem R54593 : Reach 54593 := rs (se 2 (by rfl) ⟨20472, by rfl⟩) R40945
theorem R24839 : Reach 24839 := rs (se 1 (by rfl) ⟨18629, by rfl⟩) R37259
theorem R25555 : Reach 25555 := rs (se 1 (by rfl) ⟨19166, by rfl⟩) R38333
theorem R25577 : Reach 25577 := rs (se 2 (by rfl) ⟨9591, by rfl⟩) R19183
theorem R25697 : Reach 25697 := rs (se 2 (by rfl) ⟨9636, by rfl⟩) R19273
theorem R25775 : Reach 25775 := rs (se 1 (by rfl) ⟨19331, by rfl⟩) R38663
theorem R25859 : Reach 25859 := rs (se 1 (by rfl) ⟨19394, by rfl⟩) R38789
theorem R25973 : Reach 25973 := rs (se 5 (by rfl) ⟨1217, by rfl⟩) R2435
theorem R25991 : Reach 25991 := rs (se 1 (by rfl) ⟨19493, by rfl⟩) R38987
theorem R26021 : Reach 26021 := rs (se 4 (by rfl) ⟨2439, by rfl⟩) R4879
theorem R26041 : Reach 26041 := rs (se 2 (by rfl) ⟨9765, by rfl⟩) R19531
theorem R26057 : Reach 26057 := rs (se 2 (by rfl) ⟨9771, by rfl⟩) R19543
theorem R26189 : Reach 26189 := rs (se 3 (by rfl) ⟨4910, by rfl⟩) R9821
theorem R26207 : Reach 26207 := rs (se 1 (by rfl) ⟨19655, by rfl⟩) R39311
theorem R26333 : Reach 26333 := rs (se 3 (by rfl) ⟨4937, by rfl⟩) R9875
theorem R26339 : Reach 26339 := rs (se 1 (by rfl) ⟨19754, by rfl⟩) R39509
theorem R26369 : Reach 26369 := rs (se 2 (by rfl) ⟨9888, by rfl⟩) R19777
theorem R26399 : Reach 26399 := rs (se 1 (by rfl) ⟨19799, by rfl⟩) R39599
theorem R26477 : Reach 26477 := rs (se 3 (by rfl) ⟨4964, by rfl⟩) R9929
theorem R26581 : Reach 26581 := rs (se 7 (by rfl) ⟨311, by rfl⟩) R623
theorem R26765 : Reach 26765 := rs (se 3 (by rfl) ⟨5018, by rfl⟩) R10037
theorem R26905 : Reach 26905 := rs (se 2 (by rfl) ⟨10089, by rfl⟩) R20179
theorem R26927 : Reach 26927 := rs (se 1 (by rfl) ⟨20195, by rfl⟩) R40391
theorem R27143 : Reach 27143 := rs (se 1 (by rfl) ⟨20357, by rfl⟩) R40715
theorem R27269 : Reach 27269 := rs (se 4 (by rfl) ⟨2556, by rfl⟩) R5113
theorem R27287 : Reach 27287 := rs (se 1 (by rfl) ⟨20465, by rfl⟩) R40931
theorem R27593 : Reach 27593 := rs (se 2 (by rfl) ⟨10347, by rfl⟩) R20695
theorem R27791 : Reach 27791 := rs (se 1 (by rfl) ⟨20843, by rfl⟩) R41687
theorem R27793 : Reach 27793 := rs (se 2 (by rfl) ⟨10422, by rfl⟩) R20845
theorem R27839 : Reach 27839 := rs (se 1 (by rfl) ⟨20879, by rfl⟩) R41759
theorem R28583 : Reach 28583 := rs (se 1 (by rfl) ⟨21437, by rfl⟩) R42875
theorem R61715 : Reach 61715 := rs (se 1 (by rfl) ⟨46286, by rfl⟩) R92573
theorem R543 : Reach 543 := rs (se 1 (by rfl) ⟨407, by rfl⟩) R815
theorem R553 : Reach 553 := rs (se 2 (by rfl) ⟨207, by rfl⟩) R415
theorem R33479 : Reach 33479 := rs (se 1 (by rfl) ⟨25109, by rfl⟩) R50219
theorem R1081 : Reach 1081 := rs (se 2 (by rfl) ⟨405, by rfl⟩) R811
theorem R1083 : Reach 1083 := rs (se 1 (by rfl) ⟨812, by rfl⟩) R1625
theorem R1087 : Reach 1087 := rs (se 1 (by rfl) ⟨815, by rfl⟩) R1631
theorem R1097 : Reach 1097 := rs (se 2 (by rfl) ⟨411, by rfl⟩) R823
theorem R1107 : Reach 1107 := rs (se 1 (by rfl) ⟨830, by rfl⟩) R1661
theorem R1113 : Reach 1113 := rs (se 2 (by rfl) ⟨417, by rfl⟩) R835
theorem R1127 : Reach 1127 := rs (se 1 (by rfl) ⟨845, by rfl⟩) R1691
theorem R33959 : Reach 33959 := rs (se 1 (by rfl) ⟨25469, by rfl⟩) R50939
theorem R34073 : Reach 34073 := rs (se 2 (by rfl) ⟨12777, by rfl⟩) R25555
theorem R132833 : Reach 132833 := rs (se 2 (by rfl) ⟨49812, by rfl⟩) R99625
theorem R132839 : Reach 132839 := rs (se 1 (by rfl) ⟨99629, by rfl⟩) R199259
theorem R34613 : Reach 34613 := rs (se 5 (by rfl) ⟨1622, by rfl⟩) R3245
theorem R34721 : Reach 34721 := rs (se 2 (by rfl) ⟨13020, by rfl⟩) R26041
theorem R34829 : Reach 34829 := rs (se 3 (by rfl) ⟨6530, by rfl⟩) R13061
theorem R2163 : Reach 2163 := rs (se 1 (by rfl) ⟨1622, by rfl⟩) R3245
theorem R2167 : Reach 2167 := rs (se 1 (by rfl) ⟨1625, by rfl⟩) R3251
theorem R2173 : Reach 2173 := rs (se 3 (by rfl) ⟨407, by rfl⟩) R815
theorem R2177 : Reach 2177 := rs (se 2 (by rfl) ⟨816, by rfl⟩) R1633
theorem R2183 : Reach 2183 := rs (se 1 (by rfl) ⟨1637, by rfl⟩) R3275
theorem R2193 : Reach 2193 := rs (se 2 (by rfl) ⟨822, by rfl⟩) R1645
theorem R2195 : Reach 2195 := rs (se 1 (by rfl) ⟨1646, by rfl⟩) R3293
theorem R2201 : Reach 2201 := rs (se 2 (by rfl) ⟨825, by rfl⟩) R1651
theorem R2213 : Reach 2213 := rs (se 4 (by rfl) ⟨207, by rfl⟩) R415
theorem R34991 : Reach 34991 := rs (se 1 (by rfl) ⟨26243, by rfl⟩) R52487
theorem R2225 : Reach 2225 := rs (se 2 (by rfl) ⟨834, by rfl⟩) R1669
theorem R2227 : Reach 2227 := rs (se 1 (by rfl) ⟨1670, by rfl⟩) R3341
theorem R2233 : Reach 2233 := rs (se 2 (by rfl) ⟨837, by rfl⟩) R1675
theorem R2239 : Reach 2239 := rs (se 1 (by rfl) ⟨1679, by rfl⟩) R3359
theorem R2255 : Reach 2255 := rs (se 1 (by rfl) ⟨1691, by rfl⟩) R3383
theorem R2273 : Reach 2273 := rs (se 2 (by rfl) ⟨852, by rfl⟩) R1705
theorem R35441 : Reach 35441 := rs (se 2 (by rfl) ⟨13290, by rfl⟩) R26581
theorem R1149815 : Reach 1149815 := rs (se 1 (by rfl) ⟨862361, by rfl⟩) R1724723
theorem R35747 : Reach 35747 := rs (se 1 (by rfl) ⟨26810, by rfl⟩) R53621
theorem R68525 : Reach 68525 := rs (se 3 (by rfl) ⟨12848, by rfl⟩) R25697
theorem R35873 : Reach 35873 := rs (se 2 (by rfl) ⟨13452, by rfl⟩) R26905
theorem R35903 : Reach 35903 := rs (se 1 (by rfl) ⟨26927, by rfl⟩) R53855
theorem R35963 : Reach 35963 := rs (se 1 (by rfl) ⟨26972, by rfl⟩) R53945
theorem R35983 : Reach 35983 := rs (se 1 (by rfl) ⟨26987, by rfl⟩) R53975
theorem R36085 : Reach 36085 := rs (se 5 (by rfl) ⟨1691, by rfl⟩) R3383
theorem R36395 : Reach 36395 := rs (se 1 (by rfl) ⟨27296, by rfl⟩) R54593
theorem R69443 : Reach 69443 := rs (se 1 (by rfl) ⟨52082, by rfl⟩) R104165
theorem R37057 : Reach 37057 := rs (se 2 (by rfl) ⟨13896, by rfl⟩) R27793
theorem R4325 : Reach 4325 := rs (se 4 (by rfl) ⟨405, by rfl⟩) R811
theorem R4333 : Reach 4333 := rs (se 3 (by rfl) ⟨812, by rfl⟩) R1625
theorem R4349 : Reach 4349 := rs (se 3 (by rfl) ⟨815, by rfl⟩) R1631
theorem R4353 : Reach 4353 := rs (se 2 (by rfl) ⟨1632, by rfl⟩) R3265
theorem R4355 : Reach 4355 := rs (se 1 (by rfl) ⟨3266, by rfl⟩) R6533
theorem R69893 : Reach 69893 := rs (se 4 (by rfl) ⟨6552, by rfl⟩) R13105
theorem R4361 : Reach 4361 := rs (se 2 (by rfl) ⟨1635, by rfl⟩) R3271
theorem R4363 : Reach 4363 := rs (se 1 (by rfl) ⟨3272, by rfl⟩) R6545
theorem R4367 : Reach 4367 := rs (se 1 (by rfl) ⟨3275, by rfl⟩) R6551
theorem R4385 : Reach 4385 := rs (se 2 (by rfl) ⟨1644, by rfl⟩) R3289
theorem R4387 : Reach 4387 := rs (se 1 (by rfl) ⟨3290, by rfl⟩) R6581
theorem R4389 : Reach 4389 := rs (se 4 (by rfl) ⟨411, by rfl⟩) R823
theorem R4393 : Reach 4393 := rs (se 2 (by rfl) ⟨1647, by rfl⟩) R3295
theorem R4401 : Reach 4401 := rs (se 2 (by rfl) ⟨1650, by rfl⟩) R3301
theorem R4403 : Reach 4403 := rs (se 1 (by rfl) ⟨3302, by rfl⟩) R6605
theorem R4429 : Reach 4429 := rs (se 3 (by rfl) ⟨830, by rfl⟩) R1661
theorem R4433 : Reach 4433 := rs (se 2 (by rfl) ⟨1662, by rfl⟩) R3325
theorem R69983 : Reach 69983 := rs (se 1 (by rfl) ⟨52487, by rfl⟩) R104975
theorem R4451 : Reach 4451 := rs (se 1 (by rfl) ⟨3338, by rfl⟩) R6677
theorem R4453 : Reach 4453 := rs (se 4 (by rfl) ⟨417, by rfl⟩) R835
theorem R4467 : Reach 4467 := rs (se 1 (by rfl) ⟨3350, by rfl⟩) R6701
theorem R4475 : Reach 4475 := rs (se 1 (by rfl) ⟨3356, by rfl⟩) R6713
theorem R4479 : Reach 4479 := rs (se 1 (by rfl) ⟨3359, by rfl⟩) R6719
theorem R4509 : Reach 4509 := rs (se 3 (by rfl) ⟨845, by rfl⟩) R1691
theorem R4545 : Reach 4545 := rs (se 2 (by rfl) ⟨1704, by rfl⟩) R3409
theorem R4547 : Reach 4547 := rs (se 1 (by rfl) ⟨3410, by rfl⟩) R6821
theorem R70237 : Reach 70237 := rs (se 3 (by rfl) ⟨13169, by rfl⟩) R26339
theorem R71927 : Reach 71927 := rs (se 1 (by rfl) ⟨53945, by rfl⟩) R107891
theorem R8265 : Reach 8265 := rs (se 2 (by rfl) ⟨3099, by rfl⟩) R6199
theorem R8359 : Reach 8359 := rs (se 1 (by rfl) ⟨6269, by rfl⟩) R12539
theorem R41143 : Reach 41143 := rs (se 1 (by rfl) ⟨30857, by rfl⟩) R61715
theorem R8487 : Reach 8487 := rs (se 1 (by rfl) ⟨6365, by rfl⟩) R12731
theorem R8619 : Reach 8619 := rs (se 1 (by rfl) ⟨6464, by rfl⟩) R12929
theorem R8653 : Reach 8653 := rs (se 3 (by rfl) ⟨1622, by rfl⟩) R3245
theorem R8657 : Reach 8657 := rs (se 2 (by rfl) ⟨3246, by rfl⟩) R6493
theorem R8665 : Reach 8665 := rs (se 2 (by rfl) ⟨3249, by rfl⟩) R6499
theorem R8669 : Reach 8669 := rs (se 3 (by rfl) ⟨1625, by rfl⟩) R3251
theorem R8673 : Reach 8673 := rs (se 2 (by rfl) ⟨3252, by rfl⟩) R6505
theorem R8693 : Reach 8693 := rs (se 5 (by rfl) ⟨407, by rfl⟩) R815
theorem R8707 : Reach 8707 := rs (se 1 (by rfl) ⟨6530, by rfl⟩) R13061
theorem R8709 : Reach 8709 := rs (se 4 (by rfl) ⟨816, by rfl⟩) R1633
theorem R8713 : Reach 8713 := rs (se 2 (by rfl) ⟨3267, by rfl⟩) R6535
theorem R8715 : Reach 8715 := rs (se 1 (by rfl) ⟨6536, by rfl⟩) R13073
theorem R8723 : Reach 8723 := rs (se 1 (by rfl) ⟨6542, by rfl⟩) R13085
theorem R8727 : Reach 8727 := rs (se 1 (by rfl) ⟨6545, by rfl⟩) R13091
theorem R8729 : Reach 8729 := rs (se 2 (by rfl) ⟨3273, by rfl⟩) R6547
theorem R8733 : Reach 8733 := rs (se 3 (by rfl) ⟨1637, by rfl⟩) R3275
theorem R8735 : Reach 8735 := rs (se 1 (by rfl) ⟨6551, by rfl⟩) R13103
theorem R8737 : Reach 8737 := rs (se 2 (by rfl) ⟨3276, by rfl⟩) R6553
theorem R8769 : Reach 8769 := rs (se 2 (by rfl) ⟨3288, by rfl⟩) R6577
theorem R8771 : Reach 8771 := rs (se 1 (by rfl) ⟨6578, by rfl⟩) R13157
theorem R8773 : Reach 8773 := rs (se 4 (by rfl) ⟨822, by rfl⟩) R1645
theorem R8775 : Reach 8775 := rs (se 1 (by rfl) ⟨6581, by rfl⟩) R13163
theorem R8777 : Reach 8777 := rs (se 2 (by rfl) ⟨3291, by rfl⟩) R6583
theorem R8779 : Reach 8779 := rs (se 1 (by rfl) ⟨6584, by rfl⟩) R13169
theorem R8781 : Reach 8781 := rs (se 3 (by rfl) ⟨1646, by rfl⟩) R3293
theorem R8785 : Reach 8785 := rs (se 2 (by rfl) ⟨3294, by rfl⟩) R6589
theorem R8787 : Reach 8787 := rs (se 1 (by rfl) ⟨6590, by rfl⟩) R13181
theorem R8803 : Reach 8803 := rs (se 1 (by rfl) ⟨6602, by rfl⟩) R13205
theorem R8805 : Reach 8805 := rs (se 4 (by rfl) ⟨825, by rfl⟩) R1651
theorem R8825 : Reach 8825 := rs (se 2 (by rfl) ⟨3309, by rfl⟩) R6619
theorem R8841 : Reach 8841 := rs (se 2 (by rfl) ⟨3315, by rfl⟩) R6631
theorem R8853 : Reach 8853 := rs (se 6 (by rfl) ⟨207, by rfl⟩) R415
theorem R8867 : Reach 8867 := rs (se 1 (by rfl) ⟨6650, by rfl⟩) R13301
theorem R139967 : Reach 139967 := rs (se 1 (by rfl) ⟨104975, by rfl⟩) R209951
theorem R8901 : Reach 8901 := rs (se 4 (by rfl) ⟨834, by rfl⟩) R1669
theorem R8909 : Reach 8909 := rs (se 3 (by rfl) ⟨1670, by rfl⟩) R3341
theorem R8921 : Reach 8921 := rs (se 2 (by rfl) ⟨3345, by rfl⟩) R6691
theorem R8933 : Reach 8933 := rs (se 4 (by rfl) ⟨837, by rfl⟩) R1675
theorem R74479 : Reach 74479 := rs (se 1 (by rfl) ⟨55859, by rfl⟩) R111719
theorem R8951 : Reach 8951 := rs (se 1 (by rfl) ⟨6713, by rfl⟩) R13427
theorem R8953 : Reach 8953 := rs (se 2 (by rfl) ⟨3357, by rfl⟩) R6715
theorem R8957 : Reach 8957 := rs (se 3 (by rfl) ⟨1679, by rfl⟩) R3359
theorem R8967 : Reach 8967 := rs (se 1 (by rfl) ⟨6725, by rfl⟩) R13451
theorem R8971 : Reach 8971 := rs (se 1 (by rfl) ⟨6728, by rfl⟩) R13457
theorem R8991 : Reach 8991 := rs (se 1 (by rfl) ⟨6743, by rfl⟩) R13487
theorem R9001 : Reach 9001 := rs (se 2 (by rfl) ⟨3375, by rfl⟩) R6751
theorem R9021 : Reach 9021 := rs (se 3 (by rfl) ⟨1691, by rfl⟩) R3383
theorem R9089 : Reach 9089 := rs (se 2 (by rfl) ⟨3408, by rfl⟩) R6817
theorem R9091 : Reach 9091 := rs (se 1 (by rfl) ⟨6818, by rfl⟩) R13637
theorem R9093 : Reach 9093 := rs (se 4 (by rfl) ⟨852, by rfl⟩) R1705
theorem R9095 : Reach 9095 := rs (se 1 (by rfl) ⟨6821, by rfl⟩) R13643
theorem R9263 : Reach 9263 := rs (se 1 (by rfl) ⟨6947, by rfl⟩) R13895
theorem R1190207 : Reach 1190207 := rs (se 1 (by rfl) ⟨892655, by rfl⟩) R1785311
theorem R144341 : Reach 144341 := rs (se 7 (by rfl) ⟨1691, by rfl⟩) R3383
theorem R16529 : Reach 16529 := rs (se 2 (by rfl) ⟨6198, by rfl⟩) R12397
theorem R16559 : Reach 16559 := rs (se 1 (by rfl) ⟨12419, by rfl⟩) R24839
theorem R17051 : Reach 17051 := rs (se 1 (by rfl) ⟨12788, by rfl⟩) R25577
theorem R17131 : Reach 17131 := rs (se 1 (by rfl) ⟨12848, by rfl⟩) R25697
theorem R17183 : Reach 17183 := rs (se 1 (by rfl) ⟨12887, by rfl⟩) R25775
theorem R17239 : Reach 17239 := rs (se 1 (by rfl) ⟨12929, by rfl⟩) R25859
theorem R17249 : Reach 17249 := rs (se 2 (by rfl) ⟨6468, by rfl⟩) R12937
theorem R17315 : Reach 17315 := rs (se 1 (by rfl) ⟨12986, by rfl⟩) R25973
theorem R17327 : Reach 17327 := rs (se 1 (by rfl) ⟨12995, by rfl⟩) R25991
theorem R17329 : Reach 17329 := rs (se 2 (by rfl) ⟨6498, by rfl⟩) R12997
theorem R17333 : Reach 17333 := rs (se 5 (by rfl) ⟨812, by rfl⟩) R1625
theorem R17345 : Reach 17345 := rs (se 2 (by rfl) ⟨6504, by rfl⟩) R13009
theorem R17347 : Reach 17347 := rs (se 1 (by rfl) ⟨13010, by rfl⟩) R26021
theorem R17371 : Reach 17371 := rs (se 1 (by rfl) ⟨13028, by rfl⟩) R26057
theorem R17393 : Reach 17393 := rs (se 2 (by rfl) ⟨6522, by rfl⟩) R13045
theorem R17417 : Reach 17417 := rs (se 2 (by rfl) ⟨6531, by rfl⟩) R13063
theorem R17453 : Reach 17453 := rs (se 3 (by rfl) ⟨3272, by rfl⟩) R6545
theorem R17459 : Reach 17459 := rs (se 1 (by rfl) ⟨13094, by rfl⟩) R26189
theorem R17471 : Reach 17471 := rs (se 1 (by rfl) ⟨13103, by rfl⟩) R26207
theorem R17549 : Reach 17549 := rs (se 3 (by rfl) ⟨3290, by rfl⟩) R6581
theorem R17555 : Reach 17555 := rs (se 1 (by rfl) ⟨13166, by rfl⟩) R26333
theorem R17561 : Reach 17561 := rs (se 2 (by rfl) ⟨6585, by rfl⟩) R13171
theorem R17573 : Reach 17573 := rs (se 4 (by rfl) ⟨1647, by rfl⟩) R3295
theorem R17579 : Reach 17579 := rs (se 1 (by rfl) ⟨13184, by rfl⟩) R26369
theorem R17599 : Reach 17599 := rs (se 1 (by rfl) ⟨13199, by rfl⟩) R26399
theorem R17651 : Reach 17651 := rs (se 1 (by rfl) ⟨13238, by rfl⟩) R26477
theorem R17717 : Reach 17717 := rs (se 5 (by rfl) ⟨830, by rfl⟩) R1661
theorem R17729 : Reach 17729 := rs (se 2 (by rfl) ⟨6648, by rfl⟩) R13297
theorem R17813 : Reach 17813 := rs (se 6 (by rfl) ⟨417, by rfl⟩) R835
theorem R17843 : Reach 17843 := rs (se 1 (by rfl) ⟨13382, by rfl⟩) R26765
theorem R17849 : Reach 17849 := rs (se 2 (by rfl) ⟨6693, by rfl⟩) R13387
theorem R17873 : Reach 17873 := rs (se 2 (by rfl) ⟨6702, by rfl⟩) R13405
theorem R17945 : Reach 17945 := rs (se 2 (by rfl) ⟨6729, by rfl⟩) R13459
theorem R17951 : Reach 17951 := rs (se 1 (by rfl) ⟨13463, by rfl⟩) R26927
theorem R18041 : Reach 18041 := rs (se 2 (by rfl) ⟨6765, by rfl⟩) R13531
theorem R18095 : Reach 18095 := rs (se 1 (by rfl) ⟨13571, by rfl⟩) R27143
theorem R18179 : Reach 18179 := rs (se 1 (by rfl) ⟨13634, by rfl⟩) R27269
theorem R18191 : Reach 18191 := rs (se 1 (by rfl) ⟨13643, by rfl⟩) R27287
theorem R18395 : Reach 18395 := rs (se 1 (by rfl) ⟨13796, by rfl⟩) R27593
theorem R18527 : Reach 18527 := rs (se 1 (by rfl) ⟨13895, by rfl⟩) R27791
theorem R18559 : Reach 18559 := rs (se 1 (by rfl) ⟨13919, by rfl⟩) R27839
theorem R19055 : Reach 19055 := rs (se 1 (by rfl) ⟨14291, by rfl⟩) R28583
theorem R731 : Reach 731 := rs (se 1 (by rfl) ⟨548, by rfl⟩) R1097
theorem R737 : Reach 737 := rs (se 2 (by rfl) ⟨276, by rfl⟩) R553
theorem R751 : Reach 751 := rs (se 1 (by rfl) ⟨563, by rfl⟩) R1127
theorem R99305 : Reach 99305 := rs (se 2 (by rfl) ⟨37239, by rfl⟩) R74479
theorem R1441 : Reach 1441 := rs (se 2 (by rfl) ⟨540, by rfl⟩) R1081
theorem R1449 : Reach 1449 := rs (se 2 (by rfl) ⟨543, by rfl⟩) R1087
theorem R1451 : Reach 1451 := rs (se 1 (by rfl) ⟨1088, by rfl⟩) R2177
theorem R1455 : Reach 1455 := rs (se 1 (by rfl) ⟨1091, by rfl⟩) R2183
theorem R1463 : Reach 1463 := rs (se 1 (by rfl) ⟨1097, by rfl⟩) R2195
theorem R1467 : Reach 1467 := rs (se 1 (by rfl) ⟨1100, by rfl⟩) R2201
theorem R1475 : Reach 1475 := rs (se 1 (by rfl) ⟨1106, by rfl⟩) R2213
theorem R1483 : Reach 1483 := rs (se 1 (by rfl) ⟨1112, by rfl⟩) R2225
theorem R1503 : Reach 1503 := rs (se 1 (by rfl) ⟨1127, by rfl⟩) R2255
theorem R1515 : Reach 1515 := rs (se 1 (by rfl) ⟨1136, by rfl⟩) R2273
theorem R2883 : Reach 2883 := rs (se 1 (by rfl) ⟨2162, by rfl⟩) R4325
theorem R2889 : Reach 2889 := rs (se 2 (by rfl) ⟨1083, by rfl⟩) R2167
theorem R2897 : Reach 2897 := rs (se 2 (by rfl) ⟨1086, by rfl⟩) R2173
theorem R2899 : Reach 2899 := rs (se 1 (by rfl) ⟨2174, by rfl⟩) R4349
theorem R2903 : Reach 2903 := rs (se 1 (by rfl) ⟨2177, by rfl⟩) R4355
theorem R2907 : Reach 2907 := rs (se 1 (by rfl) ⟨2180, by rfl⟩) R4361
theorem R2911 : Reach 2911 := rs (se 1 (by rfl) ⟨2183, by rfl⟩) R4367
theorem R2923 : Reach 2923 := rs (se 1 (by rfl) ⟨2192, by rfl⟩) R4385
theorem R2925 : Reach 2925 := rs (se 3 (by rfl) ⟨548, by rfl⟩) R1097
theorem R2935 : Reach 2935 := rs (se 1 (by rfl) ⟨2201, by rfl⟩) R4403
theorem R2949 : Reach 2949 := rs (se 4 (by rfl) ⟨276, by rfl⟩) R553
theorem R2955 : Reach 2955 := rs (se 1 (by rfl) ⟨2216, by rfl⟩) R4433
theorem R2967 : Reach 2967 := rs (se 1 (by rfl) ⟨2225, by rfl⟩) R4451
theorem R2969 : Reach 2969 := rs (se 2 (by rfl) ⟨1113, by rfl⟩) R2227
theorem R2977 : Reach 2977 := rs (se 2 (by rfl) ⟨1116, by rfl⟩) R2233
theorem R2983 : Reach 2983 := rs (se 1 (by rfl) ⟨2237, by rfl⟩) R4475
theorem R2985 : Reach 2985 := rs (se 2 (by rfl) ⟨1119, by rfl⟩) R2239
theorem R3005 : Reach 3005 := rs (se 3 (by rfl) ⟨563, by rfl⟩) R1127
theorem R3031 : Reach 3031 := rs (se 1 (by rfl) ⟨2273, by rfl⟩) R4547
theorem R5765 : Reach 5765 := rs (se 4 (by rfl) ⟨540, by rfl⟩) R1081
theorem R5771 : Reach 5771 := rs (se 1 (by rfl) ⟨4328, by rfl⟩) R8657
theorem R5777 : Reach 5777 := rs (se 2 (by rfl) ⟨2166, by rfl⟩) R4333
theorem R5779 : Reach 5779 := rs (se 1 (by rfl) ⟨4334, by rfl⟩) R8669
theorem R5795 : Reach 5795 := rs (se 1 (by rfl) ⟨4346, by rfl⟩) R8693
theorem R5797 : Reach 5797 := rs (se 4 (by rfl) ⟨543, by rfl⟩) R1087
theorem R5805 : Reach 5805 := rs (se 3 (by rfl) ⟨1088, by rfl⟩) R2177
theorem R5815 : Reach 5815 := rs (se 1 (by rfl) ⟨4361, by rfl⟩) R8723
theorem R5817 : Reach 5817 := rs (se 2 (by rfl) ⟨2181, by rfl⟩) R4363
theorem R5819 : Reach 5819 := rs (se 1 (by rfl) ⟨4364, by rfl⟩) R8729
theorem R5821 : Reach 5821 := rs (se 3 (by rfl) ⟨1091, by rfl⟩) R2183
theorem R5823 : Reach 5823 := rs (se 1 (by rfl) ⟨4367, by rfl⟩) R8735
theorem R5847 : Reach 5847 := rs (se 1 (by rfl) ⟨4385, by rfl⟩) R8771
theorem R5849 : Reach 5849 := rs (se 2 (by rfl) ⟨2193, by rfl⟩) R4387
theorem R5851 : Reach 5851 := rs (se 1 (by rfl) ⟨4388, by rfl⟩) R8777
theorem R5853 : Reach 5853 := rs (se 3 (by rfl) ⟨1097, by rfl⟩) R2195
theorem R5857 : Reach 5857 := rs (se 2 (by rfl) ⟨2196, by rfl⟩) R4393
theorem R5869 : Reach 5869 := rs (se 3 (by rfl) ⟨1100, by rfl⟩) R2201
theorem R5883 : Reach 5883 := rs (se 1 (by rfl) ⟨4412, by rfl⟩) R8825
theorem R5901 : Reach 5901 := rs (se 3 (by rfl) ⟨1106, by rfl⟩) R2213
theorem R5905 : Reach 5905 := rs (se 2 (by rfl) ⟨2214, by rfl⟩) R4429
theorem R5911 : Reach 5911 := rs (se 1 (by rfl) ⟨4433, by rfl⟩) R8867
theorem R5933 : Reach 5933 := rs (se 3 (by rfl) ⟨1112, by rfl⟩) R2225
theorem R5937 : Reach 5937 := rs (se 2 (by rfl) ⟨2226, by rfl⟩) R4453
theorem R5939 : Reach 5939 := rs (se 1 (by rfl) ⟨4454, by rfl⟩) R8909
theorem R5947 : Reach 5947 := rs (se 1 (by rfl) ⟨4460, by rfl⟩) R8921
theorem R5955 : Reach 5955 := rs (se 1 (by rfl) ⟨4466, by rfl⟩) R8933
theorem R5967 : Reach 5967 := rs (se 1 (by rfl) ⟨4475, by rfl⟩) R8951
theorem R5971 : Reach 5971 := rs (se 1 (by rfl) ⟨4478, by rfl⟩) R8957
theorem R6013 : Reach 6013 := rs (se 3 (by rfl) ⟨1127, by rfl⟩) R2255
theorem R6059 : Reach 6059 := rs (se 1 (by rfl) ⟨4544, by rfl⟩) R9089
theorem R6061 : Reach 6061 := rs (se 3 (by rfl) ⟨1136, by rfl⟩) R2273
theorem R6063 : Reach 6063 := rs (se 1 (by rfl) ⟨4547, by rfl⟩) R9095
theorem R6175 : Reach 6175 := rs (se 1 (by rfl) ⟨4631, by rfl⟩) R9263
theorem R793471 : Reach 793471 := rs (se 1 (by rfl) ⟨595103, by rfl⟩) R1190207
theorem R11019 : Reach 11019 := rs (se 1 (by rfl) ⟨8264, by rfl⟩) R16529
theorem R11039 : Reach 11039 := rs (se 1 (by rfl) ⟨8279, by rfl⟩) R16559
theorem R11145 : Reach 11145 := rs (se 2 (by rfl) ⟨4179, by rfl⟩) R8359
theorem R11367 : Reach 11367 := rs (se 1 (by rfl) ⟨8525, by rfl⟩) R17051
theorem R11455 : Reach 11455 := rs (se 1 (by rfl) ⟨8591, by rfl⟩) R17183
theorem R11499 : Reach 11499 := rs (se 1 (by rfl) ⟨8624, by rfl⟩) R17249
theorem R11533 : Reach 11533 := rs (se 3 (by rfl) ⟨2162, by rfl⟩) R4325
theorem R11537 : Reach 11537 := rs (se 2 (by rfl) ⟨4326, by rfl⟩) R8653
theorem R11543 : Reach 11543 := rs (se 1 (by rfl) ⟨8657, by rfl⟩) R17315
theorem R11551 : Reach 11551 := rs (se 1 (by rfl) ⟨8663, by rfl⟩) R17327
theorem R11553 : Reach 11553 := rs (se 2 (by rfl) ⟨4332, by rfl⟩) R8665
theorem R11555 : Reach 11555 := rs (se 1 (by rfl) ⟨8666, by rfl⟩) R17333
theorem R11557 : Reach 11557 := rs (se 4 (by rfl) ⟨1083, by rfl⟩) R2167
theorem R11563 : Reach 11563 := rs (se 1 (by rfl) ⟨8672, by rfl⟩) R17345
theorem R11589 : Reach 11589 := rs (se 4 (by rfl) ⟨1086, by rfl⟩) R2173
theorem R11595 : Reach 11595 := rs (se 1 (by rfl) ⟨8696, by rfl⟩) R17393
theorem R11597 : Reach 11597 := rs (se 3 (by rfl) ⟨2174, by rfl⟩) R4349
theorem R11609 : Reach 11609 := rs (se 2 (by rfl) ⟨4353, by rfl⟩) R8707
theorem R11611 : Reach 11611 := rs (se 1 (by rfl) ⟨8708, by rfl⟩) R17417
theorem R11613 : Reach 11613 := rs (se 3 (by rfl) ⟨2177, by rfl⟩) R4355
theorem R11617 : Reach 11617 := rs (se 2 (by rfl) ⟨4356, by rfl⟩) R8713
theorem R11629 : Reach 11629 := rs (se 3 (by rfl) ⟨2180, by rfl⟩) R4361
theorem R11635 : Reach 11635 := rs (se 1 (by rfl) ⟨8726, by rfl⟩) R17453
theorem R11639 : Reach 11639 := rs (se 1 (by rfl) ⟨8729, by rfl⟩) R17459
theorem R11645 : Reach 11645 := rs (se 3 (by rfl) ⟨2183, by rfl⟩) R4367
theorem R11647 : Reach 11647 := rs (se 1 (by rfl) ⟨8735, by rfl⟩) R17471
theorem R11649 : Reach 11649 := rs (se 2 (by rfl) ⟨4368, by rfl⟩) R8737
theorem R11693 : Reach 11693 := rs (se 3 (by rfl) ⟨2192, by rfl⟩) R4385
theorem R11697 : Reach 11697 := rs (se 2 (by rfl) ⟨4386, by rfl⟩) R8773
theorem R11699 : Reach 11699 := rs (se 1 (by rfl) ⟨8774, by rfl⟩) R17549
theorem R11701 : Reach 11701 := rs (se 5 (by rfl) ⟨548, by rfl⟩) R1097
theorem R11703 : Reach 11703 := rs (se 1 (by rfl) ⟨8777, by rfl⟩) R17555
theorem R11705 : Reach 11705 := rs (se 2 (by rfl) ⟨4389, by rfl⟩) R8779
theorem R11707 : Reach 11707 := rs (se 1 (by rfl) ⟨8780, by rfl⟩) R17561
theorem R11713 : Reach 11713 := rs (se 2 (by rfl) ⟨4392, by rfl⟩) R8785
theorem R11715 : Reach 11715 := rs (se 1 (by rfl) ⟨8786, by rfl⟩) R17573
theorem R11719 : Reach 11719 := rs (se 1 (by rfl) ⟨8789, by rfl⟩) R17579
theorem R11737 : Reach 11737 := rs (se 2 (by rfl) ⟨4401, by rfl⟩) R8803
theorem R11741 : Reach 11741 := rs (se 3 (by rfl) ⟨2201, by rfl⟩) R4403
theorem R11767 : Reach 11767 := rs (se 1 (by rfl) ⟨8825, by rfl⟩) R17651
theorem R11797 : Reach 11797 := rs (se 6 (by rfl) ⟨276, by rfl⟩) R553
theorem R11811 : Reach 11811 := rs (se 1 (by rfl) ⟨8858, by rfl⟩) R17717
theorem R11819 : Reach 11819 := rs (se 1 (by rfl) ⟨8864, by rfl⟩) R17729
theorem R11821 : Reach 11821 := rs (se 3 (by rfl) ⟨2216, by rfl⟩) R4433
theorem R11869 : Reach 11869 := rs (se 3 (by rfl) ⟨2225, by rfl⟩) R4451
theorem R11875 : Reach 11875 := rs (se 1 (by rfl) ⟨8906, by rfl⟩) R17813
theorem R11877 : Reach 11877 := rs (se 4 (by rfl) ⟨1113, by rfl⟩) R2227
theorem R11895 : Reach 11895 := rs (se 1 (by rfl) ⟨8921, by rfl⟩) R17843
theorem R11899 : Reach 11899 := rs (se 1 (by rfl) ⟨8924, by rfl⟩) R17849
theorem R11909 : Reach 11909 := rs (se 4 (by rfl) ⟨1116, by rfl⟩) R2233
theorem R11915 : Reach 11915 := rs (se 1 (by rfl) ⟨8936, by rfl⟩) R17873
theorem R11933 : Reach 11933 := rs (se 3 (by rfl) ⟨2237, by rfl⟩) R4475
theorem R11937 : Reach 11937 := rs (se 2 (by rfl) ⟨4476, by rfl⟩) R8953
theorem R11941 : Reach 11941 := rs (se 4 (by rfl) ⟨1119, by rfl⟩) R2239
theorem R11961 : Reach 11961 := rs (se 2 (by rfl) ⟨4485, by rfl⟩) R8971
theorem R11963 : Reach 11963 := rs (se 1 (by rfl) ⟨8972, by rfl⟩) R17945
theorem R11967 : Reach 11967 := rs (se 1 (by rfl) ⟨8975, by rfl⟩) R17951
theorem R12001 : Reach 12001 := rs (se 2 (by rfl) ⟨4500, by rfl⟩) R9001
theorem R12021 : Reach 12021 := rs (se 5 (by rfl) ⟨563, by rfl⟩) R1127
theorem R12027 : Reach 12027 := rs (se 1 (by rfl) ⟨9020, by rfl⟩) R18041
theorem R12063 : Reach 12063 := rs (se 1 (by rfl) ⟨9047, by rfl⟩) R18095
theorem R12119 : Reach 12119 := rs (se 1 (by rfl) ⟨9089, by rfl⟩) R18179
theorem R12121 : Reach 12121 := rs (se 2 (by rfl) ⟨4545, by rfl⟩) R9091
theorem R12125 : Reach 12125 := rs (se 3 (by rfl) ⟨2273, by rfl⟩) R4547
theorem R12127 : Reach 12127 := rs (se 1 (by rfl) ⟨9095, by rfl⟩) R18191
theorem R12263 : Reach 12263 := rs (se 1 (by rfl) ⟨9197, by rfl⟩) R18395
theorem R12351 : Reach 12351 := rs (se 1 (by rfl) ⟨9263, by rfl⟩) R18527
theorem R12703 : Reach 12703 := rs (se 1 (by rfl) ⟨9527, by rfl⟩) R19055
theorem R45683 : Reach 45683 := rs (se 1 (by rfl) ⟨34262, by rfl⟩) R68525
theorem R46133 : Reach 46133 := rs (se 5 (by rfl) ⟨2162, by rfl⟩) R4325
theorem R46295 : Reach 46295 := rs (se 1 (by rfl) ⟨34721, by rfl⟩) R69443
theorem R46595 : Reach 46595 := rs (se 1 (by rfl) ⟨34946, by rfl⟩) R69893
theorem R46655 : Reach 46655 := rs (se 1 (by rfl) ⟨34991, by rfl⟩) R69983
theorem R47749 : Reach 47749 := rs (se 4 (by rfl) ⟨4476, by rfl⟩) R8953
theorem R47951 : Reach 47951 := rs (se 1 (by rfl) ⟨35963, by rfl⟩) R71927
theorem R48113 : Reach 48113 := rs (se 2 (by rfl) ⟨18042, by rfl⟩) R36085
theorem R48509 : Reach 48509 := rs (se 3 (by rfl) ⟨9095, by rfl⟩) R18191
theorem R49409 : Reach 49409 := rs (se 2 (by rfl) ⟨18528, by rfl⟩) R37057
theorem R3066173 : Reach 3066173 := rs (se 3 (by rfl) ⟨574907, by rfl⟩) R1149815
theorem R54857 : Reach 54857 := rs (se 2 (by rfl) ⟨20571, by rfl⟩) R41143
theorem R22319 : Reach 22319 := rs (se 1 (by rfl) ⟨16739, by rfl⟩) R33479
theorem R22639 : Reach 22639 := rs (se 1 (by rfl) ⟨16979, by rfl⟩) R33959
theorem R22715 : Reach 22715 := rs (se 1 (by rfl) ⟨17036, by rfl⟩) R34073
theorem R22841 : Reach 22841 := rs (se 2 (by rfl) ⟨8565, by rfl⟩) R17131
theorem R22985 : Reach 22985 := rs (se 2 (by rfl) ⟨8619, by rfl⟩) R17239
theorem R88555 : Reach 88555 := rs (se 1 (by rfl) ⟨66416, by rfl⟩) R132833
theorem R88559 : Reach 88559 := rs (se 1 (by rfl) ⟨66419, by rfl⟩) R132839
theorem R23075 : Reach 23075 := rs (se 1 (by rfl) ⟨17306, by rfl⟩) R34613
theorem R23105 : Reach 23105 := rs (se 2 (by rfl) ⟨8664, by rfl⟩) R17329
theorem R23129 : Reach 23129 := rs (se 2 (by rfl) ⟨8673, by rfl⟩) R17347
theorem R23147 : Reach 23147 := rs (se 1 (by rfl) ⟨17360, by rfl⟩) R34721
theorem R23161 : Reach 23161 := rs (se 2 (by rfl) ⟨8685, by rfl⟩) R17371
theorem R23219 : Reach 23219 := rs (se 1 (by rfl) ⟨17414, by rfl⟩) R34829
theorem R23269 : Reach 23269 := rs (se 4 (by rfl) ⟨2181, by rfl⟩) R4363
theorem R23327 : Reach 23327 := rs (se 1 (by rfl) ⟨17495, by rfl⟩) R34991
theorem R23429 : Reach 23429 := rs (se 4 (by rfl) ⟨2196, by rfl⟩) R4393
theorem R23465 : Reach 23465 := rs (se 2 (by rfl) ⟨8799, by rfl⟩) R17599
theorem R23627 : Reach 23627 := rs (se 1 (by rfl) ⟨17720, by rfl⟩) R35441
theorem R23831 : Reach 23831 := rs (se 1 (by rfl) ⟨17873, by rfl⟩) R35747
theorem R23885 : Reach 23885 := rs (se 3 (by rfl) ⟨4478, by rfl⟩) R8957
theorem R23915 : Reach 23915 := rs (se 1 (by rfl) ⟨17936, by rfl⟩) R35873
theorem R23935 : Reach 23935 := rs (se 1 (by rfl) ⟨17951, by rfl⟩) R35903
theorem R23975 : Reach 23975 := rs (se 1 (by rfl) ⟨17981, by rfl⟩) R35963
theorem R24245 : Reach 24245 := rs (se 5 (by rfl) ⟨1136, by rfl⟩) R2273
theorem R24263 : Reach 24263 := rs (se 1 (by rfl) ⟨18197, by rfl⟩) R36395
theorem R24745 : Reach 24745 := rs (se 2 (by rfl) ⟨9279, by rfl⟩) R18559
theorem R90557 : Reach 90557 := rs (se 3 (by rfl) ⟨16979, by rfl⟩) R33959
theorem R93109 : Reach 93109 := rs (se 5 (by rfl) ⟨4364, by rfl⟩) R8729
theorem R93311 : Reach 93311 := rs (se 1 (by rfl) ⟨69983, by rfl⟩) R139967
theorem R191909 : Reach 191909 := rs (se 4 (by rfl) ⟨17991, by rfl⟩) R35983
theorem R93649 : Reach 93649 := rs (se 2 (by rfl) ⟨35118, by rfl⟩) R70237
theorem R95741 : Reach 95741 := rs (se 3 (by rfl) ⟨17951, by rfl⟩) R35903
theorem R96227 : Reach 96227 := rs (se 1 (by rfl) ⟨72170, by rfl⟩) R144341
theorem R32939 : Reach 32939 := rs (se 1 (by rfl) ⟨24704, by rfl⟩) R49409
theorem R32993 : Reach 32993 := rs (se 2 (by rfl) ⟨12372, by rfl⟩) R24745
theorem R487 : Reach 487 := rs (se 1 (by rfl) ⟨365, by rfl⟩) R731
theorem R491 : Reach 491 := rs (se 1 (by rfl) ⟨368, by rfl⟩) R737
theorem R66203 : Reach 66203 := rs (se 1 (by rfl) ⟨49652, by rfl⟩) R99305
theorem R967 : Reach 967 := rs (se 1 (by rfl) ⟨725, by rfl⟩) R1451
theorem R975 : Reach 975 := rs (se 1 (by rfl) ⟨731, by rfl⟩) R1463
theorem R983 : Reach 983 := rs (se 1 (by rfl) ⟨737, by rfl⟩) R1475
theorem R1001 : Reach 1001 := rs (se 2 (by rfl) ⟨375, by rfl⟩) R751
theorem R1921 : Reach 1921 := rs (se 2 (by rfl) ⟨720, by rfl⟩) R1441
theorem R1931 : Reach 1931 := rs (se 1 (by rfl) ⟨1448, by rfl⟩) R2897
theorem R1935 : Reach 1935 := rs (se 1 (by rfl) ⟨1451, by rfl⟩) R2903
theorem R1949 : Reach 1949 := rs (se 3 (by rfl) ⟨365, by rfl⟩) R731
theorem R1965 : Reach 1965 := rs (se 3 (by rfl) ⟨368, by rfl⟩) R737
theorem R1977 : Reach 1977 := rs (se 2 (by rfl) ⟨741, by rfl⟩) R1483
theorem R1979 : Reach 1979 := rs (se 1 (by rfl) ⟨1484, by rfl⟩) R2969
theorem R2003 : Reach 2003 := rs (se 1 (by rfl) ⟨1502, by rfl⟩) R3005
theorem R36571 : Reach 36571 := rs (se 1 (by rfl) ⟨27428, by rfl⟩) R54857
theorem R3843 : Reach 3843 := rs (se 1 (by rfl) ⟨2882, by rfl⟩) R5765
theorem R3847 : Reach 3847 := rs (se 1 (by rfl) ⟨2885, by rfl⟩) R5771
theorem R3851 : Reach 3851 := rs (se 1 (by rfl) ⟨2888, by rfl⟩) R5777
theorem R3863 : Reach 3863 := rs (se 1 (by rfl) ⟨2897, by rfl⟩) R5795
theorem R3865 : Reach 3865 := rs (se 2 (by rfl) ⟨1449, by rfl⟩) R2899
theorem R3869 : Reach 3869 := rs (se 3 (by rfl) ⟨725, by rfl⟩) R1451
theorem R3879 : Reach 3879 := rs (se 1 (by rfl) ⟨2909, by rfl⟩) R5819
theorem R3881 : Reach 3881 := rs (se 2 (by rfl) ⟨1455, by rfl⟩) R2911
theorem R3897 : Reach 3897 := rs (se 2 (by rfl) ⟨1461, by rfl⟩) R2923
theorem R3899 : Reach 3899 := rs (se 1 (by rfl) ⟨2924, by rfl⟩) R5849
theorem R3901 : Reach 3901 := rs (se 3 (by rfl) ⟨731, by rfl⟩) R1463
theorem R3913 : Reach 3913 := rs (se 2 (by rfl) ⟨1467, by rfl⟩) R2935
theorem R3933 : Reach 3933 := rs (se 3 (by rfl) ⟨737, by rfl⟩) R1475
theorem R3955 : Reach 3955 := rs (se 1 (by rfl) ⟨2966, by rfl⟩) R5933
theorem R3959 : Reach 3959 := rs (se 1 (by rfl) ⟨2969, by rfl⟩) R5939
theorem R3969 : Reach 3969 := rs (se 2 (by rfl) ⟨1488, by rfl⟩) R2977
theorem R3977 : Reach 3977 := rs (se 2 (by rfl) ⟨1491, by rfl⟩) R2983
theorem R4005 : Reach 4005 := rs (se 4 (by rfl) ⟨375, by rfl⟩) R751
theorem R4039 : Reach 4039 := rs (se 1 (by rfl) ⟨3029, by rfl⟩) R6059
theorem R4041 : Reach 4041 := rs (se 2 (by rfl) ⟨1515, by rfl⟩) R3031
theorem R7359 : Reach 7359 := rs (se 1 (by rfl) ⟨5519, by rfl⟩) R11039
theorem R7685 : Reach 7685 := rs (se 4 (by rfl) ⟨720, by rfl⟩) R1441
theorem R7691 : Reach 7691 := rs (se 1 (by rfl) ⟨5768, by rfl⟩) R11537
theorem R7695 : Reach 7695 := rs (se 1 (by rfl) ⟨5771, by rfl⟩) R11543
theorem R7703 : Reach 7703 := rs (se 1 (by rfl) ⟨5777, by rfl⟩) R11555
theorem R7705 : Reach 7705 := rs (se 2 (by rfl) ⟨2889, by rfl⟩) R5779
theorem R7725 : Reach 7725 := rs (se 3 (by rfl) ⟨1448, by rfl⟩) R2897
theorem R7729 : Reach 7729 := rs (se 2 (by rfl) ⟨2898, by rfl⟩) R5797
theorem R7731 : Reach 7731 := rs (se 1 (by rfl) ⟨5798, by rfl⟩) R11597
theorem R7739 : Reach 7739 := rs (se 1 (by rfl) ⟨5804, by rfl⟩) R11609
theorem R7741 : Reach 7741 := rs (se 3 (by rfl) ⟨1451, by rfl⟩) R2903
theorem R7753 : Reach 7753 := rs (se 2 (by rfl) ⟨2907, by rfl⟩) R5815
theorem R7759 : Reach 7759 := rs (se 1 (by rfl) ⟨5819, by rfl⟩) R11639
theorem R7761 : Reach 7761 := rs (se 2 (by rfl) ⟨2910, by rfl⟩) R5821
theorem R7763 : Reach 7763 := rs (se 1 (by rfl) ⟨5822, by rfl⟩) R11645
theorem R7795 : Reach 7795 := rs (se 1 (by rfl) ⟨5846, by rfl⟩) R11693
theorem R7797 : Reach 7797 := rs (se 5 (by rfl) ⟨365, by rfl⟩) R731
theorem R7799 : Reach 7799 := rs (se 1 (by rfl) ⟨5849, by rfl⟩) R11699
theorem R7801 : Reach 7801 := rs (se 2 (by rfl) ⟨2925, by rfl⟩) R5851
theorem R7803 : Reach 7803 := rs (se 1 (by rfl) ⟨5852, by rfl⟩) R11705
theorem R7809 : Reach 7809 := rs (se 2 (by rfl) ⟨2928, by rfl⟩) R5857
theorem R7825 : Reach 7825 := rs (se 2 (by rfl) ⟨2934, by rfl⟩) R5869
theorem R7827 : Reach 7827 := rs (se 1 (by rfl) ⟨5870, by rfl⟩) R11741
theorem R7861 : Reach 7861 := rs (se 5 (by rfl) ⟨368, by rfl⟩) R737
theorem R7873 : Reach 7873 := rs (se 2 (by rfl) ⟨2952, by rfl⟩) R5905
theorem R7879 : Reach 7879 := rs (se 1 (by rfl) ⟨5909, by rfl⟩) R11819
theorem R7881 : Reach 7881 := rs (se 2 (by rfl) ⟨2955, by rfl⟩) R5911
theorem R7909 : Reach 7909 := rs (se 4 (by rfl) ⟨741, by rfl⟩) R1483
theorem R7917 : Reach 7917 := rs (se 3 (by rfl) ⟨1484, by rfl⟩) R2969
theorem R7929 : Reach 7929 := rs (se 2 (by rfl) ⟨2973, by rfl⟩) R5947
theorem R7939 : Reach 7939 := rs (se 1 (by rfl) ⟨5954, by rfl⟩) R11909
theorem R7943 : Reach 7943 := rs (se 1 (by rfl) ⟨5957, by rfl⟩) R11915
theorem R7955 : Reach 7955 := rs (se 1 (by rfl) ⟨5966, by rfl⟩) R11933
theorem R7961 : Reach 7961 := rs (se 2 (by rfl) ⟨2985, by rfl⟩) R5971
theorem R7975 : Reach 7975 := rs (se 1 (by rfl) ⟨5981, by rfl⟩) R11963
theorem R8013 : Reach 8013 := rs (se 3 (by rfl) ⟨1502, by rfl⟩) R3005
theorem R8017 : Reach 8017 := rs (se 2 (by rfl) ⟨3006, by rfl⟩) R6013
theorem R8079 : Reach 8079 := rs (se 1 (by rfl) ⟨6059, by rfl⟩) R12119
theorem R8081 : Reach 8081 := rs (se 2 (by rfl) ⟨3030, by rfl⟩) R6061
theorem R8083 : Reach 8083 := rs (se 1 (by rfl) ⟨6062, by rfl⟩) R12125
theorem R8175 : Reach 8175 := rs (se 1 (by rfl) ⟨6131, by rfl⟩) R12263
theorem R8233 : Reach 8233 := rs (se 2 (by rfl) ⟨3087, by rfl⟩) R6175
theorem R1057961 : Reach 1057961 := rs (se 2 (by rfl) ⟨396735, by rfl⟩) R793471
theorem R2044115 : Reach 2044115 := rs (se 1 (by rfl) ⟨1533086, by rfl⟩) R3066173
theorem R14879 : Reach 14879 := rs (se 1 (by rfl) ⟨11159, by rfl⟩) R22319
theorem R15143 : Reach 15143 := rs (se 1 (by rfl) ⟨11357, by rfl⟩) R22715
theorem R15227 : Reach 15227 := rs (se 1 (by rfl) ⟨11420, by rfl⟩) R22841
theorem R15323 : Reach 15323 := rs (se 1 (by rfl) ⟨11492, by rfl⟩) R22985
theorem R15377 : Reach 15377 := rs (se 2 (by rfl) ⟨5766, by rfl⟩) R11533
theorem R15383 : Reach 15383 := rs (se 1 (by rfl) ⟨11537, by rfl⟩) R23075
theorem R15389 : Reach 15389 := rs (se 3 (by rfl) ⟨2885, by rfl⟩) R5771
theorem R15401 : Reach 15401 := rs (se 2 (by rfl) ⟨5775, by rfl⟩) R11551
theorem R15403 : Reach 15403 := rs (se 1 (by rfl) ⟨11552, by rfl⟩) R23105
theorem R15419 : Reach 15419 := rs (se 1 (by rfl) ⟨11564, by rfl⟩) R23129
theorem R15431 : Reach 15431 := rs (se 1 (by rfl) ⟨11573, by rfl⟩) R23147
theorem R15461 : Reach 15461 := rs (se 4 (by rfl) ⟨1449, by rfl⟩) R2899
theorem R15479 : Reach 15479 := rs (se 1 (by rfl) ⟨11609, by rfl⟩) R23219
theorem R15481 : Reach 15481 := rs (se 2 (by rfl) ⟨5805, by rfl⟩) R11611
theorem R15551 : Reach 15551 := rs (se 1 (by rfl) ⟨11663, by rfl⟩) R23327
theorem R15605 : Reach 15605 := rs (se 5 (by rfl) ⟨731, by rfl⟩) R1463
theorem R15617 : Reach 15617 := rs (se 2 (by rfl) ⟨5856, by rfl⟩) R11713
theorem R15619 : Reach 15619 := rs (se 1 (by rfl) ⟨11714, by rfl⟩) R23429
theorem R15643 : Reach 15643 := rs (se 1 (by rfl) ⟨11732, by rfl⟩) R23465
theorem R15653 : Reach 15653 := rs (se 4 (by rfl) ⟨1467, by rfl⟩) R2935
theorem R15689 : Reach 15689 := rs (se 2 (by rfl) ⟨5883, by rfl⟩) R11767
theorem R15751 : Reach 15751 := rs (se 1 (by rfl) ⟨11813, by rfl⟩) R23627
theorem R15761 : Reach 15761 := rs (se 2 (by rfl) ⟨5910, by rfl⟩) R11821
theorem R15821 : Reach 15821 := rs (se 3 (by rfl) ⟨2966, by rfl⟩) R5933
theorem R15833 : Reach 15833 := rs (se 2 (by rfl) ⟨5937, by rfl⟩) R11875
theorem R15887 : Reach 15887 := rs (se 1 (by rfl) ⟨11915, by rfl⟩) R23831
theorem R15923 : Reach 15923 := rs (se 1 (by rfl) ⟨11942, by rfl⟩) R23885
theorem R15943 : Reach 15943 := rs (se 1 (by rfl) ⟨11957, by rfl⟩) R23915
theorem R15983 : Reach 15983 := rs (se 1 (by rfl) ⟨11987, by rfl⟩) R23975
theorem R16001 : Reach 16001 := rs (se 2 (by rfl) ⟨6000, by rfl⟩) R12001
theorem R16157 : Reach 16157 := rs (se 3 (by rfl) ⟨3029, by rfl⟩) R6059
theorem R16163 : Reach 16163 := rs (se 1 (by rfl) ⟨12122, by rfl⟩) R24245
theorem R16169 : Reach 16169 := rs (se 2 (by rfl) ⟨6063, by rfl⟩) R12127
theorem R16175 : Reach 16175 := rs (se 1 (by rfl) ⟨12131, by rfl⟩) R24263
theorem R246037 : Reach 246037 := rs (se 6 (by rfl) ⟨5766, by rfl⟩) R11533
theorem R16937 : Reach 16937 := rs (se 2 (by rfl) ⟨6351, by rfl⟩) R12703
theorem R118073 : Reach 118073 := rs (se 2 (by rfl) ⟨44277, by rfl⟩) R88555
theorem R124145 : Reach 124145 := rs (se 2 (by rfl) ⟨46554, by rfl⟩) R93109
theorem R59039 : Reach 59039 := rs (se 1 (by rfl) ⟨44279, by rfl⟩) R88559
theorem R124865 : Reach 124865 := rs (se 2 (by rfl) ⟨46824, by rfl⟩) R93649
theorem R60371 : Reach 60371 := rs (se 1 (by rfl) ⟨45278, by rfl⟩) R90557
theorem R62207 : Reach 62207 := rs (se 1 (by rfl) ⟨46655, by rfl⟩) R93311
theorem R127939 : Reach 127939 := rs (se 1 (by rfl) ⟨95954, by rfl⟩) R191909
theorem R30185 : Reach 30185 := rs (se 2 (by rfl) ⟨11319, by rfl⟩) R22639
theorem R30455 : Reach 30455 := rs (se 1 (by rfl) ⟨22841, by rfl⟩) R45683
theorem R30755 : Reach 30755 := rs (se 1 (by rfl) ⟨23066, by rfl⟩) R46133
theorem R30863 : Reach 30863 := rs (se 1 (by rfl) ⟨23147, by rfl⟩) R46295
theorem R30881 : Reach 30881 := rs (se 2 (by rfl) ⟨11580, by rfl⟩) R23161
theorem R63665 : Reach 63665 := rs (se 2 (by rfl) ⟨23874, by rfl⟩) R47749
theorem R30901 : Reach 30901 := rs (se 5 (by rfl) ⟨1448, by rfl⟩) R2897
theorem R31013 : Reach 31013 := rs (se 4 (by rfl) ⟨2907, by rfl⟩) R5815
theorem R31025 : Reach 31025 := rs (se 2 (by rfl) ⟨11634, by rfl⟩) R23269
theorem R63827 : Reach 63827 := rs (se 1 (by rfl) ⟨47870, by rfl⟩) R95741
theorem R31063 : Reach 31063 := rs (se 1 (by rfl) ⟨23297, by rfl⟩) R46595
theorem R31103 : Reach 31103 := rs (se 1 (by rfl) ⟨23327, by rfl⟩) R46655
theorem R31205 : Reach 31205 := rs (se 4 (by rfl) ⟨2925, by rfl⟩) R5851
theorem R64151 : Reach 64151 := rs (se 1 (by rfl) ⟨48113, by rfl⟩) R96227
theorem R31913 : Reach 31913 := rs (se 2 (by rfl) ⟨11967, by rfl⟩) R23935
theorem R31967 : Reach 31967 := rs (se 1 (by rfl) ⟨23975, by rfl⟩) R47951
theorem R32075 : Reach 32075 := rs (se 1 (by rfl) ⟨24056, by rfl⟩) R48113
theorem R32339 : Reach 32339 := rs (se 1 (by rfl) ⟨24254, by rfl⟩) R48509
theorem R327 : Reach 327 := rs (se 1 (by rfl) ⟨245, by rfl⟩) R491
theorem R328049 : Reach 328049 := rs (se 2 (by rfl) ⟨123018, by rfl⟩) R246037
theorem R649 : Reach 649 := rs (se 2 (by rfl) ⟨243, by rfl⟩) R487
theorem R655 : Reach 655 := rs (se 1 (by rfl) ⟨491, by rfl⟩) R983
theorem R667 : Reach 667 := rs (se 1 (by rfl) ⟨500, by rfl⟩) R1001
theorem R1287 : Reach 1287 := rs (se 1 (by rfl) ⟨965, by rfl⟩) R1931
theorem R1289 : Reach 1289 := rs (se 2 (by rfl) ⟨483, by rfl⟩) R967
theorem R1299 : Reach 1299 := rs (se 1 (by rfl) ⟨974, by rfl⟩) R1949
theorem R1309 : Reach 1309 := rs (se 3 (by rfl) ⟨245, by rfl⟩) R491
theorem R1319 : Reach 1319 := rs (se 1 (by rfl) ⟨989, by rfl⟩) R1979
theorem R1335 : Reach 1335 := rs (se 1 (by rfl) ⟨1001, by rfl⟩) R2003
theorem R2561 : Reach 2561 := rs (se 2 (by rfl) ⟨960, by rfl⟩) R1921
theorem R2567 : Reach 2567 := rs (se 1 (by rfl) ⟨1925, by rfl⟩) R3851
theorem R2575 : Reach 2575 := rs (se 1 (by rfl) ⟨1931, by rfl⟩) R3863
theorem R2579 : Reach 2579 := rs (se 1 (by rfl) ⟨1934, by rfl⟩) R3869
theorem R2587 : Reach 2587 := rs (se 1 (by rfl) ⟨1940, by rfl⟩) R3881
theorem R2597 : Reach 2597 := rs (se 4 (by rfl) ⟨243, by rfl⟩) R487
theorem R2599 : Reach 2599 := rs (se 1 (by rfl) ⟨1949, by rfl⟩) R3899
theorem R2621 : Reach 2621 := rs (se 3 (by rfl) ⟨491, by rfl⟩) R983
theorem R2639 : Reach 2639 := rs (se 1 (by rfl) ⟨1979, by rfl⟩) R3959
theorem R2651 : Reach 2651 := rs (se 1 (by rfl) ⟨1988, by rfl⟩) R3977
theorem R2669 : Reach 2669 := rs (se 3 (by rfl) ⟨500, by rfl⟩) R1001
theorem R5123 : Reach 5123 := rs (se 1 (by rfl) ⟨3842, by rfl⟩) R7685
theorem R5127 : Reach 5127 := rs (se 1 (by rfl) ⟨3845, by rfl⟩) R7691
theorem R5129 : Reach 5129 := rs (se 2 (by rfl) ⟨1923, by rfl⟩) R3847
theorem R5135 : Reach 5135 := rs (se 1 (by rfl) ⟨3851, by rfl⟩) R7703
theorem R5149 : Reach 5149 := rs (se 3 (by rfl) ⟨965, by rfl⟩) R1931
theorem R5153 : Reach 5153 := rs (se 2 (by rfl) ⟨1932, by rfl⟩) R3865
theorem R5157 : Reach 5157 := rs (se 4 (by rfl) ⟨483, by rfl⟩) R967
theorem R5159 : Reach 5159 := rs (se 1 (by rfl) ⟨3869, by rfl⟩) R7739
theorem R5175 : Reach 5175 := rs (se 1 (by rfl) ⟨3881, by rfl⟩) R7763
theorem R5197 : Reach 5197 := rs (se 3 (by rfl) ⟨974, by rfl⟩) R1949
theorem R5199 : Reach 5199 := rs (se 1 (by rfl) ⟨3899, by rfl⟩) R7799
theorem R5201 : Reach 5201 := rs (se 2 (by rfl) ⟨1950, by rfl⟩) R3901
theorem R5217 : Reach 5217 := rs (se 2 (by rfl) ⟨1956, by rfl⟩) R3913
theorem R5237 : Reach 5237 := rs (se 5 (by rfl) ⟨245, by rfl⟩) R491
theorem R5273 : Reach 5273 := rs (se 2 (by rfl) ⟨1977, by rfl⟩) R3955
theorem R5277 : Reach 5277 := rs (se 3 (by rfl) ⟨989, by rfl⟩) R1979
theorem R5295 : Reach 5295 := rs (se 1 (by rfl) ⟨3971, by rfl⟩) R7943
theorem R5303 : Reach 5303 := rs (se 1 (by rfl) ⟨3977, by rfl⟩) R7955
theorem R5307 : Reach 5307 := rs (se 1 (by rfl) ⟨3980, by rfl⟩) R7961
theorem R5341 : Reach 5341 := rs (se 3 (by rfl) ⟨1001, by rfl⟩) R2003
theorem R5385 : Reach 5385 := rs (se 2 (by rfl) ⟨2019, by rfl⟩) R4039
theorem R5387 : Reach 5387 := rs (se 1 (by rfl) ⟨4040, by rfl⟩) R8081
theorem R39359 : Reach 39359 := rs (se 1 (by rfl) ⟨29519, by rfl⟩) R59039
theorem R170585 : Reach 170585 := rs (se 2 (by rfl) ⟨63969, by rfl⟩) R127939
theorem R40247 : Reach 40247 := rs (se 1 (by rfl) ⟨30185, by rfl⟩) R60371
theorem R41093 : Reach 41093 := rs (se 4 (by rfl) ⟨3852, by rfl⟩) R7705
theorem R41201 : Reach 41201 := rs (se 2 (by rfl) ⟨15450, by rfl⟩) R30901
theorem R41417 : Reach 41417 := rs (se 2 (by rfl) ⟨15531, by rfl⟩) R31063
theorem R41471 : Reach 41471 := rs (se 1 (by rfl) ⟨31103, by rfl⟩) R62207
theorem R41741 : Reach 41741 := rs (se 3 (by rfl) ⟨7826, by rfl⟩) R15653
theorem R42221 : Reach 42221 := rs (se 3 (by rfl) ⟨7916, by rfl⟩) R15833
theorem R42443 : Reach 42443 := rs (se 1 (by rfl) ⟨31832, by rfl⟩) R63665
theorem R42551 : Reach 42551 := rs (se 1 (by rfl) ⟨31913, by rfl⟩) R63827
theorem R9919 : Reach 9919 := rs (se 1 (by rfl) ⟨7439, by rfl⟩) R14879
theorem R42767 : Reach 42767 := rs (se 1 (by rfl) ⟨32075, by rfl⟩) R64151
theorem R10095 : Reach 10095 := rs (se 1 (by rfl) ⟨7571, by rfl⟩) R15143
theorem R10151 : Reach 10151 := rs (se 1 (by rfl) ⟨7613, by rfl⟩) R15227
theorem R10215 : Reach 10215 := rs (se 1 (by rfl) ⟨7661, by rfl⟩) R15323
theorem R10245 : Reach 10245 := rs (se 4 (by rfl) ⟨960, by rfl⟩) R1921
theorem R10251 : Reach 10251 := rs (se 1 (by rfl) ⟨7688, by rfl⟩) R15377
theorem R10255 : Reach 10255 := rs (se 1 (by rfl) ⟨7691, by rfl⟩) R15383
theorem R10259 : Reach 10259 := rs (se 1 (by rfl) ⟨7694, by rfl⟩) R15389
theorem R10267 : Reach 10267 := rs (se 1 (by rfl) ⟨7700, by rfl⟩) R15401
theorem R10269 : Reach 10269 := rs (se 3 (by rfl) ⟨1925, by rfl⟩) R3851
theorem R10273 : Reach 10273 := rs (se 2 (by rfl) ⟨3852, by rfl⟩) R7705
theorem R10279 : Reach 10279 := rs (se 1 (by rfl) ⟨7709, by rfl⟩) R15419
theorem R10287 : Reach 10287 := rs (se 1 (by rfl) ⟨7715, by rfl⟩) R15431
theorem R10301 : Reach 10301 := rs (se 3 (by rfl) ⟨1931, by rfl⟩) R3863
theorem R10305 : Reach 10305 := rs (se 2 (by rfl) ⟨3864, by rfl⟩) R7729
theorem R10307 : Reach 10307 := rs (se 1 (by rfl) ⟨7730, by rfl⟩) R15461
theorem R10317 : Reach 10317 := rs (se 3 (by rfl) ⟨1934, by rfl⟩) R3869
theorem R10319 : Reach 10319 := rs (se 1 (by rfl) ⟨7739, by rfl⟩) R15479
theorem R10321 : Reach 10321 := rs (se 2 (by rfl) ⟨3870, by rfl⟩) R7741
theorem R10337 : Reach 10337 := rs (se 2 (by rfl) ⟨3876, by rfl⟩) R7753
theorem R10345 : Reach 10345 := rs (se 2 (by rfl) ⟨3879, by rfl⟩) R7759
theorem R10349 : Reach 10349 := rs (se 3 (by rfl) ⟨1940, by rfl⟩) R3881
theorem R10367 : Reach 10367 := rs (se 1 (by rfl) ⟨7775, by rfl⟩) R15551
theorem R10389 : Reach 10389 := rs (se 6 (by rfl) ⟨243, by rfl⟩) R487
theorem R10393 : Reach 10393 := rs (se 2 (by rfl) ⟨3897, by rfl⟩) R7795
theorem R10397 : Reach 10397 := rs (se 3 (by rfl) ⟨1949, by rfl⟩) R3899
theorem R10401 : Reach 10401 := rs (se 2 (by rfl) ⟨3900, by rfl⟩) R7801
theorem R10403 : Reach 10403 := rs (se 1 (by rfl) ⟨7802, by rfl⟩) R15605
theorem R10411 : Reach 10411 := rs (se 1 (by rfl) ⟨7808, by rfl⟩) R15617
theorem R10433 : Reach 10433 := rs (se 2 (by rfl) ⟨3912, by rfl⟩) R7825
theorem R10435 : Reach 10435 := rs (se 1 (by rfl) ⟨7826, by rfl⟩) R15653
theorem R10459 : Reach 10459 := rs (se 1 (by rfl) ⟨7844, by rfl⟩) R15689
theorem R10481 : Reach 10481 := rs (se 2 (by rfl) ⟨3930, by rfl⟩) R7861
theorem R10485 : Reach 10485 := rs (se 5 (by rfl) ⟨491, by rfl⟩) R983
theorem R10497 : Reach 10497 := rs (se 2 (by rfl) ⟨3936, by rfl⟩) R7873
theorem R10505 : Reach 10505 := rs (se 2 (by rfl) ⟨3939, by rfl⟩) R7879
theorem R10507 : Reach 10507 := rs (se 1 (by rfl) ⟨7880, by rfl⟩) R15761
theorem R10545 : Reach 10545 := rs (se 2 (by rfl) ⟨3954, by rfl⟩) R7909
theorem R10547 : Reach 10547 := rs (se 1 (by rfl) ⟨7910, by rfl⟩) R15821
theorem R10555 : Reach 10555 := rs (se 1 (by rfl) ⟨7916, by rfl⟩) R15833
theorem R10557 : Reach 10557 := rs (se 3 (by rfl) ⟨1979, by rfl⟩) R3959
theorem R10585 : Reach 10585 := rs (se 2 (by rfl) ⟨3969, by rfl⟩) R7939
theorem R10591 : Reach 10591 := rs (se 1 (by rfl) ⟨7943, by rfl⟩) R15887
theorem R10605 : Reach 10605 := rs (se 3 (by rfl) ⟨1988, by rfl⟩) R3977
theorem R10615 : Reach 10615 := rs (se 1 (by rfl) ⟨7961, by rfl⟩) R15923
theorem R10633 : Reach 10633 := rs (se 2 (by rfl) ⟨3987, by rfl⟩) R7975
theorem R10655 : Reach 10655 := rs (se 1 (by rfl) ⟨7991, by rfl⟩) R15983
theorem R10667 : Reach 10667 := rs (se 1 (by rfl) ⟨8000, by rfl⟩) R16001
theorem R10677 : Reach 10677 := rs (se 5 (by rfl) ⟨500, by rfl⟩) R1001
theorem R10689 : Reach 10689 := rs (se 2 (by rfl) ⟨4008, by rfl⟩) R8017
theorem R10771 : Reach 10771 := rs (se 1 (by rfl) ⟨8078, by rfl⟩) R16157
theorem R10775 : Reach 10775 := rs (se 1 (by rfl) ⟨8081, by rfl⟩) R16163
theorem R10777 : Reach 10777 := rs (se 2 (by rfl) ⟨4041, by rfl⟩) R8083
theorem R10779 : Reach 10779 := rs (se 1 (by rfl) ⟨8084, by rfl⟩) R16169
theorem R10783 : Reach 10783 := rs (se 1 (by rfl) ⟨8087, by rfl⟩) R16175
theorem R10977 : Reach 10977 := rs (se 2 (by rfl) ⟨4116, by rfl⟩) R8233
theorem R11291 : Reach 11291 := rs (se 1 (by rfl) ⟨8468, by rfl⟩) R16937
theorem R44135 : Reach 44135 := rs (se 1 (by rfl) ⟨33101, by rfl⟩) R66203
theorem R78715 : Reach 78715 := rs (se 1 (by rfl) ⟨59036, by rfl⟩) R118073
theorem R48761 : Reach 48761 := rs (se 2 (by rfl) ⟨18285, by rfl⟩) R36571
theorem R82301 : Reach 82301 := rs (se 3 (by rfl) ⟨15431, by rfl⟩) R30863
theorem R705307 : Reach 705307 := rs (se 1 (by rfl) ⟨528980, by rfl⟩) R1057961
theorem R82763 : Reach 82763 := rs (se 1 (by rfl) ⟨62072, by rfl⟩) R124145
theorem R83243 : Reach 83243 := rs (se 1 (by rfl) ⟨62432, by rfl⟩) R124865
theorem R1362743 : Reach 1362743 := rs (se 1 (by rfl) ⟨1022057, by rfl⟩) R2044115
theorem R20123 : Reach 20123 := rs (se 1 (by rfl) ⟨15092, by rfl⟩) R30185
theorem R20303 : Reach 20303 := rs (se 1 (by rfl) ⟨15227, by rfl⟩) R30455
theorem R20503 : Reach 20503 := rs (se 1 (by rfl) ⟨15377, by rfl⟩) R30755
theorem R20537 : Reach 20537 := rs (se 2 (by rfl) ⟨7701, by rfl⟩) R15403
theorem R20587 : Reach 20587 := rs (se 1 (by rfl) ⟨15440, by rfl⟩) R30881
theorem R20641 : Reach 20641 := rs (se 2 (by rfl) ⟨7740, by rfl⟩) R15481
theorem R20675 : Reach 20675 := rs (se 1 (by rfl) ⟨15506, by rfl⟩) R31013
theorem R20683 : Reach 20683 := rs (se 1 (by rfl) ⟨15512, by rfl⟩) R31025
theorem R20735 : Reach 20735 := rs (se 1 (by rfl) ⟨15551, by rfl⟩) R31103
theorem R20789 : Reach 20789 := rs (se 5 (by rfl) ⟨974, by rfl⟩) R1949
theorem R20803 : Reach 20803 := rs (se 1 (by rfl) ⟨15602, by rfl⟩) R31205
theorem R20825 : Reach 20825 := rs (se 2 (by rfl) ⟨7809, by rfl⟩) R15619
theorem R20857 : Reach 20857 := rs (se 2 (by rfl) ⟨7821, by rfl⟩) R15643
theorem R21001 : Reach 21001 := rs (se 2 (by rfl) ⟨7875, by rfl⟩) R15751
theorem R21181 : Reach 21181 := rs (se 3 (by rfl) ⟨3971, by rfl⟩) R7943
theorem R21257 : Reach 21257 := rs (se 2 (by rfl) ⟨7971, by rfl⟩) R15943
theorem R21275 : Reach 21275 := rs (se 1 (by rfl) ⟨15956, by rfl⟩) R31913
theorem R21311 : Reach 21311 := rs (se 1 (by rfl) ⟨15983, by rfl⟩) R31967
theorem R21365 : Reach 21365 := rs (se 5 (by rfl) ⟨1001, by rfl⟩) R2003
theorem R21383 : Reach 21383 := rs (se 1 (by rfl) ⟨16037, by rfl⟩) R32075
theorem R21559 : Reach 21559 := rs (se 1 (by rfl) ⟨16169, by rfl⟩) R32339
theorem R21959 : Reach 21959 := rs (se 1 (by rfl) ⟨16469, by rfl⟩) R32939
theorem R21995 : Reach 21995 := rs (se 1 (by rfl) ⟨16496, by rfl⟩) R32993
theorem R859 : Reach 859 := rs (se 1 (by rfl) ⟨644, by rfl⟩) R1289
theorem R865 : Reach 865 := rs (se 2 (by rfl) ⟨324, by rfl⟩) R649
theorem R873 : Reach 873 := rs (se 2 (by rfl) ⟨327, by rfl⟩) R655
theorem R879 : Reach 879 := rs (se 1 (by rfl) ⟨659, by rfl⟩) R1319
theorem R889 : Reach 889 := rs (se 2 (by rfl) ⟨333, by rfl⟩) R667
theorem R1707 : Reach 1707 := rs (se 1 (by rfl) ⟨1280, by rfl⟩) R2561
theorem R1711 : Reach 1711 := rs (se 1 (by rfl) ⟨1283, by rfl⟩) R2567
theorem R1719 : Reach 1719 := rs (se 1 (by rfl) ⟨1289, by rfl⟩) R2579
theorem R1731 : Reach 1731 := rs (se 1 (by rfl) ⟨1298, by rfl⟩) R2597
theorem R1745 : Reach 1745 := rs (se 2 (by rfl) ⟨654, by rfl⟩) R1309
theorem R1747 : Reach 1747 := rs (se 1 (by rfl) ⟨1310, by rfl⟩) R2621
theorem R1759 : Reach 1759 := rs (se 1 (by rfl) ⟨1319, by rfl⟩) R2639
theorem R1767 : Reach 1767 := rs (se 1 (by rfl) ⟨1325, by rfl⟩) R2651
theorem R1779 : Reach 1779 := rs (se 1 (by rfl) ⟨1334, by rfl⟩) R2669
theorem R3415 : Reach 3415 := rs (se 1 (by rfl) ⟨2561, by rfl⟩) R5123
theorem R3419 : Reach 3419 := rs (se 1 (by rfl) ⟨2564, by rfl⟩) R5129
theorem R3423 : Reach 3423 := rs (se 1 (by rfl) ⟨2567, by rfl⟩) R5135
theorem R3433 : Reach 3433 := rs (se 2 (by rfl) ⟨1287, by rfl⟩) R2575
theorem R3435 : Reach 3435 := rs (se 1 (by rfl) ⟨2576, by rfl⟩) R5153
theorem R3437 : Reach 3437 := rs (se 3 (by rfl) ⟨644, by rfl⟩) R1289
theorem R3439 : Reach 3439 := rs (se 1 (by rfl) ⟨2579, by rfl⟩) R5159
theorem R3449 : Reach 3449 := rs (se 2 (by rfl) ⟨1293, by rfl⟩) R2587
theorem R3461 : Reach 3461 := rs (se 4 (by rfl) ⟨324, by rfl⟩) R649
theorem R3465 : Reach 3465 := rs (se 2 (by rfl) ⟨1299, by rfl⟩) R2599
theorem R3467 : Reach 3467 := rs (se 1 (by rfl) ⟨2600, by rfl⟩) R5201
theorem R3491 : Reach 3491 := rs (se 1 (by rfl) ⟨2618, by rfl⟩) R5237
theorem R3493 : Reach 3493 := rs (se 4 (by rfl) ⟨327, by rfl⟩) R655
theorem R3515 : Reach 3515 := rs (se 1 (by rfl) ⟨2636, by rfl⟩) R5273
theorem R3517 : Reach 3517 := rs (se 3 (by rfl) ⟨659, by rfl⟩) R1319
theorem R3535 : Reach 3535 := rs (se 1 (by rfl) ⟨2651, by rfl⟩) R5303
theorem R3557 : Reach 3557 := rs (se 4 (by rfl) ⟨333, by rfl⟩) R667
theorem R3591 : Reach 3591 := rs (se 1 (by rfl) ⟨2693, by rfl⟩) R5387
theorem R6767 : Reach 6767 := rs (se 1 (by rfl) ⟨5075, by rfl⟩) R10151
theorem R6829 : Reach 6829 := rs (se 3 (by rfl) ⟨1280, by rfl⟩) R2561
theorem R6839 : Reach 6839 := rs (se 1 (by rfl) ⟨5129, by rfl⟩) R10259
theorem R6845 : Reach 6845 := rs (se 3 (by rfl) ⟨1283, by rfl⟩) R2567
theorem R6865 : Reach 6865 := rs (se 2 (by rfl) ⟨2574, by rfl⟩) R5149
theorem R6867 : Reach 6867 := rs (se 1 (by rfl) ⟨5150, by rfl⟩) R10301
theorem R6871 : Reach 6871 := rs (se 1 (by rfl) ⟨5153, by rfl⟩) R10307
theorem R6877 : Reach 6877 := rs (se 3 (by rfl) ⟨1289, by rfl⟩) R2579
theorem R6879 : Reach 6879 := rs (se 1 (by rfl) ⟨5159, by rfl⟩) R10319
theorem R6891 : Reach 6891 := rs (se 1 (by rfl) ⟨5168, by rfl⟩) R10337
theorem R6899 : Reach 6899 := rs (se 1 (by rfl) ⟨5174, by rfl⟩) R10349
theorem R6911 : Reach 6911 := rs (se 1 (by rfl) ⟨5183, by rfl⟩) R10367
theorem R6925 : Reach 6925 := rs (se 3 (by rfl) ⟨1298, by rfl⟩) R2597
theorem R6929 : Reach 6929 := rs (se 2 (by rfl) ⟨2598, by rfl⟩) R5197
theorem R6931 : Reach 6931 := rs (se 1 (by rfl) ⟨5198, by rfl⟩) R10397
theorem R6935 : Reach 6935 := rs (se 1 (by rfl) ⟨5201, by rfl⟩) R10403
theorem R6955 : Reach 6955 := rs (se 1 (by rfl) ⟨5216, by rfl⟩) R10433
theorem R6981 : Reach 6981 := rs (se 4 (by rfl) ⟨654, by rfl⟩) R1309
theorem R6987 : Reach 6987 := rs (se 1 (by rfl) ⟨5240, by rfl⟩) R10481
theorem R6989 : Reach 6989 := rs (se 3 (by rfl) ⟨1310, by rfl⟩) R2621
theorem R7003 : Reach 7003 := rs (se 1 (by rfl) ⟨5252, by rfl⟩) R10505
theorem R7031 : Reach 7031 := rs (se 1 (by rfl) ⟨5273, by rfl⟩) R10547
theorem R7037 : Reach 7037 := rs (se 3 (by rfl) ⟨1319, by rfl⟩) R2639
theorem R7069 : Reach 7069 := rs (se 3 (by rfl) ⟨1325, by rfl⟩) R2651
theorem R7103 : Reach 7103 := rs (se 1 (by rfl) ⟨5327, by rfl⟩) R10655
theorem R7111 : Reach 7111 := rs (se 1 (by rfl) ⟨5333, by rfl⟩) R10667
theorem R7117 : Reach 7117 := rs (se 3 (by rfl) ⟨1334, by rfl⟩) R2669
theorem R7121 : Reach 7121 := rs (se 2 (by rfl) ⟨2670, by rfl⟩) R5341
theorem R7183 : Reach 7183 := rs (se 1 (by rfl) ⟨5387, by rfl⟩) R10775
theorem R7527 : Reach 7527 := rs (se 1 (by rfl) ⟨5645, by rfl⟩) R11291
theorem R109349 : Reach 109349 := rs (se 4 (by rfl) ⟨10251, by rfl⟩) R20503
theorem R13225 : Reach 13225 := rs (se 2 (by rfl) ⟨4959, by rfl⟩) R9919
theorem R13415 : Reach 13415 := rs (se 1 (by rfl) ⟨10061, by rfl⟩) R20123
theorem R13535 : Reach 13535 := rs (se 1 (by rfl) ⟨10151, by rfl⟩) R20303
theorem R13661 : Reach 13661 := rs (se 3 (by rfl) ⟨2561, by rfl⟩) R5123
theorem R13673 : Reach 13673 := rs (se 2 (by rfl) ⟨5127, by rfl⟩) R10255
theorem R13691 : Reach 13691 := rs (se 1 (by rfl) ⟨10268, by rfl⟩) R20537
theorem R13693 : Reach 13693 := rs (se 3 (by rfl) ⟨2567, by rfl⟩) R5135
theorem R13697 : Reach 13697 := rs (se 2 (by rfl) ⟨5136, by rfl⟩) R10273
theorem R13733 : Reach 13733 := rs (se 4 (by rfl) ⟨1287, by rfl⟩) R2575
theorem R13757 : Reach 13757 := rs (se 3 (by rfl) ⟨2579, by rfl⟩) R5159
theorem R13783 : Reach 13783 := rs (se 1 (by rfl) ⟨10337, by rfl⟩) R20675
theorem R13793 : Reach 13793 := rs (se 2 (by rfl) ⟨5172, by rfl⟩) R10345
theorem R13823 : Reach 13823 := rs (se 1 (by rfl) ⟨10367, by rfl⟩) R20735
theorem R13859 : Reach 13859 := rs (se 1 (by rfl) ⟨10394, by rfl⟩) R20789
theorem R13861 : Reach 13861 := rs (se 4 (by rfl) ⟨1299, by rfl⟩) R2599
theorem R13883 : Reach 13883 := rs (se 1 (by rfl) ⟨10412, by rfl⟩) R20825
theorem R13913 : Reach 13913 := rs (se 2 (by rfl) ⟨5217, by rfl⟩) R10435
theorem R13945 : Reach 13945 := rs (se 2 (by rfl) ⟨5229, by rfl⟩) R10459
theorem R13973 : Reach 13973 := rs (se 6 (by rfl) ⟨327, by rfl⟩) R655
theorem R14009 : Reach 14009 := rs (se 2 (by rfl) ⟨5253, by rfl⟩) R10507
theorem R14069 : Reach 14069 := rs (se 5 (by rfl) ⟨659, by rfl⟩) R1319
theorem R14141 : Reach 14141 := rs (se 3 (by rfl) ⟨2651, by rfl⟩) R5303
theorem R14153 : Reach 14153 := rs (se 2 (by rfl) ⟨5307, by rfl⟩) R10615
theorem R14171 : Reach 14171 := rs (se 1 (by rfl) ⟨10628, by rfl⟩) R21257
theorem R14177 : Reach 14177 := rs (se 2 (by rfl) ⟨5316, by rfl⟩) R10633
theorem R14183 : Reach 14183 := rs (se 1 (by rfl) ⟨10637, by rfl⟩) R21275
theorem R14207 : Reach 14207 := rs (se 1 (by rfl) ⟨10655, by rfl⟩) R21311
theorem R14243 : Reach 14243 := rs (se 1 (by rfl) ⟨10682, by rfl⟩) R21365
theorem R14255 : Reach 14255 := rs (se 1 (by rfl) ⟨10691, by rfl⟩) R21383
theorem R14369 : Reach 14369 := rs (se 2 (by rfl) ⟨5388, by rfl⟩) R10777
theorem R14377 : Reach 14377 := rs (se 2 (by rfl) ⟨5391, by rfl⟩) R10783
theorem R14639 : Reach 14639 := rs (se 1 (by rfl) ⟨10979, by rfl⟩) R21959
theorem R14663 : Reach 14663 := rs (se 1 (by rfl) ⟨10997, by rfl⟩) R21995
theorem R113723 : Reach 113723 := rs (se 1 (by rfl) ⟨85292, by rfl⟩) R170585
theorem R218699 : Reach 218699 := rs (se 1 (by rfl) ⟨164024, by rfl⟩) R328049
theorem R55175 : Reach 55175 := rs (se 1 (by rfl) ⟨41381, by rfl⟩) R82763
theorem R55495 : Reach 55495 := rs (se 1 (by rfl) ⟨41621, by rfl⟩) R83243
theorem R940409 : Reach 940409 := rs (se 2 (by rfl) ⟨352653, by rfl⟩) R705307
theorem R908495 : Reach 908495 := rs (se 1 (by rfl) ⟨681371, by rfl⟩) R1362743
theorem R57509 : Reach 57509 := rs (se 4 (by rfl) ⟨5391, by rfl⟩) R10783
theorem R877877 : Reach 877877 := rs (se 5 (by rfl) ⟨41150, by rfl⟩) R82301
theorem R26239 : Reach 26239 := rs (se 1 (by rfl) ⟨19679, by rfl⟩) R39359
theorem R419813 : Reach 419813 := rs (se 4 (by rfl) ⟨39357, by rfl⟩) R78715
theorem R26831 : Reach 26831 := rs (se 1 (by rfl) ⟨20123, by rfl⟩) R40247
theorem R27317 : Reach 27317 := rs (se 5 (by rfl) ⟨1280, by rfl⟩) R2561
theorem R27337 : Reach 27337 := rs (se 2 (by rfl) ⟨10251, by rfl⟩) R20503
theorem R27395 : Reach 27395 := rs (se 1 (by rfl) ⟨20546, by rfl⟩) R41093
theorem R27449 : Reach 27449 := rs (se 2 (by rfl) ⟨10293, by rfl⟩) R20587
theorem R27467 : Reach 27467 := rs (se 1 (by rfl) ⟨20600, by rfl⟩) R41201
theorem R27469 : Reach 27469 := rs (se 3 (by rfl) ⟨5150, by rfl⟩) R10301
theorem R27485 : Reach 27485 := rs (se 3 (by rfl) ⟨5153, by rfl⟩) R10307
theorem R27521 : Reach 27521 := rs (se 2 (by rfl) ⟨10320, by rfl⟩) R20641
theorem R27577 : Reach 27577 := rs (se 2 (by rfl) ⟨10341, by rfl⟩) R20683
theorem R27611 : Reach 27611 := rs (se 1 (by rfl) ⟨20708, by rfl⟩) R41417
theorem R27647 : Reach 27647 := rs (se 1 (by rfl) ⟨20735, by rfl⟩) R41471
theorem R27701 : Reach 27701 := rs (se 5 (by rfl) ⟨1298, by rfl⟩) R2597
theorem R27737 : Reach 27737 := rs (se 2 (by rfl) ⟨10401, by rfl⟩) R20803
theorem R27809 : Reach 27809 := rs (se 2 (by rfl) ⟨10428, by rfl⟩) R20857
theorem R27827 : Reach 27827 := rs (se 1 (by rfl) ⟨20870, by rfl⟩) R41741
theorem R28001 : Reach 28001 := rs (se 2 (by rfl) ⟨10500, by rfl⟩) R21001
theorem R28147 : Reach 28147 := rs (se 1 (by rfl) ⟨21110, by rfl⟩) R42221
theorem R28241 : Reach 28241 := rs (se 2 (by rfl) ⟨10590, by rfl⟩) R21181
theorem R28277 : Reach 28277 := rs (se 5 (by rfl) ⟨1325, by rfl⟩) R2651
theorem R28295 : Reach 28295 := rs (se 1 (by rfl) ⟨21221, by rfl⟩) R42443
theorem R28367 : Reach 28367 := rs (se 1 (by rfl) ⟨21275, by rfl⟩) R42551
theorem R28511 : Reach 28511 := rs (se 1 (by rfl) ⟨21383, by rfl⟩) R42767
theorem R28745 : Reach 28745 := rs (se 2 (by rfl) ⟨10779, by rfl⟩) R21559
theorem R29423 : Reach 29423 := rs (se 1 (by rfl) ⟨22067, by rfl⟩) R44135
theorem R32507 : Reach 32507 := rs (se 1 (by rfl) ⟨24380, by rfl⟩) R48761
theorem R1145 : Reach 1145 := rs (se 2 (by rfl) ⟨429, by rfl⟩) R859
theorem R1153 : Reach 1153 := rs (se 2 (by rfl) ⟨432, by rfl⟩) R865
theorem R1163 : Reach 1163 := rs (se 1 (by rfl) ⟨872, by rfl⟩) R1745
theorem R1185 : Reach 1185 := rs (se 2 (by rfl) ⟨444, by rfl⟩) R889
theorem R34985 : Reach 34985 := rs (se 2 (by rfl) ⟨13119, by rfl⟩) R26239
theorem R2279 : Reach 2279 := rs (se 1 (by rfl) ⟨1709, by rfl⟩) R3419
theorem R2281 : Reach 2281 := rs (se 2 (by rfl) ⟨855, by rfl⟩) R1711
theorem R2291 : Reach 2291 := rs (se 1 (by rfl) ⟨1718, by rfl⟩) R3437
theorem R2299 : Reach 2299 := rs (se 1 (by rfl) ⟨1724, by rfl⟩) R3449
theorem R2307 : Reach 2307 := rs (se 1 (by rfl) ⟨1730, by rfl⟩) R3461
theorem R2311 : Reach 2311 := rs (se 1 (by rfl) ⟨1733, by rfl⟩) R3467
theorem R2327 : Reach 2327 := rs (se 1 (by rfl) ⟨1745, by rfl⟩) R3491
theorem R2329 : Reach 2329 := rs (se 2 (by rfl) ⟨873, by rfl⟩) R1747
theorem R2343 : Reach 2343 := rs (se 1 (by rfl) ⟨1757, by rfl⟩) R3515
theorem R2345 : Reach 2345 := rs (se 2 (by rfl) ⟨879, by rfl⟩) R1759
theorem R2371 : Reach 2371 := rs (se 1 (by rfl) ⟨1778, by rfl⟩) R3557
theorem R36449 : Reach 36449 := rs (se 2 (by rfl) ⟨13668, by rfl⟩) R27337
theorem R36625 : Reach 36625 := rs (se 2 (by rfl) ⟨13734, by rfl⟩) R27469
theorem R36769 : Reach 36769 := rs (se 2 (by rfl) ⟨13788, by rfl⟩) R27577
theorem R626939 : Reach 626939 := rs (se 1 (by rfl) ⟨470204, by rfl⟩) R940409
theorem R4511 : Reach 4511 := rs (se 1 (by rfl) ⟨3383, by rfl⟩) R6767
theorem R4553 : Reach 4553 := rs (se 2 (by rfl) ⟨1707, by rfl⟩) R3415
theorem R4559 : Reach 4559 := rs (se 1 (by rfl) ⟨3419, by rfl⟩) R6839
theorem R4563 : Reach 4563 := rs (se 1 (by rfl) ⟨3422, by rfl⟩) R6845
theorem R4577 : Reach 4577 := rs (se 2 (by rfl) ⟨1716, by rfl⟩) R3433
theorem R4581 : Reach 4581 := rs (se 4 (by rfl) ⟨429, by rfl⟩) R859
theorem R4585 : Reach 4585 := rs (se 2 (by rfl) ⟨1719, by rfl⟩) R3439
theorem R4599 : Reach 4599 := rs (se 1 (by rfl) ⟨3449, by rfl⟩) R6899
theorem R4607 : Reach 4607 := rs (se 1 (by rfl) ⟨3455, by rfl⟩) R6911
theorem R4613 : Reach 4613 := rs (se 4 (by rfl) ⟨432, by rfl⟩) R865
theorem R4619 : Reach 4619 := rs (se 1 (by rfl) ⟨3464, by rfl⟩) R6929
theorem R4623 : Reach 4623 := rs (se 1 (by rfl) ⟨3467, by rfl⟩) R6935
theorem R4653 : Reach 4653 := rs (se 3 (by rfl) ⟨872, by rfl⟩) R1745
theorem R4657 : Reach 4657 := rs (se 2 (by rfl) ⟨1746, by rfl⟩) R3493
theorem R4659 : Reach 4659 := rs (se 1 (by rfl) ⟨3494, by rfl⟩) R6989
theorem R4687 : Reach 4687 := rs (se 1 (by rfl) ⟨3515, by rfl⟩) R7031
theorem R4689 : Reach 4689 := rs (se 2 (by rfl) ⟨1758, by rfl⟩) R3517
theorem R4691 : Reach 4691 := rs (se 1 (by rfl) ⟨3518, by rfl⟩) R7037
theorem R4713 : Reach 4713 := rs (se 2 (by rfl) ⟨1767, by rfl⟩) R3535
theorem R4735 : Reach 4735 := rs (se 1 (by rfl) ⟨3551, by rfl⟩) R7103
theorem R4741 : Reach 4741 := rs (se 4 (by rfl) ⟨444, by rfl⟩) R889
theorem R4747 : Reach 4747 := rs (se 1 (by rfl) ⟨3560, by rfl⟩) R7121
theorem R37529 : Reach 37529 := rs (se 2 (by rfl) ⟨14073, by rfl⟩) R28147
theorem R38339 : Reach 38339 := rs (se 1 (by rfl) ⟨28754, by rfl⟩) R57509
theorem R72899 : Reach 72899 := rs (se 1 (by rfl) ⟨54674, by rfl⟩) R109349
theorem R73993 : Reach 73993 := rs (se 2 (by rfl) ⟨27747, by rfl⟩) R55495
theorem R8943 : Reach 8943 := rs (se 1 (by rfl) ⟨6707, by rfl⟩) R13415
theorem R9023 : Reach 9023 := rs (se 1 (by rfl) ⟨6767, by rfl⟩) R13535
theorem R9105 : Reach 9105 := rs (se 2 (by rfl) ⟨3414, by rfl⟩) R6829
theorem R9107 : Reach 9107 := rs (se 1 (by rfl) ⟨6830, by rfl⟩) R13661
theorem R9115 : Reach 9115 := rs (se 1 (by rfl) ⟨6836, by rfl⟩) R13673
theorem R9117 : Reach 9117 := rs (se 3 (by rfl) ⟨1709, by rfl⟩) R3419
theorem R9125 : Reach 9125 := rs (se 4 (by rfl) ⟨855, by rfl⟩) R1711
theorem R9127 : Reach 9127 := rs (se 1 (by rfl) ⟨6845, by rfl⟩) R13691
theorem R9131 : Reach 9131 := rs (se 1 (by rfl) ⟨6848, by rfl⟩) R13697
theorem R9153 : Reach 9153 := rs (se 2 (by rfl) ⟨3432, by rfl⟩) R6865
theorem R9155 : Reach 9155 := rs (se 1 (by rfl) ⟨6866, by rfl⟩) R13733
theorem R9161 : Reach 9161 := rs (se 2 (by rfl) ⟨3435, by rfl⟩) R6871
theorem R9165 : Reach 9165 := rs (se 3 (by rfl) ⟨1718, by rfl⟩) R3437
theorem R9169 : Reach 9169 := rs (se 2 (by rfl) ⟨3438, by rfl⟩) R6877
theorem R9171 : Reach 9171 := rs (se 1 (by rfl) ⟨6878, by rfl⟩) R13757
theorem R9195 : Reach 9195 := rs (se 1 (by rfl) ⟨6896, by rfl⟩) R13793
theorem R9197 : Reach 9197 := rs (se 3 (by rfl) ⟨1724, by rfl⟩) R3449
theorem R9215 : Reach 9215 := rs (se 1 (by rfl) ⟨6911, by rfl⟩) R13823
theorem R9229 : Reach 9229 := rs (se 3 (by rfl) ⟨1730, by rfl⟩) R3461
theorem R9233 : Reach 9233 := rs (se 2 (by rfl) ⟨3462, by rfl⟩) R6925
theorem R9239 : Reach 9239 := rs (se 1 (by rfl) ⟨6929, by rfl⟩) R13859
theorem R9241 : Reach 9241 := rs (se 2 (by rfl) ⟨3465, by rfl⟩) R6931
theorem R9245 : Reach 9245 := rs (se 3 (by rfl) ⟨1733, by rfl⟩) R3467
theorem R9255 : Reach 9255 := rs (se 1 (by rfl) ⟨6941, by rfl⟩) R13883
theorem R9273 : Reach 9273 := rs (se 2 (by rfl) ⟨3477, by rfl⟩) R6955
theorem R9275 : Reach 9275 := rs (se 1 (by rfl) ⟨6956, by rfl⟩) R13913
theorem R9309 : Reach 9309 := rs (se 3 (by rfl) ⟨1745, by rfl⟩) R3491
theorem R9315 : Reach 9315 := rs (se 1 (by rfl) ⟨6986, by rfl⟩) R13973
theorem R9317 : Reach 9317 := rs (se 4 (by rfl) ⟨873, by rfl⟩) R1747
theorem R9337 : Reach 9337 := rs (se 2 (by rfl) ⟨3501, by rfl⟩) R7003
theorem R9339 : Reach 9339 := rs (se 1 (by rfl) ⟨7004, by rfl⟩) R14009
theorem R9373 : Reach 9373 := rs (se 3 (by rfl) ⟨1757, by rfl⟩) R3515
theorem R9379 : Reach 9379 := rs (se 1 (by rfl) ⟨7034, by rfl⟩) R14069
theorem R9381 : Reach 9381 := rs (se 4 (by rfl) ⟨879, by rfl⟩) R1759
theorem R9425 : Reach 9425 := rs (se 2 (by rfl) ⟨3534, by rfl⟩) R7069
theorem R9427 : Reach 9427 := rs (se 1 (by rfl) ⟨7070, by rfl⟩) R14141
theorem R9435 : Reach 9435 := rs (se 1 (by rfl) ⟨7076, by rfl⟩) R14153
theorem R9447 : Reach 9447 := rs (se 1 (by rfl) ⟨7085, by rfl⟩) R14171
theorem R9451 : Reach 9451 := rs (se 1 (by rfl) ⟨7088, by rfl⟩) R14177
theorem R9455 : Reach 9455 := rs (se 1 (by rfl) ⟨7091, by rfl⟩) R14183
theorem R9471 : Reach 9471 := rs (se 1 (by rfl) ⟨7103, by rfl⟩) R14207
theorem R9481 : Reach 9481 := rs (se 2 (by rfl) ⟨3555, by rfl⟩) R7111
theorem R9485 : Reach 9485 := rs (se 3 (by rfl) ⟨1778, by rfl⟩) R3557
theorem R9489 : Reach 9489 := rs (se 2 (by rfl) ⟨3558, by rfl⟩) R7117
theorem R9495 : Reach 9495 := rs (se 1 (by rfl) ⟨7121, by rfl⟩) R14243
theorem R9503 : Reach 9503 := rs (se 1 (by rfl) ⟨7127, by rfl⟩) R14255
theorem R9577 : Reach 9577 := rs (se 2 (by rfl) ⟨3591, by rfl⟩) R7183
theorem R9579 : Reach 9579 := rs (se 1 (by rfl) ⟨7184, by rfl⟩) R14369
theorem R9759 : Reach 9759 := rs (se 1 (by rfl) ⟨7319, by rfl⟩) R14639
theorem R9775 : Reach 9775 := rs (se 1 (by rfl) ⟨7331, by rfl⟩) R14663
theorem R75815 : Reach 75815 := rs (se 1 (by rfl) ⟨56861, by rfl⟩) R113723
theorem R145799 : Reach 145799 := rs (se 1 (by rfl) ⟨109349, by rfl⟩) R218699
theorem R605663 : Reach 605663 := rs (se 1 (by rfl) ⟨454247, by rfl⟩) R908495
theorem R147133 : Reach 147133 := rs (se 3 (by rfl) ⟨27587, by rfl⟩) R55175
theorem R17633 : Reach 17633 := rs (se 2 (by rfl) ⟨6612, by rfl⟩) R13225
theorem R279875 : Reach 279875 := rs (se 1 (by rfl) ⟨209906, by rfl⟩) R419813
theorem R17887 : Reach 17887 := rs (se 1 (by rfl) ⟨13415, by rfl⟩) R26831
theorem R18211 : Reach 18211 := rs (se 1 (by rfl) ⟨13658, by rfl⟩) R27317
theorem R18257 : Reach 18257 := rs (se 2 (by rfl) ⟨6846, by rfl⟩) R13693
theorem R18263 : Reach 18263 := rs (se 1 (by rfl) ⟨13697, by rfl⟩) R27395
theorem R18299 : Reach 18299 := rs (se 1 (by rfl) ⟨13724, by rfl⟩) R27449
theorem R18311 : Reach 18311 := rs (se 1 (by rfl) ⟨13733, by rfl⟩) R27467
theorem R18323 : Reach 18323 := rs (se 1 (by rfl) ⟨13742, by rfl⟩) R27485
theorem R18341 : Reach 18341 := rs (se 4 (by rfl) ⟨1719, by rfl⟩) R3439
theorem R18347 : Reach 18347 := rs (se 1 (by rfl) ⟨13760, by rfl⟩) R27521
theorem R18377 : Reach 18377 := rs (se 2 (by rfl) ⟨6891, by rfl⟩) R13783
theorem R18407 : Reach 18407 := rs (se 1 (by rfl) ⟨13805, by rfl⟩) R27611
theorem R18431 : Reach 18431 := rs (se 1 (by rfl) ⟨13823, by rfl⟩) R27647
theorem R18467 : Reach 18467 := rs (se 1 (by rfl) ⟨13850, by rfl⟩) R27701
theorem R18481 : Reach 18481 := rs (se 2 (by rfl) ⟨6930, by rfl⟩) R13861
theorem R18491 : Reach 18491 := rs (se 1 (by rfl) ⟨13868, by rfl⟩) R27737
theorem R18539 : Reach 18539 := rs (se 1 (by rfl) ⟨13904, by rfl⟩) R27809
theorem R18551 : Reach 18551 := rs (se 1 (by rfl) ⟨13913, by rfl⟩) R27827
theorem R18593 : Reach 18593 := rs (se 2 (by rfl) ⟨6972, by rfl⟩) R13945
theorem R18629 : Reach 18629 := rs (se 4 (by rfl) ⟨1746, by rfl⟩) R3493
theorem R18667 : Reach 18667 := rs (se 1 (by rfl) ⟨14000, by rfl⟩) R28001
theorem R18749 : Reach 18749 := rs (se 3 (by rfl) ⟨3515, by rfl⟩) R7031
theorem R18827 : Reach 18827 := rs (se 1 (by rfl) ⟨14120, by rfl⟩) R28241
theorem R18851 : Reach 18851 := rs (se 1 (by rfl) ⟨14138, by rfl⟩) R28277
theorem R18863 : Reach 18863 := rs (se 1 (by rfl) ⟨14147, by rfl⟩) R28295
theorem R18911 : Reach 18911 := rs (se 1 (by rfl) ⟨14183, by rfl⟩) R28367
theorem R18941 : Reach 18941 := rs (se 3 (by rfl) ⟨3551, by rfl⟩) R7103
theorem R18965 : Reach 18965 := rs (se 6 (by rfl) ⟨444, by rfl⟩) R889
theorem R18989 : Reach 18989 := rs (se 3 (by rfl) ⟨3560, by rfl⟩) R7121
theorem R19007 : Reach 19007 := rs (se 1 (by rfl) ⟨14255, by rfl⟩) R28511
theorem R19163 : Reach 19163 := rs (se 1 (by rfl) ⟨14372, by rfl⟩) R28745
theorem R19169 : Reach 19169 := rs (se 2 (by rfl) ⟨7188, by rfl⟩) R14377
theorem R19615 : Reach 19615 := rs (se 1 (by rfl) ⟨14711, by rfl⟩) R29423
theorem R21671 : Reach 21671 := rs (se 1 (by rfl) ⟨16253, by rfl⟩) R32507
theorem R585251 : Reach 585251 := rs (se 1 (by rfl) ⟨438938, by rfl⟩) R877877
theorem R98657 : Reach 98657 := rs (se 2 (by rfl) ⟨36996, by rfl⟩) R73993
theorem R763 : Reach 763 := rs (se 1 (by rfl) ⟨572, by rfl⟩) R1145
theorem R775 : Reach 775 := rs (se 1 (by rfl) ⟨581, by rfl⟩) R1163
theorem R1519 : Reach 1519 := rs (se 1 (by rfl) ⟨1139, by rfl⟩) R2279
theorem R1527 : Reach 1527 := rs (se 1 (by rfl) ⟨1145, by rfl⟩) R2291
theorem R1537 : Reach 1537 := rs (se 2 (by rfl) ⟨576, by rfl⟩) R1153
theorem R1551 : Reach 1551 := rs (se 1 (by rfl) ⟨1163, by rfl⟩) R2327
theorem R1563 : Reach 1563 := rs (se 1 (by rfl) ⟨1172, by rfl⟩) R2345
theorem R3007 : Reach 3007 := rs (se 1 (by rfl) ⟨2255, by rfl⟩) R4511
theorem R3035 : Reach 3035 := rs (se 1 (by rfl) ⟨2276, by rfl⟩) R4553
theorem R3039 : Reach 3039 := rs (se 1 (by rfl) ⟨2279, by rfl⟩) R4559
theorem R3041 : Reach 3041 := rs (se 2 (by rfl) ⟨1140, by rfl⟩) R2281
theorem R3051 : Reach 3051 := rs (se 1 (by rfl) ⟨2288, by rfl⟩) R4577
theorem R3053 : Reach 3053 := rs (se 3 (by rfl) ⟨572, by rfl⟩) R1145
theorem R3065 : Reach 3065 := rs (se 2 (by rfl) ⟨1149, by rfl⟩) R2299
theorem R3071 : Reach 3071 := rs (se 1 (by rfl) ⟨2303, by rfl⟩) R4607
theorem R3075 : Reach 3075 := rs (se 1 (by rfl) ⟨2306, by rfl⟩) R4613
theorem R3079 : Reach 3079 := rs (se 1 (by rfl) ⟨2309, by rfl⟩) R4619
theorem R3081 : Reach 3081 := rs (se 2 (by rfl) ⟨1155, by rfl⟩) R2311
theorem R3101 : Reach 3101 := rs (se 3 (by rfl) ⟨581, by rfl⟩) R1163
theorem R3105 : Reach 3105 := rs (se 2 (by rfl) ⟨1164, by rfl⟩) R2329
theorem R3127 : Reach 3127 := rs (se 1 (by rfl) ⟨2345, by rfl⟩) R4691
theorem R3161 : Reach 3161 := rs (se 2 (by rfl) ⟨1185, by rfl⟩) R2371
theorem R6015 : Reach 6015 := rs (se 1 (by rfl) ⟨4511, by rfl⟩) R9023
theorem R6071 : Reach 6071 := rs (se 1 (by rfl) ⟨4553, by rfl⟩) R9107
theorem R6077 : Reach 6077 := rs (se 3 (by rfl) ⟨1139, by rfl⟩) R2279
theorem R6083 : Reach 6083 := rs (se 1 (by rfl) ⟨4562, by rfl⟩) R9125
theorem R6087 : Reach 6087 := rs (se 1 (by rfl) ⟨4565, by rfl⟩) R9131
theorem R6103 : Reach 6103 := rs (se 1 (by rfl) ⟨4577, by rfl⟩) R9155
theorem R6107 : Reach 6107 := rs (se 1 (by rfl) ⟨4580, by rfl⟩) R9161
theorem R6109 : Reach 6109 := rs (se 3 (by rfl) ⟨1145, by rfl⟩) R2291
theorem R6113 : Reach 6113 := rs (se 2 (by rfl) ⟨2292, by rfl⟩) R4585
theorem R6131 : Reach 6131 := rs (se 1 (by rfl) ⟨4598, by rfl⟩) R9197
theorem R6143 : Reach 6143 := rs (se 1 (by rfl) ⟨4607, by rfl⟩) R9215
theorem R6149 : Reach 6149 := rs (se 4 (by rfl) ⟨576, by rfl⟩) R1153
theorem R6155 : Reach 6155 := rs (se 1 (by rfl) ⟨4616, by rfl⟩) R9233
theorem R6159 : Reach 6159 := rs (se 1 (by rfl) ⟨4619, by rfl⟩) R9239
theorem R6163 : Reach 6163 := rs (se 1 (by rfl) ⟨4622, by rfl⟩) R9245
theorem R6183 : Reach 6183 := rs (se 1 (by rfl) ⟨4637, by rfl⟩) R9275
theorem R6205 : Reach 6205 := rs (se 3 (by rfl) ⟨1163, by rfl⟩) R2327
theorem R6209 : Reach 6209 := rs (se 2 (by rfl) ⟨2328, by rfl⟩) R4657
theorem R6211 : Reach 6211 := rs (se 1 (by rfl) ⟨4658, by rfl⟩) R9317
theorem R6249 : Reach 6249 := rs (se 2 (by rfl) ⟨2343, by rfl⟩) R4687
theorem R6253 : Reach 6253 := rs (se 3 (by rfl) ⟨1172, by rfl⟩) R2345
theorem R6283 : Reach 6283 := rs (se 1 (by rfl) ⟨4712, by rfl⟩) R9425
theorem R6303 : Reach 6303 := rs (se 1 (by rfl) ⟨4727, by rfl⟩) R9455
theorem R6313 : Reach 6313 := rs (se 2 (by rfl) ⟨2367, by rfl⟩) R4735
theorem R6321 : Reach 6321 := rs (se 2 (by rfl) ⟨2370, by rfl⟩) R4741
theorem R6323 : Reach 6323 := rs (se 1 (by rfl) ⟨4742, by rfl⟩) R9485
theorem R6329 : Reach 6329 := rs (se 2 (by rfl) ⟨2373, by rfl⟩) R4747
theorem R6335 : Reach 6335 := rs (se 1 (by rfl) ⟨4751, by rfl⟩) R9503
theorem R403775 : Reach 403775 := rs (se 1 (by rfl) ⟨302831, by rfl⟩) R605663
theorem R11755 : Reach 11755 := rs (se 1 (by rfl) ⟨8816, by rfl⟩) R17633
theorem R12029 : Reach 12029 := rs (se 3 (by rfl) ⟨2255, by rfl⟩) R4511
theorem R12141 : Reach 12141 := rs (se 3 (by rfl) ⟨2276, by rfl⟩) R4553
theorem R12153 : Reach 12153 := rs (se 2 (by rfl) ⟨4557, by rfl⟩) R9115
theorem R12157 : Reach 12157 := rs (se 3 (by rfl) ⟨2279, by rfl⟩) R4559
theorem R12165 : Reach 12165 := rs (se 4 (by rfl) ⟨1140, by rfl⟩) R2281
theorem R12169 : Reach 12169 := rs (se 2 (by rfl) ⟨4563, by rfl⟩) R9127
theorem R12171 : Reach 12171 := rs (se 1 (by rfl) ⟨9128, by rfl⟩) R18257
theorem R12175 : Reach 12175 := rs (se 1 (by rfl) ⟨9131, by rfl⟩) R18263
theorem R12199 : Reach 12199 := rs (se 1 (by rfl) ⟨9149, by rfl⟩) R18299
theorem R12205 : Reach 12205 := rs (se 3 (by rfl) ⟨2288, by rfl⟩) R4577
theorem R12207 : Reach 12207 := rs (se 1 (by rfl) ⟨9155, by rfl⟩) R18311
theorem R12213 : Reach 12213 := rs (se 5 (by rfl) ⟨572, by rfl⟩) R1145
theorem R12215 : Reach 12215 := rs (se 1 (by rfl) ⟨9161, by rfl⟩) R18323
theorem R12225 : Reach 12225 := rs (se 2 (by rfl) ⟨4584, by rfl⟩) R9169
theorem R12227 : Reach 12227 := rs (se 1 (by rfl) ⟨9170, by rfl⟩) R18341
theorem R12231 : Reach 12231 := rs (se 1 (by rfl) ⟨9173, by rfl⟩) R18347
theorem R12251 : Reach 12251 := rs (se 1 (by rfl) ⟨9188, by rfl⟩) R18377
theorem R12261 : Reach 12261 := rs (se 4 (by rfl) ⟨1149, by rfl⟩) R2299
theorem R12271 : Reach 12271 := rs (se 1 (by rfl) ⟨9203, by rfl⟩) R18407
theorem R12285 : Reach 12285 := rs (se 3 (by rfl) ⟨2303, by rfl⟩) R4607
theorem R12287 : Reach 12287 := rs (se 1 (by rfl) ⟨9215, by rfl⟩) R18431
theorem R12301 : Reach 12301 := rs (se 3 (by rfl) ⟨2306, by rfl⟩) R4613
theorem R12305 : Reach 12305 := rs (se 2 (by rfl) ⟨4614, by rfl⟩) R9229
theorem R12311 : Reach 12311 := rs (se 1 (by rfl) ⟨9233, by rfl⟩) R18467
theorem R12317 : Reach 12317 := rs (se 3 (by rfl) ⟨2309, by rfl⟩) R4619
theorem R12321 : Reach 12321 := rs (se 2 (by rfl) ⟨4620, by rfl⟩) R9241
theorem R12325 : Reach 12325 := rs (se 4 (by rfl) ⟨1155, by rfl⟩) R2311
theorem R12327 : Reach 12327 := rs (se 1 (by rfl) ⟨9245, by rfl⟩) R18491
theorem R12359 : Reach 12359 := rs (se 1 (by rfl) ⟨9269, by rfl⟩) R18539
theorem R12367 : Reach 12367 := rs (se 1 (by rfl) ⟨9275, by rfl⟩) R18551
theorem R12395 : Reach 12395 := rs (se 1 (by rfl) ⟨9296, by rfl⟩) R18593
theorem R12405 : Reach 12405 := rs (se 5 (by rfl) ⟨581, by rfl⟩) R1163
theorem R12419 : Reach 12419 := rs (se 1 (by rfl) ⟨9314, by rfl⟩) R18629
theorem R12421 : Reach 12421 := rs (se 4 (by rfl) ⟨1164, by rfl⟩) R2329
theorem R12449 : Reach 12449 := rs (se 2 (by rfl) ⟨4668, by rfl⟩) R9337
theorem R12497 : Reach 12497 := rs (se 2 (by rfl) ⟨4686, by rfl⟩) R9373
theorem R12499 : Reach 12499 := rs (se 1 (by rfl) ⟨9374, by rfl⟩) R18749
theorem R12505 : Reach 12505 := rs (se 2 (by rfl) ⟨4689, by rfl⟩) R9379
theorem R12509 : Reach 12509 := rs (se 3 (by rfl) ⟨2345, by rfl⟩) R4691
theorem R12551 : Reach 12551 := rs (se 1 (by rfl) ⟨9413, by rfl⟩) R18827
theorem R12567 : Reach 12567 := rs (se 1 (by rfl) ⟨9425, by rfl⟩) R18851
theorem R12569 : Reach 12569 := rs (se 2 (by rfl) ⟨4713, by rfl⟩) R9427
theorem R12575 : Reach 12575 := rs (se 1 (by rfl) ⟨9431, by rfl⟩) R18863
theorem R12601 : Reach 12601 := rs (se 2 (by rfl) ⟨4725, by rfl⟩) R9451
theorem R12607 : Reach 12607 := rs (se 1 (by rfl) ⟨9455, by rfl⟩) R18911
theorem R12627 : Reach 12627 := rs (se 1 (by rfl) ⟨9470, by rfl⟩) R18941
theorem R12641 : Reach 12641 := rs (se 2 (by rfl) ⟨4740, by rfl⟩) R9481
theorem R12643 : Reach 12643 := rs (se 1 (by rfl) ⟨9482, by rfl⟩) R18965
theorem R12645 : Reach 12645 := rs (se 4 (by rfl) ⟨1185, by rfl⟩) R2371
theorem R12659 : Reach 12659 := rs (se 1 (by rfl) ⟨9494, by rfl⟩) R18989
theorem R12671 : Reach 12671 := rs (se 1 (by rfl) ⟨9503, by rfl⟩) R19007
theorem R12769 : Reach 12769 := rs (se 2 (by rfl) ⟨4788, by rfl⟩) R9577
theorem R12775 : Reach 12775 := rs (se 1 (by rfl) ⟨9581, by rfl⟩) R19163
theorem R12779 : Reach 12779 := rs (se 1 (by rfl) ⟨9584, by rfl⟩) R19169
theorem R14447 : Reach 14447 := rs (se 1 (by rfl) ⟨10835, by rfl⟩) R21671
theorem R48599 : Reach 48599 := rs (se 1 (by rfl) ⟨36449, by rfl⟩) R72899
theorem R48833 : Reach 48833 := rs (se 2 (by rfl) ⟨18312, by rfl⟩) R36625
theorem R49025 : Reach 49025 := rs (se 2 (by rfl) ⟨18384, by rfl⟩) R36769
theorem R49085 : Reach 49085 := rs (se 3 (by rfl) ⟨9203, by rfl⟩) R18407
theorem R49997 : Reach 49997 := rs (se 3 (by rfl) ⟨9374, by rfl⟩) R18749
theorem R50021 : Reach 50021 := rs (se 4 (by rfl) ⟨4689, by rfl⟩) R9379
theorem R50543 : Reach 50543 := rs (se 1 (by rfl) ⟨37907, by rfl⟩) R75815
theorem R186583 : Reach 186583 := rs (se 1 (by rfl) ⟨139937, by rfl⟩) R279875
theorem R23323 : Reach 23323 := rs (se 1 (by rfl) ⟨17492, by rfl⟩) R34985
theorem R23849 : Reach 23849 := rs (se 2 (by rfl) ⟨8943, by rfl⟩) R17887
theorem R24281 : Reach 24281 := rs (se 2 (by rfl) ⟨9105, by rfl⟩) R18211
theorem R24299 : Reach 24299 := rs (se 1 (by rfl) ⟨18224, by rfl⟩) R36449
theorem R24641 : Reach 24641 := rs (se 2 (by rfl) ⟨9240, by rfl⟩) R18481
theorem R417959 : Reach 417959 := rs (se 1 (by rfl) ⟨313469, by rfl⟩) R626939
theorem R24821 : Reach 24821 := rs (se 5 (by rfl) ⟨1163, by rfl⟩) R2327
theorem R24889 : Reach 24889 := rs (se 2 (by rfl) ⟨9333, by rfl⟩) R18667
theorem R25019 : Reach 25019 := rs (se 1 (by rfl) ⟨18764, by rfl⟩) R37529
theorem R25253 : Reach 25253 := rs (se 4 (by rfl) ⟨2367, by rfl⟩) R4735
theorem R25559 : Reach 25559 := rs (se 1 (by rfl) ⟨19169, by rfl⟩) R38339
theorem R26153 : Reach 26153 := rs (se 2 (by rfl) ⟨9807, by rfl⟩) R19615
theorem R390167 : Reach 390167 := rs (se 1 (by rfl) ⟨292625, by rfl⟩) R585251
theorem R97199 : Reach 97199 := rs (se 1 (by rfl) ⟨72899, by rfl⟩) R145799
theorem R196177 : Reach 196177 := rs (se 2 (by rfl) ⟨73566, by rfl⟩) R147133
theorem R65605 : Reach 65605 := rs (se 4 (by rfl) ⟨6150, by rfl⟩) R12301
theorem R32957 : Reach 32957 := rs (se 3 (by rfl) ⟨6179, by rfl⟩) R12359
theorem R65771 : Reach 65771 := rs (se 1 (by rfl) ⟨49328, by rfl⟩) R98657
theorem R33185 : Reach 33185 := rs (se 2 (by rfl) ⟨12444, by rfl⟩) R24889
theorem R33347 : Reach 33347 := rs (se 1 (by rfl) ⟨25010, by rfl⟩) R50021
theorem R33533 : Reach 33533 := rs (se 3 (by rfl) ⟨6287, by rfl⟩) R12575
theorem R33695 : Reach 33695 := rs (se 1 (by rfl) ⟨25271, by rfl⟩) R50543
theorem R1017 : Reach 1017 := rs (se 2 (by rfl) ⟨381, by rfl⟩) R763
theorem R1033 : Reach 1033 := rs (se 2 (by rfl) ⟨387, by rfl⟩) R775
theorem R2023 : Reach 2023 := rs (se 1 (by rfl) ⟨1517, by rfl⟩) R3035
theorem R2025 : Reach 2025 := rs (se 2 (by rfl) ⟨759, by rfl⟩) R1519
theorem R2027 : Reach 2027 := rs (se 1 (by rfl) ⟨1520, by rfl⟩) R3041
theorem R2035 : Reach 2035 := rs (se 1 (by rfl) ⟨1526, by rfl⟩) R3053
theorem R2043 : Reach 2043 := rs (se 1 (by rfl) ⟨1532, by rfl⟩) R3065
theorem R2047 : Reach 2047 := rs (se 1 (by rfl) ⟨1535, by rfl⟩) R3071
theorem R2049 : Reach 2049 := rs (se 2 (by rfl) ⟨768, by rfl⟩) R1537
theorem R2067 : Reach 2067 := rs (se 1 (by rfl) ⟨1550, by rfl⟩) R3101
theorem R2107 : Reach 2107 := rs (se 1 (by rfl) ⟨1580, by rfl⟩) R3161
theorem R133325 : Reach 133325 := rs (se 3 (by rfl) ⟨24998, by rfl⟩) R49997
theorem R4009 : Reach 4009 := rs (se 2 (by rfl) ⟨1503, by rfl⟩) R3007
theorem R4047 : Reach 4047 := rs (se 1 (by rfl) ⟨3035, by rfl⟩) R6071
theorem R4051 : Reach 4051 := rs (se 1 (by rfl) ⟨3038, by rfl⟩) R6077
theorem R4055 : Reach 4055 := rs (se 1 (by rfl) ⟨3041, by rfl⟩) R6083
theorem R4069 : Reach 4069 := rs (se 4 (by rfl) ⟨381, by rfl⟩) R763
theorem R4071 : Reach 4071 := rs (se 1 (by rfl) ⟨3053, by rfl⟩) R6107
theorem R4075 : Reach 4075 := rs (se 1 (by rfl) ⟨3056, by rfl⟩) R6113
theorem R4087 : Reach 4087 := rs (se 1 (by rfl) ⟨3065, by rfl⟩) R6131
theorem R4095 : Reach 4095 := rs (se 1 (by rfl) ⟨3071, by rfl⟩) R6143
theorem R4099 : Reach 4099 := rs (se 1 (by rfl) ⟨3074, by rfl⟩) R6149
theorem R4103 : Reach 4103 := rs (se 1 (by rfl) ⟨3077, by rfl⟩) R6155
theorem R4105 : Reach 4105 := rs (se 2 (by rfl) ⟨1539, by rfl⟩) R3079
theorem R4133 : Reach 4133 := rs (se 4 (by rfl) ⟨387, by rfl⟩) R775
theorem R4139 : Reach 4139 := rs (se 1 (by rfl) ⟨3104, by rfl⟩) R6209
theorem R4169 : Reach 4169 := rs (se 2 (by rfl) ⟨1563, by rfl⟩) R3127
theorem R4215 : Reach 4215 := rs (se 1 (by rfl) ⟨3161, by rfl⟩) R6323
theorem R4219 : Reach 4219 := rs (se 1 (by rfl) ⟨3164, by rfl⟩) R6329
theorem R4223 : Reach 4223 := rs (se 1 (by rfl) ⟨3167, by rfl⟩) R6335
theorem R269183 : Reach 269183 := rs (se 1 (by rfl) ⟨201887, by rfl⟩) R403775
theorem R8019 : Reach 8019 := rs (se 1 (by rfl) ⟨6014, by rfl⟩) R12029
theorem R8093 : Reach 8093 := rs (se 3 (by rfl) ⟨1517, by rfl⟩) R3035
theorem R8101 : Reach 8101 := rs (se 4 (by rfl) ⟨759, by rfl⟩) R1519
theorem R8109 : Reach 8109 := rs (se 3 (by rfl) ⟨1520, by rfl⟩) R3041
theorem R8137 : Reach 8137 := rs (se 2 (by rfl) ⟨3051, by rfl⟩) R6103
theorem R8141 : Reach 8141 := rs (se 3 (by rfl) ⟨1526, by rfl⟩) R3053
theorem R8143 : Reach 8143 := rs (se 1 (by rfl) ⟨6107, by rfl⟩) R12215
theorem R8145 : Reach 8145 := rs (se 2 (by rfl) ⟨3054, by rfl⟩) R6109
theorem R8151 : Reach 8151 := rs (se 1 (by rfl) ⟨6113, by rfl⟩) R12227
theorem R8167 : Reach 8167 := rs (se 1 (by rfl) ⟨6125, by rfl⟩) R12251
theorem R8173 : Reach 8173 := rs (se 3 (by rfl) ⟨1532, by rfl⟩) R3065
theorem R8189 : Reach 8189 := rs (se 3 (by rfl) ⟨1535, by rfl⟩) R3071
theorem R8191 : Reach 8191 := rs (se 1 (by rfl) ⟨6143, by rfl⟩) R12287
theorem R8197 : Reach 8197 := rs (se 4 (by rfl) ⟨768, by rfl⟩) R1537
theorem R8203 : Reach 8203 := rs (se 1 (by rfl) ⟨6152, by rfl⟩) R12305
theorem R8207 : Reach 8207 := rs (se 1 (by rfl) ⟨6155, by rfl⟩) R12311
theorem R8211 : Reach 8211 := rs (se 1 (by rfl) ⟨6158, by rfl⟩) R12317
theorem R8217 : Reach 8217 := rs (se 2 (by rfl) ⟨3081, by rfl⟩) R6163
theorem R8239 : Reach 8239 := rs (se 1 (by rfl) ⟨6179, by rfl⟩) R12359
theorem R8263 : Reach 8263 := rs (se 1 (by rfl) ⟨6197, by rfl⟩) R12395
theorem R8269 : Reach 8269 := rs (se 3 (by rfl) ⟨1550, by rfl⟩) R3101
theorem R8273 : Reach 8273 := rs (se 2 (by rfl) ⟨3102, by rfl⟩) R6205
theorem R8279 : Reach 8279 := rs (se 1 (by rfl) ⟨6209, by rfl⟩) R12419
theorem R8281 : Reach 8281 := rs (se 2 (by rfl) ⟨3105, by rfl⟩) R6211
theorem R8299 : Reach 8299 := rs (se 1 (by rfl) ⟨6224, by rfl⟩) R12449
theorem R8331 : Reach 8331 := rs (se 1 (by rfl) ⟨6248, by rfl⟩) R12497
theorem R8337 : Reach 8337 := rs (se 2 (by rfl) ⟨3126, by rfl⟩) R6253
theorem R8339 : Reach 8339 := rs (se 1 (by rfl) ⟨6254, by rfl⟩) R12509
theorem R8367 : Reach 8367 := rs (se 1 (by rfl) ⟨6275, by rfl⟩) R12551
theorem R8377 : Reach 8377 := rs (se 2 (by rfl) ⟨3141, by rfl⟩) R6283
theorem R8379 : Reach 8379 := rs (se 1 (by rfl) ⟨6284, by rfl⟩) R12569
theorem R8383 : Reach 8383 := rs (se 1 (by rfl) ⟨6287, by rfl⟩) R12575
theorem R8417 : Reach 8417 := rs (se 2 (by rfl) ⟨3156, by rfl⟩) R6313
theorem R8427 : Reach 8427 := rs (se 1 (by rfl) ⟨6320, by rfl⟩) R12641
theorem R8429 : Reach 8429 := rs (se 3 (by rfl) ⟨1580, by rfl⟩) R3161
theorem R8439 : Reach 8439 := rs (se 1 (by rfl) ⟨6329, by rfl⟩) R12659
theorem R8447 : Reach 8447 := rs (se 1 (by rfl) ⟨6335, by rfl⟩) R12671
theorem R8519 : Reach 8519 := rs (se 1 (by rfl) ⟨6389, by rfl⟩) R12779
theorem R9631 : Reach 9631 := rs (se 1 (by rfl) ⟨7223, by rfl⟩) R14447
theorem R15673 : Reach 15673 := rs (se 2 (by rfl) ⟨5877, by rfl⟩) R11755
theorem R15899 : Reach 15899 := rs (se 1 (by rfl) ⟨11924, by rfl⟩) R23849
theorem R16037 : Reach 16037 := rs (se 4 (by rfl) ⟨1503, by rfl⟩) R3007
theorem R16187 : Reach 16187 := rs (se 1 (by rfl) ⟨12140, by rfl⟩) R24281
theorem R16199 : Reach 16199 := rs (se 1 (by rfl) ⟨12149, by rfl⟩) R24299
theorem R16205 : Reach 16205 := rs (se 3 (by rfl) ⟨3038, by rfl⟩) R6077
theorem R16265 : Reach 16265 := rs (se 2 (by rfl) ⟨6099, by rfl⟩) R12199
theorem R16277 : Reach 16277 := rs (se 6 (by rfl) ⟨381, by rfl⟩) R763
theorem R16301 : Reach 16301 := rs (se 3 (by rfl) ⟨3056, by rfl⟩) R6113
theorem R16349 : Reach 16349 := rs (se 3 (by rfl) ⟨3065, by rfl⟩) R6131
theorem R16361 : Reach 16361 := rs (se 2 (by rfl) ⟨6135, by rfl⟩) R12271
theorem R16397 : Reach 16397 := rs (se 3 (by rfl) ⟨3074, by rfl⟩) R6149
theorem R16421 : Reach 16421 := rs (se 4 (by rfl) ⟨1539, by rfl⟩) R3079
theorem R16427 : Reach 16427 := rs (se 1 (by rfl) ⟨12320, by rfl⟩) R24641
theorem R16433 : Reach 16433 := rs (se 2 (by rfl) ⟨6162, by rfl⟩) R12325
theorem R278639 : Reach 278639 := rs (se 1 (by rfl) ⟨208979, by rfl⟩) R417959
theorem R16547 : Reach 16547 := rs (se 1 (by rfl) ⟨12410, by rfl⟩) R24821
theorem R16673 : Reach 16673 := rs (se 2 (by rfl) ⟨6252, by rfl⟩) R12505
theorem R16679 : Reach 16679 := rs (se 1 (by rfl) ⟨12509, by rfl⟩) R25019
theorem R16835 : Reach 16835 := rs (se 1 (by rfl) ⟨12626, by rfl⟩) R25253
theorem R16861 : Reach 16861 := rs (se 3 (by rfl) ⟨3161, by rfl⟩) R6323
theorem R16877 : Reach 16877 := rs (se 3 (by rfl) ⟨3164, by rfl⟩) R6329
theorem R17033 : Reach 17033 := rs (se 2 (by rfl) ⟨6387, by rfl⟩) R12775
theorem R17039 : Reach 17039 := rs (se 1 (by rfl) ⟨12779, by rfl⟩) R25559
theorem R17435 : Reach 17435 := rs (se 1 (by rfl) ⟨13076, by rfl⟩) R26153
theorem R248777 : Reach 248777 := rs (se 2 (by rfl) ⟨93291, by rfl⟩) R186583
theorem R62693 : Reach 62693 := rs (se 4 (by rfl) ⟨5877, by rfl⟩) R11755
theorem R260111 : Reach 260111 := rs (se 1 (by rfl) ⟨195083, by rfl⟩) R390167
theorem R31097 : Reach 31097 := rs (se 2 (by rfl) ⟨11661, by rfl⟩) R23323
theorem R64799 : Reach 64799 := rs (se 1 (by rfl) ⟨48599, by rfl⟩) R97199
theorem R261569 : Reach 261569 := rs (se 2 (by rfl) ⟨98088, by rfl⟩) R196177
theorem R32399 : Reach 32399 := rs (se 1 (by rfl) ⟨24299, by rfl⟩) R48599
theorem R32555 : Reach 32555 := rs (se 1 (by rfl) ⟨24416, by rfl⟩) R48833
theorem R32669 : Reach 32669 := rs (se 3 (by rfl) ⟨6125, by rfl⟩) R12251
theorem R32683 : Reach 32683 := rs (se 1 (by rfl) ⟨24512, by rfl⟩) R49025
theorem R32723 : Reach 32723 := rs (se 1 (by rfl) ⟨24542, by rfl⟩) R49085
theorem R1351 : Reach 1351 := rs (se 1 (by rfl) ⟨1013, by rfl⟩) R2027
theorem R1377 : Reach 1377 := rs (se 2 (by rfl) ⟨516, by rfl⟩) R1033
theorem R165851 : Reach 165851 := rs (se 1 (by rfl) ⟨124388, by rfl⟩) R248777
theorem R2697 : Reach 2697 := rs (se 2 (by rfl) ⟨1011, by rfl⟩) R2023
theorem R2703 : Reach 2703 := rs (se 1 (by rfl) ⟨2027, by rfl⟩) R4055
theorem R2713 : Reach 2713 := rs (se 2 (by rfl) ⟨1017, by rfl⟩) R2035
theorem R2729 : Reach 2729 := rs (se 2 (by rfl) ⟨1023, by rfl⟩) R2047
theorem R2735 : Reach 2735 := rs (se 1 (by rfl) ⟨2051, by rfl⟩) R4103
theorem R2755 : Reach 2755 := rs (se 1 (by rfl) ⟨2066, by rfl⟩) R4133
theorem R2759 : Reach 2759 := rs (se 1 (by rfl) ⟨2069, by rfl⟩) R4139
theorem R2779 : Reach 2779 := rs (se 1 (by rfl) ⟨2084, by rfl⟩) R4169
theorem R2809 : Reach 2809 := rs (se 2 (by rfl) ⟨1053, by rfl⟩) R2107
theorem R2815 : Reach 2815 := rs (se 1 (by rfl) ⟨2111, by rfl⟩) R4223
theorem R5345 : Reach 5345 := rs (se 2 (by rfl) ⟨2004, by rfl⟩) R4009
theorem R5395 : Reach 5395 := rs (se 1 (by rfl) ⟨4046, by rfl⟩) R8093
theorem R5401 : Reach 5401 := rs (se 2 (by rfl) ⟨2025, by rfl⟩) R4051
theorem R5405 : Reach 5405 := rs (se 3 (by rfl) ⟨1013, by rfl⟩) R2027
theorem R5425 : Reach 5425 := rs (se 2 (by rfl) ⟨2034, by rfl⟩) R4069
theorem R5427 : Reach 5427 := rs (se 1 (by rfl) ⟨4070, by rfl⟩) R8141
theorem R5433 : Reach 5433 := rs (se 2 (by rfl) ⟨2037, by rfl⟩) R4075
theorem R5449 : Reach 5449 := rs (se 2 (by rfl) ⟨2043, by rfl⟩) R4087
theorem R5459 : Reach 5459 := rs (se 1 (by rfl) ⟨4094, by rfl⟩) R8189
theorem R5465 : Reach 5465 := rs (se 2 (by rfl) ⟨2049, by rfl⟩) R4099
theorem R5471 : Reach 5471 := rs (se 1 (by rfl) ⟨4103, by rfl⟩) R8207
theorem R5473 : Reach 5473 := rs (se 2 (by rfl) ⟨2052, by rfl⟩) R4105
theorem R693629 : Reach 693629 := rs (se 3 (by rfl) ⟨130055, by rfl⟩) R260111
theorem R5509 : Reach 5509 := rs (se 4 (by rfl) ⟨516, by rfl⟩) R1033
theorem R5515 : Reach 5515 := rs (se 1 (by rfl) ⟨4136, by rfl⟩) R8273
theorem R5519 : Reach 5519 := rs (se 1 (by rfl) ⟨4139, by rfl⟩) R8279
theorem R5559 : Reach 5559 := rs (se 1 (by rfl) ⟨4169, by rfl⟩) R8339
theorem R5611 : Reach 5611 := rs (se 1 (by rfl) ⟨4208, by rfl⟩) R8417
theorem R5619 : Reach 5619 := rs (se 1 (by rfl) ⟨4214, by rfl⟩) R8429
theorem R5625 : Reach 5625 := rs (se 2 (by rfl) ⟨2109, by rfl⟩) R4219
theorem R5631 : Reach 5631 := rs (se 1 (by rfl) ⟨4223, by rfl⟩) R8447
theorem R5679 : Reach 5679 := rs (se 1 (by rfl) ⟨4259, by rfl⟩) R8519
theorem R41795 : Reach 41795 := rs (se 1 (by rfl) ⟨31346, by rfl⟩) R62693
theorem R697517 : Reach 697517 := rs (se 3 (by rfl) ⟨130784, by rfl⟩) R261569
theorem R43199 : Reach 43199 := rs (se 1 (by rfl) ⟨32399, by rfl⟩) R64799
theorem R43253 : Reach 43253 := rs (se 5 (by rfl) ⟨2027, by rfl⟩) R4055
theorem R10599 : Reach 10599 := rs (se 1 (by rfl) ⟨7949, by rfl⟩) R15899
theorem R10691 : Reach 10691 := rs (se 1 (by rfl) ⟨8018, by rfl⟩) R16037
theorem R10789 : Reach 10789 := rs (se 4 (by rfl) ⟨1011, by rfl⟩) R2023
theorem R10791 : Reach 10791 := rs (se 1 (by rfl) ⟨8093, by rfl⟩) R16187
theorem R10799 : Reach 10799 := rs (se 1 (by rfl) ⟨8099, by rfl⟩) R16199
theorem R10801 : Reach 10801 := rs (se 2 (by rfl) ⟨4050, by rfl⟩) R8101
theorem R10803 : Reach 10803 := rs (se 1 (by rfl) ⟨8102, by rfl⟩) R16205
theorem R43577 : Reach 43577 := rs (se 2 (by rfl) ⟨16341, by rfl⟩) R32683
theorem R10813 : Reach 10813 := rs (se 3 (by rfl) ⟨2027, by rfl⟩) R4055
theorem R10843 : Reach 10843 := rs (se 1 (by rfl) ⟨8132, by rfl⟩) R16265
theorem R10849 : Reach 10849 := rs (se 2 (by rfl) ⟨4068, by rfl⟩) R8137
theorem R10851 : Reach 10851 := rs (se 1 (by rfl) ⟨8138, by rfl⟩) R16277
theorem R10853 : Reach 10853 := rs (se 4 (by rfl) ⟨1017, by rfl⟩) R2035
theorem R10857 : Reach 10857 := rs (se 2 (by rfl) ⟨4071, by rfl⟩) R8143
theorem R10867 : Reach 10867 := rs (se 1 (by rfl) ⟨8150, by rfl⟩) R16301
theorem R10889 : Reach 10889 := rs (se 2 (by rfl) ⟨4083, by rfl⟩) R8167
theorem R10897 : Reach 10897 := rs (se 2 (by rfl) ⟨4086, by rfl⟩) R8173
theorem R10899 : Reach 10899 := rs (se 1 (by rfl) ⟨8174, by rfl⟩) R16349
theorem R10907 : Reach 10907 := rs (se 1 (by rfl) ⟨8180, by rfl⟩) R16361
theorem R43685 : Reach 43685 := rs (se 4 (by rfl) ⟨4095, by rfl⟩) R8191
theorem R10917 : Reach 10917 := rs (se 4 (by rfl) ⟨1023, by rfl⟩) R2047
theorem R10921 : Reach 10921 := rs (se 2 (by rfl) ⟨4095, by rfl⟩) R8191
theorem R10929 : Reach 10929 := rs (se 2 (by rfl) ⟨4098, by rfl⟩) R8197
theorem R10931 : Reach 10931 := rs (se 1 (by rfl) ⟨8198, by rfl⟩) R16397
theorem R10937 : Reach 10937 := rs (se 2 (by rfl) ⟨4101, by rfl⟩) R8203
theorem R10941 : Reach 10941 := rs (se 3 (by rfl) ⟨2051, by rfl⟩) R4103
theorem R10947 : Reach 10947 := rs (se 1 (by rfl) ⟨8210, by rfl⟩) R16421
theorem R10951 : Reach 10951 := rs (se 1 (by rfl) ⟨8213, by rfl⟩) R16427
theorem R10955 : Reach 10955 := rs (se 1 (by rfl) ⟨8216, by rfl⟩) R16433
theorem R10985 : Reach 10985 := rs (se 2 (by rfl) ⟨4119, by rfl⟩) R8239
theorem R11017 : Reach 11017 := rs (se 2 (by rfl) ⟨4131, by rfl⟩) R8263
theorem R11021 : Reach 11021 := rs (se 3 (by rfl) ⟨2066, by rfl⟩) R4133
theorem R11025 : Reach 11025 := rs (se 2 (by rfl) ⟨4134, by rfl⟩) R8269
theorem R11031 : Reach 11031 := rs (se 1 (by rfl) ⟨8273, by rfl⟩) R16547
theorem R11037 : Reach 11037 := rs (se 3 (by rfl) ⟨2069, by rfl⟩) R4139
theorem R11041 : Reach 11041 := rs (se 2 (by rfl) ⟨4140, by rfl⟩) R8281
theorem R11065 : Reach 11065 := rs (se 2 (by rfl) ⟨4149, by rfl⟩) R8299
theorem R43847 : Reach 43847 := rs (se 1 (by rfl) ⟨32885, by rfl⟩) R65771
theorem R11115 : Reach 11115 := rs (se 1 (by rfl) ⟨8336, by rfl⟩) R16673
theorem R11117 : Reach 11117 := rs (se 3 (by rfl) ⟨2084, by rfl⟩) R4169
theorem R11119 : Reach 11119 := rs (se 1 (by rfl) ⟨8339, by rfl⟩) R16679
theorem R11169 : Reach 11169 := rs (se 2 (by rfl) ⟨4188, by rfl⟩) R8377
theorem R11177 : Reach 11177 := rs (se 2 (by rfl) ⟨4191, by rfl⟩) R8383
theorem R11223 : Reach 11223 := rs (se 1 (by rfl) ⟨8417, by rfl⟩) R16835
theorem R11237 : Reach 11237 := rs (se 4 (by rfl) ⟨1053, by rfl⟩) R2107
theorem R11251 : Reach 11251 := rs (se 1 (by rfl) ⟨8438, by rfl⟩) R16877
theorem R11261 : Reach 11261 := rs (se 3 (by rfl) ⟨2111, by rfl⟩) R4223
theorem R11355 : Reach 11355 := rs (se 1 (by rfl) ⟨8516, by rfl⟩) R17033
theorem R11359 : Reach 11359 := rs (se 1 (by rfl) ⟨8519, by rfl⟩) R17039
theorem R44165 : Reach 44165 := rs (se 4 (by rfl) ⟨4140, by rfl⟩) R8281
theorem R11623 : Reach 11623 := rs (se 1 (by rfl) ⟨8717, by rfl⟩) R17435
theorem R46493 : Reach 46493 := rs (se 3 (by rfl) ⟨8717, by rfl⟩) R17435
theorem R179455 : Reach 179455 := rs (se 1 (by rfl) ⟨134591, by rfl⟩) R269183
theorem R20731 : Reach 20731 := rs (se 1 (by rfl) ⟨15548, by rfl⟩) R31097
theorem R20897 : Reach 20897 := rs (se 2 (by rfl) ⟨7836, by rfl⟩) R15673
theorem R86933 : Reach 86933 := rs (se 6 (by rfl) ⟨2037, by rfl⟩) R4075
theorem R21581 : Reach 21581 := rs (se 3 (by rfl) ⟨4046, by rfl⟩) R8093
theorem R21599 : Reach 21599 := rs (se 1 (by rfl) ⟨16199, by rfl⟩) R32399
theorem R21703 : Reach 21703 := rs (se 1 (by rfl) ⟨16277, by rfl⟩) R32555
theorem R21779 : Reach 21779 := rs (se 1 (by rfl) ⟨16334, by rfl⟩) R32669
theorem R21797 : Reach 21797 := rs (se 4 (by rfl) ⟨2043, by rfl⟩) R4087
theorem R21815 : Reach 21815 := rs (se 1 (by rfl) ⟨16361, by rfl⟩) R32723
theorem R185759 : Reach 185759 := rs (se 1 (by rfl) ⟨139319, by rfl⟩) R278639
theorem R87473 : Reach 87473 := rs (se 2 (by rfl) ⟨32802, by rfl⟩) R65605
theorem R21971 : Reach 21971 := rs (se 1 (by rfl) ⟨16478, by rfl⟩) R32957
theorem R22123 : Reach 22123 := rs (se 1 (by rfl) ⟨16592, by rfl⟩) R33185
theorem R22231 : Reach 22231 := rs (se 1 (by rfl) ⟨16673, by rfl⟩) R33347
theorem R22355 : Reach 22355 := rs (se 1 (by rfl) ⟨16766, by rfl⟩) R33533
theorem R22445 : Reach 22445 := rs (se 3 (by rfl) ⟨4208, by rfl⟩) R8417
theorem R22463 : Reach 22463 := rs (se 1 (by rfl) ⟨16847, by rfl⟩) R33695
theorem R22477 : Reach 22477 := rs (se 3 (by rfl) ⟨4214, by rfl⟩) R8429
theorem R22481 : Reach 22481 := rs (se 2 (by rfl) ⟨8430, by rfl⟩) R16861
theorem R88883 : Reach 88883 := rs (se 1 (by rfl) ⟨66662, by rfl⟩) R133325
theorem R89909 : Reach 89909 := rs (se 5 (by rfl) ⟨4214, by rfl⟩) R8429
theorem R1801 : Reach 1801 := rs (se 2 (by rfl) ⟨675, by rfl⟩) R1351
theorem R1819 : Reach 1819 := rs (se 1 (by rfl) ⟨1364, by rfl⟩) R2729
theorem R1823 : Reach 1823 := rs (se 1 (by rfl) ⟨1367, by rfl⟩) R2735
theorem R1839 : Reach 1839 := rs (se 1 (by rfl) ⟨1379, by rfl⟩) R2759
theorem R231821 : Reach 231821 := rs (se 3 (by rfl) ⟨43466, by rfl⟩) R86933
theorem R3563 : Reach 3563 := rs (se 1 (by rfl) ⟨2672, by rfl⟩) R5345
theorem R3603 : Reach 3603 := rs (se 1 (by rfl) ⟨2702, by rfl⟩) R5405
theorem R3617 : Reach 3617 := rs (se 2 (by rfl) ⟨1356, by rfl⟩) R2713
theorem R3639 : Reach 3639 := rs (se 1 (by rfl) ⟨2729, by rfl⟩) R5459
theorem R3643 : Reach 3643 := rs (se 1 (by rfl) ⟨2732, by rfl⟩) R5465
theorem R3647 : Reach 3647 := rs (se 1 (by rfl) ⟨2735, by rfl⟩) R5471
theorem R462419 : Reach 462419 := rs (se 1 (by rfl) ⟨346814, by rfl⟩) R693629
theorem R3673 : Reach 3673 := rs (se 2 (by rfl) ⟨1377, by rfl⟩) R2755
theorem R3679 : Reach 3679 := rs (se 1 (by rfl) ⟨2759, by rfl⟩) R5519
theorem R3705 : Reach 3705 := rs (se 2 (by rfl) ⟨1389, by rfl⟩) R2779
theorem R3745 : Reach 3745 := rs (se 2 (by rfl) ⟨1404, by rfl⟩) R2809
theorem R3753 : Reach 3753 := rs (se 2 (by rfl) ⟨1407, by rfl⟩) R2815
theorem R465011 : Reach 465011 := rs (se 1 (by rfl) ⟨348758, by rfl⟩) R697517
theorem R7127 : Reach 7127 := rs (se 1 (by rfl) ⟨5345, by rfl⟩) R10691
theorem R7193 : Reach 7193 := rs (se 2 (by rfl) ⟨2697, by rfl⟩) R5395
theorem R7199 : Reach 7199 := rs (se 1 (by rfl) ⟨5399, by rfl⟩) R10799
theorem R7201 : Reach 7201 := rs (se 2 (by rfl) ⟨2700, by rfl⟩) R5401
theorem R7205 : Reach 7205 := rs (se 4 (by rfl) ⟨675, by rfl⟩) R1351
theorem R7233 : Reach 7233 := rs (se 2 (by rfl) ⟨2712, by rfl⟩) R5425
theorem R7235 : Reach 7235 := rs (se 1 (by rfl) ⟨5426, by rfl⟩) R10853
theorem R7259 : Reach 7259 := rs (se 1 (by rfl) ⟨5444, by rfl⟩) R10889
theorem R7265 : Reach 7265 := rs (se 2 (by rfl) ⟨2724, by rfl⟩) R5449
theorem R7271 : Reach 7271 := rs (se 1 (by rfl) ⟨5453, by rfl⟩) R10907
theorem R7277 : Reach 7277 := rs (se 3 (by rfl) ⟨1364, by rfl⟩) R2729
theorem R7287 : Reach 7287 := rs (se 1 (by rfl) ⟨5465, by rfl⟩) R10931
theorem R7291 : Reach 7291 := rs (se 1 (by rfl) ⟨5468, by rfl⟩) R10937
theorem R7293 : Reach 7293 := rs (se 3 (by rfl) ⟨1367, by rfl⟩) R2735
theorem R7297 : Reach 7297 := rs (se 2 (by rfl) ⟨2736, by rfl⟩) R5473
theorem R7303 : Reach 7303 := rs (se 1 (by rfl) ⟨5477, by rfl⟩) R10955
theorem R7323 : Reach 7323 := rs (se 1 (by rfl) ⟨5492, by rfl⟩) R10985
theorem R7345 : Reach 7345 := rs (se 2 (by rfl) ⟨2754, by rfl⟩) R5509
theorem R7347 : Reach 7347 := rs (se 1 (by rfl) ⟨5510, by rfl⟩) R11021
theorem R7353 : Reach 7353 := rs (se 2 (by rfl) ⟨2757, by rfl⟩) R5515
theorem R7357 : Reach 7357 := rs (se 3 (by rfl) ⟨1379, by rfl⟩) R2759
theorem R7411 : Reach 7411 := rs (se 1 (by rfl) ⟨5558, by rfl⟩) R11117
theorem R7451 : Reach 7451 := rs (se 1 (by rfl) ⟨5588, by rfl⟩) R11177
theorem R7481 : Reach 7481 := rs (se 2 (by rfl) ⟨2805, by rfl⟩) R5611
theorem R7491 : Reach 7491 := rs (se 1 (by rfl) ⟨5618, by rfl⟩) R11237
theorem R7507 : Reach 7507 := rs (se 1 (by rfl) ⟨5630, by rfl⟩) R11261
theorem R239273 : Reach 239273 := rs (se 2 (by rfl) ⟨89727, by rfl⟩) R179455
theorem R110567 : Reach 110567 := rs (se 1 (by rfl) ⟨82925, by rfl⟩) R165851
theorem R13931 : Reach 13931 := rs (se 1 (by rfl) ⟨10448, by rfl⟩) R20897
theorem R14387 : Reach 14387 := rs (se 1 (by rfl) ⟨10790, by rfl⟩) R21581
theorem R14399 : Reach 14399 := rs (se 1 (by rfl) ⟨10799, by rfl⟩) R21599
theorem R14413 : Reach 14413 := rs (se 3 (by rfl) ⟨2702, by rfl⟩) R5405
theorem R14417 : Reach 14417 := rs (se 2 (by rfl) ⟨5406, by rfl⟩) R10813
theorem R14465 : Reach 14465 := rs (se 2 (by rfl) ⟨5424, by rfl⟩) R10849
theorem R14489 : Reach 14489 := rs (se 2 (by rfl) ⟨5433, by rfl⟩) R10867
theorem R14519 : Reach 14519 := rs (se 1 (by rfl) ⟨10889, by rfl⟩) R21779
theorem R14531 : Reach 14531 := rs (se 1 (by rfl) ⟨10898, by rfl⟩) R21797
theorem R14543 : Reach 14543 := rs (se 1 (by rfl) ⟨10907, by rfl⟩) R21815
theorem R14561 : Reach 14561 := rs (se 2 (by rfl) ⟨5460, by rfl⟩) R10921
theorem R14573 : Reach 14573 := rs (se 3 (by rfl) ⟨2732, by rfl⟩) R5465
theorem R14647 : Reach 14647 := rs (se 1 (by rfl) ⟨10985, by rfl⟩) R21971
theorem R14693 : Reach 14693 := rs (se 4 (by rfl) ⟨1377, by rfl⟩) R2755
theorem R14717 : Reach 14717 := rs (se 3 (by rfl) ⟨2759, by rfl⟩) R5519
theorem R14753 : Reach 14753 := rs (se 2 (by rfl) ⟨5532, by rfl⟩) R11065
theorem R14825 : Reach 14825 := rs (se 2 (by rfl) ⟨5559, by rfl⟩) R11119
theorem R14903 : Reach 14903 := rs (se 1 (by rfl) ⟨11177, by rfl⟩) R22355
theorem R14963 : Reach 14963 := rs (se 1 (by rfl) ⟨11222, by rfl⟩) R22445
theorem R14975 : Reach 14975 := rs (se 1 (by rfl) ⟨11231, by rfl⟩) R22463
theorem R14981 : Reach 14981 := rs (se 4 (by rfl) ⟨1404, by rfl⟩) R2809
theorem R14987 : Reach 14987 := rs (se 1 (by rfl) ⟨11240, by rfl⟩) R22481
theorem R15013 : Reach 15013 := rs (se 4 (by rfl) ⟨1407, by rfl⟩) R2815
theorem R15497 : Reach 15497 := rs (se 2 (by rfl) ⟨5811, by rfl⟩) R11623
theorem R57955 : Reach 57955 := rs (se 1 (by rfl) ⟨43466, by rfl⟩) R86933
theorem R58229 : Reach 58229 := rs (se 5 (by rfl) ⟨2729, by rfl⟩) R5459
theorem R123839 : Reach 123839 := rs (se 1 (by rfl) ⟨92879, by rfl⟩) R185759
theorem R58315 : Reach 58315 := rs (se 1 (by rfl) ⟨43736, by rfl⟩) R87473
theorem R58589 : Reach 58589 := rs (se 3 (by rfl) ⟨10985, by rfl⟩) R21971
theorem R59255 : Reach 59255 := rs (se 1 (by rfl) ⟨44441, by rfl⟩) R88883
theorem R59939 : Reach 59939 := rs (se 1 (by rfl) ⟨44954, by rfl⟩) R89909
theorem R27641 : Reach 27641 := rs (se 2 (by rfl) ⟨10365, by rfl⟩) R20731
theorem R27863 : Reach 27863 := rs (se 1 (by rfl) ⟨20897, by rfl⟩) R41795
theorem R28799 : Reach 28799 := rs (se 1 (by rfl) ⟨21599, by rfl⟩) R43199
theorem R28835 : Reach 28835 := rs (se 1 (by rfl) ⟨21626, by rfl⟩) R43253
theorem R28937 : Reach 28937 := rs (se 2 (by rfl) ⟨10851, by rfl⟩) R21703
theorem R29051 : Reach 29051 := rs (se 1 (by rfl) ⟨21788, by rfl⟩) R43577
theorem R29123 : Reach 29123 := rs (se 1 (by rfl) ⟨21842, by rfl⟩) R43685
theorem R29213 : Reach 29213 := rs (se 3 (by rfl) ⟨5477, by rfl⟩) R10955
theorem R29231 : Reach 29231 := rs (se 1 (by rfl) ⟨21923, by rfl⟩) R43847
theorem R29429 : Reach 29429 := rs (se 5 (by rfl) ⟨1379, by rfl⟩) R2759
theorem R29443 : Reach 29443 := rs (se 1 (by rfl) ⟨22082, by rfl⟩) R44165
theorem R29497 : Reach 29497 := rs (se 2 (by rfl) ⟨11061, by rfl⟩) R22123
theorem R29641 : Reach 29641 := rs (se 2 (by rfl) ⟨11115, by rfl⟩) R22231
theorem R29645 : Reach 29645 := rs (se 3 (by rfl) ⟨5558, by rfl⟩) R11117
theorem R29969 : Reach 29969 := rs (se 2 (by rfl) ⟨11238, by rfl⟩) R22477
theorem R30995 : Reach 30995 := rs (se 1 (by rfl) ⟨23246, by rfl⟩) R46493
theorem R1215 : Reach 1215 := rs (se 1 (by rfl) ⟨911, by rfl⟩) R1823
theorem R2375 : Reach 2375 := rs (se 1 (by rfl) ⟨1781, by rfl⟩) R3563
theorem R2401 : Reach 2401 := rs (se 2 (by rfl) ⟨900, by rfl⟩) R1801
theorem R2411 : Reach 2411 := rs (se 1 (by rfl) ⟨1808, by rfl⟩) R3617
theorem R2425 : Reach 2425 := rs (se 2 (by rfl) ⟨909, by rfl⟩) R1819
theorem R2431 : Reach 2431 := rs (se 1 (by rfl) ⟨1823, by rfl⟩) R3647
theorem R4751 : Reach 4751 := rs (se 1 (by rfl) ⟨3563, by rfl⟩) R7127
theorem R4795 : Reach 4795 := rs (se 1 (by rfl) ⟨3596, by rfl⟩) R7193
theorem R4799 : Reach 4799 := rs (se 1 (by rfl) ⟨3599, by rfl⟩) R7199
theorem R4803 : Reach 4803 := rs (se 1 (by rfl) ⟨3602, by rfl⟩) R7205
theorem R4823 : Reach 4823 := rs (se 1 (by rfl) ⟨3617, by rfl⟩) R7235
theorem R4839 : Reach 4839 := rs (se 1 (by rfl) ⟨3629, by rfl⟩) R7259
theorem R4843 : Reach 4843 := rs (se 1 (by rfl) ⟨3632, by rfl⟩) R7265
theorem R4847 : Reach 4847 := rs (se 1 (by rfl) ⟨3635, by rfl⟩) R7271
theorem R4851 : Reach 4851 := rs (se 1 (by rfl) ⟨3638, by rfl⟩) R7277
theorem R4857 : Reach 4857 := rs (se 2 (by rfl) ⟨1821, by rfl⟩) R3643
theorem R4861 : Reach 4861 := rs (se 3 (by rfl) ⟨911, by rfl⟩) R1823
theorem R4897 : Reach 4897 := rs (se 2 (by rfl) ⟨1836, by rfl⟩) R3673
theorem R4905 : Reach 4905 := rs (se 2 (by rfl) ⟨1839, by rfl⟩) R3679
theorem R4967 : Reach 4967 := rs (se 1 (by rfl) ⟨3725, by rfl⟩) R7451
theorem R4987 : Reach 4987 := rs (se 1 (by rfl) ⟨3740, by rfl⟩) R7481
theorem R4993 : Reach 4993 := rs (se 2 (by rfl) ⟨1872, by rfl⟩) R3745
theorem R38717 : Reach 38717 := rs (se 3 (by rfl) ⟨7259, by rfl⟩) R14519
theorem R38819 : Reach 38819 := rs (se 1 (by rfl) ⟨29114, by rfl⟩) R58229
theorem R39059 : Reach 39059 := rs (se 1 (by rfl) ⟨29294, by rfl⟩) R58589
theorem R39257 : Reach 39257 := rs (se 2 (by rfl) ⟨14721, by rfl⟩) R29443
theorem R39329 : Reach 39329 := rs (se 2 (by rfl) ⟨14748, by rfl⟩) R29497
theorem R39503 : Reach 39503 := rs (se 1 (by rfl) ⟨29627, by rfl⟩) R59255
theorem R39521 : Reach 39521 := rs (se 2 (by rfl) ⟨14820, by rfl⟩) R29641
theorem R39959 : Reach 39959 := rs (se 1 (by rfl) ⟨29969, by rfl⟩) R59939
theorem R73711 : Reach 73711 := rs (se 1 (by rfl) ⟨55283, by rfl⟩) R110567
theorem R9287 : Reach 9287 := rs (se 1 (by rfl) ⟨6965, by rfl⟩) R13931
theorem R9501 : Reach 9501 := rs (se 3 (by rfl) ⟨1781, by rfl⟩) R3563
theorem R9591 : Reach 9591 := rs (se 1 (by rfl) ⟨7193, by rfl⟩) R14387
theorem R9599 : Reach 9599 := rs (se 1 (by rfl) ⟨7199, by rfl⟩) R14399
theorem R9601 : Reach 9601 := rs (se 2 (by rfl) ⟨3600, by rfl⟩) R7201
theorem R9605 : Reach 9605 := rs (se 4 (by rfl) ⟨900, by rfl⟩) R1801
theorem R9611 : Reach 9611 := rs (se 1 (by rfl) ⟨7208, by rfl⟩) R14417
theorem R9643 : Reach 9643 := rs (se 1 (by rfl) ⟨7232, by rfl⟩) R14465
theorem R9645 : Reach 9645 := rs (se 3 (by rfl) ⟨1808, by rfl⟩) R3617
theorem R9659 : Reach 9659 := rs (se 1 (by rfl) ⟨7244, by rfl⟩) R14489
theorem R9679 : Reach 9679 := rs (se 1 (by rfl) ⟨7259, by rfl⟩) R14519
theorem R9687 : Reach 9687 := rs (se 1 (by rfl) ⟨7265, by rfl⟩) R14531
theorem R9695 : Reach 9695 := rs (se 1 (by rfl) ⟨7271, by rfl⟩) R14543
theorem R9701 : Reach 9701 := rs (se 4 (by rfl) ⟨909, by rfl⟩) R1819
theorem R9707 : Reach 9707 := rs (se 1 (by rfl) ⟨7280, by rfl⟩) R14561
theorem R9715 : Reach 9715 := rs (se 1 (by rfl) ⟨7286, by rfl⟩) R14573
theorem R9721 : Reach 9721 := rs (se 2 (by rfl) ⟨3645, by rfl⟩) R7291
theorem R9725 : Reach 9725 := rs (se 3 (by rfl) ⟨1823, by rfl⟩) R3647
theorem R9729 : Reach 9729 := rs (se 2 (by rfl) ⟨3648, by rfl⟩) R7297
theorem R9737 : Reach 9737 := rs (se 2 (by rfl) ⟨3651, by rfl⟩) R7303
theorem R9793 : Reach 9793 := rs (se 2 (by rfl) ⟨3672, by rfl⟩) R7345
theorem R9795 : Reach 9795 := rs (se 1 (by rfl) ⟨7346, by rfl⟩) R14693
theorem R9809 : Reach 9809 := rs (se 2 (by rfl) ⟨3678, by rfl⟩) R7357
theorem R9811 : Reach 9811 := rs (se 1 (by rfl) ⟨7358, by rfl⟩) R14717
theorem R9835 : Reach 9835 := rs (se 1 (by rfl) ⟨7376, by rfl⟩) R14753
theorem R9881 : Reach 9881 := rs (se 2 (by rfl) ⟨3705, by rfl⟩) R7411
theorem R9883 : Reach 9883 := rs (se 1 (by rfl) ⟨7412, by rfl⟩) R14825
theorem R9935 : Reach 9935 := rs (se 1 (by rfl) ⟨7451, by rfl⟩) R14903
theorem R9975 : Reach 9975 := rs (se 1 (by rfl) ⟨7481, by rfl⟩) R14963
theorem R9983 : Reach 9983 := rs (se 1 (by rfl) ⟨7487, by rfl⟩) R14975
theorem R9987 : Reach 9987 := rs (se 1 (by rfl) ⟨7490, by rfl⟩) R14981
theorem R9991 : Reach 9991 := rs (se 1 (by rfl) ⟨7493, by rfl⟩) R14987
theorem R10009 : Reach 10009 := rs (se 2 (by rfl) ⟨3753, by rfl⟩) R7507
theorem R10331 : Reach 10331 := rs (se 1 (by rfl) ⟨7748, by rfl⟩) R15497
theorem R77273 : Reach 77273 := rs (se 2 (by rfl) ⟨28977, by rfl⟩) R57955
theorem R77753 : Reach 77753 := rs (se 2 (by rfl) ⟨29157, by rfl⟩) R58315
theorem R308279 : Reach 308279 := rs (se 1 (by rfl) ⟨231209, by rfl⟩) R462419
theorem R310007 : Reach 310007 := rs (se 1 (by rfl) ⟨232505, by rfl⟩) R465011
theorem R82559 : Reach 82559 := rs (se 1 (by rfl) ⟨61919, by rfl⟩) R123839
theorem R18427 : Reach 18427 := rs (se 1 (by rfl) ⟨13820, by rfl⟩) R27641
theorem R18575 : Reach 18575 := rs (se 1 (by rfl) ⟨13931, by rfl⟩) R27863
theorem R19181 : Reach 19181 := rs (se 3 (by rfl) ⟨3596, by rfl⟩) R7193
theorem R19199 : Reach 19199 := rs (se 1 (by rfl) ⟨14399, by rfl⟩) R28799
theorem R19217 : Reach 19217 := rs (se 2 (by rfl) ⟨7206, by rfl⟩) R14413
theorem R19223 : Reach 19223 := rs (se 1 (by rfl) ⟨14417, by rfl⟩) R28835
theorem R19291 : Reach 19291 := rs (se 1 (by rfl) ⟨14468, by rfl⟩) R28937
theorem R19367 : Reach 19367 := rs (se 1 (by rfl) ⟨14525, by rfl⟩) R29051
theorem R19415 : Reach 19415 := rs (se 1 (by rfl) ⟨14561, by rfl⟩) R29123
theorem R19475 : Reach 19475 := rs (se 1 (by rfl) ⟨14606, by rfl⟩) R29213
theorem R19487 : Reach 19487 := rs (se 1 (by rfl) ⟨14615, by rfl⟩) R29231
theorem R19529 : Reach 19529 := rs (se 2 (by rfl) ⟨7323, by rfl⟩) R14647
theorem R19619 : Reach 19619 := rs (se 1 (by rfl) ⟨14714, by rfl⟩) R29429
theorem R19763 : Reach 19763 := rs (se 1 (by rfl) ⟨14822, by rfl⟩) R29645
theorem R19973 : Reach 19973 := rs (se 4 (by rfl) ⟨1872, by rfl⟩) R3745
theorem R19979 : Reach 19979 := rs (se 1 (by rfl) ⟨14984, by rfl⟩) R29969
theorem R20017 : Reach 20017 := rs (se 2 (by rfl) ⟨7506, by rfl⟩) R15013
theorem R20663 : Reach 20663 := rs (se 1 (by rfl) ⟨15497, by rfl⟩) R30995
theorem R154547 : Reach 154547 := rs (se 1 (by rfl) ⟨115910, by rfl⟩) R231821
theorem R159515 : Reach 159515 := rs (se 1 (by rfl) ⟨119636, by rfl⟩) R239273
theorem R1583 : Reach 1583 := rs (se 1 (by rfl) ⟨1187, by rfl⟩) R2375
theorem R1607 : Reach 1607 := rs (se 1 (by rfl) ⟨1205, by rfl⟩) R2411
theorem R3167 : Reach 3167 := rs (se 1 (by rfl) ⟨2375, by rfl⟩) R4751
theorem R3199 : Reach 3199 := rs (se 1 (by rfl) ⟨2399, by rfl⟩) R4799
theorem R3201 : Reach 3201 := rs (se 2 (by rfl) ⟨1200, by rfl⟩) R2401
theorem R3215 : Reach 3215 := rs (se 1 (by rfl) ⟨2411, by rfl⟩) R4823
theorem R3231 : Reach 3231 := rs (se 1 (by rfl) ⟨2423, by rfl⟩) R4847
theorem R3233 : Reach 3233 := rs (se 2 (by rfl) ⟨1212, by rfl⟩) R2425
theorem R3241 : Reach 3241 := rs (se 2 (by rfl) ⟨1215, by rfl⟩) R2431
theorem R3311 : Reach 3311 := rs (se 1 (by rfl) ⟨2483, by rfl⟩) R4967
theorem R103031 : Reach 103031 := rs (se 1 (by rfl) ⟨77273, by rfl⟩) R154547
theorem R103517 : Reach 103517 := rs (se 3 (by rfl) ⟨19409, by rfl⟩) R38819
theorem R6191 : Reach 6191 := rs (se 1 (by rfl) ⟨4643, by rfl⟩) R9287
theorem R6333 : Reach 6333 := rs (se 3 (by rfl) ⟨1187, by rfl⟩) R2375
theorem R6393 : Reach 6393 := rs (se 2 (by rfl) ⟨2397, by rfl⟩) R4795
theorem R6399 : Reach 6399 := rs (se 1 (by rfl) ⟨4799, by rfl⟩) R9599
theorem R6403 : Reach 6403 := rs (se 1 (by rfl) ⟨4802, by rfl⟩) R9605
theorem R6407 : Reach 6407 := rs (se 1 (by rfl) ⟨4805, by rfl⟩) R9611
theorem R6429 : Reach 6429 := rs (se 3 (by rfl) ⟨1205, by rfl⟩) R2411
theorem R6439 : Reach 6439 := rs (se 1 (by rfl) ⟨4829, by rfl⟩) R9659
theorem R6457 : Reach 6457 := rs (se 2 (by rfl) ⟨2421, by rfl⟩) R4843
theorem R6463 : Reach 6463 := rs (se 1 (by rfl) ⟨4847, by rfl⟩) R9695
theorem R6467 : Reach 6467 := rs (se 1 (by rfl) ⟨4850, by rfl⟩) R9701
theorem R6471 : Reach 6471 := rs (se 1 (by rfl) ⟨4853, by rfl⟩) R9707
theorem R6481 : Reach 6481 := rs (se 2 (by rfl) ⟨2430, by rfl⟩) R4861
theorem R6483 : Reach 6483 := rs (se 1 (by rfl) ⟨4862, by rfl⟩) R9725
theorem R6491 : Reach 6491 := rs (se 1 (by rfl) ⟨4868, by rfl⟩) R9737
theorem R6529 : Reach 6529 := rs (se 2 (by rfl) ⟨2448, by rfl⟩) R4897
theorem R6539 : Reach 6539 := rs (se 1 (by rfl) ⟨4904, by rfl⟩) R9809
theorem R6587 : Reach 6587 := rs (se 1 (by rfl) ⟨4940, by rfl⟩) R9881
theorem R6623 : Reach 6623 := rs (se 1 (by rfl) ⟨4967, by rfl⟩) R9935
theorem R6649 : Reach 6649 := rs (se 2 (by rfl) ⟨2493, by rfl⟩) R4987
theorem R6655 : Reach 6655 := rs (se 1 (by rfl) ⟨4991, by rfl⟩) R9983
theorem R6657 : Reach 6657 := rs (se 2 (by rfl) ⟨2496, by rfl⟩) R4993
theorem R6887 : Reach 6887 := rs (se 1 (by rfl) ⟨5165, by rfl⟩) R10331
theorem R826685 : Reach 826685 := rs (se 3 (by rfl) ⟨155003, by rfl⟩) R310007
theorem R106343 : Reach 106343 := rs (se 1 (by rfl) ⟨79757, by rfl⟩) R159515
theorem R205519 : Reach 205519 := rs (se 1 (by rfl) ⟨154139, by rfl⟩) R308279
theorem R206671 : Reach 206671 := rs (se 1 (by rfl) ⟨155003, by rfl⟩) R310007
theorem R12383 : Reach 12383 := rs (se 1 (by rfl) ⟨9287, by rfl⟩) R18575
theorem R12669 : Reach 12669 := rs (se 3 (by rfl) ⟨2375, by rfl⟩) R4751
theorem R12787 : Reach 12787 := rs (se 1 (by rfl) ⟨9590, by rfl⟩) R19181
theorem R12797 : Reach 12797 := rs (se 3 (by rfl) ⟨2399, by rfl⟩) R4799
theorem R12799 : Reach 12799 := rs (se 1 (by rfl) ⟨9599, by rfl⟩) R19199
theorem R12801 : Reach 12801 := rs (se 2 (by rfl) ⟨4800, by rfl⟩) R9601
theorem R12805 : Reach 12805 := rs (se 4 (by rfl) ⟨1200, by rfl⟩) R2401
theorem R12811 : Reach 12811 := rs (se 1 (by rfl) ⟨9608, by rfl⟩) R19217
theorem R12815 : Reach 12815 := rs (se 1 (by rfl) ⟨9611, by rfl⟩) R19223
theorem R12857 : Reach 12857 := rs (se 2 (by rfl) ⟨4821, by rfl⟩) R9643
theorem R12905 : Reach 12905 := rs (se 2 (by rfl) ⟨4839, by rfl⟩) R9679
theorem R12911 : Reach 12911 := rs (se 1 (by rfl) ⟨9683, by rfl⟩) R19367
theorem R12943 : Reach 12943 := rs (se 1 (by rfl) ⟨9707, by rfl⟩) R19415
theorem R12953 : Reach 12953 := rs (se 2 (by rfl) ⟨4857, by rfl⟩) R9715
theorem R12965 : Reach 12965 := rs (se 4 (by rfl) ⟨1215, by rfl⟩) R2431
theorem R12983 : Reach 12983 := rs (se 1 (by rfl) ⟨9737, by rfl⟩) R19475
theorem R12991 : Reach 12991 := rs (se 1 (by rfl) ⟨9743, by rfl⟩) R19487
theorem R13019 : Reach 13019 := rs (se 1 (by rfl) ⟨9764, by rfl⟩) R19529
theorem R13079 : Reach 13079 := rs (se 1 (by rfl) ⟨9809, by rfl⟩) R19619
theorem R13081 : Reach 13081 := rs (se 2 (by rfl) ⟨4905, by rfl⟩) R9811
theorem R13175 : Reach 13175 := rs (se 1 (by rfl) ⟨9881, by rfl⟩) R19763
theorem R13315 : Reach 13315 := rs (se 1 (by rfl) ⟨9986, by rfl⟩) R19973
theorem R13319 : Reach 13319 := rs (se 1 (by rfl) ⟨9989, by rfl⟩) R19979
theorem R13775 : Reach 13775 := rs (se 1 (by rfl) ⟨10331, by rfl⟩) R20663
theorem R51515 : Reach 51515 := rs (se 1 (by rfl) ⟨38636, by rfl⟩) R77273
theorem R51835 : Reach 51835 := rs (se 1 (by rfl) ⟨38876, by rfl⟩) R77753
theorem R52325 : Reach 52325 := rs (se 4 (by rfl) ⟨4905, by rfl⟩) R9811
theorem R55039 : Reach 55039 := rs (se 1 (by rfl) ⟨41279, by rfl⟩) R82559
theorem R24569 : Reach 24569 := rs (se 2 (by rfl) ⟨9213, by rfl⟩) R18427
theorem R25613 : Reach 25613 := rs (se 3 (by rfl) ⟨4802, by rfl⟩) R9605
theorem R25717 : Reach 25717 := rs (se 5 (by rfl) ⟨1205, by rfl⟩) R2411
theorem R25721 : Reach 25721 := rs (se 2 (by rfl) ⟨9645, by rfl⟩) R19291
theorem R25757 : Reach 25757 := rs (se 3 (by rfl) ⟨4829, by rfl⟩) R9659
theorem R25811 : Reach 25811 := rs (se 1 (by rfl) ⟨19358, by rfl⟩) R38717
theorem R25829 : Reach 25829 := rs (se 4 (by rfl) ⟨2421, by rfl⟩) R4843
theorem R25879 : Reach 25879 := rs (se 1 (by rfl) ⟨19409, by rfl⟩) R38819
theorem R26039 : Reach 26039 := rs (se 1 (by rfl) ⟨19529, by rfl⟩) R39059
theorem R26117 : Reach 26117 := rs (se 4 (by rfl) ⟨2448, by rfl⟩) R4897
theorem R26171 : Reach 26171 := rs (se 1 (by rfl) ⟨19628, by rfl⟩) R39257
theorem R26219 : Reach 26219 := rs (se 1 (by rfl) ⟨19664, by rfl⟩) R39329
theorem R26335 : Reach 26335 := rs (se 1 (by rfl) ⟨19751, by rfl⟩) R39503
theorem R26347 : Reach 26347 := rs (se 1 (by rfl) ⟨19760, by rfl⟩) R39521
theorem R26597 : Reach 26597 := rs (se 4 (by rfl) ⟨2493, by rfl⟩) R4987
theorem R26621 : Reach 26621 := rs (se 3 (by rfl) ⟨4991, by rfl⟩) R9983
theorem R26639 : Reach 26639 := rs (se 1 (by rfl) ⟨19979, by rfl⟩) R39959
theorem R26689 : Reach 26689 := rs (se 2 (by rfl) ⟨10008, by rfl⟩) R20017
theorem R98281 : Reach 98281 := rs (se 2 (by rfl) ⟨36855, by rfl⟩) R73711
theorem R1055 : Reach 1055 := rs (se 1 (by rfl) ⟨791, by rfl⟩) R1583
theorem R1071 : Reach 1071 := rs (se 1 (by rfl) ⟨803, by rfl⟩) R1607
theorem R34289 : Reach 34289 := rs (se 2 (by rfl) ⟨12858, by rfl⟩) R25717
theorem R34343 : Reach 34343 := rs (se 1 (by rfl) ⟨25757, by rfl⟩) R51515
theorem R34469 : Reach 34469 := rs (se 4 (by rfl) ⟨3231, by rfl⟩) R6463
theorem R34505 : Reach 34505 := rs (se 2 (by rfl) ⟨12939, by rfl⟩) R25879
theorem R2111 : Reach 2111 := rs (se 1 (by rfl) ⟨1583, by rfl⟩) R3167
theorem R34883 : Reach 34883 := rs (se 1 (by rfl) ⟨26162, by rfl⟩) R52325
theorem R2143 : Reach 2143 := rs (se 1 (by rfl) ⟨1607, by rfl⟩) R3215
theorem R2155 : Reach 2155 := rs (se 1 (by rfl) ⟨1616, by rfl⟩) R3233
theorem R2207 : Reach 2207 := rs (se 1 (by rfl) ⟨1655, by rfl⟩) R3311
theorem R35113 : Reach 35113 := rs (se 2 (by rfl) ⟨13167, by rfl⟩) R26335
theorem R35129 : Reach 35129 := rs (se 2 (by rfl) ⟨13173, by rfl⟩) R26347
theorem R35585 : Reach 35585 := rs (se 2 (by rfl) ⟨13344, by rfl⟩) R26689
theorem R68687 : Reach 68687 := rs (se 1 (by rfl) ⟨51515, by rfl⟩) R103031
theorem R69011 : Reach 69011 := rs (se 1 (by rfl) ⟨51758, by rfl⟩) R103517
theorem R69113 : Reach 69113 := rs (se 2 (by rfl) ⟨25917, by rfl⟩) R51835
theorem R69437 : Reach 69437 := rs (se 3 (by rfl) ⟨13019, by rfl⟩) R26039
theorem R4127 : Reach 4127 := rs (se 1 (by rfl) ⟨3095, by rfl⟩) R6191
theorem R4221 : Reach 4221 := rs (se 3 (by rfl) ⟨791, by rfl⟩) R1583
theorem R4265 : Reach 4265 := rs (se 2 (by rfl) ⟨1599, by rfl⟩) R3199
theorem R4271 : Reach 4271 := rs (se 1 (by rfl) ⟨3203, by rfl⟩) R6407
theorem R4285 : Reach 4285 := rs (se 3 (by rfl) ⟨803, by rfl⟩) R1607
theorem R4311 : Reach 4311 := rs (se 1 (by rfl) ⟨3233, by rfl⟩) R6467
theorem R4321 : Reach 4321 := rs (se 2 (by rfl) ⟨1620, by rfl⟩) R3241
theorem R4327 : Reach 4327 := rs (se 1 (by rfl) ⟨3245, by rfl⟩) R6491
theorem R4359 : Reach 4359 := rs (se 1 (by rfl) ⟨3269, by rfl⟩) R6539
theorem R4391 : Reach 4391 := rs (se 1 (by rfl) ⟨3293, by rfl⟩) R6587
theorem R4415 : Reach 4415 := rs (se 1 (by rfl) ⟨3311, by rfl⟩) R6623
theorem R4591 : Reach 4591 := rs (se 1 (by rfl) ⟨3443, by rfl⟩) R6887
theorem R70895 : Reach 70895 := rs (se 1 (by rfl) ⟨53171, by rfl⟩) R106343
theorem R73385 : Reach 73385 := rs (se 2 (by rfl) ⟨27519, by rfl⟩) R55039
theorem R8255 : Reach 8255 := rs (se 1 (by rfl) ⟨6191, by rfl⟩) R12383
theorem R8445 : Reach 8445 := rs (se 3 (by rfl) ⟨1583, by rfl⟩) R3167
theorem R8531 : Reach 8531 := rs (se 1 (by rfl) ⟨6398, by rfl⟩) R12797
theorem R8537 : Reach 8537 := rs (se 2 (by rfl) ⟨3201, by rfl⟩) R6403
theorem R8543 : Reach 8543 := rs (se 1 (by rfl) ⟨6407, by rfl⟩) R12815
theorem R8571 : Reach 8571 := rs (se 1 (by rfl) ⟨6428, by rfl⟩) R12857
theorem R8573 : Reach 8573 := rs (se 3 (by rfl) ⟨1607, by rfl⟩) R3215
theorem R8585 : Reach 8585 := rs (se 2 (by rfl) ⟨3219, by rfl⟩) R6439
theorem R8603 : Reach 8603 := rs (se 1 (by rfl) ⟨6452, by rfl⟩) R12905
theorem R8607 : Reach 8607 := rs (se 1 (by rfl) ⟨6455, by rfl⟩) R12911
theorem R8609 : Reach 8609 := rs (se 2 (by rfl) ⟨3228, by rfl⟩) R6457
theorem R8617 : Reach 8617 := rs (se 2 (by rfl) ⟨3231, by rfl⟩) R6463
theorem R8621 : Reach 8621 := rs (se 3 (by rfl) ⟨1616, by rfl⟩) R3233
theorem R8635 : Reach 8635 := rs (se 1 (by rfl) ⟨6476, by rfl⟩) R12953
theorem R8641 : Reach 8641 := rs (se 2 (by rfl) ⟨3240, by rfl⟩) R6481
theorem R8643 : Reach 8643 := rs (se 1 (by rfl) ⟨6482, by rfl⟩) R12965
theorem R8655 : Reach 8655 := rs (se 1 (by rfl) ⟨6491, by rfl⟩) R12983
theorem R8679 : Reach 8679 := rs (se 1 (by rfl) ⟨6509, by rfl⟩) R13019
theorem R8705 : Reach 8705 := rs (se 2 (by rfl) ⟨3264, by rfl⟩) R6529
theorem R8719 : Reach 8719 := rs (se 1 (by rfl) ⟨6539, by rfl⟩) R13079
theorem R8783 : Reach 8783 := rs (se 1 (by rfl) ⟨6587, by rfl⟩) R13175
theorem R8829 : Reach 8829 := rs (se 3 (by rfl) ⟨1655, by rfl⟩) R3311
theorem R8865 : Reach 8865 := rs (se 2 (by rfl) ⟨3324, by rfl⟩) R6649
theorem R8873 : Reach 8873 := rs (se 2 (by rfl) ⟨3327, by rfl⟩) R6655
theorem R8879 : Reach 8879 := rs (se 1 (by rfl) ⟨6659, by rfl⟩) R13319
theorem R9183 : Reach 9183 := rs (se 1 (by rfl) ⟨6887, by rfl⟩) R13775
theorem R274025 : Reach 274025 := rs (se 2 (by rfl) ⟨102759, by rfl⟩) R205519
theorem R275561 : Reach 275561 := rs (se 2 (by rfl) ⟨103335, by rfl⟩) R206671
theorem R277141 : Reach 277141 := rs (se 6 (by rfl) ⟨6495, by rfl⟩) R12991
theorem R16379 : Reach 16379 := rs (se 1 (by rfl) ⟨12284, by rfl⟩) R24569
theorem R17075 : Reach 17075 := rs (se 1 (by rfl) ⟨12806, by rfl⟩) R25613
theorem R17081 : Reach 17081 := rs (se 2 (by rfl) ⟨6405, by rfl⟩) R12811
theorem R17141 : Reach 17141 := rs (se 5 (by rfl) ⟨803, by rfl⟩) R1607
theorem R17147 : Reach 17147 := rs (se 1 (by rfl) ⟨12860, by rfl⟩) R25721
theorem R17171 : Reach 17171 := rs (se 1 (by rfl) ⟨12878, by rfl⟩) R25757
theorem R17207 : Reach 17207 := rs (se 1 (by rfl) ⟨12905, by rfl⟩) R25811
theorem R17219 : Reach 17219 := rs (se 1 (by rfl) ⟨12914, by rfl⟩) R25829
theorem R17257 : Reach 17257 := rs (se 2 (by rfl) ⟨6471, by rfl⟩) R12943
theorem R17285 : Reach 17285 := rs (se 4 (by rfl) ⟨1620, by rfl⟩) R3241
theorem R17309 : Reach 17309 := rs (se 3 (by rfl) ⟨3245, by rfl⟩) R6491
theorem R17321 : Reach 17321 := rs (se 2 (by rfl) ⟨6495, by rfl⟩) R12991
theorem R17411 : Reach 17411 := rs (se 1 (by rfl) ⟨13058, by rfl⟩) R26117
theorem R17441 : Reach 17441 := rs (se 2 (by rfl) ⟨6540, by rfl⟩) R13081
theorem R17447 : Reach 17447 := rs (se 1 (by rfl) ⟨13085, by rfl⟩) R26171
theorem R17479 : Reach 17479 := rs (se 1 (by rfl) ⟨13109, by rfl⟩) R26219
theorem R17731 : Reach 17731 := rs (se 1 (by rfl) ⟨13298, by rfl⟩) R26597
theorem R17747 : Reach 17747 := rs (se 1 (by rfl) ⟨13310, by rfl⟩) R26621
theorem R17753 : Reach 17753 := rs (se 2 (by rfl) ⟨6657, by rfl⟩) R13315
theorem R17759 : Reach 17759 := rs (se 1 (by rfl) ⟨13319, by rfl⟩) R26639
theorem R18365 : Reach 18365 := rs (se 3 (by rfl) ⟨3443, by rfl⟩) R6887
theorem R551123 : Reach 551123 := rs (se 1 (by rfl) ⟨413342, by rfl⟩) R826685
theorem R131041 : Reach 131041 := rs (se 2 (by rfl) ⟨49140, by rfl⟩) R98281
theorem R703 : Reach 703 := rs (se 1 (by rfl) ⟨527, by rfl⟩) R1055
theorem R1407 : Reach 1407 := rs (se 1 (by rfl) ⟨1055, by rfl⟩) R2111
theorem R1471 : Reach 1471 := rs (se 1 (by rfl) ⟨1103, by rfl⟩) R2207
theorem R2751 : Reach 2751 := rs (se 1 (by rfl) ⟨2063, by rfl⟩) R4127
theorem R2813 : Reach 2813 := rs (se 3 (by rfl) ⟨527, by rfl⟩) R1055
theorem R2843 : Reach 2843 := rs (se 1 (by rfl) ⟨2132, by rfl⟩) R4265
theorem R2847 : Reach 2847 := rs (se 1 (by rfl) ⟨2135, by rfl⟩) R4271
theorem R2857 : Reach 2857 := rs (se 2 (by rfl) ⟨1071, by rfl⟩) R2143
theorem R2873 : Reach 2873 := rs (se 2 (by rfl) ⟨1077, by rfl⟩) R2155
theorem R2927 : Reach 2927 := rs (se 1 (by rfl) ⟨2195, by rfl⟩) R4391
theorem R2943 : Reach 2943 := rs (se 1 (by rfl) ⟨2207, by rfl⟩) R4415
theorem R5503 : Reach 5503 := rs (se 1 (by rfl) ⟨4127, by rfl⟩) R8255
theorem R5629 : Reach 5629 := rs (se 3 (by rfl) ⟨1055, by rfl⟩) R2111
theorem R5687 : Reach 5687 := rs (se 1 (by rfl) ⟨4265, by rfl⟩) R8531
theorem R5691 : Reach 5691 := rs (se 1 (by rfl) ⟨4268, by rfl⟩) R8537
theorem R5695 : Reach 5695 := rs (se 1 (by rfl) ⟨4271, by rfl⟩) R8543
theorem R5713 : Reach 5713 := rs (se 2 (by rfl) ⟨2142, by rfl⟩) R4285
theorem R5715 : Reach 5715 := rs (se 1 (by rfl) ⟨4286, by rfl⟩) R8573
theorem R5723 : Reach 5723 := rs (se 1 (by rfl) ⟨4292, by rfl⟩) R8585
theorem R5735 : Reach 5735 := rs (se 1 (by rfl) ⟨4301, by rfl⟩) R8603
theorem R5739 : Reach 5739 := rs (se 1 (by rfl) ⟨4304, by rfl⟩) R8609
theorem R5747 : Reach 5747 := rs (se 1 (by rfl) ⟨4310, by rfl⟩) R8621
theorem R5761 : Reach 5761 := rs (se 2 (by rfl) ⟨2160, by rfl⟩) R4321
theorem R5769 : Reach 5769 := rs (se 2 (by rfl) ⟨2163, by rfl⟩) R4327
theorem R5803 : Reach 5803 := rs (se 1 (by rfl) ⟨4352, by rfl⟩) R8705
theorem R5855 : Reach 5855 := rs (se 1 (by rfl) ⟨4391, by rfl⟩) R8783
theorem R5885 : Reach 5885 := rs (se 3 (by rfl) ⟨1103, by rfl⟩) R2207
theorem R5915 : Reach 5915 := rs (se 1 (by rfl) ⟨4436, by rfl⟩) R8873
theorem R5919 : Reach 5919 := rs (se 1 (by rfl) ⟨4439, by rfl⟩) R8879
theorem R6121 : Reach 6121 := rs (se 2 (by rfl) ⟨2295, by rfl⟩) R4591
theorem R367415 : Reach 367415 := rs (se 1 (by rfl) ⟨275561, by rfl⟩) R551123
theorem R369521 : Reach 369521 := rs (se 2 (by rfl) ⟨138570, by rfl⟩) R277141
theorem R174721 : Reach 174721 := rs (se 2 (by rfl) ⟨65520, by rfl⟩) R131041
theorem R10919 : Reach 10919 := rs (se 1 (by rfl) ⟨8189, by rfl⟩) R16379
theorem R11005 : Reach 11005 := rs (se 3 (by rfl) ⟨2063, by rfl⟩) R4127
theorem R11253 : Reach 11253 := rs (se 5 (by rfl) ⟨527, by rfl⟩) R1055
theorem R11373 : Reach 11373 := rs (se 3 (by rfl) ⟨2132, by rfl⟩) R4265
theorem R11383 : Reach 11383 := rs (se 1 (by rfl) ⟨8537, by rfl⟩) R17075
theorem R11387 : Reach 11387 := rs (se 1 (by rfl) ⟨8540, by rfl⟩) R17081
theorem R11389 : Reach 11389 := rs (se 3 (by rfl) ⟨2135, by rfl⟩) R4271
theorem R11427 : Reach 11427 := rs (se 1 (by rfl) ⟨8570, by rfl⟩) R17141
theorem R11429 : Reach 11429 := rs (se 4 (by rfl) ⟨1071, by rfl⟩) R2143
theorem R11431 : Reach 11431 := rs (se 1 (by rfl) ⟨8573, by rfl⟩) R17147
theorem R11447 : Reach 11447 := rs (se 1 (by rfl) ⟨8585, by rfl⟩) R17171
theorem R11471 : Reach 11471 := rs (se 1 (by rfl) ⟨8603, by rfl⟩) R17207
theorem R11479 : Reach 11479 := rs (se 1 (by rfl) ⟨8609, by rfl⟩) R17219
theorem R11489 : Reach 11489 := rs (se 2 (by rfl) ⟨4308, by rfl⟩) R8617
theorem R11493 : Reach 11493 := rs (se 4 (by rfl) ⟨1077, by rfl⟩) R2155
theorem R11513 : Reach 11513 := rs (se 2 (by rfl) ⟨4317, by rfl⟩) R8635
theorem R11521 : Reach 11521 := rs (se 2 (by rfl) ⟨4320, by rfl⟩) R8641
theorem R11523 : Reach 11523 := rs (se 1 (by rfl) ⟨8642, by rfl⟩) R17285
theorem R11539 : Reach 11539 := rs (se 1 (by rfl) ⟨8654, by rfl⟩) R17309
theorem R11547 : Reach 11547 := rs (se 1 (by rfl) ⟨8660, by rfl⟩) R17321
theorem R11607 : Reach 11607 := rs (se 1 (by rfl) ⟨8705, by rfl⟩) R17411
theorem R11625 : Reach 11625 := rs (se 2 (by rfl) ⟨4359, by rfl⟩) R8719
theorem R11627 : Reach 11627 := rs (se 1 (by rfl) ⟨8720, by rfl⟩) R17441
theorem R11631 : Reach 11631 := rs (se 1 (by rfl) ⟨8723, by rfl⟩) R17447
theorem R11709 : Reach 11709 := rs (se 3 (by rfl) ⟨2195, by rfl⟩) R4391
theorem R11773 : Reach 11773 := rs (se 3 (by rfl) ⟨2207, by rfl⟩) R4415
theorem R11831 : Reach 11831 := rs (se 1 (by rfl) ⟨8873, by rfl⟩) R17747
theorem R11835 : Reach 11835 := rs (se 1 (by rfl) ⟨8876, by rfl⟩) R17753
theorem R11839 : Reach 11839 := rs (se 1 (by rfl) ⟨8879, by rfl⟩) R17759
theorem R12243 : Reach 12243 := rs (se 1 (by rfl) ⟨9182, by rfl⟩) R18365
theorem R45791 : Reach 45791 := rs (se 1 (by rfl) ⟨34343, by rfl⟩) R68687
theorem R46007 : Reach 46007 := rs (se 1 (by rfl) ⟨34505, by rfl⟩) R69011
theorem R46291 : Reach 46291 := rs (se 1 (by rfl) ⟨34718, by rfl⟩) R69437
theorem R46817 : Reach 46817 := rs (se 2 (by rfl) ⟨17556, by rfl⟩) R35113
theorem R47263 : Reach 47263 := rs (se 1 (by rfl) ⟨35447, by rfl⟩) R70895
theorem R48923 : Reach 48923 := rs (se 1 (by rfl) ⟨36692, by rfl⟩) R73385
theorem R182683 : Reach 182683 := rs (se 1 (by rfl) ⟨137012, by rfl⟩) R274025
theorem R183707 : Reach 183707 := rs (se 1 (by rfl) ⟨137780, by rfl⟩) R275561
theorem R184301 : Reach 184301 := rs (se 3 (by rfl) ⟨34556, by rfl⟩) R69113
theorem R22013 : Reach 22013 := rs (se 3 (by rfl) ⟨4127, by rfl⟩) R8255
theorem R22517 : Reach 22517 := rs (se 5 (by rfl) ⟨1055, by rfl⟩) R2111
theorem R22781 : Reach 22781 := rs (se 3 (by rfl) ⟨4271, by rfl⟩) R8543
theorem R22859 : Reach 22859 := rs (se 1 (by rfl) ⟨17144, by rfl⟩) R34289
theorem R22861 : Reach 22861 := rs (se 3 (by rfl) ⟨4286, by rfl⟩) R8573
theorem R22895 : Reach 22895 := rs (se 1 (by rfl) ⟨17171, by rfl⟩) R34343
theorem R22979 : Reach 22979 := rs (se 1 (by rfl) ⟨17234, by rfl⟩) R34469
theorem R23003 : Reach 23003 := rs (se 1 (by rfl) ⟨17252, by rfl⟩) R34505
theorem R23009 : Reach 23009 := rs (se 2 (by rfl) ⟨8628, by rfl⟩) R17257
theorem R23255 : Reach 23255 := rs (se 1 (by rfl) ⟨17441, by rfl⟩) R34883
theorem R23419 : Reach 23419 := rs (se 1 (by rfl) ⟨17564, by rfl⟩) R35129
theorem R23723 : Reach 23723 := rs (se 1 (by rfl) ⟨17792, by rfl⟩) R35585
theorem R93221 : Reach 93221 := rs (se 4 (by rfl) ⟨8739, by rfl⟩) R17479
theorem R94565 : Reach 94565 := rs (se 4 (by rfl) ⟨8865, by rfl⟩) R17731
theorem R937 : Reach 937 := rs (se 2 (by rfl) ⟨351, by rfl⟩) R703
theorem R1875 : Reach 1875 := rs (se 1 (by rfl) ⟨1406, by rfl⟩) R2813
theorem R1895 : Reach 1895 := rs (se 1 (by rfl) ⟨1421, by rfl⟩) R2843
theorem R1915 : Reach 1915 := rs (se 1 (by rfl) ⟨1436, by rfl⟩) R2873
theorem R1951 : Reach 1951 := rs (se 1 (by rfl) ⟨1463, by rfl⟩) R2927
theorem R1961 : Reach 1961 := rs (se 2 (by rfl) ⟨735, by rfl⟩) R1471
theorem R232961 : Reach 232961 := rs (se 2 (by rfl) ⟨87360, by rfl⟩) R174721
theorem R3749 : Reach 3749 := rs (se 4 (by rfl) ⟨351, by rfl⟩) R703
theorem R3791 : Reach 3791 := rs (se 1 (by rfl) ⟨2843, by rfl⟩) R5687
theorem R3809 : Reach 3809 := rs (se 2 (by rfl) ⟨1428, by rfl⟩) R2857
theorem R3815 : Reach 3815 := rs (se 1 (by rfl) ⟨2861, by rfl⟩) R5723
theorem R3823 : Reach 3823 := rs (se 1 (by rfl) ⟨2867, by rfl⟩) R5735
theorem R3831 : Reach 3831 := rs (se 1 (by rfl) ⟨2873, by rfl⟩) R5747
theorem R3903 : Reach 3903 := rs (se 1 (by rfl) ⟨2927, by rfl⟩) R5855
theorem R3923 : Reach 3923 := rs (se 1 (by rfl) ⟨2942, by rfl⟩) R5885
theorem R3943 : Reach 3943 := rs (se 1 (by rfl) ⟨2957, by rfl⟩) R5915
theorem R7279 : Reach 7279 := rs (se 1 (by rfl) ⟨5459, by rfl⟩) R10919
theorem R7337 : Reach 7337 := rs (se 2 (by rfl) ⟨2751, by rfl⟩) R5503
theorem R7501 : Reach 7501 := rs (se 3 (by rfl) ⟨1406, by rfl⟩) R2813
theorem R7505 : Reach 7505 := rs (se 2 (by rfl) ⟨2814, by rfl⟩) R5629
theorem R7581 : Reach 7581 := rs (se 3 (by rfl) ⟨1421, by rfl⟩) R2843
theorem R7591 : Reach 7591 := rs (se 1 (by rfl) ⟨5693, by rfl⟩) R11387
theorem R7593 : Reach 7593 := rs (se 2 (by rfl) ⟨2847, by rfl⟩) R5695
theorem R7617 : Reach 7617 := rs (se 2 (by rfl) ⟨2856, by rfl⟩) R5713
theorem R7619 : Reach 7619 := rs (se 1 (by rfl) ⟨5714, by rfl⟩) R11429
theorem R7631 : Reach 7631 := rs (se 1 (by rfl) ⟨5723, by rfl⟩) R11447
theorem R7647 : Reach 7647 := rs (se 1 (by rfl) ⟨5735, by rfl⟩) R11471
theorem R7659 : Reach 7659 := rs (se 1 (by rfl) ⟨5744, by rfl⟩) R11489
theorem R7661 : Reach 7661 := rs (se 3 (by rfl) ⟨1436, by rfl⟩) R2873
theorem R7675 : Reach 7675 := rs (se 1 (by rfl) ⟨5756, by rfl⟩) R11513
theorem R7681 : Reach 7681 := rs (se 2 (by rfl) ⟨2880, by rfl⟩) R5761
theorem R7737 : Reach 7737 := rs (se 2 (by rfl) ⟨2901, by rfl⟩) R5803
theorem R7751 : Reach 7751 := rs (se 1 (by rfl) ⟨5813, by rfl⟩) R11627
theorem R7805 : Reach 7805 := rs (se 3 (by rfl) ⟨1463, by rfl⟩) R2927
theorem R7845 : Reach 7845 := rs (se 4 (by rfl) ⟨735, by rfl⟩) R1471
theorem R7887 : Reach 7887 := rs (se 1 (by rfl) ⟨5915, by rfl⟩) R11831
theorem R8161 : Reach 8161 := rs (se 2 (by rfl) ⟨3060, by rfl⟩) R6121
theorem R243577 : Reach 243577 := rs (se 2 (by rfl) ⟨91341, by rfl⟩) R182683
theorem R14675 : Reach 14675 := rs (se 1 (by rfl) ⟨11006, by rfl⟩) R22013
theorem R15011 : Reach 15011 := rs (se 1 (by rfl) ⟨11258, by rfl⟩) R22517
theorem R15185 : Reach 15185 := rs (se 2 (by rfl) ⟨5694, by rfl⟩) R11389
theorem R15187 : Reach 15187 := rs (se 1 (by rfl) ⟨11390, by rfl⟩) R22781
theorem R15239 : Reach 15239 := rs (se 1 (by rfl) ⟨11429, by rfl⟩) R22859
theorem R15241 : Reach 15241 := rs (se 2 (by rfl) ⟨5715, by rfl⟩) R11431
theorem R15263 : Reach 15263 := rs (se 1 (by rfl) ⟨11447, by rfl⟩) R22895
theorem R15293 : Reach 15293 := rs (se 3 (by rfl) ⟨2867, by rfl⟩) R5735
theorem R15305 : Reach 15305 := rs (se 2 (by rfl) ⟨5739, by rfl⟩) R11479
theorem R15319 : Reach 15319 := rs (se 1 (by rfl) ⟨11489, by rfl⟩) R22979
theorem R15335 : Reach 15335 := rs (se 1 (by rfl) ⟨11501, by rfl⟩) R23003
theorem R15385 : Reach 15385 := rs (se 2 (by rfl) ⟨5769, by rfl⟩) R11539
theorem R15503 : Reach 15503 := rs (se 1 (by rfl) ⟨11627, by rfl⟩) R23255
theorem R244943 : Reach 244943 := rs (se 1 (by rfl) ⟨183707, by rfl⟩) R367415
theorem R15773 : Reach 15773 := rs (se 3 (by rfl) ⟨2957, by rfl⟩) R5915
theorem R15785 : Reach 15785 := rs (se 2 (by rfl) ⟨5919, by rfl⟩) R11839
theorem R15815 : Reach 15815 := rs (se 1 (by rfl) ⟨11861, by rfl⟩) R23723
theorem R246347 : Reach 246347 := rs (se 1 (by rfl) ⟨184760, by rfl⟩) R369521
theorem R252173 : Reach 252173 := rs (se 3 (by rfl) ⟨47282, by rfl⟩) R94565
theorem R121925 : Reach 121925 := rs (se 4 (by rfl) ⟨11430, by rfl⟩) R22861
theorem R122471 : Reach 122471 := rs (se 1 (by rfl) ⟨91853, by rfl⟩) R183707
theorem R122867 : Reach 122867 := rs (se 1 (by rfl) ⟨92150, by rfl⟩) R184301
theorem R60749 : Reach 60749 := rs (se 3 (by rfl) ⟨11390, by rfl⟩) R22781
theorem R61357 : Reach 61357 := rs (se 3 (by rfl) ⟨11504, by rfl⟩) R23009
theorem R61721 : Reach 61721 := rs (se 2 (by rfl) ⟨23145, by rfl⟩) R46291
theorem R62147 : Reach 62147 := rs (se 1 (by rfl) ⟨46610, by rfl⟩) R93221
theorem R63017 : Reach 63017 := rs (se 2 (by rfl) ⟨23631, by rfl⟩) R47263
theorem R30365 : Reach 30365 := rs (se 3 (by rfl) ⟨5693, by rfl⟩) R11387
theorem R30527 : Reach 30527 := rs (se 1 (by rfl) ⟨22895, by rfl⟩) R45791
theorem R30671 : Reach 30671 := rs (se 1 (by rfl) ⟨23003, by rfl⟩) R46007
theorem R30725 : Reach 30725 := rs (se 4 (by rfl) ⟨2880, by rfl⟩) R5761
theorem R31211 : Reach 31211 := rs (se 1 (by rfl) ⟨23408, by rfl⟩) R46817
theorem R31225 : Reach 31225 := rs (se 2 (by rfl) ⟨11709, by rfl⟩) R23419
theorem R31549 : Reach 31549 := rs (se 3 (by rfl) ⟨5915, by rfl⟩) R11831
theorem R32615 : Reach 32615 := rs (se 1 (by rfl) ⟨24461, by rfl⟩) R48923
theorem R164231 : Reach 164231 := rs (se 1 (by rfl) ⟨123173, by rfl⟩) R246347
theorem R1249 : Reach 1249 := rs (se 2 (by rfl) ⟨468, by rfl⟩) R937
theorem R1263 : Reach 1263 := rs (se 1 (by rfl) ⟨947, by rfl⟩) R1895
theorem R1307 : Reach 1307 := rs (se 1 (by rfl) ⟨980, by rfl⟩) R1961
theorem R165725 : Reach 165725 := rs (se 3 (by rfl) ⟨31073, by rfl⟩) R62147
theorem R2499 : Reach 2499 := rs (se 1 (by rfl) ⟨1874, by rfl⟩) R3749
theorem R2527 : Reach 2527 := rs (se 1 (by rfl) ⟨1895, by rfl⟩) R3791
theorem R2539 : Reach 2539 := rs (se 1 (by rfl) ⟨1904, by rfl⟩) R3809
theorem R2543 : Reach 2543 := rs (se 1 (by rfl) ⟨1907, by rfl⟩) R3815
theorem R2553 : Reach 2553 := rs (se 2 (by rfl) ⟨957, by rfl⟩) R1915
theorem R2601 : Reach 2601 := rs (se 2 (by rfl) ⟨975, by rfl⟩) R1951
theorem R2615 : Reach 2615 := rs (se 1 (by rfl) ⟨1961, by rfl⟩) R3923
theorem R168115 : Reach 168115 := rs (se 1 (by rfl) ⟨126086, by rfl⟩) R252173
theorem R4891 : Reach 4891 := rs (se 1 (by rfl) ⟨3668, by rfl⟩) R7337
theorem R4997 : Reach 4997 := rs (se 4 (by rfl) ⟨468, by rfl⟩) R937
theorem R5003 : Reach 5003 := rs (se 1 (by rfl) ⟨3752, by rfl⟩) R7505
theorem R5053 : Reach 5053 := rs (se 3 (by rfl) ⟨947, by rfl⟩) R1895
theorem R5079 : Reach 5079 := rs (se 1 (by rfl) ⟨3809, by rfl⟩) R7619
theorem R5087 : Reach 5087 := rs (se 1 (by rfl) ⟨3815, by rfl⟩) R7631
theorem R5097 : Reach 5097 := rs (se 2 (by rfl) ⟨1911, by rfl⟩) R3823
theorem R5107 : Reach 5107 := rs (se 1 (by rfl) ⟨3830, by rfl⟩) R7661
theorem R5167 : Reach 5167 := rs (se 1 (by rfl) ⟨3875, by rfl⟩) R7751
theorem R5203 : Reach 5203 := rs (se 1 (by rfl) ⟨3902, by rfl⟩) R7805
theorem R5229 : Reach 5229 := rs (se 3 (by rfl) ⟨980, by rfl⟩) R1961
theorem R5257 : Reach 5257 := rs (se 2 (by rfl) ⟨1971, by rfl⟩) R3943
theorem R40499 : Reach 40499 := rs (se 1 (by rfl) ⟨30374, by rfl⟩) R60749
theorem R41147 : Reach 41147 := rs (se 1 (by rfl) ⟨30860, by rfl⟩) R61721
theorem R41431 : Reach 41431 := rs (se 1 (by rfl) ⟨31073, by rfl⟩) R62147
theorem R41633 : Reach 41633 := rs (se 2 (by rfl) ⟨15612, by rfl⟩) R31225
theorem R42011 : Reach 42011 := rs (se 1 (by rfl) ⟨31508, by rfl⟩) R63017
theorem R42065 : Reach 42065 := rs (se 2 (by rfl) ⟨15774, by rfl⟩) R31549
theorem R42173 : Reach 42173 := rs (se 3 (by rfl) ⟨7907, by rfl⟩) R15815
theorem R9705 : Reach 9705 := rs (se 2 (by rfl) ⟨3639, by rfl⟩) R7279
theorem R9783 : Reach 9783 := rs (se 1 (by rfl) ⟨7337, by rfl⟩) R14675
theorem R9997 : Reach 9997 := rs (se 3 (by rfl) ⟨1874, by rfl⟩) R3749
theorem R10001 : Reach 10001 := rs (se 2 (by rfl) ⟨3750, by rfl⟩) R7501
theorem R10007 : Reach 10007 := rs (se 1 (by rfl) ⟨7505, by rfl⟩) R15011
theorem R10109 : Reach 10109 := rs (se 3 (by rfl) ⟨1895, by rfl⟩) R3791
theorem R10121 : Reach 10121 := rs (se 2 (by rfl) ⟨3795, by rfl⟩) R7591
theorem R10123 : Reach 10123 := rs (se 1 (by rfl) ⟨7592, by rfl⟩) R15185
theorem R10157 : Reach 10157 := rs (se 3 (by rfl) ⟨1904, by rfl⟩) R3809
theorem R10159 : Reach 10159 := rs (se 1 (by rfl) ⟨7619, by rfl⟩) R15239
theorem R10173 : Reach 10173 := rs (se 3 (by rfl) ⟨1907, by rfl⟩) R3815
theorem R10175 : Reach 10175 := rs (se 1 (by rfl) ⟨7631, by rfl⟩) R15263
theorem R10195 : Reach 10195 := rs (se 1 (by rfl) ⟨7646, by rfl⟩) R15293
theorem R10203 : Reach 10203 := rs (se 1 (by rfl) ⟨7652, by rfl⟩) R15305
theorem R10213 : Reach 10213 := rs (se 4 (by rfl) ⟨957, by rfl⟩) R1915
theorem R10223 : Reach 10223 := rs (se 1 (by rfl) ⟨7667, by rfl⟩) R15335
theorem R10233 : Reach 10233 := rs (se 2 (by rfl) ⟨3837, by rfl⟩) R7675
theorem R10241 : Reach 10241 := rs (se 2 (by rfl) ⟨3840, by rfl⟩) R7681
theorem R10335 : Reach 10335 := rs (se 1 (by rfl) ⟨7751, by rfl⟩) R15503
theorem R10405 : Reach 10405 := rs (se 4 (by rfl) ⟨975, by rfl⟩) R1951
theorem R10461 : Reach 10461 := rs (se 3 (by rfl) ⟨1961, by rfl⟩) R3923
theorem R10515 : Reach 10515 := rs (se 1 (by rfl) ⟨7886, by rfl⟩) R15773
theorem R10523 : Reach 10523 := rs (se 1 (by rfl) ⟨7892, by rfl⟩) R15785
theorem R10543 : Reach 10543 := rs (se 1 (by rfl) ⟨7907, by rfl⟩) R15815
theorem R10881 : Reach 10881 := rs (se 2 (by rfl) ⟨4080, by rfl⟩) R8161
theorem R81647 : Reach 81647 := rs (se 1 (by rfl) ⟨61235, by rfl⟩) R122471
theorem R81809 : Reach 81809 := rs (se 2 (by rfl) ⟨30678, by rfl⟩) R61357
theorem R81911 : Reach 81911 := rs (se 1 (by rfl) ⟨61433, by rfl⟩) R122867
theorem R19565 : Reach 19565 := rs (se 3 (by rfl) ⟨3668, by rfl⟩) R7337
theorem R20213 : Reach 20213 := rs (se 5 (by rfl) ⟨947, by rfl⟩) R1895
theorem R20243 : Reach 20243 := rs (se 1 (by rfl) ⟨15182, by rfl⟩) R30365
theorem R20249 : Reach 20249 := rs (se 2 (by rfl) ⟨7593, by rfl⟩) R15187
theorem R20317 : Reach 20317 := rs (se 3 (by rfl) ⟨3809, by rfl⟩) R7619
theorem R20321 : Reach 20321 := rs (se 2 (by rfl) ⟨7620, by rfl⟩) R15241
theorem R20351 : Reach 20351 := rs (se 1 (by rfl) ⟨15263, by rfl⟩) R30527
theorem R20425 : Reach 20425 := rs (se 2 (by rfl) ⟨7659, by rfl⟩) R15319
theorem R20429 : Reach 20429 := rs (se 3 (by rfl) ⟨3830, by rfl⟩) R7661
theorem R20447 : Reach 20447 := rs (se 1 (by rfl) ⟨15335, by rfl⟩) R30671
theorem R20483 : Reach 20483 := rs (se 1 (by rfl) ⟨15362, by rfl⟩) R30725
theorem R20513 : Reach 20513 := rs (se 2 (by rfl) ⟨7692, by rfl⟩) R15385
theorem R20807 : Reach 20807 := rs (se 1 (by rfl) ⟨15605, by rfl⟩) R31211
theorem R21743 : Reach 21743 := rs (se 1 (by rfl) ⟨16307, by rfl⟩) R32615
theorem R324769 : Reach 324769 := rs (se 2 (by rfl) ⟨121788, by rfl⟩) R243577
theorem R325133 : Reach 325133 := rs (se 3 (by rfl) ⟨60962, by rfl⟩) R121925
theorem R621229 : Reach 621229 := rs (se 3 (by rfl) ⟨116480, by rfl⟩) R232961
theorem R163295 : Reach 163295 := rs (se 1 (by rfl) ⟨122471, by rfl⟩) R244943
theorem R871 : Reach 871 := rs (se 1 (by rfl) ⟨653, by rfl⟩) R1307
theorem R1665 : Reach 1665 := rs (se 2 (by rfl) ⟨624, by rfl⟩) R1249
theorem R1695 : Reach 1695 := rs (se 1 (by rfl) ⟨1271, by rfl⟩) R2543
theorem R1743 : Reach 1743 := rs (se 1 (by rfl) ⟨1307, by rfl⟩) R2615
theorem R3331 : Reach 3331 := rs (se 1 (by rfl) ⟨2498, by rfl⟩) R4997
theorem R3335 : Reach 3335 := rs (se 1 (by rfl) ⟨2501, by rfl⟩) R5003
theorem R3369 : Reach 3369 := rs (se 2 (by rfl) ⟨1263, by rfl⟩) R2527
theorem R3385 : Reach 3385 := rs (se 2 (by rfl) ⟨1269, by rfl⟩) R2539
theorem R3391 : Reach 3391 := rs (se 1 (by rfl) ⟨2543, by rfl⟩) R5087
theorem R3485 : Reach 3485 := rs (se 3 (by rfl) ⟨653, by rfl⟩) R1307
theorem R6521 : Reach 6521 := rs (se 2 (by rfl) ⟨2445, by rfl⟩) R4891
theorem R6661 : Reach 6661 := rs (se 4 (by rfl) ⟨624, by rfl⟩) R1249
theorem R6667 : Reach 6667 := rs (se 1 (by rfl) ⟨5000, by rfl⟩) R10001
theorem R6671 : Reach 6671 := rs (se 1 (by rfl) ⟨5003, by rfl⟩) R10007
theorem R6737 : Reach 6737 := rs (se 2 (by rfl) ⟨2526, by rfl⟩) R5053
theorem R6739 : Reach 6739 := rs (se 1 (by rfl) ⟨5054, by rfl⟩) R10109
theorem R6747 : Reach 6747 := rs (se 1 (by rfl) ⟨5060, by rfl⟩) R10121
theorem R6771 : Reach 6771 := rs (se 1 (by rfl) ⟨5078, by rfl⟩) R10157
theorem R6781 : Reach 6781 := rs (se 3 (by rfl) ⟨1271, by rfl⟩) R2543
theorem R6783 : Reach 6783 := rs (se 1 (by rfl) ⟨5087, by rfl⟩) R10175
theorem R6809 : Reach 6809 := rs (se 2 (by rfl) ⟨2553, by rfl⟩) R5107
theorem R6815 : Reach 6815 := rs (se 1 (by rfl) ⟨5111, by rfl⟩) R10223
theorem R6827 : Reach 6827 := rs (se 1 (by rfl) ⟨5120, by rfl⟩) R10241
theorem R6889 : Reach 6889 := rs (se 2 (by rfl) ⟨2583, by rfl⟩) R5167
theorem R6937 : Reach 6937 := rs (se 2 (by rfl) ⟨2601, by rfl⟩) R5203
theorem R6973 : Reach 6973 := rs (se 3 (by rfl) ⟨1307, by rfl⟩) R2615
theorem R7009 : Reach 7009 := rs (se 2 (by rfl) ⟨2628, by rfl⟩) R5257
theorem R7015 : Reach 7015 := rs (se 1 (by rfl) ⟨5261, by rfl⟩) R10523
theorem R433025 : Reach 433025 := rs (se 2 (by rfl) ⟨162384, by rfl⟩) R324769
theorem R828305 : Reach 828305 := rs (se 2 (by rfl) ⟨310614, by rfl⟩) R621229
theorem R108863 : Reach 108863 := rs (se 1 (by rfl) ⟨81647, by rfl⟩) R163295
theorem R109487 : Reach 109487 := rs (se 1 (by rfl) ⟨82115, by rfl⟩) R164231
theorem R110483 : Reach 110483 := rs (se 1 (by rfl) ⟨82862, by rfl⟩) R165725
theorem R13043 : Reach 13043 := rs (se 1 (by rfl) ⟨9782, by rfl⟩) R19565
theorem R13325 : Reach 13325 := rs (se 3 (by rfl) ⟨2498, by rfl⟩) R4997
theorem R13475 : Reach 13475 := rs (se 1 (by rfl) ⟨10106, by rfl⟩) R20213
theorem R13477 : Reach 13477 := rs (se 4 (by rfl) ⟨1263, by rfl⟩) R2527
theorem R13495 : Reach 13495 := rs (se 1 (by rfl) ⟨10121, by rfl⟩) R20243
theorem R13499 : Reach 13499 := rs (se 1 (by rfl) ⟨10124, by rfl⟩) R20249
theorem R13541 : Reach 13541 := rs (se 4 (by rfl) ⟨1269, by rfl⟩) R2539
theorem R13547 : Reach 13547 := rs (se 1 (by rfl) ⟨10160, by rfl⟩) R20321
theorem R13565 : Reach 13565 := rs (se 3 (by rfl) ⟨2543, by rfl⟩) R5087
theorem R13567 : Reach 13567 := rs (se 1 (by rfl) ⟨10175, by rfl⟩) R20351
theorem R13619 : Reach 13619 := rs (se 1 (by rfl) ⟨10214, by rfl⟩) R20429
theorem R13631 : Reach 13631 := rs (se 1 (by rfl) ⟨10223, by rfl⟩) R20447
theorem R13655 : Reach 13655 := rs (se 1 (by rfl) ⟨10241, by rfl⟩) R20483
theorem R13675 : Reach 13675 := rs (se 1 (by rfl) ⟨10256, by rfl⟩) R20513
theorem R13871 : Reach 13871 := rs (se 1 (by rfl) ⟨10403, by rfl⟩) R20807
theorem R13873 : Reach 13873 := rs (se 2 (by rfl) ⟨5202, by rfl⟩) R10405
theorem R14057 : Reach 14057 := rs (se 2 (by rfl) ⟨5271, by rfl⟩) R10543
theorem R14495 : Reach 14495 := rs (se 1 (by rfl) ⟨10871, by rfl⟩) R21743
theorem R216755 : Reach 216755 := rs (se 1 (by rfl) ⟨162566, by rfl⟩) R325133
theorem R54269 : Reach 54269 := rs (se 3 (by rfl) ⟨10175, by rfl⟩) R20351
theorem R54431 : Reach 54431 := rs (se 1 (by rfl) ⟨40823, by rfl⟩) R81647
theorem R54539 : Reach 54539 := rs (se 1 (by rfl) ⟨40904, by rfl⟩) R81809
theorem R54607 : Reach 54607 := rs (se 1 (by rfl) ⟨40955, by rfl⟩) R81911
theorem R55241 : Reach 55241 := rs (se 2 (by rfl) ⟨20715, by rfl⟩) R41431
theorem R26669 : Reach 26669 := rs (se 3 (by rfl) ⟨5000, by rfl⟩) R10001
theorem R26999 : Reach 26999 := rs (se 1 (by rfl) ⟨20249, by rfl⟩) R40499
theorem R27089 : Reach 27089 := rs (se 2 (by rfl) ⟨10158, by rfl⟩) R20317
theorem R27125 : Reach 27125 := rs (se 5 (by rfl) ⟨1271, by rfl⟩) R2543
theorem R27233 : Reach 27233 := rs (se 2 (by rfl) ⟨10212, by rfl⟩) R20425
theorem R27431 : Reach 27431 := rs (se 1 (by rfl) ⟨20573, by rfl⟩) R41147
theorem R224153 : Reach 224153 := rs (se 2 (by rfl) ⟨84057, by rfl⟩) R168115
theorem R27557 : Reach 27557 := rs (se 4 (by rfl) ⟨2583, by rfl⟩) R5167
theorem R27755 : Reach 27755 := rs (se 1 (by rfl) ⟨20816, by rfl⟩) R41633
theorem R28007 : Reach 28007 := rs (se 1 (by rfl) ⟨21005, by rfl⟩) R42011
theorem R28043 : Reach 28043 := rs (se 1 (by rfl) ⟨21032, by rfl⟩) R42065
theorem R28061 : Reach 28061 := rs (se 3 (by rfl) ⟨5261, by rfl⟩) R10523
theorem R28115 : Reach 28115 := rs (se 1 (by rfl) ⟨21086, by rfl⟩) R42173
theorem R1161 : Reach 1161 := rs (se 2 (by rfl) ⟨435, by rfl⟩) R871
theorem R2223 : Reach 2223 := rs (se 1 (by rfl) ⟨1667, by rfl⟩) R3335
theorem R2323 : Reach 2323 := rs (se 1 (by rfl) ⟨1742, by rfl⟩) R3485
theorem R36125 : Reach 36125 := rs (se 3 (by rfl) ⟨6773, by rfl⟩) R13547
theorem R36179 : Reach 36179 := rs (se 1 (by rfl) ⟨27134, by rfl⟩) R54269
theorem R36287 : Reach 36287 := rs (se 1 (by rfl) ⟨27215, by rfl⟩) R54431
theorem R36359 : Reach 36359 := rs (se 1 (by rfl) ⟨27269, by rfl⟩) R54539
theorem R36827 : Reach 36827 := rs (se 1 (by rfl) ⟨27620, by rfl⟩) R55241
theorem R36989 : Reach 36989 := rs (se 3 (by rfl) ⟨6935, by rfl⟩) R13871
theorem R4347 : Reach 4347 := rs (se 1 (by rfl) ⟨3260, by rfl⟩) R6521
theorem R4441 : Reach 4441 := rs (se 2 (by rfl) ⟨1665, by rfl⟩) R3331
theorem R4447 : Reach 4447 := rs (se 1 (by rfl) ⟨3335, by rfl⟩) R6671
theorem R4491 : Reach 4491 := rs (se 1 (by rfl) ⟨3368, by rfl⟩) R6737
theorem R4513 : Reach 4513 := rs (se 2 (by rfl) ⟨1692, by rfl⟩) R3385
theorem R4521 : Reach 4521 := rs (se 2 (by rfl) ⟨1695, by rfl⟩) R3391
theorem R4539 : Reach 4539 := rs (se 1 (by rfl) ⟨3404, by rfl⟩) R6809
theorem R4543 : Reach 4543 := rs (se 1 (by rfl) ⟨3407, by rfl⟩) R6815
theorem R4551 : Reach 4551 := rs (se 1 (by rfl) ⟨3413, by rfl⟩) R6827
theorem R4645 : Reach 4645 := rs (se 4 (by rfl) ⟨435, by rfl⟩) R871
theorem R72575 : Reach 72575 := rs (se 1 (by rfl) ⟨54431, by rfl⟩) R108863
theorem R72809 : Reach 72809 := rs (se 2 (by rfl) ⟨27303, by rfl⟩) R54607
theorem R72991 : Reach 72991 := rs (se 1 (by rfl) ⟨54743, by rfl⟩) R109487
theorem R73655 : Reach 73655 := rs (se 1 (by rfl) ⟨55241, by rfl⟩) R110483
theorem R8695 : Reach 8695 := rs (se 1 (by rfl) ⟨6521, by rfl⟩) R13043
theorem R8881 : Reach 8881 := rs (se 2 (by rfl) ⟨3330, by rfl⟩) R6661
theorem R8883 : Reach 8883 := rs (se 1 (by rfl) ⟨6662, by rfl⟩) R13325
theorem R8889 : Reach 8889 := rs (se 2 (by rfl) ⟨3333, by rfl⟩) R6667
theorem R8893 : Reach 8893 := rs (se 3 (by rfl) ⟨1667, by rfl⟩) R3335
theorem R8983 : Reach 8983 := rs (se 1 (by rfl) ⟨6737, by rfl⟩) R13475
theorem R8985 : Reach 8985 := rs (se 2 (by rfl) ⟨3369, by rfl⟩) R6739
theorem R8999 : Reach 8999 := rs (se 1 (by rfl) ⟨6749, by rfl⟩) R13499
theorem R9027 : Reach 9027 := rs (se 1 (by rfl) ⟨6770, by rfl⟩) R13541
theorem R9031 : Reach 9031 := rs (se 1 (by rfl) ⟨6773, by rfl⟩) R13547
theorem R9041 : Reach 9041 := rs (se 2 (by rfl) ⟨3390, by rfl⟩) R6781
theorem R9043 : Reach 9043 := rs (se 1 (by rfl) ⟨6782, by rfl⟩) R13565
theorem R9079 : Reach 9079 := rs (se 1 (by rfl) ⟨6809, by rfl⟩) R13619
theorem R9087 : Reach 9087 := rs (se 1 (by rfl) ⟨6815, by rfl⟩) R13631
theorem R9103 : Reach 9103 := rs (se 1 (by rfl) ⟨6827, by rfl⟩) R13655
theorem R9185 : Reach 9185 := rs (se 2 (by rfl) ⟨3444, by rfl⟩) R6889
theorem R9247 : Reach 9247 := rs (se 1 (by rfl) ⟨6935, by rfl⟩) R13871
theorem R9249 : Reach 9249 := rs (se 2 (by rfl) ⟨3468, by rfl⟩) R6937
theorem R9293 : Reach 9293 := rs (se 3 (by rfl) ⟨1742, by rfl⟩) R3485
theorem R9297 : Reach 9297 := rs (se 2 (by rfl) ⟨3486, by rfl⟩) R6973
theorem R9345 : Reach 9345 := rs (se 2 (by rfl) ⟨3504, by rfl⟩) R7009
theorem R9353 : Reach 9353 := rs (se 2 (by rfl) ⟨3507, by rfl⟩) R7015
theorem R9371 : Reach 9371 := rs (se 1 (by rfl) ⟨7028, by rfl⟩) R14057
theorem R9663 : Reach 9663 := rs (se 1 (by rfl) ⟨7247, by rfl⟩) R14495
theorem R144503 : Reach 144503 := rs (se 1 (by rfl) ⟨108377, by rfl⟩) R216755
theorem R17765 : Reach 17765 := rs (se 4 (by rfl) ⟨1665, by rfl⟩) R3331
theorem R17779 : Reach 17779 := rs (se 1 (by rfl) ⟨13334, by rfl⟩) R26669
theorem R17789 : Reach 17789 := rs (se 3 (by rfl) ⟨3335, by rfl⟩) R6671
theorem R17969 : Reach 17969 := rs (se 2 (by rfl) ⟨6738, by rfl⟩) R13477
theorem R17993 : Reach 17993 := rs (se 2 (by rfl) ⟨6747, by rfl⟩) R13495
theorem R17999 : Reach 17999 := rs (se 1 (by rfl) ⟨13499, by rfl⟩) R26999
theorem R18053 : Reach 18053 := rs (se 4 (by rfl) ⟨1692, by rfl⟩) R3385
theorem R18059 : Reach 18059 := rs (se 1 (by rfl) ⟨13544, by rfl⟩) R27089
theorem R18083 : Reach 18083 := rs (se 1 (by rfl) ⟨13562, by rfl⟩) R27125
theorem R18089 : Reach 18089 := rs (se 2 (by rfl) ⟨6783, by rfl⟩) R13567
theorem R18155 : Reach 18155 := rs (se 1 (by rfl) ⟨13616, by rfl⟩) R27233
theorem R18157 : Reach 18157 := rs (se 3 (by rfl) ⟨3404, by rfl⟩) R6809
theorem R18173 : Reach 18173 := rs (se 3 (by rfl) ⟨3407, by rfl⟩) R6815
theorem R18233 : Reach 18233 := rs (se 2 (by rfl) ⟨6837, by rfl⟩) R13675
theorem R18287 : Reach 18287 := rs (se 1 (by rfl) ⟨13715, by rfl⟩) R27431
theorem R149435 : Reach 149435 := rs (se 1 (by rfl) ⟨112076, by rfl⟩) R224153
theorem R18371 : Reach 18371 := rs (se 1 (by rfl) ⟨13778, by rfl⟩) R27557
theorem R18497 : Reach 18497 := rs (se 2 (by rfl) ⟨6936, by rfl⟩) R13873
theorem R18503 : Reach 18503 := rs (se 1 (by rfl) ⟨13877, by rfl⟩) R27755
theorem R18581 : Reach 18581 := rs (se 6 (by rfl) ⟨435, by rfl⟩) R871
theorem R18671 : Reach 18671 := rs (se 1 (by rfl) ⟨14003, by rfl⟩) R28007
theorem R18695 : Reach 18695 := rs (se 1 (by rfl) ⟨14021, by rfl⟩) R28043
theorem R18707 : Reach 18707 := rs (se 1 (by rfl) ⟨14030, by rfl⟩) R28061
theorem R18743 : Reach 18743 := rs (se 1 (by rfl) ⟨14057, by rfl⟩) R28115
theorem R288683 : Reach 288683 := rs (se 1 (by rfl) ⟨216512, by rfl⟩) R433025
theorem R552203 : Reach 552203 := rs (se 1 (by rfl) ⟨414152, by rfl⟩) R828305
theorem R99623 : Reach 99623 := rs (se 1 (by rfl) ⟨74717, by rfl⟩) R149435
theorem R3097 : Reach 3097 := rs (se 2 (by rfl) ⟨1161, by rfl⟩) R2323
theorem R5921 : Reach 5921 := rs (se 2 (by rfl) ⟨2220, by rfl⟩) R4441
theorem R5929 : Reach 5929 := rs (se 2 (by rfl) ⟨2223, by rfl⟩) R4447
theorem R5999 : Reach 5999 := rs (se 1 (by rfl) ⟨4499, by rfl⟩) R8999
theorem R6017 : Reach 6017 := rs (se 2 (by rfl) ⟨2256, by rfl⟩) R4513
theorem R6027 : Reach 6027 := rs (se 1 (by rfl) ⟨4520, by rfl⟩) R9041
theorem R6057 : Reach 6057 := rs (se 2 (by rfl) ⟨2271, by rfl⟩) R4543
theorem R6123 : Reach 6123 := rs (se 1 (by rfl) ⟨4592, by rfl⟩) R9185
theorem R6193 : Reach 6193 := rs (se 2 (by rfl) ⟨2322, by rfl⟩) R4645
theorem R6195 : Reach 6195 := rs (se 1 (by rfl) ⟨4646, by rfl⟩) R9293
theorem R6235 : Reach 6235 := rs (se 1 (by rfl) ⟨4676, by rfl⟩) R9353
theorem R6247 : Reach 6247 := rs (se 1 (by rfl) ⟨4685, by rfl⟩) R9371
theorem R368135 : Reach 368135 := rs (se 1 (by rfl) ⟨276101, by rfl⟩) R552203
theorem R11593 : Reach 11593 := rs (se 2 (by rfl) ⟨4347, by rfl⟩) R8695
theorem R11841 : Reach 11841 := rs (se 2 (by rfl) ⟨4440, by rfl⟩) R8881
theorem R11843 : Reach 11843 := rs (se 1 (by rfl) ⟨8882, by rfl⟩) R17765
theorem R11857 : Reach 11857 := rs (se 2 (by rfl) ⟨4446, by rfl⟩) R8893
theorem R11859 : Reach 11859 := rs (se 1 (by rfl) ⟨8894, by rfl⟩) R17789
theorem R11977 : Reach 11977 := rs (se 2 (by rfl) ⟨4491, by rfl⟩) R8983
theorem R11979 : Reach 11979 := rs (se 1 (by rfl) ⟨8984, by rfl⟩) R17969
theorem R11995 : Reach 11995 := rs (se 1 (by rfl) ⟨8996, by rfl⟩) R17993
theorem R11999 : Reach 11999 := rs (se 1 (by rfl) ⟨8999, by rfl⟩) R17999
theorem R12035 : Reach 12035 := rs (se 1 (by rfl) ⟨9026, by rfl⟩) R18053
theorem R12039 : Reach 12039 := rs (se 1 (by rfl) ⟨9029, by rfl⟩) R18059
theorem R12041 : Reach 12041 := rs (se 2 (by rfl) ⟨4515, by rfl⟩) R9031
theorem R12055 : Reach 12055 := rs (se 1 (by rfl) ⟨9041, by rfl⟩) R18083
theorem R12057 : Reach 12057 := rs (se 2 (by rfl) ⟨4521, by rfl⟩) R9043
theorem R12059 : Reach 12059 := rs (se 1 (by rfl) ⟨9044, by rfl⟩) R18089
theorem R12103 : Reach 12103 := rs (se 1 (by rfl) ⟨9077, by rfl⟩) R18155
theorem R12105 : Reach 12105 := rs (se 2 (by rfl) ⟨4539, by rfl⟩) R9079
theorem R12115 : Reach 12115 := rs (se 1 (by rfl) ⟨9086, by rfl⟩) R18173
theorem R12137 : Reach 12137 := rs (se 2 (by rfl) ⟨4551, by rfl⟩) R9103
theorem R12155 : Reach 12155 := rs (se 1 (by rfl) ⟨9116, by rfl⟩) R18233
theorem R12191 : Reach 12191 := rs (se 1 (by rfl) ⟨9143, by rfl⟩) R18287
theorem R12247 : Reach 12247 := rs (se 1 (by rfl) ⟨9185, by rfl⟩) R18371
theorem R12329 : Reach 12329 := rs (se 2 (by rfl) ⟨4623, by rfl⟩) R9247
theorem R12331 : Reach 12331 := rs (se 1 (by rfl) ⟨9248, by rfl⟩) R18497
theorem R12335 : Reach 12335 := rs (se 1 (by rfl) ⟨9251, by rfl⟩) R18503
theorem R12387 : Reach 12387 := rs (se 1 (by rfl) ⟨9290, by rfl⟩) R18581
theorem R12389 : Reach 12389 := rs (se 4 (by rfl) ⟨1161, by rfl⟩) R2323
theorem R12447 : Reach 12447 := rs (se 1 (by rfl) ⟨9335, by rfl⟩) R18671
theorem R12463 : Reach 12463 := rs (se 1 (by rfl) ⟨9347, by rfl⟩) R18695
theorem R12471 : Reach 12471 := rs (se 1 (by rfl) ⟨9353, by rfl⟩) R18707
theorem R12495 : Reach 12495 := rs (se 1 (by rfl) ⟨9371, by rfl⟩) R18743
theorem R48221 : Reach 48221 := rs (se 3 (by rfl) ⟨9041, by rfl⟩) R18083
theorem R48383 : Reach 48383 := rs (se 1 (by rfl) ⟨36287, by rfl⟩) R72575
theorem R48539 : Reach 48539 := rs (se 1 (by rfl) ⟨36404, by rfl⟩) R72809
theorem R49103 : Reach 49103 := rs (se 1 (by rfl) ⟨36827, by rfl⟩) R73655
theorem R23705 : Reach 23705 := rs (se 2 (by rfl) ⟨8889, by rfl⟩) R17779
theorem R24083 : Reach 24083 := rs (se 1 (by rfl) ⟨18062, by rfl⟩) R36125
theorem R24119 : Reach 24119 := rs (se 1 (by rfl) ⟨18089, by rfl⟩) R36179
theorem R24191 : Reach 24191 := rs (se 1 (by rfl) ⟨18143, by rfl⟩) R36287
theorem R24209 : Reach 24209 := rs (se 2 (by rfl) ⟨9078, by rfl⟩) R18157
theorem R24239 : Reach 24239 := rs (se 1 (by rfl) ⟨18179, by rfl⟩) R36359
theorem R24551 : Reach 24551 := rs (se 1 (by rfl) ⟨18413, by rfl⟩) R36827
theorem R24659 : Reach 24659 := rs (se 1 (by rfl) ⟨18494, by rfl⟩) R36989
theorem R192455 : Reach 192455 := rs (se 1 (by rfl) ⟨144341, by rfl⟩) R288683
theorem R96335 : Reach 96335 := rs (se 1 (by rfl) ⟨72251, by rfl⟩) R144503
theorem R97321 : Reach 97321 := rs (se 2 (by rfl) ⟨36495, by rfl⟩) R72991
theorem R33253 : Reach 33253 := rs (se 4 (by rfl) ⟨3117, by rfl⟩) R6235
theorem R33317 : Reach 33317 := rs (se 4 (by rfl) ⟨3123, by rfl⟩) R6247
theorem R66415 : Reach 66415 := rs (se 1 (by rfl) ⟨49811, by rfl⟩) R99623
theorem R3947 : Reach 3947 := rs (se 1 (by rfl) ⟨2960, by rfl⟩) R5921
theorem R3999 : Reach 3999 := rs (se 1 (by rfl) ⟨2999, by rfl⟩) R5999
theorem R4011 : Reach 4011 := rs (se 1 (by rfl) ⟨3008, by rfl⟩) R6017
theorem R4129 : Reach 4129 := rs (se 2 (by rfl) ⟨1548, by rfl⟩) R3097
theorem R7895 : Reach 7895 := rs (se 1 (by rfl) ⟨5921, by rfl⟩) R11843
theorem R7905 : Reach 7905 := rs (se 2 (by rfl) ⟨2964, by rfl⟩) R5929
theorem R7999 : Reach 7999 := rs (se 1 (by rfl) ⟨5999, by rfl⟩) R11999
theorem R8023 : Reach 8023 := rs (se 1 (by rfl) ⟨6017, by rfl⟩) R12035
theorem R8027 : Reach 8027 := rs (se 1 (by rfl) ⟨6020, by rfl⟩) R12041
theorem R8039 : Reach 8039 := rs (se 1 (by rfl) ⟨6029, by rfl⟩) R12059
theorem R8091 : Reach 8091 := rs (se 1 (by rfl) ⟨6068, by rfl⟩) R12137
theorem R8103 : Reach 8103 := rs (se 1 (by rfl) ⟨6077, by rfl⟩) R12155
theorem R8127 : Reach 8127 := rs (se 1 (by rfl) ⟨6095, by rfl⟩) R12191
theorem R8219 : Reach 8219 := rs (se 1 (by rfl) ⟨6164, by rfl⟩) R12329
theorem R8223 : Reach 8223 := rs (se 1 (by rfl) ⟨6167, by rfl⟩) R12335
theorem R8257 : Reach 8257 := rs (se 2 (by rfl) ⟨3096, by rfl⟩) R6193
theorem R8259 : Reach 8259 := rs (se 1 (by rfl) ⟨6194, by rfl⟩) R12389
theorem R8313 : Reach 8313 := rs (se 2 (by rfl) ⟨3117, by rfl⟩) R6235
theorem R8329 : Reach 8329 := rs (se 2 (by rfl) ⟨3123, by rfl⟩) R6247
theorem R15457 : Reach 15457 := rs (se 2 (by rfl) ⟨5796, by rfl⟩) R11593
theorem R15803 : Reach 15803 := rs (se 1 (by rfl) ⟨11852, by rfl⟩) R23705
theorem R15809 : Reach 15809 := rs (se 2 (by rfl) ⟨5928, by rfl⟩) R11857
theorem R15997 : Reach 15997 := rs (se 3 (by rfl) ⟨2999, by rfl⟩) R5999
theorem R245423 : Reach 245423 := rs (se 1 (by rfl) ⟨184067, by rfl⟩) R368135
theorem R16055 : Reach 16055 := rs (se 1 (by rfl) ⟨12041, by rfl⟩) R24083
theorem R16073 : Reach 16073 := rs (se 2 (by rfl) ⟨6027, by rfl⟩) R12055
theorem R16079 : Reach 16079 := rs (se 1 (by rfl) ⟨12059, by rfl⟩) R24119
theorem R16127 : Reach 16127 := rs (se 1 (by rfl) ⟨12095, by rfl⟩) R24191
theorem R16139 : Reach 16139 := rs (se 1 (by rfl) ⟨12104, by rfl⟩) R24209
theorem R16159 : Reach 16159 := rs (se 1 (by rfl) ⟨12119, by rfl⟩) R24239
theorem R16367 : Reach 16367 := rs (se 1 (by rfl) ⟨12275, by rfl⟩) R24551
theorem R16439 : Reach 16439 := rs (se 1 (by rfl) ⟨12329, by rfl⟩) R24659
theorem R16517 : Reach 16517 := rs (se 4 (by rfl) ⟨1548, by rfl⟩) R3097
theorem R61829 : Reach 61829 := rs (se 4 (by rfl) ⟨5796, by rfl⟩) R11593
theorem R128303 : Reach 128303 := rs (se 1 (by rfl) ⟨96227, by rfl⟩) R192455
theorem R63989 : Reach 63989 := rs (se 5 (by rfl) ⟨2999, by rfl⟩) R5999
theorem R64223 : Reach 64223 := rs (se 1 (by rfl) ⟨48167, by rfl⟩) R96335
theorem R129761 : Reach 129761 := rs (se 2 (by rfl) ⟨48660, by rfl⟩) R97321
theorem R64637 : Reach 64637 := rs (se 3 (by rfl) ⟨12119, by rfl⟩) R24239
theorem R32147 : Reach 32147 := rs (se 1 (by rfl) ⟨24110, by rfl⟩) R48221
theorem R32255 : Reach 32255 := rs (se 1 (by rfl) ⟨24191, by rfl⟩) R48383
theorem R32359 : Reach 32359 := rs (se 1 (by rfl) ⟨24269, by rfl⟩) R48539
theorem R32735 : Reach 32735 := rs (se 1 (by rfl) ⟨24551, by rfl⟩) R49103
theorem R2631 : Reach 2631 := rs (se 1 (by rfl) ⟨1973, by rfl⟩) R3947
theorem R5263 : Reach 5263 := rs (se 1 (by rfl) ⟨3947, by rfl⟩) R7895
theorem R5351 : Reach 5351 := rs (se 1 (by rfl) ⟨4013, by rfl⟩) R8027
theorem R5359 : Reach 5359 := rs (se 1 (by rfl) ⟨4019, by rfl⟩) R8039
theorem R5479 : Reach 5479 := rs (se 1 (by rfl) ⟨4109, by rfl⟩) R8219
theorem R5505 : Reach 5505 := rs (se 2 (by rfl) ⟨2064, by rfl⟩) R4129
theorem R41219 : Reach 41219 := rs (se 1 (by rfl) ⟨30914, by rfl⟩) R61829
theorem R42659 : Reach 42659 := rs (se 1 (by rfl) ⟨31994, by rfl⟩) R63989
theorem R42815 : Reach 42815 := rs (se 1 (by rfl) ⟨32111, by rfl⟩) R64223
theorem R43037 : Reach 43037 := rs (se 3 (by rfl) ⟨8069, by rfl⟩) R16139
theorem R43091 : Reach 43091 := rs (se 1 (by rfl) ⟨32318, by rfl⟩) R64637
theorem R43145 : Reach 43145 := rs (se 2 (by rfl) ⟨16179, by rfl⟩) R32359
theorem R10525 : Reach 10525 := rs (se 3 (by rfl) ⟨1973, by rfl⟩) R3947
theorem R10535 : Reach 10535 := rs (se 1 (by rfl) ⟨7901, by rfl⟩) R15803
theorem R10539 : Reach 10539 := rs (se 1 (by rfl) ⟨7904, by rfl⟩) R15809
theorem R10665 : Reach 10665 := rs (se 2 (by rfl) ⟨3999, by rfl⟩) R7999
theorem R10697 : Reach 10697 := rs (se 2 (by rfl) ⟨4011, by rfl⟩) R8023
theorem R10703 : Reach 10703 := rs (se 1 (by rfl) ⟨8027, by rfl⟩) R16055
theorem R10715 : Reach 10715 := rs (se 1 (by rfl) ⟨8036, by rfl⟩) R16073
theorem R10719 : Reach 10719 := rs (se 1 (by rfl) ⟨8039, by rfl⟩) R16079
theorem R10751 : Reach 10751 := rs (se 1 (by rfl) ⟨8063, by rfl⟩) R16127
theorem R10759 : Reach 10759 := rs (se 1 (by rfl) ⟨8069, by rfl⟩) R16139
theorem R10911 : Reach 10911 := rs (se 1 (by rfl) ⟨8183, by rfl⟩) R16367
theorem R10959 : Reach 10959 := rs (se 1 (by rfl) ⟨8219, by rfl⟩) R16439
theorem R11009 : Reach 11009 := rs (se 2 (by rfl) ⟨4128, by rfl⟩) R8257
theorem R11011 : Reach 11011 := rs (se 1 (by rfl) ⟨8258, by rfl⟩) R16517
theorem R11105 : Reach 11105 := rs (se 2 (by rfl) ⟨4164, by rfl⟩) R8329
theorem R177349 : Reach 177349 := rs (se 4 (by rfl) ⟨16626, by rfl⟩) R33253
theorem R85535 : Reach 85535 := rs (se 1 (by rfl) ⟨64151, by rfl⟩) R128303
theorem R20609 : Reach 20609 := rs (se 2 (by rfl) ⟨7728, by rfl⟩) R15457
theorem R86507 : Reach 86507 := rs (se 1 (by rfl) ⟨64880, by rfl⟩) R129761
theorem R21053 : Reach 21053 := rs (se 3 (by rfl) ⟨3947, by rfl⟩) R7895
theorem R21329 : Reach 21329 := rs (se 2 (by rfl) ⟨7998, by rfl⟩) R15997
theorem R21431 : Reach 21431 := rs (se 1 (by rfl) ⟨16073, by rfl⟩) R32147
theorem R21437 : Reach 21437 := rs (se 3 (by rfl) ⟨4019, by rfl⟩) R8039
theorem R21503 : Reach 21503 := rs (se 1 (by rfl) ⟨16127, by rfl⟩) R32255
theorem R21545 : Reach 21545 := rs (se 2 (by rfl) ⟨8079, by rfl⟩) R16159
theorem R87293 : Reach 87293 := rs (se 3 (by rfl) ⟨16367, by rfl⟩) R32735
theorem R22211 : Reach 22211 := rs (se 1 (by rfl) ⟨16658, by rfl⟩) R33317
theorem R88553 : Reach 88553 := rs (se 2 (by rfl) ⟨33207, by rfl⟩) R66415
theorem R163615 : Reach 163615 := rs (se 1 (by rfl) ⟨122711, by rfl⟩) R245423
theorem R3567 : Reach 3567 := rs (se 1 (by rfl) ⟨2675, by rfl⟩) R5351
theorem R236141 : Reach 236141 := rs (se 3 (by rfl) ⟨44276, by rfl⟩) R88553
theorem R7017 : Reach 7017 := rs (se 2 (by rfl) ⟨2631, by rfl⟩) R5263
theorem R7023 : Reach 7023 := rs (se 1 (by rfl) ⟨5267, by rfl⟩) R10535
theorem R236465 : Reach 236465 := rs (se 2 (by rfl) ⟨88674, by rfl⟩) R177349
theorem R7131 : Reach 7131 := rs (se 1 (by rfl) ⟨5348, by rfl⟩) R10697
theorem R7135 : Reach 7135 := rs (se 1 (by rfl) ⟨5351, by rfl⟩) R10703
theorem R7143 : Reach 7143 := rs (se 1 (by rfl) ⟨5357, by rfl⟩) R10715
theorem R7145 : Reach 7145 := rs (se 2 (by rfl) ⟨2679, by rfl⟩) R5359
theorem R7167 : Reach 7167 := rs (se 1 (by rfl) ⟨5375, by rfl⟩) R10751
theorem R7305 : Reach 7305 := rs (se 2 (by rfl) ⟨2739, by rfl⟩) R5479
theorem R7339 : Reach 7339 := rs (se 1 (by rfl) ⟨5504, by rfl⟩) R11009
theorem R7403 : Reach 7403 := rs (se 1 (by rfl) ⟨5552, by rfl⟩) R11105
theorem R13739 : Reach 13739 := rs (se 1 (by rfl) ⟨10304, by rfl⟩) R20609
theorem R14033 : Reach 14033 := rs (se 2 (by rfl) ⟨5262, by rfl⟩) R10525
theorem R14035 : Reach 14035 := rs (se 1 (by rfl) ⟨10526, by rfl⟩) R21053
theorem R14219 : Reach 14219 := rs (se 1 (by rfl) ⟨10664, by rfl⟩) R21329
theorem R14269 : Reach 14269 := rs (se 3 (by rfl) ⟨2675, by rfl⟩) R5351
theorem R14287 : Reach 14287 := rs (se 1 (by rfl) ⟨10715, by rfl⟩) R21431
theorem R14291 : Reach 14291 := rs (se 1 (by rfl) ⟨10718, by rfl⟩) R21437
theorem R14345 : Reach 14345 := rs (se 2 (by rfl) ⟨5379, by rfl⟩) R10759
theorem R14363 : Reach 14363 := rs (se 1 (by rfl) ⟨10772, by rfl⟩) R21545
theorem R14681 : Reach 14681 := rs (se 2 (by rfl) ⟨5505, by rfl⟩) R11011
theorem R14807 : Reach 14807 := rs (se 1 (by rfl) ⟨11105, by rfl⟩) R22211
theorem R114173 : Reach 114173 := rs (se 3 (by rfl) ⟨21407, by rfl⟩) R42815
theorem R218153 : Reach 218153 := rs (se 2 (by rfl) ⟨81807, by rfl⟩) R163615
theorem R57023 : Reach 57023 := rs (se 1 (by rfl) ⟨42767, by rfl⟩) R85535
theorem R57341 : Reach 57341 := rs (se 3 (by rfl) ⟨10751, by rfl⟩) R21503
theorem R57671 : Reach 57671 := rs (se 1 (by rfl) ⟨43253, by rfl⟩) R86507
theorem R58195 : Reach 58195 := rs (se 1 (by rfl) ⟨43646, by rfl⟩) R87293
theorem R27479 : Reach 27479 := rs (se 1 (by rfl) ⟨20609, by rfl⟩) R41219
theorem R28439 : Reach 28439 := rs (se 1 (by rfl) ⟨21329, by rfl⟩) R42659
theorem R28691 : Reach 28691 := rs (se 1 (by rfl) ⟨21518, by rfl⟩) R43037
theorem R28727 : Reach 28727 := rs (se 1 (by rfl) ⟨21545, by rfl⟩) R43091
theorem R28763 : Reach 28763 := rs (se 1 (by rfl) ⟨21572, by rfl⟩) R43145
theorem R37421 : Reach 37421 := rs (se 3 (by rfl) ⟨7016, by rfl⟩) R14033
theorem R4763 : Reach 4763 := rs (se 1 (by rfl) ⟨3572, by rfl⟩) R7145
theorem R4935 : Reach 4935 := rs (se 1 (by rfl) ⟨3701, by rfl⟩) R7403
theorem R38015 : Reach 38015 := rs (se 1 (by rfl) ⟨28511, by rfl⟩) R57023
theorem R38227 : Reach 38227 := rs (se 1 (by rfl) ⟨28670, by rfl⟩) R57341
theorem R38447 : Reach 38447 := rs (se 1 (by rfl) ⟨28835, by rfl⟩) R57671
theorem R39149 : Reach 39149 := rs (se 3 (by rfl) ⟨7340, by rfl⟩) R14681
theorem R9159 : Reach 9159 := rs (se 1 (by rfl) ⟨6869, by rfl⟩) R13739
theorem R9355 : Reach 9355 := rs (se 1 (by rfl) ⟨7016, by rfl⟩) R14033
theorem R9479 : Reach 9479 := rs (se 1 (by rfl) ⟨7109, by rfl⟩) R14219
theorem R9513 : Reach 9513 := rs (se 2 (by rfl) ⟨3567, by rfl⟩) R7135
theorem R9527 : Reach 9527 := rs (se 1 (by rfl) ⟨7145, by rfl⟩) R14291
theorem R9563 : Reach 9563 := rs (se 1 (by rfl) ⟨7172, by rfl⟩) R14345
theorem R9575 : Reach 9575 := rs (se 1 (by rfl) ⟨7181, by rfl⟩) R14363
theorem R9785 : Reach 9785 := rs (se 2 (by rfl) ⟨3669, by rfl⟩) R7339
theorem R9787 : Reach 9787 := rs (se 1 (by rfl) ⟨7340, by rfl⟩) R14681
theorem R9871 : Reach 9871 := rs (se 1 (by rfl) ⟨7403, by rfl⟩) R14807
theorem R76115 : Reach 76115 := rs (se 1 (by rfl) ⟨57086, by rfl⟩) R114173
theorem R77593 : Reach 77593 := rs (se 2 (by rfl) ⟨29097, by rfl⟩) R58195
theorem R145435 : Reach 145435 := rs (se 1 (by rfl) ⟨109076, by rfl⟩) R218153
theorem R18319 : Reach 18319 := rs (se 1 (by rfl) ⟨13739, by rfl⟩) R27479
theorem R18713 : Reach 18713 := rs (se 2 (by rfl) ⟨7017, by rfl⟩) R14035
theorem R18959 : Reach 18959 := rs (se 1 (by rfl) ⟨14219, by rfl⟩) R28439
theorem R19025 : Reach 19025 := rs (se 2 (by rfl) ⟨7134, by rfl⟩) R14269
theorem R19049 : Reach 19049 := rs (se 2 (by rfl) ⟨7143, by rfl⟩) R14287
theorem R19127 : Reach 19127 := rs (se 1 (by rfl) ⟨14345, by rfl⟩) R28691
theorem R19151 : Reach 19151 := rs (se 1 (by rfl) ⟨14363, by rfl⟩) R28727
theorem R19175 : Reach 19175 := rs (se 1 (by rfl) ⟨14381, by rfl⟩) R28763
theorem R157427 : Reach 157427 := rs (se 1 (by rfl) ⟨118070, by rfl⟩) R236141
theorem R157643 : Reach 157643 := rs (se 1 (by rfl) ⟨118232, by rfl⟩) R236465
theorem R3175 : Reach 3175 := rs (se 1 (by rfl) ⟨2381, by rfl⟩) R4763
theorem R103457 : Reach 103457 := rs (se 2 (by rfl) ⟨38796, by rfl⟩) R77593
theorem R6319 : Reach 6319 := rs (se 1 (by rfl) ⟨4739, by rfl⟩) R9479
theorem R6351 : Reach 6351 := rs (se 1 (by rfl) ⟨4763, by rfl⟩) R9527
theorem R6375 : Reach 6375 := rs (se 1 (by rfl) ⟨4781, by rfl⟩) R9563
theorem R6383 : Reach 6383 := rs (se 1 (by rfl) ⟨4787, by rfl⟩) R9575
theorem R6523 : Reach 6523 := rs (se 1 (by rfl) ⟨4892, by rfl⟩) R9785
theorem R104951 : Reach 104951 := rs (se 1 (by rfl) ⟨78713, by rfl⟩) R157427
theorem R105095 : Reach 105095 := rs (se 1 (by rfl) ⟨78821, by rfl⟩) R157643
theorem R12473 : Reach 12473 := rs (se 2 (by rfl) ⟨4677, by rfl⟩) R9355
theorem R12475 : Reach 12475 := rs (se 1 (by rfl) ⟨9356, by rfl⟩) R18713
theorem R12639 : Reach 12639 := rs (se 1 (by rfl) ⟨9479, by rfl⟩) R18959
theorem R12683 : Reach 12683 := rs (se 1 (by rfl) ⟨9512, by rfl⟩) R19025
theorem R12699 : Reach 12699 := rs (se 1 (by rfl) ⟨9524, by rfl⟩) R19049
theorem R12701 : Reach 12701 := rs (se 3 (by rfl) ⟨2381, by rfl⟩) R4763
theorem R12751 : Reach 12751 := rs (se 1 (by rfl) ⟨9563, by rfl⟩) R19127
theorem R12767 : Reach 12767 := rs (se 1 (by rfl) ⟨9575, by rfl⟩) R19151
theorem R12783 : Reach 12783 := rs (se 1 (by rfl) ⟨9587, by rfl⟩) R19175
theorem R13049 : Reach 13049 := rs (se 2 (by rfl) ⟨4893, by rfl⟩) R9787
theorem R50743 : Reach 50743 := rs (se 1 (by rfl) ⟨38057, by rfl⟩) R76115
theorem R50797 : Reach 50797 := rs (se 3 (by rfl) ⟨9524, by rfl⟩) R19049
theorem R50969 : Reach 50969 := rs (se 2 (by rfl) ⟨19113, by rfl⟩) R38227
theorem R24425 : Reach 24425 := rs (se 2 (by rfl) ⟨9159, by rfl⟩) R18319
theorem R24947 : Reach 24947 := rs (se 1 (by rfl) ⟨18710, by rfl⟩) R37421
theorem R25343 : Reach 25343 := rs (se 1 (by rfl) ⟨19007, by rfl⟩) R38015
theorem R25631 : Reach 25631 := rs (se 1 (by rfl) ⟨19223, by rfl⟩) R38447
theorem R26099 : Reach 26099 := rs (se 1 (by rfl) ⟨19574, by rfl⟩) R39149
theorem R193913 : Reach 193913 := rs (se 2 (by rfl) ⟨72717, by rfl⟩) R145435
theorem R33979 : Reach 33979 := rs (se 1 (by rfl) ⟨25484, by rfl⟩) R50969
theorem R67657 : Reach 67657 := rs (se 2 (by rfl) ⟨25371, by rfl⟩) R50743
theorem R67729 : Reach 67729 := rs (se 2 (by rfl) ⟨25398, by rfl⟩) R50797
theorem R68971 : Reach 68971 := rs (se 1 (by rfl) ⟨51728, by rfl⟩) R103457
theorem R4233 : Reach 4233 := rs (se 2 (by rfl) ⟨1587, by rfl⟩) R3175
theorem R4255 : Reach 4255 := rs (se 1 (by rfl) ⟨3191, by rfl⟩) R6383
theorem R69967 : Reach 69967 := rs (se 1 (by rfl) ⟨52475, by rfl⟩) R104951
theorem R8315 : Reach 8315 := rs (se 1 (by rfl) ⟨6236, by rfl⟩) R12473
theorem R8425 : Reach 8425 := rs (se 2 (by rfl) ⟨3159, by rfl⟩) R6319
theorem R8455 : Reach 8455 := rs (se 1 (by rfl) ⟨6341, by rfl⟩) R12683
theorem R8467 : Reach 8467 := rs (se 1 (by rfl) ⟨6350, by rfl⟩) R12701
theorem R8511 : Reach 8511 := rs (se 1 (by rfl) ⟨6383, by rfl⟩) R12767
theorem R8697 : Reach 8697 := rs (se 2 (by rfl) ⟨3261, by rfl⟩) R6523
theorem R8699 : Reach 8699 := rs (se 1 (by rfl) ⟨6524, by rfl⟩) R13049
theorem R16283 : Reach 16283 := rs (se 1 (by rfl) ⟨12212, by rfl⟩) R24425
theorem R16631 : Reach 16631 := rs (se 1 (by rfl) ⟨12473, by rfl⟩) R24947
theorem R16895 : Reach 16895 := rs (se 1 (by rfl) ⟨12671, by rfl⟩) R25343
theorem R17021 : Reach 17021 := rs (se 3 (by rfl) ⟨3191, by rfl⟩) R6383
theorem R17087 : Reach 17087 := rs (se 1 (by rfl) ⟨12815, by rfl⟩) R25631
theorem R17399 : Reach 17399 := rs (se 1 (by rfl) ⟨13049, by rfl⟩) R26099
theorem R280253 : Reach 280253 := rs (se 3 (by rfl) ⟨52547, by rfl⟩) R105095
theorem R129275 : Reach 129275 := rs (se 1 (by rfl) ⟨96956, by rfl⟩) R193913
theorem R5543 : Reach 5543 := rs (se 1 (by rfl) ⟨4157, by rfl⟩) R8315
theorem R5673 : Reach 5673 := rs (se 2 (by rfl) ⟨2127, by rfl⟩) R4255
theorem R5799 : Reach 5799 := rs (se 1 (by rfl) ⟨4349, by rfl⟩) R8699
theorem R10855 : Reach 10855 := rs (se 1 (by rfl) ⟨8141, by rfl⟩) R16283
theorem R11087 : Reach 11087 := rs (se 1 (by rfl) ⟨8315, by rfl⟩) R16631
theorem R11233 : Reach 11233 := rs (se 2 (by rfl) ⟨4212, by rfl⟩) R8425
theorem R11263 : Reach 11263 := rs (se 1 (by rfl) ⟨8447, by rfl⟩) R16895
theorem R11273 : Reach 11273 := rs (se 2 (by rfl) ⟨4227, by rfl⟩) R8455
theorem R11289 : Reach 11289 := rs (se 2 (by rfl) ⟨4233, by rfl⟩) R8467
theorem R11347 : Reach 11347 := rs (se 1 (by rfl) ⟨8510, by rfl⟩) R17021
theorem R11391 : Reach 11391 := rs (se 1 (by rfl) ⟨8543, by rfl⟩) R17087
theorem R11599 : Reach 11599 := rs (se 1 (by rfl) ⟨8699, by rfl⟩) R17399
theorem R45305 : Reach 45305 := rs (se 2 (by rfl) ⟨16989, by rfl⟩) R33979
theorem R373157 : Reach 373157 := rs (se 4 (by rfl) ⟨34983, by rfl⟩) R69967
theorem R86183 : Reach 86183 := rs (se 1 (by rfl) ⟨64637, by rfl⟩) R129275
theorem R22693 : Reach 22693 := rs (se 4 (by rfl) ⟨2127, by rfl⟩) R4255
theorem R186835 : Reach 186835 := rs (se 1 (by rfl) ⟨140126, by rfl⟩) R280253
theorem R90209 : Reach 90209 := rs (se 2 (by rfl) ⟨33828, by rfl⟩) R67657
theorem R90305 : Reach 90305 := rs (se 2 (by rfl) ⟨33864, by rfl⟩) R67729
theorem R91961 : Reach 91961 := rs (se 2 (by rfl) ⟨34485, by rfl⟩) R68971
theorem R3695 : Reach 3695 := rs (se 1 (by rfl) ⟨2771, by rfl⟩) R5543
theorem R7391 : Reach 7391 := rs (se 1 (by rfl) ⟨5543, by rfl⟩) R11087
theorem R7515 : Reach 7515 := rs (se 1 (by rfl) ⟨5636, by rfl⟩) R11273
theorem R15017 : Reach 15017 := rs (se 2 (by rfl) ⟨5631, by rfl⟩) R11263
theorem R248771 : Reach 248771 := rs (se 1 (by rfl) ⟨186578, by rfl⟩) R373157
theorem R249113 : Reach 249113 := rs (se 2 (by rfl) ⟨93417, by rfl⟩) R186835
theorem R57455 : Reach 57455 := rs (se 1 (by rfl) ⟨43091, by rfl⟩) R86183
theorem R60139 : Reach 60139 := rs (se 1 (by rfl) ⟨45104, by rfl⟩) R90209
theorem R60203 : Reach 60203 := rs (se 1 (by rfl) ⟨45152, by rfl⟩) R90305
theorem R61307 : Reach 61307 := rs (se 1 (by rfl) ⟨45980, by rfl⟩) R91961
theorem R30203 : Reach 30203 := rs (se 1 (by rfl) ⟨22652, by rfl⟩) R45305
theorem R30257 : Reach 30257 := rs (se 2 (by rfl) ⟨11346, by rfl⟩) R22693
theorem R165847 : Reach 165847 := rs (se 1 (by rfl) ⟨124385, by rfl⟩) R248771
theorem R2463 : Reach 2463 := rs (se 1 (by rfl) ⟨1847, by rfl⟩) R3695
theorem R4927 : Reach 4927 := rs (se 1 (by rfl) ⟨3695, by rfl⟩) R7391
theorem R38303 : Reach 38303 := rs (se 1 (by rfl) ⟨28727, by rfl⟩) R57455
theorem R40871 : Reach 40871 := rs (se 1 (by rfl) ⟨30653, by rfl⟩) R61307
theorem R664301 : Reach 664301 := rs (se 3 (by rfl) ⟨124556, by rfl⟩) R249113
theorem R9853 : Reach 9853 := rs (se 3 (by rfl) ⟨1847, by rfl⟩) R3695
theorem R10011 : Reach 10011 := rs (se 1 (by rfl) ⟨7508, by rfl⟩) R15017
theorem R80185 : Reach 80185 := rs (se 2 (by rfl) ⟨30069, by rfl⟩) R60139
theorem R19709 : Reach 19709 := rs (se 3 (by rfl) ⟨3695, by rfl⟩) R7391
theorem R20135 : Reach 20135 := rs (se 1 (by rfl) ⟨15101, by rfl⟩) R30203
theorem R20171 : Reach 20171 := rs (se 1 (by rfl) ⟨15128, by rfl⟩) R30257
theorem R160541 : Reach 160541 := rs (se 3 (by rfl) ⟨30101, by rfl⟩) R60203
theorem R1771469 : Reach 1771469 := rs (se 3 (by rfl) ⟨332150, by rfl⟩) R664301
theorem R6569 : Reach 6569 := rs (se 2 (by rfl) ⟨2463, by rfl⟩) R4927
theorem R106913 : Reach 106913 := rs (se 2 (by rfl) ⟨40092, by rfl⟩) R80185
theorem R107027 : Reach 107027 := rs (se 1 (by rfl) ⟨80270, by rfl⟩) R160541
theorem R108989 : Reach 108989 := rs (se 3 (by rfl) ⟨20435, by rfl⟩) R40871
theorem R13139 : Reach 13139 := rs (se 1 (by rfl) ⟨9854, by rfl⟩) R19709
theorem R13423 : Reach 13423 := rs (se 1 (by rfl) ⟨10067, by rfl⟩) R20135
theorem R13447 : Reach 13447 := rs (se 1 (by rfl) ⟨10085, by rfl⟩) R20171
theorem R442867 : Reach 442867 := rs (se 1 (by rfl) ⟨332150, by rfl⟩) R664301
theorem R53693 : Reach 53693 := rs (se 3 (by rfl) ⟨10067, by rfl⟩) R20135
theorem R221129 : Reach 221129 := rs (se 2 (by rfl) ⟨82923, by rfl⟩) R165847
theorem R25535 : Reach 25535 := rs (se 1 (by rfl) ⟨19151, by rfl⟩) R38303
theorem R590489 : Reach 590489 := rs (se 2 (by rfl) ⟨221433, by rfl⟩) R442867
theorem R1180979 : Reach 1180979 := rs (se 1 (by rfl) ⟨885734, by rfl⟩) R1771469
theorem R35795 : Reach 35795 := rs (se 1 (by rfl) ⟨26846, by rfl⟩) R53693
theorem R4379 : Reach 4379 := rs (se 1 (by rfl) ⟨3284, by rfl⟩) R6569
theorem R71275 : Reach 71275 := rs (se 1 (by rfl) ⟨53456, by rfl⟩) R106913
theorem R71351 : Reach 71351 := rs (se 1 (by rfl) ⟨53513, by rfl⟩) R107027
theorem R72659 : Reach 72659 := rs (se 1 (by rfl) ⟨54494, by rfl⟩) R108989
theorem R8759 : Reach 8759 := rs (se 1 (by rfl) ⟨6569, by rfl⟩) R13139
theorem R147419 : Reach 147419 := rs (se 1 (by rfl) ⟨110564, by rfl⟩) R221129
theorem R17023 : Reach 17023 := rs (se 1 (by rfl) ⟨12767, by rfl⟩) R25535
theorem R17897 : Reach 17897 := rs (se 2 (by rfl) ⟨6711, by rfl⟩) R13423
theorem R17929 : Reach 17929 := rs (se 2 (by rfl) ⟨6723, by rfl⟩) R13447
theorem R393659 : Reach 393659 := rs (se 1 (by rfl) ⟨295244, by rfl⟩) R590489
theorem R787319 : Reach 787319 := rs (se 1 (by rfl) ⟨590489, by rfl⟩) R1180979
theorem R2919 : Reach 2919 := rs (se 1 (by rfl) ⟨2189, by rfl⟩) R4379
theorem R5839 : Reach 5839 := rs (se 1 (by rfl) ⟨4379, by rfl⟩) R8759
theorem R11677 : Reach 11677 := rs (se 3 (by rfl) ⟨2189, by rfl⟩) R4379
theorem R11931 : Reach 11931 := rs (se 1 (by rfl) ⟨8948, by rfl⟩) R17897
theorem R47567 : Reach 47567 := rs (se 1 (by rfl) ⟨35675, by rfl⟩) R71351
theorem R48439 : Reach 48439 := rs (se 1 (by rfl) ⟨36329, by rfl⟩) R72659
theorem R22697 : Reach 22697 := rs (se 2 (by rfl) ⟨8511, by rfl⟩) R17023
theorem R23863 : Reach 23863 := rs (se 1 (by rfl) ⟨17897, by rfl⟩) R35795
theorem R23905 : Reach 23905 := rs (se 2 (by rfl) ⟨8964, by rfl⟩) R17929
theorem R95033 : Reach 95033 := rs (se 2 (by rfl) ⟨35637, by rfl⟩) R71275
theorem R98279 : Reach 98279 := rs (se 1 (by rfl) ⟨73709, by rfl⟩) R147419
theorem R262439 : Reach 262439 := rs (se 1 (by rfl) ⟨196829, by rfl⟩) R393659
theorem R524879 : Reach 524879 := rs (se 1 (by rfl) ⟨393659, by rfl⟩) R787319
theorem R7785 : Reach 7785 := rs (se 2 (by rfl) ⟨2919, by rfl⟩) R5839
theorem R15131 : Reach 15131 := rs (se 1 (by rfl) ⟨11348, by rfl⟩) R22697
theorem R15569 : Reach 15569 := rs (se 2 (by rfl) ⟨5838, by rfl⟩) R11677
theorem R126845 : Reach 126845 := rs (se 3 (by rfl) ⟨23783, by rfl⟩) R47567
theorem R63355 : Reach 63355 := rs (se 1 (by rfl) ⟨47516, by rfl⟩) R95033
theorem R31711 : Reach 31711 := rs (se 1 (by rfl) ⟨23783, by rfl⟩) R47567
theorem R64585 : Reach 64585 := rs (se 2 (by rfl) ⟨24219, by rfl⟩) R48439
theorem R31817 : Reach 31817 := rs (se 2 (by rfl) ⟨11931, by rfl⟩) R23863
theorem R31873 : Reach 31873 := rs (se 2 (by rfl) ⟨11952, by rfl⟩) R23905
theorem R65519 : Reach 65519 := rs (se 1 (by rfl) ⟨49139, by rfl⟩) R98279
theorem R42281 : Reach 42281 := rs (se 2 (by rfl) ⟨15855, by rfl⟩) R31711
theorem R42497 : Reach 42497 := rs (se 2 (by rfl) ⟨15936, by rfl⟩) R31873
theorem R10087 : Reach 10087 := rs (se 1 (by rfl) ⟨7565, by rfl⟩) R15131
theorem R10379 : Reach 10379 := rs (se 1 (by rfl) ⟨7784, by rfl⟩) R15569
theorem R43679 : Reach 43679 := rs (se 1 (by rfl) ⟨32759, by rfl⟩) R65519
theorem R174959 : Reach 174959 := rs (se 1 (by rfl) ⟨131219, by rfl⟩) R262439
theorem R84473 : Reach 84473 := rs (se 2 (by rfl) ⟨31677, by rfl⟩) R63355
theorem R84563 : Reach 84563 := rs (se 1 (by rfl) ⟨63422, by rfl⟩) R126845
theorem R84845 : Reach 84845 := rs (se 3 (by rfl) ⟨15908, by rfl⟩) R31817
theorem R86113 : Reach 86113 := rs (se 2 (by rfl) ⟨32292, by rfl⟩) R64585
theorem R349919 : Reach 349919 := rs (se 1 (by rfl) ⟨262439, by rfl⟩) R524879
theorem R233279 : Reach 233279 := rs (se 1 (by rfl) ⟨174959, by rfl⟩) R349919
theorem R6919 : Reach 6919 := rs (se 1 (by rfl) ⟨5189, by rfl⟩) R10379
theorem R114817 : Reach 114817 := rs (se 2 (by rfl) ⟨43056, by rfl⟩) R86113
theorem R116639 : Reach 116639 := rs (se 1 (by rfl) ⟨87479, by rfl⟩) R174959
theorem R56315 : Reach 56315 := rs (se 1 (by rfl) ⟨42236, by rfl⟩) R84473
theorem R56375 : Reach 56375 := rs (se 1 (by rfl) ⟨42281, by rfl⟩) R84563
theorem R28187 : Reach 28187 := rs (se 1 (by rfl) ⟨21140, by rfl⟩) R42281
theorem R28331 : Reach 28331 := rs (se 1 (by rfl) ⟨21248, by rfl⟩) R42497
theorem R29119 : Reach 29119 := rs (se 1 (by rfl) ⟨21839, by rfl⟩) R43679
theorem R226253 : Reach 226253 := rs (se 3 (by rfl) ⟨42422, by rfl⟩) R84845
theorem R37543 : Reach 37543 := rs (se 1 (by rfl) ⟨28157, by rfl⟩) R56315
theorem R37583 : Reach 37583 := rs (se 1 (by rfl) ⟨28187, by rfl⟩) R56375
theorem R38825 : Reach 38825 := rs (se 2 (by rfl) ⟨14559, by rfl⟩) R29119
theorem R9225 : Reach 9225 := rs (se 2 (by rfl) ⟨3459, by rfl⟩) R6919
theorem R77759 : Reach 77759 := rs (se 1 (by rfl) ⟨58319, by rfl⟩) R116639
theorem R18791 : Reach 18791 := rs (se 1 (by rfl) ⟨14093, by rfl⟩) R28187
theorem R18887 : Reach 18887 := rs (se 1 (by rfl) ⟨14165, by rfl⟩) R28331
theorem R150835 : Reach 150835 := rs (se 1 (by rfl) ⟨113126, by rfl⟩) R226253
theorem R153089 : Reach 153089 := rs (se 2 (by rfl) ⟨57408, by rfl⟩) R114817
theorem R155519 : Reach 155519 := rs (se 1 (by rfl) ⟨116639, by rfl⟩) R233279
theorem R102059 : Reach 102059 := rs (se 1 (by rfl) ⟨76544, by rfl⟩) R153089
theorem R201113 : Reach 201113 := rs (se 2 (by rfl) ⟨75417, by rfl⟩) R150835
theorem R103679 : Reach 103679 := rs (se 1 (by rfl) ⟨77759, by rfl⟩) R155519
theorem R12527 : Reach 12527 := rs (se 1 (by rfl) ⟨9395, by rfl⟩) R18791
theorem R12591 : Reach 12591 := rs (se 1 (by rfl) ⟨9443, by rfl⟩) R18887
theorem R50057 : Reach 50057 := rs (se 2 (by rfl) ⟨18771, by rfl⟩) R37543
theorem R51839 : Reach 51839 := rs (se 1 (by rfl) ⟨38879, by rfl⟩) R77759
theorem R25055 : Reach 25055 := rs (se 1 (by rfl) ⟨18791, by rfl⟩) R37583
theorem R25883 : Reach 25883 := rs (se 1 (by rfl) ⟨19412, by rfl⟩) R38825
theorem R33371 : Reach 33371 := rs (se 1 (by rfl) ⟨25028, by rfl⟩) R50057
theorem R34559 : Reach 34559 := rs (se 1 (by rfl) ⟨25919, by rfl⟩) R51839
theorem R68039 : Reach 68039 := rs (se 1 (by rfl) ⟨51029, by rfl⟩) R102059
theorem R134075 : Reach 134075 := rs (se 1 (by rfl) ⟨100556, by rfl⟩) R201113
theorem R69119 : Reach 69119 := rs (se 1 (by rfl) ⟨51839, by rfl⟩) R103679
theorem R8351 : Reach 8351 := rs (se 1 (by rfl) ⟨6263, by rfl⟩) R12527
theorem R16703 : Reach 16703 := rs (se 1 (by rfl) ⟨12527, by rfl⟩) R25055
theorem R17255 : Reach 17255 := rs (se 1 (by rfl) ⟨12941, by rfl⟩) R25883
theorem R5567 : Reach 5567 := rs (se 1 (by rfl) ⟨4175, by rfl⟩) R8351
theorem R11135 : Reach 11135 := rs (se 1 (by rfl) ⟨8351, by rfl⟩) R16703
theorem R11503 : Reach 11503 := rs (se 1 (by rfl) ⟨8627, by rfl⟩) R17255
theorem R45359 : Reach 45359 := rs (se 1 (by rfl) ⟨34019, by rfl⟩) R68039
theorem R46079 : Reach 46079 := rs (se 1 (by rfl) ⟨34559, by rfl⟩) R69119
theorem R22247 : Reach 22247 := rs (se 1 (by rfl) ⟨16685, by rfl⟩) R33371
theorem R23039 : Reach 23039 := rs (se 1 (by rfl) ⟨17279, by rfl⟩) R34559
theorem R89383 : Reach 89383 := rs (se 1 (by rfl) ⟨67037, by rfl⟩) R134075
theorem R3711 : Reach 3711 := rs (se 1 (by rfl) ⟨2783, by rfl⟩) R5567
theorem R7423 : Reach 7423 := rs (se 1 (by rfl) ⟨5567, by rfl⟩) R11135
theorem R14831 : Reach 14831 := rs (se 1 (by rfl) ⟨11123, by rfl⟩) R22247
theorem R15359 : Reach 15359 := rs (se 1 (by rfl) ⟨11519, by rfl⟩) R23039
theorem R119177 : Reach 119177 := rs (se 2 (by rfl) ⟨44691, by rfl⟩) R89383
theorem R30239 : Reach 30239 := rs (se 1 (by rfl) ⟨22679, by rfl⟩) R45359
theorem R30719 : Reach 30719 := rs (se 1 (by rfl) ⟨23039, by rfl⟩) R46079
theorem R9887 : Reach 9887 := rs (se 1 (by rfl) ⟨7415, by rfl⟩) R14831
theorem R9897 : Reach 9897 := rs (se 2 (by rfl) ⟨3711, by rfl⟩) R7423
theorem R10239 : Reach 10239 := rs (se 1 (by rfl) ⟨7679, by rfl⟩) R15359
theorem R79451 : Reach 79451 := rs (se 1 (by rfl) ⟨59588, by rfl⟩) R119177
theorem R20159 : Reach 20159 := rs (se 1 (by rfl) ⟨15119, by rfl⟩) R30239
theorem R20479 : Reach 20479 := rs (se 1 (by rfl) ⟨15359, by rfl⟩) R30719
theorem R6591 : Reach 6591 := rs (se 1 (by rfl) ⟨4943, by rfl⟩) R9887
theorem R13439 : Reach 13439 := rs (se 1 (by rfl) ⟨10079, by rfl⟩) R20159
theorem R52967 : Reach 52967 := rs (se 1 (by rfl) ⟨39725, by rfl⟩) R79451
theorem R26365 : Reach 26365 := rs (se 3 (by rfl) ⟨4943, by rfl⟩) R9887
theorem R27305 : Reach 27305 := rs (se 2 (by rfl) ⟨10239, by rfl⟩) R20479
theorem R35153 : Reach 35153 := rs (se 2 (by rfl) ⟨13182, by rfl⟩) R26365
theorem R35311 : Reach 35311 := rs (se 1 (by rfl) ⟨26483, by rfl⟩) R52967
theorem R8959 : Reach 8959 := rs (se 1 (by rfl) ⟨6719, by rfl⟩) R13439
theorem R18203 : Reach 18203 := rs (se 1 (by rfl) ⟨13652, by rfl⟩) R27305
theorem R11945 : Reach 11945 := rs (se 2 (by rfl) ⟨4479, by rfl⟩) R8959
theorem R12135 : Reach 12135 := rs (se 1 (by rfl) ⟨9101, by rfl⟩) R18203
theorem R47081 : Reach 47081 := rs (se 2 (by rfl) ⟨17655, by rfl⟩) R35311
theorem R23435 : Reach 23435 := rs (se 1 (by rfl) ⟨17576, by rfl⟩) R35153
theorem R7963 : Reach 7963 := rs (se 1 (by rfl) ⟨5972, by rfl⟩) R11945
theorem R15623 : Reach 15623 := rs (se 1 (by rfl) ⟨11717, by rfl⟩) R23435
theorem R31387 : Reach 31387 := rs (se 1 (by rfl) ⟨23540, by rfl⟩) R47081
theorem R31853 : Reach 31853 := rs (se 3 (by rfl) ⟨5972, by rfl⟩) R11945
theorem R41849 : Reach 41849 := rs (se 2 (by rfl) ⟨15693, by rfl⟩) R31387
theorem R10415 : Reach 10415 := rs (se 1 (by rfl) ⟨7811, by rfl⟩) R15623
theorem R10617 : Reach 10617 := rs (se 2 (by rfl) ⟨3981, by rfl⟩) R7963
theorem R21235 : Reach 21235 := rs (se 1 (by rfl) ⟨15926, by rfl⟩) R31853
theorem R6943 : Reach 6943 := rs (se 1 (by rfl) ⟨5207, by rfl⟩) R10415
theorem R27773 : Reach 27773 := rs (se 3 (by rfl) ⟨5207, by rfl⟩) R10415
theorem R27899 : Reach 27899 := rs (se 1 (by rfl) ⟨20924, by rfl⟩) R41849
theorem R28313 : Reach 28313 := rs (se 2 (by rfl) ⟨10617, by rfl⟩) R21235
theorem R9257 : Reach 9257 := rs (se 2 (by rfl) ⟨3471, by rfl⟩) R6943
theorem R18515 : Reach 18515 := rs (se 1 (by rfl) ⟨13886, by rfl⟩) R27773
theorem R18599 : Reach 18599 := rs (se 1 (by rfl) ⟨13949, by rfl⟩) R27899
theorem R18875 : Reach 18875 := rs (se 1 (by rfl) ⟨14156, by rfl⟩) R28313
theorem R6171 : Reach 6171 := rs (se 1 (by rfl) ⟨4628, by rfl⟩) R9257
theorem R12343 : Reach 12343 := rs (se 1 (by rfl) ⟨9257, by rfl⟩) R18515
theorem R12399 : Reach 12399 := rs (se 1 (by rfl) ⟨9299, by rfl⟩) R18599
theorem R12583 : Reach 12583 := rs (se 1 (by rfl) ⟨9437, by rfl⟩) R18875
theorem R16457 : Reach 16457 := rs (se 2 (by rfl) ⟨6171, by rfl⟩) R12343
theorem R10971 : Reach 10971 := rs (se 1 (by rfl) ⟨8228, by rfl⟩) R16457

theorem C0 (j : ℕ) (h1 : 0 ≤ j) (h2 : j ≤ 799) : Reach (2 * j + 1) := by
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

theorem C1 (j : ℕ) (h1 : 800 ≤ j) (h2 : j ≤ 1599) : Reach (2 * j + 1) := by
  interval_cases j
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

theorem C2 (j : ℕ) (h1 : 1600 ≤ j) (h2 : j ≤ 2399) : Reach (2 * j + 1) := by
  interval_cases j
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

theorem C3 (j : ℕ) (h1 : 2400 ≤ j) (h2 : j ≤ 3199) : Reach (2 * j + 1) := by
  interval_cases j
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

theorem C4 (j : ℕ) (h1 : 3200 ≤ j) (h2 : j ≤ 3999) : Reach (2 * j + 1) := by
  interval_cases j
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
  · exact R6725
  · exact R6727
  · exact R6729
  · exact R6731
  · exact R6733
  · exact R6735
  · exact R6737
  · exact R6739
  · exact R6741
  · exact R6743
  · exact R6745
  · exact R6747
  · exact R6749
  · exact R6751
  · exact R6753
  · exact R6755
  · exact R6757
  · exact R6759
  · exact R6761
  · exact R6763
  · exact R6765
  · exact R6767
  · exact R6769
  · exact R6771
  · exact R6773
  · exact R6775
  · exact R6777
  · exact R6779
  · exact R6781
  · exact R6783
  · exact R6785
  · exact R6787
  · exact R6789
  · exact R6791
  · exact R6793
  · exact R6795
  · exact R6797
  · exact R6799
  · exact R6801
  · exact R6803
  · exact R6805
  · exact R6807
  · exact R6809
  · exact R6811
  · exact R6813
  · exact R6815
  · exact R6817
  · exact R6819
  · exact R6821
  · exact R6823
  · exact R6825
  · exact R6827
  · exact R6829
  · exact R6831
  · exact R6833
  · exact R6835
  · exact R6837
  · exact R6839
  · exact R6841
  · exact R6843
  · exact R6845
  · exact R6847
  · exact R6849
  · exact R6851
  · exact R6853
  · exact R6855
  · exact R6857
  · exact R6859
  · exact R6861
  · exact R6863
  · exact R6865
  · exact R6867
  · exact R6869
  · exact R6871
  · exact R6873
  · exact R6875
  · exact R6877
  · exact R6879
  · exact R6881
  · exact R6883
  · exact R6885
  · exact R6887
  · exact R6889
  · exact R6891
  · exact R6893
  · exact R6895
  · exact R6897
  · exact R6899
  · exact R6901
  · exact R6903
  · exact R6905
  · exact R6907
  · exact R6909
  · exact R6911
  · exact R6913
  · exact R6915
  · exact R6917
  · exact R6919
  · exact R6921
  · exact R6923
  · exact R6925
  · exact R6927
  · exact R6929
  · exact R6931
  · exact R6933
  · exact R6935
  · exact R6937
  · exact R6939
  · exact R6941
  · exact R6943
  · exact R6945
  · exact R6947
  · exact R6949
  · exact R6951
  · exact R6953
  · exact R6955
  · exact R6957
  · exact R6959
  · exact R6961
  · exact R6963
  · exact R6965
  · exact R6967
  · exact R6969
  · exact R6971
  · exact R6973
  · exact R6975
  · exact R6977
  · exact R6979
  · exact R6981
  · exact R6983
  · exact R6985
  · exact R6987
  · exact R6989
  · exact R6991
  · exact R6993
  · exact R6995
  · exact R6997
  · exact R6999
  · exact R7001
  · exact R7003
  · exact R7005
  · exact R7007
  · exact R7009
  · exact R7011
  · exact R7013
  · exact R7015
  · exact R7017
  · exact R7019
  · exact R7021
  · exact R7023
  · exact R7025
  · exact R7027
  · exact R7029
  · exact R7031
  · exact R7033
  · exact R7035
  · exact R7037
  · exact R7039
  · exact R7041
  · exact R7043
  · exact R7045
  · exact R7047
  · exact R7049
  · exact R7051
  · exact R7053
  · exact R7055
  · exact R7057
  · exact R7059
  · exact R7061
  · exact R7063
  · exact R7065
  · exact R7067
  · exact R7069
  · exact R7071
  · exact R7073
  · exact R7075
  · exact R7077
  · exact R7079
  · exact R7081
  · exact R7083
  · exact R7085
  · exact R7087
  · exact R7089
  · exact R7091
  · exact R7093
  · exact R7095
  · exact R7097
  · exact R7099
  · exact R7101
  · exact R7103
  · exact R7105
  · exact R7107
  · exact R7109
  · exact R7111
  · exact R7113
  · exact R7115
  · exact R7117
  · exact R7119
  · exact R7121
  · exact R7123
  · exact R7125
  · exact R7127
  · exact R7129
  · exact R7131
  · exact R7133
  · exact R7135
  · exact R7137
  · exact R7139
  · exact R7141
  · exact R7143
  · exact R7145
  · exact R7147
  · exact R7149
  · exact R7151
  · exact R7153
  · exact R7155
  · exact R7157
  · exact R7159
  · exact R7161
  · exact R7163
  · exact R7165
  · exact R7167
  · exact R7169
  · exact R7171
  · exact R7173
  · exact R7175
  · exact R7177
  · exact R7179
  · exact R7181
  · exact R7183
  · exact R7185
  · exact R7187
  · exact R7189
  · exact R7191
  · exact R7193
  · exact R7195
  · exact R7197
  · exact R7199
  · exact R7201
  · exact R7203
  · exact R7205
  · exact R7207
  · exact R7209
  · exact R7211
  · exact R7213
  · exact R7215
  · exact R7217
  · exact R7219
  · exact R7221
  · exact R7223
  · exact R7225
  · exact R7227
  · exact R7229
  · exact R7231
  · exact R7233
  · exact R7235
  · exact R7237
  · exact R7239
  · exact R7241
  · exact R7243
  · exact R7245
  · exact R7247
  · exact R7249
  · exact R7251
  · exact R7253
  · exact R7255
  · exact R7257
  · exact R7259
  · exact R7261
  · exact R7263
  · exact R7265
  · exact R7267
  · exact R7269
  · exact R7271
  · exact R7273
  · exact R7275
  · exact R7277
  · exact R7279
  · exact R7281
  · exact R7283
  · exact R7285
  · exact R7287
  · exact R7289
  · exact R7291
  · exact R7293
  · exact R7295
  · exact R7297
  · exact R7299
  · exact R7301
  · exact R7303
  · exact R7305
  · exact R7307
  · exact R7309
  · exact R7311
  · exact R7313
  · exact R7315
  · exact R7317
  · exact R7319
  · exact R7321
  · exact R7323
  · exact R7325
  · exact R7327
  · exact R7329
  · exact R7331
  · exact R7333
  · exact R7335
  · exact R7337
  · exact R7339
  · exact R7341
  · exact R7343
  · exact R7345
  · exact R7347
  · exact R7349
  · exact R7351
  · exact R7353
  · exact R7355
  · exact R7357
  · exact R7359
  · exact R7361
  · exact R7363
  · exact R7365
  · exact R7367
  · exact R7369
  · exact R7371
  · exact R7373
  · exact R7375
  · exact R7377
  · exact R7379
  · exact R7381
  · exact R7383
  · exact R7385
  · exact R7387
  · exact R7389
  · exact R7391
  · exact R7393
  · exact R7395
  · exact R7397
  · exact R7399
  · exact R7401
  · exact R7403
  · exact R7405
  · exact R7407
  · exact R7409
  · exact R7411
  · exact R7413
  · exact R7415
  · exact R7417
  · exact R7419
  · exact R7421
  · exact R7423
  · exact R7425
  · exact R7427
  · exact R7429
  · exact R7431
  · exact R7433
  · exact R7435
  · exact R7437
  · exact R7439
  · exact R7441
  · exact R7443
  · exact R7445
  · exact R7447
  · exact R7449
  · exact R7451
  · exact R7453
  · exact R7455
  · exact R7457
  · exact R7459
  · exact R7461
  · exact R7463
  · exact R7465
  · exact R7467
  · exact R7469
  · exact R7471
  · exact R7473
  · exact R7475
  · exact R7477
  · exact R7479
  · exact R7481
  · exact R7483
  · exact R7485
  · exact R7487
  · exact R7489
  · exact R7491
  · exact R7493
  · exact R7495
  · exact R7497
  · exact R7499
  · exact R7501
  · exact R7503
  · exact R7505
  · exact R7507
  · exact R7509
  · exact R7511
  · exact R7513
  · exact R7515
  · exact R7517
  · exact R7519
  · exact R7521
  · exact R7523
  · exact R7525
  · exact R7527
  · exact R7529
  · exact R7531
  · exact R7533
  · exact R7535
  · exact R7537
  · exact R7539
  · exact R7541
  · exact R7543
  · exact R7545
  · exact R7547
  · exact R7549
  · exact R7551
  · exact R7553
  · exact R7555
  · exact R7557
  · exact R7559
  · exact R7561
  · exact R7563
  · exact R7565
  · exact R7567
  · exact R7569
  · exact R7571
  · exact R7573
  · exact R7575
  · exact R7577
  · exact R7579
  · exact R7581
  · exact R7583
  · exact R7585
  · exact R7587
  · exact R7589
  · exact R7591
  · exact R7593
  · exact R7595
  · exact R7597
  · exact R7599
  · exact R7601
  · exact R7603
  · exact R7605
  · exact R7607
  · exact R7609
  · exact R7611
  · exact R7613
  · exact R7615
  · exact R7617
  · exact R7619
  · exact R7621
  · exact R7623
  · exact R7625
  · exact R7627
  · exact R7629
  · exact R7631
  · exact R7633
  · exact R7635
  · exact R7637
  · exact R7639
  · exact R7641
  · exact R7643
  · exact R7645
  · exact R7647
  · exact R7649
  · exact R7651
  · exact R7653
  · exact R7655
  · exact R7657
  · exact R7659
  · exact R7661
  · exact R7663
  · exact R7665
  · exact R7667
  · exact R7669
  · exact R7671
  · exact R7673
  · exact R7675
  · exact R7677
  · exact R7679
  · exact R7681
  · exact R7683
  · exact R7685
  · exact R7687
  · exact R7689
  · exact R7691
  · exact R7693
  · exact R7695
  · exact R7697
  · exact R7699
  · exact R7701
  · exact R7703
  · exact R7705
  · exact R7707
  · exact R7709
  · exact R7711
  · exact R7713
  · exact R7715
  · exact R7717
  · exact R7719
  · exact R7721
  · exact R7723
  · exact R7725
  · exact R7727
  · exact R7729
  · exact R7731
  · exact R7733
  · exact R7735
  · exact R7737
  · exact R7739
  · exact R7741
  · exact R7743
  · exact R7745
  · exact R7747
  · exact R7749
  · exact R7751
  · exact R7753
  · exact R7755
  · exact R7757
  · exact R7759
  · exact R7761
  · exact R7763
  · exact R7765
  · exact R7767
  · exact R7769
  · exact R7771
  · exact R7773
  · exact R7775
  · exact R7777
  · exact R7779
  · exact R7781
  · exact R7783
  · exact R7785
  · exact R7787
  · exact R7789
  · exact R7791
  · exact R7793
  · exact R7795
  · exact R7797
  · exact R7799
  · exact R7801
  · exact R7803
  · exact R7805
  · exact R7807
  · exact R7809
  · exact R7811
  · exact R7813
  · exact R7815
  · exact R7817
  · exact R7819
  · exact R7821
  · exact R7823
  · exact R7825
  · exact R7827
  · exact R7829
  · exact R7831
  · exact R7833
  · exact R7835
  · exact R7837
  · exact R7839
  · exact R7841
  · exact R7843
  · exact R7845
  · exact R7847
  · exact R7849
  · exact R7851
  · exact R7853
  · exact R7855
  · exact R7857
  · exact R7859
  · exact R7861
  · exact R7863
  · exact R7865
  · exact R7867
  · exact R7869
  · exact R7871
  · exact R7873
  · exact R7875
  · exact R7877
  · exact R7879
  · exact R7881
  · exact R7883
  · exact R7885
  · exact R7887
  · exact R7889
  · exact R7891
  · exact R7893
  · exact R7895
  · exact R7897
  · exact R7899
  · exact R7901
  · exact R7903
  · exact R7905
  · exact R7907
  · exact R7909
  · exact R7911
  · exact R7913
  · exact R7915
  · exact R7917
  · exact R7919
  · exact R7921
  · exact R7923
  · exact R7925
  · exact R7927
  · exact R7929
  · exact R7931
  · exact R7933
  · exact R7935
  · exact R7937
  · exact R7939
  · exact R7941
  · exact R7943
  · exact R7945
  · exact R7947
  · exact R7949
  · exact R7951
  · exact R7953
  · exact R7955
  · exact R7957
  · exact R7959
  · exact R7961
  · exact R7963
  · exact R7965
  · exact R7967
  · exact R7969
  · exact R7971
  · exact R7973
  · exact R7975
  · exact R7977
  · exact R7979
  · exact R7981
  · exact R7983
  · exact R7985
  · exact R7987
  · exact R7989
  · exact R7991
  · exact R7993
  · exact R7995
  · exact R7997
  · exact R7999

theorem C5 (j : ℕ) (h1 : 4000 ≤ j) (h2 : j ≤ 4799) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R8001
  · exact R8003
  · exact R8005
  · exact R8007
  · exact R8009
  · exact R8011
  · exact R8013
  · exact R8015
  · exact R8017
  · exact R8019
  · exact R8021
  · exact R8023
  · exact R8025
  · exact R8027
  · exact R8029
  · exact R8031
  · exact R8033
  · exact R8035
  · exact R8037
  · exact R8039
  · exact R8041
  · exact R8043
  · exact R8045
  · exact R8047
  · exact R8049
  · exact R8051
  · exact R8053
  · exact R8055
  · exact R8057
  · exact R8059
  · exact R8061
  · exact R8063
  · exact R8065
  · exact R8067
  · exact R8069
  · exact R8071
  · exact R8073
  · exact R8075
  · exact R8077
  · exact R8079
  · exact R8081
  · exact R8083
  · exact R8085
  · exact R8087
  · exact R8089
  · exact R8091
  · exact R8093
  · exact R8095
  · exact R8097
  · exact R8099
  · exact R8101
  · exact R8103
  · exact R8105
  · exact R8107
  · exact R8109
  · exact R8111
  · exact R8113
  · exact R8115
  · exact R8117
  · exact R8119
  · exact R8121
  · exact R8123
  · exact R8125
  · exact R8127
  · exact R8129
  · exact R8131
  · exact R8133
  · exact R8135
  · exact R8137
  · exact R8139
  · exact R8141
  · exact R8143
  · exact R8145
  · exact R8147
  · exact R8149
  · exact R8151
  · exact R8153
  · exact R8155
  · exact R8157
  · exact R8159
  · exact R8161
  · exact R8163
  · exact R8165
  · exact R8167
  · exact R8169
  · exact R8171
  · exact R8173
  · exact R8175
  · exact R8177
  · exact R8179
  · exact R8181
  · exact R8183
  · exact R8185
  · exact R8187
  · exact R8189
  · exact R8191
  · exact R8193
  · exact R8195
  · exact R8197
  · exact R8199
  · exact R8201
  · exact R8203
  · exact R8205
  · exact R8207
  · exact R8209
  · exact R8211
  · exact R8213
  · exact R8215
  · exact R8217
  · exact R8219
  · exact R8221
  · exact R8223
  · exact R8225
  · exact R8227
  · exact R8229
  · exact R8231
  · exact R8233
  · exact R8235
  · exact R8237
  · exact R8239
  · exact R8241
  · exact R8243
  · exact R8245
  · exact R8247
  · exact R8249
  · exact R8251
  · exact R8253
  · exact R8255
  · exact R8257
  · exact R8259
  · exact R8261
  · exact R8263
  · exact R8265
  · exact R8267
  · exact R8269
  · exact R8271
  · exact R8273
  · exact R8275
  · exact R8277
  · exact R8279
  · exact R8281
  · exact R8283
  · exact R8285
  · exact R8287
  · exact R8289
  · exact R8291
  · exact R8293
  · exact R8295
  · exact R8297
  · exact R8299
  · exact R8301
  · exact R8303
  · exact R8305
  · exact R8307
  · exact R8309
  · exact R8311
  · exact R8313
  · exact R8315
  · exact R8317
  · exact R8319
  · exact R8321
  · exact R8323
  · exact R8325
  · exact R8327
  · exact R8329
  · exact R8331
  · exact R8333
  · exact R8335
  · exact R8337
  · exact R8339
  · exact R8341
  · exact R8343
  · exact R8345
  · exact R8347
  · exact R8349
  · exact R8351
  · exact R8353
  · exact R8355
  · exact R8357
  · exact R8359
  · exact R8361
  · exact R8363
  · exact R8365
  · exact R8367
  · exact R8369
  · exact R8371
  · exact R8373
  · exact R8375
  · exact R8377
  · exact R8379
  · exact R8381
  · exact R8383
  · exact R8385
  · exact R8387
  · exact R8389
  · exact R8391
  · exact R8393
  · exact R8395
  · exact R8397
  · exact R8399
  · exact R8401
  · exact R8403
  · exact R8405
  · exact R8407
  · exact R8409
  · exact R8411
  · exact R8413
  · exact R8415
  · exact R8417
  · exact R8419
  · exact R8421
  · exact R8423
  · exact R8425
  · exact R8427
  · exact R8429
  · exact R8431
  · exact R8433
  · exact R8435
  · exact R8437
  · exact R8439
  · exact R8441
  · exact R8443
  · exact R8445
  · exact R8447
  · exact R8449
  · exact R8451
  · exact R8453
  · exact R8455
  · exact R8457
  · exact R8459
  · exact R8461
  · exact R8463
  · exact R8465
  · exact R8467
  · exact R8469
  · exact R8471
  · exact R8473
  · exact R8475
  · exact R8477
  · exact R8479
  · exact R8481
  · exact R8483
  · exact R8485
  · exact R8487
  · exact R8489
  · exact R8491
  · exact R8493
  · exact R8495
  · exact R8497
  · exact R8499
  · exact R8501
  · exact R8503
  · exact R8505
  · exact R8507
  · exact R8509
  · exact R8511
  · exact R8513
  · exact R8515
  · exact R8517
  · exact R8519
  · exact R8521
  · exact R8523
  · exact R8525
  · exact R8527
  · exact R8529
  · exact R8531
  · exact R8533
  · exact R8535
  · exact R8537
  · exact R8539
  · exact R8541
  · exact R8543
  · exact R8545
  · exact R8547
  · exact R8549
  · exact R8551
  · exact R8553
  · exact R8555
  · exact R8557
  · exact R8559
  · exact R8561
  · exact R8563
  · exact R8565
  · exact R8567
  · exact R8569
  · exact R8571
  · exact R8573
  · exact R8575
  · exact R8577
  · exact R8579
  · exact R8581
  · exact R8583
  · exact R8585
  · exact R8587
  · exact R8589
  · exact R8591
  · exact R8593
  · exact R8595
  · exact R8597
  · exact R8599
  · exact R8601
  · exact R8603
  · exact R8605
  · exact R8607
  · exact R8609
  · exact R8611
  · exact R8613
  · exact R8615
  · exact R8617
  · exact R8619
  · exact R8621
  · exact R8623
  · exact R8625
  · exact R8627
  · exact R8629
  · exact R8631
  · exact R8633
  · exact R8635
  · exact R8637
  · exact R8639
  · exact R8641
  · exact R8643
  · exact R8645
  · exact R8647
  · exact R8649
  · exact R8651
  · exact R8653
  · exact R8655
  · exact R8657
  · exact R8659
  · exact R8661
  · exact R8663
  · exact R8665
  · exact R8667
  · exact R8669
  · exact R8671
  · exact R8673
  · exact R8675
  · exact R8677
  · exact R8679
  · exact R8681
  · exact R8683
  · exact R8685
  · exact R8687
  · exact R8689
  · exact R8691
  · exact R8693
  · exact R8695
  · exact R8697
  · exact R8699
  · exact R8701
  · exact R8703
  · exact R8705
  · exact R8707
  · exact R8709
  · exact R8711
  · exact R8713
  · exact R8715
  · exact R8717
  · exact R8719
  · exact R8721
  · exact R8723
  · exact R8725
  · exact R8727
  · exact R8729
  · exact R8731
  · exact R8733
  · exact R8735
  · exact R8737
  · exact R8739
  · exact R8741
  · exact R8743
  · exact R8745
  · exact R8747
  · exact R8749
  · exact R8751
  · exact R8753
  · exact R8755
  · exact R8757
  · exact R8759
  · exact R8761
  · exact R8763
  · exact R8765
  · exact R8767
  · exact R8769
  · exact R8771
  · exact R8773
  · exact R8775
  · exact R8777
  · exact R8779
  · exact R8781
  · exact R8783
  · exact R8785
  · exact R8787
  · exact R8789
  · exact R8791
  · exact R8793
  · exact R8795
  · exact R8797
  · exact R8799
  · exact R8801
  · exact R8803
  · exact R8805
  · exact R8807
  · exact R8809
  · exact R8811
  · exact R8813
  · exact R8815
  · exact R8817
  · exact R8819
  · exact R8821
  · exact R8823
  · exact R8825
  · exact R8827
  · exact R8829
  · exact R8831
  · exact R8833
  · exact R8835
  · exact R8837
  · exact R8839
  · exact R8841
  · exact R8843
  · exact R8845
  · exact R8847
  · exact R8849
  · exact R8851
  · exact R8853
  · exact R8855
  · exact R8857
  · exact R8859
  · exact R8861
  · exact R8863
  · exact R8865
  · exact R8867
  · exact R8869
  · exact R8871
  · exact R8873
  · exact R8875
  · exact R8877
  · exact R8879
  · exact R8881
  · exact R8883
  · exact R8885
  · exact R8887
  · exact R8889
  · exact R8891
  · exact R8893
  · exact R8895
  · exact R8897
  · exact R8899
  · exact R8901
  · exact R8903
  · exact R8905
  · exact R8907
  · exact R8909
  · exact R8911
  · exact R8913
  · exact R8915
  · exact R8917
  · exact R8919
  · exact R8921
  · exact R8923
  · exact R8925
  · exact R8927
  · exact R8929
  · exact R8931
  · exact R8933
  · exact R8935
  · exact R8937
  · exact R8939
  · exact R8941
  · exact R8943
  · exact R8945
  · exact R8947
  · exact R8949
  · exact R8951
  · exact R8953
  · exact R8955
  · exact R8957
  · exact R8959
  · exact R8961
  · exact R8963
  · exact R8965
  · exact R8967
  · exact R8969
  · exact R8971
  · exact R8973
  · exact R8975
  · exact R8977
  · exact R8979
  · exact R8981
  · exact R8983
  · exact R8985
  · exact R8987
  · exact R8989
  · exact R8991
  · exact R8993
  · exact R8995
  · exact R8997
  · exact R8999
  · exact R9001
  · exact R9003
  · exact R9005
  · exact R9007
  · exact R9009
  · exact R9011
  · exact R9013
  · exact R9015
  · exact R9017
  · exact R9019
  · exact R9021
  · exact R9023
  · exact R9025
  · exact R9027
  · exact R9029
  · exact R9031
  · exact R9033
  · exact R9035
  · exact R9037
  · exact R9039
  · exact R9041
  · exact R9043
  · exact R9045
  · exact R9047
  · exact R9049
  · exact R9051
  · exact R9053
  · exact R9055
  · exact R9057
  · exact R9059
  · exact R9061
  · exact R9063
  · exact R9065
  · exact R9067
  · exact R9069
  · exact R9071
  · exact R9073
  · exact R9075
  · exact R9077
  · exact R9079
  · exact R9081
  · exact R9083
  · exact R9085
  · exact R9087
  · exact R9089
  · exact R9091
  · exact R9093
  · exact R9095
  · exact R9097
  · exact R9099
  · exact R9101
  · exact R9103
  · exact R9105
  · exact R9107
  · exact R9109
  · exact R9111
  · exact R9113
  · exact R9115
  · exact R9117
  · exact R9119
  · exact R9121
  · exact R9123
  · exact R9125
  · exact R9127
  · exact R9129
  · exact R9131
  · exact R9133
  · exact R9135
  · exact R9137
  · exact R9139
  · exact R9141
  · exact R9143
  · exact R9145
  · exact R9147
  · exact R9149
  · exact R9151
  · exact R9153
  · exact R9155
  · exact R9157
  · exact R9159
  · exact R9161
  · exact R9163
  · exact R9165
  · exact R9167
  · exact R9169
  · exact R9171
  · exact R9173
  · exact R9175
  · exact R9177
  · exact R9179
  · exact R9181
  · exact R9183
  · exact R9185
  · exact R9187
  · exact R9189
  · exact R9191
  · exact R9193
  · exact R9195
  · exact R9197
  · exact R9199
  · exact R9201
  · exact R9203
  · exact R9205
  · exact R9207
  · exact R9209
  · exact R9211
  · exact R9213
  · exact R9215
  · exact R9217
  · exact R9219
  · exact R9221
  · exact R9223
  · exact R9225
  · exact R9227
  · exact R9229
  · exact R9231
  · exact R9233
  · exact R9235
  · exact R9237
  · exact R9239
  · exact R9241
  · exact R9243
  · exact R9245
  · exact R9247
  · exact R9249
  · exact R9251
  · exact R9253
  · exact R9255
  · exact R9257
  · exact R9259
  · exact R9261
  · exact R9263
  · exact R9265
  · exact R9267
  · exact R9269
  · exact R9271
  · exact R9273
  · exact R9275
  · exact R9277
  · exact R9279
  · exact R9281
  · exact R9283
  · exact R9285
  · exact R9287
  · exact R9289
  · exact R9291
  · exact R9293
  · exact R9295
  · exact R9297
  · exact R9299
  · exact R9301
  · exact R9303
  · exact R9305
  · exact R9307
  · exact R9309
  · exact R9311
  · exact R9313
  · exact R9315
  · exact R9317
  · exact R9319
  · exact R9321
  · exact R9323
  · exact R9325
  · exact R9327
  · exact R9329
  · exact R9331
  · exact R9333
  · exact R9335
  · exact R9337
  · exact R9339
  · exact R9341
  · exact R9343
  · exact R9345
  · exact R9347
  · exact R9349
  · exact R9351
  · exact R9353
  · exact R9355
  · exact R9357
  · exact R9359
  · exact R9361
  · exact R9363
  · exact R9365
  · exact R9367
  · exact R9369
  · exact R9371
  · exact R9373
  · exact R9375
  · exact R9377
  · exact R9379
  · exact R9381
  · exact R9383
  · exact R9385
  · exact R9387
  · exact R9389
  · exact R9391
  · exact R9393
  · exact R9395
  · exact R9397
  · exact R9399
  · exact R9401
  · exact R9403
  · exact R9405
  · exact R9407
  · exact R9409
  · exact R9411
  · exact R9413
  · exact R9415
  · exact R9417
  · exact R9419
  · exact R9421
  · exact R9423
  · exact R9425
  · exact R9427
  · exact R9429
  · exact R9431
  · exact R9433
  · exact R9435
  · exact R9437
  · exact R9439
  · exact R9441
  · exact R9443
  · exact R9445
  · exact R9447
  · exact R9449
  · exact R9451
  · exact R9453
  · exact R9455
  · exact R9457
  · exact R9459
  · exact R9461
  · exact R9463
  · exact R9465
  · exact R9467
  · exact R9469
  · exact R9471
  · exact R9473
  · exact R9475
  · exact R9477
  · exact R9479
  · exact R9481
  · exact R9483
  · exact R9485
  · exact R9487
  · exact R9489
  · exact R9491
  · exact R9493
  · exact R9495
  · exact R9497
  · exact R9499
  · exact R9501
  · exact R9503
  · exact R9505
  · exact R9507
  · exact R9509
  · exact R9511
  · exact R9513
  · exact R9515
  · exact R9517
  · exact R9519
  · exact R9521
  · exact R9523
  · exact R9525
  · exact R9527
  · exact R9529
  · exact R9531
  · exact R9533
  · exact R9535
  · exact R9537
  · exact R9539
  · exact R9541
  · exact R9543
  · exact R9545
  · exact R9547
  · exact R9549
  · exact R9551
  · exact R9553
  · exact R9555
  · exact R9557
  · exact R9559
  · exact R9561
  · exact R9563
  · exact R9565
  · exact R9567
  · exact R9569
  · exact R9571
  · exact R9573
  · exact R9575
  · exact R9577
  · exact R9579
  · exact R9581
  · exact R9583
  · exact R9585
  · exact R9587
  · exact R9589
  · exact R9591
  · exact R9593
  · exact R9595
  · exact R9597
  · exact R9599

theorem C6 (j : ℕ) (h1 : 4800 ≤ j) (h2 : j ≤ 5599) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R9601
  · exact R9603
  · exact R9605
  · exact R9607
  · exact R9609
  · exact R9611
  · exact R9613
  · exact R9615
  · exact R9617
  · exact R9619
  · exact R9621
  · exact R9623
  · exact R9625
  · exact R9627
  · exact R9629
  · exact R9631
  · exact R9633
  · exact R9635
  · exact R9637
  · exact R9639
  · exact R9641
  · exact R9643
  · exact R9645
  · exact R9647
  · exact R9649
  · exact R9651
  · exact R9653
  · exact R9655
  · exact R9657
  · exact R9659
  · exact R9661
  · exact R9663
  · exact R9665
  · exact R9667
  · exact R9669
  · exact R9671
  · exact R9673
  · exact R9675
  · exact R9677
  · exact R9679
  · exact R9681
  · exact R9683
  · exact R9685
  · exact R9687
  · exact R9689
  · exact R9691
  · exact R9693
  · exact R9695
  · exact R9697
  · exact R9699
  · exact R9701
  · exact R9703
  · exact R9705
  · exact R9707
  · exact R9709
  · exact R9711
  · exact R9713
  · exact R9715
  · exact R9717
  · exact R9719
  · exact R9721
  · exact R9723
  · exact R9725
  · exact R9727
  · exact R9729
  · exact R9731
  · exact R9733
  · exact R9735
  · exact R9737
  · exact R9739
  · exact R9741
  · exact R9743
  · exact R9745
  · exact R9747
  · exact R9749
  · exact R9751
  · exact R9753
  · exact R9755
  · exact R9757
  · exact R9759
  · exact R9761
  · exact R9763
  · exact R9765
  · exact R9767
  · exact R9769
  · exact R9771
  · exact R9773
  · exact R9775
  · exact R9777
  · exact R9779
  · exact R9781
  · exact R9783
  · exact R9785
  · exact R9787
  · exact R9789
  · exact R9791
  · exact R9793
  · exact R9795
  · exact R9797
  · exact R9799
  · exact R9801
  · exact R9803
  · exact R9805
  · exact R9807
  · exact R9809
  · exact R9811
  · exact R9813
  · exact R9815
  · exact R9817
  · exact R9819
  · exact R9821
  · exact R9823
  · exact R9825
  · exact R9827
  · exact R9829
  · exact R9831
  · exact R9833
  · exact R9835
  · exact R9837
  · exact R9839
  · exact R9841
  · exact R9843
  · exact R9845
  · exact R9847
  · exact R9849
  · exact R9851
  · exact R9853
  · exact R9855
  · exact R9857
  · exact R9859
  · exact R9861
  · exact R9863
  · exact R9865
  · exact R9867
  · exact R9869
  · exact R9871
  · exact R9873
  · exact R9875
  · exact R9877
  · exact R9879
  · exact R9881
  · exact R9883
  · exact R9885
  · exact R9887
  · exact R9889
  · exact R9891
  · exact R9893
  · exact R9895
  · exact R9897
  · exact R9899
  · exact R9901
  · exact R9903
  · exact R9905
  · exact R9907
  · exact R9909
  · exact R9911
  · exact R9913
  · exact R9915
  · exact R9917
  · exact R9919
  · exact R9921
  · exact R9923
  · exact R9925
  · exact R9927
  · exact R9929
  · exact R9931
  · exact R9933
  · exact R9935
  · exact R9937
  · exact R9939
  · exact R9941
  · exact R9943
  · exact R9945
  · exact R9947
  · exact R9949
  · exact R9951
  · exact R9953
  · exact R9955
  · exact R9957
  · exact R9959
  · exact R9961
  · exact R9963
  · exact R9965
  · exact R9967
  · exact R9969
  · exact R9971
  · exact R9973
  · exact R9975
  · exact R9977
  · exact R9979
  · exact R9981
  · exact R9983
  · exact R9985
  · exact R9987
  · exact R9989
  · exact R9991
  · exact R9993
  · exact R9995
  · exact R9997
  · exact R9999
  · exact R10001
  · exact R10003
  · exact R10005
  · exact R10007
  · exact R10009
  · exact R10011
  · exact R10013
  · exact R10015
  · exact R10017
  · exact R10019
  · exact R10021
  · exact R10023
  · exact R10025
  · exact R10027
  · exact R10029
  · exact R10031
  · exact R10033
  · exact R10035
  · exact R10037
  · exact R10039
  · exact R10041
  · exact R10043
  · exact R10045
  · exact R10047
  · exact R10049
  · exact R10051
  · exact R10053
  · exact R10055
  · exact R10057
  · exact R10059
  · exact R10061
  · exact R10063
  · exact R10065
  · exact R10067
  · exact R10069
  · exact R10071
  · exact R10073
  · exact R10075
  · exact R10077
  · exact R10079
  · exact R10081
  · exact R10083
  · exact R10085
  · exact R10087
  · exact R10089
  · exact R10091
  · exact R10093
  · exact R10095
  · exact R10097
  · exact R10099
  · exact R10101
  · exact R10103
  · exact R10105
  · exact R10107
  · exact R10109
  · exact R10111
  · exact R10113
  · exact R10115
  · exact R10117
  · exact R10119
  · exact R10121
  · exact R10123
  · exact R10125
  · exact R10127
  · exact R10129
  · exact R10131
  · exact R10133
  · exact R10135
  · exact R10137
  · exact R10139
  · exact R10141
  · exact R10143
  · exact R10145
  · exact R10147
  · exact R10149
  · exact R10151
  · exact R10153
  · exact R10155
  · exact R10157
  · exact R10159
  · exact R10161
  · exact R10163
  · exact R10165
  · exact R10167
  · exact R10169
  · exact R10171
  · exact R10173
  · exact R10175
  · exact R10177
  · exact R10179
  · exact R10181
  · exact R10183
  · exact R10185
  · exact R10187
  · exact R10189
  · exact R10191
  · exact R10193
  · exact R10195
  · exact R10197
  · exact R10199
  · exact R10201
  · exact R10203
  · exact R10205
  · exact R10207
  · exact R10209
  · exact R10211
  · exact R10213
  · exact R10215
  · exact R10217
  · exact R10219
  · exact R10221
  · exact R10223
  · exact R10225
  · exact R10227
  · exact R10229
  · exact R10231
  · exact R10233
  · exact R10235
  · exact R10237
  · exact R10239
  · exact R10241
  · exact R10243
  · exact R10245
  · exact R10247
  · exact R10249
  · exact R10251
  · exact R10253
  · exact R10255
  · exact R10257
  · exact R10259
  · exact R10261
  · exact R10263
  · exact R10265
  · exact R10267
  · exact R10269
  · exact R10271
  · exact R10273
  · exact R10275
  · exact R10277
  · exact R10279
  · exact R10281
  · exact R10283
  · exact R10285
  · exact R10287
  · exact R10289
  · exact R10291
  · exact R10293
  · exact R10295
  · exact R10297
  · exact R10299
  · exact R10301
  · exact R10303
  · exact R10305
  · exact R10307
  · exact R10309
  · exact R10311
  · exact R10313
  · exact R10315
  · exact R10317
  · exact R10319
  · exact R10321
  · exact R10323
  · exact R10325
  · exact R10327
  · exact R10329
  · exact R10331
  · exact R10333
  · exact R10335
  · exact R10337
  · exact R10339
  · exact R10341
  · exact R10343
  · exact R10345
  · exact R10347
  · exact R10349
  · exact R10351
  · exact R10353
  · exact R10355
  · exact R10357
  · exact R10359
  · exact R10361
  · exact R10363
  · exact R10365
  · exact R10367
  · exact R10369
  · exact R10371
  · exact R10373
  · exact R10375
  · exact R10377
  · exact R10379
  · exact R10381
  · exact R10383
  · exact R10385
  · exact R10387
  · exact R10389
  · exact R10391
  · exact R10393
  · exact R10395
  · exact R10397
  · exact R10399
  · exact R10401
  · exact R10403
  · exact R10405
  · exact R10407
  · exact R10409
  · exact R10411
  · exact R10413
  · exact R10415
  · exact R10417
  · exact R10419
  · exact R10421
  · exact R10423
  · exact R10425
  · exact R10427
  · exact R10429
  · exact R10431
  · exact R10433
  · exact R10435
  · exact R10437
  · exact R10439
  · exact R10441
  · exact R10443
  · exact R10445
  · exact R10447
  · exact R10449
  · exact R10451
  · exact R10453
  · exact R10455
  · exact R10457
  · exact R10459
  · exact R10461
  · exact R10463
  · exact R10465
  · exact R10467
  · exact R10469
  · exact R10471
  · exact R10473
  · exact R10475
  · exact R10477
  · exact R10479
  · exact R10481
  · exact R10483
  · exact R10485
  · exact R10487
  · exact R10489
  · exact R10491
  · exact R10493
  · exact R10495
  · exact R10497
  · exact R10499
  · exact R10501
  · exact R10503
  · exact R10505
  · exact R10507
  · exact R10509
  · exact R10511
  · exact R10513
  · exact R10515
  · exact R10517
  · exact R10519
  · exact R10521
  · exact R10523
  · exact R10525
  · exact R10527
  · exact R10529
  · exact R10531
  · exact R10533
  · exact R10535
  · exact R10537
  · exact R10539
  · exact R10541
  · exact R10543
  · exact R10545
  · exact R10547
  · exact R10549
  · exact R10551
  · exact R10553
  · exact R10555
  · exact R10557
  · exact R10559
  · exact R10561
  · exact R10563
  · exact R10565
  · exact R10567
  · exact R10569
  · exact R10571
  · exact R10573
  · exact R10575
  · exact R10577
  · exact R10579
  · exact R10581
  · exact R10583
  · exact R10585
  · exact R10587
  · exact R10589
  · exact R10591
  · exact R10593
  · exact R10595
  · exact R10597
  · exact R10599
  · exact R10601
  · exact R10603
  · exact R10605
  · exact R10607
  · exact R10609
  · exact R10611
  · exact R10613
  · exact R10615
  · exact R10617
  · exact R10619
  · exact R10621
  · exact R10623
  · exact R10625
  · exact R10627
  · exact R10629
  · exact R10631
  · exact R10633
  · exact R10635
  · exact R10637
  · exact R10639
  · exact R10641
  · exact R10643
  · exact R10645
  · exact R10647
  · exact R10649
  · exact R10651
  · exact R10653
  · exact R10655
  · exact R10657
  · exact R10659
  · exact R10661
  · exact R10663
  · exact R10665
  · exact R10667
  · exact R10669
  · exact R10671
  · exact R10673
  · exact R10675
  · exact R10677
  · exact R10679
  · exact R10681
  · exact R10683
  · exact R10685
  · exact R10687
  · exact R10689
  · exact R10691
  · exact R10693
  · exact R10695
  · exact R10697
  · exact R10699
  · exact R10701
  · exact R10703
  · exact R10705
  · exact R10707
  · exact R10709
  · exact R10711
  · exact R10713
  · exact R10715
  · exact R10717
  · exact R10719
  · exact R10721
  · exact R10723
  · exact R10725
  · exact R10727
  · exact R10729
  · exact R10731
  · exact R10733
  · exact R10735
  · exact R10737
  · exact R10739
  · exact R10741
  · exact R10743
  · exact R10745
  · exact R10747
  · exact R10749
  · exact R10751
  · exact R10753
  · exact R10755
  · exact R10757
  · exact R10759
  · exact R10761
  · exact R10763
  · exact R10765
  · exact R10767
  · exact R10769
  · exact R10771
  · exact R10773
  · exact R10775
  · exact R10777
  · exact R10779
  · exact R10781
  · exact R10783
  · exact R10785
  · exact R10787
  · exact R10789
  · exact R10791
  · exact R10793
  · exact R10795
  · exact R10797
  · exact R10799
  · exact R10801
  · exact R10803
  · exact R10805
  · exact R10807
  · exact R10809
  · exact R10811
  · exact R10813
  · exact R10815
  · exact R10817
  · exact R10819
  · exact R10821
  · exact R10823
  · exact R10825
  · exact R10827
  · exact R10829
  · exact R10831
  · exact R10833
  · exact R10835
  · exact R10837
  · exact R10839
  · exact R10841
  · exact R10843
  · exact R10845
  · exact R10847
  · exact R10849
  · exact R10851
  · exact R10853
  · exact R10855
  · exact R10857
  · exact R10859
  · exact R10861
  · exact R10863
  · exact R10865
  · exact R10867
  · exact R10869
  · exact R10871
  · exact R10873
  · exact R10875
  · exact R10877
  · exact R10879
  · exact R10881
  · exact R10883
  · exact R10885
  · exact R10887
  · exact R10889
  · exact R10891
  · exact R10893
  · exact R10895
  · exact R10897
  · exact R10899
  · exact R10901
  · exact R10903
  · exact R10905
  · exact R10907
  · exact R10909
  · exact R10911
  · exact R10913
  · exact R10915
  · exact R10917
  · exact R10919
  · exact R10921
  · exact R10923
  · exact R10925
  · exact R10927
  · exact R10929
  · exact R10931
  · exact R10933
  · exact R10935
  · exact R10937
  · exact R10939
  · exact R10941
  · exact R10943
  · exact R10945
  · exact R10947
  · exact R10949
  · exact R10951
  · exact R10953
  · exact R10955
  · exact R10957
  · exact R10959
  · exact R10961
  · exact R10963
  · exact R10965
  · exact R10967
  · exact R10969
  · exact R10971
  · exact R10973
  · exact R10975
  · exact R10977
  · exact R10979
  · exact R10981
  · exact R10983
  · exact R10985
  · exact R10987
  · exact R10989
  · exact R10991
  · exact R10993
  · exact R10995
  · exact R10997
  · exact R10999
  · exact R11001
  · exact R11003
  · exact R11005
  · exact R11007
  · exact R11009
  · exact R11011
  · exact R11013
  · exact R11015
  · exact R11017
  · exact R11019
  · exact R11021
  · exact R11023
  · exact R11025
  · exact R11027
  · exact R11029
  · exact R11031
  · exact R11033
  · exact R11035
  · exact R11037
  · exact R11039
  · exact R11041
  · exact R11043
  · exact R11045
  · exact R11047
  · exact R11049
  · exact R11051
  · exact R11053
  · exact R11055
  · exact R11057
  · exact R11059
  · exact R11061
  · exact R11063
  · exact R11065
  · exact R11067
  · exact R11069
  · exact R11071
  · exact R11073
  · exact R11075
  · exact R11077
  · exact R11079
  · exact R11081
  · exact R11083
  · exact R11085
  · exact R11087
  · exact R11089
  · exact R11091
  · exact R11093
  · exact R11095
  · exact R11097
  · exact R11099
  · exact R11101
  · exact R11103
  · exact R11105
  · exact R11107
  · exact R11109
  · exact R11111
  · exact R11113
  · exact R11115
  · exact R11117
  · exact R11119
  · exact R11121
  · exact R11123
  · exact R11125
  · exact R11127
  · exact R11129
  · exact R11131
  · exact R11133
  · exact R11135
  · exact R11137
  · exact R11139
  · exact R11141
  · exact R11143
  · exact R11145
  · exact R11147
  · exact R11149
  · exact R11151
  · exact R11153
  · exact R11155
  · exact R11157
  · exact R11159
  · exact R11161
  · exact R11163
  · exact R11165
  · exact R11167
  · exact R11169
  · exact R11171
  · exact R11173
  · exact R11175
  · exact R11177
  · exact R11179
  · exact R11181
  · exact R11183
  · exact R11185
  · exact R11187
  · exact R11189
  · exact R11191
  · exact R11193
  · exact R11195
  · exact R11197
  · exact R11199

theorem C7 (j : ℕ) (h1 : 5600 ≤ j) (h2 : j ≤ 6399) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R11201
  · exact R11203
  · exact R11205
  · exact R11207
  · exact R11209
  · exact R11211
  · exact R11213
  · exact R11215
  · exact R11217
  · exact R11219
  · exact R11221
  · exact R11223
  · exact R11225
  · exact R11227
  · exact R11229
  · exact R11231
  · exact R11233
  · exact R11235
  · exact R11237
  · exact R11239
  · exact R11241
  · exact R11243
  · exact R11245
  · exact R11247
  · exact R11249
  · exact R11251
  · exact R11253
  · exact R11255
  · exact R11257
  · exact R11259
  · exact R11261
  · exact R11263
  · exact R11265
  · exact R11267
  · exact R11269
  · exact R11271
  · exact R11273
  · exact R11275
  · exact R11277
  · exact R11279
  · exact R11281
  · exact R11283
  · exact R11285
  · exact R11287
  · exact R11289
  · exact R11291
  · exact R11293
  · exact R11295
  · exact R11297
  · exact R11299
  · exact R11301
  · exact R11303
  · exact R11305
  · exact R11307
  · exact R11309
  · exact R11311
  · exact R11313
  · exact R11315
  · exact R11317
  · exact R11319
  · exact R11321
  · exact R11323
  · exact R11325
  · exact R11327
  · exact R11329
  · exact R11331
  · exact R11333
  · exact R11335
  · exact R11337
  · exact R11339
  · exact R11341
  · exact R11343
  · exact R11345
  · exact R11347
  · exact R11349
  · exact R11351
  · exact R11353
  · exact R11355
  · exact R11357
  · exact R11359
  · exact R11361
  · exact R11363
  · exact R11365
  · exact R11367
  · exact R11369
  · exact R11371
  · exact R11373
  · exact R11375
  · exact R11377
  · exact R11379
  · exact R11381
  · exact R11383
  · exact R11385
  · exact R11387
  · exact R11389
  · exact R11391
  · exact R11393
  · exact R11395
  · exact R11397
  · exact R11399
  · exact R11401
  · exact R11403
  · exact R11405
  · exact R11407
  · exact R11409
  · exact R11411
  · exact R11413
  · exact R11415
  · exact R11417
  · exact R11419
  · exact R11421
  · exact R11423
  · exact R11425
  · exact R11427
  · exact R11429
  · exact R11431
  · exact R11433
  · exact R11435
  · exact R11437
  · exact R11439
  · exact R11441
  · exact R11443
  · exact R11445
  · exact R11447
  · exact R11449
  · exact R11451
  · exact R11453
  · exact R11455
  · exact R11457
  · exact R11459
  · exact R11461
  · exact R11463
  · exact R11465
  · exact R11467
  · exact R11469
  · exact R11471
  · exact R11473
  · exact R11475
  · exact R11477
  · exact R11479
  · exact R11481
  · exact R11483
  · exact R11485
  · exact R11487
  · exact R11489
  · exact R11491
  · exact R11493
  · exact R11495
  · exact R11497
  · exact R11499
  · exact R11501
  · exact R11503
  · exact R11505
  · exact R11507
  · exact R11509
  · exact R11511
  · exact R11513
  · exact R11515
  · exact R11517
  · exact R11519
  · exact R11521
  · exact R11523
  · exact R11525
  · exact R11527
  · exact R11529
  · exact R11531
  · exact R11533
  · exact R11535
  · exact R11537
  · exact R11539
  · exact R11541
  · exact R11543
  · exact R11545
  · exact R11547
  · exact R11549
  · exact R11551
  · exact R11553
  · exact R11555
  · exact R11557
  · exact R11559
  · exact R11561
  · exact R11563
  · exact R11565
  · exact R11567
  · exact R11569
  · exact R11571
  · exact R11573
  · exact R11575
  · exact R11577
  · exact R11579
  · exact R11581
  · exact R11583
  · exact R11585
  · exact R11587
  · exact R11589
  · exact R11591
  · exact R11593
  · exact R11595
  · exact R11597
  · exact R11599
  · exact R11601
  · exact R11603
  · exact R11605
  · exact R11607
  · exact R11609
  · exact R11611
  · exact R11613
  · exact R11615
  · exact R11617
  · exact R11619
  · exact R11621
  · exact R11623
  · exact R11625
  · exact R11627
  · exact R11629
  · exact R11631
  · exact R11633
  · exact R11635
  · exact R11637
  · exact R11639
  · exact R11641
  · exact R11643
  · exact R11645
  · exact R11647
  · exact R11649
  · exact R11651
  · exact R11653
  · exact R11655
  · exact R11657
  · exact R11659
  · exact R11661
  · exact R11663
  · exact R11665
  · exact R11667
  · exact R11669
  · exact R11671
  · exact R11673
  · exact R11675
  · exact R11677
  · exact R11679
  · exact R11681
  · exact R11683
  · exact R11685
  · exact R11687
  · exact R11689
  · exact R11691
  · exact R11693
  · exact R11695
  · exact R11697
  · exact R11699
  · exact R11701
  · exact R11703
  · exact R11705
  · exact R11707
  · exact R11709
  · exact R11711
  · exact R11713
  · exact R11715
  · exact R11717
  · exact R11719
  · exact R11721
  · exact R11723
  · exact R11725
  · exact R11727
  · exact R11729
  · exact R11731
  · exact R11733
  · exact R11735
  · exact R11737
  · exact R11739
  · exact R11741
  · exact R11743
  · exact R11745
  · exact R11747
  · exact R11749
  · exact R11751
  · exact R11753
  · exact R11755
  · exact R11757
  · exact R11759
  · exact R11761
  · exact R11763
  · exact R11765
  · exact R11767
  · exact R11769
  · exact R11771
  · exact R11773
  · exact R11775
  · exact R11777
  · exact R11779
  · exact R11781
  · exact R11783
  · exact R11785
  · exact R11787
  · exact R11789
  · exact R11791
  · exact R11793
  · exact R11795
  · exact R11797
  · exact R11799
  · exact R11801
  · exact R11803
  · exact R11805
  · exact R11807
  · exact R11809
  · exact R11811
  · exact R11813
  · exact R11815
  · exact R11817
  · exact R11819
  · exact R11821
  · exact R11823
  · exact R11825
  · exact R11827
  · exact R11829
  · exact R11831
  · exact R11833
  · exact R11835
  · exact R11837
  · exact R11839
  · exact R11841
  · exact R11843
  · exact R11845
  · exact R11847
  · exact R11849
  · exact R11851
  · exact R11853
  · exact R11855
  · exact R11857
  · exact R11859
  · exact R11861
  · exact R11863
  · exact R11865
  · exact R11867
  · exact R11869
  · exact R11871
  · exact R11873
  · exact R11875
  · exact R11877
  · exact R11879
  · exact R11881
  · exact R11883
  · exact R11885
  · exact R11887
  · exact R11889
  · exact R11891
  · exact R11893
  · exact R11895
  · exact R11897
  · exact R11899
  · exact R11901
  · exact R11903
  · exact R11905
  · exact R11907
  · exact R11909
  · exact R11911
  · exact R11913
  · exact R11915
  · exact R11917
  · exact R11919
  · exact R11921
  · exact R11923
  · exact R11925
  · exact R11927
  · exact R11929
  · exact R11931
  · exact R11933
  · exact R11935
  · exact R11937
  · exact R11939
  · exact R11941
  · exact R11943
  · exact R11945
  · exact R11947
  · exact R11949
  · exact R11951
  · exact R11953
  · exact R11955
  · exact R11957
  · exact R11959
  · exact R11961
  · exact R11963
  · exact R11965
  · exact R11967
  · exact R11969
  · exact R11971
  · exact R11973
  · exact R11975
  · exact R11977
  · exact R11979
  · exact R11981
  · exact R11983
  · exact R11985
  · exact R11987
  · exact R11989
  · exact R11991
  · exact R11993
  · exact R11995
  · exact R11997
  · exact R11999
  · exact R12001
  · exact R12003
  · exact R12005
  · exact R12007
  · exact R12009
  · exact R12011
  · exact R12013
  · exact R12015
  · exact R12017
  · exact R12019
  · exact R12021
  · exact R12023
  · exact R12025
  · exact R12027
  · exact R12029
  · exact R12031
  · exact R12033
  · exact R12035
  · exact R12037
  · exact R12039
  · exact R12041
  · exact R12043
  · exact R12045
  · exact R12047
  · exact R12049
  · exact R12051
  · exact R12053
  · exact R12055
  · exact R12057
  · exact R12059
  · exact R12061
  · exact R12063
  · exact R12065
  · exact R12067
  · exact R12069
  · exact R12071
  · exact R12073
  · exact R12075
  · exact R12077
  · exact R12079
  · exact R12081
  · exact R12083
  · exact R12085
  · exact R12087
  · exact R12089
  · exact R12091
  · exact R12093
  · exact R12095
  · exact R12097
  · exact R12099
  · exact R12101
  · exact R12103
  · exact R12105
  · exact R12107
  · exact R12109
  · exact R12111
  · exact R12113
  · exact R12115
  · exact R12117
  · exact R12119
  · exact R12121
  · exact R12123
  · exact R12125
  · exact R12127
  · exact R12129
  · exact R12131
  · exact R12133
  · exact R12135
  · exact R12137
  · exact R12139
  · exact R12141
  · exact R12143
  · exact R12145
  · exact R12147
  · exact R12149
  · exact R12151
  · exact R12153
  · exact R12155
  · exact R12157
  · exact R12159
  · exact R12161
  · exact R12163
  · exact R12165
  · exact R12167
  · exact R12169
  · exact R12171
  · exact R12173
  · exact R12175
  · exact R12177
  · exact R12179
  · exact R12181
  · exact R12183
  · exact R12185
  · exact R12187
  · exact R12189
  · exact R12191
  · exact R12193
  · exact R12195
  · exact R12197
  · exact R12199
  · exact R12201
  · exact R12203
  · exact R12205
  · exact R12207
  · exact R12209
  · exact R12211
  · exact R12213
  · exact R12215
  · exact R12217
  · exact R12219
  · exact R12221
  · exact R12223
  · exact R12225
  · exact R12227
  · exact R12229
  · exact R12231
  · exact R12233
  · exact R12235
  · exact R12237
  · exact R12239
  · exact R12241
  · exact R12243
  · exact R12245
  · exact R12247
  · exact R12249
  · exact R12251
  · exact R12253
  · exact R12255
  · exact R12257
  · exact R12259
  · exact R12261
  · exact R12263
  · exact R12265
  · exact R12267
  · exact R12269
  · exact R12271
  · exact R12273
  · exact R12275
  · exact R12277
  · exact R12279
  · exact R12281
  · exact R12283
  · exact R12285
  · exact R12287
  · exact R12289
  · exact R12291
  · exact R12293
  · exact R12295
  · exact R12297
  · exact R12299
  · exact R12301
  · exact R12303
  · exact R12305
  · exact R12307
  · exact R12309
  · exact R12311
  · exact R12313
  · exact R12315
  · exact R12317
  · exact R12319
  · exact R12321
  · exact R12323
  · exact R12325
  · exact R12327
  · exact R12329
  · exact R12331
  · exact R12333
  · exact R12335
  · exact R12337
  · exact R12339
  · exact R12341
  · exact R12343
  · exact R12345
  · exact R12347
  · exact R12349
  · exact R12351
  · exact R12353
  · exact R12355
  · exact R12357
  · exact R12359
  · exact R12361
  · exact R12363
  · exact R12365
  · exact R12367
  · exact R12369
  · exact R12371
  · exact R12373
  · exact R12375
  · exact R12377
  · exact R12379
  · exact R12381
  · exact R12383
  · exact R12385
  · exact R12387
  · exact R12389
  · exact R12391
  · exact R12393
  · exact R12395
  · exact R12397
  · exact R12399
  · exact R12401
  · exact R12403
  · exact R12405
  · exact R12407
  · exact R12409
  · exact R12411
  · exact R12413
  · exact R12415
  · exact R12417
  · exact R12419
  · exact R12421
  · exact R12423
  · exact R12425
  · exact R12427
  · exact R12429
  · exact R12431
  · exact R12433
  · exact R12435
  · exact R12437
  · exact R12439
  · exact R12441
  · exact R12443
  · exact R12445
  · exact R12447
  · exact R12449
  · exact R12451
  · exact R12453
  · exact R12455
  · exact R12457
  · exact R12459
  · exact R12461
  · exact R12463
  · exact R12465
  · exact R12467
  · exact R12469
  · exact R12471
  · exact R12473
  · exact R12475
  · exact R12477
  · exact R12479
  · exact R12481
  · exact R12483
  · exact R12485
  · exact R12487
  · exact R12489
  · exact R12491
  · exact R12493
  · exact R12495
  · exact R12497
  · exact R12499
  · exact R12501
  · exact R12503
  · exact R12505
  · exact R12507
  · exact R12509
  · exact R12511
  · exact R12513
  · exact R12515
  · exact R12517
  · exact R12519
  · exact R12521
  · exact R12523
  · exact R12525
  · exact R12527
  · exact R12529
  · exact R12531
  · exact R12533
  · exact R12535
  · exact R12537
  · exact R12539
  · exact R12541
  · exact R12543
  · exact R12545
  · exact R12547
  · exact R12549
  · exact R12551
  · exact R12553
  · exact R12555
  · exact R12557
  · exact R12559
  · exact R12561
  · exact R12563
  · exact R12565
  · exact R12567
  · exact R12569
  · exact R12571
  · exact R12573
  · exact R12575
  · exact R12577
  · exact R12579
  · exact R12581
  · exact R12583
  · exact R12585
  · exact R12587
  · exact R12589
  · exact R12591
  · exact R12593
  · exact R12595
  · exact R12597
  · exact R12599
  · exact R12601
  · exact R12603
  · exact R12605
  · exact R12607
  · exact R12609
  · exact R12611
  · exact R12613
  · exact R12615
  · exact R12617
  · exact R12619
  · exact R12621
  · exact R12623
  · exact R12625
  · exact R12627
  · exact R12629
  · exact R12631
  · exact R12633
  · exact R12635
  · exact R12637
  · exact R12639
  · exact R12641
  · exact R12643
  · exact R12645
  · exact R12647
  · exact R12649
  · exact R12651
  · exact R12653
  · exact R12655
  · exact R12657
  · exact R12659
  · exact R12661
  · exact R12663
  · exact R12665
  · exact R12667
  · exact R12669
  · exact R12671
  · exact R12673
  · exact R12675
  · exact R12677
  · exact R12679
  · exact R12681
  · exact R12683
  · exact R12685
  · exact R12687
  · exact R12689
  · exact R12691
  · exact R12693
  · exact R12695
  · exact R12697
  · exact R12699
  · exact R12701
  · exact R12703
  · exact R12705
  · exact R12707
  · exact R12709
  · exact R12711
  · exact R12713
  · exact R12715
  · exact R12717
  · exact R12719
  · exact R12721
  · exact R12723
  · exact R12725
  · exact R12727
  · exact R12729
  · exact R12731
  · exact R12733
  · exact R12735
  · exact R12737
  · exact R12739
  · exact R12741
  · exact R12743
  · exact R12745
  · exact R12747
  · exact R12749
  · exact R12751
  · exact R12753
  · exact R12755
  · exact R12757
  · exact R12759
  · exact R12761
  · exact R12763
  · exact R12765
  · exact R12767
  · exact R12769
  · exact R12771
  · exact R12773
  · exact R12775
  · exact R12777
  · exact R12779
  · exact R12781
  · exact R12783
  · exact R12785
  · exact R12787
  · exact R12789
  · exact R12791
  · exact R12793
  · exact R12795
  · exact R12797
  · exact R12799

theorem C8 (j : ℕ) (h1 : 6400 ≤ j) (h2 : j ≤ 6411) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R12801
  · exact R12803
  · exact R12805
  · exact R12807
  · exact R12809
  · exact R12811
  · exact R12813
  · exact R12815
  · exact R12817
  · exact R12819
  · exact R12821
  · exact R12823

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 12824) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  have hj : j ≤ 6411 := by omega
  rcases Nat.lt_or_ge j 800 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 1600 with h1 | h1
  · exact C1 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 2400 with h2 | h2
  · exact C2 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 3200 with h3 | h3
  · exact C3 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 4000 with h4 | h4
  · exact C4 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 4800 with h5 | h5
  · exact C5 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 5600 with h6 | h6
  · exact C6 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 6400 with h7 | h7
  · exact C7 j (by omega) (by omega)
  exact C8 j (by omega) (by omega)
