-- Prove2me | solution 1 for syracuse_descends_range_263822_267822
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:08.785716+00:00
-- url     : https://prove2.me/submissions/fe24eece-f895-4eb4-9a61-2eaf607c2dc3

import Mathlib
import Definitions.Def_syracuseStep

set_option maxHeartbeats 1000000

open Nat

/-- Half of all odd numbers descend in a single Syracuse step, uniformly. -/
theorem step_lt_of_one_mod_four (m : ℕ) (h1 : 1 < m) (h4 : m % 4 = 1) : syracuseStep m < m := by
  have hne : 3 * m + 1 ≠ 0 := by omega
  have hdvd : (2:ℕ) ^ 2 ∣ 3 * m + 1 := by
    have : (4:ℕ) ∣ 3 * m + 1 := by omega
    simpa using this
  have hle : 2 ≤ (3 * m + 1).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
  have hpow : (2:ℕ) ^ 2 ≤ 2 ^ ((3 * m + 1).factorization 2) :=
    Nat.pow_le_pow_right (by norm_num) hle
  have h1' : syracuseStep m ≤ (3 * m + 1) / 2 ^ 2 := by
    show ordCompl[2] (3 * m + 1) ≤ _
    exact Nat.div_le_div_left hpow (by positivity)
  have h2' : (3 * m + 1) / 2 ^ 2 < m := by
    apply Nat.div_lt_of_lt_mul
    omega
  omega

/-- `Blo L x` : some Syracuse iterate of `x` drops below `L`. -/
abbrev Blo (L x : ℕ) : Prop := ∃ t : ℕ, syracuseStep^[t] x < L

theorem bbase {L x y : ℕ} (h : syracuseStep x = y) (hy : y < L) : Blo L x :=
  ⟨1, by rw [Function.iterate_one, h]; exact hy⟩

theorem bstep {L x y : ℕ} (h : syracuseStep x = y) (hy : Blo L y) : Blo L x := by
  obtain ⟨t, ht⟩ := hy
  exact ⟨t + 1, by rw [Function.iterate_add_apply, Function.iterate_one, h]; exact ht⟩

theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]


theorem B1015861 : Blo 263822 1015861 := bbase (se 5 (by rfl) ⟨47618, by rfl⟩ : syracuseStep 1015861 = 95237) (by norm_num)
theorem B753877 : Blo 263822 753877 := bbase (se 7 (by rfl) ⟨8834, by rfl⟩ : syracuseStep 753877 = 17669) (by norm_num)
theorem B426325 : Blo 263822 426325 := bbase (se 10 (by rfl) ⟨624, by rfl⟩ : syracuseStep 426325 = 1249) (by norm_num)
theorem B1016165 : Blo 263822 1016165 := bbase (se 4 (by rfl) ⟨95265, by rfl⟩ : syracuseStep 1016165 = 190531) (by norm_num)
theorem B1507733 : Blo 263822 1507733 := bbase (se 6 (by rfl) ⟨35337, by rfl⟩ : syracuseStep 1507733 = 70675) (by norm_num)
theorem B721349 : Blo 263822 721349 := bbase (se 4 (by rfl) ⟨67626, by rfl⟩ : syracuseStep 721349 = 135253) (by norm_num)
theorem B721477 : Blo 263822 721477 := bbase (se 4 (by rfl) ⟨67638, by rfl⟩ : syracuseStep 721477 = 135277) (by norm_num)
theorem B950885 : Blo 263822 950885 := bbase (se 4 (by rfl) ⟨89145, by rfl⟩ : syracuseStep 950885 = 178291) (by norm_num)
theorem B852725 : Blo 263822 852725 := bbase (se 5 (by rfl) ⟨39971, by rfl⟩ : syracuseStep 852725 = 79943) (by norm_num)
theorem B426773 : Blo 263822 426773 := bbase (se 6 (by rfl) ⟨10002, by rfl⟩ : syracuseStep 426773 = 20005) (by norm_num)
theorem B721813 : Blo 263822 721813 := bbase (se 6 (by rfl) ⟨16917, by rfl⟩ : syracuseStep 721813 = 33835) (by norm_num)
theorem B1344437 : Blo 263822 1344437 := bbase (se 5 (by rfl) ⟨63020, by rfl⟩ : syracuseStep 1344437 = 126041) (by norm_num)
theorem B362165 : Blo 263822 362165 := bbase (se 5 (by rfl) ⟨16976, by rfl⟩ : syracuseStep 362165 = 33953) (by norm_num)
theorem B755381 : Blo 263822 755381 := bbase (se 5 (by rfl) ⟨35408, by rfl⟩ : syracuseStep 755381 = 70817) (by norm_num)
theorem B296833 : Blo 263822 296833 := bbase (se 2 (by rfl) ⟨111312, by rfl⟩ : syracuseStep 296833 = 222625) (by norm_num)
theorem B1902485 : Blo 263822 1902485 := bbase (se 6 (by rfl) ⟨44589, by rfl⟩ : syracuseStep 1902485 = 89179) (by norm_num)
theorem B296869 : Blo 263822 296869 := bbase (se 4 (by rfl) ⟨27831, by rfl⟩ : syracuseStep 296869 = 55663) (by norm_num)
theorem B296905 : Blo 263822 296905 := bbase (se 2 (by rfl) ⟨111339, by rfl⟩ : syracuseStep 296905 = 222679) (by norm_num)
theorem B296941 : Blo 263822 296941 := bbase (se 3 (by rfl) ⟨55676, by rfl⟩ : syracuseStep 296941 = 111353) (by norm_num)
theorem B296977 : Blo 263822 296977 := bbase (se 2 (by rfl) ⟨111366, by rfl⟩ : syracuseStep 296977 = 222733) (by norm_num)
theorem B297013 : Blo 263822 297013 := bbase (se 5 (by rfl) ⟨13922, by rfl⟩ : syracuseStep 297013 = 27845) (by norm_num)
theorem B297049 : Blo 263822 297049 := bbase (se 2 (by rfl) ⟨111393, by rfl⟩ : syracuseStep 297049 = 222787) (by norm_num)
theorem B297085 : Blo 263822 297085 := bbase (se 3 (by rfl) ⟨55703, by rfl⟩ : syracuseStep 297085 = 111407) (by norm_num)
theorem B297121 : Blo 263822 297121 := bbase (se 2 (by rfl) ⟨111420, by rfl⟩ : syracuseStep 297121 = 222841) (by norm_num)
theorem B297157 : Blo 263822 297157 := bbase (se 4 (by rfl) ⟨27858, by rfl⟩ : syracuseStep 297157 = 55717) (by norm_num)
theorem B1345733 : Blo 263822 1345733 := bbase (se 4 (by rfl) ⟨126162, by rfl⟩ : syracuseStep 1345733 = 252325) (by norm_num)
theorem B297193 : Blo 263822 297193 := bbase (se 2 (by rfl) ⟨111447, by rfl⟩ : syracuseStep 297193 = 222895) (by norm_num)
theorem B428285 : Blo 263822 428285 := bbase (se 3 (by rfl) ⟨80303, by rfl⟩ : syracuseStep 428285 = 160607) (by norm_num)
theorem B297229 : Blo 263822 297229 := bbase (se 3 (by rfl) ⟨55730, by rfl⟩ : syracuseStep 297229 = 111461) (by norm_num)
theorem B297265 : Blo 263822 297265 := bbase (se 2 (by rfl) ⟨111474, by rfl⟩ : syracuseStep 297265 = 222949) (by norm_num)
theorem B297301 : Blo 263822 297301 := bbase (se 10 (by rfl) ⟨435, by rfl⟩ : syracuseStep 297301 = 871) (by norm_num)
theorem B297337 : Blo 263822 297337 := bbase (se 2 (by rfl) ⟨111501, by rfl⟩ : syracuseStep 297337 = 223003) (by norm_num)
theorem B428413 : Blo 263822 428413 := bbase (se 3 (by rfl) ⟨80327, by rfl⟩ : syracuseStep 428413 = 160655) (by norm_num)
theorem B297373 : Blo 263822 297373 := bbase (se 3 (by rfl) ⟨55757, by rfl⟩ : syracuseStep 297373 = 111515) (by norm_num)
theorem B297409 : Blo 263822 297409 := bbase (se 2 (by rfl) ⟨111528, by rfl⟩ : syracuseStep 297409 = 223057) (by norm_num)
theorem B1706453 : Blo 263822 1706453 := bbase (se 7 (by rfl) ⟨19997, by rfl⟩ : syracuseStep 1706453 = 39995) (by norm_num)
theorem B395741 : Blo 263822 395741 := bbase (se 3 (by rfl) ⟨74201, by rfl⟩ : syracuseStep 395741 = 148403) (by norm_num)
theorem B297445 : Blo 263822 297445 := bbase (se 4 (by rfl) ⟨27885, by rfl⟩ : syracuseStep 297445 = 55771) (by norm_num)
theorem B395765 : Blo 263822 395765 := bbase (se 5 (by rfl) ⟨18551, by rfl⟩ : syracuseStep 395765 = 37103) (by norm_num)
theorem B297481 : Blo 263822 297481 := bbase (se 2 (by rfl) ⟨111555, by rfl⟩ : syracuseStep 297481 = 223111) (by norm_num)
theorem B395789 : Blo 263822 395789 := bbase (se 3 (by rfl) ⟨74210, by rfl⟩ : syracuseStep 395789 = 148421) (by norm_num)
theorem B395813 : Blo 263822 395813 := bbase (se 4 (by rfl) ⟨37107, by rfl⟩ : syracuseStep 395813 = 74215) (by norm_num)
theorem B1280549 : Blo 263822 1280549 := bbase (se 4 (by rfl) ⟨120051, by rfl⟩ : syracuseStep 1280549 = 240103) (by norm_num)
theorem B297517 : Blo 263822 297517 := bbase (se 3 (by rfl) ⟨55784, by rfl⟩ : syracuseStep 297517 = 111569) (by norm_num)
theorem B1509941 : Blo 263822 1509941 := bbase (se 5 (by rfl) ⟨70778, by rfl⟩ : syracuseStep 1509941 = 141557) (by norm_num)
theorem B395837 : Blo 263822 395837 := bbase (se 3 (by rfl) ⟨74219, by rfl⟩ : syracuseStep 395837 = 148439) (by norm_num)
theorem B297553 : Blo 263822 297553 := bbase (se 2 (by rfl) ⟨111582, by rfl⟩ : syracuseStep 297553 = 223165) (by norm_num)
theorem B395861 : Blo 263822 395861 := bbase (se 8 (by rfl) ⟨2319, by rfl⟩ : syracuseStep 395861 = 4639) (by norm_num)
theorem B395885 : Blo 263822 395885 := bbase (se 3 (by rfl) ⟨74228, by rfl⟩ : syracuseStep 395885 = 148457) (by norm_num)
theorem B297589 : Blo 263822 297589 := bbase (se 5 (by rfl) ⟨13949, by rfl⟩ : syracuseStep 297589 = 27899) (by norm_num)
theorem B395909 : Blo 263822 395909 := bbase (se 4 (by rfl) ⟨37116, by rfl⟩ : syracuseStep 395909 = 74233) (by norm_num)
theorem B297625 : Blo 263822 297625 := bbase (se 2 (by rfl) ⟨111609, by rfl⟩ : syracuseStep 297625 = 223219) (by norm_num)
theorem B395933 : Blo 263822 395933 := bbase (se 3 (by rfl) ⟨74237, by rfl⟩ : syracuseStep 395933 = 148475) (by norm_num)
theorem B395957 : Blo 263822 395957 := bbase (se 5 (by rfl) ⟨18560, by rfl⟩ : syracuseStep 395957 = 37121) (by norm_num)
theorem B1215157 : Blo 263822 1215157 := bbase (se 5 (by rfl) ⟨56960, by rfl⟩ : syracuseStep 1215157 = 113921) (by norm_num)
theorem B297661 : Blo 263822 297661 := bbase (se 3 (by rfl) ⟨55811, by rfl⟩ : syracuseStep 297661 = 111623) (by norm_num)
theorem B854725 : Blo 263822 854725 := bbase (se 4 (by rfl) ⟨80130, by rfl⟩ : syracuseStep 854725 = 160261) (by norm_num)
theorem B395981 : Blo 263822 395981 := bbase (se 3 (by rfl) ⟨74246, by rfl⟩ : syracuseStep 395981 = 148493) (by norm_num)
theorem B297697 : Blo 263822 297697 := bbase (se 2 (by rfl) ⟨111636, by rfl⟩ : syracuseStep 297697 = 223273) (by norm_num)
theorem B396005 : Blo 263822 396005 := bbase (se 4 (by rfl) ⟨37125, by rfl⟩ : syracuseStep 396005 = 74251) (by norm_num)
theorem B396029 : Blo 263822 396029 := bbase (se 3 (by rfl) ⟨74255, by rfl⟩ : syracuseStep 396029 = 148511) (by norm_num)
theorem B297733 : Blo 263822 297733 := bbase (se 4 (by rfl) ⟨27912, by rfl⟩ : syracuseStep 297733 = 55825) (by norm_num)
theorem B396053 : Blo 263822 396053 := bbase (se 6 (by rfl) ⟨9282, by rfl⟩ : syracuseStep 396053 = 18565) (by norm_num)
theorem B297769 : Blo 263822 297769 := bbase (se 2 (by rfl) ⟨111663, by rfl⟩ : syracuseStep 297769 = 223327) (by norm_num)
theorem B396077 : Blo 263822 396077 := bbase (se 3 (by rfl) ⟨74264, by rfl⟩ : syracuseStep 396077 = 148529) (by norm_num)
theorem B396101 : Blo 263822 396101 := bbase (se 4 (by rfl) ⟨37134, by rfl⟩ : syracuseStep 396101 = 74269) (by norm_num)
theorem B297805 : Blo 263822 297805 := bbase (se 3 (by rfl) ⟨55838, by rfl⟩ : syracuseStep 297805 = 111677) (by norm_num)
theorem B396125 : Blo 263822 396125 := bbase (se 3 (by rfl) ⟨74273, by rfl⟩ : syracuseStep 396125 = 148547) (by norm_num)
theorem B297841 : Blo 263822 297841 := bbase (se 2 (by rfl) ⟨111690, by rfl⟩ : syracuseStep 297841 = 223381) (by norm_num)
theorem B396149 : Blo 263822 396149 := bbase (se 5 (by rfl) ⟨18569, by rfl⟩ : syracuseStep 396149 = 37139) (by norm_num)
theorem B396173 : Blo 263822 396173 := bbase (se 3 (by rfl) ⟨74282, by rfl⟩ : syracuseStep 396173 = 148565) (by norm_num)
theorem B297877 : Blo 263822 297877 := bbase (se 6 (by rfl) ⟨6981, by rfl⟩ : syracuseStep 297877 = 13963) (by norm_num)
theorem B396197 : Blo 263822 396197 := bbase (se 4 (by rfl) ⟨37143, by rfl⟩ : syracuseStep 396197 = 74287) (by norm_num)
theorem B297913 : Blo 263822 297913 := bbase (se 2 (by rfl) ⟨111717, by rfl⟩ : syracuseStep 297913 = 223435) (by norm_num)
theorem B396221 : Blo 263822 396221 := bbase (se 3 (by rfl) ⟨74291, by rfl⟩ : syracuseStep 396221 = 148583) (by norm_num)
theorem B396245 : Blo 263822 396245 := bbase (se 7 (by rfl) ⟨4643, by rfl⟩ : syracuseStep 396245 = 9287) (by norm_num)
theorem B297949 : Blo 263822 297949 := bbase (se 3 (by rfl) ⟨55865, by rfl⟩ : syracuseStep 297949 = 111731) (by norm_num)
theorem B396269 : Blo 263822 396269 := bbase (se 3 (by rfl) ⟨74300, by rfl⟩ : syracuseStep 396269 = 148601) (by norm_num)
theorem B297985 : Blo 263822 297985 := bbase (se 2 (by rfl) ⟨111744, by rfl⟩ : syracuseStep 297985 = 223489) (by norm_num)
theorem B396293 : Blo 263822 396293 := bbase (se 4 (by rfl) ⟨37152, by rfl⟩ : syracuseStep 396293 = 74305) (by norm_num)
theorem B396317 : Blo 263822 396317 := bbase (se 3 (by rfl) ⟨74309, by rfl⟩ : syracuseStep 396317 = 148619) (by norm_num)
theorem B298021 : Blo 263822 298021 := bbase (se 4 (by rfl) ⟨27939, by rfl⟩ : syracuseStep 298021 = 55879) (by norm_num)
theorem B396341 : Blo 263822 396341 := bbase (se 5 (by rfl) ⟨18578, by rfl⟩ : syracuseStep 396341 = 37157) (by norm_num)
theorem B298057 : Blo 263822 298057 := bbase (se 2 (by rfl) ⟨111771, by rfl⟩ : syracuseStep 298057 = 223543) (by norm_num)
theorem B396365 : Blo 263822 396365 := bbase (se 3 (by rfl) ⟨74318, by rfl⟩ : syracuseStep 396365 = 148637) (by norm_num)
theorem B396389 : Blo 263822 396389 := bbase (se 4 (by rfl) ⟨37161, by rfl⟩ : syracuseStep 396389 = 74323) (by norm_num)
theorem B298093 : Blo 263822 298093 := bbase (se 3 (by rfl) ⟨55892, by rfl⟩ : syracuseStep 298093 = 111785) (by norm_num)
theorem B396413 : Blo 263822 396413 := bbase (se 3 (by rfl) ⟨74327, by rfl⟩ : syracuseStep 396413 = 148655) (by norm_num)
theorem B298129 : Blo 263822 298129 := bbase (se 2 (by rfl) ⟨111798, by rfl⟩ : syracuseStep 298129 = 223597) (by norm_num)
theorem B396437 : Blo 263822 396437 := bbase (se 6 (by rfl) ⟨9291, by rfl⟩ : syracuseStep 396437 = 18583) (by norm_num)
theorem B396461 : Blo 263822 396461 := bbase (se 3 (by rfl) ⟨74336, by rfl⟩ : syracuseStep 396461 = 148673) (by norm_num)
theorem B298165 : Blo 263822 298165 := bbase (se 5 (by rfl) ⟨13976, by rfl⟩ : syracuseStep 298165 = 27953) (by norm_num)
theorem B396485 : Blo 263822 396485 := bbase (se 4 (by rfl) ⟨37170, by rfl⟩ : syracuseStep 396485 = 74341) (by norm_num)
theorem B298201 : Blo 263822 298201 := bbase (se 2 (by rfl) ⟨111825, by rfl⟩ : syracuseStep 298201 = 223651) (by norm_num)
theorem B396509 : Blo 263822 396509 := bbase (se 3 (by rfl) ⟨74345, by rfl⟩ : syracuseStep 396509 = 148691) (by norm_num)
theorem B756965 : Blo 263822 756965 := bbase (se 4 (by rfl) ⟨70965, by rfl⟩ : syracuseStep 756965 = 141931) (by norm_num)
theorem B396533 : Blo 263822 396533 := bbase (se 5 (by rfl) ⟨18587, by rfl⟩ : syracuseStep 396533 = 37175) (by norm_num)
theorem B298237 : Blo 263822 298237 := bbase (se 3 (by rfl) ⟨55919, by rfl⟩ : syracuseStep 298237 = 111839) (by norm_num)
theorem B396557 : Blo 263822 396557 := bbase (se 3 (by rfl) ⟨74354, by rfl⟩ : syracuseStep 396557 = 148709) (by norm_num)
theorem B298273 : Blo 263822 298273 := bbase (se 2 (by rfl) ⟨111852, by rfl⟩ : syracuseStep 298273 = 223705) (by norm_num)
theorem B396581 : Blo 263822 396581 := bbase (se 4 (by rfl) ⟨37179, by rfl⟩ : syracuseStep 396581 = 74359) (by norm_num)
theorem B953653 : Blo 263822 953653 := bbase (se 5 (by rfl) ⟨44702, by rfl⟩ : syracuseStep 953653 = 89405) (by norm_num)
theorem B396605 : Blo 263822 396605 := bbase (se 3 (by rfl) ⟨74363, by rfl⟩ : syracuseStep 396605 = 148727) (by norm_num)
theorem B298309 : Blo 263822 298309 := bbase (se 4 (by rfl) ⟨27966, by rfl⟩ : syracuseStep 298309 = 55933) (by norm_num)
theorem B396629 : Blo 263822 396629 := bbase (se 11 (by rfl) ⟨290, by rfl⟩ : syracuseStep 396629 = 581) (by norm_num)
theorem B298345 : Blo 263822 298345 := bbase (se 2 (by rfl) ⟨111879, by rfl⟩ : syracuseStep 298345 = 223759) (by norm_num)
theorem B396653 : Blo 263822 396653 := bbase (se 3 (by rfl) ⟨74372, by rfl⟩ : syracuseStep 396653 = 148745) (by norm_num)
theorem B396677 : Blo 263822 396677 := bbase (se 4 (by rfl) ⟨37188, by rfl⟩ : syracuseStep 396677 = 74377) (by norm_num)
theorem B298381 : Blo 263822 298381 := bbase (se 3 (by rfl) ⟨55946, by rfl⟩ : syracuseStep 298381 = 111893) (by norm_num)
theorem B396701 : Blo 263822 396701 := bbase (se 3 (by rfl) ⟨74381, by rfl⟩ : syracuseStep 396701 = 148763) (by norm_num)
theorem B298417 : Blo 263822 298417 := bbase (se 2 (by rfl) ⟨111906, by rfl⟩ : syracuseStep 298417 = 223813) (by norm_num)
theorem B396725 : Blo 263822 396725 := bbase (se 5 (by rfl) ⟨18596, by rfl⟩ : syracuseStep 396725 = 37193) (by norm_num)
theorem B396749 : Blo 263822 396749 := bbase (se 3 (by rfl) ⟨74390, by rfl⟩ : syracuseStep 396749 = 148781) (by norm_num)
theorem B298453 : Blo 263822 298453 := bbase (se 7 (by rfl) ⟨3497, by rfl⟩ : syracuseStep 298453 = 6995) (by norm_num)
theorem B1347029 : Blo 263822 1347029 := bbase (se 7 (by rfl) ⟨15785, by rfl⟩ : syracuseStep 1347029 = 31571) (by norm_num)
theorem B396773 : Blo 263822 396773 := bbase (se 4 (by rfl) ⟨37197, by rfl⟩ : syracuseStep 396773 = 74395) (by norm_num)
theorem B298489 : Blo 263822 298489 := bbase (se 2 (by rfl) ⟨111933, by rfl⟩ : syracuseStep 298489 = 223867) (by norm_num)
theorem B396797 : Blo 263822 396797 := bbase (se 3 (by rfl) ⟨74399, by rfl⟩ : syracuseStep 396797 = 148799) (by norm_num)
theorem B396821 : Blo 263822 396821 := bbase (se 6 (by rfl) ⟨9300, by rfl⟩ : syracuseStep 396821 = 18601) (by norm_num)
theorem B298525 : Blo 263822 298525 := bbase (se 3 (by rfl) ⟨55973, by rfl⟩ : syracuseStep 298525 = 111947) (by norm_num)
theorem B396845 : Blo 263822 396845 := bbase (se 3 (by rfl) ⟨74408, by rfl⟩ : syracuseStep 396845 = 148817) (by norm_num)
theorem B298561 : Blo 263822 298561 := bbase (se 2 (by rfl) ⟨111960, by rfl⟩ : syracuseStep 298561 = 223921) (by norm_num)
theorem B396869 : Blo 263822 396869 := bbase (se 4 (by rfl) ⟨37206, by rfl⟩ : syracuseStep 396869 = 74413) (by norm_num)
theorem B396893 : Blo 263822 396893 := bbase (se 3 (by rfl) ⟨74417, by rfl⟩ : syracuseStep 396893 = 148835) (by norm_num)
theorem B298597 : Blo 263822 298597 := bbase (se 4 (by rfl) ⟨27993, by rfl⟩ : syracuseStep 298597 = 55987) (by norm_num)
theorem B396917 : Blo 263822 396917 := bbase (se 5 (by rfl) ⟨18605, by rfl⟩ : syracuseStep 396917 = 37211) (by norm_num)
theorem B298633 : Blo 263822 298633 := bbase (se 2 (by rfl) ⟨111987, by rfl⟩ : syracuseStep 298633 = 223975) (by norm_num)
theorem B396941 : Blo 263822 396941 := bbase (se 3 (by rfl) ⟨74426, by rfl⟩ : syracuseStep 396941 = 148853) (by norm_num)
theorem B396965 : Blo 263822 396965 := bbase (se 4 (by rfl) ⟨37215, by rfl⟩ : syracuseStep 396965 = 74431) (by norm_num)
theorem B298669 : Blo 263822 298669 := bbase (se 3 (by rfl) ⟨56000, by rfl⟩ : syracuseStep 298669 = 112001) (by norm_num)
theorem B1904309 : Blo 263822 1904309 := bbase (se 5 (by rfl) ⟨89264, by rfl⟩ : syracuseStep 1904309 = 178529) (by norm_num)
theorem B396989 : Blo 263822 396989 := bbase (se 3 (by rfl) ⟨74435, by rfl⟩ : syracuseStep 396989 = 148871) (by norm_num)
theorem B298705 : Blo 263822 298705 := bbase (se 2 (by rfl) ⟨112014, by rfl⟩ : syracuseStep 298705 = 224029) (by norm_num)
theorem B593621 : Blo 263822 593621 := bbase (se 7 (by rfl) ⟨6956, by rfl⟩ : syracuseStep 593621 = 13913) (by norm_num)
theorem B397013 : Blo 263822 397013 := bbase (se 7 (by rfl) ⟨4652, by rfl⟩ : syracuseStep 397013 = 9305) (by norm_num)
theorem B397037 : Blo 263822 397037 := bbase (se 3 (by rfl) ⟨74444, by rfl⟩ : syracuseStep 397037 = 148889) (by norm_num)
theorem B298741 : Blo 263822 298741 := bbase (se 5 (by rfl) ⟨14003, by rfl⟩ : syracuseStep 298741 = 28007) (by norm_num)
theorem B397061 : Blo 263822 397061 := bbase (se 4 (by rfl) ⟨37224, by rfl⟩ : syracuseStep 397061 = 74449) (by norm_num)
theorem B298777 : Blo 263822 298777 := bbase (se 2 (by rfl) ⟨112041, by rfl⟩ : syracuseStep 298777 = 224083) (by norm_num)
theorem B593693 : Blo 263822 593693 := bbase (se 3 (by rfl) ⟨111317, by rfl⟩ : syracuseStep 593693 = 222635) (by norm_num)
theorem B397085 : Blo 263822 397085 := bbase (se 3 (by rfl) ⟨74453, by rfl⟩ : syracuseStep 397085 = 148907) (by norm_num)
theorem B397109 : Blo 263822 397109 := bbase (se 5 (by rfl) ⟨18614, by rfl⟩ : syracuseStep 397109 = 37229) (by norm_num)
theorem B298813 : Blo 263822 298813 := bbase (se 3 (by rfl) ⟨56027, by rfl⟩ : syracuseStep 298813 = 112055) (by norm_num)
theorem B397133 : Blo 263822 397133 := bbase (se 3 (by rfl) ⟨74462, by rfl⟩ : syracuseStep 397133 = 148925) (by norm_num)
theorem B298849 : Blo 263822 298849 := bbase (se 2 (by rfl) ⟨112068, by rfl⟩ : syracuseStep 298849 = 224137) (by norm_num)
theorem B593765 : Blo 263822 593765 := bbase (se 4 (by rfl) ⟨55665, by rfl⟩ : syracuseStep 593765 = 111331) (by norm_num)
theorem B397157 : Blo 263822 397157 := bbase (se 4 (by rfl) ⟨37233, by rfl⟩ : syracuseStep 397157 = 74467) (by norm_num)
theorem B397181 : Blo 263822 397181 := bbase (se 3 (by rfl) ⟨74471, by rfl⟩ : syracuseStep 397181 = 148943) (by norm_num)
theorem B298885 : Blo 263822 298885 := bbase (se 4 (by rfl) ⟨28020, by rfl⟩ : syracuseStep 298885 = 56041) (by norm_num)
theorem B757637 : Blo 263822 757637 := bbase (se 4 (by rfl) ⟨71028, by rfl⟩ : syracuseStep 757637 = 142057) (by norm_num)
theorem B397205 : Blo 263822 397205 := bbase (se 6 (by rfl) ⟨9309, by rfl⟩ : syracuseStep 397205 = 18619) (by norm_num)
theorem B298921 : Blo 263822 298921 := bbase (se 2 (by rfl) ⟨112095, by rfl⟩ : syracuseStep 298921 = 224191) (by norm_num)
theorem B593837 : Blo 263822 593837 := bbase (se 3 (by rfl) ⟨111344, by rfl⟩ : syracuseStep 593837 = 222689) (by norm_num)
theorem B397229 : Blo 263822 397229 := bbase (se 3 (by rfl) ⟨74480, by rfl⟩ : syracuseStep 397229 = 148961) (by norm_num)
theorem B397253 : Blo 263822 397253 := bbase (se 4 (by rfl) ⟨37242, by rfl⟩ : syracuseStep 397253 = 74485) (by norm_num)
theorem B298957 : Blo 263822 298957 := bbase (se 3 (by rfl) ⟨56054, by rfl⟩ : syracuseStep 298957 = 112109) (by norm_num)
theorem B397277 : Blo 263822 397277 := bbase (se 3 (by rfl) ⟨74489, by rfl⟩ : syracuseStep 397277 = 148979) (by norm_num)
theorem B298993 : Blo 263822 298993 := bbase (se 2 (by rfl) ⟨112122, by rfl⟩ : syracuseStep 298993 = 224245) (by norm_num)
theorem B593909 : Blo 263822 593909 := bbase (se 5 (by rfl) ⟨27839, by rfl⟩ : syracuseStep 593909 = 55679) (by norm_num)
theorem B397301 : Blo 263822 397301 := bbase (se 5 (by rfl) ⟨18623, by rfl⟩ : syracuseStep 397301 = 37247) (by norm_num)
theorem B397325 : Blo 263822 397325 := bbase (se 3 (by rfl) ⟨74498, by rfl⟩ : syracuseStep 397325 = 148997) (by norm_num)
theorem B299029 : Blo 263822 299029 := bbase (se 6 (by rfl) ⟨7008, by rfl⟩ : syracuseStep 299029 = 14017) (by norm_num)
theorem B397349 : Blo 263822 397349 := bbase (se 4 (by rfl) ⟨37251, by rfl⟩ : syracuseStep 397349 = 74503) (by norm_num)
theorem B299065 : Blo 263822 299065 := bbase (se 2 (by rfl) ⟨112149, by rfl⟩ : syracuseStep 299065 = 224299) (by norm_num)
theorem B593981 : Blo 263822 593981 := bbase (se 3 (by rfl) ⟨111371, by rfl⟩ : syracuseStep 593981 = 222743) (by norm_num)
theorem B397373 : Blo 263822 397373 := bbase (se 3 (by rfl) ⟨74507, by rfl⟩ : syracuseStep 397373 = 149015) (by norm_num)
theorem B397397 : Blo 263822 397397 := bbase (se 8 (by rfl) ⟨2328, by rfl⟩ : syracuseStep 397397 = 4657) (by norm_num)
theorem B299101 : Blo 263822 299101 := bbase (se 3 (by rfl) ⟨56081, by rfl⟩ : syracuseStep 299101 = 112163) (by norm_num)
theorem B397421 : Blo 263822 397421 := bbase (se 3 (by rfl) ⟨74516, by rfl⟩ : syracuseStep 397421 = 149033) (by norm_num)
theorem B299137 : Blo 263822 299137 := bbase (se 2 (by rfl) ⟨112176, by rfl⟩ : syracuseStep 299137 = 224353) (by norm_num)
theorem B594053 : Blo 263822 594053 := bbase (se 4 (by rfl) ⟨55692, by rfl⟩ : syracuseStep 594053 = 111385) (by norm_num)
theorem B397445 : Blo 263822 397445 := bbase (se 4 (by rfl) ⟨37260, by rfl⟩ : syracuseStep 397445 = 74521) (by norm_num)
theorem B397469 : Blo 263822 397469 := bbase (se 3 (by rfl) ⟨74525, by rfl⟩ : syracuseStep 397469 = 149051) (by norm_num)
theorem B299173 : Blo 263822 299173 := bbase (se 4 (by rfl) ⟨28047, by rfl⟩ : syracuseStep 299173 = 56095) (by norm_num)
theorem B397493 : Blo 263822 397493 := bbase (se 5 (by rfl) ⟨18632, by rfl⟩ : syracuseStep 397493 = 37265) (by norm_num)
theorem B299209 : Blo 263822 299209 := bbase (se 2 (by rfl) ⟨112203, by rfl⟩ : syracuseStep 299209 = 224407) (by norm_num)
theorem B594125 : Blo 263822 594125 := bbase (se 3 (by rfl) ⟨111398, by rfl⟩ : syracuseStep 594125 = 222797) (by norm_num)
theorem B397517 : Blo 263822 397517 := bbase (se 3 (by rfl) ⟨74534, by rfl⟩ : syracuseStep 397517 = 149069) (by norm_num)
theorem B397541 : Blo 263822 397541 := bbase (se 4 (by rfl) ⟨37269, by rfl⟩ : syracuseStep 397541 = 74539) (by norm_num)
theorem B299245 : Blo 263822 299245 := bbase (se 3 (by rfl) ⟨56108, by rfl⟩ : syracuseStep 299245 = 112217) (by norm_num)
theorem B397565 : Blo 263822 397565 := bbase (se 3 (by rfl) ⟨74543, by rfl⟩ : syracuseStep 397565 = 149087) (by norm_num)
theorem B299281 : Blo 263822 299281 := bbase (se 2 (by rfl) ⟨112230, by rfl⟩ : syracuseStep 299281 = 224461) (by norm_num)
theorem B594197 : Blo 263822 594197 := bbase (se 6 (by rfl) ⟨13926, by rfl⟩ : syracuseStep 594197 = 27853) (by norm_num)
theorem B397589 : Blo 263822 397589 := bbase (se 6 (by rfl) ⟨9318, by rfl⟩ : syracuseStep 397589 = 18637) (by norm_num)
theorem B397613 : Blo 263822 397613 := bbase (se 3 (by rfl) ⟨74552, by rfl⟩ : syracuseStep 397613 = 149105) (by norm_num)
theorem B299317 : Blo 263822 299317 := bbase (se 5 (by rfl) ⟨14030, by rfl⟩ : syracuseStep 299317 = 28061) (by norm_num)
theorem B758069 : Blo 263822 758069 := bbase (se 5 (by rfl) ⟨35534, by rfl⟩ : syracuseStep 758069 = 71069) (by norm_num)
theorem B397637 : Blo 263822 397637 := bbase (se 4 (by rfl) ⟨37278, by rfl⟩ : syracuseStep 397637 = 74557) (by norm_num)
theorem B299353 : Blo 263822 299353 := bbase (se 2 (by rfl) ⟨112257, by rfl⟩ : syracuseStep 299353 = 224515) (by norm_num)
theorem B594269 : Blo 263822 594269 := bbase (se 3 (by rfl) ⟨111425, by rfl⟩ : syracuseStep 594269 = 222851) (by norm_num)
theorem B397661 : Blo 263822 397661 := bbase (se 3 (by rfl) ⟨74561, by rfl⟩ : syracuseStep 397661 = 149123) (by norm_num)
theorem B397685 : Blo 263822 397685 := bbase (se 5 (by rfl) ⟨18641, by rfl⟩ : syracuseStep 397685 = 37283) (by norm_num)
theorem B299389 : Blo 263822 299389 := bbase (se 3 (by rfl) ⟨56135, by rfl⟩ : syracuseStep 299389 = 112271) (by norm_num)
theorem B397709 : Blo 263822 397709 := bbase (se 3 (by rfl) ⟨74570, by rfl⟩ : syracuseStep 397709 = 149141) (by norm_num)
theorem B299425 : Blo 263822 299425 := bbase (se 2 (by rfl) ⟨112284, by rfl⟩ : syracuseStep 299425 = 224569) (by norm_num)
theorem B594341 : Blo 263822 594341 := bbase (se 4 (by rfl) ⟨55719, by rfl⟩ : syracuseStep 594341 = 111439) (by norm_num)
theorem B397733 : Blo 263822 397733 := bbase (se 4 (by rfl) ⟨37287, by rfl⟩ : syracuseStep 397733 = 74575) (by norm_num)
theorem B397757 : Blo 263822 397757 := bbase (se 3 (by rfl) ⟨74579, by rfl⟩ : syracuseStep 397757 = 149159) (by norm_num)
theorem B299461 : Blo 263822 299461 := bbase (se 4 (by rfl) ⟨28074, by rfl⟩ : syracuseStep 299461 = 56149) (by norm_num)
theorem B397781 : Blo 263822 397781 := bbase (se 7 (by rfl) ⟨4661, by rfl⟩ : syracuseStep 397781 = 9323) (by norm_num)
theorem B299497 : Blo 263822 299497 := bbase (se 2 (by rfl) ⟨112311, by rfl⟩ : syracuseStep 299497 = 224623) (by norm_num)
theorem B594413 : Blo 263822 594413 := bbase (se 3 (by rfl) ⟨111452, by rfl⟩ : syracuseStep 594413 = 222905) (by norm_num)
theorem B397805 : Blo 263822 397805 := bbase (se 3 (by rfl) ⟨74588, by rfl⟩ : syracuseStep 397805 = 149177) (by norm_num)
theorem B397829 : Blo 263822 397829 := bbase (se 4 (by rfl) ⟨37296, by rfl⟩ : syracuseStep 397829 = 74593) (by norm_num)
theorem B299533 : Blo 263822 299533 := bbase (se 3 (by rfl) ⟨56162, by rfl⟩ : syracuseStep 299533 = 112325) (by norm_num)
theorem B397853 : Blo 263822 397853 := bbase (se 3 (by rfl) ⟨74597, by rfl⟩ : syracuseStep 397853 = 149195) (by norm_num)
theorem B299569 : Blo 263822 299569 := bbase (se 2 (by rfl) ⟨112338, by rfl⟩ : syracuseStep 299569 = 224677) (by norm_num)
theorem B594485 : Blo 263822 594485 := bbase (se 5 (by rfl) ⟨27866, by rfl⟩ : syracuseStep 594485 = 55733) (by norm_num)
theorem B397877 : Blo 263822 397877 := bbase (se 5 (by rfl) ⟨18650, by rfl⟩ : syracuseStep 397877 = 37301) (by norm_num)
theorem B397901 : Blo 263822 397901 := bbase (se 3 (by rfl) ⟨74606, by rfl⟩ : syracuseStep 397901 = 149213) (by norm_num)
theorem B299605 : Blo 263822 299605 := bbase (se 8 (by rfl) ⟨1755, by rfl⟩ : syracuseStep 299605 = 3511) (by norm_num)
theorem B397925 : Blo 263822 397925 := bbase (se 4 (by rfl) ⟨37305, by rfl⟩ : syracuseStep 397925 = 74611) (by norm_num)
theorem B299641 : Blo 263822 299641 := bbase (se 2 (by rfl) ⟨112365, by rfl⟩ : syracuseStep 299641 = 224731) (by norm_num)
theorem B594557 : Blo 263822 594557 := bbase (se 3 (by rfl) ⟨111479, by rfl⟩ : syracuseStep 594557 = 222959) (by norm_num)
theorem B397949 : Blo 263822 397949 := bbase (se 3 (by rfl) ⟨74615, by rfl⟩ : syracuseStep 397949 = 149231) (by norm_num)
theorem B397973 : Blo 263822 397973 := bbase (se 6 (by rfl) ⟨9327, by rfl⟩ : syracuseStep 397973 = 18655) (by norm_num)
theorem B299677 : Blo 263822 299677 := bbase (se 3 (by rfl) ⟨56189, by rfl⟩ : syracuseStep 299677 = 112379) (by norm_num)
theorem B397997 : Blo 263822 397997 := bbase (se 3 (by rfl) ⟨74624, by rfl⟩ : syracuseStep 397997 = 149249) (by norm_num)
theorem B299713 : Blo 263822 299713 := bbase (se 2 (by rfl) ⟨112392, by rfl⟩ : syracuseStep 299713 = 224785) (by norm_num)
theorem B594629 : Blo 263822 594629 := bbase (se 4 (by rfl) ⟨55746, by rfl⟩ : syracuseStep 594629 = 111493) (by norm_num)
theorem B725701 : Blo 263822 725701 := bbase (se 4 (by rfl) ⟨68034, by rfl⟩ : syracuseStep 725701 = 136069) (by norm_num)
theorem B398021 : Blo 263822 398021 := bbase (se 4 (by rfl) ⟨37314, by rfl⟩ : syracuseStep 398021 = 74629) (by norm_num)
theorem B398045 : Blo 263822 398045 := bbase (se 3 (by rfl) ⟨74633, by rfl⟩ : syracuseStep 398045 = 149267) (by norm_num)
theorem B1348325 : Blo 263822 1348325 := bbase (se 4 (by rfl) ⟨126405, by rfl⟩ : syracuseStep 1348325 = 252811) (by norm_num)
theorem B299749 : Blo 263822 299749 := bbase (se 4 (by rfl) ⟨28101, by rfl⟩ : syracuseStep 299749 = 56203) (by norm_num)
theorem B398069 : Blo 263822 398069 := bbase (se 5 (by rfl) ⟨18659, by rfl⟩ : syracuseStep 398069 = 37319) (by norm_num)
theorem B299785 : Blo 263822 299785 := bbase (se 2 (by rfl) ⟨112419, by rfl⟩ : syracuseStep 299785 = 224839) (by norm_num)
theorem B594701 : Blo 263822 594701 := bbase (se 3 (by rfl) ⟨111506, by rfl⟩ : syracuseStep 594701 = 223013) (by norm_num)
theorem B398093 : Blo 263822 398093 := bbase (se 3 (by rfl) ⟨74642, by rfl⟩ : syracuseStep 398093 = 149285) (by norm_num)
theorem B398117 : Blo 263822 398117 := bbase (se 4 (by rfl) ⟨37323, by rfl⟩ : syracuseStep 398117 = 74647) (by norm_num)
theorem B299821 : Blo 263822 299821 := bbase (se 3 (by rfl) ⟨56216, by rfl⟩ : syracuseStep 299821 = 112433) (by norm_num)
theorem B398141 : Blo 263822 398141 := bbase (se 3 (by rfl) ⟨74651, by rfl⟩ : syracuseStep 398141 = 149303) (by norm_num)
theorem B299857 : Blo 263822 299857 := bbase (se 2 (by rfl) ⟨112446, by rfl⟩ : syracuseStep 299857 = 224893) (by norm_num)
theorem B594773 : Blo 263822 594773 := bbase (se 9 (by rfl) ⟨1742, by rfl⟩ : syracuseStep 594773 = 3485) (by norm_num)
theorem B398165 : Blo 263822 398165 := bbase (se 9 (by rfl) ⟨1166, by rfl⟩ : syracuseStep 398165 = 2333) (by norm_num)
theorem B398189 : Blo 263822 398189 := bbase (se 3 (by rfl) ⟨74660, by rfl⟩ : syracuseStep 398189 = 149321) (by norm_num)
theorem B299893 : Blo 263822 299893 := bbase (se 5 (by rfl) ⟨14057, by rfl⟩ : syracuseStep 299893 = 28115) (by norm_num)
theorem B398213 : Blo 263822 398213 := bbase (se 4 (by rfl) ⟨37332, by rfl⟩ : syracuseStep 398213 = 74665) (by norm_num)
theorem B299929 : Blo 263822 299929 := bbase (se 2 (by rfl) ⟨112473, by rfl⟩ : syracuseStep 299929 = 224947) (by norm_num)
theorem B594845 : Blo 263822 594845 := bbase (se 3 (by rfl) ⟨111533, by rfl⟩ : syracuseStep 594845 = 223067) (by norm_num)
theorem B398237 : Blo 263822 398237 := bbase (se 3 (by rfl) ⟨74669, by rfl⟩ : syracuseStep 398237 = 149339) (by norm_num)
theorem B398261 : Blo 263822 398261 := bbase (se 5 (by rfl) ⟨18668, by rfl⟩ : syracuseStep 398261 = 37337) (by norm_num)
theorem B299965 : Blo 263822 299965 := bbase (se 3 (by rfl) ⟨56243, by rfl⟩ : syracuseStep 299965 = 112487) (by norm_num)
theorem B398285 : Blo 263822 398285 := bbase (se 3 (by rfl) ⟨74678, by rfl⟩ : syracuseStep 398285 = 149357) (by norm_num)
theorem B300001 : Blo 263822 300001 := bbase (se 2 (by rfl) ⟨112500, by rfl⟩ : syracuseStep 300001 = 225001) (by norm_num)
theorem B594917 : Blo 263822 594917 := bbase (se 4 (by rfl) ⟨55773, by rfl⟩ : syracuseStep 594917 = 111547) (by norm_num)
theorem B398309 : Blo 263822 398309 := bbase (se 4 (by rfl) ⟨37341, by rfl⟩ : syracuseStep 398309 = 74683) (by norm_num)
theorem B398333 : Blo 263822 398333 := bbase (se 3 (by rfl) ⟨74687, by rfl⟩ : syracuseStep 398333 = 149375) (by norm_num)
theorem B300037 : Blo 263822 300037 := bbase (se 4 (by rfl) ⟨28128, by rfl⟩ : syracuseStep 300037 = 56257) (by norm_num)
theorem B398357 : Blo 263822 398357 := bbase (se 6 (by rfl) ⟨9336, by rfl⟩ : syracuseStep 398357 = 18673) (by norm_num)
theorem B758821 : Blo 263822 758821 := bbase (se 4 (by rfl) ⟨71139, by rfl⟩ : syracuseStep 758821 = 142279) (by norm_num)
theorem B300073 : Blo 263822 300073 := bbase (se 2 (by rfl) ⟨112527, by rfl⟩ : syracuseStep 300073 = 225055) (by norm_num)
theorem B594989 : Blo 263822 594989 := bbase (se 3 (by rfl) ⟨111560, by rfl⟩ : syracuseStep 594989 = 223121) (by norm_num)
theorem B398381 : Blo 263822 398381 := bbase (se 3 (by rfl) ⟨74696, by rfl⟩ : syracuseStep 398381 = 149393) (by norm_num)
theorem B398405 : Blo 263822 398405 := bbase (se 4 (by rfl) ⟨37350, by rfl⟩ : syracuseStep 398405 = 74701) (by norm_num)
theorem B300109 : Blo 263822 300109 := bbase (se 3 (by rfl) ⟨56270, by rfl⟩ : syracuseStep 300109 = 112541) (by norm_num)
theorem B398429 : Blo 263822 398429 := bbase (se 3 (by rfl) ⟨74705, by rfl⟩ : syracuseStep 398429 = 149411) (by norm_num)
theorem B300145 : Blo 263822 300145 := bbase (se 2 (by rfl) ⟨112554, by rfl⟩ : syracuseStep 300145 = 225109) (by norm_num)
theorem B595061 : Blo 263822 595061 := bbase (se 5 (by rfl) ⟨27893, by rfl⟩ : syracuseStep 595061 = 55787) (by norm_num)
theorem B398453 : Blo 263822 398453 := bbase (se 5 (by rfl) ⟨18677, by rfl⟩ : syracuseStep 398453 = 37355) (by norm_num)
theorem B398477 : Blo 263822 398477 := bbase (se 3 (by rfl) ⟨74714, by rfl⟩ : syracuseStep 398477 = 149429) (by norm_num)
theorem B300181 : Blo 263822 300181 := bbase (se 6 (by rfl) ⟨7035, by rfl⟩ : syracuseStep 300181 = 14071) (by norm_num)
theorem B398501 : Blo 263822 398501 := bbase (se 4 (by rfl) ⟨37359, by rfl⟩ : syracuseStep 398501 = 74719) (by norm_num)
theorem B300217 : Blo 263822 300217 := bbase (se 2 (by rfl) ⟨112581, by rfl⟩ : syracuseStep 300217 = 225163) (by norm_num)
theorem B595133 : Blo 263822 595133 := bbase (se 3 (by rfl) ⟨111587, by rfl⟩ : syracuseStep 595133 = 223175) (by norm_num)
theorem B398525 : Blo 263822 398525 := bbase (se 3 (by rfl) ⟨74723, by rfl⟩ : syracuseStep 398525 = 149447) (by norm_num)
theorem B398549 : Blo 263822 398549 := bbase (se 7 (by rfl) ⟨4670, by rfl⟩ : syracuseStep 398549 = 9341) (by norm_num)
theorem B300253 : Blo 263822 300253 := bbase (se 3 (by rfl) ⟨56297, by rfl⟩ : syracuseStep 300253 = 112595) (by norm_num)
theorem B398573 : Blo 263822 398573 := bbase (se 3 (by rfl) ⟨74732, by rfl⟩ : syracuseStep 398573 = 149465) (by norm_num)
theorem B300289 : Blo 263822 300289 := bbase (se 2 (by rfl) ⟨112608, by rfl⟩ : syracuseStep 300289 = 225217) (by norm_num)
theorem B595205 : Blo 263822 595205 := bbase (se 4 (by rfl) ⟨55800, by rfl⟩ : syracuseStep 595205 = 111601) (by norm_num)
theorem B398597 : Blo 263822 398597 := bbase (se 4 (by rfl) ⟨37368, by rfl⟩ : syracuseStep 398597 = 74737) (by norm_num)
theorem B398621 : Blo 263822 398621 := bbase (se 3 (by rfl) ⟨74741, by rfl⟩ : syracuseStep 398621 = 149483) (by norm_num)
theorem B300325 : Blo 263822 300325 := bbase (se 4 (by rfl) ⟨28155, by rfl⟩ : syracuseStep 300325 = 56311) (by norm_num)
theorem B398645 : Blo 263822 398645 := bbase (se 5 (by rfl) ⟨18686, by rfl⟩ : syracuseStep 398645 = 37373) (by norm_num)
theorem B300361 : Blo 263822 300361 := bbase (se 2 (by rfl) ⟨112635, by rfl⟩ : syracuseStep 300361 = 225271) (by norm_num)
theorem B595277 : Blo 263822 595277 := bbase (se 3 (by rfl) ⟨111614, by rfl⟩ : syracuseStep 595277 = 223229) (by norm_num)
theorem B398669 : Blo 263822 398669 := bbase (se 3 (by rfl) ⟨74750, by rfl⟩ : syracuseStep 398669 = 149501) (by norm_num)
theorem B398693 : Blo 263822 398693 := bbase (se 4 (by rfl) ⟨37377, by rfl⟩ : syracuseStep 398693 = 74755) (by norm_num)
theorem B300397 : Blo 263822 300397 := bbase (se 3 (by rfl) ⟨56324, by rfl⟩ : syracuseStep 300397 = 112649) (by norm_num)
theorem B398717 : Blo 263822 398717 := bbase (se 3 (by rfl) ⟨74759, by rfl⟩ : syracuseStep 398717 = 149519) (by norm_num)
theorem B300433 : Blo 263822 300433 := bbase (se 2 (by rfl) ⟨112662, by rfl⟩ : syracuseStep 300433 = 225325) (by norm_num)
theorem B595349 : Blo 263822 595349 := bbase (se 6 (by rfl) ⟨13953, by rfl⟩ : syracuseStep 595349 = 27907) (by norm_num)
theorem B398741 : Blo 263822 398741 := bbase (se 6 (by rfl) ⟨9345, by rfl⟩ : syracuseStep 398741 = 18691) (by norm_num)
theorem B1021349 : Blo 263822 1021349 := bbase (se 4 (by rfl) ⟨95751, by rfl⟩ : syracuseStep 1021349 = 191503) (by norm_num)
theorem B398765 : Blo 263822 398765 := bbase (se 3 (by rfl) ⟨74768, by rfl⟩ : syracuseStep 398765 = 149537) (by norm_num)
theorem B300469 : Blo 263822 300469 := bbase (se 5 (by rfl) ⟨14084, by rfl⟩ : syracuseStep 300469 = 28169) (by norm_num)
theorem B398789 : Blo 263822 398789 := bbase (se 4 (by rfl) ⟨37386, by rfl⟩ : syracuseStep 398789 = 74773) (by norm_num)
theorem B300505 : Blo 263822 300505 := bbase (se 2 (by rfl) ⟨112689, by rfl⟩ : syracuseStep 300505 = 225379) (by norm_num)
theorem B595421 : Blo 263822 595421 := bbase (se 3 (by rfl) ⟨111641, by rfl⟩ : syracuseStep 595421 = 223283) (by norm_num)
theorem B398813 : Blo 263822 398813 := bbase (se 3 (by rfl) ⟨74777, by rfl⟩ : syracuseStep 398813 = 149555) (by norm_num)
theorem B398837 : Blo 263822 398837 := bbase (se 5 (by rfl) ⟨18695, by rfl⟩ : syracuseStep 398837 = 37391) (by norm_num)
theorem B300541 : Blo 263822 300541 := bbase (se 3 (by rfl) ⟨56351, by rfl⟩ : syracuseStep 300541 = 112703) (by norm_num)
theorem B398861 : Blo 263822 398861 := bbase (se 3 (by rfl) ⟨74786, by rfl⟩ : syracuseStep 398861 = 149573) (by norm_num)
theorem B300577 : Blo 263822 300577 := bbase (se 2 (by rfl) ⟨112716, by rfl⟩ : syracuseStep 300577 = 225433) (by norm_num)
theorem B890405 : Blo 263822 890405 := bbase (se 4 (by rfl) ⟨83475, by rfl⟩ : syracuseStep 890405 = 166951) (by norm_num)
theorem B595493 : Blo 263822 595493 := bbase (se 4 (by rfl) ⟨55827, by rfl⟩ : syracuseStep 595493 = 111655) (by norm_num)
theorem B398885 : Blo 263822 398885 := bbase (se 4 (by rfl) ⟨37395, by rfl⟩ : syracuseStep 398885 = 74791) (by norm_num)
theorem B398909 : Blo 263822 398909 := bbase (se 3 (by rfl) ⟨74795, by rfl⟩ : syracuseStep 398909 = 149591) (by norm_num)
theorem B300613 : Blo 263822 300613 := bbase (se 4 (by rfl) ⟨28182, by rfl⟩ : syracuseStep 300613 = 56365) (by norm_num)
theorem B398933 : Blo 263822 398933 := bbase (se 8 (by rfl) ⟨2337, by rfl⟩ : syracuseStep 398933 = 4675) (by norm_num)
theorem B300649 : Blo 263822 300649 := bbase (se 2 (by rfl) ⟨112743, by rfl⟩ : syracuseStep 300649 = 225487) (by norm_num)
theorem B595565 : Blo 263822 595565 := bbase (se 3 (by rfl) ⟨111668, by rfl⟩ : syracuseStep 595565 = 223337) (by norm_num)
theorem B398957 : Blo 263822 398957 := bbase (se 3 (by rfl) ⟨74804, by rfl⟩ : syracuseStep 398957 = 149609) (by norm_num)
theorem B1283701 : Blo 263822 1283701 := bbase (se 5 (by rfl) ⟨60173, by rfl⟩ : syracuseStep 1283701 = 120347) (by norm_num)
theorem B398981 : Blo 263822 398981 := bbase (se 4 (by rfl) ⟨37404, by rfl⟩ : syracuseStep 398981 = 74809) (by norm_num)
theorem B300685 : Blo 263822 300685 := bbase (se 3 (by rfl) ⟨56378, by rfl⟩ : syracuseStep 300685 = 112757) (by norm_num)
theorem B857749 : Blo 263822 857749 := bbase (se 6 (by rfl) ⟨20103, by rfl⟩ : syracuseStep 857749 = 40207) (by norm_num)
theorem B399005 : Blo 263822 399005 := bbase (se 3 (by rfl) ⟨74813, by rfl⟩ : syracuseStep 399005 = 149627) (by norm_num)
theorem B300721 : Blo 263822 300721 := bbase (se 2 (by rfl) ⟨112770, by rfl⟩ : syracuseStep 300721 = 225541) (by norm_num)
theorem B595637 : Blo 263822 595637 := bbase (se 5 (by rfl) ⟨27920, by rfl⟩ : syracuseStep 595637 = 55841) (by norm_num)
theorem B399029 : Blo 263822 399029 := bbase (se 5 (by rfl) ⟨18704, by rfl⟩ : syracuseStep 399029 = 37409) (by norm_num)
theorem B399053 : Blo 263822 399053 := bbase (se 3 (by rfl) ⟨74822, by rfl⟩ : syracuseStep 399053 = 149645) (by norm_num)
theorem B300757 : Blo 263822 300757 := bbase (se 7 (by rfl) ⟨3524, by rfl⟩ : syracuseStep 300757 = 7049) (by norm_num)
theorem B399077 : Blo 263822 399077 := bbase (se 4 (by rfl) ⟨37413, by rfl⟩ : syracuseStep 399077 = 74827) (by norm_num)
theorem B300793 : Blo 263822 300793 := bbase (se 2 (by rfl) ⟨112797, by rfl⟩ : syracuseStep 300793 = 225595) (by norm_num)
theorem B595709 : Blo 263822 595709 := bbase (se 3 (by rfl) ⟨111695, by rfl⟩ : syracuseStep 595709 = 223391) (by norm_num)
theorem B399101 : Blo 263822 399101 := bbase (se 3 (by rfl) ⟨74831, by rfl⟩ : syracuseStep 399101 = 149663) (by norm_num)
theorem B399125 : Blo 263822 399125 := bbase (se 6 (by rfl) ⟨9354, by rfl⟩ : syracuseStep 399125 = 18709) (by norm_num)
theorem B300829 : Blo 263822 300829 := bbase (se 3 (by rfl) ⟨56405, by rfl⟩ : syracuseStep 300829 = 112811) (by norm_num)
theorem B399149 : Blo 263822 399149 := bbase (se 3 (by rfl) ⟨74840, by rfl⟩ : syracuseStep 399149 = 149681) (by norm_num)
theorem B300865 : Blo 263822 300865 := bbase (se 2 (by rfl) ⟨112824, by rfl⟩ : syracuseStep 300865 = 225649) (by norm_num)
theorem B595781 : Blo 263822 595781 := bbase (se 4 (by rfl) ⟨55854, by rfl⟩ : syracuseStep 595781 = 111709) (by norm_num)
theorem B399173 : Blo 263822 399173 := bbase (se 4 (by rfl) ⟨37422, by rfl⟩ : syracuseStep 399173 = 74845) (by norm_num)
theorem B399197 : Blo 263822 399197 := bbase (se 3 (by rfl) ⟨74849, by rfl⟩ : syracuseStep 399197 = 149699) (by norm_num)
theorem B956261 : Blo 263822 956261 := bbase (se 4 (by rfl) ⟨89649, by rfl⟩ : syracuseStep 956261 = 179299) (by norm_num)
theorem B300901 : Blo 263822 300901 := bbase (se 4 (by rfl) ⟨28209, by rfl⟩ : syracuseStep 300901 = 56419) (by norm_num)
theorem B399221 : Blo 263822 399221 := bbase (se 5 (by rfl) ⟨18713, by rfl⟩ : syracuseStep 399221 = 37427) (by norm_num)
theorem B300937 : Blo 263822 300937 := bbase (se 2 (by rfl) ⟨112851, by rfl⟩ : syracuseStep 300937 = 225703) (by norm_num)
theorem B595853 : Blo 263822 595853 := bbase (se 3 (by rfl) ⟨111722, by rfl⟩ : syracuseStep 595853 = 223445) (by norm_num)
theorem B399245 : Blo 263822 399245 := bbase (se 3 (by rfl) ⟨74858, by rfl⟩ : syracuseStep 399245 = 149717) (by norm_num)
theorem B300953 : Blo 263822 300953 := bbase (se 2 (by rfl) ⟨112857, by rfl⟩ : syracuseStep 300953 = 225715) (by norm_num)
theorem B399269 : Blo 263822 399269 := bbase (se 4 (by rfl) ⟨37431, by rfl⟩ : syracuseStep 399269 = 74863) (by norm_num)
theorem B300973 : Blo 263822 300973 := bbase (se 3 (by rfl) ⟨56432, by rfl⟩ : syracuseStep 300973 = 112865) (by norm_num)
theorem B399293 : Blo 263822 399293 := bbase (se 3 (by rfl) ⟨74867, by rfl⟩ : syracuseStep 399293 = 149735) (by norm_num)
theorem B301009 : Blo 263822 301009 := bbase (se 2 (by rfl) ⟨112878, by rfl⟩ : syracuseStep 301009 = 225757) (by norm_num)
theorem B890837 : Blo 263822 890837 := bbase (se 7 (by rfl) ⟨10439, by rfl⟩ : syracuseStep 890837 = 20879) (by norm_num)
theorem B595925 : Blo 263822 595925 := bbase (se 7 (by rfl) ⟨6983, by rfl⟩ : syracuseStep 595925 = 13967) (by norm_num)
theorem B399317 : Blo 263822 399317 := bbase (se 7 (by rfl) ⟨4679, by rfl⟩ : syracuseStep 399317 = 9359) (by norm_num)
theorem B366557 : Blo 263822 366557 := bbase (se 3 (by rfl) ⟨68729, by rfl⟩ : syracuseStep 366557 = 137459) (by norm_num)
theorem B399341 : Blo 263822 399341 := bbase (se 3 (by rfl) ⟨74876, by rfl⟩ : syracuseStep 399341 = 149753) (by norm_num)
theorem B1349621 : Blo 263822 1349621 := bbase (se 5 (by rfl) ⟨63263, by rfl⟩ : syracuseStep 1349621 = 126527) (by norm_num)
theorem B301045 : Blo 263822 301045 := bbase (se 5 (by rfl) ⟨14111, by rfl⟩ : syracuseStep 301045 = 28223) (by norm_num)
theorem B399365 : Blo 263822 399365 := bbase (se 4 (by rfl) ⟨37440, by rfl⟩ : syracuseStep 399365 = 74881) (by norm_num)
theorem B301081 : Blo 263822 301081 := bbase (se 2 (by rfl) ⟨112905, by rfl⟩ : syracuseStep 301081 = 225811) (by norm_num)
theorem B595997 : Blo 263822 595997 := bbase (se 3 (by rfl) ⟨111749, by rfl⟩ : syracuseStep 595997 = 223499) (by norm_num)
theorem B399389 : Blo 263822 399389 := bbase (se 3 (by rfl) ⟨74885, by rfl⟩ : syracuseStep 399389 = 149771) (by norm_num)
theorem B399413 : Blo 263822 399413 := bbase (se 5 (by rfl) ⟨18722, by rfl⟩ : syracuseStep 399413 = 37445) (by norm_num)
theorem B301117 : Blo 263822 301117 := bbase (se 3 (by rfl) ⟨56459, by rfl⟩ : syracuseStep 301117 = 112919) (by norm_num)
theorem B399437 : Blo 263822 399437 := bbase (se 3 (by rfl) ⟨74894, by rfl⟩ : syracuseStep 399437 = 149789) (by norm_num)
theorem B301153 : Blo 263822 301153 := bbase (se 2 (by rfl) ⟨112932, by rfl⟩ : syracuseStep 301153 = 225865) (by norm_num)
theorem B596069 : Blo 263822 596069 := bbase (se 4 (by rfl) ⟨55881, by rfl⟩ : syracuseStep 596069 = 111763) (by norm_num)
theorem B399461 : Blo 263822 399461 := bbase (se 4 (by rfl) ⟨37449, by rfl⟩ : syracuseStep 399461 = 74899) (by norm_num)
theorem B399485 : Blo 263822 399485 := bbase (se 3 (by rfl) ⟨74903, by rfl⟩ : syracuseStep 399485 = 149807) (by norm_num)
theorem B956549 : Blo 263822 956549 := bbase (se 4 (by rfl) ⟨89676, by rfl⟩ : syracuseStep 956549 = 179353) (by norm_num)
theorem B301189 : Blo 263822 301189 := bbase (se 4 (by rfl) ⟨28236, by rfl⟩ : syracuseStep 301189 = 56473) (by norm_num)
theorem B333973 : Blo 263822 333973 := bbase (se 6 (by rfl) ⟨7827, by rfl⟩ : syracuseStep 333973 = 15655) (by norm_num)
theorem B399509 : Blo 263822 399509 := bbase (se 6 (by rfl) ⟨9363, by rfl⟩ : syracuseStep 399509 = 18727) (by norm_num)
theorem B301225 : Blo 263822 301225 := bbase (se 2 (by rfl) ⟨112959, by rfl⟩ : syracuseStep 301225 = 225919) (by norm_num)
theorem B596141 : Blo 263822 596141 := bbase (se 3 (by rfl) ⟨111776, by rfl⟩ : syracuseStep 596141 = 223553) (by norm_num)
theorem B399533 : Blo 263822 399533 := bbase (se 3 (by rfl) ⟨74912, by rfl⟩ : syracuseStep 399533 = 149825) (by norm_num)
theorem B399557 : Blo 263822 399557 := bbase (se 4 (by rfl) ⟨37458, by rfl⟩ : syracuseStep 399557 = 74917) (by norm_num)
theorem B301261 : Blo 263822 301261 := bbase (se 3 (by rfl) ⟨56486, by rfl⟩ : syracuseStep 301261 = 112973) (by norm_num)
theorem B399581 : Blo 263822 399581 := bbase (se 3 (by rfl) ⟨74921, by rfl⟩ : syracuseStep 399581 = 149843) (by norm_num)
theorem B301297 : Blo 263822 301297 := bbase (se 2 (by rfl) ⟨112986, by rfl⟩ : syracuseStep 301297 = 225973) (by norm_num)
theorem B596213 : Blo 263822 596213 := bbase (se 5 (by rfl) ⟨27947, by rfl⟩ : syracuseStep 596213 = 55895) (by norm_num)
theorem B399605 : Blo 263822 399605 := bbase (se 5 (by rfl) ⟨18731, by rfl⟩ : syracuseStep 399605 = 37463) (by norm_num)
theorem B399629 : Blo 263822 399629 := bbase (se 3 (by rfl) ⟨74930, by rfl⟩ : syracuseStep 399629 = 149861) (by norm_num)
theorem B399653 : Blo 263822 399653 := bbase (se 4 (by rfl) ⟨37467, by rfl⟩ : syracuseStep 399653 = 74935) (by norm_num)
theorem B596285 : Blo 263822 596285 := bbase (se 3 (by rfl) ⟨111803, by rfl⟩ : syracuseStep 596285 = 223607) (by norm_num)
theorem B399677 : Blo 263822 399677 := bbase (se 3 (by rfl) ⟨74939, by rfl⟩ : syracuseStep 399677 = 149879) (by norm_num)
theorem B334145 : Blo 263822 334145 := bbase (se 2 (by rfl) ⟨125304, by rfl⟩ : syracuseStep 334145 = 250609) (by norm_num)
theorem B399701 : Blo 263822 399701 := bbase (se 10 (by rfl) ⟨585, by rfl⟩ : syracuseStep 399701 = 1171) (by norm_num)
theorem B399725 : Blo 263822 399725 := bbase (se 3 (by rfl) ⟨74948, by rfl⟩ : syracuseStep 399725 = 149897) (by norm_num)
theorem B334201 : Blo 263822 334201 := bbase (se 2 (by rfl) ⟨125325, by rfl⟩ : syracuseStep 334201 = 250651) (by norm_num)
theorem B891269 : Blo 263822 891269 := bbase (se 4 (by rfl) ⟨83556, by rfl⟩ : syracuseStep 891269 = 167113) (by norm_num)
theorem B596357 : Blo 263822 596357 := bbase (se 4 (by rfl) ⟨55908, by rfl⟩ : syracuseStep 596357 = 111817) (by norm_num)
theorem B399749 : Blo 263822 399749 := bbase (se 4 (by rfl) ⟨37476, by rfl⟩ : syracuseStep 399749 = 74953) (by norm_num)
theorem B268681 : Blo 263822 268681 := bbase (se 2 (by rfl) ⟨100755, by rfl⟩ : syracuseStep 268681 = 201511) (by norm_num)
theorem B399773 : Blo 263822 399773 := bbase (se 3 (by rfl) ⟨74957, by rfl⟩ : syracuseStep 399773 = 149915) (by norm_num)
theorem B399797 : Blo 263822 399797 := bbase (se 5 (by rfl) ⟨18740, by rfl⟩ : syracuseStep 399797 = 37481) (by norm_num)
theorem B596429 : Blo 263822 596429 := bbase (se 3 (by rfl) ⟨111830, by rfl⟩ : syracuseStep 596429 = 223661) (by norm_num)
theorem B399821 : Blo 263822 399821 := bbase (se 3 (by rfl) ⟨74966, by rfl⟩ : syracuseStep 399821 = 149933) (by norm_num)
theorem B334297 : Blo 263822 334297 := bbase (se 2 (by rfl) ⟨125361, by rfl⟩ : syracuseStep 334297 = 250723) (by norm_num)
theorem B399845 : Blo 263822 399845 := bbase (se 4 (by rfl) ⟨37485, by rfl⟩ : syracuseStep 399845 = 74971) (by norm_num)
theorem B399869 : Blo 263822 399869 := bbase (se 3 (by rfl) ⟨74975, by rfl⟩ : syracuseStep 399869 = 149951) (by norm_num)
theorem B596501 : Blo 263822 596501 := bbase (se 6 (by rfl) ⟨13980, by rfl⟩ : syracuseStep 596501 = 27961) (by norm_num)
theorem B399893 : Blo 263822 399893 := bbase (se 6 (by rfl) ⟨9372, by rfl⟩ : syracuseStep 399893 = 18745) (by norm_num)
theorem B399917 : Blo 263822 399917 := bbase (se 3 (by rfl) ⟨74984, by rfl⟩ : syracuseStep 399917 = 149969) (by norm_num)
theorem B399941 : Blo 263822 399941 := bbase (se 4 (by rfl) ⟨37494, by rfl⟩ : syracuseStep 399941 = 74989) (by norm_num)
theorem B596573 : Blo 263822 596573 := bbase (se 3 (by rfl) ⟨111857, by rfl⟩ : syracuseStep 596573 = 223715) (by norm_num)
theorem B399965 : Blo 263822 399965 := bbase (se 3 (by rfl) ⟨74993, by rfl⟩ : syracuseStep 399965 = 149987) (by norm_num)
theorem B399989 : Blo 263822 399989 := bbase (se 5 (by rfl) ⟨18749, by rfl⟩ : syracuseStep 399989 = 37499) (by norm_num)
theorem B334469 : Blo 263822 334469 := bbase (se 4 (by rfl) ⟨31356, by rfl⟩ : syracuseStep 334469 = 62713) (by norm_num)
theorem B400013 : Blo 263822 400013 := bbase (se 3 (by rfl) ⟨75002, by rfl⟩ : syracuseStep 400013 = 150005) (by norm_num)
theorem B596645 : Blo 263822 596645 := bbase (se 4 (by rfl) ⟨55935, by rfl⟩ : syracuseStep 596645 = 111871) (by norm_num)
theorem B400037 : Blo 263822 400037 := bbase (se 4 (by rfl) ⟨37503, by rfl⟩ : syracuseStep 400037 = 75007) (by norm_num)
theorem B334525 : Blo 263822 334525 := bbase (se 3 (by rfl) ⟨62723, by rfl⟩ : syracuseStep 334525 = 125447) (by norm_num)
theorem B400061 : Blo 263822 400061 := bbase (se 3 (by rfl) ⟨75011, by rfl⟩ : syracuseStep 400061 = 150023) (by norm_num)
theorem B400085 : Blo 263822 400085 := bbase (se 7 (by rfl) ⟨4688, by rfl⟩ : syracuseStep 400085 = 9377) (by norm_num)
theorem B596717 : Blo 263822 596717 := bbase (se 3 (by rfl) ⟨111884, by rfl⟩ : syracuseStep 596717 = 223769) (by norm_num)
theorem B400109 : Blo 263822 400109 := bbase (se 3 (by rfl) ⟨75020, by rfl⟩ : syracuseStep 400109 = 150041) (by norm_num)
theorem B400133 : Blo 263822 400133 := bbase (se 4 (by rfl) ⟨37512, by rfl⟩ : syracuseStep 400133 = 75025) (by norm_num)
theorem B334621 : Blo 263822 334621 := bbase (se 3 (by rfl) ⟨62741, by rfl⟩ : syracuseStep 334621 = 125483) (by norm_num)
theorem B400157 : Blo 263822 400157 := bbase (se 3 (by rfl) ⟨75029, by rfl⟩ : syracuseStep 400157 = 150059) (by norm_num)
theorem B891701 : Blo 263822 891701 := bbase (se 5 (by rfl) ⟨41798, by rfl⟩ : syracuseStep 891701 = 83597) (by norm_num)
theorem B596789 : Blo 263822 596789 := bbase (se 5 (by rfl) ⟨27974, by rfl⟩ : syracuseStep 596789 = 55949) (by norm_num)
theorem B400181 : Blo 263822 400181 := bbase (se 5 (by rfl) ⟨18758, by rfl⟩ : syracuseStep 400181 = 37517) (by norm_num)
theorem B400205 : Blo 263822 400205 := bbase (se 3 (by rfl) ⟨75038, by rfl⟩ : syracuseStep 400205 = 150077) (by norm_num)
theorem B400229 : Blo 263822 400229 := bbase (se 4 (by rfl) ⟨37521, by rfl⟩ : syracuseStep 400229 = 75043) (by norm_num)
theorem B596861 : Blo 263822 596861 := bbase (se 3 (by rfl) ⟨111911, by rfl⟩ : syracuseStep 596861 = 223823) (by norm_num)
theorem B400253 : Blo 263822 400253 := bbase (se 3 (by rfl) ⟨75047, by rfl⟩ : syracuseStep 400253 = 150095) (by norm_num)
theorem B400277 : Blo 263822 400277 := bbase (se 6 (by rfl) ⟨9381, by rfl⟩ : syracuseStep 400277 = 18763) (by norm_num)
theorem B400301 : Blo 263822 400301 := bbase (se 3 (by rfl) ⟨75056, by rfl⟩ : syracuseStep 400301 = 150113) (by norm_num)
theorem B596933 : Blo 263822 596933 := bbase (se 4 (by rfl) ⟨55962, by rfl⟩ : syracuseStep 596933 = 111925) (by norm_num)
theorem B400325 : Blo 263822 400325 := bbase (se 4 (by rfl) ⟨37530, by rfl⟩ : syracuseStep 400325 = 75061) (by norm_num)
theorem B334793 : Blo 263822 334793 := bbase (se 2 (by rfl) ⟨125547, by rfl⟩ : syracuseStep 334793 = 251095) (by norm_num)
theorem B400349 : Blo 263822 400349 := bbase (se 3 (by rfl) ⟨75065, by rfl⟩ : syracuseStep 400349 = 150131) (by norm_num)
theorem B400373 : Blo 263822 400373 := bbase (se 5 (by rfl) ⟨18767, by rfl⟩ : syracuseStep 400373 = 37535) (by norm_num)
theorem B334849 : Blo 263822 334849 := bbase (se 2 (by rfl) ⟨125568, by rfl⟩ : syracuseStep 334849 = 251137) (by norm_num)
theorem B597005 : Blo 263822 597005 := bbase (se 3 (by rfl) ⟨111938, by rfl⟩ : syracuseStep 597005 = 223877) (by norm_num)
theorem B400397 : Blo 263822 400397 := bbase (se 3 (by rfl) ⟨75074, by rfl⟩ : syracuseStep 400397 = 150149) (by norm_num)
theorem B400421 : Blo 263822 400421 := bbase (se 4 (by rfl) ⟨37539, by rfl⟩ : syracuseStep 400421 = 75079) (by norm_num)
theorem B400445 : Blo 263822 400445 := bbase (se 3 (by rfl) ⟨75083, by rfl⟩ : syracuseStep 400445 = 150167) (by norm_num)
theorem B597077 : Blo 263822 597077 := bbase (se 8 (by rfl) ⟨3498, by rfl⟩ : syracuseStep 597077 = 6997) (by norm_num)
theorem B400469 : Blo 263822 400469 := bbase (se 8 (by rfl) ⟨2346, by rfl⟩ : syracuseStep 400469 = 4693) (by norm_num)
theorem B334945 : Blo 263822 334945 := bbase (se 2 (by rfl) ⟨125604, by rfl⟩ : syracuseStep 334945 = 251209) (by norm_num)
theorem B400493 : Blo 263822 400493 := bbase (se 3 (by rfl) ⟨75092, by rfl⟩ : syracuseStep 400493 = 150185) (by norm_num)
theorem B564349 : Blo 263822 564349 := bbase (se 3 (by rfl) ⟨105815, by rfl⟩ : syracuseStep 564349 = 211631) (by norm_num)
theorem B400517 : Blo 263822 400517 := bbase (se 4 (by rfl) ⟨37548, by rfl⟩ : syracuseStep 400517 = 75097) (by norm_num)
theorem B302221 : Blo 263822 302221 := bbase (se 3 (by rfl) ⟨56666, by rfl⟩ : syracuseStep 302221 = 113333) (by norm_num)
theorem B597149 : Blo 263822 597149 := bbase (se 3 (by rfl) ⟨111965, by rfl⟩ : syracuseStep 597149 = 223931) (by norm_num)
theorem B400541 : Blo 263822 400541 := bbase (se 3 (by rfl) ⟨75101, by rfl⟩ : syracuseStep 400541 = 150203) (by norm_num)
theorem B400565 : Blo 263822 400565 := bbase (se 5 (by rfl) ⟨18776, by rfl⟩ : syracuseStep 400565 = 37553) (by norm_num)
theorem B400589 : Blo 263822 400589 := bbase (se 3 (by rfl) ⟨75110, by rfl⟩ : syracuseStep 400589 = 150221) (by norm_num)
theorem B302293 : Blo 263822 302293 := bbase (se 7 (by rfl) ⟨3542, by rfl⟩ : syracuseStep 302293 = 7085) (by norm_num)
theorem B269525 : Blo 263822 269525 := bbase (se 7 (by rfl) ⟨3158, by rfl⟩ : syracuseStep 269525 = 6317) (by norm_num)
theorem B892133 : Blo 263822 892133 := bbase (se 4 (by rfl) ⟨83637, by rfl⟩ : syracuseStep 892133 = 167275) (by norm_num)
theorem B597221 : Blo 263822 597221 := bbase (se 4 (by rfl) ⟨55989, by rfl⟩ : syracuseStep 597221 = 111979) (by norm_num)
theorem B400613 : Blo 263822 400613 := bbase (se 4 (by rfl) ⟨37557, by rfl⟩ : syracuseStep 400613 = 75115) (by norm_num)
theorem B400637 : Blo 263822 400637 := bbase (se 3 (by rfl) ⟨75119, by rfl⟩ : syracuseStep 400637 = 150239) (by norm_num)
theorem B957701 : Blo 263822 957701 := bbase (se 4 (by rfl) ⟨89784, by rfl⟩ : syracuseStep 957701 = 179569) (by norm_num)
theorem B1350917 : Blo 263822 1350917 := bbase (se 4 (by rfl) ⟨126648, by rfl⟩ : syracuseStep 1350917 = 253297) (by norm_num)
theorem B335117 : Blo 263822 335117 := bbase (se 3 (by rfl) ⟨62834, by rfl⟩ : syracuseStep 335117 = 125669) (by norm_num)
theorem B400661 : Blo 263822 400661 := bbase (se 6 (by rfl) ⟨9390, by rfl⟩ : syracuseStep 400661 = 18781) (by norm_num)
theorem B597293 : Blo 263822 597293 := bbase (se 3 (by rfl) ⟨111992, by rfl⟩ : syracuseStep 597293 = 223985) (by norm_num)
theorem B400685 : Blo 263822 400685 := bbase (se 3 (by rfl) ⟨75128, by rfl⟩ : syracuseStep 400685 = 150257) (by norm_num)
theorem B335173 : Blo 263822 335173 := bbase (se 4 (by rfl) ⟨31422, by rfl⟩ : syracuseStep 335173 = 62845) (by norm_num)
theorem B400709 : Blo 263822 400709 := bbase (se 4 (by rfl) ⟨37566, by rfl⟩ : syracuseStep 400709 = 75133) (by norm_num)
theorem B400733 : Blo 263822 400733 := bbase (se 3 (by rfl) ⟨75137, by rfl⟩ : syracuseStep 400733 = 150275) (by norm_num)
theorem B597365 : Blo 263822 597365 := bbase (se 5 (by rfl) ⟨28001, by rfl⟩ : syracuseStep 597365 = 56003) (by norm_num)
theorem B400757 : Blo 263822 400757 := bbase (se 5 (by rfl) ⟨18785, by rfl⟩ : syracuseStep 400757 = 37571) (by norm_num)
theorem B400781 : Blo 263822 400781 := bbase (se 3 (by rfl) ⟨75146, by rfl⟩ : syracuseStep 400781 = 150293) (by norm_num)
theorem B335269 : Blo 263822 335269 := bbase (se 4 (by rfl) ⟨31431, by rfl⟩ : syracuseStep 335269 = 62863) (by norm_num)
theorem B400805 : Blo 263822 400805 := bbase (se 4 (by rfl) ⟨37575, by rfl⟩ : syracuseStep 400805 = 75151) (by norm_num)
theorem B597437 : Blo 263822 597437 := bbase (se 3 (by rfl) ⟨112019, by rfl⟩ : syracuseStep 597437 = 224039) (by norm_num)
theorem B400829 : Blo 263822 400829 := bbase (se 3 (by rfl) ⟨75155, by rfl⟩ : syracuseStep 400829 = 150311) (by norm_num)
theorem B400853 : Blo 263822 400853 := bbase (se 7 (by rfl) ⟨4697, by rfl⟩ : syracuseStep 400853 = 9395) (by norm_num)
theorem B400877 : Blo 263822 400877 := bbase (se 3 (by rfl) ⟨75164, by rfl⟩ : syracuseStep 400877 = 150329) (by norm_num)
theorem B564725 : Blo 263822 564725 := bbase (se 5 (by rfl) ⟨26471, by rfl⟩ : syracuseStep 564725 = 52943) (by norm_num)
theorem B597509 : Blo 263822 597509 := bbase (se 4 (by rfl) ⟨56016, by rfl⟩ : syracuseStep 597509 = 112033) (by norm_num)
theorem B400901 : Blo 263822 400901 := bbase (se 4 (by rfl) ⟨37584, by rfl⟩ : syracuseStep 400901 = 75169) (by norm_num)
theorem B400925 : Blo 263822 400925 := bbase (se 3 (by rfl) ⟨75173, by rfl⟩ : syracuseStep 400925 = 150347) (by norm_num)
theorem B400949 : Blo 263822 400949 := bbase (se 5 (by rfl) ⟨18794, by rfl⟩ : syracuseStep 400949 = 37589) (by norm_num)
theorem B597581 : Blo 263822 597581 := bbase (se 3 (by rfl) ⟨112046, by rfl⟩ : syracuseStep 597581 = 224093) (by norm_num)
theorem B400973 : Blo 263822 400973 := bbase (se 3 (by rfl) ⟨75182, by rfl⟩ : syracuseStep 400973 = 150365) (by norm_num)
theorem B335441 : Blo 263822 335441 := bbase (se 2 (by rfl) ⟨125790, by rfl⟩ : syracuseStep 335441 = 251581) (by norm_num)
theorem B400997 : Blo 263822 400997 := bbase (se 4 (by rfl) ⟨37593, by rfl⟩ : syracuseStep 400997 = 75187) (by norm_num)
theorem B401021 : Blo 263822 401021 := bbase (se 3 (by rfl) ⟨75191, by rfl⟩ : syracuseStep 401021 = 150383) (by norm_num)
theorem B335497 : Blo 263822 335497 := bbase (se 2 (by rfl) ⟨125811, by rfl⟩ : syracuseStep 335497 = 251623) (by norm_num)
theorem B892565 : Blo 263822 892565 := bbase (se 6 (by rfl) ⟨20919, by rfl⟩ : syracuseStep 892565 = 41839) (by norm_num)
theorem B597653 : Blo 263822 597653 := bbase (se 6 (by rfl) ⟨14007, by rfl⟩ : syracuseStep 597653 = 28015) (by norm_num)
theorem B401045 : Blo 263822 401045 := bbase (se 6 (by rfl) ⟨9399, by rfl⟩ : syracuseStep 401045 = 18799) (by norm_num)
theorem B401069 : Blo 263822 401069 := bbase (se 3 (by rfl) ⟨75200, by rfl⟩ : syracuseStep 401069 = 150401) (by norm_num)
theorem B401093 : Blo 263822 401093 := bbase (se 4 (by rfl) ⟨37602, by rfl⟩ : syracuseStep 401093 = 75205) (by norm_num)
theorem B597725 : Blo 263822 597725 := bbase (se 3 (by rfl) ⟨112073, by rfl⟩ : syracuseStep 597725 = 224147) (by norm_num)
theorem B401117 : Blo 263822 401117 := bbase (se 3 (by rfl) ⟨75209, by rfl⟩ : syracuseStep 401117 = 150419) (by norm_num)
theorem B335593 : Blo 263822 335593 := bbase (se 2 (by rfl) ⟨125847, by rfl⟩ : syracuseStep 335593 = 251695) (by norm_num)
theorem B401141 : Blo 263822 401141 := bbase (se 5 (by rfl) ⟨18803, by rfl⟩ : syracuseStep 401141 = 37607) (by norm_num)
theorem B401165 : Blo 263822 401165 := bbase (se 3 (by rfl) ⟨75218, by rfl⟩ : syracuseStep 401165 = 150437) (by norm_num)
theorem B1154837 : Blo 263822 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B597797 : Blo 263822 597797 := bbase (se 4 (by rfl) ⟨56043, by rfl⟩ : syracuseStep 597797 = 112087) (by norm_num)
theorem B401189 : Blo 263822 401189 := bbase (se 4 (by rfl) ⟨37611, by rfl⟩ : syracuseStep 401189 = 75223) (by norm_num)
theorem B401213 : Blo 263822 401213 := bbase (se 3 (by rfl) ⟨75227, by rfl⟩ : syracuseStep 401213 = 150455) (by norm_num)
theorem B761669 : Blo 263822 761669 := bbase (se 4 (by rfl) ⟨71406, by rfl⟩ : syracuseStep 761669 = 142813) (by norm_num)
theorem B401237 : Blo 263822 401237 := bbase (se 9 (by rfl) ⟨1175, by rfl⟩ : syracuseStep 401237 = 2351) (by norm_num)
theorem B597869 : Blo 263822 597869 := bbase (se 3 (by rfl) ⟨112100, by rfl⟩ : syracuseStep 597869 = 224201) (by norm_num)
theorem B401261 : Blo 263822 401261 := bbase (se 3 (by rfl) ⟨75236, by rfl⟩ : syracuseStep 401261 = 150473) (by norm_num)
theorem B761717 : Blo 263822 761717 := bbase (se 5 (by rfl) ⟨35705, by rfl⟩ : syracuseStep 761717 = 71411) (by norm_num)
theorem B270197 : Blo 263822 270197 := bbase (se 5 (by rfl) ⟨12665, by rfl⟩ : syracuseStep 270197 = 25331) (by norm_num)
theorem B401285 : Blo 263822 401285 := bbase (se 4 (by rfl) ⟨37620, by rfl⟩ : syracuseStep 401285 = 75241) (by norm_num)
theorem B335765 : Blo 263822 335765 := bbase (se 6 (by rfl) ⟨7869, by rfl⟩ : syracuseStep 335765 = 15739) (by norm_num)
theorem B303005 : Blo 263822 303005 := bbase (se 3 (by rfl) ⟨56813, by rfl⟩ : syracuseStep 303005 = 113627) (by norm_num)
theorem B401309 : Blo 263822 401309 := bbase (se 3 (by rfl) ⟨75245, by rfl⟩ : syracuseStep 401309 = 150491) (by norm_num)
theorem B597941 : Blo 263822 597941 := bbase (se 5 (by rfl) ⟨28028, by rfl⟩ : syracuseStep 597941 = 56057) (by norm_num)
theorem B401333 : Blo 263822 401333 := bbase (se 5 (by rfl) ⟨18812, by rfl⟩ : syracuseStep 401333 = 37625) (by norm_num)
theorem B335821 : Blo 263822 335821 := bbase (se 3 (by rfl) ⟨62966, by rfl⟩ : syracuseStep 335821 = 125933) (by norm_num)
theorem B401357 : Blo 263822 401357 := bbase (se 3 (by rfl) ⟨75254, by rfl⟩ : syracuseStep 401357 = 150509) (by norm_num)
theorem B401381 : Blo 263822 401381 := bbase (se 4 (by rfl) ⟨37629, by rfl⟩ : syracuseStep 401381 = 75259) (by norm_num)
theorem B1220597 : Blo 263822 1220597 := bbase (se 5 (by rfl) ⟨57215, by rfl⟩ : syracuseStep 1220597 = 114431) (by norm_num)
theorem B598013 : Blo 263822 598013 := bbase (se 3 (by rfl) ⟨112127, by rfl⟩ : syracuseStep 598013 = 224255) (by norm_num)
theorem B401405 : Blo 263822 401405 := bbase (se 3 (by rfl) ⟨75263, by rfl⟩ : syracuseStep 401405 = 150527) (by norm_num)
theorem B401429 : Blo 263822 401429 := bbase (se 6 (by rfl) ⟨9408, by rfl⟩ : syracuseStep 401429 = 18817) (by norm_num)
theorem B335917 : Blo 263822 335917 := bbase (se 3 (by rfl) ⟨62984, by rfl⟩ : syracuseStep 335917 = 125969) (by norm_num)
theorem B401453 : Blo 263822 401453 := bbase (se 3 (by rfl) ⟨75272, by rfl⟩ : syracuseStep 401453 = 150545) (by norm_num)
theorem B892997 : Blo 263822 892997 := bbase (se 4 (by rfl) ⟨83718, by rfl⟩ : syracuseStep 892997 = 167437) (by norm_num)
theorem B598085 : Blo 263822 598085 := bbase (se 4 (by rfl) ⟨56070, by rfl⟩ : syracuseStep 598085 = 112141) (by norm_num)
theorem B401477 : Blo 263822 401477 := bbase (se 4 (by rfl) ⟨37638, by rfl⟩ : syracuseStep 401477 = 75277) (by norm_num)
theorem B270425 : Blo 263822 270425 := bbase (se 2 (by rfl) ⟨101409, by rfl⟩ : syracuseStep 270425 = 202819) (by norm_num)
theorem B401501 : Blo 263822 401501 := bbase (se 3 (by rfl) ⟨75281, by rfl⟩ : syracuseStep 401501 = 150563) (by norm_num)
theorem B401525 : Blo 263822 401525 := bbase (se 5 (by rfl) ⟨18821, by rfl⟩ : syracuseStep 401525 = 37643) (by norm_num)
theorem B598157 : Blo 263822 598157 := bbase (se 3 (by rfl) ⟨112154, by rfl⟩ : syracuseStep 598157 = 224309) (by norm_num)
theorem B401549 : Blo 263822 401549 := bbase (se 3 (by rfl) ⟨75290, by rfl⟩ : syracuseStep 401549 = 150581) (by norm_num)
theorem B401573 : Blo 263822 401573 := bbase (se 4 (by rfl) ⟨37647, by rfl⟩ : syracuseStep 401573 = 75295) (by norm_num)
theorem B401597 : Blo 263822 401597 := bbase (se 3 (by rfl) ⟨75299, by rfl⟩ : syracuseStep 401597 = 150599) (by norm_num)
theorem B598229 : Blo 263822 598229 := bbase (se 7 (by rfl) ⟨7010, by rfl⟩ : syracuseStep 598229 = 14021) (by norm_num)
theorem B401621 : Blo 263822 401621 := bbase (se 7 (by rfl) ⟨4706, by rfl⟩ : syracuseStep 401621 = 9413) (by norm_num)
theorem B336089 : Blo 263822 336089 := bbase (se 2 (by rfl) ⟨126033, by rfl⟩ : syracuseStep 336089 = 252067) (by norm_num)
theorem B401645 : Blo 263822 401645 := bbase (se 3 (by rfl) ⟨75308, by rfl⟩ : syracuseStep 401645 = 150617) (by norm_num)
theorem B401669 : Blo 263822 401669 := bbase (se 4 (by rfl) ⟨37656, by rfl⟩ : syracuseStep 401669 = 75313) (by norm_num)
theorem B336145 : Blo 263822 336145 := bbase (se 2 (by rfl) ⟨126054, by rfl⟩ : syracuseStep 336145 = 252109) (by norm_num)
theorem B598301 : Blo 263822 598301 := bbase (se 3 (by rfl) ⟨112181, by rfl⟩ : syracuseStep 598301 = 224363) (by norm_num)
theorem B401693 : Blo 263822 401693 := bbase (se 3 (by rfl) ⟨75317, by rfl⟩ : syracuseStep 401693 = 150635) (by norm_num)
theorem B401717 : Blo 263822 401717 := bbase (se 5 (by rfl) ⟨18830, by rfl⟩ : syracuseStep 401717 = 37661) (by norm_num)
theorem B303421 : Blo 263822 303421 := bbase (se 3 (by rfl) ⟨56891, by rfl⟩ : syracuseStep 303421 = 113783) (by norm_num)
theorem B598373 : Blo 263822 598373 := bbase (se 4 (by rfl) ⟨56097, by rfl⟩ : syracuseStep 598373 = 112195) (by norm_num)
theorem B336241 : Blo 263822 336241 := bbase (se 2 (by rfl) ⟨126090, by rfl⟩ : syracuseStep 336241 = 252181) (by norm_num)
theorem B1286549 : Blo 263822 1286549 := bbase (se 6 (by rfl) ⟨30153, by rfl⟩ : syracuseStep 1286549 = 60307) (by norm_num)
theorem B270757 : Blo 263822 270757 := bbase (se 4 (by rfl) ⟨25383, by rfl⟩ : syracuseStep 270757 = 50767) (by norm_num)
theorem B598445 : Blo 263822 598445 := bbase (se 3 (by rfl) ⟨112208, by rfl⟩ : syracuseStep 598445 = 224417) (by norm_num)
theorem B893429 : Blo 263822 893429 := bbase (se 5 (by rfl) ⟨41879, by rfl⟩ : syracuseStep 893429 = 83759) (by norm_num)
theorem B598517 : Blo 263822 598517 := bbase (se 5 (by rfl) ⟨28055, by rfl⟩ : syracuseStep 598517 = 56111) (by norm_num)
theorem B1352213 : Blo 263822 1352213 := bbase (se 6 (by rfl) ⟨31692, by rfl⟩ : syracuseStep 1352213 = 63385) (by norm_num)
theorem B336413 : Blo 263822 336413 := bbase (se 3 (by rfl) ⟨63077, by rfl⟩ : syracuseStep 336413 = 126155) (by norm_num)
theorem B598589 : Blo 263822 598589 := bbase (se 3 (by rfl) ⟨112235, by rfl⟩ : syracuseStep 598589 = 224471) (by norm_num)
theorem B336469 : Blo 263822 336469 := bbase (se 8 (by rfl) ⟨1971, by rfl⟩ : syracuseStep 336469 = 3943) (by norm_num)
theorem B402013 : Blo 263822 402013 := bbase (se 3 (by rfl) ⟨75377, by rfl⟩ : syracuseStep 402013 = 150755) (by norm_num)
theorem B598661 : Blo 263822 598661 := bbase (se 4 (by rfl) ⟨56124, by rfl⟩ : syracuseStep 598661 = 112249) (by norm_num)
theorem B336565 : Blo 263822 336565 := bbase (se 5 (by rfl) ⟨15776, by rfl⟩ : syracuseStep 336565 = 31553) (by norm_num)
theorem B598733 : Blo 263822 598733 := bbase (se 3 (by rfl) ⟨112262, by rfl⟩ : syracuseStep 598733 = 224525) (by norm_num)
theorem B271073 : Blo 263822 271073 := bbase (se 2 (by rfl) ⟨101652, by rfl⟩ : syracuseStep 271073 = 203305) (by norm_num)
theorem B303845 : Blo 263822 303845 := bbase (se 4 (by rfl) ⟨28485, by rfl⟩ : syracuseStep 303845 = 56971) (by norm_num)
theorem B598805 : Blo 263822 598805 := bbase (se 6 (by rfl) ⟨14034, by rfl⟩ : syracuseStep 598805 = 28069) (by norm_num)
theorem B598877 : Blo 263822 598877 := bbase (se 3 (by rfl) ⟨112289, by rfl⟩ : syracuseStep 598877 = 224579) (by norm_num)
theorem B336737 : Blo 263822 336737 := bbase (se 2 (by rfl) ⟨126276, by rfl⟩ : syracuseStep 336737 = 252553) (by norm_num)
theorem B336793 : Blo 263822 336793 := bbase (se 2 (by rfl) ⟨126297, by rfl⟩ : syracuseStep 336793 = 252595) (by norm_num)
theorem B893861 : Blo 263822 893861 := bbase (se 4 (by rfl) ⟨83799, by rfl⟩ : syracuseStep 893861 = 167599) (by norm_num)
theorem B598949 : Blo 263822 598949 := bbase (se 4 (by rfl) ⟨56151, by rfl⟩ : syracuseStep 598949 = 112303) (by norm_num)
theorem B599021 : Blo 263822 599021 := bbase (se 3 (by rfl) ⟨112316, by rfl⟩ : syracuseStep 599021 = 224633) (by norm_num)
theorem B336889 : Blo 263822 336889 := bbase (se 2 (by rfl) ⟨126333, by rfl⟩ : syracuseStep 336889 = 252667) (by norm_num)
theorem B599093 : Blo 263822 599093 := bbase (se 5 (by rfl) ⟨28082, by rfl⟩ : syracuseStep 599093 = 56165) (by norm_num)
theorem B566365 : Blo 263822 566365 := bbase (se 3 (by rfl) ⟨106193, by rfl⟩ : syracuseStep 566365 = 212387) (by norm_num)
theorem B599165 : Blo 263822 599165 := bbase (se 3 (by rfl) ⟨112343, by rfl⟩ : syracuseStep 599165 = 224687) (by norm_num)
theorem B271517 : Blo 263822 271517 := bbase (se 3 (by rfl) ⟨50909, by rfl⟩ : syracuseStep 271517 = 101819) (by norm_num)
theorem B337061 : Blo 263822 337061 := bbase (se 4 (by rfl) ⟨31599, by rfl⟩ : syracuseStep 337061 = 63199) (by norm_num)
theorem B828613 : Blo 263822 828613 := bbase (se 4 (by rfl) ⟨77682, by rfl⟩ : syracuseStep 828613 = 155365) (by norm_num)
theorem B599237 : Blo 263822 599237 := bbase (se 4 (by rfl) ⟨56178, by rfl⟩ : syracuseStep 599237 = 112357) (by norm_num)
theorem B304337 : Blo 263822 304337 := bbase (se 2 (by rfl) ⟨114126, by rfl⟩ : syracuseStep 304337 = 228253) (by norm_num)
theorem B337117 : Blo 263822 337117 := bbase (se 3 (by rfl) ⟨63209, by rfl⟩ : syracuseStep 337117 = 126419) (by norm_num)
theorem B501005 : Blo 263822 501005 := bbase (se 3 (by rfl) ⟨93938, by rfl⟩ : syracuseStep 501005 = 187877) (by norm_num)
theorem B599309 : Blo 263822 599309 := bbase (se 3 (by rfl) ⟨112370, by rfl⟩ : syracuseStep 599309 = 224741) (by norm_num)
theorem B337213 : Blo 263822 337213 := bbase (se 3 (by rfl) ⟨63227, by rfl⟩ : syracuseStep 337213 = 126455) (by norm_num)
theorem B304465 : Blo 263822 304465 := bbase (se 2 (by rfl) ⟨114174, by rfl⟩ : syracuseStep 304465 = 228349) (by norm_num)
theorem B894293 : Blo 263822 894293 := bbase (se 12 (by rfl) ⟨327, by rfl⟩ : syracuseStep 894293 = 655) (by norm_num)
theorem B599381 : Blo 263822 599381 := bbase (se 12 (by rfl) ⟨219, by rfl⟩ : syracuseStep 599381 = 439) (by norm_num)
theorem B599453 : Blo 263822 599453 := bbase (se 3 (by rfl) ⟨112397, by rfl⟩ : syracuseStep 599453 = 224795) (by norm_num)
theorem B501157 : Blo 263822 501157 := bbase (se 4 (by rfl) ⟨46983, by rfl⟩ : syracuseStep 501157 = 93967) (by norm_num)
theorem B2565557 : Blo 263822 2565557 := bbase (se 5 (by rfl) ⟨120260, by rfl⟩ : syracuseStep 2565557 = 240521) (by norm_num)
theorem B599525 : Blo 263822 599525 := bbase (se 4 (by rfl) ⟨56205, by rfl⟩ : syracuseStep 599525 = 112411) (by norm_num)
theorem B337385 : Blo 263822 337385 := bbase (se 2 (by rfl) ⟨126519, by rfl⟩ : syracuseStep 337385 = 253039) (by norm_num)
theorem B337441 : Blo 263822 337441 := bbase (se 2 (by rfl) ⟨126540, by rfl⟩ : syracuseStep 337441 = 253081) (by norm_num)
theorem B599597 : Blo 263822 599597 := bbase (se 3 (by rfl) ⟨112424, by rfl⟩ : syracuseStep 599597 = 224849) (by norm_num)
theorem B599669 : Blo 263822 599669 := bbase (se 5 (by rfl) ⟨28109, by rfl⟩ : syracuseStep 599669 = 56219) (by norm_num)
theorem B337537 : Blo 263822 337537 := bbase (se 2 (by rfl) ⟨126576, by rfl⟩ : syracuseStep 337537 = 253153) (by norm_num)
theorem B599741 : Blo 263822 599741 := bbase (se 3 (by rfl) ⟨112451, by rfl⟩ : syracuseStep 599741 = 224903) (by norm_num)
theorem B501461 : Blo 263822 501461 := bbase (se 7 (by rfl) ⟨5876, by rfl⟩ : syracuseStep 501461 = 11753) (by norm_num)
theorem B894725 : Blo 263822 894725 := bbase (se 4 (by rfl) ⟨83880, by rfl⟩ : syracuseStep 894725 = 167761) (by norm_num)
theorem B599813 : Blo 263822 599813 := bbase (se 4 (by rfl) ⟨56232, by rfl⟩ : syracuseStep 599813 = 112465) (by norm_num)
theorem B304921 : Blo 263822 304921 := bbase (se 2 (by rfl) ⟨114345, by rfl⟩ : syracuseStep 304921 = 228691) (by norm_num)
theorem B1353509 : Blo 263822 1353509 := bbase (se 4 (by rfl) ⟨126891, by rfl⟩ : syracuseStep 1353509 = 253783) (by norm_num)
theorem B337709 : Blo 263822 337709 := bbase (se 3 (by rfl) ⟨63320, by rfl⟩ : syracuseStep 337709 = 126641) (by norm_num)
theorem B599885 : Blo 263822 599885 := bbase (se 3 (by rfl) ⟨112478, by rfl⟩ : syracuseStep 599885 = 224957) (by norm_num)
theorem B337765 : Blo 263822 337765 := bbase (se 4 (by rfl) ⟨31665, by rfl⟩ : syracuseStep 337765 = 63331) (by norm_num)
theorem B1615733 : Blo 263822 1615733 := bbase (se 5 (by rfl) ⟨75737, by rfl⟩ : syracuseStep 1615733 = 151475) (by norm_num)
theorem B599957 : Blo 263822 599957 := bbase (se 6 (by rfl) ⟨14061, by rfl⟩ : syracuseStep 599957 = 28123) (by norm_num)
theorem B337861 : Blo 263822 337861 := bbase (se 4 (by rfl) ⟨31674, by rfl⟩ : syracuseStep 337861 = 63349) (by norm_num)
theorem B567253 : Blo 263822 567253 := bbase (se 7 (by rfl) ⟨6647, by rfl⟩ : syracuseStep 567253 = 13295) (by norm_num)
theorem B600029 : Blo 263822 600029 := bbase (se 3 (by rfl) ⟨112505, by rfl⟩ : syracuseStep 600029 = 225011) (by norm_num)
theorem B600101 : Blo 263822 600101 := bbase (se 4 (by rfl) ⟨56259, by rfl⟩ : syracuseStep 600101 = 112519) (by norm_num)
theorem B305213 : Blo 263822 305213 := bbase (se 3 (by rfl) ⟨57227, by rfl⟩ : syracuseStep 305213 = 114455) (by norm_num)
theorem B305249 : Blo 263822 305249 := bbase (se 2 (by rfl) ⟨114468, by rfl⟩ : syracuseStep 305249 = 228937) (by norm_num)
theorem B764005 : Blo 263822 764005 := bbase (se 4 (by rfl) ⟨71625, by rfl⟩ : syracuseStep 764005 = 143251) (by norm_num)
theorem B600173 : Blo 263822 600173 := bbase (se 3 (by rfl) ⟨112532, by rfl⟩ : syracuseStep 600173 = 225065) (by norm_num)
theorem B338033 : Blo 263822 338033 := bbase (se 2 (by rfl) ⟨126762, by rfl⟩ : syracuseStep 338033 = 253525) (by norm_num)
theorem B338089 : Blo 263822 338089 := bbase (se 2 (by rfl) ⟨126783, by rfl⟩ : syracuseStep 338089 = 253567) (by norm_num)
theorem B895157 : Blo 263822 895157 := bbase (se 5 (by rfl) ⟨41960, by rfl⟩ : syracuseStep 895157 = 83921) (by norm_num)
theorem B600245 : Blo 263822 600245 := bbase (se 5 (by rfl) ⟨28136, by rfl⟩ : syracuseStep 600245 = 56273) (by norm_num)
theorem B403685 : Blo 263822 403685 := bbase (se 4 (by rfl) ⟨37845, by rfl⟩ : syracuseStep 403685 = 75691) (by norm_num)
theorem B600317 : Blo 263822 600317 := bbase (se 3 (by rfl) ⟨112559, by rfl⟩ : syracuseStep 600317 = 225119) (by norm_num)
theorem B338185 : Blo 263822 338185 := bbase (se 2 (by rfl) ⟨126819, by rfl⟩ : syracuseStep 338185 = 253639) (by norm_num)
theorem B600389 : Blo 263822 600389 := bbase (se 4 (by rfl) ⟨56286, by rfl⟩ : syracuseStep 600389 = 112573) (by norm_num)
theorem B600461 : Blo 263822 600461 := bbase (se 3 (by rfl) ⟨112586, by rfl⟩ : syracuseStep 600461 = 225173) (by norm_num)
theorem B338357 : Blo 263822 338357 := bbase (se 5 (by rfl) ⟨15860, by rfl⟩ : syracuseStep 338357 = 31721) (by norm_num)
theorem B502213 : Blo 263822 502213 := bbase (se 4 (by rfl) ⟨47082, by rfl⟩ : syracuseStep 502213 = 94165) (by norm_num)
theorem B567749 : Blo 263822 567749 := bbase (se 4 (by rfl) ⟨53226, by rfl⟩ : syracuseStep 567749 = 106453) (by norm_num)
theorem B600533 : Blo 263822 600533 := bbase (se 7 (by rfl) ⟨7037, by rfl⟩ : syracuseStep 600533 = 14075) (by norm_num)
theorem B338413 : Blo 263822 338413 := bbase (se 3 (by rfl) ⟨63452, by rfl⟩ : syracuseStep 338413 = 126905) (by norm_num)
theorem B600605 : Blo 263822 600605 := bbase (se 3 (by rfl) ⟨112613, by rfl⟩ : syracuseStep 600605 = 225227) (by norm_num)
theorem B338509 : Blo 263822 338509 := bbase (se 3 (by rfl) ⟨63470, by rfl⟩ : syracuseStep 338509 = 126941) (by norm_num)
theorem B502357 : Blo 263822 502357 := bbase (se 8 (by rfl) ⟨2943, by rfl⟩ : syracuseStep 502357 = 5887) (by norm_num)
theorem B895589 : Blo 263822 895589 := bbase (se 4 (by rfl) ⟨83961, by rfl⟩ : syracuseStep 895589 = 167923) (by norm_num)
theorem B600677 : Blo 263822 600677 := bbase (se 4 (by rfl) ⟨56313, by rfl⟩ : syracuseStep 600677 = 112627) (by norm_num)
theorem B600749 : Blo 263822 600749 := bbase (se 3 (by rfl) ⟨112640, by rfl⟩ : syracuseStep 600749 = 225281) (by norm_num)
theorem B502517 : Blo 263822 502517 := bbase (se 5 (by rfl) ⟨23555, by rfl⟩ : syracuseStep 502517 = 47111) (by norm_num)
theorem B600821 : Blo 263822 600821 := bbase (se 5 (by rfl) ⟨28163, by rfl⟩ : syracuseStep 600821 = 56327) (by norm_num)
theorem B338681 : Blo 263822 338681 := bbase (se 2 (by rfl) ⟨127005, by rfl⟩ : syracuseStep 338681 = 254011) (by norm_num)
theorem B338737 : Blo 263822 338737 := bbase (se 2 (by rfl) ⟨127026, by rfl⟩ : syracuseStep 338737 = 254053) (by norm_num)
theorem B600893 : Blo 263822 600893 := bbase (se 3 (by rfl) ⟨112667, by rfl⟩ : syracuseStep 600893 = 225335) (by norm_num)
theorem B600965 : Blo 263822 600965 := bbase (se 4 (by rfl) ⟨56340, by rfl⟩ : syracuseStep 600965 = 112681) (by norm_num)
theorem B502661 : Blo 263822 502661 := bbase (se 4 (by rfl) ⟨47124, by rfl⟩ : syracuseStep 502661 = 94249) (by norm_num)
theorem B338833 : Blo 263822 338833 := bbase (se 2 (by rfl) ⟨127062, by rfl⟩ : syracuseStep 338833 = 254125) (by norm_num)
theorem B601037 : Blo 263822 601037 := bbase (se 3 (by rfl) ⟨112694, by rfl⟩ : syracuseStep 601037 = 225389) (by norm_num)
theorem B896021 : Blo 263822 896021 := bbase (se 6 (by rfl) ⟨21000, by rfl⟩ : syracuseStep 896021 = 42001) (by norm_num)
theorem B601109 : Blo 263822 601109 := bbase (se 6 (by rfl) ⟨14088, by rfl⟩ : syracuseStep 601109 = 28177) (by norm_num)
theorem B1354805 : Blo 263822 1354805 := bbase (se 5 (by rfl) ⟨63506, by rfl⟩ : syracuseStep 1354805 = 127013) (by norm_num)
theorem B601181 : Blo 263822 601181 := bbase (se 3 (by rfl) ⟨112721, by rfl⟩ : syracuseStep 601181 = 225443) (by norm_num)
theorem B502949 : Blo 263822 502949 := bbase (se 4 (by rfl) ⟨47151, by rfl⟩ : syracuseStep 502949 = 94303) (by norm_num)
theorem B601253 : Blo 263822 601253 := bbase (se 4 (by rfl) ⟨56367, by rfl⟩ : syracuseStep 601253 = 112735) (by norm_num)
theorem B535781 : Blo 263822 535781 := bbase (se 4 (by rfl) ⟨50229, by rfl⟩ : syracuseStep 535781 = 100459) (by norm_num)
theorem B601325 : Blo 263822 601325 := bbase (se 3 (by rfl) ⟨112748, by rfl⟩ : syracuseStep 601325 = 225497) (by norm_num)
theorem B568613 : Blo 263822 568613 := bbase (se 4 (by rfl) ⟨53307, by rfl⟩ : syracuseStep 568613 = 106615) (by norm_num)
theorem B535853 : Blo 263822 535853 := bbase (se 3 (by rfl) ⟨100472, by rfl⟩ : syracuseStep 535853 = 200945) (by norm_num)
theorem B601397 : Blo 263822 601397 := bbase (se 5 (by rfl) ⟨28190, by rfl⟩ : syracuseStep 601397 = 56381) (by norm_num)
theorem B503101 : Blo 263822 503101 := bbase (se 3 (by rfl) ⟨94331, by rfl⟩ : syracuseStep 503101 = 188663) (by norm_num)
theorem B601469 : Blo 263822 601469 := bbase (se 3 (by rfl) ⟨112775, by rfl⟩ : syracuseStep 601469 = 225551) (by norm_num)
theorem B568757 : Blo 263822 568757 := bbase (se 5 (by rfl) ⟨26660, by rfl⟩ : syracuseStep 568757 = 53321) (by norm_num)
theorem B896453 : Blo 263822 896453 := bbase (se 4 (by rfl) ⟨84042, by rfl⟩ : syracuseStep 896453 = 168085) (by norm_num)
theorem B601541 : Blo 263822 601541 := bbase (se 4 (by rfl) ⟨56394, by rfl⟩ : syracuseStep 601541 = 112789) (by norm_num)
theorem B2010581 : Blo 263822 2010581 := bbase (se 7 (by rfl) ⟨23561, by rfl⟩ : syracuseStep 2010581 = 47123) (by norm_num)
theorem B1027541 : Blo 263822 1027541 := bbase (se 7 (by rfl) ⟨12041, by rfl⟩ : syracuseStep 1027541 = 24083) (by norm_num)
theorem B601613 : Blo 263822 601613 := bbase (se 3 (by rfl) ⟨112802, by rfl⟩ : syracuseStep 601613 = 225605) (by norm_num)
theorem B831061 : Blo 263822 831061 := bbase (se 8 (by rfl) ⟨4869, by rfl⟩ : syracuseStep 831061 = 9739) (by norm_num)
theorem B10923605 : Blo 263822 10923605 := bbase (se 8 (by rfl) ⟨64005, by rfl⟩ : syracuseStep 10923605 = 128011) (by norm_num)
theorem B601685 : Blo 263822 601685 := bbase (se 8 (by rfl) ⟨3525, by rfl⟩ : syracuseStep 601685 = 7051) (by norm_num)
theorem B503405 : Blo 263822 503405 := bbase (se 3 (by rfl) ⟨94388, by rfl⟩ : syracuseStep 503405 = 188777) (by norm_num)
theorem B601757 : Blo 263822 601757 := bbase (se 3 (by rfl) ⟨112829, by rfl⟩ : syracuseStep 601757 = 225659) (by norm_num)
theorem B1814197 : Blo 263822 1814197 := bbase (se 5 (by rfl) ⟨85040, by rfl⟩ : syracuseStep 1814197 = 170081) (by norm_num)
theorem B601829 : Blo 263822 601829 := bbase (se 4 (by rfl) ⟨56421, by rfl⟩ : syracuseStep 601829 = 112843) (by norm_num)
theorem B601901 : Blo 263822 601901 := bbase (se 3 (by rfl) ⟨112856, by rfl⟩ : syracuseStep 601901 = 225713) (by norm_num)
theorem B896885 : Blo 263822 896885 := bbase (se 5 (by rfl) ⟨42041, by rfl⟩ : syracuseStep 896885 = 84083) (by norm_num)
theorem B601973 : Blo 263822 601973 := bbase (se 5 (by rfl) ⟨28217, by rfl⟩ : syracuseStep 601973 = 56435) (by norm_num)
theorem B602045 : Blo 263822 602045 := bbase (se 3 (by rfl) ⟨112883, by rfl⟩ : syracuseStep 602045 = 225767) (by norm_num)
theorem B602117 : Blo 263822 602117 := bbase (se 4 (by rfl) ⟨56448, by rfl⟩ : syracuseStep 602117 = 112897) (by norm_num)
theorem B602189 : Blo 263822 602189 := bbase (se 3 (by rfl) ⟨112910, by rfl⟩ : syracuseStep 602189 = 225821) (by norm_num)
theorem B602261 : Blo 263822 602261 := bbase (se 6 (by rfl) ⟨14115, by rfl⟩ : syracuseStep 602261 = 28231) (by norm_num)
theorem B569501 : Blo 263822 569501 := bbase (se 3 (by rfl) ⟨106781, by rfl⟩ : syracuseStep 569501 = 213563) (by norm_num)
theorem B1519829 : Blo 263822 1519829 := bbase (se 7 (by rfl) ⟨17810, by rfl⟩ : syracuseStep 1519829 = 35621) (by norm_num)
theorem B602333 : Blo 263822 602333 := bbase (se 3 (by rfl) ⟨112937, by rfl⟩ : syracuseStep 602333 = 225875) (by norm_num)
theorem B667885 : Blo 263822 667885 := bbase (se 3 (by rfl) ⟨125228, by rfl⟩ : syracuseStep 667885 = 250457) (by norm_num)
theorem B897317 : Blo 263822 897317 := bbase (se 4 (by rfl) ⟨84123, by rfl⟩ : syracuseStep 897317 = 168247) (by norm_num)
theorem B602405 : Blo 263822 602405 := bbase (se 4 (by rfl) ⟨56475, by rfl⟩ : syracuseStep 602405 = 112951) (by norm_num)
theorem B667997 : Blo 263822 667997 := bbase (se 3 (by rfl) ⟨125249, by rfl⟩ : syracuseStep 667997 = 250499) (by norm_num)
theorem B504157 : Blo 263822 504157 := bbase (se 3 (by rfl) ⟨94529, by rfl⟩ : syracuseStep 504157 = 189059) (by norm_num)
theorem B602477 : Blo 263822 602477 := bbase (se 3 (by rfl) ⟨112964, by rfl⟩ : syracuseStep 602477 = 225929) (by norm_num)
theorem B307585 : Blo 263822 307585 := bbase (se 2 (by rfl) ⟨115344, by rfl⟩ : syracuseStep 307585 = 230689) (by norm_num)
theorem B602549 : Blo 263822 602549 := bbase (se 5 (by rfl) ⟨28244, by rfl⟩ : syracuseStep 602549 = 56489) (by norm_num)
theorem B340409 : Blo 263822 340409 := bbase (se 2 (by rfl) ⟨127653, by rfl⟩ : syracuseStep 340409 = 255307) (by norm_num)
theorem B340445 : Blo 263822 340445 := bbase (se 3 (by rfl) ⟨63833, by rfl⟩ : syracuseStep 340445 = 127667) (by norm_num)
theorem B504301 : Blo 263822 504301 := bbase (se 3 (by rfl) ⟨94556, by rfl⟩ : syracuseStep 504301 = 189113) (by norm_num)
theorem B3650069 : Blo 263822 3650069 := bbase (se 6 (by rfl) ⟨85548, by rfl⟩ : syracuseStep 3650069 = 171097) (by norm_num)
theorem B668189 : Blo 263822 668189 := bbase (se 3 (by rfl) ⟨125285, by rfl⟩ : syracuseStep 668189 = 250571) (by norm_num)
theorem B504461 : Blo 263822 504461 := bbase (se 3 (by rfl) ⟨94586, by rfl⟩ : syracuseStep 504461 = 189173) (by norm_num)
theorem B1127125 : Blo 263822 1127125 := bbase (se 7 (by rfl) ⟨13208, by rfl⟩ : syracuseStep 1127125 = 26417) (by norm_num)
theorem B1913557 : Blo 263822 1913557 := bbase (se 7 (by rfl) ⟨22424, by rfl⟩ : syracuseStep 1913557 = 44849) (by norm_num)
theorem B897749 : Blo 263822 897749 := bbase (se 7 (by rfl) ⟨10520, by rfl⟩ : syracuseStep 897749 = 21041) (by norm_num)
theorem B504605 : Blo 263822 504605 := bbase (se 3 (by rfl) ⟨94613, by rfl⟩ : syracuseStep 504605 = 189227) (by norm_num)
theorem B963413 : Blo 263822 963413 := bbase (se 9 (by rfl) ⟨2822, by rfl⟩ : syracuseStep 963413 = 5645) (by norm_num)
theorem B668533 : Blo 263822 668533 := bbase (se 5 (by rfl) ⟨31337, by rfl⟩ : syracuseStep 668533 = 62675) (by norm_num)
theorem B570253 : Blo 263822 570253 := bbase (se 3 (by rfl) ⟨106922, by rfl⟩ : syracuseStep 570253 = 213845) (by norm_num)
theorem B668645 : Blo 263822 668645 := bbase (se 4 (by rfl) ⟨62685, by rfl⟩ : syracuseStep 668645 = 125371) (by norm_num)
theorem B406525 : Blo 263822 406525 := bbase (se 3 (by rfl) ⟨76223, by rfl⟩ : syracuseStep 406525 = 152447) (by norm_num)
theorem B570397 : Blo 263822 570397 := bbase (se 3 (by rfl) ⟨106949, by rfl⟩ : syracuseStep 570397 = 213899) (by norm_num)
theorem B504893 : Blo 263822 504893 := bbase (se 3 (by rfl) ⟨94667, by rfl⟩ : syracuseStep 504893 = 189335) (by norm_num)
theorem B341065 : Blo 263822 341065 := bbase (se 2 (by rfl) ⟨127899, by rfl⟩ : syracuseStep 341065 = 255799) (by norm_num)
theorem B898181 : Blo 263822 898181 := bbase (se 4 (by rfl) ⟨84204, by rfl⟩ : syracuseStep 898181 = 168409) (by norm_num)
theorem B668837 : Blo 263822 668837 := bbase (se 4 (by rfl) ⟨62703, by rfl⟩ : syracuseStep 668837 = 125407) (by norm_num)
theorem B505045 : Blo 263822 505045 := bbase (se 7 (by rfl) ⟨5918, by rfl⟩ : syracuseStep 505045 = 11837) (by norm_num)
theorem B963845 : Blo 263822 963845 := bbase (se 4 (by rfl) ⟨90360, by rfl⟩ : syracuseStep 963845 = 180721) (by norm_num)
theorem B865637 : Blo 263822 865637 := bbase (se 4 (by rfl) ⟨81153, by rfl⟩ : syracuseStep 865637 = 162307) (by norm_num)
theorem B636277 : Blo 263822 636277 := bbase (se 5 (by rfl) ⟨29825, by rfl⟩ : syracuseStep 636277 = 59651) (by norm_num)
theorem B570773 : Blo 263822 570773 := bbase (se 6 (by rfl) ⟨13377, by rfl⟩ : syracuseStep 570773 = 26755) (by norm_num)
theorem B603605 : Blo 263822 603605 := bbase (se 7 (by rfl) ⟨7073, by rfl⟩ : syracuseStep 603605 = 14147) (by norm_num)
theorem B538093 : Blo 263822 538093 := bbase (se 3 (by rfl) ⟨100892, by rfl⟩ : syracuseStep 538093 = 201785) (by norm_num)
theorem B669181 : Blo 263822 669181 := bbase (se 3 (by rfl) ⟨125471, by rfl⟩ : syracuseStep 669181 = 250943) (by norm_num)
theorem B505349 : Blo 263822 505349 := bbase (se 4 (by rfl) ⟨47376, by rfl⟩ : syracuseStep 505349 = 94753) (by norm_num)
theorem B898613 : Blo 263822 898613 := bbase (se 5 (by rfl) ⟨42122, by rfl⟩ : syracuseStep 898613 = 84245) (by norm_num)
theorem B669293 : Blo 263822 669293 := bbase (se 3 (by rfl) ⟨125492, by rfl⟩ : syracuseStep 669293 = 250985) (by norm_num)
theorem B407189 : Blo 263822 407189 := bbase (se 6 (by rfl) ⟨9543, by rfl⟩ : syracuseStep 407189 = 19087) (by norm_num)
theorem B571141 : Blo 263822 571141 := bbase (se 4 (by rfl) ⟨53544, by rfl⟩ : syracuseStep 571141 = 107089) (by norm_num)
theorem B669485 : Blo 263822 669485 := bbase (se 3 (by rfl) ⟨125528, by rfl⟩ : syracuseStep 669485 = 251057) (by norm_num)
theorem B636797 : Blo 263822 636797 := bbase (se 3 (by rfl) ⟨119399, by rfl⟩ : syracuseStep 636797 = 238799) (by norm_num)
theorem B6862805 : Blo 263822 6862805 := bbase (se 7 (by rfl) ⟨80423, by rfl⟩ : syracuseStep 6862805 = 160847) (by norm_num)
theorem B636893 : Blo 263822 636893 := bbase (se 3 (by rfl) ⟨119417, by rfl⟩ : syracuseStep 636893 = 238835) (by norm_num)
theorem B899045 : Blo 263822 899045 := bbase (se 4 (by rfl) ⟨84285, by rfl⟩ : syracuseStep 899045 = 168571) (by norm_num)
theorem B669829 : Blo 263822 669829 := bbase (se 4 (by rfl) ⟨62796, by rfl⟩ : syracuseStep 669829 = 125593) (by norm_num)
theorem B1128613 : Blo 263822 1128613 := bbase (se 4 (by rfl) ⟨105807, by rfl⟩ : syracuseStep 1128613 = 211615) (by norm_num)
theorem B1128629 : Blo 263822 1128629 := bbase (se 5 (by rfl) ⟨52904, by rfl⟩ : syracuseStep 1128629 = 105809) (by norm_num)
theorem B669941 : Blo 263822 669941 := bbase (se 5 (by rfl) ⟨31403, by rfl⟩ : syracuseStep 669941 = 62807) (by norm_num)
theorem B2275573 : Blo 263822 2275573 := bbase (se 5 (by rfl) ⟨106667, by rfl⟩ : syracuseStep 2275573 = 213335) (by norm_num)
theorem B506101 : Blo 263822 506101 := bbase (se 5 (by rfl) ⟨23723, by rfl⟩ : syracuseStep 506101 = 47447) (by norm_num)
theorem B506245 : Blo 263822 506245 := bbase (se 4 (by rfl) ⟨47460, by rfl⟩ : syracuseStep 506245 = 94921) (by norm_num)
theorem B899477 : Blo 263822 899477 := bbase (se 6 (by rfl) ⟨21081, by rfl⟩ : syracuseStep 899477 = 42163) (by norm_num)
theorem B670133 : Blo 263822 670133 := bbase (se 5 (by rfl) ⟨31412, by rfl⟩ : syracuseStep 670133 = 62825) (by norm_num)
theorem B506405 : Blo 263822 506405 := bbase (se 4 (by rfl) ⟨47475, by rfl⟩ : syracuseStep 506405 = 94951) (by norm_num)
theorem B1096325 : Blo 263822 1096325 := bbase (se 4 (by rfl) ⟨102780, by rfl⟩ : syracuseStep 1096325 = 205561) (by norm_num)
theorem B539293 : Blo 263822 539293 := bbase (se 3 (by rfl) ⟨101117, by rfl⟩ : syracuseStep 539293 = 202235) (by norm_num)
theorem B506549 : Blo 263822 506549 := bbase (se 5 (by rfl) ⟨23744, by rfl⟩ : syracuseStep 506549 = 47489) (by norm_num)
theorem B670477 : Blo 263822 670477 := bbase (se 3 (by rfl) ⟨125714, by rfl⟩ : syracuseStep 670477 = 251429) (by norm_num)
theorem B899909 : Blo 263822 899909 := bbase (se 4 (by rfl) ⟨84366, by rfl⟩ : syracuseStep 899909 = 168733) (by norm_num)
theorem B670589 : Blo 263822 670589 := bbase (se 3 (by rfl) ⟨125735, by rfl⟩ : syracuseStep 670589 = 251471) (by norm_num)
theorem B506837 : Blo 263822 506837 := bbase (se 7 (by rfl) ⟨5939, by rfl⟩ : syracuseStep 506837 = 11879) (by norm_num)
theorem B375845 : Blo 263822 375845 := bbase (se 4 (by rfl) ⟨35235, by rfl⟩ : syracuseStep 375845 = 70471) (by norm_num)
theorem B670781 : Blo 263822 670781 := bbase (se 3 (by rfl) ⟨125771, by rfl⟩ : syracuseStep 670781 = 251543) (by norm_num)
theorem B506989 : Blo 263822 506989 := bbase (se 3 (by rfl) ⟨95060, by rfl⟩ : syracuseStep 506989 = 190121) (by norm_num)
theorem B539893 : Blo 263822 539893 := bbase (se 5 (by rfl) ⟨25307, by rfl⟩ : syracuseStep 539893 = 50615) (by norm_num)
theorem B900341 : Blo 263822 900341 := bbase (se 5 (by rfl) ⟨42203, by rfl⟩ : syracuseStep 900341 = 84407) (by norm_num)
theorem B638237 : Blo 263822 638237 := bbase (se 3 (by rfl) ⟨119669, by rfl⟩ : syracuseStep 638237 = 239339) (by norm_num)
theorem B4078997 : Blo 263822 4078997 := bbase (se 6 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 4078997 = 191203) (by norm_num)
theorem B671125 : Blo 263822 671125 := bbase (se 6 (by rfl) ⟨15729, by rfl⟩ : syracuseStep 671125 = 31459) (by norm_num)
theorem B507293 : Blo 263822 507293 := bbase (se 3 (by rfl) ⟨95117, by rfl⟩ : syracuseStep 507293 = 190235) (by norm_num)
theorem B671237 : Blo 263822 671237 := bbase (se 4 (by rfl) ⟨62928, by rfl⟩ : syracuseStep 671237 = 125857) (by norm_num)
theorem B573053 : Blo 263822 573053 := bbase (se 3 (by rfl) ⟨107447, by rfl⟩ : syracuseStep 573053 = 214895) (by norm_num)
theorem B867989 : Blo 263822 867989 := bbase (se 6 (by rfl) ⟨20343, by rfl⟩ : syracuseStep 867989 = 40687) (by norm_num)
theorem B900773 : Blo 263822 900773 := bbase (se 4 (by rfl) ⟨84447, by rfl⟩ : syracuseStep 900773 = 168895) (by norm_num)
theorem B671429 : Blo 263822 671429 := bbase (se 4 (by rfl) ⟨62946, by rfl⟩ : syracuseStep 671429 = 125893) (by norm_num)
theorem B376597 : Blo 263822 376597 := bbase (se 6 (by rfl) ⟨8826, by rfl⟩ : syracuseStep 376597 = 17653) (by norm_num)
theorem B540589 : Blo 263822 540589 := bbase (se 3 (by rfl) ⟨101360, by rfl⟩ : syracuseStep 540589 = 202721) (by norm_num)
theorem B671773 : Blo 263822 671773 := bbase (se 3 (by rfl) ⟨125957, by rfl⟩ : syracuseStep 671773 = 251915) (by norm_num)
theorem B901205 : Blo 263822 901205 := bbase (se 8 (by rfl) ⟨5280, by rfl⟩ : syracuseStep 901205 = 10561) (by norm_num)
theorem B508045 : Blo 263822 508045 := bbase (se 3 (by rfl) ⟨95258, by rfl⟩ : syracuseStep 508045 = 190517) (by norm_num)
theorem B671885 : Blo 263822 671885 := bbase (se 3 (by rfl) ⟨125978, by rfl⟩ : syracuseStep 671885 = 251957) (by norm_num)
theorem B2277557 : Blo 263822 2277557 := bbase (se 5 (by rfl) ⟨106760, by rfl⟩ : syracuseStep 2277557 = 213521) (by norm_num)
theorem B508189 : Blo 263822 508189 := bbase (se 3 (by rfl) ⟨95285, by rfl⟩ : syracuseStep 508189 = 190571) (by norm_num)
theorem B803125 : Blo 263822 803125 := bbase (se 5 (by rfl) ⟨37646, by rfl⟩ : syracuseStep 803125 = 75293) (by norm_num)
theorem B672077 : Blo 263822 672077 := bbase (se 3 (by rfl) ⟨126014, by rfl⟩ : syracuseStep 672077 = 252029) (by norm_num)
theorem B1130885 : Blo 263822 1130885 := bbase (se 4 (by rfl) ⟨106020, by rfl⟩ : syracuseStep 1130885 = 212041) (by norm_num)
theorem B508349 : Blo 263822 508349 := bbase (se 3 (by rfl) ⟨95315, by rfl⟩ : syracuseStep 508349 = 190631) (by norm_num)
theorem B10961365 : Blo 263822 10961365 := bbase (se 7 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 10961365 = 256907) (by norm_num)
theorem B901637 : Blo 263822 901637 := bbase (se 4 (by rfl) ⟨84528, by rfl⟩ : syracuseStep 901637 = 169057) (by norm_num)
theorem B377389 : Blo 263822 377389 := bbase (se 3 (by rfl) ⟨70760, by rfl⟩ : syracuseStep 377389 = 141521) (by norm_num)
theorem B475789 : Blo 263822 475789 := bbase (se 3 (by rfl) ⟨89210, by rfl⟩ : syracuseStep 475789 = 178421) (by norm_num)
theorem B672421 : Blo 263822 672421 := bbase (se 4 (by rfl) ⟨63039, by rfl⟩ : syracuseStep 672421 = 126079) (by norm_num)
theorem B443053 : Blo 263822 443053 := bbase (se 3 (by rfl) ⟨83072, by rfl⟩ : syracuseStep 443053 = 166145) (by norm_num)
theorem B672533 : Blo 263822 672533 := bbase (se 6 (by rfl) ⟨15762, by rfl⟩ : syracuseStep 672533 = 31525) (by norm_num)
theorem B770933 : Blo 263822 770933 := bbase (se 5 (by rfl) ⟨36137, by rfl⟩ : syracuseStep 770933 = 72275) (by norm_num)
theorem B377725 : Blo 263822 377725 := bbase (se 3 (by rfl) ⟨70823, by rfl⟩ : syracuseStep 377725 = 141647) (by norm_num)
theorem B902069 : Blo 263822 902069 := bbase (se 5 (by rfl) ⟨42284, by rfl⟩ : syracuseStep 902069 = 84569) (by norm_num)
theorem B672725 : Blo 263822 672725 := bbase (se 7 (by rfl) ⟨7883, by rfl⟩ : syracuseStep 672725 = 15767) (by norm_num)
theorem B607213 : Blo 263822 607213 := bbase (se 3 (by rfl) ⟨113852, by rfl⟩ : syracuseStep 607213 = 227705) (by norm_num)
theorem B377941 : Blo 263822 377941 := bbase (se 8 (by rfl) ⟨2214, by rfl⟩ : syracuseStep 377941 = 4429) (by norm_num)
theorem B476285 : Blo 263822 476285 := bbase (se 3 (by rfl) ⟨89303, by rfl⟩ : syracuseStep 476285 = 178607) (by norm_num)
theorem B640237 : Blo 263822 640237 := bbase (se 3 (by rfl) ⟨120044, by rfl⟩ : syracuseStep 640237 = 240089) (by norm_num)
theorem B673069 : Blo 263822 673069 := bbase (se 3 (by rfl) ⟨126200, by rfl⟩ : syracuseStep 673069 = 252401) (by norm_num)
theorem B902501 : Blo 263822 902501 := bbase (se 4 (by rfl) ⟨84609, by rfl⟩ : syracuseStep 902501 = 169219) (by norm_num)
theorem B640381 : Blo 263822 640381 := bbase (se 3 (by rfl) ⟨120071, by rfl⟩ : syracuseStep 640381 = 240143) (by norm_num)
theorem B771461 : Blo 263822 771461 := bbase (se 4 (by rfl) ⟨72324, by rfl⟩ : syracuseStep 771461 = 144649) (by norm_num)
theorem B673181 : Blo 263822 673181 := bbase (se 3 (by rfl) ⟨126221, by rfl⟩ : syracuseStep 673181 = 252443) (by norm_num)
theorem B378317 : Blo 263822 378317 := bbase (se 3 (by rfl) ⟨70934, by rfl⟩ : syracuseStep 378317 = 141869) (by norm_num)
theorem B804389 : Blo 263822 804389 := bbase (se 4 (by rfl) ⟨75411, by rfl⟩ : syracuseStep 804389 = 150823) (by norm_num)
theorem B2475605 : Blo 263822 2475605 := bbase (se 8 (by rfl) ⟨14505, by rfl⟩ : syracuseStep 2475605 = 29011) (by norm_num)
theorem B673373 : Blo 263822 673373 := bbase (se 3 (by rfl) ⟨126257, by rfl⟩ : syracuseStep 673373 = 252515) (by norm_num)
theorem B902933 : Blo 263822 902933 := bbase (se 6 (by rfl) ⟨21162, by rfl⟩ : syracuseStep 902933 = 42325) (by norm_num)
theorem B673717 : Blo 263822 673717 := bbase (se 5 (by rfl) ⟨31580, by rfl⟩ : syracuseStep 673717 = 63161) (by norm_num)
theorem B640997 : Blo 263822 640997 := bbase (se 4 (by rfl) ⟨60093, by rfl⟩ : syracuseStep 640997 = 120187) (by norm_num)
theorem B477173 : Blo 263822 477173 := bbase (se 5 (by rfl) ⟨22367, by rfl⟩ : syracuseStep 477173 = 44735) (by norm_num)
theorem B673829 : Blo 263822 673829 := bbase (se 4 (by rfl) ⟨63171, by rfl⟩ : syracuseStep 673829 = 126343) (by norm_num)
theorem B1722485 : Blo 263822 1722485 := bbase (se 5 (by rfl) ⟨80741, by rfl⟩ : syracuseStep 1722485 = 161483) (by norm_num)
theorem B1099909 : Blo 263822 1099909 := bbase (se 4 (by rfl) ⟨103116, by rfl⟩ : syracuseStep 1099909 = 206233) (by norm_num)
theorem B903365 : Blo 263822 903365 := bbase (se 4 (by rfl) ⟨84690, by rfl⟩ : syracuseStep 903365 = 169381) (by norm_num)
theorem B674021 : Blo 263822 674021 := bbase (se 4 (by rfl) ⟨63189, by rfl⟩ : syracuseStep 674021 = 126379) (by norm_num)
theorem B477461 : Blo 263822 477461 := bbase (se 6 (by rfl) ⟨11190, by rfl⟩ : syracuseStep 477461 = 22381) (by norm_num)
theorem B641333 : Blo 263822 641333 := bbase (se 5 (by rfl) ⟨30062, by rfl⟩ : syracuseStep 641333 = 60125) (by norm_num)
theorem B641429 : Blo 263822 641429 := bbase (se 6 (by rfl) ⟨15033, by rfl⟩ : syracuseStep 641429 = 30067) (by norm_num)
theorem B2574773 : Blo 263822 2574773 := bbase (se 5 (by rfl) ⟨120692, by rfl⟩ : syracuseStep 2574773 = 241385) (by norm_num)
theorem B674365 : Blo 263822 674365 := bbase (se 3 (by rfl) ⟨126443, by rfl⟩ : syracuseStep 674365 = 252887) (by norm_num)
theorem B641621 : Blo 263822 641621 := bbase (se 8 (by rfl) ⟨3759, by rfl⟩ : syracuseStep 641621 = 7519) (by norm_num)
theorem B903797 : Blo 263822 903797 := bbase (se 5 (by rfl) ⟨42365, by rfl⟩ : syracuseStep 903797 = 84731) (by norm_num)
theorem B674477 : Blo 263822 674477 := bbase (se 3 (by rfl) ⟨126464, by rfl⟩ : syracuseStep 674477 = 252929) (by norm_num)
theorem B445277 : Blo 263822 445277 := bbase (se 3 (by rfl) ⟨83489, by rfl⟩ : syracuseStep 445277 = 166979) (by norm_num)
theorem B379741 : Blo 263822 379741 := bbase (se 3 (by rfl) ⟨71201, by rfl⟩ : syracuseStep 379741 = 142403) (by norm_num)
theorem B674669 : Blo 263822 674669 := bbase (se 3 (by rfl) ⟨126500, by rfl⟩ : syracuseStep 674669 = 253001) (by norm_num)
theorem B510853 : Blo 263822 510853 := bbase (se 4 (by rfl) ⟨47892, by rfl⟩ : syracuseStep 510853 = 95785) (by norm_num)
theorem B445405 : Blo 263822 445405 := bbase (se 3 (by rfl) ⟨83513, by rfl⟩ : syracuseStep 445405 = 167027) (by norm_num)
theorem B445493 : Blo 263822 445493 := bbase (se 5 (by rfl) ⟨20882, by rfl⟩ : syracuseStep 445493 = 41765) (by norm_num)
theorem B2018357 : Blo 263822 2018357 := bbase (se 5 (by rfl) ⟨94610, by rfl⟩ : syracuseStep 2018357 = 189221) (by norm_num)
theorem B445621 : Blo 263822 445621 := bbase (se 5 (by rfl) ⟨20888, by rfl⟩ : syracuseStep 445621 = 41777) (by norm_num)
theorem B675013 : Blo 263822 675013 := bbase (se 4 (by rfl) ⟨63282, by rfl⟩ : syracuseStep 675013 = 126565) (by norm_num)
theorem B1002725 : Blo 263822 1002725 := bbase (se 4 (by rfl) ⟨94005, by rfl⟩ : syracuseStep 1002725 = 188011) (by norm_num)
theorem B445709 : Blo 263822 445709 := bbase (se 3 (by rfl) ⟨83570, by rfl⟩ : syracuseStep 445709 = 167141) (by norm_num)
theorem B478477 : Blo 263822 478477 := bbase (se 3 (by rfl) ⟨89714, by rfl⟩ : syracuseStep 478477 = 179429) (by norm_num)
theorem B675125 : Blo 263822 675125 := bbase (se 5 (by rfl) ⟨31646, by rfl⟩ : syracuseStep 675125 = 63293) (by norm_num)
theorem B445837 : Blo 263822 445837 := bbase (se 3 (by rfl) ⟨83594, by rfl⟩ : syracuseStep 445837 = 167189) (by norm_num)
theorem B380333 : Blo 263822 380333 := bbase (se 3 (by rfl) ⟨71312, by rfl⟩ : syracuseStep 380333 = 142625) (by norm_num)
theorem B445925 : Blo 263822 445925 := bbase (se 4 (by rfl) ⟨41805, by rfl⟩ : syracuseStep 445925 = 83611) (by norm_num)
theorem B282089 : Blo 263822 282089 := bbase (se 2 (by rfl) ⟨105783, by rfl⟩ : syracuseStep 282089 = 211567) (by norm_num)
theorem B675317 : Blo 263822 675317 := bbase (se 5 (by rfl) ⟨31655, by rfl⟩ : syracuseStep 675317 = 63311) (by norm_num)
theorem B380413 : Blo 263822 380413 := bbase (se 3 (by rfl) ⟨71327, by rfl⟩ : syracuseStep 380413 = 142655) (by norm_num)
theorem B1003013 : Blo 263822 1003013 := bbase (se 4 (by rfl) ⟨94032, by rfl⟩ : syracuseStep 1003013 = 188065) (by norm_num)
theorem B544349 : Blo 263822 544349 := bbase (se 3 (by rfl) ⟨102065, by rfl⟩ : syracuseStep 544349 = 204131) (by norm_num)
theorem B446053 : Blo 263822 446053 := bbase (se 4 (by rfl) ⟨41817, by rfl⟩ : syracuseStep 446053 = 83635) (by norm_num)
theorem B380533 : Blo 263822 380533 := bbase (se 5 (by rfl) ⟨17837, by rfl⟩ : syracuseStep 380533 = 35675) (by norm_num)
theorem B446141 : Blo 263822 446141 := bbase (se 3 (by rfl) ⟨83651, by rfl⟩ : syracuseStep 446141 = 167303) (by norm_num)
theorem B478909 : Blo 263822 478909 := bbase (se 3 (by rfl) ⟨89795, by rfl⟩ : syracuseStep 478909 = 179591) (by norm_num)
theorem B380629 : Blo 263822 380629 := bbase (se 7 (by rfl) ⟨4460, by rfl⟩ : syracuseStep 380629 = 8921) (by norm_num)
theorem B642773 : Blo 263822 642773 := bbase (se 7 (by rfl) ⟨7532, by rfl⟩ : syracuseStep 642773 = 15065) (by norm_num)
theorem B2543413 : Blo 263822 2543413 := bbase (se 5 (by rfl) ⟨119222, by rfl⟩ : syracuseStep 2543413 = 238445) (by norm_num)
theorem B872245 : Blo 263822 872245 := bbase (se 5 (by rfl) ⟨40886, by rfl⟩ : syracuseStep 872245 = 81773) (by norm_num)
theorem B446269 : Blo 263822 446269 := bbase (se 3 (by rfl) ⟨83675, by rfl⟩ : syracuseStep 446269 = 167351) (by norm_num)
theorem B675661 : Blo 263822 675661 := bbase (se 3 (by rfl) ⟨126686, by rfl⟩ : syracuseStep 675661 = 253373) (by norm_num)
theorem B446357 : Blo 263822 446357 := bbase (se 6 (by rfl) ⟨10461, by rfl⟩ : syracuseStep 446357 = 20923) (by norm_num)
theorem B282533 : Blo 263822 282533 := bbase (se 4 (by rfl) ⟨26487, by rfl⟩ : syracuseStep 282533 = 52975) (by norm_num)
theorem B675773 : Blo 263822 675773 := bbase (se 3 (by rfl) ⟨126707, by rfl⟩ : syracuseStep 675773 = 253415) (by norm_num)
theorem B479197 : Blo 263822 479197 := bbase (se 3 (by rfl) ⟨89849, by rfl⟩ : syracuseStep 479197 = 179699) (by norm_num)
theorem B446485 : Blo 263822 446485 := bbase (se 6 (by rfl) ⟨10464, by rfl⟩ : syracuseStep 446485 = 20929) (by norm_num)
theorem B446573 : Blo 263822 446573 := bbase (se 3 (by rfl) ⟨83732, by rfl⟩ : syracuseStep 446573 = 167465) (by norm_num)
theorem B675965 : Blo 263822 675965 := bbase (se 3 (by rfl) ⟨126743, by rfl⟩ : syracuseStep 675965 = 253487) (by norm_num)
theorem B282781 : Blo 263822 282781 := bbase (se 3 (by rfl) ⟨53021, by rfl⟩ : syracuseStep 282781 = 106043) (by norm_num)
theorem B381125 : Blo 263822 381125 := bbase (se 4 (by rfl) ⟨35730, by rfl⟩ : syracuseStep 381125 = 71461) (by norm_num)
theorem B446701 : Blo 263822 446701 := bbase (se 3 (by rfl) ⟨83756, by rfl⟩ : syracuseStep 446701 = 167513) (by norm_num)
theorem B446789 : Blo 263822 446789 := bbase (se 4 (by rfl) ⟨41886, by rfl⟩ : syracuseStep 446789 = 83773) (by norm_num)
theorem B1134917 : Blo 263822 1134917 := bbase (se 4 (by rfl) ⟨106398, by rfl⟩ : syracuseStep 1134917 = 212797) (by norm_num)
theorem B446917 : Blo 263822 446917 := bbase (se 4 (by rfl) ⟨41898, by rfl⟩ : syracuseStep 446917 = 83797) (by norm_num)
theorem B676309 : Blo 263822 676309 := bbase (se 7 (by rfl) ⟨7925, by rfl⟩ : syracuseStep 676309 = 15851) (by norm_num)
theorem B447005 : Blo 263822 447005 := bbase (se 3 (by rfl) ⟨83813, by rfl⟩ : syracuseStep 447005 = 167627) (by norm_num)
theorem B676421 : Blo 263822 676421 := bbase (se 4 (by rfl) ⟨63414, by rfl⟩ : syracuseStep 676421 = 126829) (by norm_num)
theorem B283213 : Blo 263822 283213 := bbase (se 3 (by rfl) ⟨53102, by rfl⟩ : syracuseStep 283213 = 106205) (by norm_num)
theorem B479861 : Blo 263822 479861 := bbase (se 5 (by rfl) ⟨22493, by rfl⟩ : syracuseStep 479861 = 44987) (by norm_num)
theorem B283285 : Blo 263822 283285 := bbase (se 6 (by rfl) ⟨6639, by rfl⟩ : syracuseStep 283285 = 13279) (by norm_num)
theorem B447133 : Blo 263822 447133 := bbase (se 3 (by rfl) ⟨83837, by rfl⟩ : syracuseStep 447133 = 167675) (by norm_num)
theorem B1004197 : Blo 263822 1004197 := bbase (se 4 (by rfl) ⟨94143, by rfl⟩ : syracuseStep 1004197 = 188287) (by norm_num)
theorem B447221 : Blo 263822 447221 := bbase (se 5 (by rfl) ⟨20963, by rfl⟩ : syracuseStep 447221 = 41927) (by norm_num)
theorem B676613 : Blo 263822 676613 := bbase (se 4 (by rfl) ⟨63432, by rfl⟩ : syracuseStep 676613 = 126865) (by norm_num)
theorem B447349 : Blo 263822 447349 := bbase (se 5 (by rfl) ⟨20969, by rfl⟩ : syracuseStep 447349 = 41939) (by norm_num)
theorem B447437 : Blo 263822 447437 := bbase (se 3 (by rfl) ⟨83894, by rfl⟩ : syracuseStep 447437 = 167789) (by norm_num)
theorem B1004501 : Blo 263822 1004501 := bbase (se 7 (by rfl) ⟨11771, by rfl⟩ : syracuseStep 1004501 = 23543) (by norm_num)
theorem B283657 : Blo 263822 283657 := bbase (se 2 (by rfl) ⟨106371, by rfl⟩ : syracuseStep 283657 = 212743) (by norm_num)
theorem B447565 : Blo 263822 447565 := bbase (se 3 (by rfl) ⟨83918, by rfl⟩ : syracuseStep 447565 = 167837) (by norm_num)
theorem B676957 : Blo 263822 676957 := bbase (se 3 (by rfl) ⟨126929, by rfl⟩ : syracuseStep 676957 = 253859) (by norm_num)
theorem B447653 : Blo 263822 447653 := bbase (se 4 (by rfl) ⟨41967, by rfl⟩ : syracuseStep 447653 = 83935) (by norm_num)
theorem B677069 : Blo 263822 677069 := bbase (se 3 (by rfl) ⟨126950, by rfl⟩ : syracuseStep 677069 = 253901) (by norm_num)
theorem B447781 : Blo 263822 447781 := bbase (se 4 (by rfl) ⟨41979, by rfl⟩ : syracuseStep 447781 = 83959) (by norm_num)
theorem B480581 : Blo 263822 480581 := bbase (se 4 (by rfl) ⟨45054, by rfl⟩ : syracuseStep 480581 = 90109) (by norm_num)
theorem B447869 : Blo 263822 447869 := bbase (se 3 (by rfl) ⟨83975, by rfl⟩ : syracuseStep 447869 = 167951) (by norm_num)
theorem B284033 : Blo 263822 284033 := bbase (se 2 (by rfl) ⟨106512, by rfl⟩ : syracuseStep 284033 = 213025) (by norm_num)
theorem B677261 : Blo 263822 677261 := bbase (se 3 (by rfl) ⟨126986, by rfl⟩ : syracuseStep 677261 = 253973) (by norm_num)
theorem B284105 : Blo 263822 284105 := bbase (se 2 (by rfl) ⟨106539, by rfl⟩ : syracuseStep 284105 = 213079) (by norm_num)
theorem B447997 : Blo 263822 447997 := bbase (se 3 (by rfl) ⟨83999, by rfl⟩ : syracuseStep 447997 = 167999) (by norm_num)
theorem B448085 : Blo 263822 448085 := bbase (se 8 (by rfl) ⟨2625, by rfl⟩ : syracuseStep 448085 = 5251) (by norm_num)
theorem B284293 : Blo 263822 284293 := bbase (se 4 (by rfl) ⟨26652, by rfl⟩ : syracuseStep 284293 = 53305) (by norm_num)
theorem B448213 : Blo 263822 448213 := bbase (se 7 (by rfl) ⟨5252, by rfl⟩ : syracuseStep 448213 = 10505) (by norm_num)
theorem B677605 : Blo 263822 677605 := bbase (se 4 (by rfl) ⟨63525, by rfl⟩ : syracuseStep 677605 = 127051) (by norm_num)
theorem B448301 : Blo 263822 448301 := bbase (se 3 (by rfl) ⟨84056, by rfl⟩ : syracuseStep 448301 = 168113) (by norm_num)
theorem B284477 : Blo 263822 284477 := bbase (se 3 (by rfl) ⟨53339, by rfl⟩ : syracuseStep 284477 = 106679) (by norm_num)
theorem B3037013 : Blo 263822 3037013 := bbase (se 9 (by rfl) ⟨8897, by rfl⟩ : syracuseStep 3037013 = 17795) (by norm_num)
theorem B677717 : Blo 263822 677717 := bbase (se 9 (by rfl) ⟨1985, by rfl⟩ : syracuseStep 677717 = 3971) (by norm_num)
theorem B448429 : Blo 263822 448429 := bbase (se 3 (by rfl) ⟨84080, by rfl⟩ : syracuseStep 448429 = 168161) (by norm_num)
theorem B382925 : Blo 263822 382925 := bbase (se 3 (by rfl) ⟨71798, by rfl⟩ : syracuseStep 382925 = 143597) (by norm_num)
theorem B448517 : Blo 263822 448517 := bbase (se 4 (by rfl) ⟨42048, by rfl⟩ : syracuseStep 448517 = 84097) (by norm_num)
theorem B677909 : Blo 263822 677909 := bbase (se 6 (by rfl) ⟨15888, by rfl⟩ : syracuseStep 677909 = 31777) (by norm_num)
theorem B1136693 : Blo 263822 1136693 := bbase (se 5 (by rfl) ⟨53282, by rfl⟩ : syracuseStep 1136693 = 106565) (by norm_num)
theorem B448645 : Blo 263822 448645 := bbase (se 4 (by rfl) ⟨42060, by rfl⟩ : syracuseStep 448645 = 84121) (by norm_num)
theorem B448733 : Blo 263822 448733 := bbase (se 3 (by rfl) ⟨84137, by rfl⟩ : syracuseStep 448733 = 168275) (by norm_num)
theorem B317773 : Blo 263822 317773 := bbase (se 3 (by rfl) ⟨59582, by rfl⟩ : syracuseStep 317773 = 119165) (by norm_num)
theorem B448861 : Blo 263822 448861 := bbase (se 3 (by rfl) ⟨84161, by rfl⟩ : syracuseStep 448861 = 168323) (by norm_num)
theorem B448949 : Blo 263822 448949 := bbase (se 5 (by rfl) ⟨21044, by rfl⟩ : syracuseStep 448949 = 42089) (by norm_num)
theorem B285229 : Blo 263822 285229 := bbase (se 3 (by rfl) ⟨53480, by rfl⟩ : syracuseStep 285229 = 106961) (by norm_num)
theorem B449077 : Blo 263822 449077 := bbase (se 5 (by rfl) ⟨21050, by rfl⟩ : syracuseStep 449077 = 42101) (by norm_num)
theorem B2546261 : Blo 263822 2546261 := bbase (se 8 (by rfl) ⟨14919, by rfl⟩ : syracuseStep 2546261 = 29839) (by norm_num)
theorem B285301 : Blo 263822 285301 := bbase (se 5 (by rfl) ⟨13373, by rfl⟩ : syracuseStep 285301 = 26747) (by norm_num)
theorem B449165 : Blo 263822 449165 := bbase (se 3 (by rfl) ⟨84218, by rfl⟩ : syracuseStep 449165 = 168437) (by norm_num)
theorem B1694357 : Blo 263822 1694357 := bbase (se 6 (by rfl) ⟨39711, by rfl⟩ : syracuseStep 1694357 = 79423) (by norm_num)
theorem B449293 : Blo 263822 449293 := bbase (se 3 (by rfl) ⟨84242, by rfl⟩ : syracuseStep 449293 = 168485) (by norm_num)
theorem B285481 : Blo 263822 285481 := bbase (se 2 (by rfl) ⟨107055, by rfl⟩ : syracuseStep 285481 = 214111) (by norm_num)
theorem B449381 : Blo 263822 449381 := bbase (se 4 (by rfl) ⟨42129, by rfl⟩ : syracuseStep 449381 = 84259) (by norm_num)
theorem B449509 : Blo 263822 449509 := bbase (se 4 (by rfl) ⟨42141, by rfl⟩ : syracuseStep 449509 = 84283) (by norm_num)
theorem B1006613 : Blo 263822 1006613 := bbase (se 6 (by rfl) ⟨23592, by rfl⟩ : syracuseStep 1006613 = 47185) (by norm_num)
theorem B1137685 : Blo 263822 1137685 := bbase (se 6 (by rfl) ⟨26664, by rfl⟩ : syracuseStep 1137685 = 53329) (by norm_num)
theorem B449597 : Blo 263822 449597 := bbase (se 3 (by rfl) ⟨84299, by rfl⟩ : syracuseStep 449597 = 168599) (by norm_num)
theorem B449725 : Blo 263822 449725 := bbase (se 3 (by rfl) ⟨84323, by rfl⟩ : syracuseStep 449725 = 168647) (by norm_num)
theorem B285925 : Blo 263822 285925 := bbase (se 4 (by rfl) ⟨26805, by rfl⟩ : syracuseStep 285925 = 53611) (by norm_num)
theorem B449813 : Blo 263822 449813 := bbase (se 6 (by rfl) ⟨10542, by rfl⟩ : syracuseStep 449813 = 21085) (by norm_num)
theorem B1006901 : Blo 263822 1006901 := bbase (se 5 (by rfl) ⟨47198, by rfl⟩ : syracuseStep 1006901 = 94397) (by norm_num)
theorem B318821 : Blo 263822 318821 := bbase (se 4 (by rfl) ⟨29889, by rfl⟩ : syracuseStep 318821 = 59779) (by norm_num)
theorem B449941 : Blo 263822 449941 := bbase (se 6 (by rfl) ⟨10545, by rfl⟩ : syracuseStep 449941 = 21091) (by norm_num)
theorem B450029 : Blo 263822 450029 := bbase (se 3 (by rfl) ⟨84380, by rfl⟩ : syracuseStep 450029 = 168761) (by norm_num)
theorem B450157 : Blo 263822 450157 := bbase (se 3 (by rfl) ⟨84404, by rfl⟩ : syracuseStep 450157 = 168809) (by norm_num)
theorem B450245 : Blo 263822 450245 := bbase (se 4 (by rfl) ⟨42210, by rfl⟩ : syracuseStep 450245 = 84421) (by norm_num)
theorem B319177 : Blo 263822 319177 := bbase (se 2 (by rfl) ⟨119691, by rfl⟩ : syracuseStep 319177 = 239383) (by norm_num)
theorem B450373 : Blo 263822 450373 := bbase (se 4 (by rfl) ⟨42222, by rfl⟩ : syracuseStep 450373 = 84445) (by norm_num)
theorem B319369 : Blo 263822 319369 := bbase (se 2 (by rfl) ⟨119763, by rfl⟩ : syracuseStep 319369 = 239527) (by norm_num)
theorem B450461 : Blo 263822 450461 := bbase (se 3 (by rfl) ⟨84461, by rfl⟩ : syracuseStep 450461 = 168923) (by norm_num)
theorem B319513 : Blo 263822 319513 := bbase (se 2 (by rfl) ⟨119817, by rfl⟩ : syracuseStep 319513 = 239635) (by norm_num)
theorem B614429 : Blo 263822 614429 := bbase (se 3 (by rfl) ⟨115205, by rfl⟩ : syracuseStep 614429 = 230411) (by norm_num)
theorem B450589 : Blo 263822 450589 := bbase (se 3 (by rfl) ⟨84485, by rfl⟩ : syracuseStep 450589 = 168971) (by norm_num)
theorem B450677 : Blo 263822 450677 := bbase (se 5 (by rfl) ⟨21125, by rfl⟩ : syracuseStep 450677 = 42251) (by norm_num)
theorem B450805 : Blo 263822 450805 := bbase (se 5 (by rfl) ⟨21131, by rfl⟩ : syracuseStep 450805 = 42263) (by norm_num)
theorem B909605 : Blo 263822 909605 := bbase (se 4 (by rfl) ⟨85275, by rfl⟩ : syracuseStep 909605 = 170551) (by norm_num)
theorem B450893 : Blo 263822 450893 := bbase (se 3 (by rfl) ⟨84542, by rfl⟩ : syracuseStep 450893 = 169085) (by norm_num)
theorem B582061 : Blo 263822 582061 := bbase (se 3 (by rfl) ⟨109136, by rfl⟩ : syracuseStep 582061 = 218273) (by norm_num)
theorem B451021 : Blo 263822 451021 := bbase (se 3 (by rfl) ⟨84566, by rfl⟩ : syracuseStep 451021 = 169133) (by norm_num)
theorem B713173 : Blo 263822 713173 := bbase (se 7 (by rfl) ⟨8357, by rfl⟩ : syracuseStep 713173 = 16715) (by norm_num)
theorem B1008085 : Blo 263822 1008085 := bbase (se 7 (by rfl) ⟨11813, by rfl⟩ : syracuseStep 1008085 = 23627) (by norm_num)
theorem B451109 : Blo 263822 451109 := bbase (se 4 (by rfl) ⟨42291, by rfl⟩ : syracuseStep 451109 = 84583) (by norm_num)
theorem B647765 : Blo 263822 647765 := bbase (se 8 (by rfl) ⟨3795, by rfl⟩ : syracuseStep 647765 = 7591) (by norm_num)
theorem B451237 : Blo 263822 451237 := bbase (se 4 (by rfl) ⟨42303, by rfl⟩ : syracuseStep 451237 = 84607) (by norm_num)
theorem B451325 : Blo 263822 451325 := bbase (se 3 (by rfl) ⟨84623, by rfl⟩ : syracuseStep 451325 = 169247) (by norm_num)
theorem B1008389 : Blo 263822 1008389 := bbase (se 4 (by rfl) ⟨94536, by rfl⟩ : syracuseStep 1008389 = 189073) (by norm_num)
theorem B451453 : Blo 263822 451453 := bbase (se 3 (by rfl) ⟨84647, by rfl⟩ : syracuseStep 451453 = 169295) (by norm_num)
theorem B3072917 : Blo 263822 3072917 := bbase (se 6 (by rfl) ⟨72021, by rfl⟩ : syracuseStep 3072917 = 144043) (by norm_num)
theorem B451541 : Blo 263822 451541 := bbase (se 7 (by rfl) ⟨5291, by rfl⟩ : syracuseStep 451541 = 10583) (by norm_num)
theorem B386077 : Blo 263822 386077 := bbase (se 3 (by rfl) ⟨72389, by rfl⟩ : syracuseStep 386077 = 144779) (by norm_num)
theorem B451669 : Blo 263822 451669 := bbase (se 8 (by rfl) ⟨2646, by rfl⟩ : syracuseStep 451669 = 5293) (by norm_num)
theorem B451757 : Blo 263822 451757 := bbase (se 3 (by rfl) ⟨84704, by rfl⟩ : syracuseStep 451757 = 169409) (by norm_num)
theorem B451885 : Blo 263822 451885 := bbase (se 3 (by rfl) ⟨84728, by rfl⟩ : syracuseStep 451885 = 169457) (by norm_num)
theorem B1336661 : Blo 263822 1336661 := bbase (se 12 (by rfl) ⟨489, by rfl⟩ : syracuseStep 1336661 = 979) (by norm_num)
theorem B1271285 : Blo 263822 1271285 := bbase (se 5 (by rfl) ⟨59591, by rfl⟩ : syracuseStep 1271285 = 119183) (by norm_num)
theorem B648701 : Blo 263822 648701 := bbase (se 3 (by rfl) ⟨121631, by rfl⟩ : syracuseStep 648701 = 243263) (by norm_num)
theorem B321041 : Blo 263822 321041 := bbase (se 2 (by rfl) ⟨120390, by rfl⟩ : syracuseStep 321041 = 240781) (by norm_num)
theorem B1697557 : Blo 263822 1697557 := bbase (se 6 (by rfl) ⟨39786, by rfl⟩ : syracuseStep 1697557 = 79573) (by norm_num)
theorem B321349 : Blo 263822 321349 := bbase (se 4 (by rfl) ⟨30126, by rfl⟩ : syracuseStep 321349 = 60253) (by norm_num)
theorem B321445 : Blo 263822 321445 := bbase (se 4 (by rfl) ⟨30135, by rfl⟩ : syracuseStep 321445 = 60271) (by norm_num)
theorem B452621 : Blo 263822 452621 := bbase (se 3 (by rfl) ⟨84866, by rfl⟩ : syracuseStep 452621 = 169733) (by norm_num)
theorem B845909 : Blo 263822 845909 := bbase (se 8 (by rfl) ⟨4956, by rfl⟩ : syracuseStep 845909 = 9913) (by norm_num)
theorem B288913 : Blo 263822 288913 := bbase (se 2 (by rfl) ⟨108342, by rfl⟩ : syracuseStep 288913 = 216685) (by norm_num)
theorem B321733 : Blo 263822 321733 := bbase (se 4 (by rfl) ⟨30162, by rfl⟩ : syracuseStep 321733 = 60325) (by norm_num)
theorem B289229 : Blo 263822 289229 := bbase (se 3 (by rfl) ⟨54230, by rfl⟩ : syracuseStep 289229 = 108461) (by norm_num)
theorem B1337957 : Blo 263822 1337957 := bbase (se 4 (by rfl) ⟨125433, by rfl⟩ : syracuseStep 1337957 = 250867) (by norm_num)
theorem B2026133 : Blo 263822 2026133 := bbase (se 6 (by rfl) ⟨47487, by rfl⟩ : syracuseStep 2026133 = 94975) (by norm_num)
theorem B1272629 : Blo 263822 1272629 := bbase (se 5 (by rfl) ⟨59654, by rfl⟩ : syracuseStep 1272629 = 119309) (by norm_num)
theorem B1010501 : Blo 263822 1010501 := bbase (se 4 (by rfl) ⟨94734, by rfl⟩ : syracuseStep 1010501 = 189469) (by norm_num)
theorem B1010789 : Blo 263822 1010789 := bbase (se 4 (by rfl) ⟨94761, by rfl⟩ : syracuseStep 1010789 = 189523) (by norm_num)
theorem B847189 : Blo 263822 847189 := bbase (se 11 (by rfl) ⟨620, by rfl⟩ : syracuseStep 847189 = 1241) (by norm_num)
theorem B1371653 : Blo 263822 1371653 := bbase (se 4 (by rfl) ⟨128592, by rfl⟩ : syracuseStep 1371653 = 257185) (by norm_num)
theorem B683549 : Blo 263822 683549 := bbase (se 3 (by rfl) ⟨128165, by rfl⟩ : syracuseStep 683549 = 256331) (by norm_num)
theorem B2256437 : Blo 263822 2256437 := bbase (se 5 (by rfl) ⟨105770, by rfl⟩ : syracuseStep 2256437 = 211541) (by norm_num)
theorem B1732309 : Blo 263822 1732309 := bbase (se 7 (by rfl) ⟨20300, by rfl⟩ : syracuseStep 1732309 = 40601) (by norm_num)
theorem B683765 : Blo 263822 683765 := bbase (se 5 (by rfl) ⟨32051, by rfl⟩ : syracuseStep 683765 = 64103) (by norm_num)
theorem B323357 : Blo 263822 323357 := bbase (se 3 (by rfl) ⟨60629, by rfl⟩ : syracuseStep 323357 = 121259) (by norm_num)
theorem B1339253 : Blo 263822 1339253 := bbase (se 5 (by rfl) ⟨62777, by rfl⟩ : syracuseStep 1339253 = 125555) (by norm_num)
theorem B651149 : Blo 263822 651149 := bbase (se 3 (by rfl) ⟨122090, by rfl⟩ : syracuseStep 651149 = 244181) (by norm_num)
theorem B1142693 : Blo 263822 1142693 := bbase (se 4 (by rfl) ⟨107127, by rfl⟩ : syracuseStep 1142693 = 214255) (by norm_num)
theorem B389053 : Blo 263822 389053 := bbase (se 3 (by rfl) ⟨72947, by rfl⟩ : syracuseStep 389053 = 145895) (by norm_num)
theorem B1929205 : Blo 263822 1929205 := bbase (se 5 (by rfl) ⟨90431, by rfl⟩ : syracuseStep 1929205 = 180863) (by norm_num)
theorem B815093 : Blo 263822 815093 := bbase (se 5 (by rfl) ⟨38207, by rfl⟩ : syracuseStep 815093 = 76415) (by norm_num)
theorem B1142981 : Blo 263822 1142981 := bbase (se 4 (by rfl) ⟨107154, by rfl⟩ : syracuseStep 1142981 = 214309) (by norm_num)
theorem B1011973 : Blo 263822 1011973 := bbase (se 4 (by rfl) ⟨94872, by rfl⟩ : syracuseStep 1011973 = 189745) (by norm_num)
theorem B1012277 : Blo 263822 1012277 := bbase (se 5 (by rfl) ⟨47450, by rfl⟩ : syracuseStep 1012277 = 94901) (by norm_num)
theorem B356933 : Blo 263822 356933 := bbase (se 4 (by rfl) ⟨33462, by rfl⟩ : syracuseStep 356933 = 66925) (by norm_num)
theorem B324253 : Blo 263822 324253 := bbase (se 3 (by rfl) ⟨60797, by rfl⟩ : syracuseStep 324253 = 121595) (by norm_num)
theorem B848549 : Blo 263822 848549 := bbase (se 4 (by rfl) ⟨79551, by rfl⟩ : syracuseStep 848549 = 159103) (by norm_num)
theorem B717541 : Blo 263822 717541 := bbase (se 4 (by rfl) ⟨67269, by rfl⟩ : syracuseStep 717541 = 134539) (by norm_num)
theorem B1274629 : Blo 263822 1274629 := bbase (se 4 (by rfl) ⟨119496, by rfl⟩ : syracuseStep 1274629 = 238993) (by norm_num)
theorem B1372949 : Blo 263822 1372949 := bbase (se 6 (by rfl) ⟨32178, by rfl⟩ : syracuseStep 1372949 = 64357) (by norm_num)
theorem B848677 : Blo 263822 848677 := bbase (se 4 (by rfl) ⟨79563, by rfl⟩ : syracuseStep 848677 = 159127) (by norm_num)
theorem B422749 : Blo 263822 422749 := bbase (se 3 (by rfl) ⟨79265, by rfl⟩ : syracuseStep 422749 = 158531) (by norm_num)
theorem B1143733 : Blo 263822 1143733 := bbase (se 5 (by rfl) ⟨53612, by rfl⟩ : syracuseStep 1143733 = 107225) (by norm_num)
theorem B717781 : Blo 263822 717781 := bbase (se 7 (by rfl) ⟨8411, by rfl⟩ : syracuseStep 717781 = 16823) (by norm_num)
theorem B848933 : Blo 263822 848933 := bbase (se 4 (by rfl) ⟨79587, by rfl⟩ : syracuseStep 848933 = 159175) (by norm_num)
theorem B1340549 : Blo 263822 1340549 := bbase (se 4 (by rfl) ⟨125676, by rfl⟩ : syracuseStep 1340549 = 251353) (by norm_num)
theorem B1504565 : Blo 263822 1504565 := bbase (se 5 (by rfl) ⟨70526, by rfl⟩ : syracuseStep 1504565 = 141053) (by norm_num)
theorem B3437909 : Blo 263822 3437909 := bbase (se 13 (by rfl) ⟨629, by rfl⟩ : syracuseStep 3437909 = 1259) (by norm_num)
theorem B357733 : Blo 263822 357733 := bbase (se 4 (by rfl) ⟨33537, by rfl⟩ : syracuseStep 357733 = 67075) (by norm_num)
theorem B423301 : Blo 263822 423301 := bbase (se 4 (by rfl) ⟨39684, by rfl⟩ : syracuseStep 423301 = 79369) (by norm_num)
theorem B292405 : Blo 263822 292405 := bbase (se 5 (by rfl) ⟨13706, by rfl⟩ : syracuseStep 292405 = 27413) (by norm_num)
theorem B423557 : Blo 263822 423557 := bbase (se 4 (by rfl) ⟨39708, by rfl⟩ : syracuseStep 423557 = 79417) (by norm_num)
theorem B751349 : Blo 263822 751349 := bbase (se 5 (by rfl) ⟨35219, by rfl⟩ : syracuseStep 751349 = 70439) (by norm_num)
theorem B456445 : Blo 263822 456445 := bbase (se 3 (by rfl) ⟨85583, by rfl⟩ : syracuseStep 456445 = 171167) (by norm_num)
theorem B751589 : Blo 263822 751589 := bbase (se 4 (by rfl) ⟨70461, by rfl⟩ : syracuseStep 751589 = 140923) (by norm_num)
theorem B489461 : Blo 263822 489461 := bbase (se 5 (by rfl) ⟨22943, by rfl⟩ : syracuseStep 489461 = 45887) (by norm_num)
theorem B751781 : Blo 263822 751781 := bbase (se 4 (by rfl) ⟨70479, by rfl⟩ : syracuseStep 751781 = 140959) (by norm_num)
theorem B719045 : Blo 263822 719045 := bbase (se 4 (by rfl) ⟨67410, by rfl⟩ : syracuseStep 719045 = 134821) (by norm_num)
theorem B424261 : Blo 263822 424261 := bbase (se 4 (by rfl) ⟨39774, by rfl⟩ : syracuseStep 424261 = 79549) (by norm_num)
theorem B1341845 : Blo 263822 1341845 := bbase (se 6 (by rfl) ⟨31449, by rfl⟩ : syracuseStep 1341845 = 62899) (by norm_num)
theorem B1505749 : Blo 263822 1505749 := bbase (se 7 (by rfl) ⟨17645, by rfl⟩ : syracuseStep 1505749 = 35291) (by norm_num)
theorem B2259413 : Blo 263822 2259413 := bbase (se 7 (by rfl) ⟨26477, by rfl⟩ : syracuseStep 2259413 = 52955) (by norm_num)
theorem B1014389 : Blo 263822 1014389 := bbase (se 5 (by rfl) ⟨47549, by rfl⟩ : syracuseStep 1014389 = 95099) (by norm_num)
theorem B293501 : Blo 263822 293501 := bbase (se 3 (by rfl) ⟨55031, by rfl⟩ : syracuseStep 293501 = 110063) (by norm_num)
theorem B424685 : Blo 263822 424685 := bbase (se 3 (by rfl) ⟨79628, by rfl⟩ : syracuseStep 424685 = 159257) (by norm_num)
theorem B1014677 : Blo 263822 1014677 := bbase (se 6 (by rfl) ⟨23781, by rfl⟩ : syracuseStep 1014677 = 47563) (by norm_num)
theorem B687109 : Blo 263822 687109 := bbase (se 4 (by rfl) ⟨64416, by rfl⟩ : syracuseStep 687109 = 128833) (by norm_num)
theorem B424973 : Blo 263822 424973 := bbase (se 3 (by rfl) ⟨79682, by rfl⟩ : syracuseStep 424973 = 159365) (by norm_num)
theorem B752773 : Blo 263822 752773 := bbase (se 4 (by rfl) ⟨70572, by rfl⟩ : syracuseStep 752773 = 141145) (by norm_num)
theorem B425197 : Blo 263822 425197 := bbase (se 3 (by rfl) ⟨79724, by rfl⟩ : syracuseStep 425197 = 159449) (by norm_num)
theorem B851381 : Blo 263822 851381 := bbase (se 5 (by rfl) ⟨39908, by rfl⟩ : syracuseStep 851381 = 79817) (by norm_num)
theorem B359869 : Blo 263822 359869 := bbase (se 3 (by rfl) ⟨67475, by rfl⟩ : syracuseStep 359869 = 134951) (by norm_num)
theorem B720485 : Blo 263822 720485 := bbase (se 4 (by rfl) ⟨67545, by rfl⟩ : syracuseStep 720485 = 135091) (by norm_num)
theorem B1343141 : Blo 263822 1343141 := bbase (se 4 (by rfl) ⟨125919, by rfl⟩ : syracuseStep 1343141 = 251839) (by norm_num)
theorem B1703605 : Blo 263822 1703605 := bbase (se 5 (by rfl) ⟨79856, by rfl⟩ : syracuseStep 1703605 = 159713) (by norm_num)
theorem B426017 : Blo 263822 426017 := bstep (se 2 (by rfl) ⟨159756, by rfl⟩ : syracuseStep 426017 = 319513) B319513
theorem B721133 : Blo 263822 721133 := bstep (se 3 (by rfl) ⟨135212, by rfl⟩ : syracuseStep 721133 = 270425) B270425
theorem B753923 : Blo 263822 753923 := bstep (se 1 (by rfl) ⟨565442, by rfl⟩ : syracuseStep 753923 = 1130885) B1130885
theorem B1016333 : Blo 263822 1016333 := bstep (se 3 (by rfl) ⟨190562, by rfl⟩ : syracuseStep 1016333 = 381125) B381125
theorem B361009 : Blo 263822 361009 := bstep (se 2 (by rfl) ⟨135378, by rfl⟩ : syracuseStep 361009 = 270757) B270757
theorem B950897 : Blo 263822 950897 := bstep (se 2 (by rfl) ⟨356586, by rfl⟩ : syracuseStep 950897 = 713173) B713173
theorem B1344113 : Blo 263822 1344113 := bstep (se 2 (by rfl) ⟨504042, by rfl⟩ : syracuseStep 1344113 = 1008085) B1008085
theorem B14615153 : Blo 263822 14615153 := bstep (se 2 (by rfl) ⟨5480682, by rfl⟩ : syracuseStep 14615153 = 10961365) B10961365
theorem B1508165 : Blo 263822 1508165 := bstep (se 4 (by rfl) ⟨141390, by rfl⟩ : syracuseStep 1508165 = 282781) B282781
theorem B427331 : Blo 263822 427331 := bstep (se 1 (by rfl) ⟨320498, by rfl⟩ : syracuseStep 427331 = 640997) B640997
theorem B9733517 : Blo 263822 9733517 := bstep (se 3 (by rfl) ⟨1825034, by rfl⟩ : syracuseStep 9733517 = 3650069) B3650069
theorem B1148323 : Blo 263822 1148323 := bstep (se 1 (by rfl) ⟨861242, by rfl⟩ : syracuseStep 1148323 = 1722485) B1722485
theorem B755153 : Blo 263822 755153 := bstep (se 2 (by rfl) ⟨283182, by rfl⟩ : syracuseStep 755153 = 566365) B566365
theorem B951821 : Blo 263822 951821 := bstep (se 3 (by rfl) ⟨178466, by rfl⟩ : syracuseStep 951821 = 356933) B356933
theorem B427555 : Blo 263822 427555 := bstep (se 1 (by rfl) ⟨320666, by rfl⟩ : syracuseStep 427555 = 641333) B641333
theorem B427619 : Blo 263822 427619 := bstep (se 1 (by rfl) ⟨320714, by rfl⟩ : syracuseStep 427619 = 641429) B641429
theorem B853649 : Blo 263822 853649 := bstep (se 2 (by rfl) ⟨320118, by rfl⟩ : syracuseStep 853649 = 640237) B640237
theorem B263827 : Blo 263822 263827 := bstep (se 1 (by rfl) ⟨197870, by rfl⟩ : syracuseStep 263827 = 395741) B395741
theorem B263843 : Blo 263822 263843 := bstep (se 1 (by rfl) ⟨197882, by rfl⟩ : syracuseStep 263843 = 395765) B395765
theorem B263859 : Blo 263822 263859 := bstep (se 1 (by rfl) ⟨197894, by rfl⟩ : syracuseStep 263859 = 395789) B395789
theorem B263875 : Blo 263822 263875 := bstep (se 1 (by rfl) ⟨197906, by rfl⟩ : syracuseStep 263875 = 395813) B395813
theorem B2262725 : Blo 263822 2262725 := bstep (se 4 (by rfl) ⟨212130, by rfl⟩ : syracuseStep 2262725 = 424261) B424261
theorem B263891 : Blo 263822 263891 := bstep (se 1 (by rfl) ⟨197918, by rfl⟩ : syracuseStep 263891 = 395837) B395837
theorem B263907 : Blo 263822 263907 := bstep (se 1 (by rfl) ⟨197930, by rfl⟩ : syracuseStep 263907 = 395861) B395861
theorem B427747 : Blo 263822 427747 := bstep (se 1 (by rfl) ⟨320810, by rfl⟩ : syracuseStep 427747 = 641621) B641621
theorem B263923 : Blo 263822 263923 := bstep (se 1 (by rfl) ⟨197942, by rfl⟩ : syracuseStep 263923 = 395885) B395885
theorem B263939 : Blo 263822 263939 := bstep (se 1 (by rfl) ⟨197954, by rfl⟩ : syracuseStep 263939 = 395909) B395909
theorem B263955 : Blo 263822 263955 := bstep (se 1 (by rfl) ⟨197966, by rfl⟩ : syracuseStep 263955 = 395933) B395933
theorem B263971 : Blo 263822 263971 := bstep (se 1 (by rfl) ⟨197978, by rfl⟩ : syracuseStep 263971 = 395957) B395957
theorem B263987 : Blo 263822 263987 := bstep (se 1 (by rfl) ⟨197990, by rfl⟩ : syracuseStep 263987 = 395981) B395981
theorem B264003 : Blo 263822 264003 := bstep (se 1 (by rfl) ⟨198002, by rfl⟩ : syracuseStep 264003 = 396005) B396005
theorem B853841 : Blo 263822 853841 := bstep (se 2 (by rfl) ⟨320190, by rfl⟩ : syracuseStep 853841 = 640381) B640381
theorem B264019 : Blo 263822 264019 := bstep (se 1 (by rfl) ⟨198014, by rfl⟩ : syracuseStep 264019 = 396029) B396029
theorem B264035 : Blo 263822 264035 := bstep (se 1 (by rfl) ⟨198026, by rfl⟩ : syracuseStep 264035 = 396053) B396053
theorem B264051 : Blo 263822 264051 := bstep (se 1 (by rfl) ⟨198038, by rfl⟩ : syracuseStep 264051 = 396077) B396077
theorem B264067 : Blo 263822 264067 := bstep (se 1 (by rfl) ⟨198050, by rfl⟩ : syracuseStep 264067 = 396101) B396101
theorem B296851 : Blo 263822 296851 := bstep (se 1 (by rfl) ⟨222638, by rfl⟩ : syracuseStep 296851 = 445277) B445277
theorem B264083 : Blo 263822 264083 := bstep (se 1 (by rfl) ⟨198062, by rfl⟩ : syracuseStep 264083 = 396125) B396125
theorem B264099 : Blo 263822 264099 := bstep (se 1 (by rfl) ⟨198074, by rfl⟩ : syracuseStep 264099 = 396149) B396149
theorem B722861 : Blo 263822 722861 := bstep (se 3 (by rfl) ⟨135536, by rfl⟩ : syracuseStep 722861 = 271073) B271073
theorem B264115 : Blo 263822 264115 := bstep (se 1 (by rfl) ⟨198086, by rfl⟩ : syracuseStep 264115 = 396173) B396173
theorem B264131 : Blo 263822 264131 := bstep (se 1 (by rfl) ⟨198098, by rfl⟩ : syracuseStep 264131 = 396197) B396197
theorem B264147 : Blo 263822 264147 := bstep (se 1 (by rfl) ⟨198110, by rfl⟩ : syracuseStep 264147 = 396221) B396221
theorem B264163 : Blo 263822 264163 := bstep (se 1 (by rfl) ⟨198122, by rfl⟩ : syracuseStep 264163 = 396245) B396245
theorem B264179 : Blo 263822 264179 := bstep (se 1 (by rfl) ⟨198134, by rfl⟩ : syracuseStep 264179 = 396269) B396269
theorem B264195 : Blo 263822 264195 := bstep (se 1 (by rfl) ⟨198146, by rfl⟩ : syracuseStep 264195 = 396293) B396293
theorem B264211 : Blo 263822 264211 := bstep (se 1 (by rfl) ⟨198158, by rfl⟩ : syracuseStep 264211 = 396317) B396317
theorem B296995 : Blo 263822 296995 := bstep (se 1 (by rfl) ⟨222746, by rfl⟩ : syracuseStep 296995 = 445493) B445493
theorem B264227 : Blo 263822 264227 := bstep (se 1 (by rfl) ⟨198170, by rfl⟩ : syracuseStep 264227 = 396341) B396341
theorem B1345571 : Blo 263822 1345571 := bstep (se 1 (by rfl) ⟨1009178, by rfl⟩ : syracuseStep 1345571 = 2018357) B2018357
theorem B264243 : Blo 263822 264243 := bstep (se 1 (by rfl) ⟨198182, by rfl⟩ : syracuseStep 264243 = 396365) B396365
theorem B264259 : Blo 263822 264259 := bstep (se 1 (by rfl) ⟨198194, by rfl⟩ : syracuseStep 264259 = 396389) B396389
theorem B264275 : Blo 263822 264275 := bstep (se 1 (by rfl) ⟨198206, by rfl⟩ : syracuseStep 264275 = 396413) B396413
theorem B264291 : Blo 263822 264291 := bstep (se 1 (by rfl) ⟨198218, by rfl⟩ : syracuseStep 264291 = 396437) B396437
theorem B264307 : Blo 263822 264307 := bstep (se 1 (by rfl) ⟨198230, by rfl⟩ : syracuseStep 264307 = 396461) B396461
theorem B264323 : Blo 263822 264323 := bstep (se 1 (by rfl) ⟨198242, by rfl⟩ : syracuseStep 264323 = 396485) B396485
theorem B264339 : Blo 263822 264339 := bstep (se 1 (by rfl) ⟨198254, by rfl⟩ : syracuseStep 264339 = 396509) B396509
theorem B264355 : Blo 263822 264355 := bstep (se 1 (by rfl) ⟨198266, by rfl⟩ : syracuseStep 264355 = 396533) B396533
theorem B297139 : Blo 263822 297139 := bstep (se 1 (by rfl) ⟨222854, by rfl⟩ : syracuseStep 297139 = 445709) B445709
theorem B264371 : Blo 263822 264371 := bstep (se 1 (by rfl) ⟨198278, by rfl⟩ : syracuseStep 264371 = 396557) B396557
theorem B264387 : Blo 263822 264387 := bstep (se 1 (by rfl) ⟨198290, by rfl⟩ : syracuseStep 264387 = 396581) B396581
theorem B264403 : Blo 263822 264403 := bstep (se 1 (by rfl) ⟨198302, by rfl⟩ : syracuseStep 264403 = 396605) B396605
theorem B264419 : Blo 263822 264419 := bstep (se 1 (by rfl) ⟨198314, by rfl⟩ : syracuseStep 264419 = 396629) B396629
theorem B264435 : Blo 263822 264435 := bstep (se 1 (by rfl) ⟨198326, by rfl⟩ : syracuseStep 264435 = 396653) B396653
theorem B264451 : Blo 263822 264451 := bstep (se 1 (by rfl) ⟨198338, by rfl⟩ : syracuseStep 264451 = 396677) B396677
theorem B264467 : Blo 263822 264467 := bstep (se 1 (by rfl) ⟨198350, by rfl⟩ : syracuseStep 264467 = 396701) B396701
theorem B264483 : Blo 263822 264483 := bstep (se 1 (by rfl) ⟨198362, by rfl⟩ : syracuseStep 264483 = 396725) B396725
theorem B264499 : Blo 263822 264499 := bstep (se 1 (by rfl) ⟨198374, by rfl⟩ : syracuseStep 264499 = 396749) B396749
theorem B297283 : Blo 263822 297283 := bstep (se 1 (by rfl) ⟨222962, by rfl⟩ : syracuseStep 297283 = 445925) B445925
theorem B264515 : Blo 263822 264515 := bstep (se 1 (by rfl) ⟨198386, by rfl⟩ : syracuseStep 264515 = 396773) B396773
theorem B264531 : Blo 263822 264531 := bstep (se 1 (by rfl) ⟨198398, by rfl⟩ : syracuseStep 264531 = 396797) B396797
theorem B264547 : Blo 263822 264547 := bstep (se 1 (by rfl) ⟨198410, by rfl⟩ : syracuseStep 264547 = 396821) B396821
theorem B2263409 : Blo 263822 2263409 := bstep (se 2 (by rfl) ⟨848778, by rfl⟩ : syracuseStep 2263409 = 1697557) B1697557
theorem B264563 : Blo 263822 264563 := bstep (se 1 (by rfl) ⟨198422, by rfl⟩ : syracuseStep 264563 = 396845) B396845
theorem B264579 : Blo 263822 264579 := bstep (se 1 (by rfl) ⟨198434, by rfl⟩ : syracuseStep 264579 = 396869) B396869
theorem B264595 : Blo 263822 264595 := bstep (se 1 (by rfl) ⟨198446, by rfl⟩ : syracuseStep 264595 = 396893) B396893
theorem B362899 : Blo 263822 362899 := bstep (se 1 (by rfl) ⟨272174, by rfl⟩ : syracuseStep 362899 = 544349) B544349
theorem B264611 : Blo 263822 264611 := bstep (se 1 (by rfl) ⟨198458, by rfl⟩ : syracuseStep 264611 = 396917) B396917
theorem B428465 : Blo 263822 428465 := bstep (se 2 (by rfl) ⟨160674, by rfl⟩ : syracuseStep 428465 = 321349) B321349
theorem B264627 : Blo 263822 264627 := bstep (se 1 (by rfl) ⟨198470, by rfl⟩ : syracuseStep 264627 = 396941) B396941
theorem B264643 : Blo 263822 264643 := bstep (se 1 (by rfl) ⟨198482, by rfl⟩ : syracuseStep 264643 = 396965) B396965
theorem B297427 : Blo 263822 297427 := bstep (se 1 (by rfl) ⟨223070, by rfl⟩ : syracuseStep 297427 = 446141) B446141
theorem B264659 : Blo 263822 264659 := bstep (se 1 (by rfl) ⟨198494, by rfl⟩ : syracuseStep 264659 = 396989) B396989
theorem B395747 : Blo 263822 395747 := bstep (se 1 (by rfl) ⟨296810, by rfl⟩ : syracuseStep 395747 = 593621) B593621
theorem B264675 : Blo 263822 264675 := bstep (se 1 (by rfl) ⟨198506, by rfl⟩ : syracuseStep 264675 = 397013) B397013
theorem B264691 : Blo 263822 264691 := bstep (se 1 (by rfl) ⟨198518, by rfl⟩ : syracuseStep 264691 = 397037) B397037
theorem B395777 : Blo 263822 395777 := bstep (se 2 (by rfl) ⟨148416, by rfl⟩ : syracuseStep 395777 = 296833) B296833
theorem B264707 : Blo 263822 264707 := bstep (se 1 (by rfl) ⟨198530, by rfl⟩ : syracuseStep 264707 = 397061) B397061
theorem B395795 : Blo 263822 395795 := bstep (se 1 (by rfl) ⟨296846, by rfl⟩ : syracuseStep 395795 = 593693) B593693
theorem B264723 : Blo 263822 264723 := bstep (se 1 (by rfl) ⟨198542, by rfl⟩ : syracuseStep 264723 = 397085) B397085
theorem B264739 : Blo 263822 264739 := bstep (se 1 (by rfl) ⟨198554, by rfl⟩ : syracuseStep 264739 = 397109) B397109
theorem B395825 : Blo 263822 395825 := bstep (se 2 (by rfl) ⟨148434, by rfl⟩ : syracuseStep 395825 = 296869) B296869
theorem B428593 : Blo 263822 428593 := bstep (se 2 (by rfl) ⟨160722, by rfl⟩ : syracuseStep 428593 = 321445) B321445
theorem B264755 : Blo 263822 264755 := bstep (se 1 (by rfl) ⟨198566, by rfl⟩ : syracuseStep 264755 = 397133) B397133
theorem B395843 : Blo 263822 395843 := bstep (se 1 (by rfl) ⟨296882, by rfl⟩ : syracuseStep 395843 = 593765) B593765
theorem B264771 : Blo 263822 264771 := bstep (se 1 (by rfl) ⟨198578, by rfl⟩ : syracuseStep 264771 = 397157) B397157
theorem B264787 : Blo 263822 264787 := bstep (se 1 (by rfl) ⟨198590, by rfl⟩ : syracuseStep 264787 = 397181) B397181
theorem B395873 : Blo 263822 395873 := bstep (se 2 (by rfl) ⟨148452, by rfl⟩ : syracuseStep 395873 = 296905) B296905
theorem B297571 : Blo 263822 297571 := bstep (se 1 (by rfl) ⟨223178, by rfl⟩ : syracuseStep 297571 = 446357) B446357
theorem B264803 : Blo 263822 264803 := bstep (se 1 (by rfl) ⟨198602, by rfl⟩ : syracuseStep 264803 = 397205) B397205
theorem B395891 : Blo 263822 395891 := bstep (se 1 (by rfl) ⟨296918, by rfl⟩ : syracuseStep 395891 = 593837) B593837
theorem B264819 : Blo 263822 264819 := bstep (se 1 (by rfl) ⟨198614, by rfl⟩ : syracuseStep 264819 = 397229) B397229
theorem B264835 : Blo 263822 264835 := bstep (se 1 (by rfl) ⟨198626, by rfl⟩ : syracuseStep 264835 = 397253) B397253
theorem B395921 : Blo 263822 395921 := bstep (se 2 (by rfl) ⟨148470, by rfl⟩ : syracuseStep 395921 = 296941) B296941
theorem B264851 : Blo 263822 264851 := bstep (se 1 (by rfl) ⟨198638, by rfl⟩ : syracuseStep 264851 = 397277) B397277
theorem B395939 : Blo 263822 395939 := bstep (se 1 (by rfl) ⟨296954, by rfl⟩ : syracuseStep 395939 = 593909) B593909
theorem B264867 : Blo 263822 264867 := bstep (se 1 (by rfl) ⟨198650, by rfl⟩ : syracuseStep 264867 = 397301) B397301
theorem B264883 : Blo 263822 264883 := bstep (se 1 (by rfl) ⟨198662, by rfl⟩ : syracuseStep 264883 = 397325) B397325
theorem B395969 : Blo 263822 395969 := bstep (se 2 (by rfl) ⟨148488, by rfl⟩ : syracuseStep 395969 = 296977) B296977
theorem B264899 : Blo 263822 264899 := bstep (se 1 (by rfl) ⟨198674, by rfl⟩ : syracuseStep 264899 = 397349) B397349
theorem B395987 : Blo 263822 395987 := bstep (se 1 (by rfl) ⟨296990, by rfl⟩ : syracuseStep 395987 = 593981) B593981
theorem B264915 : Blo 263822 264915 := bstep (se 1 (by rfl) ⟨198686, by rfl⟩ : syracuseStep 264915 = 397373) B397373
theorem B264931 : Blo 263822 264931 := bstep (se 1 (by rfl) ⟨198698, by rfl⟩ : syracuseStep 264931 = 397397) B397397
theorem B396017 : Blo 263822 396017 := bstep (se 2 (by rfl) ⟨148506, by rfl⟩ : syracuseStep 396017 = 297013) B297013
theorem B297715 : Blo 263822 297715 := bstep (se 1 (by rfl) ⟨223286, by rfl⟩ : syracuseStep 297715 = 446573) B446573
theorem B264947 : Blo 263822 264947 := bstep (se 1 (by rfl) ⟨198710, by rfl⟩ : syracuseStep 264947 = 397421) B397421
theorem B396035 : Blo 263822 396035 := bstep (se 1 (by rfl) ⟨297026, by rfl⟩ : syracuseStep 396035 = 594053) B594053
theorem B264963 : Blo 263822 264963 := bstep (se 1 (by rfl) ⟨198722, by rfl⟩ : syracuseStep 264963 = 397445) B397445
theorem B264979 : Blo 263822 264979 := bstep (se 1 (by rfl) ⟨198734, by rfl⟩ : syracuseStep 264979 = 397469) B397469
theorem B396065 : Blo 263822 396065 := bstep (se 2 (by rfl) ⟨148524, by rfl⟩ : syracuseStep 396065 = 297049) B297049
theorem B264995 : Blo 263822 264995 := bstep (se 1 (by rfl) ⟨198746, by rfl⟩ : syracuseStep 264995 = 397493) B397493
theorem B1018673 : Blo 263822 1018673 := bstep (se 2 (by rfl) ⟨382002, by rfl⟩ : syracuseStep 1018673 = 764005) B764005
theorem B396083 : Blo 263822 396083 := bstep (se 1 (by rfl) ⟨297062, by rfl⟩ : syracuseStep 396083 = 594125) B594125
theorem B265011 : Blo 263822 265011 := bstep (se 1 (by rfl) ⟨198758, by rfl⟩ : syracuseStep 265011 = 397517) B397517
theorem B265027 : Blo 263822 265027 := bstep (se 1 (by rfl) ⟨198770, by rfl⟩ : syracuseStep 265027 = 397541) B397541
theorem B1346381 : Blo 263822 1346381 := bstep (se 3 (by rfl) ⟨252446, by rfl⟩ : syracuseStep 1346381 = 504893) B504893
theorem B396113 : Blo 263822 396113 := bstep (se 2 (by rfl) ⟨148542, by rfl⟩ : syracuseStep 396113 = 297085) B297085
theorem B265043 : Blo 263822 265043 := bstep (se 1 (by rfl) ⟨198782, by rfl⟩ : syracuseStep 265043 = 397565) B397565
theorem B396131 : Blo 263822 396131 := bstep (se 1 (by rfl) ⟨297098, by rfl⟩ : syracuseStep 396131 = 594197) B594197
theorem B265059 : Blo 263822 265059 := bstep (se 1 (by rfl) ⟨198794, by rfl⟩ : syracuseStep 265059 = 397589) B397589
theorem B265075 : Blo 263822 265075 := bstep (se 1 (by rfl) ⟨198806, by rfl⟩ : syracuseStep 265075 = 397613) B397613
theorem B396161 : Blo 263822 396161 := bstep (se 2 (by rfl) ⟨148560, by rfl⟩ : syracuseStep 396161 = 297121) B297121
theorem B297859 : Blo 263822 297859 := bstep (se 1 (by rfl) ⟨223394, by rfl⟩ : syracuseStep 297859 = 446789) B446789
theorem B265091 : Blo 263822 265091 := bstep (se 1 (by rfl) ⟨198818, by rfl⟩ : syracuseStep 265091 = 397637) B397637
theorem B756611 : Blo 263822 756611 := bstep (se 1 (by rfl) ⟨567458, by rfl⟩ : syracuseStep 756611 = 1134917) B1134917
theorem B396179 : Blo 263822 396179 := bstep (se 1 (by rfl) ⟨297134, by rfl⟩ : syracuseStep 396179 = 594269) B594269
theorem B265107 : Blo 263822 265107 := bstep (se 1 (by rfl) ⟨198830, by rfl⟩ : syracuseStep 265107 = 397661) B397661
theorem B265123 : Blo 263822 265123 := bstep (se 1 (by rfl) ⟨198842, by rfl⟩ : syracuseStep 265123 = 397685) B397685
theorem B396209 : Blo 263822 396209 := bstep (se 2 (by rfl) ⟨148578, by rfl⟩ : syracuseStep 396209 = 297157) B297157
theorem B428977 : Blo 263822 428977 := bstep (se 2 (by rfl) ⟨160866, by rfl⟩ : syracuseStep 428977 = 321733) B321733
theorem B265139 : Blo 263822 265139 := bstep (se 1 (by rfl) ⟨198854, by rfl⟩ : syracuseStep 265139 = 397709) B397709
theorem B396227 : Blo 263822 396227 := bstep (se 1 (by rfl) ⟨297170, by rfl⟩ : syracuseStep 396227 = 594341) B594341
theorem B265155 : Blo 263822 265155 := bstep (se 1 (by rfl) ⟨198866, by rfl⟩ : syracuseStep 265155 = 397733) B397733
theorem B265171 : Blo 263822 265171 := bstep (se 1 (by rfl) ⟨198878, by rfl⟩ : syracuseStep 265171 = 397757) B397757
theorem B396257 : Blo 263822 396257 := bstep (se 2 (by rfl) ⟨148596, by rfl⟩ : syracuseStep 396257 = 297193) B297193
theorem B265187 : Blo 263822 265187 := bstep (se 1 (by rfl) ⟨198890, by rfl⟩ : syracuseStep 265187 = 397781) B397781
theorem B396275 : Blo 263822 396275 := bstep (se 1 (by rfl) ⟨297206, by rfl⟩ : syracuseStep 396275 = 594413) B594413
theorem B265203 : Blo 263822 265203 := bstep (se 1 (by rfl) ⟨198902, by rfl⟩ : syracuseStep 265203 = 397805) B397805
theorem B265219 : Blo 263822 265219 := bstep (se 1 (by rfl) ⟨198914, by rfl⟩ : syracuseStep 265219 = 397829) B397829
theorem B396305 : Blo 263822 396305 := bstep (se 2 (by rfl) ⟨148614, by rfl⟩ : syracuseStep 396305 = 297229) B297229
theorem B298003 : Blo 263822 298003 := bstep (se 1 (by rfl) ⟨223502, by rfl⟩ : syracuseStep 298003 = 447005) B447005
theorem B265235 : Blo 263822 265235 := bstep (se 1 (by rfl) ⟨198926, by rfl⟩ : syracuseStep 265235 = 397853) B397853
theorem B396323 : Blo 263822 396323 := bstep (se 1 (by rfl) ⟨297242, by rfl⟩ : syracuseStep 396323 = 594485) B594485
theorem B265251 : Blo 263822 265251 := bstep (se 1 (by rfl) ⟨198938, by rfl⟩ : syracuseStep 265251 = 397877) B397877
theorem B265267 : Blo 263822 265267 := bstep (se 1 (by rfl) ⟨198950, by rfl⟩ : syracuseStep 265267 = 397901) B397901
theorem B396353 : Blo 263822 396353 := bstep (se 2 (by rfl) ⟨148632, by rfl⟩ : syracuseStep 396353 = 297265) B297265
theorem B265283 : Blo 263822 265283 := bstep (se 1 (by rfl) ⟨198962, by rfl⟩ : syracuseStep 265283 = 397925) B397925
theorem B396371 : Blo 263822 396371 := bstep (se 1 (by rfl) ⟨297278, by rfl⟩ : syracuseStep 396371 = 594557) B594557
theorem B265299 : Blo 263822 265299 := bstep (se 1 (by rfl) ⟨198974, by rfl⟩ : syracuseStep 265299 = 397949) B397949
theorem B265315 : Blo 263822 265315 := bstep (se 1 (by rfl) ⟨198986, by rfl⟩ : syracuseStep 265315 = 397973) B397973
theorem B396401 : Blo 263822 396401 := bstep (se 2 (by rfl) ⟨148650, by rfl⟩ : syracuseStep 396401 = 297301) B297301
theorem B265331 : Blo 263822 265331 := bstep (se 1 (by rfl) ⟨198998, by rfl⟩ : syracuseStep 265331 = 397997) B397997
theorem B396419 : Blo 263822 396419 := bstep (se 1 (by rfl) ⟨297314, by rfl⟩ : syracuseStep 396419 = 594629) B594629
theorem B265347 : Blo 263822 265347 := bstep (se 1 (by rfl) ⟨199010, by rfl⟩ : syracuseStep 265347 = 398021) B398021
theorem B265363 : Blo 263822 265363 := bstep (se 1 (by rfl) ⟨199022, by rfl⟩ : syracuseStep 265363 = 398045) B398045
theorem B396449 : Blo 263822 396449 := bstep (se 2 (by rfl) ⟨148668, by rfl⟩ : syracuseStep 396449 = 297337) B297337
theorem B298147 : Blo 263822 298147 := bstep (se 1 (by rfl) ⟨223610, by rfl⟩ : syracuseStep 298147 = 447221) B447221
theorem B265379 : Blo 263822 265379 := bstep (se 1 (by rfl) ⟨199034, by rfl⟩ : syracuseStep 265379 = 398069) B398069
theorem B396467 : Blo 263822 396467 := bstep (se 1 (by rfl) ⟨297350, by rfl⟩ : syracuseStep 396467 = 594701) B594701
theorem B265395 : Blo 263822 265395 := bstep (se 1 (by rfl) ⟨199046, by rfl⟩ : syracuseStep 265395 = 398093) B398093
theorem B265411 : Blo 263822 265411 := bstep (se 1 (by rfl) ⟨199058, by rfl⟩ : syracuseStep 265411 = 398117) B398117
theorem B396497 : Blo 263822 396497 := bstep (se 2 (by rfl) ⟨148686, by rfl⟩ : syracuseStep 396497 = 297373) B297373
theorem B265427 : Blo 263822 265427 := bstep (se 1 (by rfl) ⟨199070, by rfl⟩ : syracuseStep 265427 = 398141) B398141
theorem B396515 : Blo 263822 396515 := bstep (se 1 (by rfl) ⟨297386, by rfl⟩ : syracuseStep 396515 = 594773) B594773
theorem B265443 : Blo 263822 265443 := bstep (se 1 (by rfl) ⟨199082, by rfl⟩ : syracuseStep 265443 = 398165) B398165
theorem B265459 : Blo 263822 265459 := bstep (se 1 (by rfl) ⟨199094, by rfl⟩ : syracuseStep 265459 = 398189) B398189
theorem B396545 : Blo 263822 396545 := bstep (se 2 (by rfl) ⟨148704, by rfl⟩ : syracuseStep 396545 = 297409) B297409
theorem B265475 : Blo 263822 265475 := bstep (se 1 (by rfl) ⟨199106, by rfl⟩ : syracuseStep 265475 = 398213) B398213
theorem B396563 : Blo 263822 396563 := bstep (se 1 (by rfl) ⟨297422, by rfl⟩ : syracuseStep 396563 = 594845) B594845
theorem B265491 : Blo 263822 265491 := bstep (se 1 (by rfl) ⟨199118, by rfl⟩ : syracuseStep 265491 = 398237) B398237
theorem B265507 : Blo 263822 265507 := bstep (se 1 (by rfl) ⟨199130, by rfl⟩ : syracuseStep 265507 = 398261) B398261
theorem B396593 : Blo 263822 396593 := bstep (se 2 (by rfl) ⟨148722, by rfl⟩ : syracuseStep 396593 = 297445) B297445
theorem B298291 : Blo 263822 298291 := bstep (se 1 (by rfl) ⟨223718, by rfl⟩ : syracuseStep 298291 = 447437) B447437
theorem B265523 : Blo 263822 265523 := bstep (se 1 (by rfl) ⟨199142, by rfl⟩ : syracuseStep 265523 = 398285) B398285
theorem B396611 : Blo 263822 396611 := bstep (se 1 (by rfl) ⟨297458, by rfl⟩ : syracuseStep 396611 = 594917) B594917
theorem B265539 : Blo 263822 265539 := bstep (se 1 (by rfl) ⟨199154, by rfl⟩ : syracuseStep 265539 = 398309) B398309
theorem B265555 : Blo 263822 265555 := bstep (se 1 (by rfl) ⟨199166, by rfl⟩ : syracuseStep 265555 = 398333) B398333
theorem B396641 : Blo 263822 396641 := bstep (se 2 (by rfl) ⟨148740, by rfl⟩ : syracuseStep 396641 = 297481) B297481
theorem B265571 : Blo 263822 265571 := bstep (se 1 (by rfl) ⟨199178, by rfl⟩ : syracuseStep 265571 = 398357) B398357
theorem B396659 : Blo 263822 396659 := bstep (se 1 (by rfl) ⟨297494, by rfl⟩ : syracuseStep 396659 = 594989) B594989
theorem B265587 : Blo 263822 265587 := bstep (se 1 (by rfl) ⟨199190, by rfl⟩ : syracuseStep 265587 = 398381) B398381
theorem B265603 : Blo 263822 265603 := bstep (se 1 (by rfl) ⟨199202, by rfl⟩ : syracuseStep 265603 = 398405) B398405
theorem B396689 : Blo 263822 396689 := bstep (se 2 (by rfl) ⟨148758, by rfl⟩ : syracuseStep 396689 = 297517) B297517
theorem B265619 : Blo 263822 265619 := bstep (se 1 (by rfl) ⟨199214, by rfl⟩ : syracuseStep 265619 = 398429) B398429
theorem B396707 : Blo 263822 396707 := bstep (se 1 (by rfl) ⟨297530, by rfl⟩ : syracuseStep 396707 = 595061) B595061
theorem B265635 : Blo 263822 265635 := bstep (se 1 (by rfl) ⟨199226, by rfl⟩ : syracuseStep 265635 = 398453) B398453
theorem B265651 : Blo 263822 265651 := bstep (se 1 (by rfl) ⟨199238, by rfl⟩ : syracuseStep 265651 = 398477) B398477
theorem B396737 : Blo 263822 396737 := bstep (se 2 (by rfl) ⟨148776, by rfl⟩ : syracuseStep 396737 = 297553) B297553
theorem B298435 : Blo 263822 298435 := bstep (se 1 (by rfl) ⟨223826, by rfl⟩ : syracuseStep 298435 = 447653) B447653
theorem B265667 : Blo 263822 265667 := bstep (se 1 (by rfl) ⟨199250, by rfl⟩ : syracuseStep 265667 = 398501) B398501
theorem B396755 : Blo 263822 396755 := bstep (se 1 (by rfl) ⟨297566, by rfl⟩ : syracuseStep 396755 = 595133) B595133
theorem B265683 : Blo 263822 265683 := bstep (se 1 (by rfl) ⟨199262, by rfl⟩ : syracuseStep 265683 = 398525) B398525
theorem B265699 : Blo 263822 265699 := bstep (se 1 (by rfl) ⟨199274, by rfl⟩ : syracuseStep 265699 = 398549) B398549
theorem B396785 : Blo 263822 396785 := bstep (se 2 (by rfl) ⟨148794, by rfl⟩ : syracuseStep 396785 = 297589) B297589
theorem B265715 : Blo 263822 265715 := bstep (se 1 (by rfl) ⟨199286, by rfl⟩ : syracuseStep 265715 = 398573) B398573
theorem B396803 : Blo 263822 396803 := bstep (se 1 (by rfl) ⟨297602, by rfl⟩ : syracuseStep 396803 = 595205) B595205
theorem B265731 : Blo 263822 265731 := bstep (se 1 (by rfl) ⟨199298, by rfl⟩ : syracuseStep 265731 = 398597) B398597
theorem B265747 : Blo 263822 265747 := bstep (se 1 (by rfl) ⟨199310, by rfl⟩ : syracuseStep 265747 = 398621) B398621
theorem B396833 : Blo 263822 396833 := bstep (se 2 (by rfl) ⟨148812, by rfl⟩ : syracuseStep 396833 = 297625) B297625
theorem B265763 : Blo 263822 265763 := bstep (se 1 (by rfl) ⟨199322, by rfl⟩ : syracuseStep 265763 = 398645) B398645
theorem B396851 : Blo 263822 396851 := bstep (se 1 (by rfl) ⟨297638, by rfl⟩ : syracuseStep 396851 = 595277) B595277
theorem B265779 : Blo 263822 265779 := bstep (se 1 (by rfl) ⟨199334, by rfl⟩ : syracuseStep 265779 = 398669) B398669
theorem B265795 : Blo 263822 265795 := bstep (se 1 (by rfl) ⟨199346, by rfl⟩ : syracuseStep 265795 = 398693) B398693
theorem B2362949 : Blo 263822 2362949 := bstep (se 4 (by rfl) ⟨221526, by rfl⟩ : syracuseStep 2362949 = 443053) B443053
theorem B396881 : Blo 263822 396881 := bstep (se 2 (by rfl) ⟨148830, by rfl⟩ : syracuseStep 396881 = 297661) B297661
theorem B298579 : Blo 263822 298579 := bstep (se 1 (by rfl) ⟨223934, by rfl⟩ : syracuseStep 298579 = 447869) B447869
theorem B265811 : Blo 263822 265811 := bstep (se 1 (by rfl) ⟨199358, by rfl⟩ : syracuseStep 265811 = 398717) B398717
theorem B396899 : Blo 263822 396899 := bstep (se 1 (by rfl) ⟨297674, by rfl⟩ : syracuseStep 396899 = 595349) B595349
theorem B265827 : Blo 263822 265827 := bstep (se 1 (by rfl) ⟨199370, by rfl⟩ : syracuseStep 265827 = 398741) B398741
theorem B265843 : Blo 263822 265843 := bstep (se 1 (by rfl) ⟨199382, by rfl⟩ : syracuseStep 265843 = 398765) B398765
theorem B396929 : Blo 263822 396929 := bstep (se 2 (by rfl) ⟨148848, by rfl⟩ : syracuseStep 396929 = 297697) B297697
theorem B265859 : Blo 263822 265859 := bstep (se 1 (by rfl) ⟨199394, by rfl⟩ : syracuseStep 265859 = 398789) B398789
theorem B396947 : Blo 263822 396947 := bstep (se 1 (by rfl) ⟨297710, by rfl⟩ : syracuseStep 396947 = 595421) B595421
theorem B265875 : Blo 263822 265875 := bstep (se 1 (by rfl) ⟨199406, by rfl⟩ : syracuseStep 265875 = 398813) B398813
theorem B265891 : Blo 263822 265891 := bstep (se 1 (by rfl) ⟨199418, by rfl⟩ : syracuseStep 265891 = 398837) B398837
theorem B757421 : Blo 263822 757421 := bstep (se 3 (by rfl) ⟨142016, by rfl⟩ : syracuseStep 757421 = 284033) B284033
theorem B396977 : Blo 263822 396977 := bstep (se 2 (by rfl) ⟨148866, by rfl⟩ : syracuseStep 396977 = 297733) B297733
theorem B265907 : Blo 263822 265907 := bstep (se 1 (by rfl) ⟨199430, by rfl⟩ : syracuseStep 265907 = 398861) B398861
theorem B593603 : Blo 263822 593603 := bstep (se 1 (by rfl) ⟨445202, by rfl⟩ : syracuseStep 593603 = 890405) B890405
theorem B396995 : Blo 263822 396995 := bstep (se 1 (by rfl) ⟨297746, by rfl⟩ : syracuseStep 396995 = 595493) B595493
theorem B265923 : Blo 263822 265923 := bstep (se 1 (by rfl) ⟨199442, by rfl⟩ : syracuseStep 265923 = 398885) B398885
theorem B265939 : Blo 263822 265939 := bstep (se 1 (by rfl) ⟨199454, by rfl⟩ : syracuseStep 265939 = 398909) B398909
theorem B397025 : Blo 263822 397025 := bstep (se 2 (by rfl) ⟨148884, by rfl⟩ : syracuseStep 397025 = 297769) B297769
theorem B298723 : Blo 263822 298723 := bstep (se 1 (by rfl) ⟨224042, by rfl⟩ : syracuseStep 298723 = 448085) B448085
theorem B265955 : Blo 263822 265955 := bstep (se 1 (by rfl) ⟨199466, by rfl⟩ : syracuseStep 265955 = 398933) B398933
theorem B397043 : Blo 263822 397043 := bstep (se 1 (by rfl) ⟨297782, by rfl⟩ : syracuseStep 397043 = 595565) B595565
theorem B265971 : Blo 263822 265971 := bstep (se 1 (by rfl) ⟨199478, by rfl⟩ : syracuseStep 265971 = 398957) B398957
theorem B265987 : Blo 263822 265987 := bstep (se 1 (by rfl) ⟨199490, by rfl⟩ : syracuseStep 265987 = 398981) B398981
theorem B397073 : Blo 263822 397073 := bstep (se 2 (by rfl) ⟨148902, by rfl⟩ : syracuseStep 397073 = 297805) B297805
theorem B266003 : Blo 263822 266003 := bstep (se 1 (by rfl) ⟨199502, by rfl⟩ : syracuseStep 266003 = 399005) B399005
theorem B397091 : Blo 263822 397091 := bstep (se 1 (by rfl) ⟨297818, by rfl⟩ : syracuseStep 397091 = 595637) B595637
theorem B266019 : Blo 263822 266019 := bstep (se 1 (by rfl) ⟨199514, by rfl⟩ : syracuseStep 266019 = 399029) B399029
theorem B266035 : Blo 263822 266035 := bstep (se 1 (by rfl) ⟨199526, by rfl⟩ : syracuseStep 266035 = 399053) B399053
theorem B397121 : Blo 263822 397121 := bstep (se 2 (by rfl) ⟨148920, by rfl⟩ : syracuseStep 397121 = 297841) B297841
theorem B266051 : Blo 263822 266051 := bstep (se 1 (by rfl) ⟨199538, by rfl⟩ : syracuseStep 266051 = 399077) B399077
theorem B397139 : Blo 263822 397139 := bstep (se 1 (by rfl) ⟨297854, by rfl⟩ : syracuseStep 397139 = 595709) B595709
theorem B266067 : Blo 263822 266067 := bstep (se 1 (by rfl) ⟨199550, by rfl⟩ : syracuseStep 266067 = 399101) B399101
theorem B266083 : Blo 263822 266083 := bstep (se 1 (by rfl) ⟨199562, by rfl⟩ : syracuseStep 266083 = 399125) B399125
theorem B757613 : Blo 263822 757613 := bstep (se 3 (by rfl) ⟨142052, by rfl⟩ : syracuseStep 757613 = 284105) B284105
theorem B397169 : Blo 263822 397169 := bstep (se 2 (by rfl) ⟨148938, by rfl⟩ : syracuseStep 397169 = 297877) B297877
theorem B298867 : Blo 263822 298867 := bstep (se 1 (by rfl) ⟨224150, by rfl⟩ : syracuseStep 298867 = 448301) B448301
theorem B266099 : Blo 263822 266099 := bstep (se 1 (by rfl) ⟨199574, by rfl⟩ : syracuseStep 266099 = 399149) B399149
theorem B397187 : Blo 263822 397187 := bstep (se 1 (by rfl) ⟨297890, by rfl⟩ : syracuseStep 397187 = 595781) B595781
theorem B266115 : Blo 263822 266115 := bstep (se 1 (by rfl) ⟨199586, by rfl⟩ : syracuseStep 266115 = 399173) B399173
theorem B266131 : Blo 263822 266131 := bstep (se 1 (by rfl) ⟨199598, by rfl⟩ : syracuseStep 266131 = 399197) B399197
theorem B397217 : Blo 263822 397217 := bstep (se 2 (by rfl) ⟨148956, by rfl⟩ : syracuseStep 397217 = 297913) B297913
theorem B266147 : Blo 263822 266147 := bstep (se 1 (by rfl) ⟨199610, by rfl⟩ : syracuseStep 266147 = 399221) B399221
theorem B397235 : Blo 263822 397235 := bstep (se 1 (by rfl) ⟨297926, by rfl⟩ : syracuseStep 397235 = 595853) B595853
theorem B266163 : Blo 263822 266163 := bstep (se 1 (by rfl) ⟨199622, by rfl⟩ : syracuseStep 266163 = 399245) B399245
theorem B266179 : Blo 263822 266179 := bstep (se 1 (by rfl) ⟨199634, by rfl⟩ : syracuseStep 266179 = 399269) B399269
theorem B593873 : Blo 263822 593873 := bstep (se 2 (by rfl) ⟨222702, by rfl⟩ : syracuseStep 593873 = 445405) B445405
theorem B397265 : Blo 263822 397265 := bstep (se 2 (by rfl) ⟨148974, by rfl⟩ : syracuseStep 397265 = 297949) B297949
theorem B266195 : Blo 263822 266195 := bstep (se 1 (by rfl) ⟨199646, by rfl⟩ : syracuseStep 266195 = 399293) B399293
theorem B593891 : Blo 263822 593891 := bstep (se 1 (by rfl) ⟨445418, by rfl⟩ : syracuseStep 593891 = 890837) B890837
theorem B397283 : Blo 263822 397283 := bstep (se 1 (by rfl) ⟨297962, by rfl⟩ : syracuseStep 397283 = 595925) B595925
theorem B266211 : Blo 263822 266211 := bstep (se 1 (by rfl) ⟨199658, by rfl⟩ : syracuseStep 266211 = 399317) B399317
theorem B266227 : Blo 263822 266227 := bstep (se 1 (by rfl) ⟨199670, by rfl⟩ : syracuseStep 266227 = 399341) B399341
theorem B397313 : Blo 263822 397313 := bstep (se 2 (by rfl) ⟨148992, by rfl⟩ : syracuseStep 397313 = 297985) B297985
theorem B299011 : Blo 263822 299011 := bstep (se 1 (by rfl) ⟨224258, by rfl⟩ : syracuseStep 299011 = 448517) B448517
theorem B266243 : Blo 263822 266243 := bstep (se 1 (by rfl) ⟨199682, by rfl⟩ : syracuseStep 266243 = 399365) B399365
theorem B397331 : Blo 263822 397331 := bstep (se 1 (by rfl) ⟨297998, by rfl⟩ : syracuseStep 397331 = 595997) B595997
theorem B266259 : Blo 263822 266259 := bstep (se 1 (by rfl) ⟨199694, by rfl⟩ : syracuseStep 266259 = 399389) B399389
theorem B266275 : Blo 263822 266275 := bstep (se 1 (by rfl) ⟨199706, by rfl⟩ : syracuseStep 266275 = 399413) B399413
theorem B856109 : Blo 263822 856109 := bstep (se 3 (by rfl) ⟨160520, by rfl⟩ : syracuseStep 856109 = 321041) B321041
theorem B397361 : Blo 263822 397361 := bstep (se 2 (by rfl) ⟨149010, by rfl⟩ : syracuseStep 397361 = 298021) B298021
theorem B266291 : Blo 263822 266291 := bstep (se 1 (by rfl) ⟨199718, by rfl⟩ : syracuseStep 266291 = 399437) B399437
theorem B397379 : Blo 263822 397379 := bstep (se 1 (by rfl) ⟨298034, by rfl⟩ : syracuseStep 397379 = 596069) B596069
theorem B266307 : Blo 263822 266307 := bstep (se 1 (by rfl) ⟨199730, by rfl⟩ : syracuseStep 266307 = 399461) B399461
theorem B266323 : Blo 263822 266323 := bstep (se 1 (by rfl) ⟨199742, by rfl⟩ : syracuseStep 266323 = 399485) B399485
theorem B397409 : Blo 263822 397409 := bstep (se 2 (by rfl) ⟨149028, by rfl⟩ : syracuseStep 397409 = 298057) B298057
theorem B266339 : Blo 263822 266339 := bstep (se 1 (by rfl) ⟨199754, by rfl⟩ : syracuseStep 266339 = 399509) B399509
theorem B397427 : Blo 263822 397427 := bstep (se 1 (by rfl) ⟨298070, by rfl⟩ : syracuseStep 397427 = 596141) B596141
theorem B266355 : Blo 263822 266355 := bstep (se 1 (by rfl) ⟨199766, by rfl⟩ : syracuseStep 266355 = 399533) B399533
theorem B266371 : Blo 263822 266371 := bstep (se 1 (by rfl) ⟨199778, by rfl⟩ : syracuseStep 266371 = 399557) B399557
theorem B397457 : Blo 263822 397457 := bstep (se 2 (by rfl) ⟨149046, by rfl⟩ : syracuseStep 397457 = 298093) B298093
theorem B299155 : Blo 263822 299155 := bstep (se 1 (by rfl) ⟨224366, by rfl⟩ : syracuseStep 299155 = 448733) B448733
theorem B266387 : Blo 263822 266387 := bstep (se 1 (by rfl) ⟨199790, by rfl⟩ : syracuseStep 266387 = 399581) B399581
theorem B397475 : Blo 263822 397475 := bstep (se 1 (by rfl) ⟨298106, by rfl⟩ : syracuseStep 397475 = 596213) B596213
theorem B266403 : Blo 263822 266403 := bstep (se 1 (by rfl) ⟨199802, by rfl⟩ : syracuseStep 266403 = 399605) B399605
theorem B266419 : Blo 263822 266419 := bstep (se 1 (by rfl) ⟨199814, by rfl⟩ : syracuseStep 266419 = 399629) B399629
theorem B397505 : Blo 263822 397505 := bstep (se 2 (by rfl) ⟨149064, by rfl⟩ : syracuseStep 397505 = 298129) B298129
theorem B266435 : Blo 263822 266435 := bstep (se 1 (by rfl) ⟨199826, by rfl⟩ : syracuseStep 266435 = 399653) B399653
theorem B397523 : Blo 263822 397523 := bstep (se 1 (by rfl) ⟨298142, by rfl⟩ : syracuseStep 397523 = 596285) B596285
theorem B266451 : Blo 263822 266451 := bstep (se 1 (by rfl) ⟨199838, by rfl⟩ : syracuseStep 266451 = 399677) B399677
theorem B266467 : Blo 263822 266467 := bstep (se 1 (by rfl) ⟨199850, by rfl⟩ : syracuseStep 266467 = 399701) B399701
theorem B594161 : Blo 263822 594161 := bstep (se 2 (by rfl) ⟨222810, by rfl⟩ : syracuseStep 594161 = 445621) B445621
theorem B397553 : Blo 263822 397553 := bstep (se 2 (by rfl) ⟨149082, by rfl⟩ : syracuseStep 397553 = 298165) B298165
theorem B266483 : Blo 263822 266483 := bstep (se 1 (by rfl) ⟨199862, by rfl⟩ : syracuseStep 266483 = 399725) B399725
theorem B594179 : Blo 263822 594179 := bstep (se 1 (by rfl) ⟨445634, by rfl⟩ : syracuseStep 594179 = 891269) B891269
theorem B397571 : Blo 263822 397571 := bstep (se 1 (by rfl) ⟨298178, by rfl⟩ : syracuseStep 397571 = 596357) B596357
theorem B266499 : Blo 263822 266499 := bstep (se 1 (by rfl) ⟨199874, by rfl⟩ : syracuseStep 266499 = 399749) B399749
theorem B266515 : Blo 263822 266515 := bstep (se 1 (by rfl) ⟨199886, by rfl⟩ : syracuseStep 266515 = 399773) B399773
theorem B397601 : Blo 263822 397601 := bstep (se 2 (by rfl) ⟨149100, by rfl⟩ : syracuseStep 397601 = 298201) B298201
theorem B299299 : Blo 263822 299299 := bstep (se 1 (by rfl) ⟨224474, by rfl⟩ : syracuseStep 299299 = 448949) B448949
theorem B266531 : Blo 263822 266531 := bstep (se 1 (by rfl) ⟨199898, by rfl⟩ : syracuseStep 266531 = 399797) B399797
theorem B397619 : Blo 263822 397619 := bstep (se 1 (by rfl) ⟨298214, by rfl⟩ : syracuseStep 397619 = 596429) B596429
theorem B266547 : Blo 263822 266547 := bstep (se 1 (by rfl) ⟨199910, by rfl⟩ : syracuseStep 266547 = 399821) B399821
theorem B266563 : Blo 263822 266563 := bstep (se 1 (by rfl) ⟨199922, by rfl⟩ : syracuseStep 266563 = 399845) B399845
theorem B397649 : Blo 263822 397649 := bstep (se 2 (by rfl) ⟨149118, by rfl⟩ : syracuseStep 397649 = 298237) B298237
theorem B266579 : Blo 263822 266579 := bstep (se 1 (by rfl) ⟨199934, by rfl⟩ : syracuseStep 266579 = 399869) B399869
theorem B397667 : Blo 263822 397667 := bstep (se 1 (by rfl) ⟨298250, by rfl⟩ : syracuseStep 397667 = 596501) B596501
theorem B266595 : Blo 263822 266595 := bstep (se 1 (by rfl) ⟨199946, by rfl⟩ : syracuseStep 266595 = 399893) B399893
theorem B266611 : Blo 263822 266611 := bstep (se 1 (by rfl) ⟨199958, by rfl⟩ : syracuseStep 266611 = 399917) B399917
theorem B397697 : Blo 263822 397697 := bstep (se 2 (by rfl) ⟨149136, by rfl⟩ : syracuseStep 397697 = 298273) B298273
theorem B266627 : Blo 263822 266627 := bstep (se 1 (by rfl) ⟨199970, by rfl⟩ : syracuseStep 266627 = 399941) B399941
theorem B397715 : Blo 263822 397715 := bstep (se 1 (by rfl) ⟨298286, by rfl⟩ : syracuseStep 397715 = 596573) B596573
theorem B266643 : Blo 263822 266643 := bstep (se 1 (by rfl) ⟨199982, by rfl⟩ : syracuseStep 266643 = 399965) B399965
theorem B266659 : Blo 263822 266659 := bstep (se 1 (by rfl) ⟨199994, by rfl⟩ : syracuseStep 266659 = 399989) B399989
theorem B397745 : Blo 263822 397745 := bstep (se 2 (by rfl) ⟨149154, by rfl⟩ : syracuseStep 397745 = 298309) B298309
theorem B299443 : Blo 263822 299443 := bstep (se 1 (by rfl) ⟨224582, by rfl⟩ : syracuseStep 299443 = 449165) B449165
theorem B266675 : Blo 263822 266675 := bstep (se 1 (by rfl) ⟨200006, by rfl⟩ : syracuseStep 266675 = 400013) B400013
theorem B397763 : Blo 263822 397763 := bstep (se 1 (by rfl) ⟨298322, by rfl⟩ : syracuseStep 397763 = 596645) B596645
theorem B266691 : Blo 263822 266691 := bstep (se 1 (by rfl) ⟨200018, by rfl⟩ : syracuseStep 266691 = 400037) B400037
theorem B266707 : Blo 263822 266707 := bstep (se 1 (by rfl) ⟨200030, by rfl⟩ : syracuseStep 266707 = 400061) B400061
theorem B397793 : Blo 263822 397793 := bstep (se 2 (by rfl) ⟨149172, by rfl⟩ : syracuseStep 397793 = 298345) B298345
theorem B266723 : Blo 263822 266723 := bstep (se 1 (by rfl) ⟨200042, by rfl⟩ : syracuseStep 266723 = 400085) B400085
theorem B397811 : Blo 263822 397811 := bstep (se 1 (by rfl) ⟨298358, by rfl⟩ : syracuseStep 397811 = 596717) B596717
theorem B266739 : Blo 263822 266739 := bstep (se 1 (by rfl) ⟨200054, by rfl⟩ : syracuseStep 266739 = 400109) B400109
theorem B266755 : Blo 263822 266755 := bstep (se 1 (by rfl) ⟨200066, by rfl⟩ : syracuseStep 266755 = 400133) B400133
theorem B594449 : Blo 263822 594449 := bstep (se 2 (by rfl) ⟨222918, by rfl⟩ : syracuseStep 594449 = 445837) B445837
theorem B397841 : Blo 263822 397841 := bstep (se 2 (by rfl) ⟨149190, by rfl⟩ : syracuseStep 397841 = 298381) B298381
theorem B266771 : Blo 263822 266771 := bstep (se 1 (by rfl) ⟨200078, by rfl⟩ : syracuseStep 266771 = 400157) B400157
theorem B594467 : Blo 263822 594467 := bstep (se 1 (by rfl) ⟨445850, by rfl⟩ : syracuseStep 594467 = 891701) B891701
theorem B397859 : Blo 263822 397859 := bstep (se 1 (by rfl) ⟨298394, by rfl⟩ : syracuseStep 397859 = 596789) B596789
theorem B266787 : Blo 263822 266787 := bstep (se 1 (by rfl) ⟨200090, by rfl⟩ : syracuseStep 266787 = 400181) B400181
theorem B266803 : Blo 263822 266803 := bstep (se 1 (by rfl) ⟨200102, by rfl⟩ : syracuseStep 266803 = 400205) B400205
theorem B397889 : Blo 263822 397889 := bstep (se 2 (by rfl) ⟨149208, by rfl⟩ : syracuseStep 397889 = 298417) B298417
theorem B299587 : Blo 263822 299587 := bstep (se 1 (by rfl) ⟨224690, by rfl⟩ : syracuseStep 299587 = 449381) B449381
theorem B266819 : Blo 263822 266819 := bstep (se 1 (by rfl) ⟨200114, by rfl⟩ : syracuseStep 266819 = 400229) B400229
theorem B397907 : Blo 263822 397907 := bstep (se 1 (by rfl) ⟨298430, by rfl⟩ : syracuseStep 397907 = 596861) B596861
theorem B266835 : Blo 263822 266835 := bstep (se 1 (by rfl) ⟨200126, by rfl⟩ : syracuseStep 266835 = 400253) B400253
theorem B266851 : Blo 263822 266851 := bstep (se 1 (by rfl) ⟨200138, by rfl⟩ : syracuseStep 266851 = 400277) B400277
theorem B397937 : Blo 263822 397937 := bstep (se 2 (by rfl) ⟨149226, by rfl⟩ : syracuseStep 397937 = 298453) B298453
theorem B266867 : Blo 263822 266867 := bstep (se 1 (by rfl) ⟨200150, by rfl⟩ : syracuseStep 266867 = 400301) B400301
theorem B397955 : Blo 263822 397955 := bstep (se 1 (by rfl) ⟨298466, by rfl⟩ : syracuseStep 397955 = 596933) B596933
theorem B266883 : Blo 263822 266883 := bstep (se 1 (by rfl) ⟨200162, by rfl⟩ : syracuseStep 266883 = 400325) B400325
theorem B266899 : Blo 263822 266899 := bstep (se 1 (by rfl) ⟨200174, by rfl⟩ : syracuseStep 266899 = 400349) B400349
theorem B397985 : Blo 263822 397985 := bstep (se 2 (by rfl) ⟨149244, by rfl⟩ : syracuseStep 397985 = 298489) B298489
theorem B266915 : Blo 263822 266915 := bstep (se 1 (by rfl) ⟨200186, by rfl⟩ : syracuseStep 266915 = 400373) B400373
theorem B398003 : Blo 263822 398003 := bstep (se 1 (by rfl) ⟨298502, by rfl⟩ : syracuseStep 398003 = 597005) B597005
theorem B266931 : Blo 263822 266931 := bstep (se 1 (by rfl) ⟨200198, by rfl⟩ : syracuseStep 266931 = 400397) B400397
theorem B266947 : Blo 263822 266947 := bstep (se 1 (by rfl) ⟨200210, by rfl⟩ : syracuseStep 266947 = 400421) B400421
theorem B398033 : Blo 263822 398033 := bstep (se 2 (by rfl) ⟨149262, by rfl⟩ : syracuseStep 398033 = 298525) B298525
theorem B299731 : Blo 263822 299731 := bstep (se 1 (by rfl) ⟨224798, by rfl⟩ : syracuseStep 299731 = 449597) B449597
theorem B266963 : Blo 263822 266963 := bstep (se 1 (by rfl) ⟨200222, by rfl⟩ : syracuseStep 266963 = 400445) B400445
theorem B398051 : Blo 263822 398051 := bstep (se 1 (by rfl) ⟨298538, by rfl⟩ : syracuseStep 398051 = 597077) B597077
theorem B266979 : Blo 263822 266979 := bstep (se 1 (by rfl) ⟨200234, by rfl⟩ : syracuseStep 266979 = 400469) B400469
theorem B266995 : Blo 263822 266995 := bstep (se 1 (by rfl) ⟨200246, by rfl⟩ : syracuseStep 266995 = 400493) B400493
theorem B398081 : Blo 263822 398081 := bstep (se 2 (by rfl) ⟨149280, by rfl⟩ : syracuseStep 398081 = 298561) B298561
theorem B267011 : Blo 263822 267011 := bstep (se 1 (by rfl) ⟨200258, by rfl⟩ : syracuseStep 267011 = 400517) B400517
theorem B398099 : Blo 263822 398099 := bstep (se 1 (by rfl) ⟨298574, by rfl⟩ : syracuseStep 398099 = 597149) B597149
theorem B267027 : Blo 263822 267027 := bstep (se 1 (by rfl) ⟨200270, by rfl⟩ : syracuseStep 267027 = 400541) B400541
theorem B267043 : Blo 263822 267043 := bstep (se 1 (by rfl) ⟨200282, by rfl⟩ : syracuseStep 267043 = 400565) B400565
theorem B594737 : Blo 263822 594737 := bstep (se 2 (by rfl) ⟨223026, by rfl⟩ : syracuseStep 594737 = 446053) B446053
theorem B398129 : Blo 263822 398129 := bstep (se 2 (by rfl) ⟨149298, by rfl⟩ : syracuseStep 398129 = 298597) B298597
theorem B267059 : Blo 263822 267059 := bstep (se 1 (by rfl) ⟨200294, by rfl⟩ : syracuseStep 267059 = 400589) B400589
theorem B594755 : Blo 263822 594755 := bstep (se 1 (by rfl) ⟨446066, by rfl⟩ : syracuseStep 594755 = 892133) B892133
theorem B398147 : Blo 263822 398147 := bstep (se 1 (by rfl) ⟨298610, by rfl⟩ : syracuseStep 398147 = 597221) B597221
theorem B267075 : Blo 263822 267075 := bstep (se 1 (by rfl) ⟨200306, by rfl⟩ : syracuseStep 267075 = 400613) B400613
theorem B758605 : Blo 263822 758605 := bstep (se 3 (by rfl) ⟨142238, by rfl⟩ : syracuseStep 758605 = 284477) B284477
theorem B267091 : Blo 263822 267091 := bstep (se 1 (by rfl) ⟨200318, by rfl⟩ : syracuseStep 267091 = 400637) B400637
theorem B398177 : Blo 263822 398177 := bstep (se 2 (by rfl) ⟨149316, by rfl⟩ : syracuseStep 398177 = 298633) B298633
theorem B299875 : Blo 263822 299875 := bstep (se 1 (by rfl) ⟨224906, by rfl⟩ : syracuseStep 299875 = 449813) B449813
theorem B267107 : Blo 263822 267107 := bstep (se 1 (by rfl) ⟨200330, by rfl⟩ : syracuseStep 267107 = 400661) B400661
theorem B398195 : Blo 263822 398195 := bstep (se 1 (by rfl) ⟨298646, by rfl⟩ : syracuseStep 398195 = 597293) B597293
theorem B267123 : Blo 263822 267123 := bstep (se 1 (by rfl) ⟨200342, by rfl⟩ : syracuseStep 267123 = 400685) B400685
theorem B267139 : Blo 263822 267139 := bstep (se 1 (by rfl) ⟨200354, by rfl⟩ : syracuseStep 267139 = 400709) B400709
theorem B398225 : Blo 263822 398225 := bstep (se 2 (by rfl) ⟨149334, by rfl⟩ : syracuseStep 398225 = 298669) B298669
theorem B267155 : Blo 263822 267155 := bstep (se 1 (by rfl) ⟨200366, by rfl⟩ : syracuseStep 267155 = 400733) B400733
theorem B398243 : Blo 263822 398243 := bstep (se 1 (by rfl) ⟨298682, by rfl⟩ : syracuseStep 398243 = 597365) B597365
theorem B267171 : Blo 263822 267171 := bstep (se 1 (by rfl) ⟨200378, by rfl⟩ : syracuseStep 267171 = 400757) B400757
theorem B267187 : Blo 263822 267187 := bstep (se 1 (by rfl) ⟨200390, by rfl⟩ : syracuseStep 267187 = 400781) B400781
theorem B398273 : Blo 263822 398273 := bstep (se 2 (by rfl) ⟨149352, by rfl⟩ : syracuseStep 398273 = 298705) B298705
theorem B267203 : Blo 263822 267203 := bstep (se 1 (by rfl) ⟨200402, by rfl⟩ : syracuseStep 267203 = 400805) B400805
theorem B398291 : Blo 263822 398291 := bstep (se 1 (by rfl) ⟨298718, by rfl⟩ : syracuseStep 398291 = 597437) B597437
theorem B267219 : Blo 263822 267219 := bstep (se 1 (by rfl) ⟨200414, by rfl⟩ : syracuseStep 267219 = 400829) B400829
theorem B267235 : Blo 263822 267235 := bstep (se 1 (by rfl) ⟨200426, by rfl⟩ : syracuseStep 267235 = 400853) B400853
theorem B398321 : Blo 263822 398321 := bstep (se 2 (by rfl) ⟨149370, by rfl⟩ : syracuseStep 398321 = 298741) B298741
theorem B300019 : Blo 263822 300019 := bstep (se 1 (by rfl) ⟨225014, by rfl⟩ : syracuseStep 300019 = 450029) B450029
theorem B267251 : Blo 263822 267251 := bstep (se 1 (by rfl) ⟨200438, by rfl⟩ : syracuseStep 267251 = 400877) B400877
theorem B398339 : Blo 263822 398339 := bstep (se 1 (by rfl) ⟨298754, by rfl⟩ : syracuseStep 398339 = 597509) B597509
theorem B267267 : Blo 263822 267267 := bstep (se 1 (by rfl) ⟨200450, by rfl⟩ : syracuseStep 267267 = 400901) B400901
theorem B267283 : Blo 263822 267283 := bstep (se 1 (by rfl) ⟨200462, by rfl⟩ : syracuseStep 267283 = 400925) B400925
theorem B398369 : Blo 263822 398369 := bstep (se 2 (by rfl) ⟨149388, by rfl⟩ : syracuseStep 398369 = 298777) B298777
theorem B267299 : Blo 263822 267299 := bstep (se 1 (by rfl) ⟨200474, by rfl⟩ : syracuseStep 267299 = 400949) B400949
theorem B398387 : Blo 263822 398387 := bstep (se 1 (by rfl) ⟨298790, by rfl⟩ : syracuseStep 398387 = 597581) B597581
theorem B267315 : Blo 263822 267315 := bstep (se 1 (by rfl) ⟨200486, by rfl⟩ : syracuseStep 267315 = 400973) B400973
theorem B267331 : Blo 263822 267331 := bstep (se 1 (by rfl) ⟨200498, by rfl⟩ : syracuseStep 267331 = 400997) B400997
theorem B595025 : Blo 263822 595025 := bstep (se 2 (by rfl) ⟨223134, by rfl⟩ : syracuseStep 595025 = 446269) B446269
theorem B398417 : Blo 263822 398417 := bstep (se 2 (by rfl) ⟨149406, by rfl⟩ : syracuseStep 398417 = 298813) B298813
theorem B267347 : Blo 263822 267347 := bstep (se 1 (by rfl) ⟨200510, by rfl⟩ : syracuseStep 267347 = 401021) B401021
theorem B595043 : Blo 263822 595043 := bstep (se 1 (by rfl) ⟨446282, by rfl⟩ : syracuseStep 595043 = 892565) B892565
theorem B398435 : Blo 263822 398435 := bstep (se 1 (by rfl) ⟨298826, by rfl⟩ : syracuseStep 398435 = 597653) B597653
theorem B267363 : Blo 263822 267363 := bstep (se 1 (by rfl) ⟨200522, by rfl⟩ : syracuseStep 267363 = 401045) B401045
theorem B267379 : Blo 263822 267379 := bstep (se 1 (by rfl) ⟨200534, by rfl⟩ : syracuseStep 267379 = 401069) B401069
theorem B398465 : Blo 263822 398465 := bstep (se 2 (by rfl) ⟨149424, by rfl⟩ : syracuseStep 398465 = 298849) B298849
theorem B300163 : Blo 263822 300163 := bstep (se 1 (by rfl) ⟨225122, by rfl⟩ : syracuseStep 300163 = 450245) B450245
theorem B267395 : Blo 263822 267395 := bstep (se 1 (by rfl) ⟨200546, by rfl⟩ : syracuseStep 267395 = 401093) B401093
theorem B398483 : Blo 263822 398483 := bstep (se 1 (by rfl) ⟨298862, by rfl⟩ : syracuseStep 398483 = 597725) B597725
theorem B267411 : Blo 263822 267411 := bstep (se 1 (by rfl) ⟨200558, by rfl⟩ : syracuseStep 267411 = 401117) B401117
theorem B267427 : Blo 263822 267427 := bstep (se 1 (by rfl) ⟨200570, by rfl⟩ : syracuseStep 267427 = 401141) B401141
theorem B398513 : Blo 263822 398513 := bstep (se 2 (by rfl) ⟨149442, by rfl⟩ : syracuseStep 398513 = 298885) B298885
theorem B267443 : Blo 263822 267443 := bstep (se 1 (by rfl) ⟨200582, by rfl⟩ : syracuseStep 267443 = 401165) B401165
theorem B398531 : Blo 263822 398531 := bstep (se 1 (by rfl) ⟨298898, by rfl⟩ : syracuseStep 398531 = 597797) B597797
theorem B267459 : Blo 263822 267459 := bstep (se 1 (by rfl) ⟨200594, by rfl⟩ : syracuseStep 267459 = 401189) B401189
theorem B1021133 : Blo 263822 1021133 := bstep (se 3 (by rfl) ⟨191462, by rfl⟩ : syracuseStep 1021133 = 382925) B382925
theorem B267475 : Blo 263822 267475 := bstep (se 1 (by rfl) ⟨200606, by rfl⟩ : syracuseStep 267475 = 401213) B401213
theorem B398561 : Blo 263822 398561 := bstep (se 2 (by rfl) ⟨149460, by rfl⟩ : syracuseStep 398561 = 298921) B298921
theorem B267491 : Blo 263822 267491 := bstep (se 1 (by rfl) ⟨200618, by rfl⟩ : syracuseStep 267491 = 401237) B401237
theorem B398579 : Blo 263822 398579 := bstep (se 1 (by rfl) ⟨298934, by rfl⟩ : syracuseStep 398579 = 597869) B597869
theorem B267507 : Blo 263822 267507 := bstep (se 1 (by rfl) ⟨200630, by rfl⟩ : syracuseStep 267507 = 401261) B401261
theorem B267523 : Blo 263822 267523 := bstep (se 1 (by rfl) ⟨200642, by rfl⟩ : syracuseStep 267523 = 401285) B401285
theorem B398609 : Blo 263822 398609 := bstep (se 2 (by rfl) ⟨149478, by rfl⟩ : syracuseStep 398609 = 298957) B298957
theorem B300307 : Blo 263822 300307 := bstep (se 1 (by rfl) ⟨225230, by rfl⟩ : syracuseStep 300307 = 450461) B450461
theorem B267539 : Blo 263822 267539 := bstep (se 1 (by rfl) ⟨200654, by rfl⟩ : syracuseStep 267539 = 401309) B401309
theorem B398627 : Blo 263822 398627 := bstep (se 1 (by rfl) ⟨298970, by rfl⟩ : syracuseStep 398627 = 597941) B597941
theorem B267555 : Blo 263822 267555 := bstep (se 1 (by rfl) ⟨200666, by rfl⟩ : syracuseStep 267555 = 401333) B401333
theorem B267571 : Blo 263822 267571 := bstep (se 1 (by rfl) ⟨200678, by rfl⟩ : syracuseStep 267571 = 401357) B401357
theorem B398657 : Blo 263822 398657 := bstep (se 2 (by rfl) ⟨149496, by rfl⟩ : syracuseStep 398657 = 298993) B298993
theorem B267587 : Blo 263822 267587 := bstep (se 1 (by rfl) ⟨200690, by rfl⟩ : syracuseStep 267587 = 401381) B401381
theorem B398675 : Blo 263822 398675 := bstep (se 1 (by rfl) ⟨299006, by rfl⟩ : syracuseStep 398675 = 598013) B598013
theorem B267603 : Blo 263822 267603 := bstep (se 1 (by rfl) ⟨200702, by rfl⟩ : syracuseStep 267603 = 401405) B401405
theorem B267619 : Blo 263822 267619 := bstep (se 1 (by rfl) ⟨200714, by rfl⟩ : syracuseStep 267619 = 401429) B401429
theorem B595313 : Blo 263822 595313 := bstep (se 2 (by rfl) ⟨223242, by rfl⟩ : syracuseStep 595313 = 446485) B446485
theorem B398705 : Blo 263822 398705 := bstep (se 2 (by rfl) ⟨149514, by rfl⟩ : syracuseStep 398705 = 299029) B299029
theorem B267635 : Blo 263822 267635 := bstep (se 1 (by rfl) ⟨200726, by rfl⟩ : syracuseStep 267635 = 401453) B401453
theorem B595331 : Blo 263822 595331 := bstep (se 1 (by rfl) ⟨446498, by rfl⟩ : syracuseStep 595331 = 892997) B892997
theorem B398723 : Blo 263822 398723 := bstep (se 1 (by rfl) ⟨299042, by rfl⟩ : syracuseStep 398723 = 598085) B598085
theorem B267651 : Blo 263822 267651 := bstep (se 1 (by rfl) ⟨200738, by rfl⟩ : syracuseStep 267651 = 401477) B401477
theorem B267667 : Blo 263822 267667 := bstep (se 1 (by rfl) ⟨200750, by rfl⟩ : syracuseStep 267667 = 401501) B401501
theorem B398753 : Blo 263822 398753 := bstep (se 2 (by rfl) ⟨149532, by rfl⟩ : syracuseStep 398753 = 299065) B299065
theorem B300451 : Blo 263822 300451 := bstep (se 1 (by rfl) ⟨225338, by rfl⟩ : syracuseStep 300451 = 450677) B450677
theorem B267683 : Blo 263822 267683 := bstep (se 1 (by rfl) ⟨200762, by rfl⟩ : syracuseStep 267683 = 401525) B401525
theorem B398771 : Blo 263822 398771 := bstep (se 1 (by rfl) ⟨299078, by rfl⟩ : syracuseStep 398771 = 598157) B598157
theorem B267699 : Blo 263822 267699 := bstep (se 1 (by rfl) ⟨200774, by rfl⟩ : syracuseStep 267699 = 401549) B401549
theorem B267715 : Blo 263822 267715 := bstep (se 1 (by rfl) ⟨200786, by rfl⟩ : syracuseStep 267715 = 401573) B401573
theorem B398801 : Blo 263822 398801 := bstep (se 2 (by rfl) ⟨149550, by rfl⟩ : syracuseStep 398801 = 299101) B299101
theorem B267731 : Blo 263822 267731 := bstep (se 1 (by rfl) ⟨200798, by rfl⟩ : syracuseStep 267731 = 401597) B401597
theorem B398819 : Blo 263822 398819 := bstep (se 1 (by rfl) ⟨299114, by rfl⟩ : syracuseStep 398819 = 598229) B598229
theorem B267747 : Blo 263822 267747 := bstep (se 1 (by rfl) ⟨200810, by rfl⟩ : syracuseStep 267747 = 401621) B401621
theorem B267763 : Blo 263822 267763 := bstep (se 1 (by rfl) ⟨200822, by rfl⟩ : syracuseStep 267763 = 401645) B401645
theorem B398849 : Blo 263822 398849 := bstep (se 2 (by rfl) ⟨149568, by rfl⟩ : syracuseStep 398849 = 299137) B299137
theorem B267779 : Blo 263822 267779 := bstep (se 1 (by rfl) ⟨200834, by rfl⟩ : syracuseStep 267779 = 401669) B401669
theorem B398867 : Blo 263822 398867 := bstep (se 1 (by rfl) ⟨299150, by rfl⟩ : syracuseStep 398867 = 598301) B598301
theorem B267795 : Blo 263822 267795 := bstep (se 1 (by rfl) ⟨200846, by rfl⟩ : syracuseStep 267795 = 401693) B401693
theorem B267811 : Blo 263822 267811 := bstep (se 1 (by rfl) ⟨200858, by rfl⟩ : syracuseStep 267811 = 401717) B401717
theorem B398897 : Blo 263822 398897 := bstep (se 2 (by rfl) ⟨149586, by rfl⟩ : syracuseStep 398897 = 299173) B299173
theorem B300595 : Blo 263822 300595 := bstep (se 1 (by rfl) ⟨225446, by rfl⟩ : syracuseStep 300595 = 450893) B450893
theorem B398915 : Blo 263822 398915 := bstep (se 1 (by rfl) ⟨299186, by rfl⟩ : syracuseStep 398915 = 598373) B598373
theorem B398945 : Blo 263822 398945 := bstep (se 2 (by rfl) ⟨149604, by rfl⟩ : syracuseStep 398945 = 299209) B299209
theorem B857699 : Blo 263822 857699 := bstep (se 1 (by rfl) ⟨643274, by rfl⟩ : syracuseStep 857699 = 1286549) B1286549
theorem B398963 : Blo 263822 398963 := bstep (se 1 (by rfl) ⟨299222, by rfl⟩ : syracuseStep 398963 = 598445) B598445
theorem B890513 : Blo 263822 890513 := bstep (se 2 (by rfl) ⟨333942, by rfl⟩ : syracuseStep 890513 = 667885) B667885
theorem B595601 : Blo 263822 595601 := bstep (se 2 (by rfl) ⟨223350, by rfl⟩ : syracuseStep 595601 = 446701) B446701
theorem B398993 : Blo 263822 398993 := bstep (se 2 (by rfl) ⟨149622, by rfl⟩ : syracuseStep 398993 = 299245) B299245
theorem B595619 : Blo 263822 595619 := bstep (se 1 (by rfl) ⟨446714, by rfl⟩ : syracuseStep 595619 = 893429) B893429
theorem B399011 : Blo 263822 399011 := bstep (se 1 (by rfl) ⟨299258, by rfl⟩ : syracuseStep 399011 = 598517) B598517
theorem B1349297 : Blo 263822 1349297 := bstep (se 2 (by rfl) ⟨505986, by rfl⟩ : syracuseStep 1349297 = 1011973) B1011973
theorem B399041 : Blo 263822 399041 := bstep (se 2 (by rfl) ⟨149640, by rfl⟩ : syracuseStep 399041 = 299281) B299281
theorem B300739 : Blo 263822 300739 := bstep (se 1 (by rfl) ⟨225554, by rfl⟩ : syracuseStep 300739 = 451109) B451109
theorem B399059 : Blo 263822 399059 := bstep (se 1 (by rfl) ⟨299294, by rfl⟩ : syracuseStep 399059 = 598589) B598589
theorem B431843 : Blo 263822 431843 := bstep (se 1 (by rfl) ⟨323882, by rfl⟩ : syracuseStep 431843 = 647765) B647765
theorem B399089 : Blo 263822 399089 := bstep (se 2 (by rfl) ⟨149658, by rfl⟩ : syracuseStep 399089 = 299317) B299317
theorem B399107 : Blo 263822 399107 := bstep (se 1 (by rfl) ⟨299330, by rfl⟩ : syracuseStep 399107 = 598661) B598661
theorem B2004749 : Blo 263822 2004749 := bstep (se 3 (by rfl) ⟨375890, by rfl⟩ : syracuseStep 2004749 = 751781) B751781
theorem B399137 : Blo 263822 399137 := bstep (se 2 (by rfl) ⟨149676, by rfl⟩ : syracuseStep 399137 = 299353) B299353
theorem B399155 : Blo 263822 399155 := bstep (se 1 (by rfl) ⟨299366, by rfl⟩ : syracuseStep 399155 = 598733) B598733
theorem B399185 : Blo 263822 399185 := bstep (se 2 (by rfl) ⟨149694, by rfl⟩ : syracuseStep 399185 = 299389) B299389
theorem B300883 : Blo 263822 300883 := bstep (se 1 (by rfl) ⟨225662, by rfl⟩ : syracuseStep 300883 = 451325) B451325
theorem B399203 : Blo 263822 399203 := bstep (se 1 (by rfl) ⟨299402, by rfl⟩ : syracuseStep 399203 = 598805) B598805
theorem B399233 : Blo 263822 399233 := bstep (se 2 (by rfl) ⟨149712, by rfl⟩ : syracuseStep 399233 = 299425) B299425
theorem B399251 : Blo 263822 399251 := bstep (se 1 (by rfl) ⟨299438, by rfl⟩ : syracuseStep 399251 = 598877) B598877
theorem B595889 : Blo 263822 595889 := bstep (se 2 (by rfl) ⟨223458, by rfl⟩ : syracuseStep 595889 = 446917) B446917
theorem B399281 : Blo 263822 399281 := bstep (se 2 (by rfl) ⟨149730, by rfl⟩ : syracuseStep 399281 = 299461) B299461
theorem B595907 : Blo 263822 595907 := bstep (se 1 (by rfl) ⟨446930, by rfl⟩ : syracuseStep 595907 = 893861) B893861
theorem B399299 : Blo 263822 399299 := bstep (se 1 (by rfl) ⟨299474, by rfl⟩ : syracuseStep 399299 = 598949) B598949
theorem B399329 : Blo 263822 399329 := bstep (se 2 (by rfl) ⟨149748, by rfl⟩ : syracuseStep 399329 = 299497) B299497
theorem B301027 : Blo 263822 301027 := bstep (se 1 (by rfl) ⟨225770, by rfl⟩ : syracuseStep 301027 = 451541) B451541
theorem B399347 : Blo 263822 399347 := bstep (se 1 (by rfl) ⟨299510, by rfl⟩ : syracuseStep 399347 = 599021) B599021
theorem B399377 : Blo 263822 399377 := bstep (se 2 (by rfl) ⟨149766, by rfl⟩ : syracuseStep 399377 = 299533) B299533
theorem B399395 : Blo 263822 399395 := bstep (se 1 (by rfl) ⟨299546, by rfl⟩ : syracuseStep 399395 = 599093) B599093
theorem B399425 : Blo 263822 399425 := bstep (se 2 (by rfl) ⟨149784, by rfl⟩ : syracuseStep 399425 = 299569) B299569
theorem B399443 : Blo 263822 399443 := bstep (se 1 (by rfl) ⟨299582, by rfl⟩ : syracuseStep 399443 = 599165) B599165
theorem B399473 : Blo 263822 399473 := bstep (se 2 (by rfl) ⟨149802, by rfl⟩ : syracuseStep 399473 = 299605) B299605
theorem B301171 : Blo 263822 301171 := bstep (se 1 (by rfl) ⟨225878, by rfl⟩ : syracuseStep 301171 = 451757) B451757
theorem B399491 : Blo 263822 399491 := bstep (se 1 (by rfl) ⟨299618, by rfl⟩ : syracuseStep 399491 = 599237) B599237
theorem B399521 : Blo 263822 399521 := bstep (se 2 (by rfl) ⟨149820, by rfl⟩ : syracuseStep 399521 = 299641) B299641
theorem B891053 : Blo 263822 891053 := bstep (se 3 (by rfl) ⟨167072, by rfl⟩ : syracuseStep 891053 = 334145) B334145
theorem B399539 : Blo 263822 399539 := bstep (se 1 (by rfl) ⟨299654, by rfl⟩ : syracuseStep 399539 = 599309) B599309
theorem B596177 : Blo 263822 596177 := bstep (se 2 (by rfl) ⟨223566, by rfl⟩ : syracuseStep 596177 = 447133) B447133
theorem B399569 : Blo 263822 399569 := bstep (se 2 (by rfl) ⟨149838, by rfl⟩ : syracuseStep 399569 = 299677) B299677
theorem B891107 : Blo 263822 891107 := bstep (se 1 (by rfl) ⟨668330, by rfl⟩ : syracuseStep 891107 = 1336661) B1336661
theorem B596195 : Blo 263822 596195 := bstep (se 1 (by rfl) ⟨447146, by rfl⟩ : syracuseStep 596195 = 894293) B894293
theorem B399587 : Blo 263822 399587 := bstep (se 1 (by rfl) ⟨299690, by rfl⟩ : syracuseStep 399587 = 599381) B599381
theorem B399617 : Blo 263822 399617 := bstep (se 2 (by rfl) ⟨149856, by rfl⟩ : syracuseStep 399617 = 299713) B299713
theorem B399635 : Blo 263822 399635 := bstep (se 1 (by rfl) ⟨299726, by rfl⟩ : syracuseStep 399635 = 599453) B599453
theorem B1710371 : Blo 263822 1710371 := bstep (se 1 (by rfl) ⟨1282778, by rfl⟩ : syracuseStep 1710371 = 2565557) B2565557
theorem B399665 : Blo 263822 399665 := bstep (se 2 (by rfl) ⟨149874, by rfl⟩ : syracuseStep 399665 = 299749) B299749
theorem B399683 : Blo 263822 399683 := bstep (se 1 (by rfl) ⟨299762, by rfl⟩ : syracuseStep 399683 = 599525) B599525
theorem B432467 : Blo 263822 432467 := bstep (se 1 (by rfl) ⟨324350, by rfl⟩ : syracuseStep 432467 = 648701) B648701
theorem B399713 : Blo 263822 399713 := bstep (se 2 (by rfl) ⟨149892, by rfl⟩ : syracuseStep 399713 = 299785) B299785
theorem B399731 : Blo 263822 399731 := bstep (se 1 (by rfl) ⟨299798, by rfl⟩ : syracuseStep 399731 = 599597) B599597
theorem B399761 : Blo 263822 399761 := bstep (se 2 (by rfl) ⟨149910, by rfl⟩ : syracuseStep 399761 = 299821) B299821
theorem B399779 : Blo 263822 399779 := bstep (se 1 (by rfl) ⟨299834, by rfl⟩ : syracuseStep 399779 = 599669) B599669
theorem B399809 : Blo 263822 399809 := bstep (se 2 (by rfl) ⟨149928, by rfl⟩ : syracuseStep 399809 = 299857) B299857
theorem B1612229 : Blo 263822 1612229 := bstep (se 4 (by rfl) ⟨151146, by rfl⟩ : syracuseStep 1612229 = 302293) B302293
theorem B399827 : Blo 263822 399827 := bstep (se 1 (by rfl) ⟨299870, by rfl⟩ : syracuseStep 399827 = 599741) B599741
theorem B334307 : Blo 263822 334307 := bstep (se 1 (by rfl) ⟨250730, by rfl⟩ : syracuseStep 334307 = 501461) B501461
theorem B891377 : Blo 263822 891377 := bstep (se 2 (by rfl) ⟨334266, by rfl⟩ : syracuseStep 891377 = 668533) B668533
theorem B596465 : Blo 263822 596465 := bstep (se 2 (by rfl) ⟨223674, by rfl⟩ : syracuseStep 596465 = 447349) B447349
theorem B399857 : Blo 263822 399857 := bstep (se 2 (by rfl) ⟨149946, by rfl⟩ : syracuseStep 399857 = 299893) B299893
theorem B596483 : Blo 263822 596483 := bstep (se 1 (by rfl) ⟨447362, by rfl⟩ : syracuseStep 596483 = 894725) B894725
theorem B399875 : Blo 263822 399875 := bstep (se 1 (by rfl) ⟨299906, by rfl⟩ : syracuseStep 399875 = 599813) B599813
theorem B1513997 : Blo 263822 1513997 := bstep (se 3 (by rfl) ⟨283874, by rfl⟩ : syracuseStep 1513997 = 567749) B567749
theorem B760337 : Blo 263822 760337 := bstep (se 2 (by rfl) ⟨285126, by rfl⟩ : syracuseStep 760337 = 570253) B570253
theorem B399905 : Blo 263822 399905 := bstep (se 2 (by rfl) ⟨149964, by rfl⟩ : syracuseStep 399905 = 299929) B299929
theorem B399923 : Blo 263822 399923 := bstep (se 1 (by rfl) ⟨299942, by rfl⟩ : syracuseStep 399923 = 599885) B599885
theorem B399953 : Blo 263822 399953 := bstep (se 2 (by rfl) ⟨149982, by rfl⟩ : syracuseStep 399953 = 299965) B299965
theorem B399971 : Blo 263822 399971 := bstep (se 1 (by rfl) ⟨299978, by rfl⟩ : syracuseStep 399971 = 599957) B599957
theorem B957041 : Blo 263822 957041 := bstep (se 2 (by rfl) ⟨358890, by rfl⟩ : syracuseStep 957041 = 717781) B717781
theorem B400001 : Blo 263822 400001 := bstep (se 2 (by rfl) ⟨150000, by rfl⟩ : syracuseStep 400001 = 300001) B300001
theorem B400019 : Blo 263822 400019 := bstep (se 1 (by rfl) ⟨300014, by rfl⟩ : syracuseStep 400019 = 600029) B600029
theorem B400049 : Blo 263822 400049 := bstep (se 2 (by rfl) ⟨150018, by rfl⟩ : syracuseStep 400049 = 300037) B300037
theorem B301747 : Blo 263822 301747 := bstep (se 1 (by rfl) ⟨226310, by rfl⟩ : syracuseStep 301747 = 452621) B452621
theorem B400067 : Blo 263822 400067 := bstep (se 1 (by rfl) ⟨300050, by rfl⟩ : syracuseStep 400067 = 600101) B600101
theorem B760529 : Blo 263822 760529 := bstep (se 2 (by rfl) ⟨285198, by rfl⟩ : syracuseStep 760529 = 570397) B570397
theorem B400097 : Blo 263822 400097 := bstep (se 2 (by rfl) ⟨150036, by rfl⟩ : syracuseStep 400097 = 300073) B300073
theorem B563939 : Blo 263822 563939 := bstep (se 1 (by rfl) ⟨422954, by rfl⟩ : syracuseStep 563939 = 845909) B845909
theorem B400115 : Blo 263822 400115 := bstep (se 1 (by rfl) ⟨300086, by rfl⟩ : syracuseStep 400115 = 600173) B600173
theorem B3414797 : Blo 263822 3414797 := bstep (se 3 (by rfl) ⟨640274, by rfl⟩ : syracuseStep 3414797 = 1280549) B1280549
theorem B596753 : Blo 263822 596753 := bstep (se 2 (by rfl) ⟨223782, by rfl⟩ : syracuseStep 596753 = 447565) B447565
theorem B400145 : Blo 263822 400145 := bstep (se 2 (by rfl) ⟨150054, by rfl⟩ : syracuseStep 400145 = 300109) B300109
theorem B596771 : Blo 263822 596771 := bstep (se 1 (by rfl) ⟨447578, by rfl⟩ : syracuseStep 596771 = 895157) B895157
theorem B400163 : Blo 263822 400163 := bstep (se 1 (by rfl) ⟨300122, by rfl⟩ : syracuseStep 400163 = 600245) B600245
theorem B400193 : Blo 263822 400193 := bstep (se 2 (by rfl) ⟨150072, by rfl⟩ : syracuseStep 400193 = 300145) B300145
theorem B269123 : Blo 263822 269123 := bstep (se 1 (by rfl) ⟨201842, by rfl⟩ : syracuseStep 269123 = 403685) B403685
theorem B400211 : Blo 263822 400211 := bstep (se 1 (by rfl) ⟨300158, by rfl⟩ : syracuseStep 400211 = 600317) B600317
theorem B400241 : Blo 263822 400241 := bstep (se 2 (by rfl) ⟨150090, by rfl⟩ : syracuseStep 400241 = 300181) B300181
theorem B400259 : Blo 263822 400259 := bstep (se 1 (by rfl) ⟨300194, by rfl⟩ : syracuseStep 400259 = 600389) B600389
theorem B400289 : Blo 263822 400289 := bstep (se 2 (by rfl) ⟨150108, by rfl⟩ : syracuseStep 400289 = 300217) B300217
theorem B400307 : Blo 263822 400307 := bstep (se 1 (by rfl) ⟨300230, by rfl⟩ : syracuseStep 400307 = 600461) B600461
theorem B400337 : Blo 263822 400337 := bstep (se 2 (by rfl) ⟨150126, by rfl⟩ : syracuseStep 400337 = 300253) B300253
theorem B400355 : Blo 263822 400355 := bstep (se 1 (by rfl) ⟨300266, by rfl⟩ : syracuseStep 400355 = 600533) B600533
theorem B400385 : Blo 263822 400385 := bstep (se 2 (by rfl) ⟨150144, by rfl⟩ : syracuseStep 400385 = 300289) B300289
theorem B891917 : Blo 263822 891917 := bstep (se 3 (by rfl) ⟨167234, by rfl⟩ : syracuseStep 891917 = 334469) B334469
theorem B400403 : Blo 263822 400403 := bstep (se 1 (by rfl) ⟨300302, by rfl⟩ : syracuseStep 400403 = 600605) B600605
theorem B597041 : Blo 263822 597041 := bstep (se 2 (by rfl) ⟨223890, by rfl⟩ : syracuseStep 597041 = 447781) B447781
theorem B400433 : Blo 263822 400433 := bstep (se 2 (by rfl) ⟨150162, by rfl⟩ : syracuseStep 400433 = 300325) B300325
theorem B891971 : Blo 263822 891971 := bstep (se 1 (by rfl) ⟨668978, by rfl⟩ : syracuseStep 891971 = 1337957) B1337957
theorem B597059 : Blo 263822 597059 := bstep (se 1 (by rfl) ⟨447794, by rfl⟩ : syracuseStep 597059 = 895589) B895589
theorem B400451 : Blo 263822 400451 := bstep (se 1 (by rfl) ⟨300338, by rfl⟩ : syracuseStep 400451 = 600677) B600677
theorem B400481 : Blo 263822 400481 := bstep (se 2 (by rfl) ⟨150180, by rfl⟩ : syracuseStep 400481 = 300361) B300361
theorem B1350755 : Blo 263822 1350755 := bstep (se 1 (by rfl) ⟨1013066, by rfl⟩ : syracuseStep 1350755 = 2026133) B2026133
theorem B400499 : Blo 263822 400499 := bstep (se 1 (by rfl) ⟨300374, by rfl⟩ : syracuseStep 400499 = 600749) B600749
theorem B400529 : Blo 263822 400529 := bstep (se 2 (by rfl) ⟨150198, by rfl⟩ : syracuseStep 400529 = 300397) B300397
theorem B335011 : Blo 263822 335011 := bstep (se 1 (by rfl) ⟨251258, by rfl⟩ : syracuseStep 335011 = 502517) B502517
theorem B400547 : Blo 263822 400547 := bstep (se 1 (by rfl) ⟨300410, by rfl⟩ : syracuseStep 400547 = 600821) B600821
theorem B564401 : Blo 263822 564401 := bstep (se 2 (by rfl) ⟨211650, by rfl⟩ : syracuseStep 564401 = 423301) B423301
theorem B400577 : Blo 263822 400577 := bstep (se 2 (by rfl) ⟨150216, by rfl⟩ : syracuseStep 400577 = 300433) B300433
theorem B400595 : Blo 263822 400595 := bstep (se 1 (by rfl) ⟨300446, by rfl⟩ : syracuseStep 400595 = 600893) B600893
theorem B400625 : Blo 263822 400625 := bstep (se 2 (by rfl) ⟨150234, by rfl⟩ : syracuseStep 400625 = 300469) B300469
theorem B335107 : Blo 263822 335107 := bstep (se 1 (by rfl) ⟨251330, by rfl⟩ : syracuseStep 335107 = 502661) B502661
theorem B400643 : Blo 263822 400643 := bstep (se 1 (by rfl) ⟨300482, by rfl⟩ : syracuseStep 400643 = 600965) B600965
theorem B400673 : Blo 263822 400673 := bstep (se 2 (by rfl) ⟨150252, by rfl⟩ : syracuseStep 400673 = 300505) B300505
theorem B400691 : Blo 263822 400691 := bstep (se 1 (by rfl) ⟨300518, by rfl⟩ : syracuseStep 400691 = 601037) B601037
theorem B892241 : Blo 263822 892241 := bstep (se 2 (by rfl) ⟨334590, by rfl⟩ : syracuseStep 892241 = 669181) B669181
theorem B597329 : Blo 263822 597329 := bstep (se 2 (by rfl) ⟨223998, by rfl⟩ : syracuseStep 597329 = 447997) B447997
theorem B400721 : Blo 263822 400721 := bstep (se 2 (by rfl) ⟨150270, by rfl⟩ : syracuseStep 400721 = 300541) B300541
theorem B597347 : Blo 263822 597347 := bstep (se 1 (by rfl) ⟨448010, by rfl⟩ : syracuseStep 597347 = 896021) B896021
theorem B400739 : Blo 263822 400739 := bstep (se 1 (by rfl) ⟨300554, by rfl⟩ : syracuseStep 400739 = 601109) B601109
theorem B400769 : Blo 263822 400769 := bstep (se 2 (by rfl) ⟨150288, by rfl⟩ : syracuseStep 400769 = 300577) B300577
theorem B400787 : Blo 263822 400787 := bstep (se 1 (by rfl) ⟨300590, by rfl⟩ : syracuseStep 400787 = 601181) B601181
theorem B400817 : Blo 263822 400817 := bstep (se 2 (by rfl) ⟨150306, by rfl⟩ : syracuseStep 400817 = 300613) B300613
theorem B400835 : Blo 263822 400835 := bstep (se 1 (by rfl) ⟨300626, by rfl⟩ : syracuseStep 400835 = 601253) B601253
theorem B400865 : Blo 263822 400865 := bstep (se 2 (by rfl) ⟨150324, by rfl⟩ : syracuseStep 400865 = 300649) B300649
theorem B1711601 : Blo 263822 1711601 := bstep (se 2 (by rfl) ⟨641850, by rfl⟩ : syracuseStep 1711601 = 1283701) B1283701
theorem B400883 : Blo 263822 400883 := bstep (se 1 (by rfl) ⟨300662, by rfl⟩ : syracuseStep 400883 = 601325) B601325
theorem B400913 : Blo 263822 400913 := bstep (se 2 (by rfl) ⟨150342, by rfl⟩ : syracuseStep 400913 = 300685) B300685
theorem B400931 : Blo 263822 400931 := bstep (se 1 (by rfl) ⟨300698, by rfl⟩ : syracuseStep 400931 = 601397) B601397
theorem B400961 : Blo 263822 400961 := bstep (se 2 (by rfl) ⟨150360, by rfl⟩ : syracuseStep 400961 = 300721) B300721
theorem B400979 : Blo 263822 400979 := bstep (se 1 (by rfl) ⟨300734, by rfl⟩ : syracuseStep 400979 = 601469) B601469
theorem B597617 : Blo 263822 597617 := bstep (se 2 (by rfl) ⟨224106, by rfl⟩ : syracuseStep 597617 = 448213) B448213
theorem B401009 : Blo 263822 401009 := bstep (se 2 (by rfl) ⟨150378, by rfl⟩ : syracuseStep 401009 = 300757) B300757
theorem B597635 : Blo 263822 597635 := bstep (se 1 (by rfl) ⟨448226, by rfl⟩ : syracuseStep 597635 = 896453) B896453
theorem B401027 : Blo 263822 401027 := bstep (se 1 (by rfl) ⟨300770, by rfl⟩ : syracuseStep 401027 = 601541) B601541
theorem B401057 : Blo 263822 401057 := bstep (se 2 (by rfl) ⟨150396, by rfl⟩ : syracuseStep 401057 = 300793) B300793
theorem B761521 : Blo 263822 761521 := bstep (se 2 (by rfl) ⟨285570, by rfl⟩ : syracuseStep 761521 = 571141) B571141
theorem B401075 : Blo 263822 401075 := bstep (se 1 (by rfl) ⟨300806, by rfl⟩ : syracuseStep 401075 = 601613) B601613
theorem B401105 : Blo 263822 401105 := bstep (se 2 (by rfl) ⟨150414, by rfl⟩ : syracuseStep 401105 = 300829) B300829
theorem B7282403 : Blo 263822 7282403 := bstep (se 1 (by rfl) ⟨5461802, by rfl⟩ : syracuseStep 7282403 = 10923605) B10923605
theorem B401123 : Blo 263822 401123 := bstep (se 1 (by rfl) ⟨300842, by rfl⟩ : syracuseStep 401123 = 601685) B601685
theorem B335603 : Blo 263822 335603 := bstep (se 1 (by rfl) ⟨251702, by rfl⟩ : syracuseStep 335603 = 503405) B503405
theorem B401153 : Blo 263822 401153 := bstep (se 2 (by rfl) ⟨150432, by rfl⟩ : syracuseStep 401153 = 300865) B300865
theorem B401171 : Blo 263822 401171 := bstep (se 1 (by rfl) ⟨300878, by rfl⟩ : syracuseStep 401171 = 601757) B601757
theorem B401201 : Blo 263822 401201 := bstep (se 2 (by rfl) ⟨150450, by rfl⟩ : syracuseStep 401201 = 300901) B300901
theorem B401219 : Blo 263822 401219 := bstep (se 1 (by rfl) ⟨300914, by rfl⟩ : syracuseStep 401219 = 601829) B601829
theorem B401249 : Blo 263822 401249 := bstep (se 2 (by rfl) ⟨150468, by rfl⟩ : syracuseStep 401249 = 300937) B300937
theorem B892781 : Blo 263822 892781 := bstep (se 3 (by rfl) ⟨167396, by rfl⟩ : syracuseStep 892781 = 334793) B334793
theorem B401267 : Blo 263822 401267 := bstep (se 1 (by rfl) ⟨300950, by rfl⟩ : syracuseStep 401267 = 601901) B601901
theorem B1351565 : Blo 263822 1351565 := bstep (se 3 (by rfl) ⟨253418, by rfl⟩ : syracuseStep 1351565 = 506837) B506837
theorem B597905 : Blo 263822 597905 := bstep (se 2 (by rfl) ⟨224214, by rfl⟩ : syracuseStep 597905 = 448429) B448429
theorem B401297 : Blo 263822 401297 := bstep (se 2 (by rfl) ⟨150486, by rfl⟩ : syracuseStep 401297 = 300973) B300973
theorem B892835 : Blo 263822 892835 := bstep (se 1 (by rfl) ⟨669626, by rfl⟩ : syracuseStep 892835 = 1339253) B1339253
theorem B597923 : Blo 263822 597923 := bstep (se 1 (by rfl) ⟨448442, by rfl⟩ : syracuseStep 597923 = 896885) B896885
theorem B401315 : Blo 263822 401315 := bstep (se 1 (by rfl) ⟨300986, by rfl⟩ : syracuseStep 401315 = 601973) B601973
theorem B434099 : Blo 263822 434099 := bstep (se 1 (by rfl) ⟨325574, by rfl⟩ : syracuseStep 434099 = 651149) B651149
theorem B401345 : Blo 263822 401345 := bstep (se 2 (by rfl) ⟨150504, by rfl⟩ : syracuseStep 401345 = 301009) B301009
theorem B761795 : Blo 263822 761795 := bstep (se 1 (by rfl) ⟨571346, by rfl⟩ : syracuseStep 761795 = 1142693) B1142693
theorem B401363 : Blo 263822 401363 := bstep (se 1 (by rfl) ⟨301022, by rfl⟩ : syracuseStep 401363 = 602045) B602045
theorem B401393 : Blo 263822 401393 := bstep (se 2 (by rfl) ⟨150522, by rfl⟩ : syracuseStep 401393 = 301045) B301045
theorem B401411 : Blo 263822 401411 := bstep (se 1 (by rfl) ⟨301058, by rfl⟩ : syracuseStep 401411 = 602117) B602117
theorem B401441 : Blo 263822 401441 := bstep (se 2 (by rfl) ⟨150540, by rfl⟩ : syracuseStep 401441 = 301081) B301081
theorem B401459 : Blo 263822 401459 := bstep (se 1 (by rfl) ⟨301094, by rfl⟩ : syracuseStep 401459 = 602189) B602189
theorem B401489 : Blo 263822 401489 := bstep (se 2 (by rfl) ⟨150558, by rfl⟩ : syracuseStep 401489 = 301117) B301117
theorem B401507 : Blo 263822 401507 := bstep (se 1 (by rfl) ⟨301130, by rfl⟩ : syracuseStep 401507 = 602261) B602261
theorem B401537 : Blo 263822 401537 := bstep (se 2 (by rfl) ⟨150576, by rfl⟩ : syracuseStep 401537 = 301153) B301153
theorem B761987 : Blo 263822 761987 := bstep (se 1 (by rfl) ⟨571490, by rfl⟩ : syracuseStep 761987 = 1142981) B1142981
theorem B401555 : Blo 263822 401555 := bstep (se 1 (by rfl) ⟨301166, by rfl⟩ : syracuseStep 401555 = 602333) B602333
theorem B893105 : Blo 263822 893105 := bstep (se 2 (by rfl) ⟨334914, by rfl⟩ : syracuseStep 893105 = 669829) B669829
theorem B598193 : Blo 263822 598193 := bstep (se 2 (by rfl) ⟨224322, by rfl⟩ : syracuseStep 598193 = 448645) B448645
theorem B401585 : Blo 263822 401585 := bstep (se 2 (by rfl) ⟨150594, by rfl⟩ : syracuseStep 401585 = 301189) B301189
theorem B598211 : Blo 263822 598211 := bstep (se 1 (by rfl) ⟨448658, by rfl⟩ : syracuseStep 598211 = 897317) B897317
theorem B401603 : Blo 263822 401603 := bstep (se 1 (by rfl) ⟨301202, by rfl⟩ : syracuseStep 401603 = 602405) B602405
theorem B401633 : Blo 263822 401633 := bstep (se 2 (by rfl) ⟨150612, by rfl⟩ : syracuseStep 401633 = 301225) B301225
theorem B401651 : Blo 263822 401651 := bstep (se 1 (by rfl) ⟨301238, by rfl⟩ : syracuseStep 401651 = 602477) B602477
theorem B401681 : Blo 263822 401681 := bstep (se 2 (by rfl) ⟨150630, by rfl⟩ : syracuseStep 401681 = 301261) B301261
theorem B401699 : Blo 263822 401699 := bstep (se 1 (by rfl) ⟨301274, by rfl⟩ : syracuseStep 401699 = 602549) B602549
theorem B3449141 : Blo 263822 3449141 := bstep (se 5 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 3449141 = 323357) B323357
theorem B401729 : Blo 263822 401729 := bstep (se 2 (by rfl) ⟨150648, by rfl⟩ : syracuseStep 401729 = 301297) B301297
theorem B336307 : Blo 263822 336307 := bstep (se 1 (by rfl) ⟨252230, by rfl⟩ : syracuseStep 336307 = 504461) B504461
theorem B565699 : Blo 263822 565699 := bstep (se 1 (by rfl) ⟨424274, by rfl⟩ : syracuseStep 565699 = 848549) B848549
theorem B598481 : Blo 263822 598481 := bstep (se 2 (by rfl) ⟨224430, by rfl⟩ : syracuseStep 598481 = 448861) B448861
theorem B598499 : Blo 263822 598499 := bstep (se 1 (by rfl) ⟨448874, by rfl⟩ : syracuseStep 598499 = 897749) B897749
theorem B336403 : Blo 263822 336403 := bstep (se 1 (by rfl) ⟨252302, by rfl⟩ : syracuseStep 336403 = 504605) B504605
theorem B2007665 : Blo 263822 2007665 := bstep (se 2 (by rfl) ⟨752874, by rfl⟩ : syracuseStep 2007665 = 1505749) B1505749
theorem B565955 : Blo 263822 565955 := bstep (se 1 (by rfl) ⟨424466, by rfl⟩ : syracuseStep 565955 = 848933) B848933
theorem B1516229 : Blo 263822 1516229 := bstep (se 4 (by rfl) ⟨142146, by rfl⟩ : syracuseStep 1516229 = 284293) B284293
theorem B893645 : Blo 263822 893645 := bstep (se 3 (by rfl) ⟨167558, by rfl⟩ : syracuseStep 893645 = 335117) B335117
theorem B598769 : Blo 263822 598769 := bstep (se 2 (by rfl) ⟨224538, by rfl⟩ : syracuseStep 598769 = 449077) B449077
theorem B893699 : Blo 263822 893699 := bstep (se 1 (by rfl) ⟨670274, by rfl⟩ : syracuseStep 893699 = 1340549) B1340549
theorem B598787 : Blo 263822 598787 := bstep (se 1 (by rfl) ⟨449090, by rfl⟩ : syracuseStep 598787 = 898181) B898181
theorem B402403 : Blo 263822 402403 := bstep (se 1 (by rfl) ⟨301802, by rfl⟩ : syracuseStep 402403 = 603605) B603605
theorem B336899 : Blo 263822 336899 := bstep (se 1 (by rfl) ⟨252674, by rfl⟩ : syracuseStep 336899 = 505349) B505349
theorem B893969 : Blo 263822 893969 := bstep (se 2 (by rfl) ⟨335238, by rfl⟩ : syracuseStep 893969 = 670477) B670477
theorem B599057 : Blo 263822 599057 := bstep (se 2 (by rfl) ⟨224646, by rfl⟩ : syracuseStep 599057 = 449293) B449293
theorem B599075 : Blo 263822 599075 := bstep (se 1 (by rfl) ⟨449306, by rfl⟩ : syracuseStep 599075 = 898613) B898613
theorem B271459 : Blo 263822 271459 := bstep (se 1 (by rfl) ⟨203594, by rfl⟩ : syracuseStep 271459 = 407189) B407189
theorem B500899 : Blo 263822 500899 := bstep (se 1 (by rfl) ⟨375674, by rfl⟩ : syracuseStep 500899 = 751349) B751349
theorem B599345 : Blo 263822 599345 := bstep (se 2 (by rfl) ⟨224754, by rfl⟩ : syracuseStep 599345 = 449509) B449509
theorem B501059 : Blo 263822 501059 := bstep (se 1 (by rfl) ⟨375794, by rfl⟩ : syracuseStep 501059 = 751589) B751589
theorem B599363 : Blo 263822 599363 := bstep (se 1 (by rfl) ⟨449522, by rfl⟩ : syracuseStep 599363 = 899045) B899045
theorem B2434373 : Blo 263822 2434373 := bstep (se 4 (by rfl) ⟨228222, by rfl⟩ : syracuseStep 2434373 = 456445) B456445
theorem B1516913 : Blo 263822 1516913 := bstep (se 2 (by rfl) ⟨568842, by rfl⟩ : syracuseStep 1516913 = 1137685) B1137685
theorem B402961 : Blo 263822 402961 := bstep (se 2 (by rfl) ⟨151110, by rfl⟩ : syracuseStep 402961 = 302221) B302221
theorem B894509 : Blo 263822 894509 := bstep (se 3 (by rfl) ⟨167720, by rfl⟩ : syracuseStep 894509 = 335441) B335441
theorem B599633 : Blo 263822 599633 := bstep (se 2 (by rfl) ⟨224862, by rfl⟩ : syracuseStep 599633 = 449725) B449725
theorem B894563 : Blo 263822 894563 := bstep (se 1 (by rfl) ⟨670922, by rfl⟩ : syracuseStep 894563 = 1341845) B1341845
theorem B599651 : Blo 263822 599651 := bstep (se 1 (by rfl) ⟨449738, by rfl⟩ : syracuseStep 599651 = 899477) B899477
theorem B566929 : Blo 263822 566929 := bstep (se 2 (by rfl) ⟨212598, by rfl⟩ : syracuseStep 566929 = 425197) B425197
theorem B337603 : Blo 263822 337603 := bstep (se 1 (by rfl) ⟨253202, by rfl⟩ : syracuseStep 337603 = 506405) B506405
theorem B730883 : Blo 263822 730883 := bstep (se 1 (by rfl) ⟨548162, by rfl⟩ : syracuseStep 730883 = 1096325) B1096325
theorem B337699 : Blo 263822 337699 := bstep (se 1 (by rfl) ⟨253274, by rfl⟩ : syracuseStep 337699 = 506549) B506549
theorem B894833 : Blo 263822 894833 := bstep (se 2 (by rfl) ⟨335562, by rfl⟩ : syracuseStep 894833 = 671125) B671125
theorem B599921 : Blo 263822 599921 := bstep (se 2 (by rfl) ⟨224970, by rfl⟩ : syracuseStep 599921 = 449941) B449941
theorem B599939 : Blo 263822 599939 := bstep (se 1 (by rfl) ⟨449954, by rfl⟩ : syracuseStep 599939 = 899909) B899909
theorem B1714061 : Blo 263822 1714061 := bstep (se 3 (by rfl) ⟨321386, by rfl⟩ : syracuseStep 1714061 = 642773) B642773
theorem B600209 : Blo 263822 600209 := bstep (se 2 (by rfl) ⟨225078, by rfl⟩ : syracuseStep 600209 = 450157) B450157
theorem B600227 : Blo 263822 600227 := bstep (se 1 (by rfl) ⟨450170, by rfl⟩ : syracuseStep 600227 = 900341) B900341
theorem B2271473 : Blo 263822 2271473 := bstep (se 2 (by rfl) ⟨851802, by rfl⟩ : syracuseStep 2271473 = 1703605) B1703605
theorem B338195 : Blo 263822 338195 := bstep (se 1 (by rfl) ⟨253646, by rfl⟩ : syracuseStep 338195 = 507293) B507293
theorem B567587 : Blo 263822 567587 := bstep (se 1 (by rfl) ⟨425690, by rfl⟩ : syracuseStep 567587 = 851381) B851381
theorem B3909941 : Blo 263822 3909941 := bstep (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) B366557
theorem B502129 : Blo 263822 502129 := bstep (se 2 (by rfl) ⟨188298, by rfl⟩ : syracuseStep 502129 = 376597) B376597
theorem B895373 : Blo 263822 895373 := bstep (se 3 (by rfl) ⟨167882, by rfl⟩ : syracuseStep 895373 = 335765) B335765
theorem B600497 : Blo 263822 600497 := bstep (se 2 (by rfl) ⟨225186, by rfl⟩ : syracuseStep 600497 = 450373) B450373
theorem B895427 : Blo 263822 895427 := bstep (se 1 (by rfl) ⟨671570, by rfl⟩ : syracuseStep 895427 = 1343141) B1343141
theorem B600515 : Blo 263822 600515 := bstep (se 1 (by rfl) ⟨450386, by rfl⟩ : syracuseStep 600515 = 900773) B900773
theorem B3025349 : Blo 263822 3025349 := bstep (se 4 (by rfl) ⟨283626, by rfl⟩ : syracuseStep 3025349 = 567253) B567253
theorem B895697 : Blo 263822 895697 := bstep (se 2 (by rfl) ⟨335886, by rfl⟩ : syracuseStep 895697 = 671773) B671773
theorem B600785 : Blo 263822 600785 := bstep (se 2 (by rfl) ⟨225294, by rfl⟩ : syracuseStep 600785 = 450589) B450589
theorem B600803 : Blo 263822 600803 := bstep (se 1 (by rfl) ⟨450602, by rfl⟩ : syracuseStep 600803 = 901205) B901205
theorem B1354481 : Blo 263822 1354481 := bstep (se 2 (by rfl) ⟨507930, by rfl⟩ : syracuseStep 1354481 = 1015861) B1015861
theorem B1518371 : Blo 263822 1518371 := bstep (se 1 (by rfl) ⟨1138778, by rfl⟩ : syracuseStep 1518371 = 2277557) B2277557
theorem B338899 : Blo 263822 338899 := bstep (se 1 (by rfl) ⟨254174, by rfl⟩ : syracuseStep 338899 = 508349) B508349
theorem B601073 : Blo 263822 601073 := bstep (se 2 (by rfl) ⟨225402, by rfl⟩ : syracuseStep 601073 = 450805) B450805
theorem B601091 : Blo 263822 601091 := bstep (se 1 (by rfl) ⟨450818, by rfl⟩ : syracuseStep 601091 = 901637) B901637
theorem B633923 : Blo 263822 633923 := bstep (se 1 (by rfl) ⟨475442, by rfl⟩ : syracuseStep 633923 = 950885) B950885
theorem B404561 : Blo 263822 404561 := bstep (se 2 (by rfl) ⟨151710, by rfl⟩ : syracuseStep 404561 = 303421) B303421
theorem B568433 : Blo 263822 568433 := bstep (se 2 (by rfl) ⟨213162, by rfl⟩ : syracuseStep 568433 = 426325) B426325
theorem B896237 : Blo 263822 896237 := bstep (se 3 (by rfl) ⟨168044, by rfl⟩ : syracuseStep 896237 = 336089) B336089
theorem B601361 : Blo 263822 601361 := bstep (se 2 (by rfl) ⟨225510, by rfl⟩ : syracuseStep 601361 = 451021) B451021
theorem B896291 : Blo 263822 896291 := bstep (se 1 (by rfl) ⟨672218, by rfl⟩ : syracuseStep 896291 = 1344437) B1344437
theorem B601379 : Blo 263822 601379 := bstep (se 1 (by rfl) ⟨451034, by rfl⟩ : syracuseStep 601379 = 902069) B902069
theorem B503185 : Blo 263822 503185 := bstep (se 2 (by rfl) ⟨188694, by rfl⟩ : syracuseStep 503185 = 377389) B377389
theorem B961969 : Blo 263822 961969 := bstep (se 2 (by rfl) ⟨360738, by rfl⟩ : syracuseStep 961969 = 721477) B721477
theorem B536017 : Blo 263822 536017 := bstep (se 2 (by rfl) ⟨201006, by rfl⟩ : syracuseStep 536017 = 402013) B402013
theorem B634385 : Blo 263822 634385 := bstep (se 2 (by rfl) ⟨237894, by rfl⟩ : syracuseStep 634385 = 475789) B475789
theorem B896561 : Blo 263822 896561 := bstep (se 2 (by rfl) ⟨336210, by rfl⟩ : syracuseStep 896561 = 672421) B672421
theorem B601649 : Blo 263822 601649 := bstep (se 2 (by rfl) ⟨225618, by rfl⟩ : syracuseStep 601649 = 451237) B451237
theorem B601667 : Blo 263822 601667 := bstep (se 1 (by rfl) ⟨451250, by rfl⟩ : syracuseStep 601667 = 902501) B902501
theorem B1650403 : Blo 263822 1650403 := bstep (se 1 (by rfl) ⟨1237802, by rfl⟩ : syracuseStep 1650403 = 2475605) B2475605
theorem B503587 : Blo 263822 503587 := bstep (se 1 (by rfl) ⟨377690, by rfl⟩ : syracuseStep 503587 = 755381) B755381
theorem B503633 : Blo 263822 503633 := bstep (se 2 (by rfl) ⟨188862, by rfl⟩ : syracuseStep 503633 = 377725) B377725
theorem B601937 : Blo 263822 601937 := bstep (se 2 (by rfl) ⟨225726, by rfl⟩ : syracuseStep 601937 = 451453) B451453
theorem B601955 : Blo 263822 601955 := bstep (se 1 (by rfl) ⟨451466, by rfl⟩ : syracuseStep 601955 = 902933) B902933
theorem B962417 : Blo 263822 962417 := bstep (se 2 (by rfl) ⟨360906, by rfl⟩ : syracuseStep 962417 = 721813) B721813
theorem B897101 : Blo 263822 897101 := bstep (se 3 (by rfl) ⟨168206, by rfl⟩ : syracuseStep 897101 = 336413) B336413
theorem B503921 : Blo 263822 503921 := bstep (se 2 (by rfl) ⟨188970, by rfl⟩ : syracuseStep 503921 = 377941) B377941
theorem B602225 : Blo 263822 602225 := bstep (se 2 (by rfl) ⟨225834, by rfl⟩ : syracuseStep 602225 = 451669) B451669
theorem B897155 : Blo 263822 897155 := bstep (se 1 (by rfl) ⟨672866, by rfl⟩ : syracuseStep 897155 = 1345733) B1345733
theorem B602243 : Blo 263822 602243 := bstep (se 1 (by rfl) ⟨451682, by rfl⟩ : syracuseStep 602243 = 903365) B903365
theorem B1716515 : Blo 263822 1716515 := bstep (se 1 (by rfl) ⟨1287386, by rfl⟩ : syracuseStep 1716515 = 2574773) B2574773
theorem B2896181 : Blo 263822 2896181 := bstep (se 5 (by rfl) ⟨135758, by rfl⟩ : syracuseStep 2896181 = 271517) B271517
theorem B897425 : Blo 263822 897425 := bstep (se 2 (by rfl) ⟨336534, by rfl⟩ : syracuseStep 897425 = 673069) B673069
theorem B602513 : Blo 263822 602513 := bstep (se 2 (by rfl) ⟨225942, by rfl⟩ : syracuseStep 602513 = 451885) B451885
theorem B602531 : Blo 263822 602531 := bstep (se 1 (by rfl) ⟨451898, by rfl⟩ : syracuseStep 602531 = 903797) B903797
theorem B405953 : Blo 263822 405953 := bstep (se 2 (by rfl) ⟨152232, by rfl⟩ : syracuseStep 405953 = 304465) B304465
theorem B668209 : Blo 263822 668209 := bstep (se 2 (by rfl) ⟨250578, by rfl⟩ : syracuseStep 668209 = 501157) B501157
theorem B2273933 : Blo 263822 2273933 := bstep (se 3 (by rfl) ⟨426362, by rfl⟩ : syracuseStep 2273933 = 852725) B852725
theorem B668483 : Blo 263822 668483 := bstep (se 1 (by rfl) ⟨501362, by rfl⟩ : syracuseStep 668483 = 1002725) B1002725
theorem B504643 : Blo 263822 504643 := bstep (se 1 (by rfl) ⟨378482, by rfl⟩ : syracuseStep 504643 = 756965) B756965
theorem B897965 : Blo 263822 897965 := bstep (se 3 (by rfl) ⟨168368, by rfl⟩ : syracuseStep 897965 = 336737) B336737
theorem B898019 : Blo 263822 898019 := bstep (se 1 (by rfl) ⟨673514, by rfl⟩ : syracuseStep 898019 = 1347029) B1347029
theorem B668675 : Blo 263822 668675 := bstep (se 1 (by rfl) ⟨501506, by rfl⟩ : syracuseStep 668675 = 1003013) B1003013
theorem B406561 : Blo 263822 406561 := bstep (se 2 (by rfl) ⟨152460, by rfl⟩ : syracuseStep 406561 = 304921) B304921
theorem B898289 : Blo 263822 898289 := bstep (se 2 (by rfl) ⟨336858, by rfl⟩ : syracuseStep 898289 = 673717) B673717
theorem B505091 : Blo 263822 505091 := bstep (se 1 (by rfl) ⟨378818, by rfl⟩ : syracuseStep 505091 = 757637) B757637
theorem B505379 : Blo 263822 505379 := bstep (se 1 (by rfl) ⟨379034, by rfl⟩ : syracuseStep 505379 = 758069) B758069
theorem B898829 : Blo 263822 898829 := bstep (se 3 (by rfl) ⟨168530, by rfl⟩ : syracuseStep 898829 = 337061) B337061
theorem B898883 : Blo 263822 898883 := bstep (se 1 (by rfl) ⟨674162, by rfl⟩ : syracuseStep 898883 = 1348325) B1348325
theorem B571217 : Blo 263822 571217 := bstep (se 2 (by rfl) ⟨214206, by rfl⟩ : syracuseStep 571217 = 428413) B428413
theorem B669617 : Blo 263822 669617 := bstep (se 2 (by rfl) ⟨251106, by rfl⟩ : syracuseStep 669617 = 502213) B502213
theorem B1521605 : Blo 263822 1521605 := bstep (se 4 (by rfl) ⟨142650, by rfl⟩ : syracuseStep 1521605 = 285301) B285301
theorem B669667 : Blo 263822 669667 := bstep (se 1 (by rfl) ⟨502250, by rfl⟩ : syracuseStep 669667 = 1004501) B1004501
theorem B899153 : Blo 263822 899153 := bstep (se 2 (by rfl) ⟨337182, by rfl⟩ : syracuseStep 899153 = 674365) B674365
theorem B669809 : Blo 263822 669809 := bstep (se 2 (by rfl) ⟨251178, by rfl⟩ : syracuseStep 669809 = 502357) B502357
theorem B1620209 : Blo 263822 1620209 := bstep (se 2 (by rfl) ⟨607578, by rfl⟩ : syracuseStep 1620209 = 1215157) B1215157
theorem B1522061 : Blo 263822 1522061 := bstep (se 3 (by rfl) ⟨285386, by rfl⟩ : syracuseStep 1522061 = 570773) B570773
theorem B506321 : Blo 263822 506321 := bstep (se 2 (by rfl) ⟨189870, by rfl⟩ : syracuseStep 506321 = 379741) B379741
theorem B637507 : Blo 263822 637507 := bstep (se 1 (by rfl) ⟨478130, by rfl⟩ : syracuseStep 637507 = 956261) B956261
theorem B899693 : Blo 263822 899693 := bstep (se 3 (by rfl) ⟨168692, by rfl⟩ : syracuseStep 899693 = 337385) B337385
theorem B899747 : Blo 263822 899747 := bstep (se 1 (by rfl) ⟨674810, by rfl⟩ : syracuseStep 899747 = 1349621) B1349621
theorem B637699 : Blo 263822 637699 := bstep (se 1 (by rfl) ⟨478274, by rfl⟩ : syracuseStep 637699 = 956549) B956549
theorem B2145037 : Blo 263822 2145037 := bstep (se 3 (by rfl) ⟨402194, by rfl⟩ : syracuseStep 2145037 = 804389) B804389
theorem B900017 : Blo 263822 900017 := bstep (se 2 (by rfl) ⟨337506, by rfl⟩ : syracuseStep 900017 = 675013) B675013
theorem B637969 : Blo 263822 637969 := bstep (se 2 (by rfl) ⟨239238, by rfl⟩ : syracuseStep 637969 = 478477) B478477
theorem B670801 : Blo 263822 670801 := bstep (se 2 (by rfl) ⟨251550, by rfl⟩ : syracuseStep 670801 = 503101) B503101
theorem B1129571 : Blo 263822 1129571 := bstep (se 1 (by rfl) ⟨847178, by rfl⟩ : syracuseStep 1129571 = 1694357) B1694357
theorem B965773 : Blo 263822 965773 := bstep (se 3 (by rfl) ⟨181082, by rfl⟩ : syracuseStep 965773 = 362165) B362165
theorem B507217 : Blo 263822 507217 := bstep (se 2 (by rfl) ⟨190206, by rfl⟩ : syracuseStep 507217 = 380413) B380413
theorem B671075 : Blo 263822 671075 := bstep (se 1 (by rfl) ⟨503306, by rfl⟩ : syracuseStep 671075 = 1006613) B1006613
theorem B900557 : Blo 263822 900557 := bstep (se 3 (by rfl) ⟨168854, by rfl⟩ : syracuseStep 900557 = 337709) B337709
theorem B507377 : Blo 263822 507377 := bstep (se 2 (by rfl) ⟨190266, by rfl⟩ : syracuseStep 507377 = 380533) B380533
theorem B900611 : Blo 263822 900611 := bstep (se 1 (by rfl) ⟨675458, by rfl⟩ : syracuseStep 900611 = 1350917) B1350917
theorem B671267 : Blo 263822 671267 := bstep (se 1 (by rfl) ⟨503450, by rfl⟩ : syracuseStep 671267 = 1006901) B1006901
theorem B638545 : Blo 263822 638545 := bstep (se 2 (by rfl) ⟨239454, by rfl⟩ : syracuseStep 638545 = 478909) B478909
theorem B376483 : Blo 263822 376483 := bstep (se 1 (by rfl) ⟨282362, by rfl⟩ : syracuseStep 376483 = 564725) B564725
theorem B802541 : Blo 263822 802541 := bstep (se 3 (by rfl) ⟨150476, by rfl⟩ : syracuseStep 802541 = 300953) B300953
theorem B3391217 : Blo 263822 3391217 := bstep (se 2 (by rfl) ⟨1271706, by rfl⟩ : syracuseStep 3391217 = 2543413) B2543413
theorem B1162993 : Blo 263822 1162993 := bstep (se 2 (by rfl) ⟨436122, by rfl⟩ : syracuseStep 1162993 = 872245) B872245
theorem B900881 : Blo 263822 900881 := bstep (se 2 (by rfl) ⟨337830, by rfl⟩ : syracuseStep 900881 = 675661) B675661
theorem B507779 : Blo 263822 507779 := bstep (se 1 (by rfl) ⟨380834, by rfl⟩ : syracuseStep 507779 = 761669) B761669
theorem B638929 : Blo 263822 638929 := bstep (se 2 (by rfl) ⟨239598, by rfl⟩ : syracuseStep 638929 = 479197) B479197
theorem B2572273 : Blo 263822 2572273 := bstep (se 2 (by rfl) ⟨964602, by rfl⟩ : syracuseStep 2572273 = 1929205) B1929205
theorem B409619 : Blo 263822 409619 := bstep (se 1 (by rfl) ⟨307214, by rfl⟩ : syracuseStep 409619 = 614429) B614429
theorem B3031181 : Blo 263822 3031181 := bstep (se 3 (by rfl) ⟨568346, by rfl⟩ : syracuseStep 3031181 = 1136693) B1136693
theorem B606403 : Blo 263822 606403 := bstep (se 1 (by rfl) ⟨454802, by rfl⟩ : syracuseStep 606403 = 909605) B909605
theorem B901421 : Blo 263822 901421 := bstep (se 3 (by rfl) ⟨169016, by rfl⟩ : syracuseStep 901421 = 338033) B338033
theorem B901475 : Blo 263822 901475 := bstep (se 1 (by rfl) ⟨676106, by rfl⟩ : syracuseStep 901475 = 1352213) B1352213
theorem B672209 : Blo 263822 672209 := bstep (se 2 (by rfl) ⟨252078, by rfl⟩ : syracuseStep 672209 = 504157) B504157
theorem B410113 : Blo 263822 410113 := bstep (se 2 (by rfl) ⟨153792, by rfl⟩ : syracuseStep 410113 = 307585) B307585
theorem B672259 : Blo 263822 672259 := bstep (se 1 (by rfl) ⟨504194, by rfl⟩ : syracuseStep 672259 = 1008389) B1008389
theorem B2048611 : Blo 263822 2048611 := bstep (se 1 (by rfl) ⟨1536458, by rfl⟩ : syracuseStep 2048611 = 3072917) B3072917
theorem B901745 : Blo 263822 901745 := bstep (se 2 (by rfl) ⟨338154, by rfl⟩ : syracuseStep 901745 = 676309) B676309
theorem B672401 : Blo 263822 672401 := bstep (se 2 (by rfl) ⟨252150, by rfl⟩ : syracuseStep 672401 = 504301) B504301
theorem B377617 : Blo 263822 377617 := bstep (se 2 (by rfl) ⟨141606, by rfl⟩ : syracuseStep 377617 = 283213) B283213
theorem B377713 : Blo 263822 377713 := bstep (se 2 (by rfl) ⟨141642, by rfl⟩ : syracuseStep 377713 = 283285) B283285
theorem B967601 : Blo 263822 967601 := bstep (se 2 (by rfl) ⟨362850, by rfl⟩ : syracuseStep 967601 = 725701) B725701
theorem B1131569 : Blo 263822 1131569 := bstep (se 2 (by rfl) ⟨424338, by rfl⟩ : syracuseStep 1131569 = 848677) B848677
theorem B902285 : Blo 263822 902285 := bstep (se 3 (by rfl) ⟨169178, by rfl⟩ : syracuseStep 902285 = 338357) B338357
theorem B902339 : Blo 263822 902339 := bstep (se 1 (by rfl) ⟨676754, by rfl⟩ : syracuseStep 902339 = 1353509) B1353509
theorem B771277 : Blo 263822 771277 := bstep (se 3 (by rfl) ⟨144614, by rfl⟩ : syracuseStep 771277 = 289229) B289229
theorem B1524977 : Blo 263822 1524977 := bstep (se 2 (by rfl) ⟨571866, by rfl⟩ : syracuseStep 1524977 = 1143733) B1143733
theorem B542033 : Blo 263822 542033 := bstep (se 2 (by rfl) ⟨203262, by rfl⟩ : syracuseStep 542033 = 406525) B406525
theorem B378209 : Blo 263822 378209 := bstep (se 2 (by rfl) ⟨141828, by rfl⟩ : syracuseStep 378209 = 283657) B283657
theorem B902609 : Blo 263822 902609 := bstep (se 2 (by rfl) ⟨338478, by rfl⟩ : syracuseStep 902609 = 676957) B676957
theorem B673393 : Blo 263822 673393 := bstep (se 2 (by rfl) ⟨252522, by rfl⟩ : syracuseStep 673393 = 505045) B505045
theorem B476977 : Blo 263822 476977 := bstep (se 2 (by rfl) ⟨178866, by rfl⟩ : syracuseStep 476977 = 357733) B357733
theorem B673667 : Blo 263822 673667 := bstep (se 1 (by rfl) ⟨505250, by rfl⟩ : syracuseStep 673667 = 1010501) B1010501
theorem B903149 : Blo 263822 903149 := bstep (se 3 (by rfl) ⟨169340, by rfl⟩ : syracuseStep 903149 = 338681) B338681
theorem B903203 : Blo 263822 903203 := bstep (se 1 (by rfl) ⟨677402, by rfl⟩ : syracuseStep 903203 = 1354805) B1354805
theorem B673859 : Blo 263822 673859 := bstep (se 1 (by rfl) ⟨505394, by rfl⟩ : syracuseStep 673859 = 1010789) B1010789
theorem B3393677 : Blo 263822 3393677 := bstep (se 3 (by rfl) ⟨636314, by rfl⟩ : syracuseStep 3393677 = 1272629) B1272629
theorem B379075 : Blo 263822 379075 := bstep (se 1 (by rfl) ⟨284306, by rfl⟩ : syracuseStep 379075 = 568613) B568613
theorem B379171 : Blo 263822 379171 := bstep (se 1 (by rfl) ⟨284378, by rfl⟩ : syracuseStep 379171 = 568757) B568757
theorem B903473 : Blo 263822 903473 := bstep (se 2 (by rfl) ⟨338802, by rfl⟩ : syracuseStep 903473 = 677605) B677605
theorem B543395 : Blo 263822 543395 := bstep (se 1 (by rfl) ⟨407546, by rfl⟩ : syracuseStep 543395 = 815093) B815093
theorem B1133261 : Blo 263822 1133261 := bstep (se 3 (by rfl) ⟨212486, by rfl⟩ : syracuseStep 1133261 = 424973) B424973
theorem B1002253 : Blo 263822 1002253 := bstep (se 3 (by rfl) ⟨187922, by rfl⟩ : syracuseStep 1002253 = 375845) B375845
theorem B379667 : Blo 263822 379667 := bstep (se 1 (by rfl) ⟨284750, by rfl⟩ : syracuseStep 379667 = 569501) B569501
theorem B445297 : Blo 263822 445297 := bstep (se 2 (by rfl) ⟨166986, by rfl⟩ : syracuseStep 445297 = 333973) B333973
theorem B445331 : Blo 263822 445331 := bstep (se 1 (by rfl) ⟨333998, by rfl⟩ : syracuseStep 445331 = 667997) B667997
theorem B3034097 : Blo 263822 3034097 := bstep (se 2 (by rfl) ⟨1137786, by rfl⟩ : syracuseStep 3034097 = 2275573) B2275573
theorem B674801 : Blo 263822 674801 := bstep (se 2 (by rfl) ⟨253050, by rfl⟩ : syracuseStep 674801 = 506101) B506101
theorem B445459 : Blo 263822 445459 := bstep (se 1 (by rfl) ⟨334094, by rfl⟩ : syracuseStep 445459 = 668189) B668189
theorem B674851 : Blo 263822 674851 := bstep (se 1 (by rfl) ⟨506138, by rfl⟩ : syracuseStep 674851 = 1012277) B1012277
theorem B445601 : Blo 263822 445601 := bstep (se 2 (by rfl) ⟨167100, by rfl⟩ : syracuseStep 445601 = 334201) B334201
theorem B674993 : Blo 263822 674993 := bstep (se 2 (by rfl) ⟨253122, by rfl⟩ : syracuseStep 674993 = 506245) B506245
theorem B642275 : Blo 263822 642275 := bstep (se 1 (by rfl) ⟨481706, by rfl⟩ : syracuseStep 642275 = 963413) B963413
theorem B1428749 : Blo 263822 1428749 := bstep (se 3 (by rfl) ⟨267890, by rfl⟩ : syracuseStep 1428749 = 535781) B535781
theorem B445729 : Blo 263822 445729 := bstep (se 2 (by rfl) ⟨167148, by rfl⟩ : syracuseStep 445729 = 334297) B334297
theorem B445763 : Blo 263822 445763 := bstep (se 1 (by rfl) ⟨334322, by rfl⟩ : syracuseStep 445763 = 668645) B668645
theorem B380305 : Blo 263822 380305 := bstep (se 2 (by rfl) ⟨142614, by rfl⟩ : syracuseStep 380305 = 285229) B285229
theorem B445891 : Blo 263822 445891 := bstep (se 1 (by rfl) ⟨334418, by rfl⟩ : syracuseStep 445891 = 668837) B668837
theorem B1428941 : Blo 263822 1428941 := bstep (se 3 (by rfl) ⟨267926, by rfl⟩ : syracuseStep 1428941 = 535853) B535853
theorem B642563 : Blo 263822 642563 := bstep (se 1 (by rfl) ⟨481922, by rfl⟩ : syracuseStep 642563 = 963845) B963845
theorem B1003043 : Blo 263822 1003043 := bstep (se 1 (by rfl) ⟨752282, by rfl⟩ : syracuseStep 1003043 = 1504565) B1504565
theorem B577091 : Blo 263822 577091 := bstep (se 1 (by rfl) ⟨432818, by rfl⟩ : syracuseStep 577091 = 865637) B865637
theorem B446033 : Blo 263822 446033 := bstep (se 2 (by rfl) ⟨167262, by rfl⟩ : syracuseStep 446033 = 334525) B334525
theorem B446161 : Blo 263822 446161 := bstep (se 2 (by rfl) ⟨167310, by rfl⟩ : syracuseStep 446161 = 334621) B334621
theorem B380641 : Blo 263822 380641 := bstep (se 2 (by rfl) ⟨142740, by rfl⟩ : syracuseStep 380641 = 285481) B285481
theorem B446195 : Blo 263822 446195 := bstep (se 1 (by rfl) ⟨334646, by rfl⟩ : syracuseStep 446195 = 669293) B669293
theorem B282371 : Blo 263822 282371 := bstep (se 1 (by rfl) ⟨211778, by rfl⟩ : syracuseStep 282371 = 423557) B423557
theorem B446323 : Blo 263822 446323 := bstep (se 1 (by rfl) ⟨334742, by rfl⟩ : syracuseStep 446323 = 669485) B669485
theorem B4575203 : Blo 263822 4575203 := bstep (se 1 (by rfl) ⟨3431402, by rfl⟩ : syracuseStep 4575203 = 6862805) B6862805
theorem B446465 : Blo 263822 446465 := bstep (se 2 (by rfl) ⟨167424, by rfl⟩ : syracuseStep 446465 = 334849) B334849
theorem B446593 : Blo 263822 446593 := bstep (se 2 (by rfl) ⟨167472, by rfl⟩ : syracuseStep 446593 = 334945) B334945
theorem B479363 : Blo 263822 479363 := bstep (se 1 (by rfl) ⟨359522, by rfl⟩ : syracuseStep 479363 = 719045) B719045
theorem B675985 : Blo 263822 675985 := bstep (se 2 (by rfl) ⟨253494, by rfl⟩ : syracuseStep 675985 = 506989) B506989
theorem B446627 : Blo 263822 446627 := bstep (se 1 (by rfl) ⟨334970, by rfl⟩ : syracuseStep 446627 = 669941) B669941
theorem B1003697 : Blo 263822 1003697 := bstep (se 2 (by rfl) ⟨376386, by rfl⟩ : syracuseStep 1003697 = 752773) B752773
theorem B446755 : Blo 263822 446755 := bstep (se 1 (by rfl) ⟨335066, by rfl⟩ : syracuseStep 446755 = 670133) B670133
theorem B381233 : Blo 263822 381233 := bstep (se 2 (by rfl) ⟨142962, by rfl⟩ : syracuseStep 381233 = 285925) B285925
theorem B1528141 : Blo 263822 1528141 := bstep (se 3 (by rfl) ⟨286526, by rfl⟩ : syracuseStep 1528141 = 573053) B573053
theorem B676259 : Blo 263822 676259 := bstep (se 1 (by rfl) ⟨507194, by rfl⟩ : syracuseStep 676259 = 1014389) B1014389
theorem B446897 : Blo 263822 446897 := bstep (se 2 (by rfl) ⟨167586, by rfl⟩ : syracuseStep 446897 = 335173) B335173
theorem B283123 : Blo 263822 283123 := bstep (se 1 (by rfl) ⟨212342, by rfl⟩ : syracuseStep 283123 = 424685) B424685
theorem B447025 : Blo 263822 447025 := bstep (se 2 (by rfl) ⟨167634, by rfl⟩ : syracuseStep 447025 = 335269) B335269
theorem B479825 : Blo 263822 479825 := bstep (se 2 (by rfl) ⟨179934, by rfl⟩ : syracuseStep 479825 = 359869) B359869
theorem B447059 : Blo 263822 447059 := bstep (se 1 (by rfl) ⟨335294, by rfl⟩ : syracuseStep 447059 = 670589) B670589
theorem B676451 : Blo 263822 676451 := bstep (se 1 (by rfl) ⟨507338, by rfl⟩ : syracuseStep 676451 = 1014677) B1014677
theorem B447187 : Blo 263822 447187 := bstep (se 1 (by rfl) ⟨335390, by rfl⟩ : syracuseStep 447187 = 670781) B670781
theorem B447329 : Blo 263822 447329 := bstep (se 2 (by rfl) ⟨167748, by rfl⟩ : syracuseStep 447329 = 335497) B335497
theorem B447457 : Blo 263822 447457 := bstep (se 2 (by rfl) ⟨167796, by rfl⟩ : syracuseStep 447457 = 335593) B335593
theorem B447491 : Blo 263822 447491 := bstep (se 1 (by rfl) ⟨335618, by rfl⟩ : syracuseStep 447491 = 671237) B671237
theorem B480323 : Blo 263822 480323 := bstep (se 1 (by rfl) ⟨360242, by rfl⟩ : syracuseStep 480323 = 720485) B720485
theorem B808013 : Blo 263822 808013 := bstep (se 3 (by rfl) ⟨151502, by rfl⟩ : syracuseStep 808013 = 303005) B303005
theorem B578659 : Blo 263822 578659 := bstep (se 1 (by rfl) ⟨433994, by rfl⟩ : syracuseStep 578659 = 867989) B867989
theorem B447619 : Blo 263822 447619 := bstep (se 1 (by rfl) ⟨335714, by rfl⟩ : syracuseStep 447619 = 671429) B671429
theorem B447761 : Blo 263822 447761 := bstep (se 2 (by rfl) ⟨167910, by rfl⟩ : syracuseStep 447761 = 335821) B335821
theorem B447889 : Blo 263822 447889 := bstep (se 2 (by rfl) ⟨167958, by rfl⟩ : syracuseStep 447889 = 335917) B335917
theorem B447923 : Blo 263822 447923 := bstep (se 1 (by rfl) ⟨335942, by rfl⟩ : syracuseStep 447923 = 671885) B671885
theorem B677393 : Blo 263822 677393 := bstep (se 2 (by rfl) ⟨254022, by rfl⟩ : syracuseStep 677393 = 508045) B508045
theorem B448051 : Blo 263822 448051 := bstep (se 1 (by rfl) ⟨336038, by rfl⟩ : syracuseStep 448051 = 672077) B672077
theorem B677443 : Blo 263822 677443 := bstep (se 1 (by rfl) ⟨508082, by rfl⟩ : syracuseStep 677443 = 1016165) B1016165
theorem B1005155 : Blo 263822 1005155 := bstep (se 1 (by rfl) ⟨753866, by rfl⟩ : syracuseStep 1005155 = 1507733) B1507733
theorem B1005169 : Blo 263822 1005169 := bstep (se 2 (by rfl) ⟨376938, by rfl⟩ : syracuseStep 1005169 = 753877) B753877
theorem B480899 : Blo 263822 480899 := bstep (se 1 (by rfl) ⟨360674, by rfl⟩ : syracuseStep 480899 = 721349) B721349
theorem B448193 : Blo 263822 448193 := bstep (se 2 (by rfl) ⟨168072, by rfl⟩ : syracuseStep 448193 = 336145) B336145
theorem B677585 : Blo 263822 677585 := bstep (se 2 (by rfl) ⟨254094, by rfl⟩ : syracuseStep 677585 = 508189) B508189
theorem B1070833 : Blo 263822 1070833 := bstep (se 2 (by rfl) ⟨401562, by rfl⟩ : syracuseStep 1070833 = 803125) B803125
theorem B448321 : Blo 263822 448321 := bstep (se 2 (by rfl) ⟨168120, by rfl⟩ : syracuseStep 448321 = 336241) B336241
theorem B448355 : Blo 263822 448355 := bstep (se 1 (by rfl) ⟨336266, by rfl⟩ : syracuseStep 448355 = 672533) B672533
theorem B284515 : Blo 263822 284515 := bstep (se 1 (by rfl) ⟨213386, by rfl⟩ : syracuseStep 284515 = 426773) B426773
theorem B776081 : Blo 263822 776081 := bstep (se 2 (by rfl) ⟨291030, by rfl⟩ : syracuseStep 776081 = 582061) B582061
theorem B513955 : Blo 263822 513955 := bstep (se 1 (by rfl) ⟨385466, by rfl⟩ : syracuseStep 513955 = 770933) B770933
theorem B448483 : Blo 263822 448483 := bstep (se 1 (by rfl) ⟨336362, by rfl⟩ : syracuseStep 448483 = 672725) B672725
theorem B448625 : Blo 263822 448625 := bstep (se 2 (by rfl) ⟨168234, by rfl⟩ : syracuseStep 448625 = 336469) B336469
theorem B448753 : Blo 263822 448753 := bstep (se 2 (by rfl) ⟨168282, by rfl⟩ : syracuseStep 448753 = 336565) B336565
theorem B514307 : Blo 263822 514307 := bstep (se 1 (by rfl) ⟨385730, by rfl⟩ : syracuseStep 514307 = 771461) B771461
theorem B448787 : Blo 263822 448787 := bstep (se 1 (by rfl) ⟨336590, by rfl⟩ : syracuseStep 448787 = 673181) B673181
theorem B448915 : Blo 263822 448915 := bstep (se 1 (by rfl) ⟨336686, by rfl⟩ : syracuseStep 448915 = 673373) B673373
theorem B907757 : Blo 263822 907757 := bstep (se 3 (by rfl) ⟨170204, by rfl⟩ : syracuseStep 907757 = 340409) B340409
theorem B449057 : Blo 263822 449057 := bstep (se 2 (by rfl) ⟨168396, by rfl⟩ : syracuseStep 449057 = 336793) B336793
theorem B907853 : Blo 263822 907853 := bstep (se 3 (by rfl) ⟨170222, by rfl⟩ : syracuseStep 907853 = 340445) B340445
theorem B449185 : Blo 263822 449185 := bstep (se 2 (by rfl) ⟨168444, by rfl⟩ : syracuseStep 449185 = 336889) B336889
theorem B318115 : Blo 263822 318115 := bstep (se 1 (by rfl) ⟨238586, by rfl⟩ : syracuseStep 318115 = 477173) B477173
theorem B449219 : Blo 263822 449219 := bstep (se 1 (by rfl) ⟨336914, by rfl⟩ : syracuseStep 449219 = 673829) B673829
theorem B514769 : Blo 263822 514769 := bstep (se 2 (by rfl) ⟨193038, by rfl⟩ : syracuseStep 514769 = 386077) B386077
theorem B449347 : Blo 263822 449347 := bstep (se 1 (by rfl) ⟨337010, by rfl⟩ : syracuseStep 449347 = 674021) B674021
theorem B449489 : Blo 263822 449489 := bstep (se 2 (by rfl) ⟨168558, by rfl⟩ : syracuseStep 449489 = 337117) B337117
theorem B1137635 : Blo 263822 1137635 := bstep (se 1 (by rfl) ⟨853226, by rfl⟩ : syracuseStep 1137635 = 1706453) B1706453
theorem B1006627 : Blo 263822 1006627 := bstep (se 1 (by rfl) ⟨754970, by rfl⟩ : syracuseStep 1006627 = 1509941) B1509941
theorem B1694789 : Blo 263822 1694789 := bstep (se 4 (by rfl) ⟨158886, by rfl⟩ : syracuseStep 1694789 = 317773) B317773
theorem B449617 : Blo 263822 449617 := bstep (se 2 (by rfl) ⟨168606, by rfl⟩ : syracuseStep 449617 = 337213) B337213
theorem B449651 : Blo 263822 449651 := bstep (se 1 (by rfl) ⟨337238, by rfl⟩ : syracuseStep 449651 = 674477) B674477
theorem B449779 : Blo 263822 449779 := bstep (se 1 (by rfl) ⟨337334, by rfl⟩ : syracuseStep 449779 = 674669) B674669
theorem B810253 : Blo 263822 810253 := bstep (se 3 (by rfl) ⟨151922, by rfl⟩ : syracuseStep 810253 = 303845) B303845
theorem B449921 : Blo 263822 449921 := bstep (se 2 (by rfl) ⟨168720, by rfl⟩ : syracuseStep 449921 = 337441) B337441
theorem B450049 : Blo 263822 450049 := bstep (se 2 (by rfl) ⟨168768, by rfl⟩ : syracuseStep 450049 = 337537) B337537
theorem B450083 : Blo 263822 450083 := bstep (se 1 (by rfl) ⟨337562, by rfl⟩ : syracuseStep 450083 = 675125) B675125
theorem B450211 : Blo 263822 450211 := bstep (se 1 (by rfl) ⟨337658, by rfl⟩ : syracuseStep 450211 = 675317) B675317
theorem B1269539 : Blo 263822 1269539 := bstep (se 1 (by rfl) ⟨952154, by rfl⟩ : syracuseStep 1269539 = 1904309) B1904309
theorem B450353 : Blo 263822 450353 := bstep (se 2 (by rfl) ⟨168882, by rfl⟩ : syracuseStep 450353 = 337765) B337765
theorem B450481 : Blo 263822 450481 := bstep (se 2 (by rfl) ⟨168930, by rfl⟩ : syracuseStep 450481 = 337861) B337861
theorem B450515 : Blo 263822 450515 := bstep (se 1 (by rfl) ⟨337886, by rfl⟩ : syracuseStep 450515 = 675773) B675773
theorem B450643 : Blo 263822 450643 := bstep (se 1 (by rfl) ⟨337982, by rfl⟩ : syracuseStep 450643 = 675965) B675965
theorem B1466545 : Blo 263822 1466545 := bstep (se 2 (by rfl) ⟨549954, by rfl⟩ : syracuseStep 1466545 = 1099909) B1099909
theorem B385217 : Blo 263822 385217 := bstep (se 2 (by rfl) ⟨144456, by rfl⟩ : syracuseStep 385217 = 288913) B288913
theorem B450785 : Blo 263822 450785 := bstep (se 2 (by rfl) ⟨169044, by rfl⟩ : syracuseStep 450785 = 338089) B338089
theorem B1270093 : Blo 263822 1270093 := bstep (se 3 (by rfl) ⟨238142, by rfl⟩ : syracuseStep 1270093 = 476285) B476285
theorem B450913 : Blo 263822 450913 := bstep (se 2 (by rfl) ⟨169092, by rfl⟩ : syracuseStep 450913 = 338185) B338185
theorem B450947 : Blo 263822 450947 := bstep (se 1 (by rfl) ⟨338210, by rfl⟩ : syracuseStep 450947 = 676421) B676421
theorem B319907 : Blo 263822 319907 := bstep (se 1 (by rfl) ⟨239930, by rfl⟩ : syracuseStep 319907 = 479861) B479861
theorem B451075 : Blo 263822 451075 := bstep (se 1 (by rfl) ⟨338306, by rfl⟩ : syracuseStep 451075 = 676613) B676613
theorem B811565 : Blo 263822 811565 := bstep (se 3 (by rfl) ⟨152168, by rfl⟩ : syracuseStep 811565 = 304337) B304337
theorem B451217 : Blo 263822 451217 := bstep (se 2 (by rfl) ⟨169206, by rfl⟩ : syracuseStep 451217 = 338413) B338413
theorem B1336013 : Blo 263822 1336013 := bstep (se 3 (by rfl) ⟨250502, by rfl⟩ : syracuseStep 1336013 = 501005) B501005
theorem B451345 : Blo 263822 451345 := bstep (se 2 (by rfl) ⟨169254, by rfl⟩ : syracuseStep 451345 = 338509) B338509
theorem B451379 : Blo 263822 451379 := bstep (se 1 (by rfl) ⟨338534, by rfl⟩ : syracuseStep 451379 = 677069) B677069
theorem B1729349 : Blo 263822 1729349 := bstep (se 4 (by rfl) ⟨162126, by rfl⟩ : syracuseStep 1729349 = 324253) B324253
theorem B320387 : Blo 263822 320387 := bstep (se 1 (by rfl) ⟨240290, by rfl⟩ : syracuseStep 320387 = 480581) B480581
theorem B1139633 : Blo 263822 1139633 := bstep (se 2 (by rfl) ⟨427362, by rfl⟩ : syracuseStep 1139633 = 854725) B854725
theorem B451507 : Blo 263822 451507 := bstep (se 1 (by rfl) ⟨338630, by rfl⟩ : syracuseStep 451507 = 677261) B677261
theorem B680899 : Blo 263822 680899 := bstep (se 1 (by rfl) ⟨510674, by rfl⟩ : syracuseStep 680899 = 1021349) B1021349
theorem B451649 : Blo 263822 451649 := bstep (se 2 (by rfl) ⟨169368, by rfl⟩ : syracuseStep 451649 = 338737) B338737
theorem B681137 : Blo 263822 681137 := bstep (se 2 (by rfl) ⟨255426, by rfl⟩ : syracuseStep 681137 = 510853) B510853
theorem B451777 : Blo 263822 451777 := bstep (se 2 (by rfl) ⟨169416, by rfl⟩ : syracuseStep 451777 = 338833) B338833
theorem B3826885 : Blo 263822 3826885 := bstep (se 4 (by rfl) ⟨358770, by rfl⟩ : syracuseStep 3826885 = 717541) B717541
theorem B1008845 : Blo 263822 1008845 := bstep (se 3 (by rfl) ⟨189158, by rfl⟩ : syracuseStep 1008845 = 378317) B378317
theorem B2024675 : Blo 263822 2024675 := bstep (se 1 (by rfl) ⟨1518506, by rfl⟩ : syracuseStep 2024675 = 3037013) B3037013
theorem B451811 : Blo 263822 451811 := bstep (se 1 (by rfl) ⟨338858, by rfl⟩ : syracuseStep 451811 = 677717) B677717
theorem B451939 : Blo 263822 451939 := bstep (se 1 (by rfl) ⟨338954, by rfl⟩ : syracuseStep 451939 = 677909) B677909
theorem B1697507 : Blo 263822 1697507 := bstep (se 1 (by rfl) ⟨1273130, by rfl⟩ : syracuseStep 1697507 = 2546261) B2546261
theorem B1271537 : Blo 263822 1271537 := bstep (se 2 (by rfl) ⟨476826, by rfl⟩ : syracuseStep 1271537 = 953653) B953653
theorem B2254661 : Blo 263822 2254661 := bstep (se 4 (by rfl) ⟨211374, by rfl⟩ : syracuseStep 2254661 = 422749) B422749
theorem B1108081 : Blo 263822 1108081 := bstep (se 2 (by rfl) ⟨415530, by rfl⟩ : syracuseStep 1108081 = 831061) B831061
theorem B2418929 : Blo 263822 2418929 := bstep (se 2 (by rfl) ⟨907098, by rfl⟩ : syracuseStep 2418929 = 1814197) B1814197
theorem B5073293 : Blo 263822 5073293 := bstep (se 3 (by rfl) ⟨951242, by rfl⟩ : syracuseStep 5073293 = 1902485) B1902485
theorem B3238469 : Blo 263822 3238469 := bstep (se 4 (by rfl) ⟨303606, by rfl⟩ : syracuseStep 3238469 = 607213) B607213
theorem B518737 : Blo 263822 518737 := bstep (se 2 (by rfl) ⟨194526, by rfl⟩ : syracuseStep 518737 = 389053) B389053
theorem B1305229 : Blo 263822 1305229 := bstep (se 3 (by rfl) ⟨244730, by rfl⟩ : syracuseStep 1305229 = 489461) B489461
theorem B813731 : Blo 263822 813731 := bstep (se 1 (by rfl) ⟨610298, by rfl⟩ : syracuseStep 813731 = 1220597) B1220597
theorem B813901 : Blo 263822 813901 := bstep (se 3 (by rfl) ⟨152606, by rfl⟩ : syracuseStep 813901 = 305213) B305213
theorem B813997 : Blo 263822 813997 := bstep (se 3 (by rfl) ⟨152624, by rfl⟩ : syracuseStep 813997 = 305249) B305249
theorem B1142093 : Blo 263822 1142093 := bstep (se 3 (by rfl) ⟨214142, by rfl⟩ : syracuseStep 1142093 = 428285) B428285
theorem B1273229 : Blo 263822 1273229 := bstep (se 3 (by rfl) ⟨238730, by rfl⟩ : syracuseStep 1273229 = 477461) B477461
theorem B1338929 : Blo 263822 1338929 := bstep (se 2 (by rfl) ⟨502098, by rfl⟩ : syracuseStep 1338929 = 1004197) B1004197
theorem B1502833 : Blo 263822 1502833 := bstep (se 2 (by rfl) ⟨563562, by rfl⟩ : syracuseStep 1502833 = 1127125) B1127125
theorem B2551409 : Blo 263822 2551409 := bstep (se 2 (by rfl) ⟨956778, by rfl⟩ : syracuseStep 2551409 = 1913557) B1913557
theorem B847523 : Blo 263822 847523 := bstep (se 1 (by rfl) ⟨635642, by rfl⟩ : syracuseStep 847523 = 1271285) B1271285
theorem B1699505 : Blo 263822 1699505 := bstep (se 2 (by rfl) ⟨637314, by rfl⟩ : syracuseStep 1699505 = 1274629) B1274629
theorem B4419269 : Blo 263822 4419269 := bstep (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) B828613
theorem B1077155 : Blo 263822 1077155 := bstep (se 1 (by rfl) ⟨807866, by rfl⟩ : syracuseStep 1077155 = 1615733) B1615733
theorem B1011761 : Blo 263822 1011761 := bstep (se 2 (by rfl) ⟨379410, by rfl⟩ : syracuseStep 1011761 = 758821) B758821
theorem B454753 : Blo 263822 454753 := bstep (se 2 (by rfl) ⟨170532, by rfl⟩ : syracuseStep 454753 = 341065) B341065
theorem B782669 : Blo 263822 782669 := bstep (se 3 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 782669 = 293501) B293501
theorem B4518341 : Blo 263822 4518341 := bstep (se 4 (by rfl) ⟨423594, by rfl⟩ : syracuseStep 4518341 = 847189) B847189
theorem B848369 : Blo 263822 848369 := bstep (se 2 (by rfl) ⟨318138, by rfl⟩ : syracuseStep 848369 = 636277) B636277
theorem B717457 : Blo 263822 717457 := bstep (se 2 (by rfl) ⟨269046, by rfl⟩ : syracuseStep 717457 = 538093) B538093
theorem B389873 : Blo 263822 389873 := bstep (se 2 (by rfl) ⟨146202, by rfl⟩ : syracuseStep 389873 = 292405) B292405
theorem B1143665 : Blo 263822 1143665 := bstep (se 2 (by rfl) ⟨428874, by rfl⟩ : syracuseStep 1143665 = 857749) B857749
theorem B1340387 : Blo 263822 1340387 := bstep (se 1 (by rfl) ⟨1005290, by rfl⟩ : syracuseStep 1340387 = 2010581) B2010581
theorem B685027 : Blo 263822 685027 := bstep (se 1 (by rfl) ⟨513770, by rfl⟩ : syracuseStep 685027 = 1027541) B1027541
theorem B914435 : Blo 263822 914435 := bstep (se 1 (by rfl) ⟨685826, by rfl⟩ : syracuseStep 914435 = 1371653) B1371653
theorem B455699 : Blo 263822 455699 := bstep (se 1 (by rfl) ⟨341774, by rfl⟩ : syracuseStep 455699 = 683549) B683549
theorem B1504291 : Blo 263822 1504291 := bstep (se 1 (by rfl) ⟨1128218, by rfl⟩ : syracuseStep 1504291 = 2256437) B2256437
theorem B455843 : Blo 263822 455843 := bstep (se 1 (by rfl) ⟨341882, by rfl⟩ : syracuseStep 455843 = 683765) B683765
theorem B1013219 : Blo 263822 1013219 := bstep (se 1 (by rfl) ⟨759914, by rfl⟩ : syracuseStep 1013219 = 1519829) B1519829
theorem B1504817 : Blo 263822 1504817 := bstep (se 2 (by rfl) ⟨564306, by rfl⟩ : syracuseStep 1504817 = 1128613) B1128613
theorem B1341197 : Blo 263822 1341197 := bstep (se 3 (by rfl) ⟨251474, by rfl⟩ : syracuseStep 1341197 = 502949) B502949
theorem B358241 : Blo 263822 358241 := bstep (se 2 (by rfl) ⟨134340, by rfl⟩ : syracuseStep 358241 = 268681) B268681
theorem B915299 : Blo 263822 915299 := bstep (se 1 (by rfl) ⟨686474, by rfl⟩ : syracuseStep 915299 = 1372949) B1372949
theorem B718733 : Blo 263822 718733 := bstep (se 3 (by rfl) ⟨134762, by rfl⟩ : syracuseStep 718733 = 269525) B269525
theorem B2553869 : Blo 263822 2553869 := bstep (se 3 (by rfl) ⟨478850, by rfl⟩ : syracuseStep 2553869 = 957701) B957701
theorem B1701965 : Blo 263822 1701965 := bstep (se 3 (by rfl) ⟨319118, by rfl⟩ : syracuseStep 1701965 = 638237) B638237
theorem B719057 : Blo 263822 719057 := bstep (se 2 (by rfl) ⟨269646, by rfl⟩ : syracuseStep 719057 = 539293) B539293
theorem B2291939 : Blo 263822 2291939 := bstep (se 1 (by rfl) ⟨1718954, by rfl⟩ : syracuseStep 2291939 = 3437909) B3437909
theorem B850189 : Blo 263822 850189 := bstep (se 3 (by rfl) ⟨159410, by rfl⟩ : syracuseStep 850189 = 318821) B318821
theorem B9238981 : Blo 263822 9238981 := bstep (se 4 (by rfl) ⟨866154, by rfl⟩ : syracuseStep 9238981 = 1732309) B1732309
theorem B2030021 : Blo 263822 2030021 := bstep (se 4 (by rfl) ⟨190314, by rfl⟩ : syracuseStep 2030021 = 380629) B380629
theorem B1014221 : Blo 263822 1014221 := bstep (se 3 (by rfl) ⟨190166, by rfl⟩ : syracuseStep 1014221 = 380333) B380333
theorem B2882101 : Blo 263822 2882101 := bstep (se 5 (by rfl) ⟨135098, by rfl⟩ : syracuseStep 2882101 = 270197) B270197
theorem B424531 : Blo 263822 424531 := bstep (se 1 (by rfl) ⟨318398, by rfl⟩ : syracuseStep 424531 = 636797) B636797
theorem B752237 : Blo 263822 752237 := bstep (se 3 (by rfl) ⟨141044, by rfl⟩ : syracuseStep 752237 = 282089) B282089
theorem B424595 : Blo 263822 424595 := bstep (se 1 (by rfl) ⟨318446, by rfl⟩ : syracuseStep 424595 = 636893) B636893
theorem B916145 : Blo 263822 916145 := bstep (se 2 (by rfl) ⟨343554, by rfl⟩ : syracuseStep 916145 = 687109) B687109
theorem B752419 : Blo 263822 752419 := bstep (se 1 (by rfl) ⟨564314, by rfl⟩ : syracuseStep 752419 = 1128629) B1128629
theorem B752465 : Blo 263822 752465 := bstep (se 2 (by rfl) ⟨282174, by rfl⟩ : syracuseStep 752465 = 564349) B564349
theorem B1506275 : Blo 263822 1506275 := bstep (se 1 (by rfl) ⟨1129706, by rfl⟩ : syracuseStep 1506275 = 2259413) B2259413
theorem B719857 : Blo 263822 719857 := bstep (se 2 (by rfl) ⟨269946, by rfl⟩ : syracuseStep 719857 = 539893) B539893
theorem B3013685 : Blo 263822 3013685 := bstep (se 5 (by rfl) ⟨141266, by rfl⟩ : syracuseStep 3013685 = 282533) B282533
theorem B3079565 : Blo 263822 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B425569 : Blo 263822 425569 := bstep (se 2 (by rfl) ⟨159588, by rfl⟩ : syracuseStep 425569 = 319177) B319177
theorem B2719331 : Blo 263822 2719331 := bstep (se 1 (by rfl) ⟨2039498, by rfl⟩ : syracuseStep 2719331 = 4078997) B4078997
theorem B2031245 : Blo 263822 2031245 := bstep (se 3 (by rfl) ⟨380858, by rfl⟩ : syracuseStep 2031245 = 761717) B761717
theorem B425825 : Blo 263822 425825 := bstep (se 2 (by rfl) ⟨159684, by rfl⟩ : syracuseStep 425825 = 319369) B319369
theorem B720785 : Blo 263822 720785 := bstep (se 2 (by rfl) ⟨270294, by rfl⟩ : syracuseStep 720785 = 540589) B540589
theorem B1343789 : Blo 263822 1343789 := bstep (se 3 (by rfl) ⟨251960, by rfl⟩ : syracuseStep 1343789 = 503921) B503921
theorem B2031965 : Blo 263822 2031965 := bstep (se 3 (by rfl) ⟨380993, by rfl⟩ : syracuseStep 2031965 = 761987) B761987
theorem B2425349 : Blo 263822 2425349 := bstep (se 4 (by rfl) ⟨227376, by rfl⟩ : syracuseStep 2425349 = 454753) B454753
theorem B754265 : Blo 263822 754265 := bstep (se 2 (by rfl) ⟨282849, by rfl⟩ : syracuseStep 754265 = 565699) B565699
theorem B754379 : Blo 263822 754379 := bstep (se 1 (by rfl) ⟨565784, by rfl⟩ : syracuseStep 754379 = 1131569) B1131569
theorem B1016621 : Blo 263822 1016621 := bstep (se 3 (by rfl) ⟨190616, by rfl⟩ : syracuseStep 1016621 = 381233) B381233
theorem B1016651 : Blo 263822 1016651 := bstep (se 1 (by rfl) ⟨762488, by rfl⟩ : syracuseStep 1016651 = 1524977) B1524977
theorem B361355 : Blo 263822 361355 := bstep (se 1 (by rfl) ⟨271016, by rfl⟩ : syracuseStep 361355 = 542033) B542033
theorem B6489011 : Blo 263822 6489011 := bstep (se 1 (by rfl) ⟨4866758, by rfl⟩ : syracuseStep 6489011 = 9733517) B9733517
theorem B853085 : Blo 263822 853085 := bstep (se 3 (by rfl) ⟨159953, by rfl⟩ : syracuseStep 853085 = 319907) B319907
theorem B1508483 : Blo 263822 1508483 := bstep (se 1 (by rfl) ⟨1131362, by rfl⟩ : syracuseStep 1508483 = 2262725) B2262725
theorem B5113205 : Blo 263822 5113205 := bstep (se 5 (by rfl) ⟨239681, by rfl⟩ : syracuseStep 5113205 = 479363) B479363
theorem B2262451 : Blo 263822 2262451 := bstep (se 1 (by rfl) ⟨1696838, by rfl⟩ : syracuseStep 2262451 = 3393677) B3393677
theorem B361945 : Blo 263822 361945 := bstep (se 2 (by rfl) ⟨135729, by rfl⟩ : syracuseStep 361945 = 271459) B271459
theorem B1508939 : Blo 263822 1508939 := bstep (se 1 (by rfl) ⟨1131704, by rfl⟩ : syracuseStep 1508939 = 2263409) B2263409
theorem B263831 : Blo 263822 263831 := bstep (se 1 (by rfl) ⟨197873, by rfl⟩ : syracuseStep 263831 = 395747) B395747
theorem B263851 : Blo 263822 263851 := bstep (se 1 (by rfl) ⟨197888, by rfl⟩ : syracuseStep 263851 = 395777) B395777
theorem B263863 : Blo 263822 263863 := bstep (se 1 (by rfl) ⟨197897, by rfl⟩ : syracuseStep 263863 = 395795) B395795
theorem B263883 : Blo 263822 263883 := bstep (se 1 (by rfl) ⟨197912, by rfl⟩ : syracuseStep 263883 = 395825) B395825
theorem B263895 : Blo 263822 263895 := bstep (se 1 (by rfl) ⟨197921, by rfl⟩ : syracuseStep 263895 = 395843) B395843
theorem B263915 : Blo 263822 263915 := bstep (se 1 (by rfl) ⟨197936, by rfl⟩ : syracuseStep 263915 = 395873) B395873
theorem B263927 : Blo 263822 263927 := bstep (se 1 (by rfl) ⟨197945, by rfl⟩ : syracuseStep 263927 = 395891) B395891
theorem B263947 : Blo 263822 263947 := bstep (se 1 (by rfl) ⟨197960, by rfl⟩ : syracuseStep 263947 = 395921) B395921
theorem B263959 : Blo 263822 263959 := bstep (se 1 (by rfl) ⟨197969, by rfl⟩ : syracuseStep 263959 = 395939) B395939
theorem B362263 : Blo 263822 362263 := bstep (se 1 (by rfl) ⟨271697, by rfl⟩ : syracuseStep 362263 = 543395) B543395
theorem B263979 : Blo 263822 263979 := bstep (se 1 (by rfl) ⟨197984, by rfl⟩ : syracuseStep 263979 = 395969) B395969
theorem B755507 : Blo 263822 755507 := bstep (se 1 (by rfl) ⟨566630, by rfl⟩ : syracuseStep 755507 = 1133261) B1133261
theorem B263991 : Blo 263822 263991 := bstep (se 1 (by rfl) ⟨197993, by rfl⟩ : syracuseStep 263991 = 395987) B395987
theorem B264011 : Blo 263822 264011 := bstep (se 1 (by rfl) ⟨198008, by rfl⟩ : syracuseStep 264011 = 396017) B396017
theorem B264023 : Blo 263822 264023 := bstep (se 1 (by rfl) ⟨198017, by rfl⟩ : syracuseStep 264023 = 396035) B396035
theorem B264043 : Blo 263822 264043 := bstep (se 1 (by rfl) ⟨198032, by rfl⟩ : syracuseStep 264043 = 396065) B396065
theorem B264055 : Blo 263822 264055 := bstep (se 1 (by rfl) ⟨198041, by rfl⟩ : syracuseStep 264055 = 396083) B396083
theorem B264075 : Blo 263822 264075 := bstep (se 1 (by rfl) ⟨198056, by rfl⟩ : syracuseStep 264075 = 396113) B396113
theorem B264087 : Blo 263822 264087 := bstep (se 1 (by rfl) ⟨198065, by rfl⟩ : syracuseStep 264087 = 396131) B396131
theorem B264107 : Blo 263822 264107 := bstep (se 1 (by rfl) ⟨198080, by rfl⟩ : syracuseStep 264107 = 396161) B396161
theorem B296887 : Blo 263822 296887 := bstep (se 1 (by rfl) ⟨222665, by rfl⟩ : syracuseStep 296887 = 445331) B445331
theorem B264119 : Blo 263822 264119 := bstep (se 1 (by rfl) ⟨198089, by rfl⟩ : syracuseStep 264119 = 396179) B396179
theorem B264139 : Blo 263822 264139 := bstep (se 1 (by rfl) ⟨198104, by rfl⟩ : syracuseStep 264139 = 396209) B396209
theorem B264151 : Blo 263822 264151 := bstep (se 1 (by rfl) ⟨198113, by rfl⟩ : syracuseStep 264151 = 396227) B396227
theorem B264171 : Blo 263822 264171 := bstep (se 1 (by rfl) ⟨198128, by rfl⟩ : syracuseStep 264171 = 396257) B396257
theorem B264183 : Blo 263822 264183 := bstep (se 1 (by rfl) ⟨198137, by rfl⟩ : syracuseStep 264183 = 396275) B396275
theorem B264203 : Blo 263822 264203 := bstep (se 1 (by rfl) ⟨198152, by rfl⟩ : syracuseStep 264203 = 396305) B396305
theorem B264215 : Blo 263822 264215 := bstep (se 1 (by rfl) ⟨198161, by rfl⟩ : syracuseStep 264215 = 396323) B396323
theorem B264235 : Blo 263822 264235 := bstep (se 1 (by rfl) ⟨198176, by rfl⟩ : syracuseStep 264235 = 396353) B396353
theorem B264247 : Blo 263822 264247 := bstep (se 1 (by rfl) ⟨198185, by rfl⟩ : syracuseStep 264247 = 396371) B396371
theorem B264267 : Blo 263822 264267 := bstep (se 1 (by rfl) ⟨198200, by rfl⟩ : syracuseStep 264267 = 396401) B396401
theorem B264279 : Blo 263822 264279 := bstep (se 1 (by rfl) ⟨198209, by rfl⟩ : syracuseStep 264279 = 396419) B396419
theorem B1935461 : Blo 263822 1935461 := bstep (se 4 (by rfl) ⟨181449, by rfl⟩ : syracuseStep 1935461 = 362899) B362899
theorem B297067 : Blo 263822 297067 := bstep (se 1 (by rfl) ⟨222800, by rfl⟩ : syracuseStep 297067 = 445601) B445601
theorem B264299 : Blo 263822 264299 := bstep (se 1 (by rfl) ⟨198224, by rfl⟩ : syracuseStep 264299 = 396449) B396449
theorem B264311 : Blo 263822 264311 := bstep (se 1 (by rfl) ⟨198233, by rfl⟩ : syracuseStep 264311 = 396467) B396467
theorem B264331 : Blo 263822 264331 := bstep (se 1 (by rfl) ⟨198248, by rfl⟩ : syracuseStep 264331 = 396497) B396497
theorem B264343 : Blo 263822 264343 := bstep (se 1 (by rfl) ⟨198257, by rfl⟩ : syracuseStep 264343 = 396515) B396515
theorem B428183 : Blo 263822 428183 := bstep (se 1 (by rfl) ⟨321137, by rfl⟩ : syracuseStep 428183 = 642275) B642275
theorem B264363 : Blo 263822 264363 := bstep (se 1 (by rfl) ⟨198272, by rfl⟩ : syracuseStep 264363 = 396545) B396545
theorem B952499 : Blo 263822 952499 := bstep (se 1 (by rfl) ⟨714374, by rfl⟩ : syracuseStep 952499 = 1428749) B1428749
theorem B264375 : Blo 263822 264375 := bstep (se 1 (by rfl) ⟨198281, by rfl⟩ : syracuseStep 264375 = 396563) B396563
theorem B755905 : Blo 263822 755905 := bstep (se 2 (by rfl) ⟨283464, by rfl⟩ : syracuseStep 755905 = 566929) B566929
theorem B264395 : Blo 263822 264395 := bstep (se 1 (by rfl) ⟨198296, by rfl⟩ : syracuseStep 264395 = 396593) B396593
theorem B297175 : Blo 263822 297175 := bstep (se 1 (by rfl) ⟨222881, by rfl⟩ : syracuseStep 297175 = 445763) B445763
theorem B264407 : Blo 263822 264407 := bstep (se 1 (by rfl) ⟨198305, by rfl⟩ : syracuseStep 264407 = 396611) B396611
theorem B264427 : Blo 263822 264427 := bstep (se 1 (by rfl) ⟨198320, by rfl⟩ : syracuseStep 264427 = 396641) B396641
theorem B264439 : Blo 263822 264439 := bstep (se 1 (by rfl) ⟨198329, by rfl⟩ : syracuseStep 264439 = 396659) B396659
theorem B264459 : Blo 263822 264459 := bstep (se 1 (by rfl) ⟨198344, by rfl⟩ : syracuseStep 264459 = 396689) B396689
theorem B264471 : Blo 263822 264471 := bstep (se 1 (by rfl) ⟨198353, by rfl⟩ : syracuseStep 264471 = 396707) B396707
theorem B264491 : Blo 263822 264491 := bstep (se 1 (by rfl) ⟨198368, by rfl⟩ : syracuseStep 264491 = 396737) B396737
theorem B952627 : Blo 263822 952627 := bstep (se 1 (by rfl) ⟨714470, by rfl⟩ : syracuseStep 952627 = 1428941) B1428941
theorem B264503 : Blo 263822 264503 := bstep (se 1 (by rfl) ⟨198377, by rfl⟩ : syracuseStep 264503 = 396755) B396755
theorem B264523 : Blo 263822 264523 := bstep (se 1 (by rfl) ⟨198392, by rfl⟩ : syracuseStep 264523 = 396785) B396785
theorem B264535 : Blo 263822 264535 := bstep (se 1 (by rfl) ⟨198401, by rfl⟩ : syracuseStep 264535 = 396803) B396803
theorem B428375 : Blo 263822 428375 := bstep (se 1 (by rfl) ⟨321281, by rfl⟩ : syracuseStep 428375 = 642563) B642563
theorem B264555 : Blo 263822 264555 := bstep (se 1 (by rfl) ⟨198416, by rfl⟩ : syracuseStep 264555 = 396833) B396833
theorem B264567 : Blo 263822 264567 := bstep (se 1 (by rfl) ⟨198425, by rfl⟩ : syracuseStep 264567 = 396851) B396851
theorem B1575299 : Blo 263822 1575299 := bstep (se 1 (by rfl) ⟨1181474, by rfl⟩ : syracuseStep 1575299 = 2362949) B2362949
theorem B297355 : Blo 263822 297355 := bstep (se 1 (by rfl) ⟨223016, by rfl⟩ : syracuseStep 297355 = 446033) B446033
theorem B264587 : Blo 263822 264587 := bstep (se 1 (by rfl) ⟨198440, by rfl⟩ : syracuseStep 264587 = 396881) B396881
theorem B264599 : Blo 263822 264599 := bstep (se 1 (by rfl) ⟨198449, by rfl⟩ : syracuseStep 264599 = 396899) B396899
theorem B264619 : Blo 263822 264619 := bstep (se 1 (by rfl) ⟨198464, by rfl⟩ : syracuseStep 264619 = 396929) B396929
theorem B264631 : Blo 263822 264631 := bstep (se 1 (by rfl) ⟨198473, by rfl⟩ : syracuseStep 264631 = 396947) B396947
theorem B264651 : Blo 263822 264651 := bstep (se 1 (by rfl) ⟨198488, by rfl⟩ : syracuseStep 264651 = 396977) B396977
theorem B395735 : Blo 263822 395735 := bstep (se 1 (by rfl) ⟨296801, by rfl⟩ : syracuseStep 395735 = 593603) B593603
theorem B264663 : Blo 263822 264663 := bstep (se 1 (by rfl) ⟨198497, by rfl⟩ : syracuseStep 264663 = 396995) B396995
theorem B264683 : Blo 263822 264683 := bstep (se 1 (by rfl) ⟨198512, by rfl⟩ : syracuseStep 264683 = 397025) B397025
theorem B297463 : Blo 263822 297463 := bstep (se 1 (by rfl) ⟨223097, by rfl⟩ : syracuseStep 297463 = 446195) B446195
theorem B264695 : Blo 263822 264695 := bstep (se 1 (by rfl) ⟨198521, by rfl⟩ : syracuseStep 264695 = 397043) B397043
theorem B264715 : Blo 263822 264715 := bstep (se 1 (by rfl) ⟨198536, by rfl⟩ : syracuseStep 264715 = 397073) B397073
theorem B264727 : Blo 263822 264727 := bstep (se 1 (by rfl) ⟨198545, by rfl⟩ : syracuseStep 264727 = 397091) B397091
theorem B395801 : Blo 263822 395801 := bstep (se 2 (by rfl) ⟨148425, by rfl⟩ : syracuseStep 395801 = 296851) B296851
theorem B264747 : Blo 263822 264747 := bstep (se 1 (by rfl) ⟨198560, by rfl⟩ : syracuseStep 264747 = 397121) B397121
theorem B264759 : Blo 263822 264759 := bstep (se 1 (by rfl) ⟨198569, by rfl⟩ : syracuseStep 264759 = 397139) B397139
theorem B264779 : Blo 263822 264779 := bstep (se 1 (by rfl) ⟨198584, by rfl⟩ : syracuseStep 264779 = 397169) B397169
theorem B264791 : Blo 263822 264791 := bstep (se 1 (by rfl) ⟨198593, by rfl⟩ : syracuseStep 264791 = 397187) B397187
theorem B264811 : Blo 263822 264811 := bstep (se 1 (by rfl) ⟨198608, by rfl⟩ : syracuseStep 264811 = 397217) B397217
theorem B264823 : Blo 263822 264823 := bstep (se 1 (by rfl) ⟨198617, by rfl⟩ : syracuseStep 264823 = 397235) B397235
theorem B395915 : Blo 263822 395915 := bstep (se 1 (by rfl) ⟨296936, by rfl⟩ : syracuseStep 395915 = 593873) B593873
theorem B264843 : Blo 263822 264843 := bstep (se 1 (by rfl) ⟨198632, by rfl⟩ : syracuseStep 264843 = 397265) B397265
theorem B395927 : Blo 263822 395927 := bstep (se 1 (by rfl) ⟨296945, by rfl⟩ : syracuseStep 395927 = 593891) B593891
theorem B264855 : Blo 263822 264855 := bstep (se 1 (by rfl) ⟨198641, by rfl⟩ : syracuseStep 264855 = 397283) B397283
theorem B3050135 : Blo 263822 3050135 := bstep (se 1 (by rfl) ⟨2287601, by rfl⟩ : syracuseStep 3050135 = 4575203) B4575203
theorem B297643 : Blo 263822 297643 := bstep (se 1 (by rfl) ⟨223232, by rfl⟩ : syracuseStep 297643 = 446465) B446465
theorem B264875 : Blo 263822 264875 := bstep (se 1 (by rfl) ⟨198656, by rfl⟩ : syracuseStep 264875 = 397313) B397313
theorem B264887 : Blo 263822 264887 := bstep (se 1 (by rfl) ⟨198665, by rfl⟩ : syracuseStep 264887 = 397331) B397331
theorem B264907 : Blo 263822 264907 := bstep (se 1 (by rfl) ⟨198680, by rfl⟩ : syracuseStep 264907 = 397361) B397361
theorem B264919 : Blo 263822 264919 := bstep (se 1 (by rfl) ⟨198689, by rfl⟩ : syracuseStep 264919 = 397379) B397379
theorem B395993 : Blo 263822 395993 := bstep (se 2 (by rfl) ⟨148497, by rfl⟩ : syracuseStep 395993 = 296995) B296995
theorem B264939 : Blo 263822 264939 := bstep (se 1 (by rfl) ⟨198704, by rfl⟩ : syracuseStep 264939 = 397409) B397409
theorem B264951 : Blo 263822 264951 := bstep (se 1 (by rfl) ⟨198713, by rfl⟩ : syracuseStep 264951 = 397427) B397427
theorem B264971 : Blo 263822 264971 := bstep (se 1 (by rfl) ⟨198728, by rfl⟩ : syracuseStep 264971 = 397457) B397457
theorem B297751 : Blo 263822 297751 := bstep (se 1 (by rfl) ⟨223313, by rfl⟩ : syracuseStep 297751 = 446627) B446627
theorem B264983 : Blo 263822 264983 := bstep (se 1 (by rfl) ⟨198737, by rfl⟩ : syracuseStep 264983 = 397475) B397475
theorem B265003 : Blo 263822 265003 := bstep (se 1 (by rfl) ⟨198752, by rfl⟩ : syracuseStep 265003 = 397505) B397505
theorem B265015 : Blo 263822 265015 := bstep (se 1 (by rfl) ⟨198761, by rfl⟩ : syracuseStep 265015 = 397523) B397523
theorem B1477441 : Blo 263822 1477441 := bstep (se 2 (by rfl) ⟨554040, by rfl⟩ : syracuseStep 1477441 = 1108081) B1108081
theorem B396107 : Blo 263822 396107 := bstep (se 1 (by rfl) ⟨297080, by rfl⟩ : syracuseStep 396107 = 594161) B594161
theorem B265035 : Blo 263822 265035 := bstep (se 1 (by rfl) ⟨198776, by rfl⟩ : syracuseStep 265035 = 397553) B397553
theorem B396119 : Blo 263822 396119 := bstep (se 1 (by rfl) ⟨297089, by rfl⟩ : syracuseStep 396119 = 594179) B594179
theorem B265047 : Blo 263822 265047 := bstep (se 1 (by rfl) ⟨198785, by rfl⟩ : syracuseStep 265047 = 397571) B397571
theorem B265067 : Blo 263822 265067 := bstep (se 1 (by rfl) ⟨198800, by rfl⟩ : syracuseStep 265067 = 397601) B397601
theorem B265079 : Blo 263822 265079 := bstep (se 1 (by rfl) ⟨198809, by rfl⟩ : syracuseStep 265079 = 397619) B397619
theorem B265099 : Blo 263822 265099 := bstep (se 1 (by rfl) ⟨198824, by rfl⟩ : syracuseStep 265099 = 397649) B397649
theorem B265111 : Blo 263822 265111 := bstep (se 1 (by rfl) ⟨198833, by rfl⟩ : syracuseStep 265111 = 397667) B397667
theorem B396185 : Blo 263822 396185 := bstep (se 2 (by rfl) ⟨148569, by rfl⟩ : syracuseStep 396185 = 297139) B297139
theorem B265131 : Blo 263822 265131 := bstep (se 1 (by rfl) ⟨198848, by rfl⟩ : syracuseStep 265131 = 397697) B397697
theorem B265143 : Blo 263822 265143 := bstep (se 1 (by rfl) ⟨198857, by rfl⟩ : syracuseStep 265143 = 397715) B397715
theorem B297931 : Blo 263822 297931 := bstep (se 1 (by rfl) ⟨223448, by rfl⟩ : syracuseStep 297931 = 446897) B446897
theorem B265163 : Blo 263822 265163 := bstep (se 1 (by rfl) ⟨198872, by rfl⟩ : syracuseStep 265163 = 397745) B397745
theorem B265175 : Blo 263822 265175 := bstep (se 1 (by rfl) ⟨198881, by rfl⟩ : syracuseStep 265175 = 397763) B397763
theorem B265195 : Blo 263822 265195 := bstep (se 1 (by rfl) ⟨198896, by rfl⟩ : syracuseStep 265195 = 397793) B397793
theorem B265207 : Blo 263822 265207 := bstep (se 1 (by rfl) ⟨198905, by rfl⟩ : syracuseStep 265207 = 397811) B397811
theorem B396299 : Blo 263822 396299 := bstep (se 1 (by rfl) ⟨297224, by rfl⟩ : syracuseStep 396299 = 594449) B594449
theorem B265227 : Blo 263822 265227 := bstep (se 1 (by rfl) ⟨198920, by rfl⟩ : syracuseStep 265227 = 397841) B397841
theorem B396311 : Blo 263822 396311 := bstep (se 1 (by rfl) ⟨297233, by rfl⟩ : syracuseStep 396311 = 594467) B594467
theorem B265239 : Blo 263822 265239 := bstep (se 1 (by rfl) ⟨198929, by rfl⟩ : syracuseStep 265239 = 397859) B397859
theorem B265259 : Blo 263822 265259 := bstep (se 1 (by rfl) ⟨198944, by rfl⟩ : syracuseStep 265259 = 397889) B397889
theorem B298039 : Blo 263822 298039 := bstep (se 1 (by rfl) ⟨223529, by rfl⟩ : syracuseStep 298039 = 447059) B447059
theorem B265271 : Blo 263822 265271 := bstep (se 1 (by rfl) ⟨198953, by rfl⟩ : syracuseStep 265271 = 397907) B397907
theorem B265291 : Blo 263822 265291 := bstep (se 1 (by rfl) ⟨198968, by rfl⟩ : syracuseStep 265291 = 397937) B397937
theorem B265303 : Blo 263822 265303 := bstep (se 1 (by rfl) ⟨198977, by rfl⟩ : syracuseStep 265303 = 397955) B397955
theorem B396377 : Blo 263822 396377 := bstep (se 2 (by rfl) ⟨148641, by rfl⟩ : syracuseStep 396377 = 297283) B297283
theorem B265323 : Blo 263822 265323 := bstep (se 1 (by rfl) ⟨198992, by rfl⟩ : syracuseStep 265323 = 397985) B397985
theorem B265335 : Blo 263822 265335 := bstep (se 1 (by rfl) ⟨199001, by rfl⟩ : syracuseStep 265335 = 398003) B398003
theorem B265355 : Blo 263822 265355 := bstep (se 1 (by rfl) ⟨199016, by rfl⟩ : syracuseStep 265355 = 398033) B398033
theorem B265367 : Blo 263822 265367 := bstep (se 1 (by rfl) ⟨199025, by rfl⟩ : syracuseStep 265367 = 398051) B398051
theorem B265387 : Blo 263822 265387 := bstep (se 1 (by rfl) ⟨199040, by rfl⟩ : syracuseStep 265387 = 398081) B398081
theorem B265399 : Blo 263822 265399 := bstep (se 1 (by rfl) ⟨199049, by rfl⟩ : syracuseStep 265399 = 398099) B398099
theorem B396491 : Blo 263822 396491 := bstep (se 1 (by rfl) ⟨297368, by rfl⟩ : syracuseStep 396491 = 594737) B594737
theorem B265419 : Blo 263822 265419 := bstep (se 1 (by rfl) ⟨199064, by rfl⟩ : syracuseStep 265419 = 398129) B398129
theorem B396503 : Blo 263822 396503 := bstep (se 1 (by rfl) ⟨297377, by rfl⟩ : syracuseStep 396503 = 594755) B594755
theorem B265431 : Blo 263822 265431 := bstep (se 1 (by rfl) ⟨199073, by rfl⟩ : syracuseStep 265431 = 398147) B398147
theorem B298219 : Blo 263822 298219 := bstep (se 1 (by rfl) ⟨223664, by rfl⟩ : syracuseStep 298219 = 447329) B447329
theorem B265451 : Blo 263822 265451 := bstep (se 1 (by rfl) ⟨199088, by rfl⟩ : syracuseStep 265451 = 398177) B398177
theorem B265463 : Blo 263822 265463 := bstep (se 1 (by rfl) ⟨199097, by rfl⟩ : syracuseStep 265463 = 398195) B398195
theorem B265483 : Blo 263822 265483 := bstep (se 1 (by rfl) ⟨199112, by rfl⟩ : syracuseStep 265483 = 398225) B398225
theorem B265495 : Blo 263822 265495 := bstep (se 1 (by rfl) ⟨199121, by rfl⟩ : syracuseStep 265495 = 398243) B398243
theorem B396569 : Blo 263822 396569 := bstep (se 2 (by rfl) ⟨148713, by rfl⟩ : syracuseStep 396569 = 297427) B297427
theorem B265515 : Blo 263822 265515 := bstep (se 1 (by rfl) ⟨199136, by rfl⟩ : syracuseStep 265515 = 398273) B398273
theorem B265527 : Blo 263822 265527 := bstep (se 1 (by rfl) ⟨199145, by rfl⟩ : syracuseStep 265527 = 398291) B398291
theorem B265547 : Blo 263822 265547 := bstep (se 1 (by rfl) ⟨199160, by rfl⟩ : syracuseStep 265547 = 398321) B398321
theorem B298327 : Blo 263822 298327 := bstep (se 1 (by rfl) ⟨223745, by rfl⟩ : syracuseStep 298327 = 447491) B447491
theorem B265559 : Blo 263822 265559 := bstep (se 1 (by rfl) ⟨199169, by rfl⟩ : syracuseStep 265559 = 398339) B398339
theorem B265579 : Blo 263822 265579 := bstep (se 1 (by rfl) ⟨199184, by rfl⟩ : syracuseStep 265579 = 398369) B398369
theorem B265591 : Blo 263822 265591 := bstep (se 1 (by rfl) ⟨199193, by rfl⟩ : syracuseStep 265591 = 398387) B398387
theorem B396683 : Blo 263822 396683 := bstep (se 1 (by rfl) ⟨297512, by rfl⟩ : syracuseStep 396683 = 595025) B595025
theorem B265611 : Blo 263822 265611 := bstep (se 1 (by rfl) ⟨199208, by rfl⟩ : syracuseStep 265611 = 398417) B398417
theorem B396695 : Blo 263822 396695 := bstep (se 1 (by rfl) ⟨297521, by rfl⟩ : syracuseStep 396695 = 595043) B595043
theorem B265623 : Blo 263822 265623 := bstep (se 1 (by rfl) ⟨199217, by rfl⟩ : syracuseStep 265623 = 398435) B398435
theorem B265643 : Blo 263822 265643 := bstep (se 1 (by rfl) ⟨199232, by rfl⟩ : syracuseStep 265643 = 398465) B398465
theorem B265655 : Blo 263822 265655 := bstep (se 1 (by rfl) ⟨199241, by rfl⟩ : syracuseStep 265655 = 398483) B398483
theorem B691649 : Blo 263822 691649 := bstep (se 2 (by rfl) ⟨259368, by rfl⟩ : syracuseStep 691649 = 518737) B518737
theorem B265675 : Blo 263822 265675 := bstep (se 1 (by rfl) ⟨199256, by rfl⟩ : syracuseStep 265675 = 398513) B398513
theorem B265687 : Blo 263822 265687 := bstep (se 1 (by rfl) ⟨199265, by rfl⟩ : syracuseStep 265687 = 398531) B398531
theorem B396761 : Blo 263822 396761 := bstep (se 2 (by rfl) ⟨148785, by rfl⟩ : syracuseStep 396761 = 297571) B297571
theorem B265707 : Blo 263822 265707 := bstep (se 1 (by rfl) ⟨199280, by rfl⟩ : syracuseStep 265707 = 398561) B398561
theorem B265719 : Blo 263822 265719 := bstep (se 1 (by rfl) ⟨199289, by rfl⟩ : syracuseStep 265719 = 398579) B398579
theorem B298507 : Blo 263822 298507 := bstep (se 1 (by rfl) ⟨223880, by rfl⟩ : syracuseStep 298507 = 447761) B447761
theorem B265739 : Blo 263822 265739 := bstep (se 1 (by rfl) ⟨199304, by rfl⟩ : syracuseStep 265739 = 398609) B398609
theorem B1740305 : Blo 263822 1740305 := bstep (se 2 (by rfl) ⟨652614, by rfl⟩ : syracuseStep 1740305 = 1305229) B1305229
theorem B265751 : Blo 263822 265751 := bstep (se 1 (by rfl) ⟨199313, by rfl⟩ : syracuseStep 265751 = 398627) B398627
theorem B265771 : Blo 263822 265771 := bstep (se 1 (by rfl) ⟨199328, by rfl⟩ : syracuseStep 265771 = 398657) B398657
theorem B265783 : Blo 263822 265783 := bstep (se 1 (by rfl) ⟨199337, by rfl⟩ : syracuseStep 265783 = 398675) B398675
theorem B396875 : Blo 263822 396875 := bstep (se 1 (by rfl) ⟨297656, by rfl⟩ : syracuseStep 396875 = 595313) B595313
theorem B265803 : Blo 263822 265803 := bstep (se 1 (by rfl) ⟨199352, by rfl⟩ : syracuseStep 265803 = 398705) B398705
theorem B396887 : Blo 263822 396887 := bstep (se 1 (by rfl) ⟨297665, by rfl⟩ : syracuseStep 396887 = 595331) B595331
theorem B265815 : Blo 263822 265815 := bstep (se 1 (by rfl) ⟨199361, by rfl⟩ : syracuseStep 265815 = 398723) B398723
theorem B265835 : Blo 263822 265835 := bstep (se 1 (by rfl) ⟨199376, by rfl⟩ : syracuseStep 265835 = 398753) B398753
theorem B298615 : Blo 263822 298615 := bstep (se 1 (by rfl) ⟨223961, by rfl⟩ : syracuseStep 298615 = 447923) B447923
theorem B265847 : Blo 263822 265847 := bstep (se 1 (by rfl) ⟨199385, by rfl⟩ : syracuseStep 265847 = 398771) B398771
theorem B265867 : Blo 263822 265867 := bstep (se 1 (by rfl) ⟨199400, by rfl⟩ : syracuseStep 265867 = 398801) B398801
theorem B265879 : Blo 263822 265879 := bstep (se 1 (by rfl) ⟨199409, by rfl⟩ : syracuseStep 265879 = 398819) B398819
theorem B396953 : Blo 263822 396953 := bstep (se 2 (by rfl) ⟨148857, by rfl⟩ : syracuseStep 396953 = 297715) B297715
theorem B265899 : Blo 263822 265899 := bstep (se 1 (by rfl) ⟨199424, by rfl⟩ : syracuseStep 265899 = 398849) B398849
theorem B265911 : Blo 263822 265911 := bstep (se 1 (by rfl) ⟨199433, by rfl⟩ : syracuseStep 265911 = 398867) B398867
theorem B265931 : Blo 263822 265931 := bstep (se 1 (by rfl) ⟨199448, by rfl⟩ : syracuseStep 265931 = 398897) B398897
theorem B265943 : Blo 263822 265943 := bstep (se 1 (by rfl) ⟨199457, by rfl⟩ : syracuseStep 265943 = 398915) B398915
theorem B265963 : Blo 263822 265963 := bstep (se 1 (by rfl) ⟨199472, by rfl⟩ : syracuseStep 265963 = 398945) B398945
theorem B265975 : Blo 263822 265975 := bstep (se 1 (by rfl) ⟨199481, by rfl⟩ : syracuseStep 265975 = 398963) B398963
theorem B593675 : Blo 263822 593675 := bstep (se 1 (by rfl) ⟨445256, by rfl⟩ : syracuseStep 593675 = 890513) B890513
theorem B397067 : Blo 263822 397067 := bstep (se 1 (by rfl) ⟨297800, by rfl⟩ : syracuseStep 397067 = 595601) B595601
theorem B265995 : Blo 263822 265995 := bstep (se 1 (by rfl) ⟨199496, by rfl⟩ : syracuseStep 265995 = 398993) B398993
theorem B1085201 : Blo 263822 1085201 := bstep (se 2 (by rfl) ⟨406950, by rfl⟩ : syracuseStep 1085201 = 813901) B813901
theorem B397079 : Blo 263822 397079 := bstep (se 1 (by rfl) ⟨297809, by rfl⟩ : syracuseStep 397079 = 595619) B595619
theorem B266007 : Blo 263822 266007 := bstep (se 1 (by rfl) ⟨199505, by rfl⟩ : syracuseStep 266007 = 399011) B399011
theorem B298795 : Blo 263822 298795 := bstep (se 1 (by rfl) ⟨224096, by rfl⟩ : syracuseStep 298795 = 448193) B448193
theorem B266027 : Blo 263822 266027 := bstep (se 1 (by rfl) ⟨199520, by rfl⟩ : syracuseStep 266027 = 399041) B399041
theorem B266039 : Blo 263822 266039 := bstep (se 1 (by rfl) ⟨199529, by rfl⟩ : syracuseStep 266039 = 399059) B399059
theorem B593729 : Blo 263822 593729 := bstep (se 2 (by rfl) ⟨222648, by rfl⟩ : syracuseStep 593729 = 445297) B445297
theorem B266059 : Blo 263822 266059 := bstep (se 1 (by rfl) ⟨199544, by rfl⟩ : syracuseStep 266059 = 399089) B399089
theorem B266071 : Blo 263822 266071 := bstep (se 1 (by rfl) ⟨199553, by rfl⟩ : syracuseStep 266071 = 399107) B399107
theorem B397145 : Blo 263822 397145 := bstep (se 2 (by rfl) ⟨148929, by rfl⟩ : syracuseStep 397145 = 297859) B297859
theorem B266091 : Blo 263822 266091 := bstep (se 1 (by rfl) ⟨199568, by rfl⟩ : syracuseStep 266091 = 399137) B399137
theorem B266103 : Blo 263822 266103 := bstep (se 1 (by rfl) ⟨199577, by rfl⟩ : syracuseStep 266103 = 399155) B399155
theorem B266123 : Blo 263822 266123 := bstep (se 1 (by rfl) ⟨199592, by rfl⟩ : syracuseStep 266123 = 399185) B399185
theorem B1085329 : Blo 263822 1085329 := bstep (se 2 (by rfl) ⟨406998, by rfl⟩ : syracuseStep 1085329 = 813997) B813997
theorem B298903 : Blo 263822 298903 := bstep (se 1 (by rfl) ⟨224177, by rfl⟩ : syracuseStep 298903 = 448355) B448355
theorem B266135 : Blo 263822 266135 := bstep (se 1 (by rfl) ⟨199601, by rfl⟩ : syracuseStep 266135 = 399203) B399203
theorem B266155 : Blo 263822 266155 := bstep (se 1 (by rfl) ⟨199616, by rfl⟩ : syracuseStep 266155 = 399233) B399233
theorem B266167 : Blo 263822 266167 := bstep (se 1 (by rfl) ⟨199625, by rfl⟩ : syracuseStep 266167 = 399251) B399251
theorem B397259 : Blo 263822 397259 := bstep (se 1 (by rfl) ⟨297944, by rfl⟩ : syracuseStep 397259 = 595889) B595889
theorem B266187 : Blo 263822 266187 := bstep (se 1 (by rfl) ⟨199640, by rfl⟩ : syracuseStep 266187 = 399281) B399281
theorem B397271 : Blo 263822 397271 := bstep (se 1 (by rfl) ⟨297953, by rfl⟩ : syracuseStep 397271 = 595907) B595907
theorem B266199 : Blo 263822 266199 := bstep (se 1 (by rfl) ⟨199649, by rfl⟩ : syracuseStep 266199 = 399299) B399299
theorem B266219 : Blo 263822 266219 := bstep (se 1 (by rfl) ⟨199664, by rfl⟩ : syracuseStep 266219 = 399329) B399329
theorem B266231 : Blo 263822 266231 := bstep (se 1 (by rfl) ⟨199673, by rfl⟩ : syracuseStep 266231 = 399347) B399347
theorem B266251 : Blo 263822 266251 := bstep (se 1 (by rfl) ⟨199688, by rfl⟩ : syracuseStep 266251 = 399377) B399377
theorem B266263 : Blo 263822 266263 := bstep (se 1 (by rfl) ⟨199697, by rfl⟩ : syracuseStep 266263 = 399395) B399395
theorem B593945 : Blo 263822 593945 := bstep (se 2 (by rfl) ⟨222729, by rfl⟩ : syracuseStep 593945 = 445459) B445459
theorem B397337 : Blo 263822 397337 := bstep (se 2 (by rfl) ⟨149001, by rfl⟩ : syracuseStep 397337 = 298003) B298003
theorem B266283 : Blo 263822 266283 := bstep (se 1 (by rfl) ⟨199712, by rfl⟩ : syracuseStep 266283 = 399425) B399425
theorem B266295 : Blo 263822 266295 := bstep (se 1 (by rfl) ⟨199721, by rfl⟩ : syracuseStep 266295 = 399443) B399443
theorem B299083 : Blo 263822 299083 := bstep (se 1 (by rfl) ⟨224312, by rfl⟩ : syracuseStep 299083 = 448625) B448625
theorem B266315 : Blo 263822 266315 := bstep (se 1 (by rfl) ⟨199736, by rfl⟩ : syracuseStep 266315 = 399473) B399473
theorem B266327 : Blo 263822 266327 := bstep (se 1 (by rfl) ⟨199745, by rfl⟩ : syracuseStep 266327 = 399491) B399491
theorem B1347677 : Blo 263822 1347677 := bstep (se 3 (by rfl) ⟨252689, by rfl⟩ : syracuseStep 1347677 = 505379) B505379
theorem B266347 : Blo 263822 266347 := bstep (se 1 (by rfl) ⟨199760, by rfl⟩ : syracuseStep 266347 = 399521) B399521
theorem B594035 : Blo 263822 594035 := bstep (se 1 (by rfl) ⟨445526, by rfl⟩ : syracuseStep 594035 = 891053) B891053
theorem B266359 : Blo 263822 266359 := bstep (se 1 (by rfl) ⟨199769, by rfl⟩ : syracuseStep 266359 = 399539) B399539
theorem B397451 : Blo 263822 397451 := bstep (se 1 (by rfl) ⟨298088, by rfl⟩ : syracuseStep 397451 = 596177) B596177
theorem B266379 : Blo 263822 266379 := bstep (se 1 (by rfl) ⟨199784, by rfl⟩ : syracuseStep 266379 = 399569) B399569
theorem B594071 : Blo 263822 594071 := bstep (se 1 (by rfl) ⟨445553, by rfl⟩ : syracuseStep 594071 = 891107) B891107
theorem B397463 : Blo 263822 397463 := bstep (se 1 (by rfl) ⟨298097, by rfl⟩ : syracuseStep 397463 = 596195) B596195
theorem B266391 : Blo 263822 266391 := bstep (se 1 (by rfl) ⟨199793, by rfl⟩ : syracuseStep 266391 = 399587) B399587
theorem B266411 : Blo 263822 266411 := bstep (se 1 (by rfl) ⟨199808, by rfl⟩ : syracuseStep 266411 = 399617) B399617
theorem B299191 : Blo 263822 299191 := bstep (se 1 (by rfl) ⟨224393, by rfl⟩ : syracuseStep 299191 = 448787) B448787
theorem B266423 : Blo 263822 266423 := bstep (se 1 (by rfl) ⟨199817, by rfl⟩ : syracuseStep 266423 = 399635) B399635
theorem B266443 : Blo 263822 266443 := bstep (se 1 (by rfl) ⟨199832, by rfl⟩ : syracuseStep 266443 = 399665) B399665
theorem B266455 : Blo 263822 266455 := bstep (se 1 (by rfl) ⟨199841, by rfl⟩ : syracuseStep 266455 = 399683) B399683
theorem B397529 : Blo 263822 397529 := bstep (se 2 (by rfl) ⟨149073, by rfl⟩ : syracuseStep 397529 = 298147) B298147
theorem B266475 : Blo 263822 266475 := bstep (se 1 (by rfl) ⟨199856, by rfl⟩ : syracuseStep 266475 = 399713) B399713
theorem B266487 : Blo 263822 266487 := bstep (se 1 (by rfl) ⟨199865, by rfl⟩ : syracuseStep 266487 = 399731) B399731
theorem B266507 : Blo 263822 266507 := bstep (se 1 (by rfl) ⟨199880, by rfl⟩ : syracuseStep 266507 = 399761) B399761
theorem B266519 : Blo 263822 266519 := bstep (se 1 (by rfl) ⟨199889, by rfl⟩ : syracuseStep 266519 = 399779) B399779
theorem B266539 : Blo 263822 266539 := bstep (se 1 (by rfl) ⟨199904, by rfl⟩ : syracuseStep 266539 = 399809) B399809
theorem B266551 : Blo 263822 266551 := bstep (se 1 (by rfl) ⟨199913, by rfl⟩ : syracuseStep 266551 = 399827) B399827
theorem B594251 : Blo 263822 594251 := bstep (se 1 (by rfl) ⟨445688, by rfl⟩ : syracuseStep 594251 = 891377) B891377
theorem B397643 : Blo 263822 397643 := bstep (se 1 (by rfl) ⟨298232, by rfl⟩ : syracuseStep 397643 = 596465) B596465
theorem B266571 : Blo 263822 266571 := bstep (se 1 (by rfl) ⟨199928, by rfl⟩ : syracuseStep 266571 = 399857) B399857
theorem B397655 : Blo 263822 397655 := bstep (se 1 (by rfl) ⟨298241, by rfl⟩ : syracuseStep 397655 = 596483) B596483
theorem B266583 : Blo 263822 266583 := bstep (se 1 (by rfl) ⟨199937, by rfl⟩ : syracuseStep 266583 = 399875) B399875
theorem B299371 : Blo 263822 299371 := bstep (se 1 (by rfl) ⟨224528, by rfl⟩ : syracuseStep 299371 = 449057) B449057
theorem B266603 : Blo 263822 266603 := bstep (se 1 (by rfl) ⟨199952, by rfl⟩ : syracuseStep 266603 = 399905) B399905
theorem B266615 : Blo 263822 266615 := bstep (se 1 (by rfl) ⟨199961, by rfl⟩ : syracuseStep 266615 = 399923) B399923
theorem B594305 : Blo 263822 594305 := bstep (se 2 (by rfl) ⟨222864, by rfl⟩ : syracuseStep 594305 = 445729) B445729
theorem B266635 : Blo 263822 266635 := bstep (se 1 (by rfl) ⟨199976, by rfl⟩ : syracuseStep 266635 = 399953) B399953
theorem B266647 : Blo 263822 266647 := bstep (se 1 (by rfl) ⟨199985, by rfl⟩ : syracuseStep 266647 = 399971) B399971
theorem B397721 : Blo 263822 397721 := bstep (se 2 (by rfl) ⟨149145, by rfl⟩ : syracuseStep 397721 = 298291) B298291
theorem B266667 : Blo 263822 266667 := bstep (se 1 (by rfl) ⟨200000, by rfl⟩ : syracuseStep 266667 = 400001) B400001
theorem B266679 : Blo 263822 266679 := bstep (se 1 (by rfl) ⟨200009, by rfl⟩ : syracuseStep 266679 = 400019) B400019
theorem B266699 : Blo 263822 266699 := bstep (se 1 (by rfl) ⟨200024, by rfl⟩ : syracuseStep 266699 = 400049) B400049
theorem B299479 : Blo 263822 299479 := bstep (se 1 (by rfl) ⟨224609, by rfl⟩ : syracuseStep 299479 = 449219) B449219
theorem B266711 : Blo 263822 266711 := bstep (se 1 (by rfl) ⟨200033, by rfl⟩ : syracuseStep 266711 = 400067) B400067
theorem B266731 : Blo 263822 266731 := bstep (se 1 (by rfl) ⟨200048, by rfl⟩ : syracuseStep 266731 = 400097) B400097
theorem B266743 : Blo 263822 266743 := bstep (se 1 (by rfl) ⟨200057, by rfl⟩ : syracuseStep 266743 = 400115) B400115
theorem B397835 : Blo 263822 397835 := bstep (se 1 (by rfl) ⟨298376, by rfl⟩ : syracuseStep 397835 = 596753) B596753
theorem B266763 : Blo 263822 266763 := bstep (se 1 (by rfl) ⟨200072, by rfl⟩ : syracuseStep 266763 = 400145) B400145
theorem B397847 : Blo 263822 397847 := bstep (se 1 (by rfl) ⟨298385, by rfl⟩ : syracuseStep 397847 = 596771) B596771
theorem B266775 : Blo 263822 266775 := bstep (se 1 (by rfl) ⟨200081, by rfl⟩ : syracuseStep 266775 = 400163) B400163
theorem B266795 : Blo 263822 266795 := bstep (se 1 (by rfl) ⟨200096, by rfl⟩ : syracuseStep 266795 = 400193) B400193
theorem B266807 : Blo 263822 266807 := bstep (se 1 (by rfl) ⟨200105, by rfl⟩ : syracuseStep 266807 = 400211) B400211
theorem B1282625 : Blo 263822 1282625 := bstep (se 2 (by rfl) ⟨480984, by rfl⟩ : syracuseStep 1282625 = 961969) B961969
theorem B266827 : Blo 263822 266827 := bstep (se 1 (by rfl) ⟨200120, by rfl⟩ : syracuseStep 266827 = 400241) B400241
theorem B266839 : Blo 263822 266839 := bstep (se 1 (by rfl) ⟨200129, by rfl⟩ : syracuseStep 266839 = 400259) B400259
theorem B594521 : Blo 263822 594521 := bstep (se 2 (by rfl) ⟨222945, by rfl⟩ : syracuseStep 594521 = 445891) B445891
theorem B397913 : Blo 263822 397913 := bstep (se 2 (by rfl) ⟨149217, by rfl⟩ : syracuseStep 397913 = 298435) B298435
theorem B1151581 : Blo 263822 1151581 := bstep (se 3 (by rfl) ⟨215921, by rfl⟩ : syracuseStep 1151581 = 431843) B431843
theorem B266859 : Blo 263822 266859 := bstep (se 1 (by rfl) ⟨200144, by rfl⟩ : syracuseStep 266859 = 400289) B400289
theorem B266871 : Blo 263822 266871 := bstep (se 1 (by rfl) ⟨200153, by rfl⟩ : syracuseStep 266871 = 400307) B400307
theorem B299659 : Blo 263822 299659 := bstep (se 1 (by rfl) ⟨224744, by rfl⟩ : syracuseStep 299659 = 449489) B449489
theorem B266891 : Blo 263822 266891 := bstep (se 1 (by rfl) ⟨200168, by rfl⟩ : syracuseStep 266891 = 400337) B400337
theorem B758423 : Blo 263822 758423 := bstep (se 1 (by rfl) ⟨568817, by rfl⟩ : syracuseStep 758423 = 1137635) B1137635
theorem B266903 : Blo 263822 266903 := bstep (se 1 (by rfl) ⟨200177, by rfl⟩ : syracuseStep 266903 = 400355) B400355
theorem B266923 : Blo 263822 266923 := bstep (se 1 (by rfl) ⟨200192, by rfl⟩ : syracuseStep 266923 = 400385) B400385
theorem B594611 : Blo 263822 594611 := bstep (se 1 (by rfl) ⟨445958, by rfl⟩ : syracuseStep 594611 = 891917) B891917
theorem B266935 : Blo 263822 266935 := bstep (se 1 (by rfl) ⟨200201, by rfl⟩ : syracuseStep 266935 = 400403) B400403
theorem B398027 : Blo 263822 398027 := bstep (se 1 (by rfl) ⟨298520, by rfl⟩ : syracuseStep 398027 = 597041) B597041
theorem B266955 : Blo 263822 266955 := bstep (se 1 (by rfl) ⟨200216, by rfl⟩ : syracuseStep 266955 = 400433) B400433
theorem B594647 : Blo 263822 594647 := bstep (se 1 (by rfl) ⟨445985, by rfl⟩ : syracuseStep 594647 = 891971) B891971
theorem B398039 : Blo 263822 398039 := bstep (se 1 (by rfl) ⟨298529, by rfl⟩ : syracuseStep 398039 = 597059) B597059
theorem B266967 : Blo 263822 266967 := bstep (se 1 (by rfl) ⟨200225, by rfl⟩ : syracuseStep 266967 = 400451) B400451
theorem B266987 : Blo 263822 266987 := bstep (se 1 (by rfl) ⟨200240, by rfl⟩ : syracuseStep 266987 = 400481) B400481
theorem B299767 : Blo 263822 299767 := bstep (se 1 (by rfl) ⟨224825, by rfl⟩ : syracuseStep 299767 = 449651) B449651
theorem B266999 : Blo 263822 266999 := bstep (se 1 (by rfl) ⟨200249, by rfl⟩ : syracuseStep 266999 = 400499) B400499
theorem B267019 : Blo 263822 267019 := bstep (se 1 (by rfl) ⟨200264, by rfl⟩ : syracuseStep 267019 = 400529) B400529
theorem B267031 : Blo 263822 267031 := bstep (se 1 (by rfl) ⟨200273, by rfl⟩ : syracuseStep 267031 = 400547) B400547
theorem B398105 : Blo 263822 398105 := bstep (se 2 (by rfl) ⟨149289, by rfl⟩ : syracuseStep 398105 = 298579) B298579
theorem B267051 : Blo 263822 267051 := bstep (se 1 (by rfl) ⟨200288, by rfl⟩ : syracuseStep 267051 = 400577) B400577
theorem B267063 : Blo 263822 267063 := bstep (se 1 (by rfl) ⟨200297, by rfl⟩ : syracuseStep 267063 = 400595) B400595
theorem B2003777 : Blo 263822 2003777 := bstep (se 2 (by rfl) ⟨751416, by rfl⟩ : syracuseStep 2003777 = 1502833) B1502833
theorem B267083 : Blo 263822 267083 := bstep (se 1 (by rfl) ⟨200312, by rfl⟩ : syracuseStep 267083 = 400625) B400625
theorem B267095 : Blo 263822 267095 := bstep (se 1 (by rfl) ⟨200321, by rfl⟩ : syracuseStep 267095 = 400643) B400643
theorem B267115 : Blo 263822 267115 := bstep (se 1 (by rfl) ⟨200336, by rfl⟩ : syracuseStep 267115 = 400673) B400673
theorem B267127 : Blo 263822 267127 := bstep (se 1 (by rfl) ⟨200345, by rfl⟩ : syracuseStep 267127 = 400691) B400691
theorem B594827 : Blo 263822 594827 := bstep (se 1 (by rfl) ⟨446120, by rfl⟩ : syracuseStep 594827 = 892241) B892241
theorem B398219 : Blo 263822 398219 := bstep (se 1 (by rfl) ⟨298664, by rfl⟩ : syracuseStep 398219 = 597329) B597329
theorem B267147 : Blo 263822 267147 := bstep (se 1 (by rfl) ⟨200360, by rfl⟩ : syracuseStep 267147 = 400721) B400721
theorem B398231 : Blo 263822 398231 := bstep (se 1 (by rfl) ⟨298673, by rfl⟩ : syracuseStep 398231 = 597347) B597347
theorem B267159 : Blo 263822 267159 := bstep (se 1 (by rfl) ⟨200369, by rfl⟩ : syracuseStep 267159 = 400739) B400739
theorem B299947 : Blo 263822 299947 := bstep (se 1 (by rfl) ⟨224960, by rfl⟩ : syracuseStep 299947 = 449921) B449921
theorem B267179 : Blo 263822 267179 := bstep (se 1 (by rfl) ⟨200384, by rfl⟩ : syracuseStep 267179 = 400769) B400769
theorem B955309 : Blo 263822 955309 := bstep (se 3 (by rfl) ⟨179120, by rfl⟩ : syracuseStep 955309 = 358241) B358241
theorem B267191 : Blo 263822 267191 := bstep (se 1 (by rfl) ⟨200393, by rfl⟩ : syracuseStep 267191 = 400787) B400787
theorem B594881 : Blo 263822 594881 := bstep (se 2 (by rfl) ⟨223080, by rfl⟩ : syracuseStep 594881 = 446161) B446161
theorem B267211 : Blo 263822 267211 := bstep (se 1 (by rfl) ⟨200408, by rfl⟩ : syracuseStep 267211 = 400817) B400817
theorem B267223 : Blo 263822 267223 := bstep (se 1 (by rfl) ⟨200417, by rfl⟩ : syracuseStep 267223 = 400835) B400835
theorem B398297 : Blo 263822 398297 := bstep (se 2 (by rfl) ⟨149361, by rfl⟩ : syracuseStep 398297 = 298723) B298723
theorem B2200537 : Blo 263822 2200537 := bstep (se 2 (by rfl) ⟨825201, by rfl⟩ : syracuseStep 2200537 = 1650403) B1650403
theorem B267243 : Blo 263822 267243 := bstep (se 1 (by rfl) ⟨200432, by rfl⟩ : syracuseStep 267243 = 400865) B400865
theorem B267255 : Blo 263822 267255 := bstep (se 1 (by rfl) ⟨200441, by rfl⟩ : syracuseStep 267255 = 400883) B400883
theorem B267275 : Blo 263822 267275 := bstep (se 1 (by rfl) ⟨200456, by rfl⟩ : syracuseStep 267275 = 400913) B400913
theorem B300055 : Blo 263822 300055 := bstep (se 1 (by rfl) ⟨225041, by rfl⟩ : syracuseStep 300055 = 450083) B450083
theorem B267287 : Blo 263822 267287 := bstep (se 1 (by rfl) ⟨200465, by rfl⟩ : syracuseStep 267287 = 400931) B400931
theorem B267307 : Blo 263822 267307 := bstep (se 1 (by rfl) ⟨200480, by rfl⟩ : syracuseStep 267307 = 400961) B400961
theorem B267319 : Blo 263822 267319 := bstep (se 1 (by rfl) ⟨200489, by rfl⟩ : syracuseStep 267319 = 400979) B400979
theorem B398411 : Blo 263822 398411 := bstep (se 1 (by rfl) ⟨298808, by rfl⟩ : syracuseStep 398411 = 597617) B597617
theorem B267339 : Blo 263822 267339 := bstep (se 1 (by rfl) ⟨200504, by rfl⟩ : syracuseStep 267339 = 401009) B401009
theorem B398423 : Blo 263822 398423 := bstep (se 1 (by rfl) ⟨298817, by rfl⟩ : syracuseStep 398423 = 597635) B597635
theorem B267351 : Blo 263822 267351 := bstep (se 1 (by rfl) ⟨200513, by rfl⟩ : syracuseStep 267351 = 401027) B401027
theorem B267371 : Blo 263822 267371 := bstep (se 1 (by rfl) ⟨200528, by rfl⟩ : syracuseStep 267371 = 401057) B401057
theorem B267383 : Blo 263822 267383 := bstep (se 1 (by rfl) ⟨200537, by rfl⟩ : syracuseStep 267383 = 401075) B401075
theorem B267403 : Blo 263822 267403 := bstep (se 1 (by rfl) ⟨200552, by rfl⟩ : syracuseStep 267403 = 401105) B401105
theorem B4854935 : Blo 263822 4854935 := bstep (se 1 (by rfl) ⟨3641201, by rfl⟩ : syracuseStep 4854935 = 7282403) B7282403
theorem B267415 : Blo 263822 267415 := bstep (se 1 (by rfl) ⟨200561, by rfl⟩ : syracuseStep 267415 = 401123) B401123
theorem B595097 : Blo 263822 595097 := bstep (se 2 (by rfl) ⟨223161, by rfl⟩ : syracuseStep 595097 = 446323) B446323
theorem B398489 : Blo 263822 398489 := bstep (se 2 (by rfl) ⟨149433, by rfl⟩ : syracuseStep 398489 = 298867) B298867
theorem B267435 : Blo 263822 267435 := bstep (se 1 (by rfl) ⟨200576, by rfl⟩ : syracuseStep 267435 = 401153) B401153
theorem B267447 : Blo 263822 267447 := bstep (se 1 (by rfl) ⟨200585, by rfl⟩ : syracuseStep 267447 = 401171) B401171
theorem B300235 : Blo 263822 300235 := bstep (se 1 (by rfl) ⟨225176, by rfl⟩ : syracuseStep 300235 = 450353) B450353
theorem B267467 : Blo 263822 267467 := bstep (se 1 (by rfl) ⟨200600, by rfl⟩ : syracuseStep 267467 = 401201) B401201
theorem B267479 : Blo 263822 267479 := bstep (se 1 (by rfl) ⟨200609, by rfl⟩ : syracuseStep 267479 = 401219) B401219
theorem B267499 : Blo 263822 267499 := bstep (se 1 (by rfl) ⟨200624, by rfl⟩ : syracuseStep 267499 = 401249) B401249
theorem B595187 : Blo 263822 595187 := bstep (se 1 (by rfl) ⟨446390, by rfl⟩ : syracuseStep 595187 = 892781) B892781
theorem B267511 : Blo 263822 267511 := bstep (se 1 (by rfl) ⟨200633, by rfl⟩ : syracuseStep 267511 = 401267) B401267
theorem B398603 : Blo 263822 398603 := bstep (se 1 (by rfl) ⟨298952, by rfl⟩ : syracuseStep 398603 = 597905) B597905
theorem B267531 : Blo 263822 267531 := bstep (se 1 (by rfl) ⟨200648, by rfl⟩ : syracuseStep 267531 = 401297) B401297
theorem B595223 : Blo 263822 595223 := bstep (se 1 (by rfl) ⟨446417, by rfl⟩ : syracuseStep 595223 = 892835) B892835
theorem B398615 : Blo 263822 398615 := bstep (se 1 (by rfl) ⟨298961, by rfl⟩ : syracuseStep 398615 = 597923) B597923
theorem B267543 : Blo 263822 267543 := bstep (se 1 (by rfl) ⟨200657, by rfl⟩ : syracuseStep 267543 = 401315) B401315
theorem B267563 : Blo 263822 267563 := bstep (se 1 (by rfl) ⟨200672, by rfl⟩ : syracuseStep 267563 = 401345) B401345
theorem B300343 : Blo 263822 300343 := bstep (se 1 (by rfl) ⟨225257, by rfl⟩ : syracuseStep 300343 = 450515) B450515
theorem B267575 : Blo 263822 267575 := bstep (se 1 (by rfl) ⟨200681, by rfl⟩ : syracuseStep 267575 = 401363) B401363
theorem B267595 : Blo 263822 267595 := bstep (se 1 (by rfl) ⟨200696, by rfl⟩ : syracuseStep 267595 = 401393) B401393
theorem B267607 : Blo 263822 267607 := bstep (se 1 (by rfl) ⟨200705, by rfl⟩ : syracuseStep 267607 = 401411) B401411
theorem B398681 : Blo 263822 398681 := bstep (se 2 (by rfl) ⟨149505, by rfl⟩ : syracuseStep 398681 = 299011) B299011
theorem B267627 : Blo 263822 267627 := bstep (se 1 (by rfl) ⟨200720, by rfl⟩ : syracuseStep 267627 = 401441) B401441
theorem B267639 : Blo 263822 267639 := bstep (se 1 (by rfl) ⟨200729, by rfl⟩ : syracuseStep 267639 = 401459) B401459
theorem B267659 : Blo 263822 267659 := bstep (se 1 (by rfl) ⟨200744, by rfl⟩ : syracuseStep 267659 = 401489) B401489
theorem B267671 : Blo 263822 267671 := bstep (se 1 (by rfl) ⟨200753, by rfl⟩ : syracuseStep 267671 = 401507) B401507
theorem B267691 : Blo 263822 267691 := bstep (se 1 (by rfl) ⟨200768, by rfl⟩ : syracuseStep 267691 = 401537) B401537
theorem B267703 : Blo 263822 267703 := bstep (se 1 (by rfl) ⟨200777, by rfl⟩ : syracuseStep 267703 = 401555) B401555
theorem B595403 : Blo 263822 595403 := bstep (se 1 (by rfl) ⟨446552, by rfl⟩ : syracuseStep 595403 = 893105) B893105
theorem B398795 : Blo 263822 398795 := bstep (se 1 (by rfl) ⟨299096, by rfl⟩ : syracuseStep 398795 = 598193) B598193
theorem B267723 : Blo 263822 267723 := bstep (se 1 (by rfl) ⟨200792, by rfl⟩ : syracuseStep 267723 = 401585) B401585
theorem B398807 : Blo 263822 398807 := bstep (se 1 (by rfl) ⟨299105, by rfl⟩ : syracuseStep 398807 = 598211) B598211
theorem B267735 : Blo 263822 267735 := bstep (se 1 (by rfl) ⟨200801, by rfl⟩ : syracuseStep 267735 = 401603) B401603
theorem B300523 : Blo 263822 300523 := bstep (se 1 (by rfl) ⟨225392, by rfl⟩ : syracuseStep 300523 = 450785) B450785
theorem B267755 : Blo 263822 267755 := bstep (se 1 (by rfl) ⟨200816, by rfl⟩ : syracuseStep 267755 = 401633) B401633
theorem B267767 : Blo 263822 267767 := bstep (se 1 (by rfl) ⟨200825, by rfl⟩ : syracuseStep 267767 = 401651) B401651
theorem B595457 : Blo 263822 595457 := bstep (se 2 (by rfl) ⟨223296, by rfl⟩ : syracuseStep 595457 = 446593) B446593
theorem B267787 : Blo 263822 267787 := bstep (se 1 (by rfl) ⟨200840, by rfl⟩ : syracuseStep 267787 = 401681) B401681
theorem B267799 : Blo 263822 267799 := bstep (se 1 (by rfl) ⟨200849, by rfl⟩ : syracuseStep 267799 = 401699) B401699
theorem B398873 : Blo 263822 398873 := bstep (se 2 (by rfl) ⟨149577, by rfl⟩ : syracuseStep 398873 = 299155) B299155
theorem B2299427 : Blo 263822 2299427 := bstep (se 1 (by rfl) ⟨1724570, by rfl⟩ : syracuseStep 2299427 = 3449141) B3449141
theorem B267819 : Blo 263822 267819 := bstep (se 1 (by rfl) ⟨200864, by rfl⟩ : syracuseStep 267819 = 401729) B401729
theorem B300631 : Blo 263822 300631 := bstep (se 1 (by rfl) ⟨225473, by rfl⟩ : syracuseStep 300631 = 450947) B450947
theorem B398987 : Blo 263822 398987 := bstep (se 1 (by rfl) ⟨299240, by rfl⟩ : syracuseStep 398987 = 598481) B598481
theorem B398999 : Blo 263822 398999 := bstep (se 1 (by rfl) ⟨299249, by rfl⟩ : syracuseStep 398999 = 598499) B598499
theorem B595673 : Blo 263822 595673 := bstep (se 2 (by rfl) ⟨223377, by rfl⟩ : syracuseStep 595673 = 446755) B446755
theorem B399065 : Blo 263822 399065 := bstep (se 2 (by rfl) ⟨149649, by rfl⟩ : syracuseStep 399065 = 299299) B299299
theorem B300811 : Blo 263822 300811 := bstep (se 1 (by rfl) ⟨225608, by rfl⟩ : syracuseStep 300811 = 451217) B451217
theorem B2037521 : Blo 263822 2037521 := bstep (se 2 (by rfl) ⟨764070, by rfl⟩ : syracuseStep 2037521 = 1528141) B1528141
theorem B890675 : Blo 263822 890675 := bstep (se 1 (by rfl) ⟨668006, by rfl⟩ : syracuseStep 890675 = 1336013) B1336013
theorem B595763 : Blo 263822 595763 := bstep (se 1 (by rfl) ⟨446822, by rfl⟩ : syracuseStep 595763 = 893645) B893645
theorem B399179 : Blo 263822 399179 := bstep (se 1 (by rfl) ⟨299384, by rfl⟩ : syracuseStep 399179 = 598769) B598769
theorem B595799 : Blo 263822 595799 := bstep (se 1 (by rfl) ⟨446849, by rfl⟩ : syracuseStep 595799 = 893699) B893699
theorem B399191 : Blo 263822 399191 := bstep (se 1 (by rfl) ⟨299393, by rfl⟩ : syracuseStep 399191 = 598787) B598787
theorem B300919 : Blo 263822 300919 := bstep (se 1 (by rfl) ⟨225689, by rfl⟩ : syracuseStep 300919 = 451379) B451379
theorem B1152899 : Blo 263822 1152899 := bstep (se 1 (by rfl) ⟨864674, by rfl⟩ : syracuseStep 1152899 = 1729349) B1729349
theorem B399257 : Blo 263822 399257 := bstep (se 2 (by rfl) ⟨149721, by rfl⟩ : syracuseStep 399257 = 299443) B299443
theorem B759755 : Blo 263822 759755 := bstep (se 1 (by rfl) ⟨569816, by rfl⟩ : syracuseStep 759755 = 1139633) B1139633
theorem B595979 : Blo 263822 595979 := bstep (se 1 (by rfl) ⟨446984, by rfl⟩ : syracuseStep 595979 = 893969) B893969
theorem B399371 : Blo 263822 399371 := bstep (se 1 (by rfl) ⟨299528, by rfl⟩ : syracuseStep 399371 = 599057) B599057
theorem B399383 : Blo 263822 399383 := bstep (se 1 (by rfl) ⟨299537, by rfl⟩ : syracuseStep 399383 = 599075) B599075
theorem B301099 : Blo 263822 301099 := bstep (se 1 (by rfl) ⟨225824, by rfl⟩ : syracuseStep 301099 = 451649) B451649
theorem B890945 : Blo 263822 890945 := bstep (se 2 (by rfl) ⟨334104, by rfl⟩ : syracuseStep 890945 = 668209) B668209
theorem B596033 : Blo 263822 596033 := bstep (se 2 (by rfl) ⟨223512, by rfl⟩ : syracuseStep 596033 = 447025) B447025
theorem B5150789 : Blo 263822 5150789 := bstep (se 4 (by rfl) ⟨482886, by rfl⟩ : syracuseStep 5150789 = 965773) B965773
theorem B399449 : Blo 263822 399449 := bstep (se 2 (by rfl) ⟨149793, by rfl⟩ : syracuseStep 399449 = 299587) B299587
theorem B1513565 : Blo 263822 1513565 := bstep (se 3 (by rfl) ⟨283793, by rfl⟩ : syracuseStep 1513565 = 567587) B567587
theorem B1349783 : Blo 263822 1349783 := bstep (se 1 (by rfl) ⟨1012337, by rfl⟩ : syracuseStep 1349783 = 2024675) B2024675
theorem B301207 : Blo 263822 301207 := bstep (se 1 (by rfl) ⟨225905, by rfl⟩ : syracuseStep 301207 = 451811) B451811
theorem B956609 : Blo 263822 956609 := bstep (se 2 (by rfl) ⟨358728, by rfl⟩ : syracuseStep 956609 = 717457) B717457
theorem B399563 : Blo 263822 399563 := bstep (se 1 (by rfl) ⟨299672, by rfl⟩ : syracuseStep 399563 = 599345) B599345
theorem B334039 : Blo 263822 334039 := bstep (se 1 (by rfl) ⟨250529, by rfl⟩ : syracuseStep 334039 = 501059) B501059
theorem B399575 : Blo 263822 399575 := bstep (se 1 (by rfl) ⟨299681, by rfl⟩ : syracuseStep 399575 = 599363) B599363
theorem B596249 : Blo 263822 596249 := bstep (se 2 (by rfl) ⟨223593, by rfl⟩ : syracuseStep 596249 = 447187) B447187
theorem B399641 : Blo 263822 399641 := bstep (se 2 (by rfl) ⟨149865, by rfl⟩ : syracuseStep 399641 = 299731) B299731
theorem B596339 : Blo 263822 596339 := bstep (se 1 (by rfl) ⟨447254, by rfl⟩ : syracuseStep 596339 = 894509) B894509
theorem B399755 : Blo 263822 399755 := bstep (se 1 (by rfl) ⟨299816, by rfl⟩ : syracuseStep 399755 = 599633) B599633
theorem B596375 : Blo 263822 596375 := bstep (se 1 (by rfl) ⟨447281, by rfl⟩ : syracuseStep 596375 = 894563) B894563
theorem B399767 : Blo 263822 399767 := bstep (se 1 (by rfl) ⟨299825, by rfl⟩ : syracuseStep 399767 = 599651) B599651
theorem B399833 : Blo 263822 399833 := bstep (se 2 (by rfl) ⟨149937, by rfl⟩ : syracuseStep 399833 = 299875) B299875
theorem B4299277 : Blo 263822 4299277 := bstep (se 3 (by rfl) ⟨806114, by rfl⟩ : syracuseStep 4299277 = 1612229) B1612229
theorem B596555 : Blo 263822 596555 := bstep (se 1 (by rfl) ⟨447416, by rfl⟩ : syracuseStep 596555 = 894833) B894833
theorem B399947 : Blo 263822 399947 := bstep (se 1 (by rfl) ⟨299960, by rfl⟩ : syracuseStep 399947 = 599921) B599921
theorem B399959 : Blo 263822 399959 := bstep (se 1 (by rfl) ⟨299969, by rfl⟩ : syracuseStep 399959 = 599939) B599939
theorem B891485 : Blo 263822 891485 := bstep (se 3 (by rfl) ⟨167153, by rfl⟩ : syracuseStep 891485 = 334307) B334307
theorem B596609 : Blo 263822 596609 := bstep (se 2 (by rfl) ⟨223728, by rfl⟩ : syracuseStep 596609 = 447457) B447457
theorem B400025 : Blo 263822 400025 := bstep (se 2 (by rfl) ⟨150009, by rfl⟩ : syracuseStep 400025 = 300019) B300019
theorem B2005721 : Blo 263822 2005721 := bstep (se 2 (by rfl) ⟨752145, by rfl⟩ : syracuseStep 2005721 = 1504291) B1504291
theorem B400139 : Blo 263822 400139 := bstep (se 1 (by rfl) ⟨300104, by rfl⟩ : syracuseStep 400139 = 600209) B600209
theorem B400151 : Blo 263822 400151 := bstep (se 1 (by rfl) ⟨300113, by rfl⟩ : syracuseStep 400151 = 600227) B600227
theorem B1612619 : Blo 263822 1612619 := bstep (se 1 (by rfl) ⟨1209464, by rfl⟩ : syracuseStep 1612619 = 2418929) B2418929
theorem B1514315 : Blo 263822 1514315 := bstep (se 1 (by rfl) ⟨1135736, by rfl⟩ : syracuseStep 1514315 = 2271473) B2271473
theorem B596825 : Blo 263822 596825 := bstep (se 2 (by rfl) ⟨223809, by rfl⟩ : syracuseStep 596825 = 447619) B447619
theorem B400217 : Blo 263822 400217 := bstep (se 2 (by rfl) ⟨150081, by rfl⟩ : syracuseStep 400217 = 300163) B300163
theorem B3382195 : Blo 263822 3382195 := bstep (se 1 (by rfl) ⟨2536646, by rfl⟩ : syracuseStep 3382195 = 5073293) B5073293
theorem B596915 : Blo 263822 596915 := bstep (se 1 (by rfl) ⟨447686, by rfl⟩ : syracuseStep 596915 = 895373) B895373
theorem B400331 : Blo 263822 400331 := bstep (se 1 (by rfl) ⟨300248, by rfl⟩ : syracuseStep 400331 = 600497) B600497
theorem B596951 : Blo 263822 596951 := bstep (se 1 (by rfl) ⟨447713, by rfl⟩ : syracuseStep 596951 = 895427) B895427
theorem B400343 : Blo 263822 400343 := bstep (se 1 (by rfl) ⟨300257, by rfl⟩ : syracuseStep 400343 = 600515) B600515
theorem B400409 : Blo 263822 400409 := bstep (se 2 (by rfl) ⟨150153, by rfl⟩ : syracuseStep 400409 = 300307) B300307
theorem B2169949 : Blo 263822 2169949 := bstep (se 3 (by rfl) ⟨406865, by rfl⟩ : syracuseStep 2169949 = 813731) B813731
theorem B597131 : Blo 263822 597131 := bstep (se 1 (by rfl) ⟨447848, by rfl⟩ : syracuseStep 597131 = 895697) B895697
theorem B400523 : Blo 263822 400523 := bstep (se 1 (by rfl) ⟨300392, by rfl⟩ : syracuseStep 400523 = 600785) B600785
theorem B400535 : Blo 263822 400535 := bstep (se 1 (by rfl) ⟨300401, by rfl⟩ : syracuseStep 400535 = 600803) B600803
theorem B597185 : Blo 263822 597185 := bstep (se 2 (by rfl) ⟨223944, by rfl⟩ : syracuseStep 597185 = 447889) B447889
theorem B400601 : Blo 263822 400601 := bstep (se 2 (by rfl) ⟨150225, by rfl⟩ : syracuseStep 400601 = 300451) B300451
theorem B400715 : Blo 263822 400715 := bstep (se 1 (by rfl) ⟨300536, by rfl⟩ : syracuseStep 400715 = 601073) B601073
theorem B400727 : Blo 263822 400727 := bstep (se 1 (by rfl) ⟨300545, by rfl⟩ : syracuseStep 400727 = 601091) B601091
theorem B597401 : Blo 263822 597401 := bstep (se 2 (by rfl) ⟨224025, by rfl⟩ : syracuseStep 597401 = 448051) B448051
theorem B400793 : Blo 263822 400793 := bstep (se 2 (by rfl) ⟨150297, by rfl⟩ : syracuseStep 400793 = 300595) B300595
theorem B597491 : Blo 263822 597491 := bstep (se 1 (by rfl) ⟨448118, by rfl⟩ : syracuseStep 597491 = 896237) B896237
theorem B400907 : Blo 263822 400907 := bstep (se 1 (by rfl) ⟨300680, by rfl⟩ : syracuseStep 400907 = 601361) B601361
theorem B597527 : Blo 263822 597527 := bstep (se 1 (by rfl) ⟨448145, by rfl⟩ : syracuseStep 597527 = 896291) B896291
theorem B400919 : Blo 263822 400919 := bstep (se 1 (by rfl) ⟨300689, by rfl⟩ : syracuseStep 400919 = 601379) B601379
theorem B761395 : Blo 263822 761395 := bstep (se 1 (by rfl) ⟨571046, by rfl⟩ : syracuseStep 761395 = 1142093) B1142093
theorem B400985 : Blo 263822 400985 := bstep (se 2 (by rfl) ⟨150369, by rfl⟩ : syracuseStep 400985 = 300739) B300739
theorem B892619 : Blo 263822 892619 := bstep (se 1 (by rfl) ⟨669464, by rfl⟩ : syracuseStep 892619 = 1338929) B1338929
theorem B597707 : Blo 263822 597707 := bstep (se 1 (by rfl) ⟨448280, by rfl⟩ : syracuseStep 597707 = 896561) B896561
theorem B401099 : Blo 263822 401099 := bstep (se 1 (by rfl) ⟨300824, by rfl⟩ : syracuseStep 401099 = 601649) B601649
theorem B401111 : Blo 263822 401111 := bstep (se 1 (by rfl) ⟨300833, by rfl⟩ : syracuseStep 401111 = 601667) B601667
theorem B597761 : Blo 263822 597761 := bstep (se 2 (by rfl) ⟨224160, by rfl⟩ : syracuseStep 597761 = 448321) B448321
theorem B401177 : Blo 263822 401177 := bstep (se 2 (by rfl) ⟨150441, by rfl⟩ : syracuseStep 401177 = 300883) B300883
theorem B335755 : Blo 263822 335755 := bstep (se 1 (by rfl) ⟨251816, by rfl⟩ : syracuseStep 335755 = 503633) B503633
theorem B401291 : Blo 263822 401291 := bstep (se 1 (by rfl) ⟨300968, by rfl⟩ : syracuseStep 401291 = 601937) B601937
theorem B401303 : Blo 263822 401303 := bstep (se 1 (by rfl) ⟨300977, by rfl⟩ : syracuseStep 401303 = 601955) B601955
theorem B892889 : Blo 263822 892889 := bstep (se 2 (by rfl) ⟨334833, by rfl⟩ : syracuseStep 892889 = 669667) B669667
theorem B597977 : Blo 263822 597977 := bstep (se 2 (by rfl) ⟨224241, by rfl⟩ : syracuseStep 597977 = 448483) B448483
theorem B401369 : Blo 263822 401369 := bstep (se 2 (by rfl) ⟨150513, by rfl⟩ : syracuseStep 401369 = 301027) B301027
theorem B598067 : Blo 263822 598067 := bstep (se 1 (by rfl) ⟨448550, by rfl⟩ : syracuseStep 598067 = 897101) B897101
theorem B401483 : Blo 263822 401483 := bstep (se 1 (by rfl) ⟨301112, by rfl⟩ : syracuseStep 401483 = 602225) B602225
theorem B598103 : Blo 263822 598103 := bstep (se 1 (by rfl) ⟨448577, by rfl⟩ : syracuseStep 598103 = 897155) B897155
theorem B401495 : Blo 263822 401495 := bstep (se 1 (by rfl) ⟨301121, by rfl⟩ : syracuseStep 401495 = 602243) B602243
theorem B401561 : Blo 263822 401561 := bstep (se 2 (by rfl) ⟨150585, by rfl⟩ : syracuseStep 401561 = 301171) B301171
theorem B598283 : Blo 263822 598283 := bstep (se 1 (by rfl) ⟨448712, by rfl⟩ : syracuseStep 598283 = 897425) B897425
theorem B401675 : Blo 263822 401675 := bstep (se 1 (by rfl) ⟨301256, by rfl⟩ : syracuseStep 401675 = 602513) B602513
theorem B401687 : Blo 263822 401687 := bstep (se 1 (by rfl) ⟨301265, by rfl⟩ : syracuseStep 401687 = 602531) B602531
theorem B270635 : Blo 263822 270635 := bstep (se 1 (by rfl) ⟨202976, by rfl⟩ : syracuseStep 270635 = 405953) B405953
theorem B598337 : Blo 263822 598337 := bstep (se 2 (by rfl) ⟨224376, by rfl⟩ : syracuseStep 598337 = 448753) B448753
theorem B565579 : Blo 263822 565579 := bstep (se 1 (by rfl) ⟨424184, by rfl⟩ : syracuseStep 565579 = 848369) B848369
theorem B1515955 : Blo 263822 1515955 := bstep (se 1 (by rfl) ⟨1136966, by rfl⟩ : syracuseStep 1515955 = 2273933) B2273933
theorem B598553 : Blo 263822 598553 := bstep (se 2 (by rfl) ⟨224457, by rfl⟩ : syracuseStep 598553 = 448915) B448915
theorem B762443 : Blo 263822 762443 := bstep (se 1 (by rfl) ⟨571832, by rfl⟩ : syracuseStep 762443 = 1143665) B1143665
theorem B598643 : Blo 263822 598643 := bstep (se 1 (by rfl) ⟨448982, by rfl⟩ : syracuseStep 598643 = 897965) B897965
theorem B893591 : Blo 263822 893591 := bstep (se 1 (by rfl) ⟨670193, by rfl⟩ : syracuseStep 893591 = 1340387) B1340387
theorem B598679 : Blo 263822 598679 := bstep (se 1 (by rfl) ⟨449009, by rfl⟩ : syracuseStep 598679 = 898019) B898019
theorem B303799 : Blo 263822 303799 := bstep (se 1 (by rfl) ⟨227849, by rfl⟩ : syracuseStep 303799 = 455699) B455699
theorem B3842801 : Blo 263822 3842801 := bstep (se 2 (by rfl) ⟨1441050, by rfl⟩ : syracuseStep 3842801 = 2882101) B2882101
theorem B303895 : Blo 263822 303895 := bstep (se 1 (by rfl) ⟨227921, by rfl⟩ : syracuseStep 303895 = 455843) B455843
theorem B566041 : Blo 263822 566041 := bstep (se 2 (by rfl) ⟨212265, by rfl⟩ : syracuseStep 566041 = 424531) B424531
theorem B598859 : Blo 263822 598859 := bstep (se 1 (by rfl) ⟨449144, by rfl⟩ : syracuseStep 598859 = 898289) B898289
theorem B336727 : Blo 263822 336727 := bstep (se 1 (by rfl) ⟨252545, by rfl⟩ : syracuseStep 336727 = 505091) B505091
theorem B598913 : Blo 263822 598913 := bstep (se 2 (by rfl) ⟨224592, by rfl⟩ : syracuseStep 598913 = 449185) B449185
theorem B402329 : Blo 263822 402329 := bstep (se 2 (by rfl) ⟨150873, by rfl⟩ : syracuseStep 402329 = 301747) B301747
theorem B2860049 : Blo 263822 2860049 := bstep (se 2 (by rfl) ⟨1072518, by rfl⟩ : syracuseStep 2860049 = 2145037) B2145037
theorem B599129 : Blo 263822 599129 := bstep (se 2 (by rfl) ⟨224673, by rfl⟩ : syracuseStep 599129 = 449347) B449347
theorem B894131 : Blo 263822 894131 := bstep (se 1 (by rfl) ⟨670598, by rfl⟩ : syracuseStep 894131 = 1341197) B1341197
theorem B599219 : Blo 263822 599219 := bstep (se 1 (by rfl) ⟨449414, by rfl⟩ : syracuseStep 599219 = 898829) B898829
theorem B599255 : Blo 263822 599255 := bstep (se 1 (by rfl) ⟨449441, by rfl⟩ : syracuseStep 599255 = 898883) B898883
theorem B959809 : Blo 263822 959809 := bstep (se 2 (by rfl) ⟨359928, by rfl⟩ : syracuseStep 959809 = 719857) B719857
theorem B3417461 : Blo 263822 3417461 := bstep (se 5 (by rfl) ⟨160193, by rfl⟩ : syracuseStep 3417461 = 320387) B320387
theorem B599435 : Blo 263822 599435 := bstep (se 1 (by rfl) ⟨449576, by rfl⟩ : syracuseStep 599435 = 899153) B899153
theorem B894401 : Blo 263822 894401 := bstep (se 2 (by rfl) ⟨335400, by rfl⟩ : syracuseStep 894401 = 670801) B670801
theorem B599489 : Blo 263822 599489 := bstep (se 2 (by rfl) ⟨224808, by rfl⟩ : syracuseStep 599489 = 449617) B449617
theorem B1353347 : Blo 263822 1353347 := bstep (se 1 (by rfl) ⟨1015010, by rfl⟩ : syracuseStep 1353347 = 2030021) B2030021
theorem B337547 : Blo 263822 337547 := bstep (se 1 (by rfl) ⟨253160, by rfl⟩ : syracuseStep 337547 = 506321) B506321
theorem B599705 : Blo 263822 599705 := bstep (se 2 (by rfl) ⟨224889, by rfl⟩ : syracuseStep 599705 = 449779) B449779
theorem B501491 : Blo 263822 501491 := bstep (se 1 (by rfl) ⟨376118, by rfl⟩ : syracuseStep 501491 = 752237) B752237
theorem B599795 : Blo 263822 599795 := bstep (se 1 (by rfl) ⟨449846, by rfl⟩ : syracuseStep 599795 = 899693) B899693
theorem B599831 : Blo 263822 599831 := bstep (se 1 (by rfl) ⟨449873, by rfl⟩ : syracuseStep 599831 = 899747) B899747
theorem B1517413 : Blo 263822 1517413 := bstep (se 4 (by rfl) ⟨142257, by rfl⟩ : syracuseStep 1517413 = 284515) B284515
theorem B501643 : Blo 263822 501643 := bstep (se 1 (by rfl) ⟨376232, by rfl⟩ : syracuseStep 501643 = 752465) B752465
theorem B600011 : Blo 263822 600011 := bstep (se 1 (by rfl) ⟨450008, by rfl⟩ : syracuseStep 600011 = 900017) B900017
theorem B894941 : Blo 263822 894941 := bstep (se 3 (by rfl) ⟨167801, by rfl⟩ : syracuseStep 894941 = 335603) B335603
theorem B600065 : Blo 263822 600065 := bstep (se 2 (by rfl) ⟨225024, by rfl⟩ : syracuseStep 600065 = 450049) B450049
theorem B2009123 : Blo 263822 2009123 := bstep (se 1 (by rfl) ⟨1506842, by rfl⟩ : syracuseStep 2009123 = 3013685) B3013685
theorem B567425 : Blo 263822 567425 := bstep (se 2 (by rfl) ⟨212784, by rfl⟩ : syracuseStep 567425 = 425569) B425569
theorem B501977 : Blo 263822 501977 := bstep (se 2 (by rfl) ⟨188241, by rfl⟩ : syracuseStep 501977 = 376483) B376483
theorem B600281 : Blo 263822 600281 := bstep (se 2 (by rfl) ⟨225105, by rfl⟩ : syracuseStep 600281 = 450211) B450211
theorem B600371 : Blo 263822 600371 := bstep (se 1 (by rfl) ⟨450278, by rfl⟩ : syracuseStep 600371 = 900557) B900557
theorem B1550657 : Blo 263822 1550657 := bstep (se 2 (by rfl) ⟨581496, by rfl⟩ : syracuseStep 1550657 = 1162993) B1162993
theorem B338251 : Blo 263822 338251 := bstep (se 1 (by rfl) ⟨253688, by rfl⟩ : syracuseStep 338251 = 507377) B507377
theorem B600407 : Blo 263822 600407 := bstep (se 1 (by rfl) ⟨450305, by rfl⟩ : syracuseStep 600407 = 900611) B900611
theorem B1812887 : Blo 263822 1812887 := bstep (se 1 (by rfl) ⟨1359665, by rfl⟩ : syracuseStep 1812887 = 2719331) B2719331
theorem B1354163 : Blo 263822 1354163 := bstep (se 1 (by rfl) ⟨1015622, by rfl⟩ : syracuseStep 1354163 = 2031245) B2031245
theorem B1157597 : Blo 263822 1157597 := bstep (se 3 (by rfl) ⟨217049, by rfl⟩ : syracuseStep 1157597 = 434099) B434099
theorem B535027 : Blo 263822 535027 := bstep (se 1 (by rfl) ⟨401270, by rfl⟩ : syracuseStep 535027 = 802541) B802541
theorem B600587 : Blo 263822 600587 := bstep (se 1 (by rfl) ⟨450440, by rfl⟩ : syracuseStep 600587 = 900881) B900881
theorem B600641 : Blo 263822 600641 := bstep (se 2 (by rfl) ⟨225240, by rfl⟩ : syracuseStep 600641 = 450481) B450481
theorem B338519 : Blo 263822 338519 := bstep (se 1 (by rfl) ⟨253889, by rfl⟩ : syracuseStep 338519 = 507779) B507779
theorem B273079 : Blo 263822 273079 := bstep (se 1 (by rfl) ⟨204809, by rfl⟩ : syracuseStep 273079 = 409619) B409619
theorem B600857 : Blo 263822 600857 := bstep (se 2 (by rfl) ⟨225321, by rfl⟩ : syracuseStep 600857 = 450643) B450643
theorem B502615 : Blo 263822 502615 := bstep (se 1 (by rfl) ⟨376961, by rfl⟩ : syracuseStep 502615 = 753923) B753923
theorem B600947 : Blo 263822 600947 := bstep (se 1 (by rfl) ⟨450710, by rfl⟩ : syracuseStep 600947 = 901421) B901421
theorem B600983 : Blo 263822 600983 := bstep (se 1 (by rfl) ⟨450737, by rfl⟩ : syracuseStep 600983 = 901475) B901475
theorem B601163 : Blo 263822 601163 := bstep (se 1 (by rfl) ⟨450872, by rfl⟩ : syracuseStep 601163 = 901745) B901745
theorem B896075 : Blo 263822 896075 := bstep (se 1 (by rfl) ⟨672056, by rfl⟩ : syracuseStep 896075 = 1344113) B1344113
theorem B9743435 : Blo 263822 9743435 := bstep (se 1 (by rfl) ⟨7307576, by rfl⟩ : syracuseStep 9743435 = 14615153) B14615153
theorem B601217 : Blo 263822 601217 := bstep (se 2 (by rfl) ⟨225456, by rfl⟩ : syracuseStep 601217 = 450913) B450913
theorem B896345 : Blo 263822 896345 := bstep (se 2 (by rfl) ⟨336129, by rfl⟩ : syracuseStep 896345 = 672259) B672259
theorem B601433 : Blo 263822 601433 := bstep (se 2 (by rfl) ⟨225537, by rfl⟩ : syracuseStep 601433 = 451075) B451075
theorem B601523 : Blo 263822 601523 := bstep (se 1 (by rfl) ⟨451142, by rfl⟩ : syracuseStep 601523 = 902285) B902285
theorem B601559 : Blo 263822 601559 := bstep (se 1 (by rfl) ⟨451169, by rfl⟩ : syracuseStep 601559 = 902339) B902339
theorem B2731481 : Blo 263822 2731481 := bstep (se 2 (by rfl) ⟨1024305, by rfl⟩ : syracuseStep 2731481 = 2048611) B2048611
theorem B503435 : Blo 263822 503435 := bstep (se 1 (by rfl) ⟨377576, by rfl⟩ : syracuseStep 503435 = 755153) B755153
theorem B601739 : Blo 263822 601739 := bstep (se 1 (by rfl) ⟨451304, by rfl⟩ : syracuseStep 601739 = 902609) B902609
theorem B634547 : Blo 263822 634547 := bstep (se 1 (by rfl) ⟨475910, by rfl⟩ : syracuseStep 634547 = 951821) B951821
theorem B503489 : Blo 263822 503489 := bstep (se 2 (by rfl) ⟨188808, by rfl⟩ : syracuseStep 503489 = 377617) B377617
theorem B601793 : Blo 263822 601793 := bstep (se 2 (by rfl) ⟨225672, by rfl⟩ : syracuseStep 601793 = 451345) B451345
theorem B569099 : Blo 263822 569099 := bstep (se 1 (by rfl) ⟨426824, by rfl⟩ : syracuseStep 569099 = 853649) B853649
theorem B602009 : Blo 263822 602009 := bstep (se 2 (by rfl) ⟨225753, by rfl⟩ : syracuseStep 602009 = 451507) B451507
theorem B536537 : Blo 263822 536537 := bstep (se 2 (by rfl) ⟨201201, by rfl⟩ : syracuseStep 536537 = 402403) B402403
theorem B602099 : Blo 263822 602099 := bstep (se 1 (by rfl) ⟨451574, by rfl⟩ : syracuseStep 602099 = 903149) B903149
theorem B897047 : Blo 263822 897047 := bstep (se 1 (by rfl) ⟨672785, by rfl⟩ : syracuseStep 897047 = 1345571) B1345571
theorem B602135 : Blo 263822 602135 := bstep (se 1 (by rfl) ⟨451601, by rfl⟩ : syracuseStep 602135 = 903203) B903203
theorem B602315 : Blo 263822 602315 := bstep (se 1 (by rfl) ⟨451736, by rfl⟩ : syracuseStep 602315 = 903473) B903473
theorem B667865 : Blo 263822 667865 := bstep (se 2 (by rfl) ⟨250449, by rfl⟩ : syracuseStep 667865 = 500899) B500899
theorem B602369 : Blo 263822 602369 := bstep (se 2 (by rfl) ⟨225888, by rfl⟩ : syracuseStep 602369 = 451777) B451777
theorem B1028369 : Blo 263822 1028369 := bstep (se 2 (by rfl) ⟨385638, by rfl⟩ : syracuseStep 1028369 = 771277) B771277
theorem B2535725 : Blo 263822 2535725 := bstep (se 3 (by rfl) ⟨475448, by rfl⟩ : syracuseStep 2535725 = 950897) B950897
theorem B602585 : Blo 263822 602585 := bstep (se 2 (by rfl) ⟨225969, by rfl⟩ : syracuseStep 602585 = 451939) B451939
theorem B897587 : Blo 263822 897587 := bstep (se 1 (by rfl) ⟨673190, by rfl⟩ : syracuseStep 897587 = 1346381) B1346381
theorem B504407 : Blo 263822 504407 := bstep (se 1 (by rfl) ⟨378305, by rfl⟩ : syracuseStep 504407 = 756611) B756611
theorem B4108981 : Blo 263822 4108981 := bstep (se 5 (by rfl) ⟨192608, by rfl⟩ : syracuseStep 4108981 = 385217) B385217
theorem B537281 : Blo 263822 537281 := bstep (se 2 (by rfl) ⟨201480, by rfl⟩ : syracuseStep 537281 = 402961) B402961
theorem B570073 : Blo 263822 570073 := bstep (se 2 (by rfl) ⟨213777, by rfl⟩ : syracuseStep 570073 = 427555) B427555
theorem B897857 : Blo 263822 897857 := bstep (se 2 (by rfl) ⟨336696, by rfl⟩ : syracuseStep 897857 = 673393) B673393
theorem B570329 : Blo 263822 570329 := bstep (se 2 (by rfl) ⟨213873, by rfl⟩ : syracuseStep 570329 = 427747) B427747
theorem B668695 : Blo 263822 668695 := bstep (se 1 (by rfl) ⟨501521, by rfl⟩ : syracuseStep 668695 = 1003043) B1003043
theorem B635969 : Blo 263822 635969 := bstep (se 2 (by rfl) ⟨238488, by rfl⟩ : syracuseStep 635969 = 476977) B476977
theorem B504947 : Blo 263822 504947 := bstep (se 1 (by rfl) ⟨378710, by rfl⟩ : syracuseStep 504947 = 757421) B757421
theorem B898397 : Blo 263822 898397 := bstep (se 3 (by rfl) ⟨168449, by rfl⟩ : syracuseStep 898397 = 336899) B336899
theorem B570739 : Blo 263822 570739 := bstep (se 1 (by rfl) ⟨428054, by rfl⟩ : syracuseStep 570739 = 856109) B856109
theorem B669131 : Blo 263822 669131 := bstep (se 1 (by rfl) ⟨501848, by rfl⟩ : syracuseStep 669131 = 1003697) B1003697
theorem B505433 : Blo 263822 505433 := bstep (se 2 (by rfl) ⟨189537, by rfl⟩ : syracuseStep 505433 = 379075) B379075
theorem B669505 : Blo 263822 669505 := bstep (se 2 (by rfl) ⟨251064, by rfl⟩ : syracuseStep 669505 = 502129) B502129
theorem B571457 : Blo 263822 571457 := bstep (se 2 (by rfl) ⟨214296, by rfl⟩ : syracuseStep 571457 = 428593) B428593
theorem B670103 : Blo 263822 670103 := bstep (se 1 (by rfl) ⟨502577, by rfl⟩ : syracuseStep 670103 = 1005155) B1005155
theorem B571799 : Blo 263822 571799 := bstep (se 1 (by rfl) ⟨428849, by rfl⟩ : syracuseStep 571799 = 857699) B857699
theorem B899531 : Blo 263822 899531 := bstep (se 1 (by rfl) ⟨674648, by rfl⟩ : syracuseStep 899531 = 1349297) B1349297
theorem B571969 : Blo 263822 571969 := bstep (se 2 (by rfl) ⟨214488, by rfl⟩ : syracuseStep 571969 = 428977) B428977
theorem B899801 : Blo 263822 899801 := bstep (se 2 (by rfl) ⟨337425, by rfl⟩ : syracuseStep 899801 = 674851) B674851
theorem B605171 : Blo 263822 605171 := bstep (se 1 (by rfl) ⟨453878, by rfl⟩ : syracuseStep 605171 = 907757) B907757
theorem B506891 : Blo 263822 506891 := bstep (se 1 (by rfl) ⟨380168, by rfl⟩ : syracuseStep 506891 = 760337) B760337
theorem B638027 : Blo 263822 638027 := bstep (se 1 (by rfl) ⟨478520, by rfl⟩ : syracuseStep 638027 = 957041) B957041
theorem B375959 : Blo 263822 375959 := bstep (se 1 (by rfl) ⟨281969, by rfl⟩ : syracuseStep 375959 = 563939) B563939
theorem B2276531 : Blo 263822 2276531 := bstep (se 1 (by rfl) ⟨1707398, by rfl⟩ : syracuseStep 2276531 = 3414797) B3414797
theorem B670913 : Blo 263822 670913 := bstep (se 2 (by rfl) ⟨251592, by rfl⟩ : syracuseStep 670913 = 503185) B503185
theorem B507073 : Blo 263822 507073 := bstep (se 2 (by rfl) ⟨190152, by rfl⟩ : syracuseStep 507073 = 380305) B380305
theorem B2014469 : Blo 263822 2014469 := bstep (se 4 (by rfl) ⟨188856, by rfl⟩ : syracuseStep 2014469 = 377713) B377713
theorem B1949021 : Blo 263822 1949021 := bstep (se 3 (by rfl) ⟨365441, by rfl⟩ : syracuseStep 1949021 = 730883) B730883
theorem B1129859 : Blo 263822 1129859 := bstep (se 1 (by rfl) ⟨847394, by rfl⟩ : syracuseStep 1129859 = 1694789) B1694789
theorem B900503 : Blo 263822 900503 := bstep (se 1 (by rfl) ⟨675377, by rfl⟩ : syracuseStep 900503 = 1350755) B1350755
theorem B376267 : Blo 263822 376267 := bstep (se 1 (by rfl) ⟨282200, by rfl⟩ : syracuseStep 376267 = 564401) B564401
theorem B2276909 : Blo 263822 2276909 := bstep (se 3 (by rfl) ⟨426920, by rfl⟩ : syracuseStep 2276909 = 853841) B853841
theorem B1523245 : Blo 263822 1523245 := bstep (se 3 (by rfl) ⟨285608, by rfl⟩ : syracuseStep 1523245 = 571217) B571217
theorem B507521 : Blo 263822 507521 := bstep (se 2 (by rfl) ⟨190320, by rfl⟩ : syracuseStep 507521 = 380641) B380641
theorem B4570829 : Blo 263822 4570829 := bstep (se 3 (by rfl) ⟨857030, by rfl⟩ : syracuseStep 4570829 = 1714061) B1714061
theorem B671449 : Blo 263822 671449 := bstep (se 2 (by rfl) ⟨251793, by rfl⟩ : syracuseStep 671449 = 503587) B503587
theorem B901043 : Blo 263822 901043 := bstep (se 1 (by rfl) ⟨675782, by rfl⟩ : syracuseStep 901043 = 1351565) B1351565
theorem B507863 : Blo 263822 507863 := bstep (se 1 (by rfl) ⟨380897, by rfl⟩ : syracuseStep 507863 = 761795) B761795
theorem B901313 : Blo 263822 901313 := bstep (se 2 (by rfl) ⟨337992, by rfl⟩ : syracuseStep 901313 = 675985) B675985
theorem B541043 : Blo 263822 541043 := bstep (se 1 (by rfl) ⟨405782, by rfl⟩ : syracuseStep 541043 = 811565) B811565
theorem B377303 : Blo 263822 377303 := bstep (se 1 (by rfl) ⟨282977, by rfl⟩ : syracuseStep 377303 = 565955) B565955
theorem B377497 : Blo 263822 377497 := bstep (se 2 (by rfl) ⟨141561, by rfl⟩ : syracuseStep 377497 = 283123) B283123
theorem B901853 : Blo 263822 901853 := bstep (se 3 (by rfl) ⟨169097, by rfl⟩ : syracuseStep 901853 = 338195) B338195
theorem B672563 : Blo 263822 672563 := bstep (se 1 (by rfl) ⟨504422, by rfl⟩ : syracuseStep 672563 = 1008845) B1008845
theorem B1622915 : Blo 263822 1622915 := bstep (se 1 (by rfl) ⟨1217186, by rfl⟩ : syracuseStep 1622915 = 2434373) B2434373
theorem B672857 : Blo 263822 672857 := bstep (se 2 (by rfl) ⟨252321, by rfl⟩ : syracuseStep 672857 = 504643) B504643
theorem B1131671 : Blo 263822 1131671 := bstep (se 1 (by rfl) ⟨848753, by rfl⟩ : syracuseStep 1131671 = 1697507) B1697507
theorem B542081 : Blo 263822 542081 := bstep (se 2 (by rfl) ⟨203280, by rfl⟩ : syracuseStep 542081 = 406561) B406561
theorem B771545 : Blo 263822 771545 := bstep (se 2 (by rfl) ⟨289329, by rfl⟩ : syracuseStep 771545 = 578659) B578659
theorem B2606627 : Blo 263822 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B2016899 : Blo 263822 2016899 := bstep (se 1 (by rfl) ⟨1512674, by rfl⟩ : syracuseStep 2016899 = 3025349) B3025349
theorem B902987 : Blo 263822 902987 := bstep (se 1 (by rfl) ⟨677240, by rfl⟩ : syracuseStep 902987 = 1354481) B1354481
theorem B378955 : Blo 263822 378955 := bstep (se 1 (by rfl) ⟨284216, by rfl⟩ : syracuseStep 378955 = 568433) B568433
theorem B903257 : Blo 263822 903257 := bstep (se 2 (by rfl) ⟨338721, by rfl⟩ : syracuseStep 903257 = 677443) B677443
theorem B1427557 : Blo 263822 1427557 := bstep (se 4 (by rfl) ⟨133833, by rfl⟩ : syracuseStep 1427557 = 267667) B267667
theorem B1427777 : Blo 263822 1427777 := bstep (se 2 (by rfl) ⟨535416, by rfl⟩ : syracuseStep 1427777 = 1070833) B1070833
theorem B1133003 : Blo 263822 1133003 := bstep (se 1 (by rfl) ⟨849752, by rfl⟩ : syracuseStep 1133003 = 1699505) B1699505
theorem B641611 : Blo 263822 641611 := bstep (se 1 (by rfl) ⟨481208, by rfl⟩ : syracuseStep 641611 = 962417) B962417
theorem B674507 : Blo 263822 674507 := bstep (se 1 (by rfl) ⟨505880, by rfl⟩ : syracuseStep 674507 = 1011761) B1011761
theorem B1133585 : Blo 263822 1133585 := bstep (se 2 (by rfl) ⟨425094, by rfl⟩ : syracuseStep 1133585 = 850189) B850189
theorem B445655 : Blo 263822 445655 := bstep (se 1 (by rfl) ⟨334241, by rfl⟩ : syracuseStep 445655 = 668483) B668483
theorem B445783 : Blo 263822 445783 := bstep (se 1 (by rfl) ⟨334337, by rfl⟩ : syracuseStep 445783 = 668675) B668675
theorem B609623 : Blo 263822 609623 := bstep (se 1 (by rfl) ⟨457217, by rfl⟩ : syracuseStep 609623 = 914435) B914435
theorem B675479 : Blo 263822 675479 := bstep (se 1 (by rfl) ⟨506609, by rfl⟩ : syracuseStep 675479 = 1013219) B1013219
theorem B1003211 : Blo 263822 1003211 := bstep (se 1 (by rfl) ⟨752408, by rfl⟩ : syracuseStep 1003211 = 1504817) B1504817
theorem B1003225 : Blo 263822 1003225 := bstep (se 2 (by rfl) ⟨376209, by rfl⟩ : syracuseStep 1003225 = 752419) B752419
theorem B610199 : Blo 263822 610199 := bstep (se 1 (by rfl) ⟨457649, by rfl⟩ : syracuseStep 610199 = 915299) B915299
theorem B479155 : Blo 263822 479155 := bstep (se 1 (by rfl) ⟨359366, by rfl⟩ : syracuseStep 479155 = 718733) B718733
theorem B446411 : Blo 263822 446411 := bstep (se 1 (by rfl) ⟨334808, by rfl⟩ : syracuseStep 446411 = 669617) B669617
theorem B1134643 : Blo 263822 1134643 := bstep (se 1 (by rfl) ⟨850982, by rfl⟩ : syracuseStep 1134643 = 1701965) B1701965
theorem B446539 : Blo 263822 446539 := bstep (se 1 (by rfl) ⟨334904, by rfl⟩ : syracuseStep 446539 = 669809) B669809
theorem B479371 : Blo 263822 479371 := bstep (se 1 (by rfl) ⟨359528, by rfl⟩ : syracuseStep 479371 = 719057) B719057
theorem B1527959 : Blo 263822 1527959 := bstep (se 1 (by rfl) ⟨1145969, by rfl⟩ : syracuseStep 1527959 = 2291939) B2291939
theorem B446681 : Blo 263822 446681 := bstep (se 2 (by rfl) ⟨167505, by rfl⟩ : syracuseStep 446681 = 335011) B335011
theorem B676147 : Blo 263822 676147 := bstep (se 1 (by rfl) ⟨507110, by rfl⟩ : syracuseStep 676147 = 1014221) B1014221
theorem B446809 : Blo 263822 446809 := bstep (se 2 (by rfl) ⟨167553, by rfl⟩ : syracuseStep 446809 = 335107) B335107
theorem B283063 : Blo 263822 283063 := bstep (se 1 (by rfl) ⟨212297, by rfl⟩ : syracuseStep 283063 = 424595) B424595
theorem B676289 : Blo 263822 676289 := bstep (se 2 (by rfl) ⟨253608, by rfl⟩ : syracuseStep 676289 = 507217) B507217
theorem B610763 : Blo 263822 610763 := bstep (se 1 (by rfl) ⟨458072, by rfl⟩ : syracuseStep 610763 = 916145) B916145
theorem B1004183 : Blo 263822 1004183 := bstep (se 1 (by rfl) ⟨753137, by rfl⟩ : syracuseStep 1004183 = 1506275) B1506275
theorem B447383 : Blo 263822 447383 := bstep (se 1 (by rfl) ⟨335537, by rfl⟩ : syracuseStep 447383 = 671075) B671075
theorem B2053043 : Blo 263822 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B2020301 : Blo 263822 2020301 := bstep (se 3 (by rfl) ⟨378806, by rfl⟩ : syracuseStep 2020301 = 757613) B757613
theorem B447511 : Blo 263822 447511 := bstep (se 1 (by rfl) ⟨335633, by rfl⟩ : syracuseStep 447511 = 671267) B671267
theorem B1922093 : Blo 263822 1922093 := bstep (se 3 (by rfl) ⟨360392, by rfl⟩ : syracuseStep 1922093 = 720785) B720785
theorem B283883 : Blo 263822 283883 := bstep (se 1 (by rfl) ⟨212912, by rfl⟩ : syracuseStep 283883 = 425825) B425825
theorem B3429697 : Blo 263822 3429697 := bstep (se 2 (by rfl) ⟨1286136, by rfl⟩ : syracuseStep 3429697 = 2572273) B2572273
theorem B1136045 : Blo 263822 1136045 := bstep (se 3 (by rfl) ⟨213008, by rfl⟩ : syracuseStep 1136045 = 426017) B426017
theorem B2020787 : Blo 263822 2020787 := bstep (se 1 (by rfl) ⟨1515590, by rfl⟩ : syracuseStep 2020787 = 3031181) B3031181
theorem B480755 : Blo 263822 480755 := bstep (se 1 (by rfl) ⟨360566, by rfl⟩ : syracuseStep 480755 = 721133) B721133
theorem B1955393 : Blo 263822 1955393 := bstep (se 2 (by rfl) ⟨733272, by rfl⟩ : syracuseStep 1955393 = 1466545) B1466545
theorem B808537 : Blo 263822 808537 := bstep (se 2 (by rfl) ⟨303201, by rfl⟩ : syracuseStep 808537 = 606403) B606403
theorem B448139 : Blo 263822 448139 := bstep (se 1 (by rfl) ⟨336104, by rfl⟩ : syracuseStep 448139 = 672209) B672209
theorem B677555 : Blo 263822 677555 := bstep (se 1 (by rfl) ⟨508166, by rfl⟩ : syracuseStep 677555 = 1016333) B1016333
theorem B448267 : Blo 263822 448267 := bstep (se 1 (by rfl) ⟨336200, by rfl⟩ : syracuseStep 448267 = 672401) B672401
theorem B1693457 : Blo 263822 1693457 := bstep (se 2 (by rfl) ⟨635046, by rfl⟩ : syracuseStep 1693457 = 1270093) B1270093
theorem B1005443 : Blo 263822 1005443 := bstep (se 1 (by rfl) ⟨754082, by rfl⟩ : syracuseStep 1005443 = 1508165) B1508165
theorem B448409 : Blo 263822 448409 := bstep (se 2 (by rfl) ⟨168153, by rfl⟩ : syracuseStep 448409 = 336307) B336307
theorem B645067 : Blo 263822 645067 := bstep (se 1 (by rfl) ⟨483800, by rfl⟩ : syracuseStep 645067 = 967601) B967601
theorem B546817 : Blo 263822 546817 := bstep (se 2 (by rfl) ⟨205056, by rfl⟩ : syracuseStep 546817 = 410113) B410113
theorem B448537 : Blo 263822 448537 := bstep (se 2 (by rfl) ⟨168201, by rfl⟩ : syracuseStep 448537 = 336403) B336403
theorem B481345 : Blo 263822 481345 := bstep (se 2 (by rfl) ⟨180504, by rfl⟩ : syracuseStep 481345 = 361009) B361009
theorem B2087117 : Blo 263822 2087117 := bstep (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) B782669
theorem B284887 : Blo 263822 284887 := bstep (se 1 (by rfl) ⟨213665, by rfl⟩ : syracuseStep 284887 = 427331) B427331
theorem B449111 : Blo 263822 449111 := bstep (se 1 (by rfl) ⟨336833, by rfl⟩ : syracuseStep 449111 = 673667) B673667
theorem B907865 : Blo 263822 907865 := bstep (se 2 (by rfl) ⟨340449, by rfl⟩ : syracuseStep 907865 = 680899) B680899
theorem B481907 : Blo 263822 481907 := bstep (se 1 (by rfl) ⟨361430, by rfl⟩ : syracuseStep 481907 = 722861) B722861
theorem B449239 : Blo 263822 449239 := bstep (se 1 (by rfl) ⟨336929, by rfl⟩ : syracuseStep 449239 = 673859) B673859
theorem B2022245 : Blo 263822 2022245 := bstep (se 4 (by rfl) ⟨189585, by rfl⟩ : syracuseStep 2022245 = 379171) B379171
theorem B5102513 : Blo 263822 5102513 := bstep (se 2 (by rfl) ⟨1913442, by rfl⟩ : syracuseStep 5102513 = 3826885) B3826885
theorem B285643 : Blo 263822 285643 := bstep (se 1 (by rfl) ⟨214232, by rfl⟩ : syracuseStep 285643 = 428465) B428465
theorem B679115 : Blo 263822 679115 := bstep (se 1 (by rfl) ⟨509336, by rfl⟩ : syracuseStep 679115 = 1018673) B1018673
theorem B1531097 : Blo 263822 1531097 := bstep (se 2 (by rfl) ⟨574161, by rfl⟩ : syracuseStep 1531097 = 1148323) B1148323
theorem B1039661 : Blo 263822 1039661 := bstep (se 3 (by rfl) ⟨194936, by rfl⟩ : syracuseStep 1039661 = 389873) B389873
theorem B2022731 : Blo 263822 2022731 := bstep (se 1 (by rfl) ⟨1517048, by rfl⟩ : syracuseStep 2022731 = 3034097) B3034097
theorem B449867 : Blo 263822 449867 := bstep (se 1 (by rfl) ⟨337400, by rfl⟩ : syracuseStep 449867 = 674801) B674801
theorem B449995 : Blo 263822 449995 := bstep (se 1 (by rfl) ⟨337496, by rfl⟩ : syracuseStep 449995 = 674993) B674993
theorem B450137 : Blo 263822 450137 := bstep (se 2 (by rfl) ⟨168801, by rfl⟩ : syracuseStep 450137 = 337603) B337603
theorem B450265 : Blo 263822 450265 := bstep (se 2 (by rfl) ⟨168849, by rfl⟩ : syracuseStep 450265 = 337699) B337699
theorem B2154701 : Blo 263822 2154701 := bstep (se 3 (by rfl) ⟨404006, by rfl⟩ : syracuseStep 2154701 = 808013) B808013
theorem B450839 : Blo 263822 450839 := bstep (se 1 (by rfl) ⟨338129, by rfl⟩ : syracuseStep 450839 = 676259) B676259
theorem B319883 : Blo 263822 319883 := bstep (se 1 (by rfl) ⟨239912, by rfl⟩ : syracuseStep 319883 = 479825) B479825
theorem B450967 : Blo 263822 450967 := bstep (se 1 (by rfl) ⟨338225, by rfl⟩ : syracuseStep 450967 = 676451) B676451
theorem B320215 : Blo 263822 320215 := bstep (se 1 (by rfl) ⟨240161, by rfl⟩ : syracuseStep 320215 = 480323) B480323
theorem B680755 : Blo 263822 680755 := bstep (se 1 (by rfl) ⟨510566, by rfl⟩ : syracuseStep 680755 = 1021133) B1021133
theorem B1008557 : Blo 263822 1008557 := bstep (se 3 (by rfl) ⟨189104, by rfl⟩ : syracuseStep 1008557 = 378209) B378209
theorem B451595 : Blo 263822 451595 := bstep (se 1 (by rfl) ⟨338696, by rfl⟩ : syracuseStep 451595 = 677393) B677393
theorem B1336337 : Blo 263822 1336337 := bstep (se 2 (by rfl) ⟨501126, by rfl⟩ : syracuseStep 1336337 = 1002253) B1002253
theorem B320599 : Blo 263822 320599 := bstep (se 1 (by rfl) ⟨240449, by rfl⟩ : syracuseStep 320599 = 480899) B480899
theorem B451723 : Blo 263822 451723 := bstep (se 1 (by rfl) ⟨338792, by rfl⟩ : syracuseStep 451723 = 677585) B677585
theorem B1336499 : Blo 263822 1336499 := bstep (se 1 (by rfl) ⟨1002374, by rfl⟩ : syracuseStep 1336499 = 2004749) B2004749
theorem B517387 : Blo 263822 517387 := bstep (se 1 (by rfl) ⟨388040, by rfl⟩ : syracuseStep 517387 = 776081) B776081
theorem B451865 : Blo 263822 451865 := bstep (se 2 (by rfl) ⟨169449, by rfl⟩ : syracuseStep 451865 = 338899) B338899
theorem B1140247 : Blo 263822 1140247 := bstep (se 1 (by rfl) ⟨855185, by rfl⟩ : syracuseStep 1140247 = 1710371) B1710371
theorem B288311 : Blo 263822 288311 := bstep (se 1 (by rfl) ⟨216233, by rfl⟩ : syracuseStep 288311 = 432467) B432467
theorem B1140317 : Blo 263822 1140317 := bstep (se 3 (by rfl) ⟨213809, by rfl⟩ : syracuseStep 1140317 = 427619) B427619
theorem B1009331 : Blo 263822 1009331 := bstep (se 1 (by rfl) ⟨756998, by rfl⟩ : syracuseStep 1009331 = 1513997) B1513997
theorem B714689 : Blo 263822 714689 := bstep (se 2 (by rfl) ⟨268008, by rfl⟩ : syracuseStep 714689 = 536017) B536017
theorem B1141067 : Blo 263822 1141067 := bstep (se 1 (by rfl) ⟨855800, by rfl⟩ : syracuseStep 1141067 = 1711601) B1711601
theorem B846359 : Blo 263822 846359 := bstep (se 1 (by rfl) ⟨634769, by rfl⟩ : syracuseStep 846359 = 1269539) B1269539
theorem B6810317 : Blo 263822 6810317 := bstep (se 3 (by rfl) ⟨1276934, by rfl⟩ : syracuseStep 6810317 = 2553869) B2553869
theorem B1338443 : Blo 263822 1338443 := bstep (se 1 (by rfl) ⟨1003832, by rfl⟩ : syracuseStep 1338443 = 2007665) B2007665
theorem B1010819 : Blo 263822 1010819 := bstep (se 1 (by rfl) ⟨758114, by rfl⟩ : syracuseStep 1010819 = 1516229) B1516229
theorem B1371485 : Blo 263822 1371485 := bstep (se 3 (by rfl) ⟨257153, by rfl⟩ : syracuseStep 1371485 = 514307) B514307
theorem B454091 : Blo 263822 454091 := bstep (se 1 (by rfl) ⟨340568, by rfl⟩ : syracuseStep 454091 = 681137) B681137
theorem B1011275 : Blo 263822 1011275 := bstep (se 1 (by rfl) ⟨758456, by rfl⟩ : syracuseStep 1011275 = 1516913) B1516913
theorem B1011473 : Blo 263822 1011473 := bstep (se 2 (by rfl) ⟨379302, by rfl⟩ : syracuseStep 1011473 = 758605) B758605
theorem B847691 : Blo 263822 847691 := bstep (se 1 (by rfl) ⟨635768, by rfl⟩ : syracuseStep 847691 = 1271537) B1271537
theorem B1503107 : Blo 263822 1503107 := bstep (se 1 (by rfl) ⟨1127330, by rfl⟩ : syracuseStep 1503107 = 2254661) B2254661
theorem B913369 : Blo 263822 913369 := bstep (se 2 (by rfl) ⟨342513, by rfl⟩ : syracuseStep 913369 = 685027) B685027
theorem B2420941 : Blo 263822 2420941 := bstep (se 3 (by rfl) ⟨453926, by rfl⟩ : syracuseStep 2420941 = 907853) B907853
theorem B2158979 : Blo 263822 2158979 := bstep (se 1 (by rfl) ⟨1619234, by rfl⟩ : syracuseStep 2158979 = 3238469) B3238469
theorem B1012247 : Blo 263822 1012247 := bstep (se 1 (by rfl) ⟨759185, by rfl⟩ : syracuseStep 1012247 = 1518371) B1518371
theorem B2028077 : Blo 263822 2028077 := bstep (se 3 (by rfl) ⟨380264, by rfl⟩ : syracuseStep 2028077 = 760529) B760529
theorem B1372717 : Blo 263822 1372717 := bstep (se 3 (by rfl) ⟨257384, by rfl⟩ : syracuseStep 1372717 = 514769) B514769
theorem B422615 : Blo 263822 422615 := bstep (se 1 (by rfl) ⟨316961, by rfl⟩ : syracuseStep 422615 = 633923) B633923
theorem B1012445 : Blo 263822 1012445 := bstep (se 3 (by rfl) ⟨189833, by rfl⟩ : syracuseStep 1012445 = 379667) B379667
theorem B1340225 : Blo 263822 1340225 := bstep (se 2 (by rfl) ⟨502584, by rfl⟩ : syracuseStep 1340225 = 1005169) B1005169
theorem B717661 : Blo 263822 717661 := bstep (se 3 (by rfl) ⟨134561, by rfl⟩ : syracuseStep 717661 = 269123) B269123
theorem B848819 : Blo 263822 848819 := bstep (se 1 (by rfl) ⟨636614, by rfl⟩ : syracuseStep 848819 = 1273229) B1273229
theorem B422923 : Blo 263822 422923 := bstep (se 1 (by rfl) ⟨317192, by rfl⟩ : syracuseStep 422923 = 634385) B634385
theorem B1700939 : Blo 263822 1700939 := bstep (se 1 (by rfl) ⟨1275704, by rfl⟩ : syracuseStep 1700939 = 2551409) B2551409
theorem B2946179 : Blo 263822 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B685273 : Blo 263822 685273 := bstep (se 2 (by rfl) ⟨256977, by rfl⟩ : syracuseStep 685273 = 513955) B513955
theorem B718103 : Blo 263822 718103 := bstep (se 1 (by rfl) ⟨538577, by rfl⟩ : syracuseStep 718103 = 1077155) B1077155
theorem B1144343 : Blo 263822 1144343 := bstep (se 1 (by rfl) ⟨858257, by rfl⟩ : syracuseStep 1144343 = 1716515) B1716515
theorem B1930787 : Blo 263822 1930787 := bstep (se 1 (by rfl) ⟨1448090, by rfl⟩ : syracuseStep 1930787 = 2896181) B2896181
theorem B1078829 : Blo 263822 1078829 := bstep (se 3 (by rfl) ⟨202280, by rfl⟩ : syracuseStep 1078829 = 404561) B404561
theorem B3012227 : Blo 263822 3012227 := bstep (se 1 (by rfl) ⟨2259170, by rfl⟩ : syracuseStep 3012227 = 4518341) B4518341
theorem B12318641 : Blo 263822 12318641 := bstep (se 2 (by rfl) ⟨4619490, by rfl⟩ : syracuseStep 12318641 = 9238981) B9238981
theorem B850009 : Blo 263822 850009 := bstep (se 2 (by rfl) ⟨318753, by rfl⟩ : syracuseStep 850009 = 637507) B637507
theorem B424153 : Blo 263822 424153 := bstep (se 2 (by rfl) ⟨159057, by rfl⟩ : syracuseStep 424153 = 318115) B318115
theorem B850265 : Blo 263822 850265 := bstep (se 2 (by rfl) ⟨318849, by rfl⟩ : syracuseStep 850265 = 637699) B637699
theorem B1014403 : Blo 263822 1014403 := bstep (se 1 (by rfl) ⟨760802, by rfl⟩ : syracuseStep 1014403 = 1521605) B1521605
theorem B850625 : Blo 263822 850625 := bstep (se 2 (by rfl) ⟨318984, by rfl⟩ : syracuseStep 850625 = 637969) B637969
theorem B1342169 : Blo 263822 1342169 := bstep (se 2 (by rfl) ⟨503313, by rfl⟩ : syracuseStep 1342169 = 1006627) B1006627
theorem B1080139 : Blo 263822 1080139 := bstep (se 1 (by rfl) ⟨810104, by rfl⟩ : syracuseStep 1080139 = 1620209) B1620209
theorem B1538909 : Blo 263822 1538909 := bstep (se 3 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 1538909 = 577091) B577091
theorem B1014707 : Blo 263822 1014707 := bstep (se 1 (by rfl) ⟨761030, by rfl⟩ : syracuseStep 1014707 = 1522061) B1522061
theorem B1080337 : Blo 263822 1080337 := bstep (se 2 (by rfl) ⟨405126, by rfl⟩ : syracuseStep 1080337 = 810253) B810253
theorem B2260061 : Blo 263822 2260061 := bstep (se 3 (by rfl) ⟨423761, by rfl⟩ : syracuseStep 2260061 = 847523) B847523
theorem B752989 : Blo 263822 752989 := bstep (se 3 (by rfl) ⟨141185, by rfl⟩ : syracuseStep 752989 = 282371) B282371
theorem B753047 : Blo 263822 753047 := bstep (se 1 (by rfl) ⟨564785, by rfl⟩ : syracuseStep 753047 = 1129571) B1129571
theorem B851393 : Blo 263822 851393 := bstep (se 2 (by rfl) ⟨319272, by rfl⟩ : syracuseStep 851393 = 638545) B638545
theorem B1015361 : Blo 263822 1015361 := bstep (se 2 (by rfl) ⟨380760, by rfl⟩ : syracuseStep 1015361 = 761521) B761521
theorem B2260811 : Blo 263822 2260811 := bstep (se 1 (by rfl) ⟨1695608, by rfl⟩ : syracuseStep 2260811 = 3391217) B3391217
theorem B851905 : Blo 263822 851905 := bstep (se 2 (by rfl) ⟨319464, by rfl⟩ : syracuseStep 851905 = 638929) B638929
theorem B360695 : Blo 263822 360695 := bstep (se 1 (by rfl) ⟨270521, by rfl⟩ : syracuseStep 360695 = 541043) B541043
theorem B754105 : Blo 263822 754105 := bstep (se 2 (by rfl) ⟨282789, by rfl⟩ : syracuseStep 754105 = 565579) B565579
theorem B1081943 : Blo 263822 1081943 := bstep (se 1 (by rfl) ⟨811457, by rfl⟩ : syracuseStep 1081943 = 1622915) B1622915
theorem B4326007 : Blo 263822 4326007 := bstep (se 1 (by rfl) ⟨3244505, by rfl⟩ : syracuseStep 4326007 = 6489011) B6489011
theorem B754447 : Blo 263822 754447 := bstep (se 1 (by rfl) ⟨565835, by rfl⟩ : syracuseStep 754447 = 1131671) B1131671
theorem B721693 : Blo 263822 721693 := bstep (se 3 (by rfl) ⟨135317, by rfl⟩ : syracuseStep 721693 = 270635) B270635
theorem B3408803 : Blo 263822 3408803 := bstep (se 1 (by rfl) ⟨2556602, by rfl⟩ : syracuseStep 3408803 = 5113205) B5113205
theorem B361387 : Blo 263822 361387 := bstep (se 1 (by rfl) ⟨271040, by rfl⟩ : syracuseStep 361387 = 542081) B542081
theorem B426953 : Blo 263822 426953 := bstep (se 2 (by rfl) ⟨160107, by rfl⟩ : syracuseStep 426953 = 320215) B320215
theorem B853021 : Blo 263822 853021 := bstep (se 3 (by rfl) ⟨159941, by rfl⟩ : syracuseStep 853021 = 319883) B319883
theorem B754721 : Blo 263822 754721 := bstep (se 2 (by rfl) ⟨283020, by rfl⟩ : syracuseStep 754721 = 566041) B566041
theorem B1344599 : Blo 263822 1344599 := bstep (se 1 (by rfl) ⟨1008449, by rfl⟩ : syracuseStep 1344599 = 2016899) B2016899
theorem B427465 : Blo 263822 427465 := bstep (se 2 (by rfl) ⟨160299, by rfl⟩ : syracuseStep 427465 = 320599) B320599
theorem B951851 : Blo 263822 951851 := bstep (se 1 (by rfl) ⟨713888, by rfl⟩ : syracuseStep 951851 = 1427777) B1427777
theorem B1345085 : Blo 263822 1345085 := bstep (se 3 (by rfl) ⟨252203, by rfl⟩ : syracuseStep 1345085 = 504407) B504407
theorem B1050199 : Blo 263822 1050199 := bstep (se 1 (by rfl) ⟨787649, by rfl⟩ : syracuseStep 1050199 = 1575299) B1575299
theorem B755335 : Blo 263822 755335 := bstep (se 1 (by rfl) ⟨566501, by rfl⟩ : syracuseStep 755335 = 1133003) B1133003
theorem B263823 : Blo 263822 263823 := bstep (se 1 (by rfl) ⟨197867, by rfl⟩ : syracuseStep 263823 = 395735) B395735
theorem B689849 : Blo 263822 689849 := bstep (se 2 (by rfl) ⟨258693, by rfl⟩ : syracuseStep 689849 = 517387) B517387
theorem B263867 : Blo 263822 263867 := bstep (se 1 (by rfl) ⟨197900, by rfl⟩ : syracuseStep 263867 = 395801) B395801
theorem B1279745 : Blo 263822 1279745 := bstep (se 2 (by rfl) ⟨479904, by rfl⟩ : syracuseStep 1279745 = 959809) B959809
theorem B263943 : Blo 263822 263943 := bstep (se 1 (by rfl) ⟨197957, by rfl⟩ : syracuseStep 263943 = 395915) B395915
theorem B263951 : Blo 263822 263951 := bstep (se 1 (by rfl) ⟨197963, by rfl⟩ : syracuseStep 263951 = 395927) B395927
theorem B2033423 : Blo 263822 2033423 := bstep (se 1 (by rfl) ⟨1525067, by rfl⟩ : syracuseStep 2033423 = 3050135) B3050135
theorem B263995 : Blo 263822 263995 := bstep (se 1 (by rfl) ⟨197996, by rfl⟩ : syracuseStep 263995 = 395993) B395993
theorem B264071 : Blo 263822 264071 := bstep (se 1 (by rfl) ⟨198053, by rfl⟩ : syracuseStep 264071 = 396107) B396107
theorem B264079 : Blo 263822 264079 := bstep (se 1 (by rfl) ⟨198059, by rfl⟩ : syracuseStep 264079 = 396119) B396119
theorem B3016601 : Blo 263822 3016601 := bstep (se 2 (by rfl) ⟨1131225, by rfl⟩ : syracuseStep 3016601 = 2262451) B2262451
theorem B264123 : Blo 263822 264123 := bstep (se 1 (by rfl) ⟨198092, by rfl⟩ : syracuseStep 264123 = 396185) B396185
theorem B264199 : Blo 263822 264199 := bstep (se 1 (by rfl) ⟨198149, by rfl⟩ : syracuseStep 264199 = 396299) B396299
theorem B755723 : Blo 263822 755723 := bstep (se 1 (by rfl) ⟨566792, by rfl⟩ : syracuseStep 755723 = 1133585) B1133585
theorem B264207 : Blo 263822 264207 := bstep (se 1 (by rfl) ⟨198155, by rfl⟩ : syracuseStep 264207 = 396311) B396311
theorem B264251 : Blo 263822 264251 := bstep (se 1 (by rfl) ⟨198188, by rfl⟩ : syracuseStep 264251 = 396377) B396377
theorem B264327 : Blo 263822 264327 := bstep (se 1 (by rfl) ⟨198245, by rfl⟩ : syracuseStep 264327 = 396491) B396491
theorem B297103 : Blo 263822 297103 := bstep (se 1 (by rfl) ⟨222827, by rfl⟩ : syracuseStep 297103 = 445655) B445655
theorem B264335 : Blo 263822 264335 := bstep (se 1 (by rfl) ⟨198251, by rfl⟩ : syracuseStep 264335 = 396503) B396503
theorem B264379 : Blo 263822 264379 := bstep (se 1 (by rfl) ⟨198284, by rfl⟩ : syracuseStep 264379 = 396569) B396569
theorem B264455 : Blo 263822 264455 := bstep (se 1 (by rfl) ⟨198341, by rfl⟩ : syracuseStep 264455 = 396683) B396683
theorem B264463 : Blo 263822 264463 := bstep (se 1 (by rfl) ⟨198347, by rfl⟩ : syracuseStep 264463 = 396695) B396695
theorem B461099 : Blo 263822 461099 := bstep (se 1 (by rfl) ⟨345824, by rfl⟩ : syracuseStep 461099 = 691649) B691649
theorem B264507 : Blo 263822 264507 := bstep (se 1 (by rfl) ⟨198380, by rfl⟩ : syracuseStep 264507 = 396761) B396761
theorem B264583 : Blo 263822 264583 := bstep (se 1 (by rfl) ⟨198437, by rfl⟩ : syracuseStep 264583 = 396875) B396875
theorem B264591 : Blo 263822 264591 := bstep (se 1 (by rfl) ⟨198443, by rfl⟩ : syracuseStep 264591 = 396887) B396887
theorem B264635 : Blo 263822 264635 := bstep (se 1 (by rfl) ⟨198476, by rfl⟩ : syracuseStep 264635 = 396953) B396953
theorem B395783 : Blo 263822 395783 := bstep (se 1 (by rfl) ⟨296837, by rfl⟩ : syracuseStep 395783 = 593675) B593675
theorem B264711 : Blo 263822 264711 := bstep (se 1 (by rfl) ⟨198533, by rfl⟩ : syracuseStep 264711 = 397067) B397067
theorem B723467 : Blo 263822 723467 := bstep (se 1 (by rfl) ⟨542600, by rfl⟩ : syracuseStep 723467 = 1085201) B1085201
theorem B264719 : Blo 263822 264719 := bstep (se 1 (by rfl) ⟨198539, by rfl⟩ : syracuseStep 264719 = 397079) B397079
theorem B395819 : Blo 263822 395819 := bstep (se 1 (by rfl) ⟨296864, by rfl⟩ : syracuseStep 395819 = 593729) B593729
theorem B264763 : Blo 263822 264763 := bstep (se 1 (by rfl) ⟨198572, by rfl⟩ : syracuseStep 264763 = 397145) B397145
theorem B395849 : Blo 263822 395849 := bstep (se 2 (by rfl) ⟨148443, by rfl⟩ : syracuseStep 395849 = 296887) B296887
theorem B297607 : Blo 263822 297607 := bstep (se 1 (by rfl) ⟨223205, by rfl⟩ : syracuseStep 297607 = 446411) B446411
theorem B264839 : Blo 263822 264839 := bstep (se 1 (by rfl) ⟨198629, by rfl⟩ : syracuseStep 264839 = 397259) B397259
theorem B264847 : Blo 263822 264847 := bstep (se 1 (by rfl) ⟨198635, by rfl⟩ : syracuseStep 264847 = 397271) B397271
theorem B395963 : Blo 263822 395963 := bstep (se 1 (by rfl) ⟨296972, by rfl⟩ : syracuseStep 395963 = 593945) B593945
theorem B264891 : Blo 263822 264891 := bstep (se 1 (by rfl) ⟨198668, by rfl⟩ : syracuseStep 264891 = 397337) B397337
theorem B396023 : Blo 263822 396023 := bstep (se 1 (by rfl) ⟨297017, by rfl⟩ : syracuseStep 396023 = 594035) B594035
theorem B264967 : Blo 263822 264967 := bstep (se 1 (by rfl) ⟨198725, by rfl⟩ : syracuseStep 264967 = 397451) B397451
theorem B396047 : Blo 263822 396047 := bstep (se 1 (by rfl) ⟨297035, by rfl⟩ : syracuseStep 396047 = 594071) B594071
theorem B1018639 : Blo 263822 1018639 := bstep (se 1 (by rfl) ⟨763979, by rfl⟩ : syracuseStep 1018639 = 1527959) B1527959
theorem B264975 : Blo 263822 264975 := bstep (se 1 (by rfl) ⟨198731, by rfl⟩ : syracuseStep 264975 = 397463) B397463
theorem B1903409 : Blo 263822 1903409 := bstep (se 2 (by rfl) ⟨713778, by rfl⟩ : syracuseStep 1903409 = 1427557) B1427557
theorem B396089 : Blo 263822 396089 := bstep (se 2 (by rfl) ⟨148533, by rfl⟩ : syracuseStep 396089 = 297067) B297067
theorem B297787 : Blo 263822 297787 := bstep (se 1 (by rfl) ⟨223340, by rfl⟩ : syracuseStep 297787 = 446681) B446681
theorem B265019 : Blo 263822 265019 := bstep (se 1 (by rfl) ⟨198764, by rfl⟩ : syracuseStep 265019 = 397529) B397529
theorem B396167 : Blo 263822 396167 := bstep (se 1 (by rfl) ⟨297125, by rfl⟩ : syracuseStep 396167 = 594251) B594251
theorem B265095 : Blo 263822 265095 := bstep (se 1 (by rfl) ⟨198821, by rfl⟩ : syracuseStep 265095 = 397643) B397643
theorem B265103 : Blo 263822 265103 := bstep (se 1 (by rfl) ⟨198827, by rfl⟩ : syracuseStep 265103 = 397655) B397655
theorem B396203 : Blo 263822 396203 := bstep (se 1 (by rfl) ⟨297152, by rfl⟩ : syracuseStep 396203 = 594305) B594305
theorem B265147 : Blo 263822 265147 := bstep (se 1 (by rfl) ⟨198860, by rfl⟩ : syracuseStep 265147 = 397721) B397721
theorem B396233 : Blo 263822 396233 := bstep (se 2 (by rfl) ⟨148587, by rfl⟩ : syracuseStep 396233 = 297175) B297175
theorem B265223 : Blo 263822 265223 := bstep (se 1 (by rfl) ⟨198917, by rfl⟩ : syracuseStep 265223 = 397835) B397835
theorem B265231 : Blo 263822 265231 := bstep (se 1 (by rfl) ⟨198923, by rfl⟩ : syracuseStep 265231 = 397847) B397847
theorem B855083 : Blo 263822 855083 := bstep (se 1 (by rfl) ⟨641312, by rfl⟩ : syracuseStep 855083 = 1282625) B1282625
theorem B396347 : Blo 263822 396347 := bstep (se 1 (by rfl) ⟨297260, by rfl⟩ : syracuseStep 396347 = 594521) B594521
theorem B265275 : Blo 263822 265275 := bstep (se 1 (by rfl) ⟨198956, by rfl⟩ : syracuseStep 265275 = 397913) B397913
theorem B12946493 : Blo 263822 12946493 := bstep (se 3 (by rfl) ⟨2427467, by rfl⟩ : syracuseStep 12946493 = 4854935) B4854935
theorem B396407 : Blo 263822 396407 := bstep (se 1 (by rfl) ⟨297305, by rfl⟩ : syracuseStep 396407 = 594611) B594611
theorem B265351 : Blo 263822 265351 := bstep (se 1 (by rfl) ⟨199013, by rfl⟩ : syracuseStep 265351 = 398027) B398027
theorem B396431 : Blo 263822 396431 := bstep (se 1 (by rfl) ⟨297323, by rfl⟩ : syracuseStep 396431 = 594647) B594647
theorem B265359 : Blo 263822 265359 := bstep (se 1 (by rfl) ⟨199019, by rfl⟩ : syracuseStep 265359 = 398039) B398039
theorem B396473 : Blo 263822 396473 := bstep (se 2 (by rfl) ⟨148677, by rfl⟩ : syracuseStep 396473 = 297355) B297355
theorem B265403 : Blo 263822 265403 := bstep (se 1 (by rfl) ⟨199052, by rfl⟩ : syracuseStep 265403 = 398105) B398105
theorem B396551 : Blo 263822 396551 := bstep (se 1 (by rfl) ⟨297413, by rfl⟩ : syracuseStep 396551 = 594827) B594827
theorem B265479 : Blo 263822 265479 := bstep (se 1 (by rfl) ⟨199109, by rfl⟩ : syracuseStep 265479 = 398219) B398219
theorem B298255 : Blo 263822 298255 := bstep (se 1 (by rfl) ⟨223691, by rfl⟩ : syracuseStep 298255 = 447383) B447383
theorem B265487 : Blo 263822 265487 := bstep (se 1 (by rfl) ⟨199115, by rfl⟩ : syracuseStep 265487 = 398231) B398231
theorem B757021 : Blo 263822 757021 := bstep (se 3 (by rfl) ⟨141941, by rfl⟩ : syracuseStep 757021 = 283883) B283883
theorem B396587 : Blo 263822 396587 := bstep (se 1 (by rfl) ⟨297440, by rfl⟩ : syracuseStep 396587 = 594881) B594881
theorem B1346867 : Blo 263822 1346867 := bstep (se 1 (by rfl) ⟨1010150, by rfl⟩ : syracuseStep 1346867 = 2020301) B2020301
theorem B265531 : Blo 263822 265531 := bstep (se 1 (by rfl) ⟨199148, by rfl⟩ : syracuseStep 265531 = 398297) B398297
theorem B396617 : Blo 263822 396617 := bstep (se 2 (by rfl) ⟨148731, by rfl⟩ : syracuseStep 396617 = 297463) B297463
theorem B1281395 : Blo 263822 1281395 := bstep (se 1 (by rfl) ⟨961046, by rfl⟩ : syracuseStep 1281395 = 1922093) B1922093
theorem B265607 : Blo 263822 265607 := bstep (se 1 (by rfl) ⟨199205, by rfl⟩ : syracuseStep 265607 = 398411) B398411
theorem B265615 : Blo 263822 265615 := bstep (se 1 (by rfl) ⟨199211, by rfl⟩ : syracuseStep 265615 = 398423) B398423
theorem B396731 : Blo 263822 396731 := bstep (se 1 (by rfl) ⟨297548, by rfl⟩ : syracuseStep 396731 = 595097) B595097
theorem B265659 : Blo 263822 265659 := bstep (se 1 (by rfl) ⟨199244, by rfl⟩ : syracuseStep 265659 = 398489) B398489
theorem B396791 : Blo 263822 396791 := bstep (se 1 (by rfl) ⟨297593, by rfl⟩ : syracuseStep 396791 = 595187) B595187
theorem B265735 : Blo 263822 265735 := bstep (se 1 (by rfl) ⟨199301, by rfl⟩ : syracuseStep 265735 = 398603) B398603
theorem B396815 : Blo 263822 396815 := bstep (se 1 (by rfl) ⟨297611, by rfl⟩ : syracuseStep 396815 = 595223) B595223
theorem B265743 : Blo 263822 265743 := bstep (se 1 (by rfl) ⟨199307, by rfl⟩ : syracuseStep 265743 = 398615) B398615
theorem B396857 : Blo 263822 396857 := bstep (se 2 (by rfl) ⟨148821, by rfl⟩ : syracuseStep 396857 = 297643) B297643
theorem B265787 : Blo 263822 265787 := bstep (se 1 (by rfl) ⟨199340, by rfl⟩ : syracuseStep 265787 = 398681) B398681
theorem B364105 : Blo 263822 364105 := bstep (se 2 (by rfl) ⟨136539, by rfl⟩ : syracuseStep 364105 = 273079) B273079
theorem B757363 : Blo 263822 757363 := bstep (se 1 (by rfl) ⟨568022, by rfl⟩ : syracuseStep 757363 = 1136045) B1136045
theorem B1347191 : Blo 263822 1347191 := bstep (se 1 (by rfl) ⟨1010393, by rfl⟩ : syracuseStep 1347191 = 2020787) B2020787
theorem B396935 : Blo 263822 396935 := bstep (se 1 (by rfl) ⟨297701, by rfl⟩ : syracuseStep 396935 = 595403) B595403
theorem B265863 : Blo 263822 265863 := bstep (se 1 (by rfl) ⟨199397, by rfl⟩ : syracuseStep 265863 = 398795) B398795
theorem B265871 : Blo 263822 265871 := bstep (se 1 (by rfl) ⟨199403, by rfl⟩ : syracuseStep 265871 = 398807) B398807
theorem B396971 : Blo 263822 396971 := bstep (se 1 (by rfl) ⟨297728, by rfl⟩ : syracuseStep 396971 = 595457) B595457
theorem B265915 : Blo 263822 265915 := bstep (se 1 (by rfl) ⟨199436, by rfl⟩ : syracuseStep 265915 = 398873) B398873
theorem B397001 : Blo 263822 397001 := bstep (se 2 (by rfl) ⟨148875, by rfl⟩ : syracuseStep 397001 = 297751) B297751
theorem B1969921 : Blo 263822 1969921 := bstep (se 2 (by rfl) ⟨738720, by rfl⟩ : syracuseStep 1969921 = 1477441) B1477441
theorem B298759 : Blo 263822 298759 := bstep (se 1 (by rfl) ⟨224069, by rfl⟩ : syracuseStep 298759 = 448139) B448139
theorem B265991 : Blo 263822 265991 := bstep (se 1 (by rfl) ⟨199493, by rfl⟩ : syracuseStep 265991 = 398987) B398987
theorem B265999 : Blo 263822 265999 := bstep (se 1 (by rfl) ⟨199499, by rfl⟩ : syracuseStep 265999 = 398999) B398999
theorem B397115 : Blo 263822 397115 := bstep (se 1 (by rfl) ⟨297836, by rfl⟩ : syracuseStep 397115 = 595673) B595673
theorem B266043 : Blo 263822 266043 := bstep (se 1 (by rfl) ⟨199532, by rfl⟩ : syracuseStep 266043 = 399065) B399065
theorem B593783 : Blo 263822 593783 := bstep (se 1 (by rfl) ⟨445337, by rfl⟩ : syracuseStep 593783 = 890675) B890675
theorem B397175 : Blo 263822 397175 := bstep (se 1 (by rfl) ⟨297881, by rfl⟩ : syracuseStep 397175 = 595763) B595763
theorem B266119 : Blo 263822 266119 := bstep (se 1 (by rfl) ⟨199589, by rfl⟩ : syracuseStep 266119 = 399179) B399179
theorem B397199 : Blo 263822 397199 := bstep (se 1 (by rfl) ⟨297899, by rfl⟩ : syracuseStep 397199 = 595799) B595799
theorem B266127 : Blo 263822 266127 := bstep (se 1 (by rfl) ⟨199595, by rfl⟩ : syracuseStep 266127 = 399191) B399191
theorem B397241 : Blo 263822 397241 := bstep (se 2 (by rfl) ⟨148965, by rfl⟩ : syracuseStep 397241 = 297931) B297931
theorem B298939 : Blo 263822 298939 := bstep (se 1 (by rfl) ⟨224204, by rfl⟩ : syracuseStep 298939 = 448409) B448409
theorem B266171 : Blo 263822 266171 := bstep (se 1 (by rfl) ⟨199628, by rfl⟩ : syracuseStep 266171 = 399257) B399257
theorem B397319 : Blo 263822 397319 := bstep (se 1 (by rfl) ⟨297989, by rfl⟩ : syracuseStep 397319 = 595979) B595979
theorem B266247 : Blo 263822 266247 := bstep (se 1 (by rfl) ⟨199685, by rfl⟩ : syracuseStep 266247 = 399371) B399371
theorem B266255 : Blo 263822 266255 := bstep (se 1 (by rfl) ⟨199691, by rfl⟩ : syracuseStep 266255 = 399383) B399383
theorem B593963 : Blo 263822 593963 := bstep (se 1 (by rfl) ⟨445472, by rfl⟩ : syracuseStep 593963 = 890945) B890945
theorem B397355 : Blo 263822 397355 := bstep (se 1 (by rfl) ⟨298016, by rfl⟩ : syracuseStep 397355 = 596033) B596033
theorem B266299 : Blo 263822 266299 := bstep (se 1 (by rfl) ⟨199724, by rfl⟩ : syracuseStep 266299 = 399449) B399449
theorem B397385 : Blo 263822 397385 := bstep (se 2 (by rfl) ⟨149019, by rfl⟩ : syracuseStep 397385 = 298039) B298039
theorem B6951005 : Blo 263822 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B266375 : Blo 263822 266375 := bstep (se 1 (by rfl) ⟨199781, by rfl⟩ : syracuseStep 266375 = 399563) B399563
theorem B266383 : Blo 263822 266383 := bstep (se 1 (by rfl) ⟨199787, by rfl⟩ : syracuseStep 266383 = 399575) B399575
theorem B397499 : Blo 263822 397499 := bstep (se 1 (by rfl) ⟨298124, by rfl⟩ : syracuseStep 397499 = 596249) B596249
theorem B266427 : Blo 263822 266427 := bstep (se 1 (by rfl) ⟨199820, by rfl⟩ : syracuseStep 266427 = 399641) B399641
theorem B397559 : Blo 263822 397559 := bstep (se 1 (by rfl) ⟨298169, by rfl⟩ : syracuseStep 397559 = 596339) B596339
theorem B266503 : Blo 263822 266503 := bstep (se 1 (by rfl) ⟨199877, by rfl⟩ : syracuseStep 266503 = 399755) B399755
theorem B397583 : Blo 263822 397583 := bstep (se 1 (by rfl) ⟨298187, by rfl⟩ : syracuseStep 397583 = 596375) B596375
theorem B266511 : Blo 263822 266511 := bstep (se 1 (by rfl) ⟨199883, by rfl⟩ : syracuseStep 266511 = 399767) B399767
theorem B397625 : Blo 263822 397625 := bstep (se 2 (by rfl) ⟨149109, by rfl⟩ : syracuseStep 397625 = 298219) B298219
theorem B266555 : Blo 263822 266555 := bstep (se 1 (by rfl) ⟨199916, by rfl⟩ : syracuseStep 266555 = 399833) B399833
theorem B397703 : Blo 263822 397703 := bstep (se 1 (by rfl) ⟨298277, by rfl⟩ : syracuseStep 397703 = 596555) B596555
theorem B266631 : Blo 263822 266631 := bstep (se 1 (by rfl) ⟨199973, by rfl⟩ : syracuseStep 266631 = 399947) B399947
theorem B299407 : Blo 263822 299407 := bstep (se 1 (by rfl) ⟨224555, by rfl⟩ : syracuseStep 299407 = 449111) B449111
theorem B266639 : Blo 263822 266639 := bstep (se 1 (by rfl) ⟨199979, by rfl⟩ : syracuseStep 266639 = 399959) B399959
theorem B594323 : Blo 263822 594323 := bstep (se 1 (by rfl) ⟨445742, by rfl⟩ : syracuseStep 594323 = 891485) B891485
theorem B397739 : Blo 263822 397739 := bstep (se 1 (by rfl) ⟨298304, by rfl⟩ : syracuseStep 397739 = 596609) B596609
theorem B266683 : Blo 263822 266683 := bstep (se 1 (by rfl) ⟨200012, by rfl⟩ : syracuseStep 266683 = 400025) B400025
theorem B594377 : Blo 263822 594377 := bstep (se 2 (by rfl) ⟨222891, by rfl⟩ : syracuseStep 594377 = 445783) B445783
theorem B397769 : Blo 263822 397769 := bstep (se 2 (by rfl) ⟨149163, by rfl⟩ : syracuseStep 397769 = 298327) B298327
theorem B266759 : Blo 263822 266759 := bstep (se 1 (by rfl) ⟨200069, by rfl⟩ : syracuseStep 266759 = 400139) B400139
theorem B266767 : Blo 263822 266767 := bstep (se 1 (by rfl) ⟨200075, by rfl⟩ : syracuseStep 266767 = 400151) B400151
theorem B397883 : Blo 263822 397883 := bstep (se 1 (by rfl) ⟨298412, by rfl⟩ : syracuseStep 397883 = 596825) B596825
theorem B266811 : Blo 263822 266811 := bstep (se 1 (by rfl) ⟨200108, by rfl⟩ : syracuseStep 266811 = 400217) B400217
theorem B1348163 : Blo 263822 1348163 := bstep (se 1 (by rfl) ⟨1011122, by rfl⟩ : syracuseStep 1348163 = 2022245) B2022245
theorem B397943 : Blo 263822 397943 := bstep (se 1 (by rfl) ⟨298457, by rfl⟩ : syracuseStep 397943 = 596915) B596915
theorem B266887 : Blo 263822 266887 := bstep (se 1 (by rfl) ⟨200165, by rfl⟩ : syracuseStep 266887 = 400331) B400331
theorem B397967 : Blo 263822 397967 := bstep (se 1 (by rfl) ⟨298475, by rfl⟩ : syracuseStep 397967 = 596951) B596951
theorem B266895 : Blo 263822 266895 := bstep (se 1 (by rfl) ⟨200171, by rfl⟩ : syracuseStep 266895 = 400343) B400343
theorem B398009 : Blo 263822 398009 := bstep (se 2 (by rfl) ⟨149253, by rfl⟩ : syracuseStep 398009 = 298507) B298507
theorem B266939 : Blo 263822 266939 := bstep (se 1 (by rfl) ⟨200204, by rfl⟩ : syracuseStep 266939 = 400409) B400409
theorem B398087 : Blo 263822 398087 := bstep (se 1 (by rfl) ⟨298565, by rfl⟩ : syracuseStep 398087 = 597131) B597131
theorem B267015 : Blo 263822 267015 := bstep (se 1 (by rfl) ⟨200261, by rfl⟩ : syracuseStep 267015 = 400523) B400523
theorem B267023 : Blo 263822 267023 := bstep (se 1 (by rfl) ⟨200267, by rfl⟩ : syracuseStep 267023 = 400535) B400535
theorem B398123 : Blo 263822 398123 := bstep (se 1 (by rfl) ⟨298592, by rfl⟩ : syracuseStep 398123 = 597185) B597185
theorem B1020731 : Blo 263822 1020731 := bstep (se 1 (by rfl) ⟨765548, by rfl⟩ : syracuseStep 1020731 = 1531097) B1531097
theorem B267067 : Blo 263822 267067 := bstep (se 1 (by rfl) ⟨200300, by rfl⟩ : syracuseStep 267067 = 400601) B400601
theorem B398153 : Blo 263822 398153 := bstep (se 2 (by rfl) ⟨149307, by rfl⟩ : syracuseStep 398153 = 298615) B298615
theorem B693107 : Blo 263822 693107 := bstep (se 1 (by rfl) ⟨519830, by rfl⟩ : syracuseStep 693107 = 1039661) B1039661
theorem B1348487 : Blo 263822 1348487 := bstep (se 1 (by rfl) ⟨1011365, by rfl⟩ : syracuseStep 1348487 = 2022731) B2022731
theorem B299911 : Blo 263822 299911 := bstep (se 1 (by rfl) ⟨224933, by rfl⟩ : syracuseStep 299911 = 449867) B449867
theorem B267143 : Blo 263822 267143 := bstep (se 1 (by rfl) ⟨200357, by rfl⟩ : syracuseStep 267143 = 400715) B400715
theorem B267151 : Blo 263822 267151 := bstep (se 1 (by rfl) ⟨200363, by rfl⟩ : syracuseStep 267151 = 400727) B400727
theorem B398267 : Blo 263822 398267 := bstep (se 1 (by rfl) ⟨298700, by rfl⟩ : syracuseStep 398267 = 597401) B597401
theorem B267195 : Blo 263822 267195 := bstep (se 1 (by rfl) ⟨200396, by rfl⟩ : syracuseStep 267195 = 400793) B400793
theorem B398327 : Blo 263822 398327 := bstep (se 1 (by rfl) ⟨298745, by rfl⟩ : syracuseStep 398327 = 597491) B597491
theorem B267271 : Blo 263822 267271 := bstep (se 1 (by rfl) ⟨200453, by rfl⟩ : syracuseStep 267271 = 400907) B400907
theorem B398351 : Blo 263822 398351 := bstep (se 1 (by rfl) ⟨298763, by rfl⟩ : syracuseStep 398351 = 597527) B597527
theorem B267279 : Blo 263822 267279 := bstep (se 1 (by rfl) ⟨200459, by rfl⟩ : syracuseStep 267279 = 400919) B400919
theorem B398393 : Blo 263822 398393 := bstep (se 2 (by rfl) ⟨149397, by rfl⟩ : syracuseStep 398393 = 298795) B298795
theorem B300091 : Blo 263822 300091 := bstep (se 1 (by rfl) ⟨225068, by rfl⟩ : syracuseStep 300091 = 450137) B450137
theorem B267323 : Blo 263822 267323 := bstep (se 1 (by rfl) ⟨200492, by rfl⟩ : syracuseStep 267323 = 400985) B400985
theorem B595079 : Blo 263822 595079 := bstep (se 1 (by rfl) ⟨446309, by rfl⟩ : syracuseStep 595079 = 892619) B892619
theorem B398471 : Blo 263822 398471 := bstep (se 1 (by rfl) ⟨298853, by rfl⟩ : syracuseStep 398471 = 597707) B597707
theorem B267399 : Blo 263822 267399 := bstep (se 1 (by rfl) ⟨200549, by rfl⟩ : syracuseStep 267399 = 401099) B401099
theorem B267407 : Blo 263822 267407 := bstep (se 1 (by rfl) ⟨200555, by rfl⟩ : syracuseStep 267407 = 401111) B401111
theorem B398507 : Blo 263822 398507 := bstep (se 1 (by rfl) ⟨298880, by rfl⟩ : syracuseStep 398507 = 597761) B597761
theorem B267451 : Blo 263822 267451 := bstep (se 1 (by rfl) ⟨200588, by rfl⟩ : syracuseStep 267451 = 401177) B401177
theorem B398537 : Blo 263822 398537 := bstep (se 2 (by rfl) ⟨149451, by rfl⟩ : syracuseStep 398537 = 298903) B298903
theorem B267527 : Blo 263822 267527 := bstep (se 1 (by rfl) ⟨200645, by rfl⟩ : syracuseStep 267527 = 401291) B401291
theorem B267535 : Blo 263822 267535 := bstep (se 1 (by rfl) ⟨200651, by rfl⟩ : syracuseStep 267535 = 401303) B401303
theorem B1217825 : Blo 263822 1217825 := bstep (se 2 (by rfl) ⟨456684, by rfl⟩ : syracuseStep 1217825 = 913369) B913369
theorem B595259 : Blo 263822 595259 := bstep (se 1 (by rfl) ⟨446444, by rfl⟩ : syracuseStep 595259 = 892889) B892889
theorem B398651 : Blo 263822 398651 := bstep (se 1 (by rfl) ⟨298988, by rfl⟩ : syracuseStep 398651 = 597977) B597977
theorem B267579 : Blo 263822 267579 := bstep (se 1 (by rfl) ⟨200684, by rfl⟩ : syracuseStep 267579 = 401369) B401369
theorem B398711 : Blo 263822 398711 := bstep (se 1 (by rfl) ⟨299033, by rfl⟩ : syracuseStep 398711 = 598067) B598067
theorem B267655 : Blo 263822 267655 := bstep (se 1 (by rfl) ⟨200741, by rfl⟩ : syracuseStep 267655 = 401483) B401483
theorem B398735 : Blo 263822 398735 := bstep (se 1 (by rfl) ⟨299051, by rfl⟩ : syracuseStep 398735 = 598103) B598103
theorem B267663 : Blo 263822 267663 := bstep (se 1 (by rfl) ⟨200747, by rfl⟩ : syracuseStep 267663 = 401495) B401495
theorem B1512857 : Blo 263822 1512857 := bstep (se 2 (by rfl) ⟨567321, by rfl⟩ : syracuseStep 1512857 = 1134643) B1134643
theorem B595385 : Blo 263822 595385 := bstep (se 2 (by rfl) ⟨223269, by rfl⟩ : syracuseStep 595385 = 446539) B446539
theorem B398777 : Blo 263822 398777 := bstep (se 2 (by rfl) ⟨149541, by rfl⟩ : syracuseStep 398777 = 299083) B299083
theorem B267707 : Blo 263822 267707 := bstep (se 1 (by rfl) ⟨200780, by rfl⟩ : syracuseStep 267707 = 401561) B401561
theorem B398855 : Blo 263822 398855 := bstep (se 1 (by rfl) ⟨299141, by rfl⟩ : syracuseStep 398855 = 598283) B598283
theorem B267783 : Blo 263822 267783 := bstep (se 1 (by rfl) ⟨200837, by rfl⟩ : syracuseStep 267783 = 401675) B401675
theorem B300559 : Blo 263822 300559 := bstep (se 1 (by rfl) ⟨225419, by rfl⟩ : syracuseStep 300559 = 450839) B450839
theorem B267791 : Blo 263822 267791 := bstep (se 1 (by rfl) ⟨200843, by rfl⟩ : syracuseStep 267791 = 401687) B401687
theorem B398891 : Blo 263822 398891 := bstep (se 1 (by rfl) ⟨299168, by rfl⟩ : syracuseStep 398891 = 598337) B598337
theorem B398921 : Blo 263822 398921 := bstep (se 2 (by rfl) ⟨149595, by rfl⟩ : syracuseStep 398921 = 299191) B299191
theorem B399035 : Blo 263822 399035 := bstep (se 1 (by rfl) ⟨299276, by rfl⟩ : syracuseStep 399035 = 598553) B598553
theorem B399095 : Blo 263822 399095 := bstep (se 1 (by rfl) ⟨299321, by rfl⟩ : syracuseStep 399095 = 598643) B598643
theorem B595727 : Blo 263822 595727 := bstep (se 1 (by rfl) ⟨446795, by rfl⟩ : syracuseStep 595727 = 893591) B893591
theorem B399119 : Blo 263822 399119 := bstep (se 1 (by rfl) ⟨299339, by rfl⟩ : syracuseStep 399119 = 598679) B598679
theorem B595745 : Blo 263822 595745 := bstep (se 2 (by rfl) ⟨223404, by rfl⟩ : syracuseStep 595745 = 446809) B446809
theorem B399161 : Blo 263822 399161 := bstep (se 2 (by rfl) ⟨149685, by rfl⟩ : syracuseStep 399161 = 299371) B299371
theorem B2561867 : Blo 263822 2561867 := bstep (se 1 (by rfl) ⟨1921400, by rfl⟩ : syracuseStep 2561867 = 3842801) B3842801
theorem B399239 : Blo 263822 399239 := bstep (se 1 (by rfl) ⟨299429, by rfl⟩ : syracuseStep 399239 = 598859) B598859
theorem B399275 : Blo 263822 399275 := bstep (se 1 (by rfl) ⟨299456, by rfl⟩ : syracuseStep 399275 = 598913) B598913
theorem B268219 : Blo 263822 268219 := bstep (se 1 (by rfl) ⟨201164, by rfl⟩ : syracuseStep 268219 = 402329) B402329
theorem B399305 : Blo 263822 399305 := bstep (se 2 (by rfl) ⟨149739, by rfl⟩ : syracuseStep 399305 = 299479) B299479
theorem B301063 : Blo 263822 301063 := bstep (se 1 (by rfl) ⟨225797, by rfl⟩ : syracuseStep 301063 = 451595) B451595
theorem B890891 : Blo 263822 890891 := bstep (se 1 (by rfl) ⟨668168, by rfl⟩ : syracuseStep 890891 = 1336337) B1336337
theorem B1906699 : Blo 263822 1906699 := bstep (se 1 (by rfl) ⟨1430024, by rfl⟩ : syracuseStep 1906699 = 2860049) B2860049
theorem B399419 : Blo 263822 399419 := bstep (se 1 (by rfl) ⟨299564, by rfl⟩ : syracuseStep 399419 = 599129) B599129
theorem B890999 : Blo 263822 890999 := bstep (se 1 (by rfl) ⟨668249, by rfl⟩ : syracuseStep 890999 = 1336499) B1336499
theorem B596087 : Blo 263822 596087 := bstep (se 1 (by rfl) ⟨447065, by rfl⟩ : syracuseStep 596087 = 894131) B894131
theorem B399479 : Blo 263822 399479 := bstep (se 1 (by rfl) ⟨299609, by rfl⟩ : syracuseStep 399479 = 599219) B599219
theorem B399503 : Blo 263822 399503 := bstep (se 1 (by rfl) ⟨299627, by rfl⟩ : syracuseStep 399503 = 599255) B599255
theorem B399545 : Blo 263822 399545 := bstep (se 2 (by rfl) ⟨149829, by rfl⟩ : syracuseStep 399545 = 299659) B299659
theorem B301243 : Blo 263822 301243 := bstep (se 1 (by rfl) ⟨225932, by rfl⟩ : syracuseStep 301243 = 451865) B451865
theorem B5478641 : Blo 263822 5478641 := bstep (se 2 (by rfl) ⟨2054490, by rfl⟩ : syracuseStep 5478641 = 4108981) B4108981
theorem B399623 : Blo 263822 399623 := bstep (se 1 (by rfl) ⟨299717, by rfl⟩ : syracuseStep 399623 = 599435) B599435
theorem B760097 : Blo 263822 760097 := bstep (se 2 (by rfl) ⟨285036, by rfl⟩ : syracuseStep 760097 = 570073) B570073
theorem B596267 : Blo 263822 596267 := bstep (se 1 (by rfl) ⟨447200, by rfl⟩ : syracuseStep 596267 = 894401) B894401
theorem B399659 : Blo 263822 399659 := bstep (se 1 (by rfl) ⟨299744, by rfl⟩ : syracuseStep 399659 = 599489) B599489
theorem B399689 : Blo 263822 399689 := bstep (se 2 (by rfl) ⟨149883, by rfl⟩ : syracuseStep 399689 = 299767) B299767
theorem B760211 : Blo 263822 760211 := bstep (se 1 (by rfl) ⟨570158, by rfl⟩ : syracuseStep 760211 = 1140317) B1140317
theorem B14522773 : Blo 263822 14522773 := bstep (se 6 (by rfl) ⟨340377, by rfl⟩ : syracuseStep 14522773 = 680755) B680755
theorem B399803 : Blo 263822 399803 := bstep (se 1 (by rfl) ⟨299852, by rfl⟩ : syracuseStep 399803 = 599705) B599705
theorem B956881 : Blo 263822 956881 := bstep (se 2 (by rfl) ⟨358830, by rfl⟩ : syracuseStep 956881 = 717661) B717661
theorem B399863 : Blo 263822 399863 := bstep (se 1 (by rfl) ⟨299897, by rfl⟩ : syracuseStep 399863 = 599795) B599795
theorem B399887 : Blo 263822 399887 := bstep (se 1 (by rfl) ⟨299915, by rfl⟩ : syracuseStep 399887 = 599831) B599831
theorem B399929 : Blo 263822 399929 := bstep (se 2 (by rfl) ⟨149973, by rfl⟩ : syracuseStep 399929 = 299947) B299947
theorem B400007 : Blo 263822 400007 := bstep (se 1 (by rfl) ⟨300005, by rfl⟩ : syracuseStep 400007 = 600011) B600011
theorem B596627 : Blo 263822 596627 := bstep (se 1 (by rfl) ⟨447470, by rfl⟩ : syracuseStep 596627 = 894941) B894941
theorem B400043 : Blo 263822 400043 := bstep (se 1 (by rfl) ⟨300032, by rfl⟩ : syracuseStep 400043 = 600065) B600065
theorem B563897 : Blo 263822 563897 := bstep (se 2 (by rfl) ⟨211461, by rfl⟩ : syracuseStep 563897 = 422923) B422923
theorem B891593 : Blo 263822 891593 := bstep (se 2 (by rfl) ⟨334347, by rfl⟩ : syracuseStep 891593 = 668695) B668695
theorem B596681 : Blo 263822 596681 := bstep (se 2 (by rfl) ⟨223755, by rfl⟩ : syracuseStep 596681 = 447511) B447511
theorem B400073 : Blo 263822 400073 := bstep (se 2 (by rfl) ⟨150027, by rfl⟩ : syracuseStep 400073 = 300055) B300055
theorem B400187 : Blo 263822 400187 := bstep (se 1 (by rfl) ⟨300140, by rfl⟩ : syracuseStep 400187 = 600281) B600281
theorem B400247 : Blo 263822 400247 := bstep (se 1 (by rfl) ⟨300185, by rfl⟩ : syracuseStep 400247 = 600371) B600371
theorem B400271 : Blo 263822 400271 := bstep (se 1 (by rfl) ⟨300203, by rfl⟩ : syracuseStep 400271 = 600407) B600407
theorem B400313 : Blo 263822 400313 := bstep (se 2 (by rfl) ⟨150117, by rfl⟩ : syracuseStep 400313 = 300235) B300235
theorem B1285085 : Blo 263822 1285085 := bstep (se 3 (by rfl) ⟨240953, by rfl⟩ : syracuseStep 1285085 = 481907) B481907
theorem B400391 : Blo 263822 400391 := bstep (se 1 (by rfl) ⟨300293, by rfl⟩ : syracuseStep 400391 = 600587) B600587
theorem B564239 : Blo 263822 564239 := bstep (se 1 (by rfl) ⟨423179, by rfl⟩ : syracuseStep 564239 = 846359) B846359
theorem B400427 : Blo 263822 400427 := bstep (se 1 (by rfl) ⟨300320, by rfl⟩ : syracuseStep 400427 = 600641) B600641
theorem B400457 : Blo 263822 400457 := bstep (se 2 (by rfl) ⟨150171, by rfl⟩ : syracuseStep 400457 = 300343) B300343
theorem B760985 : Blo 263822 760985 := bstep (se 2 (by rfl) ⟨285369, by rfl⟩ : syracuseStep 760985 = 570739) B570739
theorem B400571 : Blo 263822 400571 := bstep (se 1 (by rfl) ⟨300428, by rfl⟩ : syracuseStep 400571 = 600857) B600857
theorem B400631 : Blo 263822 400631 := bstep (se 1 (by rfl) ⟨300473, by rfl⟩ : syracuseStep 400631 = 600947) B600947
theorem B400655 : Blo 263822 400655 := bstep (se 1 (by rfl) ⟨300491, by rfl⟩ : syracuseStep 400655 = 600983) B600983
theorem B400697 : Blo 263822 400697 := bstep (se 2 (by rfl) ⟨150261, by rfl⟩ : syracuseStep 400697 = 300523) B300523
theorem B892295 : Blo 263822 892295 := bstep (se 1 (by rfl) ⟨669221, by rfl⟩ : syracuseStep 892295 = 1338443) B1338443
theorem B597383 : Blo 263822 597383 := bstep (se 1 (by rfl) ⟨448037, by rfl⟩ : syracuseStep 597383 = 896075) B896075
theorem B6495623 : Blo 263822 6495623 := bstep (se 1 (by rfl) ⟨4871717, by rfl⟩ : syracuseStep 6495623 = 9743435) B9743435
theorem B400775 : Blo 263822 400775 := bstep (se 1 (by rfl) ⟨300581, by rfl⟩ : syracuseStep 400775 = 601163) B601163
theorem B400811 : Blo 263822 400811 := bstep (se 1 (by rfl) ⟨300608, by rfl⟩ : syracuseStep 400811 = 601217) B601217
theorem B400841 : Blo 263822 400841 := bstep (se 2 (by rfl) ⟨150315, by rfl⟩ : syracuseStep 400841 = 300631) B300631
theorem B597563 : Blo 263822 597563 := bstep (se 1 (by rfl) ⟨448172, by rfl⟩ : syracuseStep 597563 = 896345) B896345
theorem B400955 : Blo 263822 400955 := bstep (se 1 (by rfl) ⟨300716, by rfl⟩ : syracuseStep 400955 = 601433) B601433
theorem B401015 : Blo 263822 401015 := bstep (se 1 (by rfl) ⟨300761, by rfl⟩ : syracuseStep 401015 = 601523) B601523
theorem B401039 : Blo 263822 401039 := bstep (se 1 (by rfl) ⟨300779, by rfl⟩ : syracuseStep 401039 = 601559) B601559
theorem B597689 : Blo 263822 597689 := bstep (se 2 (by rfl) ⟨224133, by rfl⟩ : syracuseStep 597689 = 448267) B448267
theorem B401081 : Blo 263822 401081 := bstep (se 2 (by rfl) ⟨150405, by rfl⟩ : syracuseStep 401081 = 300811) B300811
theorem B892673 : Blo 263822 892673 := bstep (se 2 (by rfl) ⟨334752, by rfl⟩ : syracuseStep 892673 = 669505) B669505
theorem B401159 : Blo 263822 401159 := bstep (se 1 (by rfl) ⟨300869, by rfl⟩ : syracuseStep 401159 = 601739) B601739
theorem B335659 : Blo 263822 335659 := bstep (se 1 (by rfl) ⟨251744, by rfl⟩ : syracuseStep 335659 = 503489) B503489
theorem B401195 : Blo 263822 401195 := bstep (se 1 (by rfl) ⟨300896, by rfl⟩ : syracuseStep 401195 = 601793) B601793
theorem B401225 : Blo 263822 401225 := bstep (se 2 (by rfl) ⟨150459, by rfl⟩ : syracuseStep 401225 = 300919) B300919
theorem B565127 : Blo 263822 565127 := bstep (se 1 (by rfl) ⟨423845, by rfl⟩ : syracuseStep 565127 = 847691) B847691
theorem B401339 : Blo 263822 401339 := bstep (se 1 (by rfl) ⟨301004, by rfl⟩ : syracuseStep 401339 = 602009) B602009
theorem B401399 : Blo 263822 401399 := bstep (se 1 (by rfl) ⟨301049, by rfl⟩ : syracuseStep 401399 = 602099) B602099
theorem B729089 : Blo 263822 729089 := bstep (se 2 (by rfl) ⟨273408, by rfl⟩ : syracuseStep 729089 = 546817) B546817
theorem B598031 : Blo 263822 598031 := bstep (se 1 (by rfl) ⟨448523, by rfl⟩ : syracuseStep 598031 = 897047) B897047
theorem B401423 : Blo 263822 401423 := bstep (se 1 (by rfl) ⟨301067, by rfl⟩ : syracuseStep 401423 = 602135) B602135
theorem B598049 : Blo 263822 598049 := bstep (se 2 (by rfl) ⟨224268, by rfl⟩ : syracuseStep 598049 = 448537) B448537
theorem B401465 : Blo 263822 401465 := bstep (se 2 (by rfl) ⟨150549, by rfl⟩ : syracuseStep 401465 = 301099) B301099
theorem B401543 : Blo 263822 401543 := bstep (se 1 (by rfl) ⟨301157, by rfl⟩ : syracuseStep 401543 = 602315) B602315
theorem B401579 : Blo 263822 401579 := bstep (se 1 (by rfl) ⟨301184, by rfl⟩ : syracuseStep 401579 = 602369) B602369
theorem B401609 : Blo 263822 401609 := bstep (se 2 (by rfl) ⟨150603, by rfl⟩ : syracuseStep 401609 = 301207) B301207
theorem B565537 : Blo 263822 565537 := bstep (se 2 (by rfl) ⟨212076, by rfl⟩ : syracuseStep 565537 = 424153) B424153
theorem B401723 : Blo 263822 401723 := bstep (se 1 (by rfl) ⟨301292, by rfl⟩ : syracuseStep 401723 = 602585) B602585
theorem B1352051 : Blo 263822 1352051 := bstep (se 1 (by rfl) ⟨1014038, by rfl⟩ : syracuseStep 1352051 = 2028077) B2028077
theorem B598391 : Blo 263822 598391 := bstep (se 1 (by rfl) ⟨448793, by rfl⟩ : syracuseStep 598391 = 897587) B897587
theorem B1810973 : Blo 263822 1810973 := bstep (se 3 (by rfl) ⟨339557, by rfl⟩ : syracuseStep 1810973 = 679115) B679115
theorem B893483 : Blo 263822 893483 := bstep (se 1 (by rfl) ⟨670112, by rfl⟩ : syracuseStep 893483 = 1340225) B1340225
theorem B598571 : Blo 263822 598571 := bstep (se 1 (by rfl) ⟨448928, by rfl⟩ : syracuseStep 598571 = 897857) B897857
theorem B565879 : Blo 263822 565879 := bstep (se 1 (by rfl) ⟨424409, by rfl⟩ : syracuseStep 565879 = 848819) B848819
theorem B336631 : Blo 263822 336631 := bstep (se 1 (by rfl) ⟨252473, by rfl⟩ : syracuseStep 336631 = 504947) B504947
theorem B762625 : Blo 263822 762625 := bstep (se 2 (by rfl) ⟨285984, by rfl⟩ : syracuseStep 762625 = 571969) B571969
theorem B1352537 : Blo 263822 1352537 := bstep (se 2 (by rfl) ⟨507201, by rfl⟩ : syracuseStep 1352537 = 1014403) B1014403
theorem B598931 : Blo 263822 598931 := bstep (se 1 (by rfl) ⟨449198, by rfl⟩ : syracuseStep 598931 = 898397) B898397
theorem B598985 : Blo 263822 598985 := bstep (se 2 (by rfl) ⟨224619, by rfl⟩ : syracuseStep 598985 = 449239) B449239
theorem B762895 : Blo 263822 762895 := bstep (se 1 (by rfl) ⟨572171, by rfl⟩ : syracuseStep 762895 = 1144343) B1144343
theorem B1287191 : Blo 263822 1287191 := bstep (se 1 (by rfl) ⟨965393, by rfl⟩ : syracuseStep 1287191 = 1930787) B1930787
theorem B336955 : Blo 263822 336955 := bstep (se 1 (by rfl) ⟨252716, by rfl⟩ : syracuseStep 336955 = 505433) B505433
theorem B2008151 : Blo 263822 2008151 := bstep (se 1 (by rfl) ⟨1506113, by rfl⟩ : syracuseStep 2008151 = 3012227) B3012227
theorem B2893265 : Blo 263822 2893265 := bstep (se 2 (by rfl) ⟨1084974, by rfl⟩ : syracuseStep 2893265 = 2169949) B2169949
theorem B566843 : Blo 263822 566843 := bstep (se 1 (by rfl) ⟨425132, by rfl⟩ : syracuseStep 566843 = 850265) B850265
theorem B599687 : Blo 263822 599687 := bstep (se 1 (by rfl) ⟨449765, by rfl⟩ : syracuseStep 599687 = 899531) B899531
theorem B567083 : Blo 263822 567083 := bstep (se 1 (by rfl) ⟨425312, by rfl⟩ : syracuseStep 567083 = 850625) B850625
theorem B894779 : Blo 263822 894779 := bstep (se 1 (by rfl) ⟨671084, by rfl⟩ : syracuseStep 894779 = 1342169) B1342169
theorem B599867 : Blo 263822 599867 := bstep (se 1 (by rfl) ⟨449900, by rfl⟩ : syracuseStep 599867 = 899801) B899801
theorem B1025939 : Blo 263822 1025939 := bstep (se 1 (by rfl) ⟨769454, by rfl⟩ : syracuseStep 1025939 = 1538909) B1538909
theorem B501689 : Blo 263822 501689 := bstep (se 2 (by rfl) ⟨188133, by rfl⟩ : syracuseStep 501689 = 376267) B376267
theorem B599993 : Blo 263822 599993 := bstep (se 2 (by rfl) ⟨224997, by rfl⟩ : syracuseStep 599993 = 449995) B449995
theorem B403447 : Blo 263822 403447 := bstep (se 1 (by rfl) ⟨302585, by rfl⟩ : syracuseStep 403447 = 605171) B605171
theorem B337927 : Blo 263822 337927 := bstep (se 1 (by rfl) ⟨253445, by rfl⟩ : syracuseStep 337927 = 506891) B506891
theorem B1517687 : Blo 263822 1517687 := bstep (se 1 (by rfl) ⟨1138265, by rfl⟩ : syracuseStep 1517687 = 2276531) B2276531
theorem B502031 : Blo 263822 502031 := bstep (se 1 (by rfl) ⟨376523, by rfl⟩ : syracuseStep 502031 = 753047) B753047
theorem B600335 : Blo 263822 600335 := bstep (se 1 (by rfl) ⟨450251, by rfl⟩ : syracuseStep 600335 = 900503) B900503
theorem B895265 : Blo 263822 895265 := bstep (se 2 (by rfl) ⟨335724, by rfl⟩ : syracuseStep 895265 = 671449) B671449
theorem B600353 : Blo 263822 600353 := bstep (se 2 (by rfl) ⟨225132, by rfl⟩ : syracuseStep 600353 = 450265) B450265
theorem B567595 : Blo 263822 567595 := bstep (se 1 (by rfl) ⟨425696, by rfl⟩ : syracuseStep 567595 = 851393) B851393
theorem B1517939 : Blo 263822 1517939 := bstep (se 1 (by rfl) ⟨1138454, by rfl⟩ : syracuseStep 1517939 = 2276909) B2276909
theorem B338347 : Blo 263822 338347 := bstep (se 1 (by rfl) ⟨253760, by rfl⟩ : syracuseStep 338347 = 507521) B507521
theorem B600695 : Blo 263822 600695 := bstep (se 1 (by rfl) ⟨450521, by rfl⟩ : syracuseStep 600695 = 901043) B901043
theorem B338575 : Blo 263822 338575 := bstep (se 1 (by rfl) ⟨253931, by rfl⟩ : syracuseStep 338575 = 507863) B507863
theorem B600875 : Blo 263822 600875 := bstep (se 1 (by rfl) ⟨450656, by rfl⟩ : syracuseStep 600875 = 901313) B901313
theorem B895859 : Blo 263822 895859 := bstep (se 1 (by rfl) ⟨671894, by rfl⟩ : syracuseStep 895859 = 1343789) B1343789
theorem B1354643 : Blo 263822 1354643 := bstep (se 1 (by rfl) ⟨1015982, by rfl⟩ : syracuseStep 1354643 = 2031965) B2031965
theorem B2567173 : Blo 263822 2567173 := bstep (se 4 (by rfl) ⟨240672, by rfl⟩ : syracuseStep 2567173 = 481345) B481345
theorem B502843 : Blo 263822 502843 := bstep (se 1 (by rfl) ⟨377132, by rfl⟩ : syracuseStep 502843 = 754265) B754265
theorem B502919 : Blo 263822 502919 := bstep (se 1 (by rfl) ⟨377189, by rfl⟩ : syracuseStep 502919 = 754379) B754379
theorem B601235 : Blo 263822 601235 := bstep (se 1 (by rfl) ⟨450926, by rfl⟩ : syracuseStep 601235 = 901853) B901853
theorem B601289 : Blo 263822 601289 := bstep (se 2 (by rfl) ⟨225483, by rfl⟩ : syracuseStep 601289 = 450967) B450967
theorem B568723 : Blo 263822 568723 := bstep (se 1 (by rfl) ⟨426542, by rfl⟩ : syracuseStep 568723 = 853085) B853085
theorem B503329 : Blo 263822 503329 := bstep (se 2 (by rfl) ⟨188748, by rfl⟩ : syracuseStep 503329 = 377497) B377497
theorem B405065 : Blo 263822 405065 := bstep (se 2 (by rfl) ⟨151899, by rfl⟩ : syracuseStep 405065 = 303799) B303799
theorem B1519397 : Blo 263822 1519397 := bstep (se 4 (by rfl) ⟨142443, by rfl⟩ : syracuseStep 1519397 = 284887) B284887
theorem B503671 : Blo 263822 503671 := bstep (se 1 (by rfl) ⟨377753, by rfl⟩ : syracuseStep 503671 = 755507) B755507
theorem B601991 : Blo 263822 601991 := bstep (se 1 (by rfl) ⟨451493, by rfl⟩ : syracuseStep 601991 = 902987) B902987
theorem B6467597 : Blo 263822 6467597 := bstep (se 3 (by rfl) ⟨1212674, by rfl⟩ : syracuseStep 6467597 = 2425349) B2425349
theorem B602171 : Blo 263822 602171 := bstep (se 1 (by rfl) ⟨451628, by rfl⟩ : syracuseStep 602171 = 903257) B903257
theorem B602297 : Blo 263822 602297 := bstep (se 2 (by rfl) ⟨225861, by rfl⟩ : syracuseStep 602297 = 451723) B451723
theorem B1126973 : Blo 263822 1126973 := bstep (se 3 (by rfl) ⟨211307, by rfl⟩ : syracuseStep 1126973 = 422615) B422615
theorem B1520329 : Blo 263822 1520329 := bstep (se 2 (by rfl) ⟨570123, by rfl⟩ : syracuseStep 1520329 = 1140247) B1140247
theorem B406415 : Blo 263822 406415 := bstep (se 1 (by rfl) ⟨304811, by rfl⟩ : syracuseStep 406415 = 609623) B609623
theorem B963613 : Blo 263822 963613 := bstep (se 3 (by rfl) ⟨180677, by rfl⟩ : syracuseStep 963613 = 361355) B361355
theorem B668807 : Blo 263822 668807 := bstep (se 1 (by rfl) ⟨501605, by rfl⟩ : syracuseStep 668807 = 1003211) B1003211
theorem B668857 : Blo 263822 668857 := bstep (se 2 (by rfl) ⟨250821, by rfl⟩ : syracuseStep 668857 = 501643) B501643
theorem B406799 : Blo 263822 406799 := bstep (se 1 (by rfl) ⟨305099, by rfl⟩ : syracuseStep 406799 = 610199) B610199
theorem B898451 : Blo 263822 898451 := bstep (se 1 (by rfl) ⟨673838, by rfl⟩ : syracuseStep 898451 = 1347677) B1347677
theorem B505273 : Blo 263822 505273 := bstep (se 2 (by rfl) ⟨189477, by rfl⟩ : syracuseStep 505273 = 378955) B378955
theorem B4535837 : Blo 263822 4535837 := bstep (se 3 (by rfl) ⟨850469, by rfl⟩ : syracuseStep 4535837 = 1700939) B1700939
theorem B3421925 : Blo 263822 3421925 := bstep (se 4 (by rfl) ⟨320805, by rfl⟩ : syracuseStep 3421925 = 641611) B641611
theorem B669455 : Blo 263822 669455 := bstep (se 1 (by rfl) ⟨502091, by rfl⟩ : syracuseStep 669455 = 1004183) B1004183
theorem B505615 : Blo 263822 505615 := bstep (se 1 (by rfl) ⟨379211, by rfl⟩ : syracuseStep 505615 = 758423) B758423
theorem B1914941 : Blo 263822 1914941 := bstep (se 3 (by rfl) ⟨359051, by rfl⟩ : syracuseStep 1914941 = 718103) B718103
theorem B670153 : Blo 263822 670153 := bstep (se 2 (by rfl) ⟨251307, by rfl⟩ : syracuseStep 670153 = 502615) B502615
theorem B1128971 : Blo 263822 1128971 := bstep (se 1 (by rfl) ⟨846728, by rfl⟩ : syracuseStep 1128971 = 1693457) B1693457
theorem B670295 : Blo 263822 670295 := bstep (se 1 (by rfl) ⟨502721, by rfl⟩ : syracuseStep 670295 = 1005443) B1005443
theorem B768599 : Blo 263822 768599 := bstep (se 1 (by rfl) ⟨576449, by rfl⟩ : syracuseStep 768599 = 1152899) B1152899
theorem B506503 : Blo 263822 506503 := bstep (se 1 (by rfl) ⟨379877, by rfl⟩ : syracuseStep 506503 = 759755) B759755
theorem B899855 : Blo 263822 899855 := bstep (se 1 (by rfl) ⟨674891, by rfl⟩ : syracuseStep 899855 = 1349783) B1349783
theorem B1620773 : Blo 263822 1620773 := bstep (se 4 (by rfl) ⟨151947, by rfl⟩ : syracuseStep 1620773 = 303895) B303895
theorem B637739 : Blo 263822 637739 := bstep (se 1 (by rfl) ⟨478304, by rfl⟩ : syracuseStep 637739 = 956609) B956609
theorem B1391411 : Blo 263822 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B900125 : Blo 263822 900125 := bstep (se 3 (by rfl) ⟨168773, by rfl⟩ : syracuseStep 900125 = 337547) B337547
theorem B605243 : Blo 263822 605243 := bstep (se 1 (by rfl) ⟨453932, by rfl⟩ : syracuseStep 605243 = 907865) B907865
theorem B638873 : Blo 263822 638873 := bstep (se 2 (by rfl) ⟨239577, by rfl⟩ : syracuseStep 638873 = 479155) B479155
theorem B639161 : Blo 263822 639161 := bstep (se 2 (by rfl) ⟨239685, by rfl⟩ : syracuseStep 639161 = 479371) B479371
theorem B5161229 : Blo 263822 5161229 := bstep (se 3 (by rfl) ⟨967730, by rfl⟩ : syracuseStep 5161229 = 1935461) B1935461
theorem B3227921 : Blo 263822 3227921 := bstep (se 2 (by rfl) ⟨1210470, by rfl⟩ : syracuseStep 3227921 = 2420941) B2420941
theorem B508295 : Blo 263822 508295 := bstep (se 1 (by rfl) ⟨381221, by rfl⟩ : syracuseStep 508295 = 762443) B762443
theorem B901529 : Blo 263822 901529 := bstep (se 2 (by rfl) ⟨338073, by rfl⟩ : syracuseStep 901529 = 676147) B676147
theorem B2539997 : Blo 263822 2539997 := bstep (se 3 (by rfl) ⟨476249, by rfl⟩ : syracuseStep 2539997 = 952499) B952499
theorem B377417 : Blo 263822 377417 := bstep (se 2 (by rfl) ⟨141531, by rfl⟩ : syracuseStep 377417 = 283063) B283063
theorem B672371 : Blo 263822 672371 := bstep (se 1 (by rfl) ⟨504278, by rfl⟩ : syracuseStep 672371 = 1008557) B1008557
theorem B2278307 : Blo 263822 2278307 := bstep (se 1 (by rfl) ⟨1708730, by rfl⟩ : syracuseStep 2278307 = 3417461) B3417461
theorem B902231 : Blo 263822 902231 := bstep (se 1 (by rfl) ⟨676673, by rfl⟩ : syracuseStep 902231 = 1353347) B1353347
theorem B672887 : Blo 263822 672887 := bstep (se 1 (by rfl) ⟨504665, by rfl⟩ : syracuseStep 672887 = 1009331) B1009331
theorem B2934049 : Blo 263822 2934049 := bstep (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) B2200537
theorem B476459 : Blo 263822 476459 := bstep (se 1 (by rfl) ⟨357344, by rfl⟩ : syracuseStep 476459 = 714689) B714689
theorem B378283 : Blo 263822 378283 := bstep (se 1 (by rfl) ⟨283712, by rfl⟩ : syracuseStep 378283 = 567425) B567425
theorem B1033771 : Blo 263822 1033771 := bstep (se 1 (by rfl) ⟨775328, by rfl⟩ : syracuseStep 1033771 = 1550657) B1550657
theorem B902717 : Blo 263822 902717 := bstep (se 3 (by rfl) ⟨169259, by rfl⟩ : syracuseStep 902717 = 338519) B338519
theorem B771731 : Blo 263822 771731 := bstep (se 1 (by rfl) ⟨578798, by rfl⟩ : syracuseStep 771731 = 1157597) B1157597
theorem B4572929 : Blo 263822 4572929 := bstep (se 2 (by rfl) ⟨1714848, by rfl⟩ : syracuseStep 4572929 = 3429697) B3429697
theorem B4540211 : Blo 263822 4540211 := bstep (se 1 (by rfl) ⟨3405158, by rfl⟩ : syracuseStep 4540211 = 6810317) B6810317
theorem B673879 : Blo 263822 673879 := bstep (se 1 (by rfl) ⟨505409, by rfl⟩ : syracuseStep 673879 = 1010819) B1010819
theorem B1820987 : Blo 263822 1820987 := bstep (se 1 (by rfl) ⟨1365740, by rfl⟩ : syracuseStep 1820987 = 2731481) B2731481
theorem B674183 : Blo 263822 674183 := bstep (se 1 (by rfl) ⟨505637, by rfl⟩ : syracuseStep 674183 = 1011275) B1011275
theorem B379399 : Blo 263822 379399 := bstep (se 1 (by rfl) ⟨284549, by rfl⟩ : syracuseStep 379399 = 569099) B569099
theorem B674315 : Blo 263822 674315 := bstep (se 1 (by rfl) ⟨505736, by rfl⟩ : syracuseStep 674315 = 1011473) B1011473
theorem B1002071 : Blo 263822 1002071 := bstep (se 1 (by rfl) ⟨751553, by rfl⟩ : syracuseStep 1002071 = 1503107) B1503107
theorem B1133345 : Blo 263822 1133345 := bstep (se 2 (by rfl) ⟨425004, by rfl⟩ : syracuseStep 1133345 = 850009) B850009
theorem B445243 : Blo 263822 445243 := bstep (se 1 (by rfl) ⟨333932, by rfl⟩ : syracuseStep 445243 = 667865) B667865
theorem B1690483 : Blo 263822 1690483 := bstep (se 1 (by rfl) ⟨1267862, by rfl⟩ : syracuseStep 1690483 = 2535725) B2535725
theorem B445385 : Blo 263822 445385 := bstep (se 2 (by rfl) ⟨167019, by rfl⟩ : syracuseStep 445385 = 334039) B334039
theorem B674831 : Blo 263822 674831 := bstep (se 1 (by rfl) ⟨506123, by rfl⟩ : syracuseStep 674831 = 1012247) B1012247
theorem B1002557 : Blo 263822 1002557 := bstep (se 3 (by rfl) ⟨187979, by rfl⟩ : syracuseStep 1002557 = 375959) B375959
theorem B674963 : Blo 263822 674963 := bstep (se 1 (by rfl) ⟨506222, by rfl⟩ : syracuseStep 674963 = 1012445) B1012445
theorem B380219 : Blo 263822 380219 := bstep (se 1 (by rfl) ⟨285164, by rfl⟩ : syracuseStep 380219 = 570329) B570329
theorem B446087 : Blo 263822 446087 := bstep (se 1 (by rfl) ⟨334565, by rfl⟩ : syracuseStep 446087 = 669131) B669131
theorem B4509593 : Blo 263822 4509593 := bstep (se 2 (by rfl) ⟨1691097, by rfl⟩ : syracuseStep 4509593 = 3382195) B3382195
theorem B380857 : Blo 263822 380857 := bstep (se 2 (by rfl) ⟨142821, by rfl⟩ : syracuseStep 380857 = 285643) B285643
theorem B8212427 : Blo 263822 8212427 := bstep (se 1 (by rfl) ⟨6159320, by rfl⟩ : syracuseStep 8212427 = 12318641) B12318641
theorem B380971 : Blo 263822 380971 := bstep (se 1 (by rfl) ⟨285728, by rfl⟩ : syracuseStep 380971 = 571457) B571457
theorem B4640813 : Blo 263822 4640813 := bstep (se 3 (by rfl) ⟨870152, by rfl⟩ : syracuseStep 4640813 = 1740305) B1740305
theorem B676097 : Blo 263822 676097 := bstep (se 2 (by rfl) ⟨253536, by rfl⟩ : syracuseStep 676097 = 507073) B507073
theorem B446735 : Blo 263822 446735 := bstep (se 1 (by rfl) ⟨335051, by rfl⟩ : syracuseStep 446735 = 670103) B670103
theorem B381199 : Blo 263822 381199 := bstep (se 1 (by rfl) ⟨285899, by rfl⟩ : syracuseStep 381199 = 571799) B571799
theorem B1003985 : Blo 263822 1003985 := bstep (se 2 (by rfl) ⟨376494, by rfl⟩ : syracuseStep 1003985 = 752989) B752989
theorem B676471 : Blo 263822 676471 := bstep (se 1 (by rfl) ⟨507353, by rfl⟩ : syracuseStep 676471 = 1014707) B1014707
theorem B5788421 : Blo 263822 5788421 := bstep (se 4 (by rfl) ⟨542664, by rfl⟩ : syracuseStep 5788421 = 1085329) B1085329
theorem B447275 : Blo 263822 447275 := bstep (se 1 (by rfl) ⟨335456, by rfl⟩ : syracuseStep 447275 = 670913) B670913
theorem B1299347 : Blo 263822 1299347 := bstep (se 1 (by rfl) ⟨974510, by rfl⟩ : syracuseStep 1299347 = 1949021) B1949021
theorem B676907 : Blo 263822 676907 := bstep (se 1 (by rfl) ⟨507680, by rfl⟩ : syracuseStep 676907 = 1015361) B1015361
theorem B447673 : Blo 263822 447673 := bstep (se 2 (by rfl) ⟨167877, by rfl⟩ : syracuseStep 447673 = 335755) B335755
theorem B1135873 : Blo 263822 1135873 := bstep (se 2 (by rfl) ⟨425952, by rfl⟩ : syracuseStep 1135873 = 851905) B851905
theorem B677747 : Blo 263822 677747 := bstep (se 1 (by rfl) ⟨508310, by rfl⟩ : syracuseStep 677747 = 1016621) B1016621
theorem B448375 : Blo 263822 448375 := bstep (se 1 (by rfl) ⟨336281, by rfl⟩ : syracuseStep 448375 = 672563) B672563
theorem B677767 : Blo 263822 677767 := bstep (se 1 (by rfl) ⟨508325, by rfl⟩ : syracuseStep 677767 = 1016651) B1016651
theorem B2021273 : Blo 263822 2021273 := bstep (se 2 (by rfl) ⟨757977, by rfl⟩ : syracuseStep 2021273 = 1515955) B1515955
theorem B448571 : Blo 263822 448571 := bstep (se 1 (by rfl) ⟨336428, by rfl⟩ : syracuseStep 448571 = 672857) B672857
theorem B1005655 : Blo 263822 1005655 := bstep (se 1 (by rfl) ⟨754241, by rfl⟩ : syracuseStep 1005655 = 1508483) B1508483
theorem B514363 : Blo 263822 514363 := bstep (se 1 (by rfl) ⟨385772, by rfl⟩ : syracuseStep 514363 = 771545) B771545
theorem B1005959 : Blo 263822 1005959 := bstep (se 1 (by rfl) ⟨754469, by rfl⟩ : syracuseStep 1005959 = 1508939) B1508939
theorem B448969 : Blo 263822 448969 := bstep (se 2 (by rfl) ⟨168363, by rfl⟩ : syracuseStep 448969 = 336727) B336727
theorem B1006141 : Blo 263822 1006141 := bstep (se 3 (by rfl) ⟨188651, by rfl⟩ : syracuseStep 1006141 = 377303) B377303
theorem B285455 : Blo 263822 285455 := bstep (se 1 (by rfl) ⟨214091, by rfl⟩ : syracuseStep 285455 = 428183) B428183
theorem B449671 : Blo 263822 449671 := bstep (se 1 (by rfl) ⟨337253, by rfl⟩ : syracuseStep 449671 = 674507) B674507
theorem B482593 : Blo 263822 482593 := bstep (se 2 (by rfl) ⟨180972, by rfl⟩ : syracuseStep 482593 = 361945) B361945
theorem B483017 : Blo 263822 483017 := bstep (se 2 (by rfl) ⟨181131, by rfl⟩ : syracuseStep 483017 = 362263) B362263
theorem B450319 : Blo 263822 450319 := bstep (se 1 (by rfl) ⟨337739, by rfl⟩ : syracuseStep 450319 = 675479) B675479
theorem B2023217 : Blo 263822 2023217 := bstep (se 2 (by rfl) ⟨758706, by rfl⟩ : syracuseStep 2023217 = 1517413) B1517413
theorem B1204253 : Blo 263822 1204253 := bstep (se 3 (by rfl) ⟨225797, by rfl⟩ : syracuseStep 1204253 = 451595) B451595
theorem B1695917 : Blo 263822 1695917 := bstep (se 3 (by rfl) ⟨317984, by rfl⟩ : syracuseStep 1695917 = 635969) B635969
theorem B1007873 : Blo 263822 1007873 := bstep (se 2 (by rfl) ⟨377952, by rfl⟩ : syracuseStep 1007873 = 755905) B755905
theorem B450859 : Blo 263822 450859 := bstep (se 1 (by rfl) ⟨338144, by rfl⟩ : syracuseStep 450859 = 676289) B676289
theorem B1270169 : Blo 263822 1270169 := bstep (se 2 (by rfl) ⟨476313, by rfl⟩ : syracuseStep 1270169 = 952627) B952627
theorem B451001 : Blo 263822 451001 := bstep (se 2 (by rfl) ⟨169125, by rfl⟩ : syracuseStep 451001 = 338251) B338251
theorem B1335851 : Blo 263822 1335851 := bstep (se 1 (by rfl) ⟨1001888, by rfl⟩ : syracuseStep 1335851 = 2003777) B2003777
theorem B1368695 : Blo 263822 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B713369 : Blo 263822 713369 := bstep (se 2 (by rfl) ⟨267513, by rfl⟩ : syracuseStep 713369 = 535027) B535027
theorem B320503 : Blo 263822 320503 := bstep (se 1 (by rfl) ⟨240377, by rfl⟩ : syracuseStep 320503 = 480755) B480755
theorem B1532951 : Blo 263822 1532951 := bstep (se 1 (by rfl) ⟨1149713, by rfl⟩ : syracuseStep 1532951 = 2299427) B2299427
theorem B1303595 : Blo 263822 1303595 := bstep (se 1 (by rfl) ⟨977696, by rfl⟩ : syracuseStep 1303595 = 1955393) B1955393
theorem B451703 : Blo 263822 451703 := bstep (se 1 (by rfl) ⟨338777, by rfl⟩ : syracuseStep 451703 = 677555) B677555
theorem B23029109 : Blo 263822 23029109 := bstep (se 5 (by rfl) ⟨1079489, by rfl⟩ : syracuseStep 23029109 = 2158979) B2158979
theorem B3433859 : Blo 263822 3433859 := bstep (se 1 (by rfl) ⟨2575394, by rfl⟩ : syracuseStep 3433859 = 5150789) B5150789
theorem B1009043 : Blo 263822 1009043 := bstep (se 1 (by rfl) ⟨756782, by rfl⟩ : syracuseStep 1009043 = 1513565) B1513565
theorem B1337147 : Blo 263822 1337147 := bstep (se 1 (by rfl) ⟨1002860, by rfl⟩ : syracuseStep 1337147 = 2005721) B2005721
theorem B14444405 : Blo 263822 14444405 := bstep (se 5 (by rfl) ⟨677081, by rfl⟩ : syracuseStep 14444405 = 1354163) B1354163
theorem B1075079 : Blo 263822 1075079 := bstep (se 1 (by rfl) ⟨806309, by rfl⟩ : syracuseStep 1075079 = 1612619) B1612619
theorem B1009543 : Blo 263822 1009543 := bstep (se 1 (by rfl) ⟨757157, by rfl⟩ : syracuseStep 1009543 = 1514315) B1514315
theorem B3401675 : Blo 263822 3401675 := bstep (se 1 (by rfl) ⟨2551256, by rfl⟩ : syracuseStep 3401675 = 5102513) B5102513
theorem B1337309 : Blo 263822 1337309 := bstep (se 3 (by rfl) ⟨250745, by rfl⟩ : syracuseStep 1337309 = 501491) B501491
theorem B5433389 : Blo 263822 5433389 := bstep (se 3 (by rfl) ⟨1018760, by rfl⟩ : syracuseStep 5433389 = 2037521) B2037521
theorem B6514805 : Blo 263822 6514805 := bstep (se 5 (by rfl) ⟨305381, by rfl⟩ : syracuseStep 6514805 = 610763) B610763
theorem B4843637 : Blo 263822 4843637 := bstep (se 5 (by rfl) ⟨227045, by rfl⟩ : syracuseStep 4843637 = 454091) B454091
theorem B1337633 : Blo 263822 1337633 := bstep (se 2 (by rfl) ⟨501612, by rfl⟩ : syracuseStep 1337633 = 1003225) B1003225
theorem B1436467 : Blo 263822 1436467 := bstep (se 1 (by rfl) ⟨1077350, by rfl⟩ : syracuseStep 1436467 = 2154701) B2154701
theorem B1338605 : Blo 263822 1338605 := bstep (se 3 (by rfl) ⟨250988, by rfl⟩ : syracuseStep 1338605 = 501977) B501977
theorem B3075317 : Blo 263822 3075317 := bstep (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) B288311
theorem B1830289 : Blo 263822 1830289 := bstep (se 2 (by rfl) ⟨686358, by rfl⟩ : syracuseStep 1830289 = 1372717) B1372717
theorem B1535441 : Blo 263822 1535441 := bstep (se 2 (by rfl) ⟨575790, by rfl⟩ : syracuseStep 1535441 = 1151581) B1151581
theorem B3042845 : Blo 263822 3042845 := bstep (se 3 (by rfl) ⟨570533, by rfl⟩ : syracuseStep 3042845 = 1141067) B1141067
theorem B1142333 : Blo 263822 1142333 := bstep (se 3 (by rfl) ⟨214187, by rfl⟩ : syracuseStep 1142333 = 428375) B428375
theorem B1273745 : Blo 263822 1273745 := bstep (se 2 (by rfl) ⟨477654, by rfl⟩ : syracuseStep 1273745 = 955309) B955309
theorem B1339415 : Blo 263822 1339415 := bstep (se 1 (by rfl) ⟨1004561, by rfl⟩ : syracuseStep 1339415 = 2009123) B2009123
theorem B1208591 : Blo 263822 1208591 := bstep (se 1 (by rfl) ⟨906443, by rfl⟩ : syracuseStep 1208591 = 1812887) B1812887
theorem B913697 : Blo 263822 913697 := bstep (se 2 (by rfl) ⟨342636, by rfl⟩ : syracuseStep 913697 = 685273) B685273
theorem B1078049 : Blo 263822 1078049 := bstep (se 2 (by rfl) ⟨404268, by rfl⟩ : syracuseStep 1078049 = 808537) B808537
theorem B914323 : Blo 263822 914323 := bstep (se 1 (by rfl) ⟨685742, by rfl⟩ : syracuseStep 914323 = 1371485) B1371485
theorem B423031 : Blo 263822 423031 := bstep (se 1 (by rfl) ⟨317273, by rfl⟩ : syracuseStep 423031 = 634547) B634547
theorem B357691 : Blo 263822 357691 := bstep (se 1 (by rfl) ⟨268268, by rfl⟩ : syracuseStep 357691 = 536537) B536537
theorem B685579 : Blo 263822 685579 := bstep (se 1 (by rfl) ⟨514184, by rfl⟩ : syracuseStep 685579 = 1028369) B1028369
theorem B358187 : Blo 263822 358187 := bstep (se 1 (by rfl) ⟨268640, by rfl⟩ : syracuseStep 358187 = 537281) B537281
theorem B5732369 : Blo 263822 5732369 := bstep (se 2 (by rfl) ⟨2149638, by rfl⟩ : syracuseStep 5732369 = 4299277) B4299277
theorem B1964119 : Blo 263822 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B719219 : Blo 263822 719219 := bstep (se 1 (by rfl) ⟨539414, by rfl⟩ : syracuseStep 719219 = 1078829) B1078829
theorem B1440185 : Blo 263822 1440185 := bstep (se 2 (by rfl) ⟨540069, by rfl⟩ : syracuseStep 1440185 = 1080139) B1080139
theorem B1440449 : Blo 263822 1440449 := bstep (se 2 (by rfl) ⟨540168, by rfl⟩ : syracuseStep 1440449 = 1080337) B1080337
theorem B1342493 : Blo 263822 1342493 := bstep (se 3 (by rfl) ⟨251717, by rfl⟩ : syracuseStep 1342493 = 503435) B503435
theorem B425351 : Blo 263822 425351 := bstep (se 1 (by rfl) ⟨319013, by rfl⟩ : syracuseStep 425351 = 638027) B638027
theorem B2030993 : Blo 263822 2030993 := bstep (se 2 (by rfl) ⟨761622, by rfl⟩ : syracuseStep 2030993 = 1523245) B1523245
theorem B1506707 : Blo 263822 1506707 := bstep (se 1 (by rfl) ⟨1130030, by rfl⟩ : syracuseStep 1506707 = 2260061) B2260061
theorem B1015193 : Blo 263822 1015193 := bstep (se 2 (by rfl) ⟨380697, by rfl⟩ : syracuseStep 1015193 = 761395) B761395
theorem B1342979 : Blo 263822 1342979 := bstep (se 1 (by rfl) ⟨1007234, by rfl⟩ : syracuseStep 1342979 = 2014469) B2014469
theorem B753239 : Blo 263822 753239 := bstep (se 1 (by rfl) ⟨564929, by rfl⟩ : syracuseStep 753239 = 1129859) B1129859
theorem B3440357 : Blo 263822 3440357 := bstep (se 4 (by rfl) ⟨322533, by rfl⟩ : syracuseStep 3440357 = 645067) B645067
theorem B3047219 : Blo 263822 3047219 := bstep (se 1 (by rfl) ⟨2285414, by rfl⟩ : syracuseStep 3047219 = 4570829) B4570829
theorem B1507207 : Blo 263822 1507207 := bstep (se 1 (by rfl) ⟨1130405, by rfl⟩ : syracuseStep 1507207 = 2260811) B2260811
theorem B426107 : Blo 263822 426107 := bstep (se 1 (by rfl) ⟨319580, by rfl⟩ : syracuseStep 426107 = 639161) B639161
theorem B3440819 : Blo 263822 3440819 := bstep (se 1 (by rfl) ⟨2580614, by rfl⟩ : syracuseStep 3440819 = 5161229) B5161229
theorem B754049 : Blo 263822 754049 := bstep (se 2 (by rfl) ⟨282768, by rfl⟩ : syracuseStep 754049 = 565537) B565537
theorem B721295 : Blo 263822 721295 := bstep (se 1 (by rfl) ⟨540971, by rfl⟩ : syracuseStep 721295 = 1081943) B1081943
theorem B754505 : Blo 263822 754505 := bstep (se 2 (by rfl) ⟨282939, by rfl⟩ : syracuseStep 754505 = 565879) B565879
theorem B5768009 : Blo 263822 5768009 := bstep (se 2 (by rfl) ⟨2163003, by rfl⟩ : syracuseStep 5768009 = 4326007) B4326007
theorem B1016833 : Blo 263822 1016833 := bstep (se 2 (by rfl) ⟨381312, by rfl⟩ : syracuseStep 1016833 = 762625) B762625
theorem B459899 : Blo 263822 459899 := bstep (se 1 (by rfl) ⟨344924, by rfl⟩ : syracuseStep 459899 = 689849) B689849
theorem B3048619 : Blo 263822 3048619 := bstep (se 1 (by rfl) ⟨2286464, by rfl⟩ : syracuseStep 3048619 = 4572929) B4572929
theorem B853163 : Blo 263822 853163 := bstep (se 1 (by rfl) ⟨639872, by rfl⟩ : syracuseStep 853163 = 1279745) B1279745
theorem B427337 : Blo 263822 427337 := bstep (se 2 (by rfl) ⟨160251, by rfl⟩ : syracuseStep 427337 = 320503) B320503
theorem B1017193 : Blo 263822 1017193 := bstep (se 2 (by rfl) ⟨381447, by rfl⟩ : syracuseStep 1017193 = 762895) B762895
theorem B1213991 : Blo 263822 1213991 := bstep (se 1 (by rfl) ⟨910493, by rfl⟩ : syracuseStep 1213991 = 1820987) B1820987
theorem B263855 : Blo 263822 263855 := bstep (se 1 (by rfl) ⟨197891, by rfl⟩ : syracuseStep 263855 = 395783) B395783
theorem B263879 : Blo 263822 263879 := bstep (se 1 (by rfl) ⟨197909, by rfl⟩ : syracuseStep 263879 = 395819) B395819
theorem B263899 : Blo 263822 263899 := bstep (se 1 (by rfl) ⟨197924, by rfl⟩ : syracuseStep 263899 = 395849) B395849
theorem B263975 : Blo 263822 263975 := bstep (se 1 (by rfl) ⟨197981, by rfl⟩ : syracuseStep 263975 = 395963) B395963
theorem B264015 : Blo 263822 264015 := bstep (se 1 (by rfl) ⟨198011, by rfl⟩ : syracuseStep 264015 = 396023) B396023
theorem B264031 : Blo 263822 264031 := bstep (se 1 (by rfl) ⟨198023, by rfl⟩ : syracuseStep 264031 = 396047) B396047
theorem B755563 : Blo 263822 755563 := bstep (se 1 (by rfl) ⟨566672, by rfl⟩ : syracuseStep 755563 = 1133345) B1133345
theorem B264059 : Blo 263822 264059 := bstep (se 1 (by rfl) ⟨198044, by rfl⟩ : syracuseStep 264059 = 396089) B396089
theorem B264111 : Blo 263822 264111 := bstep (se 1 (by rfl) ⟨198083, by rfl⟩ : syracuseStep 264111 = 396167) B396167
theorem B264135 : Blo 263822 264135 := bstep (se 1 (by rfl) ⟨198101, by rfl⟩ : syracuseStep 264135 = 396203) B396203
theorem B296923 : Blo 263822 296923 := bstep (se 1 (by rfl) ⟨222692, by rfl⟩ : syracuseStep 296923 = 445385) B445385
theorem B264155 : Blo 263822 264155 := bstep (se 1 (by rfl) ⟨198116, by rfl⟩ : syracuseStep 264155 = 396233) B396233
theorem B264231 : Blo 263822 264231 := bstep (se 1 (by rfl) ⟨198173, by rfl⟩ : syracuseStep 264231 = 396347) B396347
theorem B1378361 : Blo 263822 1378361 := bstep (se 2 (by rfl) ⟨516885, by rfl⟩ : syracuseStep 1378361 = 1033771) B1033771
theorem B264271 : Blo 263822 264271 := bstep (se 1 (by rfl) ⟨198203, by rfl⟩ : syracuseStep 264271 = 396407) B396407
theorem B264287 : Blo 263822 264287 := bstep (se 1 (by rfl) ⟨198215, by rfl⟩ : syracuseStep 264287 = 396431) B396431
theorem B264315 : Blo 263822 264315 := bstep (se 1 (by rfl) ⟨198236, by rfl⟩ : syracuseStep 264315 = 396473) B396473
theorem B264367 : Blo 263822 264367 := bstep (se 1 (by rfl) ⟨198275, by rfl⟩ : syracuseStep 264367 = 396551) B396551
theorem B264391 : Blo 263822 264391 := bstep (se 1 (by rfl) ⟨198293, by rfl⟩ : syracuseStep 264391 = 396587) B396587
theorem B264411 : Blo 263822 264411 := bstep (se 1 (by rfl) ⟨198308, by rfl⟩ : syracuseStep 264411 = 396617) B396617
theorem B854263 : Blo 263822 854263 := bstep (se 1 (by rfl) ⟨640697, by rfl⟩ : syracuseStep 854263 = 1281395) B1281395
theorem B264487 : Blo 263822 264487 := bstep (se 1 (by rfl) ⟨198365, by rfl⟩ : syracuseStep 264487 = 396731) B396731
theorem B264527 : Blo 263822 264527 := bstep (se 1 (by rfl) ⟨198395, by rfl⟩ : syracuseStep 264527 = 396791) B396791
theorem B264543 : Blo 263822 264543 := bstep (se 1 (by rfl) ⟨198407, by rfl⟩ : syracuseStep 264543 = 396815) B396815
theorem B264571 : Blo 263822 264571 := bstep (se 1 (by rfl) ⟨198428, by rfl⟩ : syracuseStep 264571 = 396857) B396857
theorem B1083773 : Blo 263822 1083773 := bstep (se 3 (by rfl) ⟨203207, by rfl⟩ : syracuseStep 1083773 = 406415) B406415
theorem B297391 : Blo 263822 297391 := bstep (se 1 (by rfl) ⟨223043, by rfl⟩ : syracuseStep 297391 = 446087) B446087
theorem B264623 : Blo 263822 264623 := bstep (se 1 (by rfl) ⟨198467, by rfl⟩ : syracuseStep 264623 = 396935) B396935
theorem B264647 : Blo 263822 264647 := bstep (se 1 (by rfl) ⟨198485, by rfl⟩ : syracuseStep 264647 = 396971) B396971
theorem B264667 : Blo 263822 264667 := bstep (se 1 (by rfl) ⟨198500, by rfl⟩ : syracuseStep 264667 = 397001) B397001
theorem B1346057 : Blo 263822 1346057 := bstep (se 2 (by rfl) ⟨504771, by rfl⟩ : syracuseStep 1346057 = 1009543) B1009543
theorem B264743 : Blo 263822 264743 := bstep (se 1 (by rfl) ⟨198557, by rfl⟩ : syracuseStep 264743 = 397115) B397115
theorem B395855 : Blo 263822 395855 := bstep (se 1 (by rfl) ⟨296891, by rfl⟩ : syracuseStep 395855 = 593783) B593783
theorem B264783 : Blo 263822 264783 := bstep (se 1 (by rfl) ⟨198587, by rfl⟩ : syracuseStep 264783 = 397175) B397175
theorem B264799 : Blo 263822 264799 := bstep (se 1 (by rfl) ⟨198599, by rfl⟩ : syracuseStep 264799 = 397199) B397199
theorem B264827 : Blo 263822 264827 := bstep (se 1 (by rfl) ⟨198620, by rfl⟩ : syracuseStep 264827 = 397241) B397241
theorem B5474951 : Blo 263822 5474951 := bstep (se 1 (by rfl) ⟨4106213, by rfl⟩ : syracuseStep 5474951 = 8212427) B8212427
theorem B264879 : Blo 263822 264879 := bstep (se 1 (by rfl) ⟨198659, by rfl⟩ : syracuseStep 264879 = 397319) B397319
theorem B395975 : Blo 263822 395975 := bstep (se 1 (by rfl) ⟨296981, by rfl⟩ : syracuseStep 395975 = 593963) B593963
theorem B264903 : Blo 263822 264903 := bstep (se 1 (by rfl) ⟨198677, by rfl⟩ : syracuseStep 264903 = 397355) B397355
theorem B264923 : Blo 263822 264923 := bstep (se 1 (by rfl) ⟨198692, by rfl⟩ : syracuseStep 264923 = 397385) B397385
theorem B264999 : Blo 263822 264999 := bstep (se 1 (by rfl) ⟨198749, by rfl⟩ : syracuseStep 264999 = 397499) B397499
theorem B265039 : Blo 263822 265039 := bstep (se 1 (by rfl) ⟨198779, by rfl⟩ : syracuseStep 265039 = 397559) B397559
theorem B297823 : Blo 263822 297823 := bstep (se 1 (by rfl) ⟨223367, by rfl⟩ : syracuseStep 297823 = 446735) B446735
theorem B265055 : Blo 263822 265055 := bstep (se 1 (by rfl) ⟨198791, by rfl⟩ : syracuseStep 265055 = 397583) B397583
theorem B396137 : Blo 263822 396137 := bstep (se 2 (by rfl) ⟨148551, by rfl⟩ : syracuseStep 396137 = 297103) B297103
theorem B265083 : Blo 263822 265083 := bstep (se 1 (by rfl) ⟨198812, by rfl⟩ : syracuseStep 265083 = 397625) B397625
theorem B265135 : Blo 263822 265135 := bstep (se 1 (by rfl) ⟨198851, by rfl⟩ : syracuseStep 265135 = 397703) B397703
theorem B396215 : Blo 263822 396215 := bstep (se 1 (by rfl) ⟨297161, by rfl⟩ : syracuseStep 396215 = 594323) B594323
theorem B265159 : Blo 263822 265159 := bstep (se 1 (by rfl) ⟨198869, by rfl⟩ : syracuseStep 265159 = 397739) B397739
theorem B396251 : Blo 263822 396251 := bstep (se 1 (by rfl) ⟨297188, by rfl⟩ : syracuseStep 396251 = 594377) B594377
theorem B265179 : Blo 263822 265179 := bstep (se 1 (by rfl) ⟨198884, by rfl⟩ : syracuseStep 265179 = 397769) B397769
theorem B265255 : Blo 263822 265255 := bstep (se 1 (by rfl) ⟨198941, by rfl⟩ : syracuseStep 265255 = 397883) B397883
theorem B756793 : Blo 263822 756793 := bstep (se 2 (by rfl) ⟨283797, by rfl⟩ : syracuseStep 756793 = 567595) B567595
theorem B265295 : Blo 263822 265295 := bstep (se 1 (by rfl) ⟨198971, by rfl⟩ : syracuseStep 265295 = 397943) B397943
theorem B265311 : Blo 263822 265311 := bstep (se 1 (by rfl) ⟨198983, by rfl⟩ : syracuseStep 265311 = 397967) B397967
theorem B265339 : Blo 263822 265339 := bstep (se 1 (by rfl) ⟨199004, by rfl⟩ : syracuseStep 265339 = 398009) B398009
theorem B265391 : Blo 263822 265391 := bstep (se 1 (by rfl) ⟨199043, by rfl⟩ : syracuseStep 265391 = 398087) B398087
theorem B298183 : Blo 263822 298183 := bstep (se 1 (by rfl) ⟨223637, by rfl⟩ : syracuseStep 298183 = 447275) B447275
theorem B265415 : Blo 263822 265415 := bstep (se 1 (by rfl) ⟨199061, by rfl⟩ : syracuseStep 265415 = 398123) B398123
theorem B265435 : Blo 263822 265435 := bstep (se 1 (by rfl) ⟨199076, by rfl⟩ : syracuseStep 265435 = 398153) B398153
theorem B462071 : Blo 263822 462071 := bstep (se 1 (by rfl) ⟨346553, by rfl⟩ : syracuseStep 462071 = 693107) B693107
theorem B265511 : Blo 263822 265511 := bstep (se 1 (by rfl) ⟨199133, by rfl⟩ : syracuseStep 265511 = 398267) B398267
theorem B265551 : Blo 263822 265551 := bstep (se 1 (by rfl) ⟨199163, by rfl⟩ : syracuseStep 265551 = 398327) B398327
theorem B265567 : Blo 263822 265567 := bstep (se 1 (by rfl) ⟨199175, by rfl⟩ : syracuseStep 265567 = 398351) B398351
theorem B265595 : Blo 263822 265595 := bstep (se 1 (by rfl) ⟨199196, by rfl⟩ : syracuseStep 265595 = 398393) B398393
theorem B396719 : Blo 263822 396719 := bstep (se 1 (by rfl) ⟨297539, by rfl⟩ : syracuseStep 396719 = 595079) B595079
theorem B265647 : Blo 263822 265647 := bstep (se 1 (by rfl) ⟨199235, by rfl⟩ : syracuseStep 265647 = 398471) B398471
theorem B265671 : Blo 263822 265671 := bstep (se 1 (by rfl) ⟨199253, by rfl⟩ : syracuseStep 265671 = 398507) B398507
theorem B265691 : Blo 263822 265691 := bstep (se 1 (by rfl) ⟨199268, by rfl⟩ : syracuseStep 265691 = 398537) B398537
theorem B396809 : Blo 263822 396809 := bstep (se 2 (by rfl) ⟨148803, by rfl⟩ : syracuseStep 396809 = 297607) B297607
theorem B396839 : Blo 263822 396839 := bstep (se 1 (by rfl) ⟨297629, by rfl⟩ : syracuseStep 396839 = 595259) B595259
theorem B265767 : Blo 263822 265767 := bstep (se 1 (by rfl) ⟨199325, by rfl⟩ : syracuseStep 265767 = 398651) B398651
theorem B265807 : Blo 263822 265807 := bstep (se 1 (by rfl) ⟨199355, by rfl⟩ : syracuseStep 265807 = 398711) B398711
theorem B265823 : Blo 263822 265823 := bstep (se 1 (by rfl) ⟨199367, by rfl⟩ : syracuseStep 265823 = 398735) B398735
theorem B396923 : Blo 263822 396923 := bstep (se 1 (by rfl) ⟨297692, by rfl⟩ : syracuseStep 396923 = 595385) B595385
theorem B265851 : Blo 263822 265851 := bstep (se 1 (by rfl) ⟨199388, by rfl⟩ : syracuseStep 265851 = 398777) B398777
theorem B265903 : Blo 263822 265903 := bstep (se 1 (by rfl) ⟨199427, by rfl⟩ : syracuseStep 265903 = 398855) B398855
theorem B265927 : Blo 263822 265927 := bstep (se 1 (by rfl) ⟨199445, by rfl⟩ : syracuseStep 265927 = 398891) B398891
theorem B265947 : Blo 263822 265947 := bstep (se 1 (by rfl) ⟨199460, by rfl⟩ : syracuseStep 265947 = 398921) B398921
theorem B593657 : Blo 263822 593657 := bstep (se 2 (by rfl) ⟨222621, by rfl⟩ : syracuseStep 593657 = 445243) B445243
theorem B397049 : Blo 263822 397049 := bstep (se 2 (by rfl) ⟨148893, by rfl⟩ : syracuseStep 397049 = 297787) B297787
theorem B266023 : Blo 263822 266023 := bstep (se 1 (by rfl) ⟨199517, by rfl⟩ : syracuseStep 266023 = 399035) B399035
theorem B266063 : Blo 263822 266063 := bstep (se 1 (by rfl) ⟨199547, by rfl⟩ : syracuseStep 266063 = 399095) B399095
theorem B397151 : Blo 263822 397151 := bstep (se 1 (by rfl) ⟨297863, by rfl⟩ : syracuseStep 397151 = 595727) B595727
theorem B266079 : Blo 263822 266079 := bstep (se 1 (by rfl) ⟨199559, by rfl⟩ : syracuseStep 266079 = 399119) B399119
theorem B397163 : Blo 263822 397163 := bstep (se 1 (by rfl) ⟨297872, by rfl⟩ : syracuseStep 397163 = 595745) B595745
theorem B266107 : Blo 263822 266107 := bstep (se 1 (by rfl) ⟨199580, by rfl⟩ : syracuseStep 266107 = 399161) B399161
theorem B1707911 : Blo 263822 1707911 := bstep (se 1 (by rfl) ⟨1280933, by rfl⟩ : syracuseStep 1707911 = 2561867) B2561867
theorem B266159 : Blo 263822 266159 := bstep (se 1 (by rfl) ⟨199619, by rfl⟩ : syracuseStep 266159 = 399239) B399239
theorem B1347515 : Blo 263822 1347515 := bstep (se 1 (by rfl) ⟨1010636, by rfl⟩ : syracuseStep 1347515 = 2021273) B2021273
theorem B266183 : Blo 263822 266183 := bstep (se 1 (by rfl) ⟨199637, by rfl⟩ : syracuseStep 266183 = 399275) B399275
theorem B266203 : Blo 263822 266203 := bstep (se 1 (by rfl) ⟨199652, by rfl⟩ : syracuseStep 266203 = 399305) B399305
theorem B593927 : Blo 263822 593927 := bstep (se 1 (by rfl) ⟨445445, by rfl⟩ : syracuseStep 593927 = 890891) B890891
theorem B299047 : Blo 263822 299047 := bstep (se 1 (by rfl) ⟨224285, by rfl⟩ : syracuseStep 299047 = 448571) B448571
theorem B266279 : Blo 263822 266279 := bstep (se 1 (by rfl) ⟨199709, by rfl⟩ : syracuseStep 266279 = 399419) B399419
theorem B593999 : Blo 263822 593999 := bstep (se 1 (by rfl) ⟨445499, by rfl⟩ : syracuseStep 593999 = 890999) B890999
theorem B397391 : Blo 263822 397391 := bstep (se 1 (by rfl) ⟨298043, by rfl⟩ : syracuseStep 397391 = 596087) B596087
theorem B266319 : Blo 263822 266319 := bstep (se 1 (by rfl) ⟨199739, by rfl⟩ : syracuseStep 266319 = 399479) B399479
theorem B266335 : Blo 263822 266335 := bstep (se 1 (by rfl) ⟨199751, by rfl⟩ : syracuseStep 266335 = 399503) B399503
theorem B266363 : Blo 263822 266363 := bstep (se 1 (by rfl) ⟨199772, by rfl⟩ : syracuseStep 266363 = 399545) B399545
theorem B1511581 : Blo 263822 1511581 := bstep (se 3 (by rfl) ⟨283421, by rfl⟩ : syracuseStep 1511581 = 566843) B566843
theorem B266415 : Blo 263822 266415 := bstep (se 1 (by rfl) ⟨199811, by rfl⟩ : syracuseStep 266415 = 399623) B399623
theorem B397511 : Blo 263822 397511 := bstep (se 1 (by rfl) ⟨298133, by rfl⟩ : syracuseStep 397511 = 596267) B596267
theorem B266439 : Blo 263822 266439 := bstep (se 1 (by rfl) ⟨199829, by rfl⟩ : syracuseStep 266439 = 399659) B399659
theorem B266459 : Blo 263822 266459 := bstep (se 1 (by rfl) ⟨199844, by rfl⟩ : syracuseStep 266459 = 399689) B399689
theorem B266535 : Blo 263822 266535 := bstep (se 1 (by rfl) ⟨199901, by rfl⟩ : syracuseStep 266535 = 399803) B399803
theorem B266575 : Blo 263822 266575 := bstep (se 1 (by rfl) ⟨199931, by rfl⟩ : syracuseStep 266575 = 399863) B399863
theorem B266591 : Blo 263822 266591 := bstep (se 1 (by rfl) ⟨199943, by rfl⟩ : syracuseStep 266591 = 399887) B399887
theorem B397673 : Blo 263822 397673 := bstep (se 2 (by rfl) ⟨149127, by rfl⟩ : syracuseStep 397673 = 298255) B298255
theorem B266619 : Blo 263822 266619 := bstep (se 1 (by rfl) ⟨199964, by rfl⟩ : syracuseStep 266619 = 399929) B399929
theorem B266671 : Blo 263822 266671 := bstep (se 1 (by rfl) ⟨200003, by rfl⟩ : syracuseStep 266671 = 400007) B400007
theorem B397751 : Blo 263822 397751 := bstep (se 1 (by rfl) ⟨298313, by rfl⟩ : syracuseStep 397751 = 596627) B596627
theorem B266695 : Blo 263822 266695 := bstep (se 1 (by rfl) ⟨200021, by rfl⟩ : syracuseStep 266695 = 400043) B400043
theorem B594395 : Blo 263822 594395 := bstep (se 1 (by rfl) ⟨445796, by rfl⟩ : syracuseStep 594395 = 891593) B891593
theorem B397787 : Blo 263822 397787 := bstep (se 1 (by rfl) ⟨298340, by rfl⟩ : syracuseStep 397787 = 596681) B596681
theorem B266715 : Blo 263822 266715 := bstep (se 1 (by rfl) ⟨200036, by rfl⟩ : syracuseStep 266715 = 400073) B400073
theorem B758297 : Blo 263822 758297 := bstep (se 2 (by rfl) ⟨284361, by rfl⟩ : syracuseStep 758297 = 568723) B568723
theorem B266791 : Blo 263822 266791 := bstep (se 1 (by rfl) ⟨200093, by rfl⟩ : syracuseStep 266791 = 400187) B400187
theorem B266831 : Blo 263822 266831 := bstep (se 1 (by rfl) ⟨200123, by rfl⟩ : syracuseStep 266831 = 400247) B400247
theorem B266847 : Blo 263822 266847 := bstep (se 1 (by rfl) ⟨200135, by rfl⟩ : syracuseStep 266847 = 400271) B400271
theorem B266875 : Blo 263822 266875 := bstep (se 1 (by rfl) ⟨200156, by rfl⟩ : syracuseStep 266875 = 400313) B400313
theorem B266927 : Blo 263822 266927 := bstep (se 1 (by rfl) ⟨200195, by rfl⟩ : syracuseStep 266927 = 400391) B400391
theorem B266951 : Blo 263822 266951 := bstep (se 1 (by rfl) ⟨200213, by rfl⟩ : syracuseStep 266951 = 400427) B400427
theorem B266971 : Blo 263822 266971 := bstep (se 1 (by rfl) ⟨200228, by rfl⟩ : syracuseStep 266971 = 400457) B400457
theorem B955165 : Blo 263822 955165 := bstep (se 3 (by rfl) ⟨179093, by rfl⟩ : syracuseStep 955165 = 358187) B358187
theorem B267047 : Blo 263822 267047 := bstep (se 1 (by rfl) ⟨200285, by rfl⟩ : syracuseStep 267047 = 400571) B400571
theorem B267087 : Blo 263822 267087 := bstep (se 1 (by rfl) ⟨200315, by rfl⟩ : syracuseStep 267087 = 400631) B400631
theorem B267103 : Blo 263822 267103 := bstep (se 1 (by rfl) ⟨200327, by rfl⟩ : syracuseStep 267103 = 400655) B400655
theorem B267131 : Blo 263822 267131 := bstep (se 1 (by rfl) ⟨200348, by rfl⟩ : syracuseStep 267131 = 400697) B400697
theorem B594863 : Blo 263822 594863 := bstep (se 1 (by rfl) ⟨446147, by rfl⟩ : syracuseStep 594863 = 892295) B892295
theorem B398255 : Blo 263822 398255 := bstep (se 1 (by rfl) ⟨298691, by rfl⟩ : syracuseStep 398255 = 597383) B597383
theorem B4330415 : Blo 263822 4330415 := bstep (se 1 (by rfl) ⟨3247811, by rfl⟩ : syracuseStep 4330415 = 6495623) B6495623
theorem B267183 : Blo 263822 267183 := bstep (se 1 (by rfl) ⟨200387, by rfl⟩ : syracuseStep 267183 = 400775) B400775
theorem B267207 : Blo 263822 267207 := bstep (se 1 (by rfl) ⟨200405, by rfl⟩ : syracuseStep 267207 = 400811) B400811
theorem B267227 : Blo 263822 267227 := bstep (se 1 (by rfl) ⟨200420, by rfl⟩ : syracuseStep 267227 = 400841) B400841
theorem B2626561 : Blo 263822 2626561 := bstep (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) B1969921
theorem B398345 : Blo 263822 398345 := bstep (se 2 (by rfl) ⟨149379, by rfl⟩ : syracuseStep 398345 = 298759) B298759
theorem B398375 : Blo 263822 398375 := bstep (se 1 (by rfl) ⟨298781, by rfl⟩ : syracuseStep 398375 = 597563) B597563
theorem B267303 : Blo 263822 267303 := bstep (se 1 (by rfl) ⟨200477, by rfl⟩ : syracuseStep 267303 = 400955) B400955
theorem B267343 : Blo 263822 267343 := bstep (se 1 (by rfl) ⟨200507, by rfl⟩ : syracuseStep 267343 = 401015) B401015
theorem B267359 : Blo 263822 267359 := bstep (se 1 (by rfl) ⟨200519, by rfl⟩ : syracuseStep 267359 = 401039) B401039
theorem B398459 : Blo 263822 398459 := bstep (se 1 (by rfl) ⟨298844, by rfl⟩ : syracuseStep 398459 = 597689) B597689
theorem B267387 : Blo 263822 267387 := bstep (se 1 (by rfl) ⟨200540, by rfl⟩ : syracuseStep 267387 = 401081) B401081
theorem B595115 : Blo 263822 595115 := bstep (se 1 (by rfl) ⟨446336, by rfl⟩ : syracuseStep 595115 = 892673) B892673
theorem B267439 : Blo 263822 267439 := bstep (se 1 (by rfl) ⟨200579, by rfl⟩ : syracuseStep 267439 = 401159) B401159
theorem B267463 : Blo 263822 267463 := bstep (se 1 (by rfl) ⟨200597, by rfl⟩ : syracuseStep 267463 = 401195) B401195
theorem B1348811 : Blo 263822 1348811 := bstep (se 1 (by rfl) ⟨1011608, by rfl⟩ : syracuseStep 1348811 = 2023217) B2023217
theorem B267483 : Blo 263822 267483 := bstep (se 1 (by rfl) ⟨200612, by rfl⟩ : syracuseStep 267483 = 401225) B401225
theorem B398585 : Blo 263822 398585 := bstep (se 2 (by rfl) ⟨149469, by rfl⟩ : syracuseStep 398585 = 298939) B298939
theorem B267559 : Blo 263822 267559 := bstep (se 1 (by rfl) ⟨200669, by rfl⟩ : syracuseStep 267559 = 401339) B401339
theorem B267599 : Blo 263822 267599 := bstep (se 1 (by rfl) ⟨200699, by rfl⟩ : syracuseStep 267599 = 401399) B401399
theorem B398687 : Blo 263822 398687 := bstep (se 1 (by rfl) ⟨299015, by rfl⟩ : syracuseStep 398687 = 598031) B598031
theorem B267615 : Blo 263822 267615 := bstep (se 1 (by rfl) ⟨200711, by rfl⟩ : syracuseStep 267615 = 401423) B401423
theorem B398699 : Blo 263822 398699 := bstep (se 1 (by rfl) ⟨299024, by rfl⟩ : syracuseStep 398699 = 598049) B598049
theorem B267643 : Blo 263822 267643 := bstep (se 1 (by rfl) ⟨200732, by rfl⟩ : syracuseStep 267643 = 401465) B401465
theorem B267695 : Blo 263822 267695 := bstep (se 1 (by rfl) ⟨200771, by rfl⟩ : syracuseStep 267695 = 401543) B401543
theorem B267719 : Blo 263822 267719 := bstep (se 1 (by rfl) ⟨200789, by rfl⟩ : syracuseStep 267719 = 401579) B401579
theorem B267739 : Blo 263822 267739 := bstep (se 1 (by rfl) ⟨200804, by rfl⟩ : syracuseStep 267739 = 401609) B401609
theorem B267815 : Blo 263822 267815 := bstep (se 1 (by rfl) ⟨200861, by rfl⟩ : syracuseStep 267815 = 401723) B401723
theorem B398927 : Blo 263822 398927 := bstep (se 1 (by rfl) ⟨299195, by rfl⟩ : syracuseStep 398927 = 598391) B598391
theorem B300667 : Blo 263822 300667 := bstep (se 1 (by rfl) ⟨225500, by rfl⟩ : syracuseStep 300667 = 451001) B451001
theorem B890567 : Blo 263822 890567 := bstep (se 1 (by rfl) ⟨667925, by rfl⟩ : syracuseStep 890567 = 1335851) B1335851
theorem B595655 : Blo 263822 595655 := bstep (se 1 (by rfl) ⟨446741, by rfl⟩ : syracuseStep 595655 = 893483) B893483
theorem B399047 : Blo 263822 399047 := bstep (se 1 (by rfl) ⟨299285, by rfl⟩ : syracuseStep 399047 = 598571) B598571
theorem B399209 : Blo 263822 399209 := bstep (se 2 (by rfl) ⟨149703, by rfl⟩ : syracuseStep 399209 = 299407) B299407
theorem B399287 : Blo 263822 399287 := bstep (se 1 (by rfl) ⟨299465, by rfl⟩ : syracuseStep 399287 = 598931) B598931
theorem B399323 : Blo 263822 399323 := bstep (se 1 (by rfl) ⟨299492, by rfl⟩ : syracuseStep 399323 = 598985) B598985
theorem B858127 : Blo 263822 858127 := bstep (se 1 (by rfl) ⟨643595, by rfl⟩ : syracuseStep 858127 = 1287191) B1287191
theorem B1021967 : Blo 263822 1021967 := bstep (se 1 (by rfl) ⟨766475, by rfl⟩ : syracuseStep 1021967 = 1532951) B1532951
theorem B301135 : Blo 263822 301135 := bstep (se 1 (by rfl) ⟨225851, by rfl⟩ : syracuseStep 301135 = 451703) B451703
theorem B399791 : Blo 263822 399791 := bstep (se 1 (by rfl) ⟨299843, by rfl⟩ : syracuseStep 399791 = 599687) B599687
theorem B3840493 : Blo 263822 3840493 := bstep (se 3 (by rfl) ⟨720092, by rfl⟩ : syracuseStep 3840493 = 1440185) B1440185
theorem B399881 : Blo 263822 399881 := bstep (se 2 (by rfl) ⟨149955, by rfl⟩ : syracuseStep 399881 = 299911) B299911
theorem B1219097 : Blo 263822 1219097 := bstep (se 2 (by rfl) ⟨457161, by rfl⟩ : syracuseStep 1219097 = 914323) B914323
theorem B891431 : Blo 263822 891431 := bstep (se 1 (by rfl) ⟨668573, by rfl⟩ : syracuseStep 891431 = 1337147) B1337147
theorem B596519 : Blo 263822 596519 := bstep (se 1 (by rfl) ⟨447389, by rfl⟩ : syracuseStep 596519 = 894779) B894779
theorem B399911 : Blo 263822 399911 := bstep (se 1 (by rfl) ⟨299933, by rfl⟩ : syracuseStep 399911 = 599867) B599867
theorem B334459 : Blo 263822 334459 := bstep (se 1 (by rfl) ⟨250844, by rfl⟩ : syracuseStep 334459 = 501689) B501689
theorem B399995 : Blo 263822 399995 := bstep (se 1 (by rfl) ⟨299996, by rfl⟩ : syracuseStep 399995 = 599993) B599993
theorem B2267783 : Blo 263822 2267783 := bstep (se 1 (by rfl) ⟨1700837, by rfl⟩ : syracuseStep 2267783 = 3401675) B3401675
theorem B891539 : Blo 263822 891539 := bstep (se 1 (by rfl) ⟨668654, by rfl⟩ : syracuseStep 891539 = 1337309) B1337309
theorem B1284817 : Blo 263822 1284817 := bstep (se 2 (by rfl) ⟨481806, by rfl⟩ : syracuseStep 1284817 = 963613) B963613
theorem B400121 : Blo 263822 400121 := bstep (se 2 (by rfl) ⟨150045, by rfl⟩ : syracuseStep 400121 = 300091) B300091
theorem B564041 : Blo 263822 564041 := bstep (se 2 (by rfl) ⟨211515, by rfl⟩ : syracuseStep 564041 = 423031) B423031
theorem B334687 : Blo 263822 334687 := bstep (se 1 (by rfl) ⟨251015, by rfl⟩ : syracuseStep 334687 = 502031) B502031
theorem B400223 : Blo 263822 400223 := bstep (se 1 (by rfl) ⟨300167, by rfl⟩ : syracuseStep 400223 = 600335) B600335
theorem B891755 : Blo 263822 891755 := bstep (se 1 (by rfl) ⟨668816, by rfl⟩ : syracuseStep 891755 = 1337633) B1337633
theorem B596843 : Blo 263822 596843 := bstep (se 1 (by rfl) ⟨447632, by rfl⟩ : syracuseStep 596843 = 895265) B895265
theorem B400235 : Blo 263822 400235 := bstep (se 1 (by rfl) ⟨300176, by rfl⟩ : syracuseStep 400235 = 600353) B600353
theorem B891809 : Blo 263822 891809 := bstep (se 2 (by rfl) ⟨334428, by rfl⟩ : syracuseStep 891809 = 668857) B668857
theorem B596897 : Blo 263822 596897 := bstep (se 2 (by rfl) ⟨223836, by rfl⟩ : syracuseStep 596897 = 447673) B447673
theorem B1514497 : Blo 263822 1514497 := bstep (se 2 (by rfl) ⟨567936, by rfl⟩ : syracuseStep 1514497 = 1135873) B1135873
theorem B400463 : Blo 263822 400463 := bstep (se 1 (by rfl) ⟨300347, by rfl⟩ : syracuseStep 400463 = 600695) B600695
theorem B400583 : Blo 263822 400583 := bstep (se 1 (by rfl) ⟨300437, by rfl⟩ : syracuseStep 400583 = 600875) B600875
theorem B597239 : Blo 263822 597239 := bstep (se 1 (by rfl) ⟨447929, by rfl⟩ : syracuseStep 597239 = 895859) B895859
theorem B400745 : Blo 263822 400745 := bstep (se 2 (by rfl) ⟨150279, by rfl⟩ : syracuseStep 400745 = 300559) B300559
theorem B761213 : Blo 263822 761213 := bstep (se 3 (by rfl) ⟨142727, by rfl⟩ : syracuseStep 761213 = 285455) B285455
theorem B335279 : Blo 263822 335279 := bstep (se 1 (by rfl) ⟨251459, by rfl⟩ : syracuseStep 335279 = 502919) B502919
theorem B400823 : Blo 263822 400823 := bstep (se 1 (by rfl) ⟨300617, by rfl⟩ : syracuseStep 400823 = 601235) B601235
theorem B400859 : Blo 263822 400859 := bstep (se 1 (by rfl) ⟨300644, by rfl⟩ : syracuseStep 400859 = 601289) B601289
theorem B892403 : Blo 263822 892403 := bstep (se 1 (by rfl) ⟨669302, by rfl⟩ : syracuseStep 892403 = 1338605) B1338605
theorem B761555 : Blo 263822 761555 := bstep (se 1 (by rfl) ⟨571166, by rfl⟩ : syracuseStep 761555 = 1142333) B1142333
theorem B597833 : Blo 263822 597833 := bstep (se 2 (by rfl) ⟨224187, by rfl⟩ : syracuseStep 597833 = 448375) B448375
theorem B401327 : Blo 263822 401327 := bstep (se 1 (by rfl) ⟨300995, by rfl⟩ : syracuseStep 401327 = 601991) B601991
theorem B401417 : Blo 263822 401417 := bstep (se 2 (by rfl) ⟨150531, by rfl⟩ : syracuseStep 401417 = 301063) B301063
theorem B892943 : Blo 263822 892943 := bstep (se 1 (by rfl) ⟨669707, by rfl⟩ : syracuseStep 892943 = 1339415) B1339415
theorem B401447 : Blo 263822 401447 := bstep (se 1 (by rfl) ⟨301085, by rfl⟩ : syracuseStep 401447 = 602171) B602171
theorem B401531 : Blo 263822 401531 := bstep (se 1 (by rfl) ⟨301148, by rfl⟩ : syracuseStep 401531 = 602297) B602297
theorem B1613981 : Blo 263822 1613981 := bstep (se 3 (by rfl) ⟨302621, by rfl⟩ : syracuseStep 1613981 = 605243) B605243
theorem B401657 : Blo 263822 401657 := bstep (se 2 (by rfl) ⟨150621, by rfl⟩ : syracuseStep 401657 = 301243) B301243
theorem B893537 : Blo 263822 893537 := bstep (se 2 (by rfl) ⟨335076, by rfl⟩ : syracuseStep 893537 = 670153) B670153
theorem B598625 : Blo 263822 598625 := bstep (se 2 (by rfl) ⟨224484, by rfl⟩ : syracuseStep 598625 = 448969) B448969
theorem B10887797 : Blo 263822 10887797 := bstep (se 5 (by rfl) ⟨510365, by rfl⟩ : syracuseStep 10887797 = 1020731) B1020731
theorem B271199 : Blo 263822 271199 := bstep (se 1 (by rfl) ⟨203399, by rfl⟩ : syracuseStep 271199 = 406799) B406799
theorem B598967 : Blo 263822 598967 := bstep (se 1 (by rfl) ⟨449225, by rfl⟩ : syracuseStep 598967 = 898451) B898451
theorem B3023891 : Blo 263822 3023891 := bstep (se 1 (by rfl) ⟨2267918, by rfl⟩ : syracuseStep 3023891 = 4535837) B4535837
theorem B599561 : Blo 263822 599561 := bstep (se 2 (by rfl) ⟨224835, by rfl⟩ : syracuseStep 599561 = 449671) B449671
theorem B2008637 : Blo 263822 2008637 := bstep (se 3 (by rfl) ⟨376619, by rfl⟩ : syracuseStep 2008637 = 753239) B753239
theorem B960299 : Blo 263822 960299 := bstep (se 1 (by rfl) ⟨720224, by rfl⟩ : syracuseStep 960299 = 1440449) B1440449
theorem B599903 : Blo 263822 599903 := bstep (se 1 (by rfl) ⟨449927, by rfl⟩ : syracuseStep 599903 = 899855) B899855
theorem B1288045 : Blo 263822 1288045 := bstep (se 3 (by rfl) ⟨241508, by rfl⟩ : syracuseStep 1288045 = 483017) B483017
theorem B927607 : Blo 263822 927607 := bstep (se 1 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 927607 = 1391411) B1391411
theorem B894995 : Blo 263822 894995 := bstep (se 1 (by rfl) ⟨671246, by rfl⟩ : syracuseStep 894995 = 1342493) B1342493
theorem B600083 : Blo 263822 600083 := bstep (se 1 (by rfl) ⟨450062, by rfl⟩ : syracuseStep 600083 = 900125) B900125
theorem B1353995 : Blo 263822 1353995 := bstep (se 1 (by rfl) ⟨1015496, by rfl⟩ : syracuseStep 1353995 = 2030993) B2030993
theorem B895319 : Blo 263822 895319 := bstep (se 1 (by rfl) ⟨671489, by rfl⟩ : syracuseStep 895319 = 1342979) B1342979
theorem B600425 : Blo 263822 600425 := bstep (se 2 (by rfl) ⟨225159, by rfl⟩ : syracuseStep 600425 = 450319) B450319
theorem B2009609 : Blo 263822 2009609 := bstep (se 2 (by rfl) ⟨753603, by rfl⟩ : syracuseStep 2009609 = 1507207) B1507207
theorem B601019 : Blo 263822 601019 := bstep (se 1 (by rfl) ⟨450764, by rfl⟩ : syracuseStep 601019 = 901529) B901529
theorem B601145 : Blo 263822 601145 := bstep (se 2 (by rfl) ⟨225429, by rfl⟩ : syracuseStep 601145 = 450859) B450859
theorem B2272535 : Blo 263822 2272535 := bstep (se 1 (by rfl) ⟨1704401, by rfl⟩ : syracuseStep 2272535 = 3408803) B3408803
theorem B1518871 : Blo 263822 1518871 := bstep (se 1 (by rfl) ⟨1139153, by rfl⟩ : syracuseStep 1518871 = 2278307) B2278307
theorem B961853 : Blo 263822 961853 := bstep (se 3 (by rfl) ⟨180347, by rfl⟩ : syracuseStep 961853 = 360695) B360695
theorem B503147 : Blo 263822 503147 := bstep (se 1 (by rfl) ⟨377360, by rfl⟩ : syracuseStep 503147 = 754721) B754721
theorem B896399 : Blo 263822 896399 := bstep (se 1 (by rfl) ⟨672299, by rfl⟩ : syracuseStep 896399 = 1344599) B1344599
theorem B601487 : Blo 263822 601487 := bstep (se 1 (by rfl) ⟨451115, by rfl⟩ : syracuseStep 601487 = 902231) B902231
theorem B1355453 : Blo 263822 1355453 := bstep (se 3 (by rfl) ⟨254147, by rfl⟩ : syracuseStep 1355453 = 508295) B508295
theorem B634567 : Blo 263822 634567 := bstep (se 1 (by rfl) ⟨475925, by rfl⟩ : syracuseStep 634567 = 951851) B951851
theorem B896723 : Blo 263822 896723 := bstep (se 1 (by rfl) ⟨672542, by rfl⟩ : syracuseStep 896723 = 1345085) B1345085
theorem B601811 : Blo 263822 601811 := bstep (se 1 (by rfl) ⟨451358, by rfl⟩ : syracuseStep 601811 = 902717) B902717
theorem B1355615 : Blo 263822 1355615 := bstep (se 1 (by rfl) ⟨1016711, by rfl⟩ : syracuseStep 1355615 = 2033423) B2033423
theorem B3026807 : Blo 263822 3026807 := bstep (se 1 (by rfl) ⟨2270105, by rfl⟩ : syracuseStep 3026807 = 4540211) B4540211
theorem B2011067 : Blo 263822 2011067 := bstep (se 1 (by rfl) ⟨1508300, by rfl⟩ : syracuseStep 2011067 = 3016601) B3016601
theorem B503815 : Blo 263822 503815 := bstep (se 1 (by rfl) ⟨377861, by rfl⟩ : syracuseStep 503815 = 755723) B755723
theorem B307399 : Blo 263822 307399 := bstep (se 1 (by rfl) ⟨230549, by rfl⟩ : syracuseStep 307399 = 461099) B461099
theorem B3649853 : Blo 263822 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B3912065 : Blo 263822 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B668047 : Blo 263822 668047 := bstep (se 1 (by rfl) ⟨501035, by rfl⟩ : syracuseStep 668047 = 1002071) B1002071
theorem B504377 : Blo 263822 504377 := bstep (se 2 (by rfl) ⟨189141, by rfl⟩ : syracuseStep 504377 = 378283) B378283
theorem B569953 : Blo 263822 569953 := bstep (se 2 (by rfl) ⟨213732, by rfl⟩ : syracuseStep 569953 = 427465) B427465
theorem B668371 : Blo 263822 668371 := bstep (se 1 (by rfl) ⟨501278, by rfl⟩ : syracuseStep 668371 = 1002557) B1002557
theorem B8630995 : Blo 263822 8630995 := bstep (se 1 (by rfl) ⟨6473246, by rfl⟩ : syracuseStep 8630995 = 12946493) B12946493
theorem B897911 : Blo 263822 897911 := bstep (se 1 (by rfl) ⟨673433, by rfl⟩ : syracuseStep 897911 = 1346867) B1346867
theorem B898127 : Blo 263822 898127 := bstep (se 1 (by rfl) ⟨673595, by rfl⟩ : syracuseStep 898127 = 1347191) B1347191
theorem B537929 : Blo 263822 537929 := bstep (se 2 (by rfl) ⟨201723, by rfl⟩ : syracuseStep 537929 = 403447) B403447
theorem B3093875 : Blo 263822 3093875 := bstep (se 1 (by rfl) ⟨2320406, by rfl⟩ : syracuseStep 3093875 = 4640813) B4640813
theorem B4634003 : Blo 263822 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B898505 : Blo 263822 898505 := bstep (se 2 (by rfl) ⟨336939, by rfl⟩ : syracuseStep 898505 = 673879) B673879
theorem B669323 : Blo 263822 669323 := bstep (se 1 (by rfl) ⟨501992, by rfl⟩ : syracuseStep 669323 = 1003985) B1003985
theorem B898775 : Blo 263822 898775 := bstep (se 1 (by rfl) ⟨674081, by rfl⟩ : syracuseStep 898775 = 1348163) B1348163
theorem B898991 : Blo 263822 898991 := bstep (se 1 (by rfl) ⟨674243, by rfl⟩ : syracuseStep 898991 = 1348487) B1348487
theorem B866231 : Blo 263822 866231 := bstep (se 1 (by rfl) ⟨649673, by rfl⟩ : syracuseStep 866231 = 1299347) B1299347
theorem B505865 : Blo 263822 505865 := bstep (se 2 (by rfl) ⟨189699, by rfl⟩ : syracuseStep 505865 = 379399) B379399
theorem B1915289 : Blo 263822 1915289 := bstep (se 2 (by rfl) ⟨718233, by rfl⟩ : syracuseStep 1915289 = 1436467) B1436467
theorem B3422897 : Blo 263822 3422897 := bstep (se 2 (by rfl) ⟨1283586, by rfl⟩ : syracuseStep 3422897 = 2567173) B2567173
theorem B670457 : Blo 263822 670457 := bstep (se 2 (by rfl) ⟨251421, by rfl⟩ : syracuseStep 670457 = 502843) B502843
theorem B3849029 : Blo 263822 3849029 := bstep (se 4 (by rfl) ⟨360846, by rfl⟩ : syracuseStep 3849029 = 721693) B721693
theorem B3652427 : Blo 263822 3652427 := bstep (se 1 (by rfl) ⟨2739320, by rfl⟩ : syracuseStep 3652427 = 5478641) B5478641
theorem B506731 : Blo 263822 506731 := bstep (se 1 (by rfl) ⟨380048, by rfl⟩ : syracuseStep 506731 = 760097) B760097
theorem B670639 : Blo 263822 670639 := bstep (se 1 (by rfl) ⟨502979, by rfl⟩ : syracuseStep 670639 = 1005959) B1005959
theorem B506807 : Blo 263822 506807 := bstep (se 1 (by rfl) ⟨380105, by rfl⟩ : syracuseStep 506807 = 760211) B760211
theorem B375931 : Blo 263822 375931 := bstep (se 1 (by rfl) ⟨281948, by rfl⟩ : syracuseStep 375931 = 563897) B563897
theorem B2440385 : Blo 263822 2440385 := bstep (se 2 (by rfl) ⟨915144, by rfl⟩ : syracuseStep 2440385 = 1830289) B1830289
theorem B376159 : Blo 263822 376159 := bstep (se 1 (by rfl) ⟨282119, by rfl⟩ : syracuseStep 376159 = 564239) B564239
theorem B671105 : Blo 263822 671105 := bstep (se 2 (by rfl) ⟨251664, by rfl⟩ : syracuseStep 671105 = 503329) B503329
theorem B507323 : Blo 263822 507323 := bstep (se 1 (by rfl) ⟨380492, by rfl⟩ : syracuseStep 507323 = 760985) B760985
theorem B2866877 : Blo 263822 2866877 := bstep (se 3 (by rfl) ⟨537539, by rfl⟩ : syracuseStep 2866877 = 1075079) B1075079
theorem B671561 : Blo 263822 671561 := bstep (se 2 (by rfl) ⟨251835, by rfl⟩ : syracuseStep 671561 = 503671) B503671
theorem B507809 : Blo 263822 507809 := bstep (se 2 (by rfl) ⟨190428, by rfl⟩ : syracuseStep 507809 = 380857) B380857
theorem B376751 : Blo 263822 376751 := bstep (se 1 (by rfl) ⟨282563, by rfl⟩ : syracuseStep 376751 = 565127) B565127
theorem B802835 : Blo 263822 802835 := bstep (se 1 (by rfl) ⟨602126, by rfl⟩ : syracuseStep 802835 = 1204253) B1204253
theorem B507961 : Blo 263822 507961 := bstep (se 2 (by rfl) ⟨190485, by rfl⟩ : syracuseStep 507961 = 380971) B380971
theorem B1130611 : Blo 263822 1130611 := bstep (se 1 (by rfl) ⟨847958, by rfl⟩ : syracuseStep 1130611 = 1695917) B1695917
theorem B671915 : Blo 263822 671915 := bstep (se 1 (by rfl) ⟨503936, by rfl⟩ : syracuseStep 671915 = 1007873) B1007873
theorem B901367 : Blo 263822 901367 := bstep (se 1 (by rfl) ⟨676025, by rfl⟩ : syracuseStep 901367 = 1352051) B1352051
theorem B508265 : Blo 263822 508265 := bstep (se 2 (by rfl) ⟨190599, by rfl⟩ : syracuseStep 508265 = 381199) B381199
theorem B475579 : Blo 263822 475579 := bstep (se 1 (by rfl) ⟨356684, by rfl⟩ : syracuseStep 475579 = 713369) B713369
theorem B901691 : Blo 263822 901691 := bstep (se 1 (by rfl) ⟨676268, by rfl⟩ : syracuseStep 901691 = 1352537) B1352537
theorem B869063 : Blo 263822 869063 := bstep (se 1 (by rfl) ⟨651797, by rfl⟩ : syracuseStep 869063 = 1303595) B1303595
theorem B901961 : Blo 263822 901961 := bstep (se 2 (by rfl) ⟨338235, by rfl⟩ : syracuseStep 901961 = 676471) B676471
theorem B15352739 : Blo 263822 15352739 := bstep (se 1 (by rfl) ⟨11514554, by rfl⟩ : syracuseStep 15352739 = 23029109) B23029109
theorem B672695 : Blo 263822 672695 := bstep (se 1 (by rfl) ⟨504521, by rfl⟩ : syracuseStep 672695 = 1009043) B1009043
theorem B1917917 : Blo 263822 1917917 := bstep (se 3 (by rfl) ⟨359609, by rfl⟩ : syracuseStep 1917917 = 719219) B719219
theorem B378055 : Blo 263822 378055 := bstep (se 1 (by rfl) ⟨283541, by rfl⟩ : syracuseStep 378055 = 567083) B567083
theorem B3622259 : Blo 263822 3622259 := bstep (se 1 (by rfl) ⟨2716694, by rfl⟩ : syracuseStep 3622259 = 5433389) B5433389
theorem B4343203 : Blo 263822 4343203 := bstep (se 1 (by rfl) ⟨3257402, by rfl⟩ : syracuseStep 4343203 = 6514805) B6514805
theorem B3229091 : Blo 263822 3229091 := bstep (se 1 (by rfl) ⟨2421818, by rfl⟩ : syracuseStep 3229091 = 4843637) B4843637
theorem B476921 : Blo 263822 476921 := bstep (se 2 (by rfl) ⟨178845, by rfl⟩ : syracuseStep 476921 = 357691) B357691
theorem B673697 : Blo 263822 673697 := bstep (se 2 (by rfl) ⟨252636, by rfl⟩ : syracuseStep 673697 = 505273) B505273
theorem B903095 : Blo 263822 903095 := bstep (se 1 (by rfl) ⟨677321, by rfl⟩ : syracuseStep 903095 = 1354643) B1354643
theorem B2050211 : Blo 263822 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B674153 : Blo 263822 674153 := bstep (se 2 (by rfl) ⟨252807, by rfl⟩ : syracuseStep 674153 = 505615) B505615
theorem B903689 : Blo 263822 903689 := bstep (se 2 (by rfl) ⟨338883, by rfl⟩ : syracuseStep 903689 = 677767) B677767
theorem B3426893 : Blo 263822 3426893 := bstep (se 3 (by rfl) ⟨642542, by rfl⟩ : syracuseStep 3426893 = 1285085) B1285085
theorem B4311731 : Blo 263822 4311731 := bstep (se 1 (by rfl) ⟨3233798, by rfl⟩ : syracuseStep 4311731 = 6467597) B6467597
theorem B2542265 : Blo 263822 2542265 := bstep (se 2 (by rfl) ⟨953349, by rfl⟩ : syracuseStep 2542265 = 1906699) B1906699
theorem B2280221 : Blo 263822 2280221 := bstep (se 3 (by rfl) ⟨427541, by rfl⟩ : syracuseStep 2280221 = 855083) B855083
theorem B805727 : Blo 263822 805727 := bstep (se 1 (by rfl) ⟨604295, by rfl⟩ : syracuseStep 805727 = 1208591) B1208591
theorem B609131 : Blo 263822 609131 := bstep (se 1 (by rfl) ⟨456848, by rfl⟩ : syracuseStep 609131 = 913697) B913697
theorem B445871 : Blo 263822 445871 := bstep (se 1 (by rfl) ⟨334403, by rfl⟩ : syracuseStep 445871 = 668807) B668807
theorem B675337 : Blo 263822 675337 := bstep (se 2 (by rfl) ⟨253251, by rfl⟩ : syracuseStep 675337 = 506503) B506503
theorem B1134269 : Blo 263822 1134269 := bstep (se 3 (by rfl) ⟨212675, by rfl⟩ : syracuseStep 1134269 = 425351) B425351
theorem B2281283 : Blo 263822 2281283 := bstep (se 1 (by rfl) ⟨1710962, by rfl⟩ : syracuseStep 2281283 = 3421925) B3421925
theorem B446303 : Blo 263822 446303 := bstep (se 1 (by rfl) ⟨334727, by rfl⟩ : syracuseStep 446303 = 669455) B669455
theorem B3821579 : Blo 263822 3821579 := bstep (se 1 (by rfl) ⟨2866184, by rfl⟩ : syracuseStep 3821579 = 5732369) B5732369
theorem B643457 : Blo 263822 643457 := bstep (se 2 (by rfl) ⟨241296, by rfl⟩ : syracuseStep 643457 = 482593) B482593
theorem B446863 : Blo 263822 446863 := bstep (se 1 (by rfl) ⟨335147, by rfl⟩ : syracuseStep 446863 = 670295) B670295
theorem B512399 : Blo 263822 512399 := bstep (se 1 (by rfl) ⟨384299, by rfl⟩ : syracuseStep 512399 = 768599) B768599
theorem B1004471 : Blo 263822 1004471 := bstep (se 1 (by rfl) ⟨753353, by rfl⟩ : syracuseStep 1004471 = 1506707) B1506707
theorem B676795 : Blo 263822 676795 := bstep (se 1 (by rfl) ⟨507596, by rfl⟩ : syracuseStep 676795 = 1015193) B1015193
theorem B3396653 : Blo 263822 3396653 := bstep (se 3 (by rfl) ⟨636872, by rfl⟩ : syracuseStep 3396653 = 1273745) B1273745
theorem B447545 : Blo 263822 447545 := bstep (se 2 (by rfl) ⟨167829, by rfl⟩ : syracuseStep 447545 = 335659) B335659
theorem B2151947 : Blo 263822 2151947 := bstep (se 1 (by rfl) ⟨1613960, by rfl⟩ : syracuseStep 2151947 = 3227921) B3227921
theorem B1693331 : Blo 263822 1693331 := bstep (se 1 (by rfl) ⟨1269998, by rfl⟩ : syracuseStep 1693331 = 2539997) B2539997
theorem B448247 : Blo 263822 448247 := bstep (se 1 (by rfl) ⟨336185, by rfl⟩ : syracuseStep 448247 = 672371) B672371
theorem B1005473 : Blo 263822 1005473 := bstep (se 2 (by rfl) ⟨377052, by rfl⟩ : syracuseStep 1005473 = 754105) B754105
theorem B284635 : Blo 263822 284635 := bstep (se 1 (by rfl) ⟨213476, by rfl⟩ : syracuseStep 284635 = 426953) B426953
theorem B448591 : Blo 263822 448591 := bstep (se 1 (by rfl) ⟨336443, by rfl⟩ : syracuseStep 448591 = 672887) B672887
theorem B317639 : Blo 263822 317639 := bstep (se 1 (by rfl) ⟨238229, by rfl⟩ : syracuseStep 317639 = 476459) B476459
theorem B448841 : Blo 263822 448841 := bstep (se 2 (by rfl) ⟨168315, by rfl⟩ : syracuseStep 448841 = 336631) B336631
theorem B1005929 : Blo 263822 1005929 := bstep (se 2 (by rfl) ⟨377223, by rfl⟩ : syracuseStep 1005929 = 754447) B754447
theorem B514487 : Blo 263822 514487 := bstep (se 1 (by rfl) ⟨385865, by rfl⟩ : syracuseStep 514487 = 771731) B771731
theorem B1137361 : Blo 263822 1137361 := bstep (se 2 (by rfl) ⟨426510, by rfl⟩ : syracuseStep 1137361 = 853021) B853021
theorem B449273 : Blo 263822 449273 := bstep (se 2 (by rfl) ⟨168477, by rfl⟩ : syracuseStep 449273 = 336955) B336955
theorem B1006445 : Blo 263822 1006445 := bstep (se 3 (by rfl) ⟨188708, by rfl⟩ : syracuseStep 1006445 = 377417) B377417
theorem B449455 : Blo 263822 449455 := bstep (se 1 (by rfl) ⟨337091, by rfl⟩ : syracuseStep 449455 = 674183) B674183
theorem B449543 : Blo 263822 449543 := bstep (se 1 (by rfl) ⟨337157, by rfl⟩ : syracuseStep 449543 = 674315) B674315
theorem B482311 : Blo 263822 482311 := bstep (se 1 (by rfl) ⟨361733, by rfl⟩ : syracuseStep 482311 = 723467) B723467
theorem B1268939 : Blo 263822 1268939 := bstep (se 1 (by rfl) ⟨951704, by rfl⟩ : syracuseStep 1268939 = 1903409) B1903409
theorem B449887 : Blo 263822 449887 := bstep (se 1 (by rfl) ⟨337415, by rfl⟩ : syracuseStep 449887 = 674831) B674831
theorem B2874797 : Blo 263822 2874797 := bstep (se 3 (by rfl) ⟨539024, by rfl⟩ : syracuseStep 2874797 = 1078049) B1078049
theorem B449975 : Blo 263822 449975 := bstep (se 1 (by rfl) ⟨337481, by rfl⟩ : syracuseStep 449975 = 674963) B674963
theorem B1007113 : Blo 263822 1007113 := bstep (se 2 (by rfl) ⟨377667, by rfl⟩ : syracuseStep 1007113 = 755335) B755335
theorem B3006395 : Blo 263822 3006395 := bstep (se 1 (by rfl) ⟨2254796, by rfl⟩ : syracuseStep 3006395 = 4509593) B4509593
theorem B450569 : Blo 263822 450569 := bstep (se 2 (by rfl) ⟨168963, by rfl⟩ : syracuseStep 450569 = 337927) B337927
theorem B450731 : Blo 263822 450731 := bstep (se 1 (by rfl) ⟨338048, by rfl⟩ : syracuseStep 450731 = 676097) B676097
theorem B3858947 : Blo 263822 3858947 := bstep (se 1 (by rfl) ⟨2894210, by rfl⟩ : syracuseStep 3858947 = 5788421) B5788421
theorem B451129 : Blo 263822 451129 := bstep (se 2 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 451129 = 338347) B338347
theorem B451271 : Blo 263822 451271 := bstep (se 1 (by rfl) ⟨338453, by rfl⟩ : syracuseStep 451271 = 676907) B676907
theorem B451433 : Blo 263822 451433 := bstep (se 2 (by rfl) ⟨169287, by rfl⟩ : syracuseStep 451433 = 338575) B338575
theorem B811883 : Blo 263822 811883 := bstep (se 1 (by rfl) ⟨608912, by rfl⟩ : syracuseStep 811883 = 1217825) B1217825
theorem B1008571 : Blo 263822 1008571 := bstep (se 1 (by rfl) ⟨756428, by rfl⟩ : syracuseStep 1008571 = 1512857) B1512857
theorem B2253977 : Blo 263822 2253977 := bstep (se 2 (by rfl) ⟨845241, by rfl⟩ : syracuseStep 2253977 = 1690483) B1690483
theorem B451831 : Blo 263822 451831 := bstep (se 1 (by rfl) ⟨338873, by rfl⟩ : syracuseStep 451831 = 677747) B677747
theorem B5432741 : Blo 263822 5432741 := bstep (se 4 (by rfl) ⟨509319, by rfl⟩ : syracuseStep 5432741 = 1018639) B1018639
theorem B1009361 : Blo 263822 1009361 := bstep (se 2 (by rfl) ⟨378510, by rfl⟩ : syracuseStep 1009361 = 757021) B757021
theorem B485473 : Blo 263822 485473 := bstep (se 2 (by rfl) ⟨182052, by rfl⟩ : syracuseStep 485473 = 364105) B364105
theorem B1009817 : Blo 263822 1009817 := bstep (se 2 (by rfl) ⟨378681, by rfl⟩ : syracuseStep 1009817 = 757363) B757363
theorem B1927397 : Blo 263822 1927397 := bstep (se 4 (by rfl) ⟨180693, by rfl⟩ : syracuseStep 1927397 = 361387) B361387
theorem B486059 : Blo 263822 486059 := bstep (se 1 (by rfl) ⟨364544, by rfl⟩ : syracuseStep 486059 = 729089) B729089
theorem B5106509 : Blo 263822 5106509 := bstep (se 3 (by rfl) ⟨957470, by rfl⟩ : syracuseStep 5106509 = 1914941) B1914941
theorem B846779 : Blo 263822 846779 := bstep (se 1 (by rfl) ⟨635084, by rfl⟩ : syracuseStep 846779 = 1270169) B1270169
theorem B1207315 : Blo 263822 1207315 := bstep (se 1 (by rfl) ⟨905486, by rfl⟩ : syracuseStep 1207315 = 1810973) B1810973
theorem B1338767 : Blo 263822 1338767 := bstep (se 1 (by rfl) ⟨1004075, by rfl⟩ : syracuseStep 1338767 = 2008151) B2008151
theorem B2289239 : Blo 263822 2289239 := bstep (se 1 (by rfl) ⟨1716929, by rfl⟩ : syracuseStep 2289239 = 3433859) B3433859
theorem B2027105 : Blo 263822 2027105 := bstep (se 2 (by rfl) ⟨760164, by rfl⟩ : syracuseStep 2027105 = 1520329) B1520329
theorem B1928843 : Blo 263822 1928843 := bstep (se 1 (by rfl) ⟨1446632, by rfl⟩ : syracuseStep 1928843 = 2893265) B2893265
theorem B9629603 : Blo 263822 9629603 := bstep (se 1 (by rfl) ⟨7222202, by rfl⟩ : syracuseStep 9629603 = 14444405) B14444405
theorem B683959 : Blo 263822 683959 := bstep (se 1 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 683959 = 1025939) B1025939
theorem B1011791 : Blo 263822 1011791 := bstep (se 1 (by rfl) ⟨758843, by rfl⟩ : syracuseStep 1011791 = 1517687) B1517687
theorem B1011959 : Blo 263822 1011959 := bstep (se 1 (by rfl) ⟨758969, by rfl⟩ : syracuseStep 1011959 = 1517939) B1517939
theorem B914105 : Blo 263822 914105 := bstep (se 2 (by rfl) ⟨342789, by rfl⟩ : syracuseStep 914105 = 685579) B685579
theorem B2028563 : Blo 263822 2028563 := bstep (se 1 (by rfl) ⟨1521422, by rfl⟩ : syracuseStep 2028563 = 3042845) B3042845
theorem B1012931 : Blo 263822 1012931 := bstep (se 1 (by rfl) ⟨759698, by rfl⟩ : syracuseStep 1012931 = 1519397) B1519397
theorem B357625 : Blo 263822 357625 := bstep (se 2 (by rfl) ⟨134109, by rfl⟩ : syracuseStep 357625 = 268219) B268219
theorem B1340873 : Blo 263822 1340873 := bstep (se 2 (by rfl) ⟨502827, by rfl⟩ : syracuseStep 1340873 = 1005655) B1005655
theorem B2618825 : Blo 263822 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B751315 : Blo 263822 751315 := bstep (se 1 (by rfl) ⟨563486, by rfl⟩ : syracuseStep 751315 = 1126973) B1126973
theorem B685817 : Blo 263822 685817 := bstep (se 2 (by rfl) ⟨257181, by rfl⟩ : syracuseStep 685817 = 514363) B514363
theorem B5601061 : Blo 263822 5601061 := bstep (se 4 (by rfl) ⟨525099, by rfl⟩ : syracuseStep 5601061 = 1050199) B1050199
theorem B19363697 : Blo 263822 19363697 := bstep (se 2 (by rfl) ⟨7261386, by rfl⟩ : syracuseStep 19363697 = 14522773) B14522773
theorem B1275841 : Blo 263822 1275841 := bstep (se 2 (by rfl) ⟨478440, by rfl⟩ : syracuseStep 1275841 = 956881) B956881
theorem B1341521 : Blo 263822 1341521 := bstep (se 2 (by rfl) ⟨503070, by rfl⟩ : syracuseStep 1341521 = 1006141) B1006141
theorem B1013917 : Blo 263822 1013917 := bstep (se 3 (by rfl) ⟨190109, by rfl⟩ : syracuseStep 1013917 = 380219) B380219
theorem B4094509 : Blo 263822 4094509 := bstep (se 3 (by rfl) ⟨767720, by rfl⟩ : syracuseStep 4094509 = 1535441) B1535441
theorem B1080173 : Blo 263822 1080173 := bstep (se 3 (by rfl) ⟨202532, by rfl⟩ : syracuseStep 1080173 = 405065) B405065
theorem B752647 : Blo 263822 752647 := bstep (se 1 (by rfl) ⟨564485, by rfl⟩ : syracuseStep 752647 = 1128971) B1128971
theorem B1080515 : Blo 263822 1080515 := bstep (se 1 (by rfl) ⟨810386, by rfl⟩ : syracuseStep 1080515 = 1620773) B1620773
theorem B425159 : Blo 263822 425159 := bstep (se 1 (by rfl) ⟨318869, by rfl⟩ : syracuseStep 425159 = 637739) B637739
theorem B2293571 : Blo 263822 2293571 := bstep (se 1 (by rfl) ⟨1720178, by rfl⟩ : syracuseStep 2293571 = 3440357) B3440357
theorem B2031479 : Blo 263822 2031479 := bstep (se 1 (by rfl) ⟨1523609, by rfl⟩ : syracuseStep 2031479 = 3047219) B3047219
theorem B425915 : Blo 263822 425915 := bstep (se 1 (by rfl) ⟨319436, by rfl⟩ : syracuseStep 425915 = 638873) B638873
theorem B2293879 : Blo 263822 2293879 := bstep (se 1 (by rfl) ⟨1720409, by rfl⟩ : syracuseStep 2293879 = 3440819) B3440819
theorem B1507481 : Blo 263822 1507481 := bstep (se 2 (by rfl) ⟨565305, by rfl⟩ : syracuseStep 1507481 = 1130611) B1130611
theorem B1278611 : Blo 263822 1278611 := bstep (se 1 (by rfl) ⟨958958, by rfl⟩ : syracuseStep 1278611 = 1917917) B1917917
theorem B1344761 : Blo 263822 1344761 := bstep (se 2 (by rfl) ⟨504285, by rfl⟩ : syracuseStep 1344761 = 1008571) B1008571
theorem B918907 : Blo 263822 918907 := bstep (se 1 (by rfl) ⟨689180, by rfl⟩ : syracuseStep 918907 = 1378361) B1378361
theorem B4064825 : Blo 263822 4064825 := bstep (se 2 (by rfl) ⟨1524309, by rfl⟩ : syracuseStep 4064825 = 3048619) B3048619
theorem B722515 : Blo 263822 722515 := bstep (se 1 (by rfl) ⟨541886, by rfl⟩ : syracuseStep 722515 = 1083773) B1083773
theorem B263903 : Blo 263822 263903 := bstep (se 1 (by rfl) ⟨197927, by rfl⟩ : syracuseStep 263903 = 395855) B395855
theorem B263983 : Blo 263822 263983 := bstep (se 1 (by rfl) ⟨197987, by rfl⟩ : syracuseStep 263983 = 395975) B395975
theorem B264091 : Blo 263822 264091 := bstep (se 1 (by rfl) ⟨198068, by rfl⟩ : syracuseStep 264091 = 396137) B396137
theorem B264143 : Blo 263822 264143 := bstep (se 1 (by rfl) ⟨198107, by rfl⟩ : syracuseStep 264143 = 396215) B396215
theorem B264167 : Blo 263822 264167 := bstep (se 1 (by rfl) ⟨198125, by rfl⟩ : syracuseStep 264167 = 396251) B396251
theorem B723197 : Blo 263822 723197 := bstep (se 3 (by rfl) ⟨135599, by rfl⟩ : syracuseStep 723197 = 271199) B271199
theorem B297247 : Blo 263822 297247 := bstep (se 1 (by rfl) ⟨222935, by rfl⟩ : syracuseStep 297247 = 445871) B445871
theorem B264479 : Blo 263822 264479 := bstep (se 1 (by rfl) ⟨198359, by rfl⟩ : syracuseStep 264479 = 396719) B396719
theorem B264539 : Blo 263822 264539 := bstep (se 1 (by rfl) ⟨198404, by rfl⟩ : syracuseStep 264539 = 396809) B396809
theorem B264559 : Blo 263822 264559 := bstep (se 1 (by rfl) ⟨198419, by rfl⟩ : syracuseStep 264559 = 396839) B396839
theorem B264615 : Blo 263822 264615 := bstep (se 1 (by rfl) ⟨198461, by rfl⟩ : syracuseStep 264615 = 396923) B396923
theorem B756179 : Blo 263822 756179 := bstep (se 1 (by rfl) ⟨567134, by rfl⟩ : syracuseStep 756179 = 1134269) B1134269
theorem B395771 : Blo 263822 395771 := bstep (se 1 (by rfl) ⟨296828, by rfl⟩ : syracuseStep 395771 = 593657) B593657
theorem B264699 : Blo 263822 264699 := bstep (se 1 (by rfl) ⟨198524, by rfl⟩ : syracuseStep 264699 = 397049) B397049
theorem B297535 : Blo 263822 297535 := bstep (se 1 (by rfl) ⟨223151, by rfl⟩ : syracuseStep 297535 = 446303) B446303
theorem B264767 : Blo 263822 264767 := bstep (se 1 (by rfl) ⟨198575, by rfl⟩ : syracuseStep 264767 = 397151) B397151
theorem B264775 : Blo 263822 264775 := bstep (se 1 (by rfl) ⟨198581, by rfl⟩ : syracuseStep 264775 = 397163) B397163
theorem B395897 : Blo 263822 395897 := bstep (se 2 (by rfl) ⟨148461, by rfl⟩ : syracuseStep 395897 = 296923) B296923
theorem B395951 : Blo 263822 395951 := bstep (se 1 (by rfl) ⟨296963, by rfl⟩ : syracuseStep 395951 = 593927) B593927
theorem B395999 : Blo 263822 395999 := bstep (se 1 (by rfl) ⟨296999, by rfl⟩ : syracuseStep 395999 = 593999) B593999
theorem B264927 : Blo 263822 264927 := bstep (se 1 (by rfl) ⟨198695, by rfl⟩ : syracuseStep 264927 = 397391) B397391
theorem B265007 : Blo 263822 265007 := bstep (se 1 (by rfl) ⟨198755, by rfl⟩ : syracuseStep 265007 = 397511) B397511
theorem B265115 : Blo 263822 265115 := bstep (se 1 (by rfl) ⟨198836, by rfl⟩ : syracuseStep 265115 = 397673) B397673
theorem B428971 : Blo 263822 428971 := bstep (se 1 (by rfl) ⟨321728, by rfl⟩ : syracuseStep 428971 = 643457) B643457
theorem B265167 : Blo 263822 265167 := bstep (se 1 (by rfl) ⟨198875, by rfl⟩ : syracuseStep 265167 = 397751) B397751
theorem B396263 : Blo 263822 396263 := bstep (se 1 (by rfl) ⟨297197, by rfl⟩ : syracuseStep 396263 = 594395) B594395
theorem B265191 : Blo 263822 265191 := bstep (se 1 (by rfl) ⟨198893, by rfl⟩ : syracuseStep 265191 = 397787) B397787
theorem B396521 : Blo 263822 396521 := bstep (se 2 (by rfl) ⟨148695, by rfl⟩ : syracuseStep 396521 = 297391) B297391
theorem B396575 : Blo 263822 396575 := bstep (se 1 (by rfl) ⟨297431, by rfl⟩ : syracuseStep 396575 = 594863) B594863
theorem B265503 : Blo 263822 265503 := bstep (se 1 (by rfl) ⟨199127, by rfl⟩ : syracuseStep 265503 = 398255) B398255
theorem B2886943 : Blo 263822 2886943 := bstep (se 1 (by rfl) ⟨2165207, by rfl⟩ : syracuseStep 2886943 = 4330415) B4330415
theorem B265563 : Blo 263822 265563 := bstep (se 1 (by rfl) ⟨199172, by rfl⟩ : syracuseStep 265563 = 398345) B398345
theorem B265583 : Blo 263822 265583 := bstep (se 1 (by rfl) ⟨199187, by rfl⟩ : syracuseStep 265583 = 398375) B398375
theorem B2264435 : Blo 263822 2264435 := bstep (se 1 (by rfl) ⟨1698326, by rfl⟩ : syracuseStep 2264435 = 3396653) B3396653
theorem B298363 : Blo 263822 298363 := bstep (se 1 (by rfl) ⟨223772, by rfl⟩ : syracuseStep 298363 = 447545) B447545
theorem B265639 : Blo 263822 265639 := bstep (se 1 (by rfl) ⟨199229, by rfl⟩ : syracuseStep 265639 = 398459) B398459
theorem B396743 : Blo 263822 396743 := bstep (se 1 (by rfl) ⟨297557, by rfl⟩ : syracuseStep 396743 = 595115) B595115
theorem B265723 : Blo 263822 265723 := bstep (se 1 (by rfl) ⟨199292, by rfl⟩ : syracuseStep 265723 = 398585) B398585
theorem B265791 : Blo 263822 265791 := bstep (se 1 (by rfl) ⟨199343, by rfl⟩ : syracuseStep 265791 = 398687) B398687
theorem B265799 : Blo 263822 265799 := bstep (se 1 (by rfl) ⟨199349, by rfl⟩ : syracuseStep 265799 = 398699) B398699
theorem B265951 : Blo 263822 265951 := bstep (se 1 (by rfl) ⟨199463, by rfl⟩ : syracuseStep 265951 = 398927) B398927
theorem B397097 : Blo 263822 397097 := bstep (se 2 (by rfl) ⟨148911, by rfl⟩ : syracuseStep 397097 = 297823) B297823
theorem B593711 : Blo 263822 593711 := bstep (se 1 (by rfl) ⟨445283, by rfl⟩ : syracuseStep 593711 = 890567) B890567
theorem B397103 : Blo 263822 397103 := bstep (se 1 (by rfl) ⟨297827, by rfl⟩ : syracuseStep 397103 = 595655) B595655
theorem B266031 : Blo 263822 266031 := bstep (se 1 (by rfl) ⟨199523, by rfl⟩ : syracuseStep 266031 = 399047) B399047
theorem B298831 : Blo 263822 298831 := bstep (se 1 (by rfl) ⟨224123, by rfl⟩ : syracuseStep 298831 = 448247) B448247
theorem B6983533 : Blo 263822 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B266139 : Blo 263822 266139 := bstep (se 1 (by rfl) ⟨199604, by rfl⟩ : syracuseStep 266139 = 399209) B399209
theorem B266191 : Blo 263822 266191 := bstep (se 1 (by rfl) ⟨199643, by rfl⟩ : syracuseStep 266191 = 399287) B399287
theorem B266215 : Blo 263822 266215 := bstep (se 1 (by rfl) ⟨199661, by rfl⟩ : syracuseStep 266215 = 399323) B399323
theorem B1609753 : Blo 263822 1609753 := bstep (se 2 (by rfl) ⟨603657, by rfl⟩ : syracuseStep 1609753 = 1207315) B1207315
theorem B299227 : Blo 263822 299227 := bstep (se 1 (by rfl) ⟨224420, by rfl⟩ : syracuseStep 299227 = 448841) B448841
theorem B397577 : Blo 263822 397577 := bstep (se 2 (by rfl) ⟨149091, by rfl⟩ : syracuseStep 397577 = 298183) B298183
theorem B266527 : Blo 263822 266527 := bstep (se 1 (by rfl) ⟨199895, by rfl⟩ : syracuseStep 266527 = 399791) B399791
theorem B266587 : Blo 263822 266587 := bstep (se 1 (by rfl) ⟨199940, by rfl⟩ : syracuseStep 266587 = 399881) B399881
theorem B594287 : Blo 263822 594287 := bstep (se 1 (by rfl) ⟨445715, by rfl⟩ : syracuseStep 594287 = 891431) B891431
theorem B397679 : Blo 263822 397679 := bstep (se 1 (by rfl) ⟨298259, by rfl⟩ : syracuseStep 397679 = 596519) B596519
theorem B266607 : Blo 263822 266607 := bstep (se 1 (by rfl) ⟨199955, by rfl⟩ : syracuseStep 266607 = 399911) B399911
theorem B266663 : Blo 263822 266663 := bstep (se 1 (by rfl) ⟨199997, by rfl⟩ : syracuseStep 266663 = 399995) B399995
theorem B1511855 : Blo 263822 1511855 := bstep (se 1 (by rfl) ⟨1133891, by rfl⟩ : syracuseStep 1511855 = 2267783) B2267783
theorem B594359 : Blo 263822 594359 := bstep (se 1 (by rfl) ⟨445769, by rfl⟩ : syracuseStep 594359 = 891539) B891539
theorem B299515 : Blo 263822 299515 := bstep (se 1 (by rfl) ⟨224636, by rfl⟩ : syracuseStep 299515 = 449273) B449273
theorem B266747 : Blo 263822 266747 := bstep (se 1 (by rfl) ⟨200060, by rfl⟩ : syracuseStep 266747 = 400121) B400121
theorem B266815 : Blo 263822 266815 := bstep (se 1 (by rfl) ⟨200111, by rfl⟩ : syracuseStep 266815 = 400223) B400223
theorem B594503 : Blo 263822 594503 := bstep (se 1 (by rfl) ⟨445877, by rfl⟩ : syracuseStep 594503 = 891755) B891755
theorem B397895 : Blo 263822 397895 := bstep (se 1 (by rfl) ⟨298421, by rfl⟩ : syracuseStep 397895 = 596843) B596843
theorem B266823 : Blo 263822 266823 := bstep (se 1 (by rfl) ⟨200117, by rfl⟩ : syracuseStep 266823 = 400235) B400235
theorem B594539 : Blo 263822 594539 := bstep (se 1 (by rfl) ⟨445904, by rfl⟩ : syracuseStep 594539 = 891809) B891809
theorem B397931 : Blo 263822 397931 := bstep (se 1 (by rfl) ⟨298448, by rfl⟩ : syracuseStep 397931 = 596897) B596897
theorem B299695 : Blo 263822 299695 := bstep (se 1 (by rfl) ⟨224771, by rfl⟩ : syracuseStep 299695 = 449543) B449543
theorem B266975 : Blo 263822 266975 := bstep (se 1 (by rfl) ⟨200231, by rfl⟩ : syracuseStep 266975 = 400463) B400463
theorem B267055 : Blo 263822 267055 := bstep (se 1 (by rfl) ⟨200291, by rfl⟩ : syracuseStep 267055 = 400583) B400583
theorem B398159 : Blo 263822 398159 := bstep (se 1 (by rfl) ⟨298619, by rfl⟩ : syracuseStep 398159 = 597239) B597239
theorem B267163 : Blo 263822 267163 := bstep (se 1 (by rfl) ⟨200372, by rfl⟩ : syracuseStep 267163 = 400745) B400745
theorem B299983 : Blo 263822 299983 := bstep (se 1 (by rfl) ⟨224987, by rfl⟩ : syracuseStep 299983 = 449975) B449975
theorem B267215 : Blo 263822 267215 := bstep (se 1 (by rfl) ⟨200411, by rfl⟩ : syracuseStep 267215 = 400823) B400823
theorem B267239 : Blo 263822 267239 := bstep (se 1 (by rfl) ⟨200429, by rfl⟩ : syracuseStep 267239 = 400859) B400859
theorem B594935 : Blo 263822 594935 := bstep (se 1 (by rfl) ⟨446201, by rfl⟩ : syracuseStep 594935 = 892403) B892403
theorem B398555 : Blo 263822 398555 := bstep (se 1 (by rfl) ⟨298916, by rfl⟩ : syracuseStep 398555 = 597833) B597833
theorem B267551 : Blo 263822 267551 := bstep (se 1 (by rfl) ⟨200663, by rfl⟩ : syracuseStep 267551 = 401327) B401327
theorem B2004263 : Blo 263822 2004263 := bstep (se 1 (by rfl) ⟨1503197, by rfl⟩ : syracuseStep 2004263 = 3006395) B3006395
theorem B300379 : Blo 263822 300379 := bstep (se 1 (by rfl) ⟨225284, by rfl⟩ : syracuseStep 300379 = 450569) B450569
theorem B267611 : Blo 263822 267611 := bstep (se 1 (by rfl) ⟨200708, by rfl⟩ : syracuseStep 267611 = 401417) B401417
theorem B595295 : Blo 263822 595295 := bstep (se 1 (by rfl) ⟨446471, by rfl⟩ : syracuseStep 595295 = 892943) B892943
theorem B1348973 : Blo 263822 1348973 := bstep (se 3 (by rfl) ⟨252932, by rfl⟩ : syracuseStep 1348973 = 505865) B505865
theorem B267631 : Blo 263822 267631 := bstep (se 1 (by rfl) ⟨200723, by rfl⟩ : syracuseStep 267631 = 401447) B401447
theorem B398729 : Blo 263822 398729 := bstep (se 2 (by rfl) ⟨149523, by rfl⟩ : syracuseStep 398729 = 299047) B299047
theorem B267687 : Blo 263822 267687 := bstep (se 1 (by rfl) ⟨200765, by rfl⟩ : syracuseStep 267687 = 401531) B401531
theorem B300487 : Blo 263822 300487 := bstep (se 1 (by rfl) ⟨225365, by rfl⟩ : syracuseStep 300487 = 450731) B450731
theorem B267771 : Blo 263822 267771 := bstep (se 1 (by rfl) ⟨200828, by rfl⟩ : syracuseStep 267771 = 401657) B401657
theorem B595691 : Blo 263822 595691 := bstep (se 1 (by rfl) ⟨446768, by rfl⟩ : syracuseStep 595691 = 893537) B893537
theorem B399083 : Blo 263822 399083 := bstep (se 1 (by rfl) ⟨299312, by rfl⟩ : syracuseStep 399083 = 598625) B598625
theorem B300847 : Blo 263822 300847 := bstep (se 1 (by rfl) ⟨225635, by rfl⟩ : syracuseStep 300847 = 451271) B451271
theorem B890729 : Blo 263822 890729 := bstep (se 2 (by rfl) ⟨334023, by rfl⟩ : syracuseStep 890729 = 668047) B668047
theorem B595817 : Blo 263822 595817 := bstep (se 2 (by rfl) ⟨223431, by rfl⟩ : syracuseStep 595817 = 446863) B446863
theorem B300955 : Blo 263822 300955 := bstep (se 1 (by rfl) ⟨225716, by rfl⟩ : syracuseStep 300955 = 451433) B451433
theorem B399311 : Blo 263822 399311 := bstep (se 1 (by rfl) ⟨299483, by rfl⟩ : syracuseStep 399311 = 598967) B598967
theorem B759937 : Blo 263822 759937 := bstep (se 2 (by rfl) ⟨284976, by rfl⟩ : syracuseStep 759937 = 569953) B569953
theorem B891161 : Blo 263822 891161 := bstep (se 2 (by rfl) ⟨334185, by rfl⟩ : syracuseStep 891161 = 668371) B668371
theorem B11507993 : Blo 263822 11507993 := bstep (se 2 (by rfl) ⟨4315497, by rfl⟩ : syracuseStep 11507993 = 8630995) B8630995
theorem B399707 : Blo 263822 399707 := bstep (se 1 (by rfl) ⟨299780, by rfl⟩ : syracuseStep 399707 = 599561) B599561
theorem B399935 : Blo 263822 399935 := bstep (se 1 (by rfl) ⟨299951, by rfl⟩ : syracuseStep 399935 = 599903) B599903
theorem B596663 : Blo 263822 596663 := bstep (se 1 (by rfl) ⟨447497, by rfl⟩ : syracuseStep 596663 = 894995) B894995
theorem B400055 : Blo 263822 400055 := bstep (se 1 (by rfl) ⟨300041, by rfl⟩ : syracuseStep 400055 = 600083) B600083
theorem B3250925 : Blo 263822 3250925 := bstep (se 3 (by rfl) ⟨609548, by rfl⟩ : syracuseStep 3250925 = 1219097) B1219097
theorem B1284931 : Blo 263822 1284931 := bstep (se 1 (by rfl) ⟨963698, by rfl⟩ : syracuseStep 1284931 = 1927397) B1927397
theorem B596879 : Blo 263822 596879 := bstep (se 1 (by rfl) ⟨447659, by rfl⟩ : syracuseStep 596879 = 895319) B895319
theorem B400283 : Blo 263822 400283 := bstep (se 1 (by rfl) ⟨300212, by rfl⟩ : syracuseStep 400283 = 600425) B600425
theorem B400679 : Blo 263822 400679 := bstep (se 1 (by rfl) ⟨300509, by rfl⟩ : syracuseStep 400679 = 601019) B601019
theorem B400763 : Blo 263822 400763 := bstep (se 1 (by rfl) ⟨300572, by rfl⟩ : syracuseStep 400763 = 601145) B601145
theorem B400889 : Blo 263822 400889 := bstep (se 2 (by rfl) ⟨150333, by rfl⟩ : syracuseStep 400889 = 300667) B300667
theorem B1515023 : Blo 263822 1515023 := bstep (se 1 (by rfl) ⟨1136267, by rfl⟩ : syracuseStep 1515023 = 2272535) B2272535
theorem B335431 : Blo 263822 335431 := bstep (se 1 (by rfl) ⟨251573, by rfl⟩ : syracuseStep 335431 = 503147) B503147
theorem B892511 : Blo 263822 892511 := bstep (se 1 (by rfl) ⟨669383, by rfl⟩ : syracuseStep 892511 = 1338767) B1338767
theorem B597599 : Blo 263822 597599 := bstep (se 1 (by rfl) ⟨448199, by rfl⟩ : syracuseStep 597599 = 896399) B896399
theorem B400991 : Blo 263822 400991 := bstep (se 1 (by rfl) ⟨300743, by rfl⟩ : syracuseStep 400991 = 601487) B601487
theorem B1351403 : Blo 263822 1351403 := bstep (se 1 (by rfl) ⟨1013552, by rfl⟩ : syracuseStep 1351403 = 2027105) B2027105
theorem B1285895 : Blo 263822 1285895 := bstep (se 1 (by rfl) ⟨964421, by rfl⟩ : syracuseStep 1285895 = 1928843) B1928843
theorem B597815 : Blo 263822 597815 := bstep (se 1 (by rfl) ⟨448361, by rfl⟩ : syracuseStep 597815 = 896723) B896723
theorem B401207 : Blo 263822 401207 := bstep (se 1 (by rfl) ⟨300905, by rfl⟩ : syracuseStep 401207 = 601811) B601811
theorem B598121 : Blo 263822 598121 := bstep (se 2 (by rfl) ⟨224295, by rfl⟩ : syracuseStep 598121 = 448591) B448591
theorem B401513 : Blo 263822 401513 := bstep (se 2 (by rfl) ⟨150567, by rfl⟩ : syracuseStep 401513 = 301135) B301135
theorem B1351889 : Blo 263822 1351889 := bstep (se 2 (by rfl) ⟨506958, by rfl⟩ : syracuseStep 1351889 = 1013917) B1013917
theorem B2433235 : Blo 263822 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B336251 : Blo 263822 336251 := bstep (se 1 (by rfl) ⟨252188, by rfl⟩ : syracuseStep 336251 = 504377) B504377
theorem B598607 : Blo 263822 598607 := bstep (se 1 (by rfl) ⟨448955, by rfl⟩ : syracuseStep 598607 = 897911) B897911
theorem B5120657 : Blo 263822 5120657 := bstep (se 2 (by rfl) ⟨1920246, by rfl⟩ : syracuseStep 5120657 = 3840493) B3840493
theorem B1352375 : Blo 263822 1352375 := bstep (se 1 (by rfl) ⟨1014281, by rfl⟩ : syracuseStep 1352375 = 2028563) B2028563
theorem B598751 : Blo 263822 598751 := bstep (se 1 (by rfl) ⟨449063, by rfl⟩ : syracuseStep 598751 = 898127) B898127
theorem B2564941 : Blo 263822 2564941 := bstep (se 3 (by rfl) ⟨480926, by rfl⟩ : syracuseStep 2564941 = 961853) B961853
theorem B3089335 : Blo 263822 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B1516481 : Blo 263822 1516481 := bstep (se 2 (by rfl) ⟨568680, by rfl⟩ : syracuseStep 1516481 = 1137361) B1137361
theorem B1713089 : Blo 263822 1713089 := bstep (se 2 (by rfl) ⟨642408, by rfl⟩ : syracuseStep 1713089 = 1284817) B1284817
theorem B893915 : Blo 263822 893915 := bstep (se 1 (by rfl) ⟨670436, by rfl⟩ : syracuseStep 893915 = 1340873) B1340873
theorem B599003 : Blo 263822 599003 := bstep (se 1 (by rfl) ⟨449252, by rfl⟩ : syracuseStep 599003 = 898505) B898505
theorem B894077 : Blo 263822 894077 := bstep (se 3 (by rfl) ⟨167639, by rfl⟩ : syracuseStep 894077 = 335279) B335279
theorem B599183 : Blo 263822 599183 := bstep (se 1 (by rfl) ⟨449387, by rfl⟩ : syracuseStep 599183 = 898775) B898775
theorem B1352861 : Blo 263822 1352861 := bstep (se 3 (by rfl) ⟨253661, by rfl⟩ : syracuseStep 1352861 = 507323) B507323
theorem B894185 : Blo 263822 894185 := bstep (se 2 (by rfl) ⟨335319, by rfl⟩ : syracuseStep 894185 = 670639) B670639
theorem B599273 : Blo 263822 599273 := bstep (se 2 (by rfl) ⟨224727, by rfl⟩ : syracuseStep 599273 = 449455) B449455
theorem B599327 : Blo 263822 599327 := bstep (se 1 (by rfl) ⟨449495, by rfl⟩ : syracuseStep 599327 = 898991) B898991
theorem B894347 : Blo 263822 894347 := bstep (se 1 (by rfl) ⟨670760, by rfl⟩ : syracuseStep 894347 = 1341521) B1341521
theorem B501241 : Blo 263822 501241 := bstep (se 2 (by rfl) ⟨187965, by rfl⟩ : syracuseStep 501241 = 375931) B375931
theorem B501545 : Blo 263822 501545 := bstep (se 2 (by rfl) ⟨188079, by rfl⟩ : syracuseStep 501545 = 376159) B376159
theorem B599849 : Blo 263822 599849 := bstep (se 2 (by rfl) ⟨224943, by rfl⟩ : syracuseStep 599849 = 449887) B449887
theorem B2566019 : Blo 263822 2566019 := bstep (se 1 (by rfl) ⟨1924514, by rfl⟩ : syracuseStep 2566019 = 3849029) B3849029
theorem B2434951 : Blo 263822 2434951 := bstep (se 1 (by rfl) ⟨1826213, by rfl⟩ : syracuseStep 2434951 = 3652427) B3652427
theorem B337871 : Blo 263822 337871 := bstep (se 1 (by rfl) ⟨253403, by rfl⟩ : syracuseStep 337871 = 506807) B506807
theorem B1354157 : Blo 263822 1354157 := bstep (se 3 (by rfl) ⟨253904, by rfl⟩ : syracuseStep 1354157 = 507809) B507809
theorem B1911251 : Blo 263822 1911251 := bstep (se 1 (by rfl) ⟨1433438, by rfl⟩ : syracuseStep 1911251 = 2866877) B2866877
theorem B1354319 : Blo 263822 1354319 := bstep (se 1 (by rfl) ⟨1015739, by rfl⟩ : syracuseStep 1354319 = 2031479) B2031479
theorem B535223 : Blo 263822 535223 := bstep (se 1 (by rfl) ⟨401417, by rfl⟩ : syracuseStep 535223 = 802835) B802835
theorem B600911 : Blo 263822 600911 := bstep (se 1 (by rfl) ⟨450683, by rfl⟩ : syracuseStep 600911 = 901367) B901367
theorem B338843 : Blo 263822 338843 := bstep (se 1 (by rfl) ⟨254132, by rfl⟩ : syracuseStep 338843 = 508265) B508265
theorem B502699 : Blo 263822 502699 := bstep (se 1 (by rfl) ⟨377024, by rfl⟩ : syracuseStep 502699 = 754049) B754049
theorem B601127 : Blo 263822 601127 := bstep (se 1 (by rfl) ⟨450845, by rfl⟩ : syracuseStep 601127 = 901691) B901691
theorem B503003 : Blo 263822 503003 := bstep (se 1 (by rfl) ⟨377252, by rfl⟩ : syracuseStep 503003 = 754505) B754505
theorem B3845339 : Blo 263822 3845339 := bstep (se 1 (by rfl) ⟨2884004, by rfl⟩ : syracuseStep 3845339 = 5768009) B5768009
theorem B601307 : Blo 263822 601307 := bstep (se 1 (by rfl) ⟨450980, by rfl⟩ : syracuseStep 601307 = 901961) B901961
theorem B634105 : Blo 263822 634105 := bstep (se 2 (by rfl) ⟨237789, by rfl⟩ : syracuseStep 634105 = 475579) B475579
theorem B10235159 : Blo 263822 10235159 := bstep (se 1 (by rfl) ⟨7676369, by rfl⟩ : syracuseStep 10235159 = 15352739) B15352739
theorem B601505 : Blo 263822 601505 := bstep (se 2 (by rfl) ⟨225564, by rfl⟩ : syracuseStep 601505 = 451129) B451129
theorem B306599 : Blo 263822 306599 := bstep (se 1 (by rfl) ⟨229949, by rfl⟩ : syracuseStep 306599 = 459899) B459899
theorem B568775 : Blo 263822 568775 := bstep (se 1 (by rfl) ⟨426581, by rfl⟩ : syracuseStep 568775 = 853163) B853163
theorem B602063 : Blo 263822 602063 := bstep (se 1 (by rfl) ⟨451547, by rfl⟩ : syracuseStep 602063 = 903095) B903095
theorem B1355777 : Blo 263822 1355777 := bstep (se 2 (by rfl) ⟨508416, by rfl⟩ : syracuseStep 1355777 = 1016833) B1016833
theorem B504073 : Blo 263822 504073 := bstep (se 2 (by rfl) ⟨189027, by rfl⟩ : syracuseStep 504073 = 378055) B378055
theorem B602441 : Blo 263822 602441 := bstep (se 2 (by rfl) ⟨225915, by rfl⟩ : syracuseStep 602441 = 451831) B451831
theorem B897371 : Blo 263822 897371 := bstep (se 1 (by rfl) ⟨673028, by rfl⟩ : syracuseStep 897371 = 1346057) B1346057
theorem B602459 : Blo 263822 602459 := bstep (se 1 (by rfl) ⟨451844, by rfl⟩ : syracuseStep 602459 = 903689) B903689
theorem B3649967 : Blo 263822 3649967 := bstep (se 1 (by rfl) ⟨2737475, by rfl⟩ : syracuseStep 3649967 = 5474951) B5474951
theorem B1356257 : Blo 263822 1356257 := bstep (se 2 (by rfl) ⟨508596, by rfl⟩ : syracuseStep 1356257 = 1017193) B1017193
theorem B2437613 : Blo 263822 2437613 := bstep (se 3 (by rfl) ⟨457052, by rfl⟩ : syracuseStep 2437613 = 914105) B914105
theorem B1520147 : Blo 263822 1520147 := bstep (se 1 (by rfl) ⟨1140110, by rfl⟩ : syracuseStep 1520147 = 2280221) B2280221
theorem B537151 : Blo 263822 537151 := bstep (se 1 (by rfl) ⟨402863, by rfl⟩ : syracuseStep 537151 = 805727) B805727
theorem B308047 : Blo 263822 308047 := bstep (se 1 (by rfl) ⟨231035, by rfl⟩ : syracuseStep 308047 = 462071) B462071
theorem B1717393 : Blo 263822 1717393 := bstep (se 2 (by rfl) ⟨644022, by rfl⟩ : syracuseStep 1717393 = 1288045) B1288045
theorem B1520855 : Blo 263822 1520855 := bstep (se 1 (by rfl) ⟨1140641, by rfl⟩ : syracuseStep 1520855 = 2281283) B2281283
theorem B898343 : Blo 263822 898343 := bstep (se 1 (by rfl) ⟨673757, by rfl⟩ : syracuseStep 898343 = 1347515) B1347515
theorem B505531 : Blo 263822 505531 := bstep (se 1 (by rfl) ⟨379148, by rfl⟩ : syracuseStep 505531 = 758297) B758297
theorem B669647 : Blo 263822 669647 := bstep (se 1 (by rfl) ⟨502235, by rfl⟩ : syracuseStep 669647 = 1004471) B1004471
theorem B899207 : Blo 263822 899207 := bstep (se 1 (by rfl) ⟨674405, by rfl⟩ : syracuseStep 899207 = 1348811) B1348811
theorem B1128887 : Blo 263822 1128887 := bstep (se 1 (by rfl) ⟨846665, by rfl⟩ : syracuseStep 1128887 = 1693331) B1693331
theorem B670315 : Blo 263822 670315 := bstep (se 1 (by rfl) ⟨502736, by rfl⟩ : syracuseStep 670315 = 1005473) B1005473
theorem B670619 : Blo 263822 670619 := bstep (se 1 (by rfl) ⟨502964, by rfl⟩ : syracuseStep 670619 = 1005929) B1005929
theorem B342991 : Blo 263822 342991 := bstep (se 1 (by rfl) ⟨257243, by rfl⟩ : syracuseStep 342991 = 514487) B514487
theorem B670963 : Blo 263822 670963 := bstep (se 1 (by rfl) ⟨503222, by rfl⟩ : syracuseStep 670963 = 1006445) B1006445
theorem B900449 : Blo 263822 900449 := bstep (se 2 (by rfl) ⟨337668, by rfl⟩ : syracuseStep 900449 = 675337) B675337
theorem B507475 : Blo 263822 507475 := bstep (se 1 (by rfl) ⟨380606, by rfl⟩ : syracuseStep 507475 = 761213) B761213
theorem B1916531 : Blo 263822 1916531 := bstep (se 1 (by rfl) ⟨1437398, by rfl⟩ : syracuseStep 1916531 = 2874797) B2874797
theorem B507703 : Blo 263822 507703 := bstep (se 1 (by rfl) ⟨380777, by rfl⟩ : syracuseStep 507703 = 761555) B761555
theorem B671753 : Blo 263822 671753 := bstep (se 2 (by rfl) ⟨251907, by rfl⟩ : syracuseStep 671753 = 503815) B503815
theorem B2015441 : Blo 263822 2015441 := bstep (se 2 (by rfl) ⟨755790, by rfl⟩ : syracuseStep 2015441 = 1511581) B1511581
theorem B409865 : Blo 263822 409865 := bstep (se 2 (by rfl) ⟨153699, by rfl⟩ : syracuseStep 409865 = 307399) B307399
theorem B2572631 : Blo 263822 2572631 := bstep (se 1 (by rfl) ⟨1929473, by rfl⟩ : syracuseStep 2572631 = 3858947) B3858947
theorem B7258531 : Blo 263822 7258531 := bstep (se 1 (by rfl) ⟨5443898, by rfl⟩ : syracuseStep 7258531 = 10887797) B10887797
theorem B541255 : Blo 263822 541255 := bstep (se 1 (by rfl) ⟨405941, by rfl⟩ : syracuseStep 541255 = 811883) B811883
theorem B2015927 : Blo 263822 2015927 := bstep (se 1 (by rfl) ⟨1511945, by rfl⟩ : syracuseStep 2015927 = 3023891) B3023891
theorem B3621827 : Blo 263822 3621827 := bstep (se 1 (by rfl) ⟨2716370, by rfl⟩ : syracuseStep 3621827 = 5432741) B5432741
theorem B672907 : Blo 263822 672907 := bstep (se 1 (by rfl) ⟨504680, by rfl⟩ : syracuseStep 672907 = 1009361) B1009361
theorem B640199 : Blo 263822 640199 := bstep (se 1 (by rfl) ⟨480149, by rfl⟩ : syracuseStep 640199 = 960299) B960299
theorem B902393 : Blo 263822 902393 := bstep (se 2 (by rfl) ⟨338397, by rfl⟩ : syracuseStep 902393 = 676795) B676795
theorem B673211 : Blo 263822 673211 := bstep (se 1 (by rfl) ⟨504908, by rfl⟩ : syracuseStep 673211 = 1009817) B1009817
theorem B902663 : Blo 263822 902663 := bstep (se 1 (by rfl) ⟨676997, by rfl⟩ : syracuseStep 902663 = 1353995) B1353995
theorem B476833 : Blo 263822 476833 := bstep (se 2 (by rfl) ⟨178812, by rfl⟩ : syracuseStep 476833 = 357625) B357625
theorem B1296157 : Blo 263822 1296157 := bstep (se 3 (by rfl) ⟨243029, by rfl⟩ : syracuseStep 1296157 = 486059) B486059
theorem B1001753 : Blo 263822 1001753 := bstep (se 2 (by rfl) ⟨375657, by rfl⟩ : syracuseStep 1001753 = 751315) B751315
theorem B1624349 : Blo 263822 1624349 := bstep (se 3 (by rfl) ⟨304565, by rfl⟩ : syracuseStep 1624349 = 609131) B609131
theorem B1526159 : Blo 263822 1526159 := bstep (se 1 (by rfl) ⟨1144619, by rfl⟩ : syracuseStep 1526159 = 2289239) B2289239
theorem B903635 : Blo 263822 903635 := bstep (se 1 (by rfl) ⟨677726, by rfl⟩ : syracuseStep 903635 = 1355453) B1355453
theorem B903743 : Blo 263822 903743 := bstep (se 1 (by rfl) ⟨677807, by rfl⟩ : syracuseStep 903743 = 1355615) B1355615
theorem B2017871 : Blo 263822 2017871 := bstep (se 1 (by rfl) ⟨1513403, by rfl⟩ : syracuseStep 2017871 = 3026807) B3026807
theorem B379513 : Blo 263822 379513 := bstep (se 2 (by rfl) ⟨142317, by rfl⟩ : syracuseStep 379513 = 284635) B284635
theorem B674527 : Blo 263822 674527 := bstep (se 1 (by rfl) ⟨505895, by rfl⟩ : syracuseStep 674527 = 1011791) B1011791
theorem B674639 : Blo 263822 674639 := bstep (se 1 (by rfl) ⟨505979, by rfl⟩ : syracuseStep 674639 = 1011959) B1011959
theorem B2608043 : Blo 263822 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B5459345 : Blo 263822 5459345 := bstep (se 2 (by rfl) ⟨2047254, by rfl⟩ : syracuseStep 5459345 = 4094509) B4094509
theorem B675287 : Blo 263822 675287 := bstep (se 1 (by rfl) ⟨506465, by rfl⟩ : syracuseStep 675287 = 1012931) B1012931
theorem B445945 : Blo 263822 445945 := bstep (se 2 (by rfl) ⟨167229, by rfl⟩ : syracuseStep 445945 = 334459) B334459
theorem B446215 : Blo 263822 446215 := bstep (se 1 (by rfl) ⟨334661, by rfl⟩ : syracuseStep 446215 = 669323) B669323
theorem B446249 : Blo 263822 446249 := bstep (se 2 (by rfl) ⟨167343, by rfl⟩ : syracuseStep 446249 = 334687) B334687
theorem B675641 : Blo 263822 675641 := bstep (se 2 (by rfl) ⟨253365, by rfl⟩ : syracuseStep 675641 = 506731) B506731
theorem B577487 : Blo 263822 577487 := bstep (se 1 (by rfl) ⟨433115, by rfl⟩ : syracuseStep 577487 = 866231) B866231
theorem B2019329 : Blo 263822 2019329 := bstep (se 2 (by rfl) ⟨757248, by rfl⟩ : syracuseStep 2019329 = 1514497) B1514497
theorem B1003529 : Blo 263822 1003529 := bstep (se 2 (by rfl) ⟨376323, by rfl⟩ : syracuseStep 1003529 = 752647) B752647
theorem B643081 : Blo 263822 643081 := bstep (se 2 (by rfl) ⟨241155, by rfl⟩ : syracuseStep 643081 = 482311) B482311
theorem B2281931 : Blo 263822 2281931 := bstep (se 1 (by rfl) ⟨1711448, by rfl⟩ : syracuseStep 2281931 = 3422897) B3422897
theorem B446971 : Blo 263822 446971 := bstep (se 1 (by rfl) ⟨335228, by rfl⟩ : syracuseStep 446971 = 670457) B670457
theorem B1626923 : Blo 263822 1626923 := bstep (se 1 (by rfl) ⟨1220192, by rfl⟩ : syracuseStep 1626923 = 2440385) B2440385
theorem B283439 : Blo 263822 283439 := bstep (se 1 (by rfl) ⟨212579, by rfl⟩ : syracuseStep 283439 = 425159) B425159
theorem B447403 : Blo 263822 447403 := bstep (se 1 (by rfl) ⟨335552, by rfl⟩ : syracuseStep 447403 = 671105) B671105
theorem B1004669 : Blo 263822 1004669 := bstep (se 3 (by rfl) ⟨188375, by rfl⟩ : syracuseStep 1004669 = 376751) B376751
theorem B1529047 : Blo 263822 1529047 := bstep (se 1 (by rfl) ⟨1146785, by rfl⟩ : syracuseStep 1529047 = 2293571) B2293571
theorem B447707 : Blo 263822 447707 := bstep (se 1 (by rfl) ⟨335780, by rfl⟩ : syracuseStep 447707 = 671561) B671561
theorem B283943 : Blo 263822 283943 := bstep (se 1 (by rfl) ⟨212957, by rfl⟩ : syracuseStep 283943 = 425915) B425915
theorem B677281 : Blo 263822 677281 := bstep (se 2 (by rfl) ⟨253980, by rfl⟩ : syracuseStep 677281 = 507961) B507961
theorem B284071 : Blo 263822 284071 := bstep (se 1 (by rfl) ⟨213053, by rfl⟩ : syracuseStep 284071 = 426107) B426107
theorem B447943 : Blo 263822 447943 := bstep (se 1 (by rfl) ⟨335957, by rfl⟩ : syracuseStep 447943 = 671915) B671915
theorem B480863 : Blo 263822 480863 := bstep (se 1 (by rfl) ⟨360647, by rfl⟩ : syracuseStep 480863 = 721295) B721295
theorem B448463 : Blo 263822 448463 := bstep (se 1 (by rfl) ⟨336347, by rfl⟩ : syracuseStep 448463 = 672695) B672695
theorem B284891 : Blo 263822 284891 := bstep (se 1 (by rfl) ⟨213668, by rfl⟩ : syracuseStep 284891 = 427337) B427337
theorem B2152727 : Blo 263822 2152727 := bstep (se 1 (by rfl) ⟨1614545, by rfl⟩ : syracuseStep 2152727 = 3229091) B3229091
theorem B809327 : Blo 263822 809327 := bstep (se 1 (by rfl) ⟨606995, by rfl⟩ : syracuseStep 809327 = 1213991) B1213991
theorem B1366397 : Blo 263822 1366397 := bstep (se 3 (by rfl) ⟨256199, by rfl⟩ : syracuseStep 1366397 = 512399) B512399
theorem B317947 : Blo 263822 317947 := bstep (se 1 (by rfl) ⟨238460, by rfl⟩ : syracuseStep 317947 = 476921) B476921
theorem B449131 : Blo 263822 449131 := bstep (se 1 (by rfl) ⟨336848, by rfl⟩ : syracuseStep 449131 = 673697) B673697
theorem B1366807 : Blo 263822 1366807 := bstep (se 1 (by rfl) ⟨1025105, by rfl⟩ : syracuseStep 1366807 = 2050211) B2050211
theorem B449435 : Blo 263822 449435 := bstep (se 1 (by rfl) ⟨337076, by rfl⟩ : syracuseStep 449435 = 674153) B674153
theorem B2284595 : Blo 263822 2284595 := bstep (se 1 (by rfl) ⟨1713446, by rfl⟩ : syracuseStep 2284595 = 3426893) B3426893
theorem B1694843 : Blo 263822 1694843 := bstep (se 1 (by rfl) ⟨1271132, by rfl⟩ : syracuseStep 1694843 = 2542265) B2542265
theorem B2317501 : Blo 263822 2317501 := bstep (se 3 (by rfl) ⟨434531, by rfl⟩ : syracuseStep 2317501 = 869063) B869063
theorem B5790937 : Blo 263822 5790937 := bstep (se 2 (by rfl) ⟨2171601, by rfl⟩ : syracuseStep 5790937 = 4343203) B4343203
theorem B1007417 : Blo 263822 1007417 := bstep (se 2 (by rfl) ⟨377781, by rfl⟩ : syracuseStep 1007417 = 755563) B755563
theorem B1236809 : Blo 263822 1236809 := bstep (se 2 (by rfl) ⟨463803, by rfl⟩ : syracuseStep 1236809 = 927607) B927607
theorem B1138607 : Blo 263822 1138607 := bstep (se 1 (by rfl) ⟨853955, by rfl⟩ : syracuseStep 1138607 = 1707911) B1707911
theorem B2547719 : Blo 263822 2547719 := bstep (se 1 (by rfl) ⟨1910789, by rfl⟩ : syracuseStep 2547719 = 3821579) B3821579
theorem B647297 : Blo 263822 647297 := bstep (se 2 (by rfl) ⟨242736, by rfl⟩ : syracuseStep 647297 = 485473) B485473
theorem B1139017 : Blo 263822 1139017 := bstep (se 2 (by rfl) ⟨427131, by rfl⟩ : syracuseStep 1139017 = 854263) B854263
theorem B9659357 : Blo 263822 9659357 := bstep (se 3 (by rfl) ⟨1811129, by rfl⟩ : syracuseStep 9659357 = 3622259) B3622259
theorem B1434631 : Blo 263822 1434631 := bstep (se 1 (by rfl) ⟨1075973, by rfl⟩ : syracuseStep 1434631 = 2151947) B2151947
theorem B681311 : Blo 263822 681311 := bstep (se 1 (by rfl) ⟨510983, by rfl⟩ : syracuseStep 681311 = 1021967) B1021967
theorem B1009057 : Blo 263822 1009057 := bstep (se 2 (by rfl) ⟨378396, by rfl⟩ : syracuseStep 1009057 = 756793) B756793
theorem B2025161 : Blo 263822 2025161 := bstep (se 2 (by rfl) ⟨759435, by rfl⟩ : syracuseStep 2025161 = 1518871) B1518871
theorem B845959 : Blo 263822 845959 := bstep (se 1 (by rfl) ⟨634469, by rfl⟩ : syracuseStep 845959 = 1268939) B1268939
theorem B846089 : Blo 263822 846089 := bstep (se 2 (by rfl) ⟨317283, by rfl⟩ : syracuseStep 846089 = 634567) B634567
theorem B911945 : Blo 263822 911945 := bstep (se 2 (by rfl) ⟨341979, by rfl⟩ : syracuseStep 911945 = 683959) B683959
theorem B1075987 : Blo 263822 1075987 := bstep (se 1 (by rfl) ⟨806990, by rfl⟩ : syracuseStep 1075987 = 1613981) B1613981
theorem B847037 : Blo 263822 847037 := bstep (se 3 (by rfl) ⟨158819, by rfl⟩ : syracuseStep 847037 = 317639) B317639
theorem B1502651 : Blo 263822 1502651 := bstep (se 1 (by rfl) ⟨1126988, by rfl⟩ : syracuseStep 1502651 = 2253977) B2253977
theorem B1273553 : Blo 263822 1273553 := bstep (se 2 (by rfl) ⟨477582, by rfl⟩ : syracuseStep 1273553 = 955165) B955165
theorem B1339091 : Blo 263822 1339091 := bstep (se 1 (by rfl) ⟨1004318, by rfl⟩ : syracuseStep 1339091 = 2008637) B2008637
theorem B3502081 : Blo 263822 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B1339739 : Blo 263822 1339739 := bstep (se 1 (by rfl) ⟨1004804, by rfl⟩ : syracuseStep 1339739 = 2009609) B2009609
theorem B11497949 : Blo 263822 11497949 := bstep (se 3 (by rfl) ⟨2155865, by rfl⟩ : syracuseStep 11497949 = 4311731) B4311731
theorem B3404339 : Blo 263822 3404339 := bstep (se 1 (by rfl) ⟨2553254, by rfl⟩ : syracuseStep 3404339 = 5106509) B5106509
theorem B1504109 : Blo 263822 1504109 := bstep (se 3 (by rfl) ⟨282020, by rfl⟩ : syracuseStep 1504109 = 564041) B564041
theorem B2880461 : Blo 263822 2880461 := bstep (se 3 (by rfl) ⟨540086, by rfl⟩ : syracuseStep 2880461 = 1080173) B1080173
theorem B7468081 : Blo 263822 7468081 := bstep (se 2 (by rfl) ⟨2800530, by rfl⟩ : syracuseStep 7468081 = 5601061) B5601061
theorem B2258077 : Blo 263822 2258077 := bstep (se 3 (by rfl) ⟨423389, by rfl⟩ : syracuseStep 2258077 = 846779) B846779
theorem B1701121 : Blo 263822 1701121 := bstep (se 2 (by rfl) ⟨637920, by rfl⟩ : syracuseStep 1701121 = 1275841) B1275841
theorem B6419735 : Blo 263822 6419735 := bstep (se 1 (by rfl) ⟨4814801, by rfl⟩ : syracuseStep 6419735 = 9629603) B9629603
theorem B1340711 : Blo 263822 1340711 := bstep (se 1 (by rfl) ⟨1005533, by rfl⟩ : syracuseStep 1340711 = 2011067) B2011067
theorem B1144169 : Blo 263822 1144169 := bstep (se 2 (by rfl) ⟨429063, by rfl⟩ : syracuseStep 1144169 = 858127) B858127
theorem B358619 : Blo 263822 358619 := bstep (se 1 (by rfl) ⟨268964, by rfl⟩ : syracuseStep 358619 = 537929) B537929
theorem B2062583 : Blo 263822 2062583 := bstep (se 1 (by rfl) ⟨1546937, by rfl⟩ : syracuseStep 2062583 = 3093875) B3093875
theorem B457211 : Blo 263822 457211 := bstep (se 1 (by rfl) ⟨342908, by rfl⟩ : syracuseStep 457211 = 685817) B685817
theorem B12909131 : Blo 263822 12909131 := bstep (se 1 (by rfl) ⟨9681848, by rfl⟩ : syracuseStep 12909131 = 19363697) B19363697
theorem B1276859 : Blo 263822 1276859 := bstep (se 1 (by rfl) ⟨957644, by rfl⟩ : syracuseStep 1276859 = 1915289) B1915289
theorem B1342817 : Blo 263822 1342817 := bstep (se 2 (by rfl) ⟨503556, by rfl⟩ : syracuseStep 1342817 = 1007113) B1007113
theorem B720343 : Blo 263822 720343 := bstep (se 1 (by rfl) ⟨540257, by rfl⟩ : syracuseStep 720343 = 1080515) B1080515
theorem B18677765 : Blo 263822 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B1343627 : Blo 263822 1343627 := bstep (se 1 (by rfl) ⟨1007720, by rfl⟩ : syracuseStep 1343627 = 2015441) B2015441
theorem B3244313 : Blo 263822 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B852407 : Blo 263822 852407 := bstep (se 1 (by rfl) ⟨639305, by rfl⟩ : syracuseStep 852407 = 1278611) B1278611
theorem B1343951 : Blo 263822 1343951 := bstep (se 1 (by rfl) ⟨1007963, by rfl⟩ : syracuseStep 1343951 = 2015927) B2015927
theorem B721673 : Blo 263822 721673 := bstep (se 2 (by rfl) ⟨270627, by rfl⟩ : syracuseStep 721673 = 541255) B541255
theorem B426799 : Blo 263822 426799 := bstep (se 1 (by rfl) ⟨320099, by rfl⟩ : syracuseStep 426799 = 640199) B640199
theorem B1082899 : Blo 263822 1082899 := bstep (se 1 (by rfl) ⟨812174, by rfl⟩ : syracuseStep 1082899 = 1624349) B1624349
theorem B263847 : Blo 263822 263847 := bstep (se 1 (by rfl) ⟨197885, by rfl⟩ : syracuseStep 263847 = 395771) B395771
theorem B1345247 : Blo 263822 1345247 := bstep (se 1 (by rfl) ⟨1008935, by rfl⟩ : syracuseStep 1345247 = 2017871) B2017871
theorem B263931 : Blo 263822 263931 := bstep (se 1 (by rfl) ⟨197948, by rfl⟩ : syracuseStep 263931 = 395897) B395897
theorem B263967 : Blo 263822 263967 := bstep (se 1 (by rfl) ⟨197975, by rfl⟩ : syracuseStep 263967 = 395951) B395951
theorem B263999 : Blo 263822 263999 := bstep (se 1 (by rfl) ⟨197999, by rfl⟩ : syracuseStep 263999 = 395999) B395999
theorem B1345409 : Blo 263822 1345409 := bstep (se 2 (by rfl) ⟨504528, by rfl⟩ : syracuseStep 1345409 = 1009057) B1009057
theorem B264175 : Blo 263822 264175 := bstep (se 1 (by rfl) ⟨198131, by rfl⟩ : syracuseStep 264175 = 396263) B396263
theorem B755837 : Blo 263822 755837 := bstep (se 3 (by rfl) ⟨141719, by rfl⟩ : syracuseStep 755837 = 283439) B283439
theorem B264347 : Blo 263822 264347 := bstep (se 1 (by rfl) ⟨198260, by rfl⟩ : syracuseStep 264347 = 396521) B396521
theorem B264383 : Blo 263822 264383 := bstep (se 1 (by rfl) ⟨198287, by rfl⟩ : syracuseStep 264383 = 396575) B396575
theorem B1509623 : Blo 263822 1509623 := bstep (se 1 (by rfl) ⟨1132217, by rfl⟩ : syracuseStep 1509623 = 2264435) B2264435
theorem B3639563 : Blo 263822 3639563 := bstep (se 1 (by rfl) ⟨2729672, by rfl⟩ : syracuseStep 3639563 = 5459345) B5459345
theorem B264495 : Blo 263822 264495 := bstep (se 1 (by rfl) ⟨198371, by rfl⟩ : syracuseStep 264495 = 396743) B396743
theorem B297499 : Blo 263822 297499 := bstep (se 1 (by rfl) ⟨223124, by rfl⟩ : syracuseStep 297499 = 446249) B446249
theorem B264731 : Blo 263822 264731 := bstep (se 1 (by rfl) ⟨198548, by rfl⟩ : syracuseStep 264731 = 397097) B397097
theorem B395807 : Blo 263822 395807 := bstep (se 1 (by rfl) ⟨296855, by rfl⟩ : syracuseStep 395807 = 593711) B593711
theorem B264735 : Blo 263822 264735 := bstep (se 1 (by rfl) ⟨198551, by rfl⟩ : syracuseStep 264735 = 397103) B397103
theorem B1346219 : Blo 263822 1346219 := bstep (se 1 (by rfl) ⟨1009664, by rfl⟩ : syracuseStep 1346219 = 2019329) B2019329
theorem B265051 : Blo 263822 265051 := bstep (se 1 (by rfl) ⟨198788, by rfl⟩ : syracuseStep 265051 = 397577) B397577
theorem B396191 : Blo 263822 396191 := bstep (se 1 (by rfl) ⟨297143, by rfl⟩ : syracuseStep 396191 = 594287) B594287
theorem B265119 : Blo 263822 265119 := bstep (se 1 (by rfl) ⟨198839, by rfl⟩ : syracuseStep 265119 = 397679) B397679
theorem B396239 : Blo 263822 396239 := bstep (se 1 (by rfl) ⟨297179, by rfl⟩ : syracuseStep 396239 = 594359) B594359
theorem B36637717 : Blo 263822 36637717 := bstep (se 6 (by rfl) ⟨858696, by rfl⟩ : syracuseStep 36637717 = 1717393) B1717393
theorem B396329 : Blo 263822 396329 := bstep (se 2 (by rfl) ⟨148623, by rfl⟩ : syracuseStep 396329 = 297247) B297247
theorem B396335 : Blo 263822 396335 := bstep (se 1 (by rfl) ⟨297251, by rfl⟩ : syracuseStep 396335 = 594503) B594503
theorem B265263 : Blo 263822 265263 := bstep (se 1 (by rfl) ⟨198947, by rfl⟩ : syracuseStep 265263 = 397895) B397895
theorem B396359 : Blo 263822 396359 := bstep (se 1 (by rfl) ⟨297269, by rfl⟩ : syracuseStep 396359 = 594539) B594539
theorem B265287 : Blo 263822 265287 := bstep (se 1 (by rfl) ⟨198965, by rfl⟩ : syracuseStep 265287 = 397931) B397931
theorem B265439 : Blo 263822 265439 := bstep (se 1 (by rfl) ⟨199079, by rfl⟩ : syracuseStep 265439 = 398159) B398159
theorem B396623 : Blo 263822 396623 := bstep (se 1 (by rfl) ⟨297467, by rfl⟩ : syracuseStep 396623 = 594935) B594935
theorem B396713 : Blo 263822 396713 := bstep (se 2 (by rfl) ⟨148767, by rfl⟩ : syracuseStep 396713 = 297535) B297535
theorem B757181 : Blo 263822 757181 := bstep (se 3 (by rfl) ⟨141971, by rfl⟩ : syracuseStep 757181 = 283943) B283943
theorem B298471 : Blo 263822 298471 := bstep (se 1 (by rfl) ⟨223853, by rfl⟩ : syracuseStep 298471 = 447707) B447707
theorem B265703 : Blo 263822 265703 := bstep (se 1 (by rfl) ⟨199277, by rfl⟩ : syracuseStep 265703 = 398555) B398555
theorem B396863 : Blo 263822 396863 := bstep (se 1 (by rfl) ⟨297647, by rfl⟩ : syracuseStep 396863 = 595295) B595295
theorem B265819 : Blo 263822 265819 := bstep (se 1 (by rfl) ⟨199364, by rfl⟩ : syracuseStep 265819 = 398729) B398729
theorem B397127 : Blo 263822 397127 := bstep (se 1 (by rfl) ⟨297845, by rfl⟩ : syracuseStep 397127 = 595691) B595691
theorem B266055 : Blo 263822 266055 := bstep (se 1 (by rfl) ⟨199541, by rfl⟩ : syracuseStep 266055 = 399083) B399083
theorem B593819 : Blo 263822 593819 := bstep (se 1 (by rfl) ⟨445364, by rfl⟩ : syracuseStep 593819 = 890729) B890729
theorem B397211 : Blo 263822 397211 := bstep (se 1 (by rfl) ⟨297908, by rfl⟩ : syracuseStep 397211 = 595817) B595817
theorem B298975 : Blo 263822 298975 := bstep (se 1 (by rfl) ⟨224231, by rfl⟩ : syracuseStep 298975 = 448463) B448463
theorem B266207 : Blo 263822 266207 := bstep (se 1 (by rfl) ⟨199655, by rfl⟩ : syracuseStep 266207 = 399311) B399311
theorem B5738597 : Blo 263822 5738597 := bstep (se 4 (by rfl) ⟨537993, by rfl⟩ : syracuseStep 5738597 = 1075987) B1075987
theorem B594107 : Blo 263822 594107 := bstep (se 1 (by rfl) ⟨445580, by rfl⟩ : syracuseStep 594107 = 891161) B891161
theorem B7671995 : Blo 263822 7671995 := bstep (se 1 (by rfl) ⟨5753996, by rfl⟩ : syracuseStep 7671995 = 11507993) B11507993
theorem B266471 : Blo 263822 266471 := bstep (se 1 (by rfl) ⟨199853, by rfl⟩ : syracuseStep 266471 = 399707) B399707
theorem B1282301 : Blo 263822 1282301 := bstep (se 3 (by rfl) ⟨240431, by rfl⟩ : syracuseStep 1282301 = 480863) B480863
theorem B266623 : Blo 263822 266623 := bstep (se 1 (by rfl) ⟨199967, by rfl⟩ : syracuseStep 266623 = 399935) B399935
theorem B397775 : Blo 263822 397775 := bstep (se 1 (by rfl) ⟨298331, by rfl⟩ : syracuseStep 397775 = 596663) B596663
theorem B266703 : Blo 263822 266703 := bstep (se 1 (by rfl) ⟨200027, by rfl⟩ : syracuseStep 266703 = 400055) B400055
theorem B2167283 : Blo 263822 2167283 := bstep (se 1 (by rfl) ⟨1625462, by rfl⟩ : syracuseStep 2167283 = 3250925) B3250925
theorem B397817 : Blo 263822 397817 := bstep (se 2 (by rfl) ⟨149181, by rfl⟩ : syracuseStep 397817 = 298363) B298363
theorem B397919 : Blo 263822 397919 := bstep (se 1 (by rfl) ⟨298439, by rfl⟩ : syracuseStep 397919 = 596879) B596879
theorem B299623 : Blo 263822 299623 := bstep (se 1 (by rfl) ⟨224717, by rfl⟩ : syracuseStep 299623 = 449435) B449435
theorem B266855 : Blo 263822 266855 := bstep (se 1 (by rfl) ⟨200141, by rfl⟩ : syracuseStep 266855 = 400283) B400283
theorem B594593 : Blo 263822 594593 := bstep (se 2 (by rfl) ⟨222972, by rfl⟩ : syracuseStep 594593 = 445945) B445945
theorem B267119 : Blo 263822 267119 := bstep (se 1 (by rfl) ⟨200339, by rfl⟩ : syracuseStep 267119 = 400679) B400679
theorem B267175 : Blo 263822 267175 := bstep (se 1 (by rfl) ⟨200381, by rfl⟩ : syracuseStep 267175 = 400763) B400763
theorem B267259 : Blo 263822 267259 := bstep (se 1 (by rfl) ⟨200444, by rfl⟩ : syracuseStep 267259 = 400889) B400889
theorem B594953 : Blo 263822 594953 := bstep (se 2 (by rfl) ⟨223107, by rfl⟩ : syracuseStep 594953 = 446215) B446215
theorem B595007 : Blo 263822 595007 := bstep (se 1 (by rfl) ⟨446255, by rfl⟩ : syracuseStep 595007 = 892511) B892511
theorem B398399 : Blo 263822 398399 := bstep (se 1 (by rfl) ⟨298799, by rfl⟩ : syracuseStep 398399 = 597599) B597599
theorem B267327 : Blo 263822 267327 := bstep (se 1 (by rfl) ⟨200495, by rfl⟩ : syracuseStep 267327 = 400991) B400991
theorem B398441 : Blo 263822 398441 := bstep (se 2 (by rfl) ⟨149415, by rfl⟩ : syracuseStep 398441 = 298831) B298831
theorem B9311377 : Blo 263822 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B857263 : Blo 263822 857263 := bstep (se 1 (by rfl) ⟨642947, by rfl⟩ : syracuseStep 857263 = 1285895) B1285895
theorem B398543 : Blo 263822 398543 := bstep (se 1 (by rfl) ⟨298907, by rfl⟩ : syracuseStep 398543 = 597815) B597815
theorem B267471 : Blo 263822 267471 := bstep (se 1 (by rfl) ⟨200603, by rfl⟩ : syracuseStep 267471 = 401207) B401207
theorem B759071 : Blo 263822 759071 := bstep (se 1 (by rfl) ⟨569303, by rfl⟩ : syracuseStep 759071 = 1138607) B1138607
theorem B857441 : Blo 263822 857441 := bstep (se 2 (by rfl) ⟨321540, by rfl⟩ : syracuseStep 857441 = 643081) B643081
theorem B398747 : Blo 263822 398747 := bstep (se 1 (by rfl) ⟨299060, by rfl⟩ : syracuseStep 398747 = 598121) B598121
theorem B267675 : Blo 263822 267675 := bstep (se 1 (by rfl) ⟨200756, by rfl⟩ : syracuseStep 267675 = 401513) B401513
theorem B431531 : Blo 263822 431531 := bstep (se 1 (by rfl) ⟨323648, by rfl⟩ : syracuseStep 431531 = 647297) B647297
theorem B398969 : Blo 263822 398969 := bstep (se 2 (by rfl) ⟨149613, by rfl⟩ : syracuseStep 398969 = 299227) B299227
theorem B399071 : Blo 263822 399071 := bstep (se 1 (by rfl) ⟨299303, by rfl⟩ : syracuseStep 399071 = 598607) B598607
theorem B3413771 : Blo 263822 3413771 := bstep (se 1 (by rfl) ⟨2560328, by rfl⟩ : syracuseStep 3413771 = 5120657) B5120657
theorem B399167 : Blo 263822 399167 := bstep (se 1 (by rfl) ⟨299375, by rfl⟩ : syracuseStep 399167 = 598751) B598751
theorem B759709 : Blo 263822 759709 := bstep (se 3 (by rfl) ⟨142445, by rfl⟩ : syracuseStep 759709 = 284891) B284891
theorem B595943 : Blo 263822 595943 := bstep (se 1 (by rfl) ⟨446957, by rfl⟩ : syracuseStep 595943 = 893915) B893915
theorem B399335 : Blo 263822 399335 := bstep (se 1 (by rfl) ⟨299501, by rfl⟩ : syracuseStep 399335 = 599003) B599003
theorem B595961 : Blo 263822 595961 := bstep (se 2 (by rfl) ⟨223485, by rfl⟩ : syracuseStep 595961 = 446971) B446971
theorem B399353 : Blo 263822 399353 := bstep (se 2 (by rfl) ⟨149757, by rfl⟩ : syracuseStep 399353 = 299515) B299515
theorem B596051 : Blo 263822 596051 := bstep (se 1 (by rfl) ⟨447038, by rfl⟩ : syracuseStep 596051 = 894077) B894077
theorem B399455 : Blo 263822 399455 := bstep (se 1 (by rfl) ⟨299591, by rfl⟩ : syracuseStep 399455 = 599183) B599183
theorem B596123 : Blo 263822 596123 := bstep (se 1 (by rfl) ⟨447092, by rfl⟩ : syracuseStep 596123 = 894185) B894185
theorem B399515 : Blo 263822 399515 := bstep (se 1 (by rfl) ⟨299636, by rfl⟩ : syracuseStep 399515 = 599273) B599273
theorem B399551 : Blo 263822 399551 := bstep (se 1 (by rfl) ⟨299663, by rfl⟩ : syracuseStep 399551 = 599327) B599327
theorem B399593 : Blo 263822 399593 := bstep (se 2 (by rfl) ⟨149847, by rfl⟩ : syracuseStep 399593 = 299695) B299695
theorem B596231 : Blo 263822 596231 := bstep (se 1 (by rfl) ⟨447173, by rfl⟩ : syracuseStep 596231 = 894347) B894347
theorem B4069757 : Blo 263822 4069757 := bstep (se 3 (by rfl) ⟨763079, by rfl⟩ : syracuseStep 4069757 = 1526159) B1526159
theorem B1350107 : Blo 263822 1350107 := bstep (se 1 (by rfl) ⟨1012580, by rfl⟩ : syracuseStep 1350107 = 2025161) B2025161
theorem B334363 : Blo 263822 334363 := bstep (se 1 (by rfl) ⟨250772, by rfl⟩ : syracuseStep 334363 = 501545) B501545
theorem B399899 : Blo 263822 399899 := bstep (se 1 (by rfl) ⟨299924, by rfl⟩ : syracuseStep 399899 = 599849) B599849
theorem B596537 : Blo 263822 596537 := bstep (se 2 (by rfl) ⟨223701, by rfl⟩ : syracuseStep 596537 = 447403) B447403
theorem B1710679 : Blo 263822 1710679 := bstep (se 1 (by rfl) ⟨1283009, by rfl⟩ : syracuseStep 1710679 = 2566019) B2566019
theorem B399977 : Blo 263822 399977 := bstep (se 2 (by rfl) ⟨149991, by rfl⟩ : syracuseStep 399977 = 299983) B299983
theorem B564059 : Blo 263822 564059 := bstep (se 1 (by rfl) ⟨423044, by rfl⟩ : syracuseStep 564059 = 846089) B846089
theorem B2431853 : Blo 263822 2431853 := bstep (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) B911945
theorem B2038729 : Blo 263822 2038729 := bstep (se 2 (by rfl) ⟨764523, by rfl⟩ : syracuseStep 2038729 = 1529047) B1529047
theorem B2268161 : Blo 263822 2268161 := bstep (se 2 (by rfl) ⟨850560, by rfl⟩ : syracuseStep 2268161 = 1701121) B1701121
theorem B400505 : Blo 263822 400505 := bstep (se 2 (by rfl) ⟨150189, by rfl⟩ : syracuseStep 400505 = 300379) B300379
theorem B400607 : Blo 263822 400607 := bstep (se 1 (by rfl) ⟨300455, by rfl⟩ : syracuseStep 400607 = 600911) B600911
theorem B597257 : Blo 263822 597257 := bstep (se 2 (by rfl) ⟨223971, by rfl⟩ : syracuseStep 597257 = 447943) B447943
theorem B400649 : Blo 263822 400649 := bstep (se 2 (by rfl) ⟨150243, by rfl⟩ : syracuseStep 400649 = 300487) B300487
theorem B400751 : Blo 263822 400751 := bstep (se 1 (by rfl) ⟨300563, by rfl⟩ : syracuseStep 400751 = 601127) B601127
theorem B564691 : Blo 263822 564691 := bstep (se 1 (by rfl) ⟨423518, by rfl⟩ : syracuseStep 564691 = 847037) B847037
theorem B335335 : Blo 263822 335335 := bstep (se 1 (by rfl) ⟨251501, by rfl⟩ : syracuseStep 335335 = 503003) B503003
theorem B2563559 : Blo 263822 2563559 := bstep (se 1 (by rfl) ⟨1922669, by rfl⟩ : syracuseStep 2563559 = 3845339) B3845339
theorem B400871 : Blo 263822 400871 := bstep (se 1 (by rfl) ⟨300653, by rfl⟩ : syracuseStep 400871 = 601307) B601307
theorem B6823439 : Blo 263822 6823439 := bstep (se 1 (by rfl) ⟨5117579, by rfl⟩ : syracuseStep 6823439 = 10235159) B10235159
theorem B401003 : Blo 263822 401003 := bstep (se 1 (by rfl) ⟨300752, by rfl⟩ : syracuseStep 401003 = 601505) B601505
theorem B401129 : Blo 263822 401129 := bstep (se 2 (by rfl) ⟨150423, by rfl⟩ : syracuseStep 401129 = 300847) B300847
theorem B6954781 : Blo 263822 6954781 := bstep (se 3 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 6954781 = 2608043) B2608043
theorem B3841829 : Blo 263822 3841829 := bstep (se 4 (by rfl) ⟨360171, by rfl⟩ : syracuseStep 3841829 = 720343) B720343
theorem B892727 : Blo 263822 892727 := bstep (se 1 (by rfl) ⟨669545, by rfl⟩ : syracuseStep 892727 = 1339091) B1339091
theorem B401273 : Blo 263822 401273 := bstep (se 2 (by rfl) ⟨150477, by rfl⟩ : syracuseStep 401273 = 300955) B300955
theorem B401375 : Blo 263822 401375 := bstep (se 1 (by rfl) ⟨301031, by rfl⟩ : syracuseStep 401375 = 602063) B602063
theorem B401627 : Blo 263822 401627 := bstep (se 1 (by rfl) ⟨301220, by rfl⟩ : syracuseStep 401627 = 602441) B602441
theorem B893159 : Blo 263822 893159 := bstep (se 1 (by rfl) ⟨669869, by rfl⟩ : syracuseStep 893159 = 1339739) B1339739
theorem B598247 : Blo 263822 598247 := bstep (se 1 (by rfl) ⟨448685, by rfl⟩ : syracuseStep 598247 = 897371) B897371
theorem B401639 : Blo 263822 401639 := bstep (se 1 (by rfl) ⟨301229, by rfl⟩ : syracuseStep 401639 = 602459) B602459
theorem B2433311 : Blo 263822 2433311 := bstep (se 1 (by rfl) ⟨1824983, by rfl⟩ : syracuseStep 2433311 = 3649967) B3649967
theorem B2269559 : Blo 263822 2269559 := bstep (se 1 (by rfl) ⟨1702169, by rfl⟩ : syracuseStep 2269559 = 3404339) B3404339
theorem B893753 : Blo 263822 893753 := bstep (se 2 (by rfl) ⟨335157, by rfl⟩ : syracuseStep 893753 = 670315) B670315
theorem B598841 : Blo 263822 598841 := bstep (se 2 (by rfl) ⟨224565, by rfl⟩ : syracuseStep 598841 = 449131) B449131
theorem B893807 : Blo 263822 893807 := bstep (se 1 (by rfl) ⟨670355, by rfl⟩ : syracuseStep 893807 = 1340711) B1340711
theorem B598895 : Blo 263822 598895 := bstep (se 1 (by rfl) ⟨449171, by rfl⟩ : syracuseStep 598895 = 898343) B898343
theorem B762779 : Blo 263822 762779 := bstep (se 1 (by rfl) ⟨572084, by rfl⟩ : syracuseStep 762779 = 1144169) B1144169
theorem B1713241 : Blo 263822 1713241 := bstep (se 2 (by rfl) ⟨642465, by rfl⟩ : syracuseStep 1713241 = 1284931) B1284931
theorem B599471 : Blo 263822 599471 := bstep (se 1 (by rfl) ⟨449603, by rfl⟩ : syracuseStep 599471 = 899207) B899207
theorem B3090001 : Blo 263822 3090001 := bstep (se 2 (by rfl) ⟨1158750, by rfl⟩ : syracuseStep 3090001 = 2317501) B2317501
theorem B894617 : Blo 263822 894617 := bstep (se 2 (by rfl) ⟨335481, by rfl⟩ : syracuseStep 894617 = 670963) B670963
theorem B304807 : Blo 263822 304807 := bstep (se 1 (by rfl) ⟨228605, by rfl⟩ : syracuseStep 304807 = 457211) B457211
theorem B12986405 : Blo 263822 12986405 := bstep (se 4 (by rfl) ⟨1217475, by rfl⟩ : syracuseStep 12986405 = 2434951) B2434951
theorem B895211 : Blo 263822 895211 := bstep (se 1 (by rfl) ⟨671408, by rfl⟩ : syracuseStep 895211 = 1342817) B1342817
theorem B600299 : Blo 263822 600299 := bstep (se 1 (by rfl) ⟨450224, by rfl⟩ : syracuseStep 600299 = 900449) B900449
theorem B3058505 : Blo 263822 3058505 := bstep (se 2 (by rfl) ⟨1146939, by rfl⟩ : syracuseStep 3058505 = 2293879) B2293879
theorem B1715087 : Blo 263822 1715087 := bstep (se 1 (by rfl) ⟨1286315, by rfl⟩ : syracuseStep 1715087 = 2572631) B2572631
theorem B1518689 : Blo 263822 1518689 := bstep (se 2 (by rfl) ⟨569508, by rfl⟩ : syracuseStep 1518689 = 1139017) B1139017
theorem B9678041 : Blo 263822 9678041 := bstep (se 2 (by rfl) ⟨3629265, by rfl⟩ : syracuseStep 9678041 = 7258531) B7258531
theorem B1092973 : Blo 263822 1092973 := bstep (se 3 (by rfl) ⟨204932, by rfl⟩ : syracuseStep 1092973 = 409865) B409865
theorem B896507 : Blo 263822 896507 := bstep (se 1 (by rfl) ⟨672380, by rfl⟩ : syracuseStep 896507 = 1344761) B1344761
theorem B601595 : Blo 263822 601595 := bstep (se 1 (by rfl) ⟨451196, by rfl⟩ : syracuseStep 601595 = 902393) B902393
theorem B896669 : Blo 263822 896669 := bstep (se 3 (by rfl) ⟨168125, by rfl⟩ : syracuseStep 896669 = 336251) B336251
theorem B601775 : Blo 263822 601775 := bstep (se 1 (by rfl) ⟨451331, by rfl⟩ : syracuseStep 601775 = 902663) B902663
theorem B3419921 : Blo 263822 3419921 := bstep (se 2 (by rfl) ⟨1282470, by rfl⟩ : syracuseStep 3419921 = 2564941) B2564941
theorem B1912841 : Blo 263822 1912841 := bstep (se 2 (by rfl) ⟨717315, by rfl⟩ : syracuseStep 1912841 = 1434631) B1434631
theorem B897209 : Blo 263822 897209 := bstep (se 2 (by rfl) ⟨336453, by rfl⟩ : syracuseStep 897209 = 672907) B672907
theorem B667835 : Blo 263822 667835 := bstep (se 1 (by rfl) ⟨500876, by rfl⟩ : syracuseStep 667835 = 1001753) B1001753
theorem B504119 : Blo 263822 504119 := bstep (se 1 (by rfl) ⟨378089, by rfl⟩ : syracuseStep 504119 = 756179) B756179
theorem B602423 : Blo 263822 602423 := bstep (se 1 (by rfl) ⟨451817, by rfl⟩ : syracuseStep 602423 = 903635) B903635
theorem B602495 : Blo 263822 602495 := bstep (se 1 (by rfl) ⟨451871, by rfl⟩ : syracuseStep 602495 = 903743) B903743
theorem B668321 : Blo 263822 668321 := bstep (se 2 (by rfl) ⟨250620, by rfl⟩ : syracuseStep 668321 = 501241) B501241
theorem B963353 : Blo 263822 963353 := bstep (se 2 (by rfl) ⟨361257, by rfl⟩ : syracuseStep 963353 = 722515) B722515
theorem B4338461 : Blo 263822 4338461 := bstep (se 3 (by rfl) ⟨813461, by rfl⟩ : syracuseStep 4338461 = 1626923) B1626923
theorem B635777 : Blo 263822 635777 := bstep (se 2 (by rfl) ⟨238416, by rfl⟩ : syracuseStep 635777 = 476833) B476833
theorem B669019 : Blo 263822 669019 := bstep (se 1 (by rfl) ⟨501764, by rfl⟩ : syracuseStep 669019 = 1003529) B1003529
theorem B1127945 : Blo 263822 1127945 := bstep (se 2 (by rfl) ⟨422979, by rfl⟩ : syracuseStep 1127945 = 845959) B845959
theorem B1521287 : Blo 263822 1521287 := bstep (se 1 (by rfl) ⟨1140965, by rfl⟩ : syracuseStep 1521287 = 2281931) B2281931
theorem B669779 : Blo 263822 669779 := bstep (se 1 (by rfl) ⟨502334, by rfl⟩ : syracuseStep 669779 = 1004669) B1004669
theorem B506017 : Blo 263822 506017 := bstep (se 2 (by rfl) ⟨189756, by rfl⟩ : syracuseStep 506017 = 379513) B379513
theorem B899315 : Blo 263822 899315 := bstep (se 1 (by rfl) ⟨674486, by rfl⟩ : syracuseStep 899315 = 1348973) B1348973
theorem B1816829 : Blo 263822 1816829 := bstep (se 3 (by rfl) ⟨340655, by rfl⟩ : syracuseStep 1816829 = 681311) B681311
theorem B899369 : Blo 263822 899369 := bstep (se 2 (by rfl) ⟨337263, by rfl⟩ : syracuseStep 899369 = 674527) B674527
theorem B670265 : Blo 263822 670265 := bstep (se 2 (by rfl) ⟨251349, by rfl⟩ : syracuseStep 670265 = 502699) B502699
theorem B571961 : Blo 263822 571961 := bstep (se 2 (by rfl) ⟨214485, by rfl⟩ : syracuseStep 571961 = 428971) B428971
theorem B539551 : Blo 263822 539551 := bstep (se 1 (by rfl) ⟨404663, by rfl⟩ : syracuseStep 539551 = 809327) B809327
theorem B3849257 : Blo 263822 3849257 := bstep (se 2 (by rfl) ⟨1443471, by rfl⟩ : syracuseStep 3849257 = 2886943) B2886943
theorem B1523063 : Blo 263822 1523063 := bstep (se 1 (by rfl) ⟨1142297, by rfl⟩ : syracuseStep 1523063 = 2284595) B2284595
theorem B1129895 : Blo 263822 1129895 := bstep (se 1 (by rfl) ⟨847421, by rfl⟩ : syracuseStep 1129895 = 1694843) B1694843
theorem B900935 : Blo 263822 900935 := bstep (se 1 (by rfl) ⟨675701, by rfl⟩ : syracuseStep 900935 = 1351403) B1351403
theorem B671611 : Blo 263822 671611 := bstep (se 1 (by rfl) ⟨503708, by rfl⟩ : syracuseStep 671611 = 1007417) B1007417
theorem B900989 : Blo 263822 900989 := bstep (se 3 (by rfl) ⟨168935, by rfl⟩ : syracuseStep 900989 = 337871) B337871
theorem B2146337 : Blo 263822 2146337 := bstep (se 2 (by rfl) ⟨804876, by rfl⟩ : syracuseStep 2146337 = 1609753) B1609753
theorem B901259 : Blo 263822 901259 := bstep (se 1 (by rfl) ⟨675944, by rfl⟩ : syracuseStep 901259 = 1351889) B1351889
theorem B39829765 : Blo 263822 39829765 := bstep (se 4 (by rfl) ⟨3734040, by rfl⟩ : syracuseStep 39829765 = 7468081) B7468081
theorem B672097 : Blo 263822 672097 := bstep (se 2 (by rfl) ⟨252036, by rfl⟩ : syracuseStep 672097 = 504073) B504073
theorem B901583 : Blo 263822 901583 := bstep (se 1 (by rfl) ⟨676187, by rfl⟩ : syracuseStep 901583 = 1352375) B1352375
theorem B6439571 : Blo 263822 6439571 := bstep (se 1 (by rfl) ⟨4829678, by rfl⟩ : syracuseStep 6439571 = 9659357) B9659357
theorem B901907 : Blo 263822 901907 := bstep (se 1 (by rfl) ⟨676430, by rfl⟩ : syracuseStep 901907 = 1352861) B1352861
theorem B410729 : Blo 263822 410729 := bstep (se 2 (by rfl) ⟨154023, by rfl⟩ : syracuseStep 410729 = 308047) B308047
theorem B902771 : Blo 263822 902771 := bstep (se 1 (by rfl) ⟨677078, by rfl⟩ : syracuseStep 902771 = 1354157) B1354157
theorem B902879 : Blo 263822 902879 := bstep (se 1 (by rfl) ⟨677159, by rfl⟩ : syracuseStep 902879 = 1354319) B1354319
theorem B903041 : Blo 263822 903041 := bstep (se 2 (by rfl) ⟨338640, by rfl⟩ : syracuseStep 903041 = 677281) B677281
theorem B378761 : Blo 263822 378761 := bstep (se 2 (by rfl) ⟨142035, by rfl⟩ : syracuseStep 378761 = 284071) B284071
theorem B4900837 : Blo 263822 4900837 := bstep (se 4 (by rfl) ⟨459453, by rfl⟩ : syracuseStep 4900837 = 918907) B918907
theorem B674041 : Blo 263822 674041 := bstep (se 2 (by rfl) ⟨252765, by rfl⟩ : syracuseStep 674041 = 505531) B505531
theorem B1001767 : Blo 263822 1001767 := bstep (se 1 (by rfl) ⟨751325, by rfl⟩ : syracuseStep 1001767 = 1502651) B1502651
theorem B379183 : Blo 263822 379183 := bstep (se 1 (by rfl) ⟨284387, by rfl⟩ : syracuseStep 379183 = 568775) B568775
theorem B903581 : Blo 263822 903581 := bstep (se 3 (by rfl) ⟨169421, by rfl⟩ : syracuseStep 903581 = 338843) B338843
theorem B903851 : Blo 263822 903851 := bstep (se 1 (by rfl) ⟨677888, by rfl⟩ : syracuseStep 903851 = 1355777) B1355777
theorem B904171 : Blo 263822 904171 := bstep (se 1 (by rfl) ⟨678128, by rfl⟩ : syracuseStep 904171 = 1356257) B1356257
theorem B1625075 : Blo 263822 1625075 := bstep (se 1 (by rfl) ⟨1218806, by rfl⟩ : syracuseStep 1625075 = 2437613) B2437613
theorem B1002739 : Blo 263822 1002739 := bstep (se 1 (by rfl) ⟨752054, by rfl⟩ : syracuseStep 1002739 = 1504109) B1504109
theorem B1920307 : Blo 263822 1920307 := bstep (se 1 (by rfl) ⟨1440230, by rfl⟩ : syracuseStep 1920307 = 2880461) B2880461
theorem B4279823 : Blo 263822 4279823 := bstep (se 1 (by rfl) ⟨3209867, by rfl⟩ : syracuseStep 4279823 = 6419735) B6419735
theorem B1822409 : Blo 263822 1822409 := bstep (se 2 (by rfl) ⟨683403, by rfl⟩ : syracuseStep 1822409 = 1366807) B1366807
theorem B446431 : Blo 263822 446431 := bstep (se 1 (by rfl) ⟨334823, by rfl⟩ : syracuseStep 446431 = 669647) B669647
theorem B7721249 : Blo 263822 7721249 := bstep (se 2 (by rfl) ⟨2895468, by rfl⟩ : syracuseStep 7721249 = 5790937) B5790937
theorem B8606087 : Blo 263822 8606087 := bstep (se 1 (by rfl) ⟨6454565, by rfl⟩ : syracuseStep 8606087 = 12909131) B12909131
theorem B447079 : Blo 263822 447079 := bstep (se 1 (by rfl) ⟨335309, by rfl⟩ : syracuseStep 447079 = 670619) B670619
theorem B447241 : Blo 263822 447241 := bstep (se 2 (by rfl) ⟨167715, by rfl⟩ : syracuseStep 447241 = 335431) B335431
theorem B676633 : Blo 263822 676633 := bstep (se 2 (by rfl) ⟨253737, by rfl⟩ : syracuseStep 676633 = 507475) B507475
theorem B3298157 : Blo 263822 3298157 := bstep (se 3 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 3298157 = 1236809) B1236809
theorem B676937 : Blo 263822 676937 := bstep (se 2 (by rfl) ⟨253851, by rfl⟩ : syracuseStep 676937 = 507703) B507703
theorem B447835 : Blo 263822 447835 := bstep (se 1 (by rfl) ⟨335876, by rfl⟩ : syracuseStep 447835 = 671753) B671753
theorem B1004987 : Blo 263822 1004987 := bstep (se 1 (by rfl) ⟨753740, by rfl⟩ : syracuseStep 1004987 = 1507481) B1507481
theorem B2414551 : Blo 263822 2414551 := bstep (se 1 (by rfl) ⟨1810913, by rfl⟩ : syracuseStep 2414551 = 3621827) B3621827
theorem B448807 : Blo 263822 448807 := bstep (se 1 (by rfl) ⟨336605, by rfl⟩ : syracuseStep 448807 = 673211) B673211
theorem B2709883 : Blo 263822 2709883 := bstep (se 1 (by rfl) ⟨2032412, by rfl⟩ : syracuseStep 2709883 = 4064825) B4064825
theorem B4119113 : Blo 263822 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B482131 : Blo 263822 482131 := bstep (se 1 (by rfl) ⟨361598, by rfl⟩ : syracuseStep 482131 = 723197) B723197
theorem B449759 : Blo 263822 449759 := bstep (se 1 (by rfl) ⟨337319, by rfl⟩ : syracuseStep 449759 = 674639) B674639
theorem B3825269 : Blo 263822 3825269 := bstep (se 5 (by rfl) ⟨179309, by rfl⟩ : syracuseStep 3825269 = 358619) B358619
theorem B450191 : Blo 263822 450191 := bstep (se 1 (by rfl) ⟨337643, by rfl⟩ : syracuseStep 450191 = 675287) B675287
theorem B1728209 : Blo 263822 1728209 := bstep (se 2 (by rfl) ⟨648078, by rfl⟩ : syracuseStep 1728209 = 1296157) B1296157
theorem B450427 : Blo 263822 450427 := bstep (se 1 (by rfl) ⟨337820, by rfl⟩ : syracuseStep 450427 = 675641) B675641
theorem B1007903 : Blo 263822 1007903 := bstep (se 1 (by rfl) ⟨755927, by rfl⟩ : syracuseStep 1007903 = 1511855) B1511855
theorem B1336175 : Blo 263822 1336175 := bstep (se 1 (by rfl) ⟨1002131, by rfl⟩ : syracuseStep 1336175 = 2004263) B2004263
theorem B1435151 : Blo 263822 1435151 := bstep (se 1 (by rfl) ⟨1076363, by rfl⟩ : syracuseStep 1435151 = 2152727) B2152727
theorem B910931 : Blo 263822 910931 := bstep (se 1 (by rfl) ⟨683198, by rfl⟩ : syracuseStep 910931 = 1366397) B1366397
theorem B845473 : Blo 263822 845473 := bstep (se 2 (by rfl) ⟨317052, by rfl⟩ : syracuseStep 845473 = 634105) B634105
theorem B1010015 : Blo 263822 1010015 := bstep (se 1 (by rfl) ⟨757511, by rfl⟩ : syracuseStep 1010015 = 1515023) B1515023
theorem B1698479 : Blo 263822 1698479 := bstep (se 1 (by rfl) ⟨1273859, by rfl⟩ : syracuseStep 1698479 = 2547719) B2547719
theorem B1010987 : Blo 263822 1010987 := bstep (se 1 (by rfl) ⟨758240, by rfl⟩ : syracuseStep 1010987 = 1516481) B1516481
theorem B1142059 : Blo 263822 1142059 := bstep (se 1 (by rfl) ⟨856544, by rfl⟩ : syracuseStep 1142059 = 1713089) B1713089
theorem B716201 : Blo 263822 716201 := bstep (se 2 (by rfl) ⟨268575, by rfl⟩ : syracuseStep 716201 = 537151) B537151
theorem B3010769 : Blo 263822 3010769 := bstep (se 2 (by rfl) ⟨1129038, by rfl⟩ : syracuseStep 3010769 = 2258077) B2258077
theorem B1274167 : Blo 263822 1274167 := bstep (se 1 (by rfl) ⟨955625, by rfl⟩ : syracuseStep 1274167 = 1911251) B1911251
theorem B356815 : Blo 263822 356815 := bstep (se 1 (by rfl) ⟨267611, by rfl⟩ : syracuseStep 356815 = 535223) B535223
theorem B849035 : Blo 263822 849035 := bstep (se 1 (by rfl) ⟨636776, by rfl⟩ : syracuseStep 849035 = 1273553) B1273553
theorem B1013249 : Blo 263822 1013249 := bstep (se 2 (by rfl) ⟨379968, by rfl⟩ : syracuseStep 1013249 = 759937) B759937
theorem B7665299 : Blo 263822 7665299 := bstep (se 1 (by rfl) ⟨5748974, by rfl⟩ : syracuseStep 7665299 = 11497949) B11497949
theorem B1013431 : Blo 263822 1013431 := bstep (se 1 (by rfl) ⟨760073, by rfl⟩ : syracuseStep 1013431 = 1520147) B1520147
theorem B423929 : Blo 263822 423929 := bstep (se 2 (by rfl) ⟨158973, by rfl⟩ : syracuseStep 423929 = 317947) B317947
theorem B1013903 : Blo 263822 1013903 := bstep (se 1 (by rfl) ⟨760427, by rfl⟩ : syracuseStep 1013903 = 1520855) B1520855
theorem B817597 : Blo 263822 817597 := bstep (se 3 (by rfl) ⟨153299, by rfl⟩ : syracuseStep 817597 = 306599) B306599
theorem B457321 : Blo 263822 457321 := bstep (se 2 (by rfl) ⟨171495, by rfl⟩ : syracuseStep 457321 = 342991) B342991
theorem B1375055 : Blo 263822 1375055 := bstep (se 1 (by rfl) ⟨1031291, by rfl⟩ : syracuseStep 1375055 = 2062583) B2062583
theorem B752591 : Blo 263822 752591 := bstep (se 1 (by rfl) ⟨564443, by rfl⟩ : syracuseStep 752591 = 1128887) B1128887
theorem B851239 : Blo 263822 851239 := bstep (se 1 (by rfl) ⟨638429, by rfl⟩ : syracuseStep 851239 = 1276859) B1276859
theorem B1277687 : Blo 263822 1277687 := bstep (se 1 (by rfl) ⟨958265, by rfl⟩ : syracuseStep 1277687 = 1916531) B1916531
theorem B1539965 : Blo 263822 1539965 := bstep (se 3 (by rfl) ⟨288743, by rfl⟩ : syracuseStep 1539965 = 577487) B577487
theorem B12451843 : Blo 263822 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B2162875 : Blo 263822 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B4293047 : Blo 263822 4293047 := bstep (se 1 (by rfl) ⟨3219785, by rfl⟩ : syracuseStep 4293047 = 6439571) B6439571
theorem B2426375 : Blo 263822 2426375 := bstep (se 1 (by rfl) ⟨1819781, by rfl⟩ : syracuseStep 2426375 = 3639563) B3639563
theorem B263871 : Blo 263822 263871 := bstep (se 1 (by rfl) ⟨197903, by rfl⟩ : syracuseStep 263871 = 395807) B395807
theorem B264127 : Blo 263822 264127 := bstep (se 1 (by rfl) ⟨198095, by rfl⟩ : syracuseStep 264127 = 396191) B396191
theorem B264159 : Blo 263822 264159 := bstep (se 1 (by rfl) ⟨198119, by rfl⟩ : syracuseStep 264159 = 396239) B396239
theorem B1083383 : Blo 263822 1083383 := bstep (se 1 (by rfl) ⟨812537, by rfl⟩ : syracuseStep 1083383 = 1625075) B1625075
theorem B1443865 : Blo 263822 1443865 := bstep (se 2 (by rfl) ⟨541449, by rfl⟩ : syracuseStep 1443865 = 1082899) B1082899
theorem B264219 : Blo 263822 264219 := bstep (se 1 (by rfl) ⟨198164, by rfl⟩ : syracuseStep 264219 = 396329) B396329
theorem B264223 : Blo 263822 264223 := bstep (se 1 (by rfl) ⟨198167, by rfl⟩ : syracuseStep 264223 = 396335) B396335
theorem B264239 : Blo 263822 264239 := bstep (se 1 (by rfl) ⟨198179, by rfl⟩ : syracuseStep 264239 = 396359) B396359
theorem B11569229 : Blo 263822 11569229 := bstep (se 3 (by rfl) ⟨2169230, by rfl⟩ : syracuseStep 11569229 = 4338461) B4338461
theorem B264415 : Blo 263822 264415 := bstep (se 1 (by rfl) ⟨198311, by rfl⟩ : syracuseStep 264415 = 396623) B396623
theorem B264475 : Blo 263822 264475 := bstep (se 1 (by rfl) ⟨198356, by rfl⟩ : syracuseStep 264475 = 396713) B396713
theorem B4360517 : Blo 263822 4360517 := bstep (se 4 (by rfl) ⟨408798, by rfl⟩ : syracuseStep 4360517 = 817597) B817597
theorem B2853215 : Blo 263822 2853215 := bstep (se 1 (by rfl) ⟨2139911, by rfl⟩ : syracuseStep 2853215 = 4279823) B4279823
theorem B264575 : Blo 263822 264575 := bstep (se 1 (by rfl) ⟨198431, by rfl⟩ : syracuseStep 264575 = 396863) B396863
theorem B2034077 : Blo 263822 2034077 := bstep (se 3 (by rfl) ⟨381389, by rfl⟩ : syracuseStep 2034077 = 762779) B762779
theorem B1214939 : Blo 263822 1214939 := bstep (se 1 (by rfl) ⟨911204, by rfl⟩ : syracuseStep 1214939 = 1822409) B1822409
theorem B264751 : Blo 263822 264751 := bstep (se 1 (by rfl) ⟨198563, by rfl⟩ : syracuseStep 264751 = 397127) B397127
theorem B395879 : Blo 263822 395879 := bstep (se 1 (by rfl) ⟨296909, by rfl⟩ : syracuseStep 395879 = 593819) B593819
theorem B264807 : Blo 263822 264807 := bstep (se 1 (by rfl) ⟨198605, by rfl⟩ : syracuseStep 264807 = 397211) B397211
theorem B396071 : Blo 263822 396071 := bstep (se 1 (by rfl) ⟨297053, by rfl⟩ : syracuseStep 396071 = 594107) B594107
theorem B5114663 : Blo 263822 5114663 := bstep (se 1 (by rfl) ⟨3835997, by rfl⟩ : syracuseStep 5114663 = 7671995) B7671995
theorem B854867 : Blo 263822 854867 := bstep (se 1 (by rfl) ⟨641150, by rfl⟩ : syracuseStep 854867 = 1282301) B1282301
theorem B5737391 : Blo 263822 5737391 := bstep (se 1 (by rfl) ⟨4303043, by rfl⟩ : syracuseStep 5737391 = 8606087) B8606087
theorem B265183 : Blo 263822 265183 := bstep (se 1 (by rfl) ⟨198887, by rfl⟩ : syracuseStep 265183 = 397775) B397775
theorem B265211 : Blo 263822 265211 := bstep (se 1 (by rfl) ⟨198908, by rfl⟩ : syracuseStep 265211 = 397817) B397817
theorem B265279 : Blo 263822 265279 := bstep (se 1 (by rfl) ⟨198959, by rfl⟩ : syracuseStep 265279 = 397919) B397919
theorem B396395 : Blo 263822 396395 := bstep (se 1 (by rfl) ⟨297296, by rfl⟩ : syracuseStep 396395 = 594593) B594593
theorem B2198771 : Blo 263822 2198771 := bstep (se 1 (by rfl) ⟨1649078, by rfl⟩ : syracuseStep 2198771 = 3298157) B3298157
theorem B396635 : Blo 263822 396635 := bstep (se 1 (by rfl) ⟨297476, by rfl⟩ : syracuseStep 396635 = 594953) B594953
theorem B396665 : Blo 263822 396665 := bstep (se 2 (by rfl) ⟨148749, by rfl⟩ : syracuseStep 396665 = 297499) B297499
theorem B396671 : Blo 263822 396671 := bstep (se 1 (by rfl) ⟨297503, by rfl⟩ : syracuseStep 396671 = 595007) B595007
theorem B265599 : Blo 263822 265599 := bstep (se 1 (by rfl) ⟨199199, by rfl⟩ : syracuseStep 265599 = 398399) B398399
theorem B265627 : Blo 263822 265627 := bstep (se 1 (by rfl) ⟨199220, by rfl⟩ : syracuseStep 265627 = 398441) B398441
theorem B265695 : Blo 263822 265695 := bstep (se 1 (by rfl) ⟨199271, by rfl⟩ : syracuseStep 265695 = 398543) B398543
theorem B265831 : Blo 263822 265831 := bstep (se 1 (by rfl) ⟨199373, by rfl⟩ : syracuseStep 265831 = 398747) B398747
theorem B265979 : Blo 263822 265979 := bstep (se 1 (by rfl) ⟨199484, by rfl⟩ : syracuseStep 265979 = 398969) B398969
theorem B266047 : Blo 263822 266047 := bstep (se 1 (by rfl) ⟨199535, by rfl⟩ : syracuseStep 266047 = 399071) B399071
theorem B266111 : Blo 263822 266111 := bstep (se 1 (by rfl) ⟨199583, by rfl⟩ : syracuseStep 266111 = 399167) B399167
theorem B397295 : Blo 263822 397295 := bstep (se 1 (by rfl) ⟨297971, by rfl⟩ : syracuseStep 397295 = 595943) B595943
theorem B266223 : Blo 263822 266223 := bstep (se 1 (by rfl) ⟨199667, by rfl⟩ : syracuseStep 266223 = 399335) B399335
theorem B397307 : Blo 263822 397307 := bstep (se 1 (by rfl) ⟨297980, by rfl⟩ : syracuseStep 397307 = 595961) B595961
theorem B266235 : Blo 263822 266235 := bstep (se 1 (by rfl) ⟨199676, by rfl⟩ : syracuseStep 266235 = 399353) B399353
theorem B397367 : Blo 263822 397367 := bstep (se 1 (by rfl) ⟨298025, by rfl⟩ : syracuseStep 397367 = 596051) B596051
theorem B266303 : Blo 263822 266303 := bstep (se 1 (by rfl) ⟨199727, by rfl⟩ : syracuseStep 266303 = 399455) B399455
theorem B397415 : Blo 263822 397415 := bstep (se 1 (by rfl) ⟨298061, by rfl⟩ : syracuseStep 397415 = 596123) B596123
theorem B266343 : Blo 263822 266343 := bstep (se 1 (by rfl) ⟨199757, by rfl⟩ : syracuseStep 266343 = 399515) B399515
theorem B266367 : Blo 263822 266367 := bstep (se 1 (by rfl) ⟨199775, by rfl⟩ : syracuseStep 266367 = 399551) B399551
theorem B266395 : Blo 263822 266395 := bstep (se 1 (by rfl) ⟨199796, by rfl⟩ : syracuseStep 266395 = 399593) B399593
theorem B397487 : Blo 263822 397487 := bstep (se 1 (by rfl) ⟨298115, by rfl⟩ : syracuseStep 397487 = 596231) B596231
theorem B2429149 : Blo 263822 2429149 := bstep (se 3 (by rfl) ⟨455465, by rfl⟩ : syracuseStep 2429149 = 910931) B910931
theorem B266599 : Blo 263822 266599 := bstep (se 1 (by rfl) ⟨199949, by rfl⟩ : syracuseStep 266599 = 399899) B399899
theorem B397691 : Blo 263822 397691 := bstep (se 1 (by rfl) ⟨298268, by rfl⟩ : syracuseStep 397691 = 596537) B596537
theorem B2560409 : Blo 263822 2560409 := bstep (se 2 (by rfl) ⟨960153, by rfl⟩ : syracuseStep 2560409 = 1920307) B1920307
theorem B266651 : Blo 263822 266651 := bstep (se 1 (by rfl) ⟨199988, by rfl⟩ : syracuseStep 266651 = 399977) B399977
theorem B397961 : Blo 263822 397961 := bstep (se 2 (by rfl) ⟨149235, by rfl⟩ : syracuseStep 397961 = 298471) B298471
theorem B1512107 : Blo 263822 1512107 := bstep (se 1 (by rfl) ⟨1134080, by rfl⟩ : syracuseStep 1512107 = 2268161) B2268161
theorem B267003 : Blo 263822 267003 := bstep (se 1 (by rfl) ⟨200252, by rfl⟩ : syracuseStep 267003 = 400505) B400505
theorem B267071 : Blo 263822 267071 := bstep (se 1 (by rfl) ⟨200303, by rfl⟩ : syracuseStep 267071 = 400607) B400607
theorem B299839 : Blo 263822 299839 := bstep (se 1 (by rfl) ⟨224879, by rfl⟩ : syracuseStep 299839 = 449759) B449759
theorem B398171 : Blo 263822 398171 := bstep (se 1 (by rfl) ⟨298628, by rfl⟩ : syracuseStep 398171 = 597257) B597257
theorem B267099 : Blo 263822 267099 := bstep (se 1 (by rfl) ⟨200324, by rfl⟩ : syracuseStep 267099 = 400649) B400649
theorem B267167 : Blo 263822 267167 := bstep (se 1 (by rfl) ⟨200375, by rfl⟩ : syracuseStep 267167 = 400751) B400751
theorem B1709039 : Blo 263822 1709039 := bstep (se 1 (by rfl) ⟨1281779, by rfl⟩ : syracuseStep 1709039 = 2563559) B2563559
theorem B267247 : Blo 263822 267247 := bstep (se 1 (by rfl) ⟨200435, by rfl⟩ : syracuseStep 267247 = 400871) B400871
theorem B267335 : Blo 263822 267335 := bstep (se 1 (by rfl) ⟨200501, by rfl⟩ : syracuseStep 267335 = 401003) B401003
theorem B300127 : Blo 263822 300127 := bstep (se 1 (by rfl) ⟨225095, by rfl⟩ : syracuseStep 300127 = 450191) B450191
theorem B1152139 : Blo 263822 1152139 := bstep (se 1 (by rfl) ⟨864104, by rfl⟩ : syracuseStep 1152139 = 1728209) B1728209
theorem B267419 : Blo 263822 267419 := bstep (se 1 (by rfl) ⟨200564, by rfl⟩ : syracuseStep 267419 = 401129) B401129
theorem B2561219 : Blo 263822 2561219 := bstep (se 1 (by rfl) ⟨1920914, by rfl⟩ : syracuseStep 2561219 = 3841829) B3841829
theorem B595151 : Blo 263822 595151 := bstep (se 1 (by rfl) ⟨446363, by rfl⟩ : syracuseStep 595151 = 892727) B892727
theorem B267515 : Blo 263822 267515 := bstep (se 1 (by rfl) ⟨200636, by rfl⟩ : syracuseStep 267515 = 401273) B401273
theorem B595241 : Blo 263822 595241 := bstep (se 2 (by rfl) ⟨223215, by rfl⟩ : syracuseStep 595241 = 446431) B446431
theorem B398633 : Blo 263822 398633 := bstep (se 2 (by rfl) ⟨149487, by rfl⟩ : syracuseStep 398633 = 298975) B298975
theorem B267583 : Blo 263822 267583 := bstep (se 1 (by rfl) ⟨200687, by rfl⟩ : syracuseStep 267583 = 401375) B401375
theorem B267751 : Blo 263822 267751 := bstep (se 1 (by rfl) ⟨200813, by rfl⟩ : syracuseStep 267751 = 401627) B401627
theorem B595439 : Blo 263822 595439 := bstep (se 1 (by rfl) ⟨446579, by rfl⟩ : syracuseStep 595439 = 893159) B893159
theorem B398831 : Blo 263822 398831 := bstep (se 1 (by rfl) ⟨299123, by rfl⟩ : syracuseStep 398831 = 598247) B598247
theorem B267759 : Blo 263822 267759 := bstep (se 1 (by rfl) ⟨200819, by rfl⟩ : syracuseStep 267759 = 401639) B401639
theorem B1513039 : Blo 263822 1513039 := bstep (se 1 (by rfl) ⟨1134779, by rfl⟩ : syracuseStep 1513039 = 2269559) B2269559
theorem B595835 : Blo 263822 595835 := bstep (se 1 (by rfl) ⟨446876, by rfl⟩ : syracuseStep 595835 = 893753) B893753
theorem B399227 : Blo 263822 399227 := bstep (se 1 (by rfl) ⟨299420, by rfl⟩ : syracuseStep 399227 = 598841) B598841
theorem B890783 : Blo 263822 890783 := bstep (se 1 (by rfl) ⟨668087, by rfl⟩ : syracuseStep 890783 = 1336175) B1336175
theorem B595871 : Blo 263822 595871 := bstep (se 1 (by rfl) ⟨446903, by rfl⟩ : syracuseStep 595871 = 893807) B893807
theorem B399263 : Blo 263822 399263 := bstep (se 1 (by rfl) ⟨299447, by rfl⟩ : syracuseStep 399263 = 598895) B598895
theorem B596105 : Blo 263822 596105 := bstep (se 2 (by rfl) ⟨223539, by rfl⟩ : syracuseStep 596105 = 447079) B447079
theorem B399497 : Blo 263822 399497 := bstep (se 2 (by rfl) ⟨149811, by rfl⟩ : syracuseStep 399497 = 299623) B299623
theorem B399647 : Blo 263822 399647 := bstep (se 1 (by rfl) ⟨299735, by rfl⟩ : syracuseStep 399647 = 599471) B599471
theorem B956767 : Blo 263822 956767 := bstep (se 1 (by rfl) ⟨717575, by rfl⟩ : syracuseStep 956767 = 1435151) B1435151
theorem B596321 : Blo 263822 596321 := bstep (se 2 (by rfl) ⟨223620, by rfl⟩ : syracuseStep 596321 = 447241) B447241
theorem B596411 : Blo 263822 596411 := bstep (se 1 (by rfl) ⟨447308, by rfl⟩ : syracuseStep 596411 = 894617) B894617
theorem B8657603 : Blo 263822 8657603 := bstep (se 1 (by rfl) ⟨6493202, by rfl⟩ : syracuseStep 8657603 = 12986405) B12986405
theorem B596807 : Blo 263822 596807 := bstep (se 1 (by rfl) ⟨447605, by rfl⟩ : syracuseStep 596807 = 895211) B895211
theorem B400199 : Blo 263822 400199 := bstep (se 1 (by rfl) ⟨300149, by rfl⟩ : syracuseStep 400199 = 600299) B600299
theorem B892025 : Blo 263822 892025 := bstep (se 2 (by rfl) ⟨334509, by rfl⟩ : syracuseStep 892025 = 669019) B669019
theorem B597113 : Blo 263822 597113 := bstep (se 2 (by rfl) ⟨223917, by rfl⟩ : syracuseStep 597113 = 447835) B447835
theorem B2039003 : Blo 263822 2039003 := bstep (se 1 (by rfl) ⟨1529252, by rfl⟩ : syracuseStep 2039003 = 3058505) B3058505
theorem B1351241 : Blo 263822 1351241 := bstep (se 2 (by rfl) ⟨506715, by rfl⟩ : syracuseStep 1351241 = 1013431) B1013431
theorem B597671 : Blo 263822 597671 := bstep (se 1 (by rfl) ⟨448253, by rfl⟩ : syracuseStep 597671 = 896507) B896507
theorem B401063 : Blo 263822 401063 := bstep (se 1 (by rfl) ⟨300797, by rfl⟩ : syracuseStep 401063 = 601595) B601595
theorem B597779 : Blo 263822 597779 := bstep (se 1 (by rfl) ⟨448334, by rfl⟩ : syracuseStep 597779 = 896669) B896669
theorem B401183 : Blo 263822 401183 := bstep (se 1 (by rfl) ⟨300887, by rfl⟩ : syracuseStep 401183 = 601775) B601775
theorem B3219401 : Blo 263822 3219401 := bstep (se 2 (by rfl) ⟨1207275, by rfl⟩ : syracuseStep 3219401 = 2414551) B2414551
theorem B598139 : Blo 263822 598139 := bstep (se 1 (by rfl) ⟨448604, by rfl⟩ : syracuseStep 598139 = 897209) B897209
theorem B2007179 : Blo 263822 2007179 := bstep (se 1 (by rfl) ⟨1505384, by rfl⟩ : syracuseStep 2007179 = 3010769) B3010769
theorem B336079 : Blo 263822 336079 := bstep (se 1 (by rfl) ⟨252059, by rfl⟩ : syracuseStep 336079 = 504119) B504119
theorem B401615 : Blo 263822 401615 := bstep (se 1 (by rfl) ⟨301211, by rfl⟩ : syracuseStep 401615 = 602423) B602423
theorem B401663 : Blo 263822 401663 := bstep (se 1 (by rfl) ⟨301247, by rfl⟩ : syracuseStep 401663 = 602495) B602495
theorem B598409 : Blo 263822 598409 := bstep (se 2 (by rfl) ⟨224403, by rfl⟩ : syracuseStep 598409 = 448807) B448807
theorem B3613177 : Blo 263822 3613177 := bstep (se 2 (by rfl) ⟨1354941, by rfl⟩ : syracuseStep 3613177 = 2709883) B2709883
theorem B566023 : Blo 263822 566023 := bstep (se 1 (by rfl) ⟨424517, by rfl⟩ : syracuseStep 566023 = 849035) B849035
theorem B599543 : Blo 263822 599543 := bstep (se 1 (by rfl) ⟨449657, by rfl⟩ : syracuseStep 599543 = 899315) B899315
theorem B599579 : Blo 263822 599579 := bstep (se 1 (by rfl) ⟨449684, by rfl⟩ : syracuseStep 599579 = 899369) B899369
theorem B501727 : Blo 263822 501727 := bstep (se 1 (by rfl) ⟨376295, by rfl⟩ : syracuseStep 501727 = 752591) B752591
theorem B2566171 : Blo 263822 2566171 := bstep (se 1 (by rfl) ⟨1924628, by rfl⟩ : syracuseStep 2566171 = 3849257) B3849257
theorem B895481 : Blo 263822 895481 := bstep (se 2 (by rfl) ⟨335805, by rfl⟩ : syracuseStep 895481 = 671611) B671611
theorem B600569 : Blo 263822 600569 := bstep (se 2 (by rfl) ⟨225213, by rfl⟩ : syracuseStep 600569 = 450427) B450427
theorem B600623 : Blo 263822 600623 := bstep (se 1 (by rfl) ⟨450467, by rfl⟩ : syracuseStep 600623 = 900935) B900935
theorem B1026643 : Blo 263822 1026643 := bstep (se 1 (by rfl) ⟨769982, by rfl⟩ : syracuseStep 1026643 = 1539965) B1539965
theorem B600659 : Blo 263822 600659 := bstep (se 1 (by rfl) ⟨450494, by rfl⟩ : syracuseStep 600659 = 900989) B900989
theorem B895751 : Blo 263822 895751 := bstep (se 1 (by rfl) ⟨671813, by rfl⟩ : syracuseStep 895751 = 1343627) B1343627
theorem B600839 : Blo 263822 600839 := bstep (se 1 (by rfl) ⟨450629, by rfl⟩ : syracuseStep 600839 = 901259) B901259
theorem B568271 : Blo 263822 568271 := bstep (se 1 (by rfl) ⟨426203, by rfl⟩ : syracuseStep 568271 = 852407) B852407
theorem B895967 : Blo 263822 895967 := bstep (se 1 (by rfl) ⟨671975, by rfl⟩ : syracuseStep 895967 = 1343951) B1343951
theorem B601055 : Blo 263822 601055 := bstep (se 1 (by rfl) ⟨450791, by rfl⟩ : syracuseStep 601055 = 901583) B901583
theorem B896129 : Blo 263822 896129 := bstep (se 2 (by rfl) ⟨336048, by rfl⟩ : syracuseStep 896129 = 672097) B672097
theorem B601271 : Blo 263822 601271 := bstep (se 1 (by rfl) ⟨450953, by rfl⟩ : syracuseStep 601271 = 901907) B901907
theorem B20589997 : Blo 263822 20589997 := bstep (se 3 (by rfl) ⟨3860624, by rfl⟩ : syracuseStep 20589997 = 7721249) B7721249
theorem B569065 : Blo 263822 569065 := bstep (se 2 (by rfl) ⟨213399, by rfl⟩ : syracuseStep 569065 = 426799) B426799
theorem B601847 : Blo 263822 601847 := bstep (se 1 (by rfl) ⟨451385, by rfl⟩ : syracuseStep 601847 = 902771) B902771
theorem B896831 : Blo 263822 896831 := bstep (se 1 (by rfl) ⟨672623, by rfl⟩ : syracuseStep 896831 = 1345247) B1345247
theorem B601919 : Blo 263822 601919 := bstep (se 1 (by rfl) ⟨451439, by rfl⟩ : syracuseStep 601919 = 902879) B902879
theorem B896939 : Blo 263822 896939 := bstep (se 1 (by rfl) ⟨672704, by rfl⟩ : syracuseStep 896939 = 1345409) B1345409
theorem B602027 : Blo 263822 602027 := bstep (se 1 (by rfl) ⟨451520, by rfl⟩ : syracuseStep 602027 = 903041) B903041
theorem B5779421 : Blo 263822 5779421 := bstep (se 3 (by rfl) ⟨1083641, by rfl⟩ : syracuseStep 5779421 = 2167283) B2167283
theorem B503891 : Blo 263822 503891 := bstep (se 1 (by rfl) ⟨377918, by rfl⟩ : syracuseStep 503891 = 755837) B755837
theorem B602387 : Blo 263822 602387 := bstep (se 1 (by rfl) ⟨451790, by rfl⟩ : syracuseStep 602387 = 903581) B903581
theorem B897479 : Blo 263822 897479 := bstep (se 1 (by rfl) ⟨673109, by rfl⟩ : syracuseStep 897479 = 1346219) B1346219
theorem B602567 : Blo 263822 602567 := bstep (se 1 (by rfl) ⟨451925, by rfl⟩ : syracuseStep 602567 = 903851) B903851
theorem B2568941 : Blo 263822 2568941 := bstep (se 3 (by rfl) ⟨481676, by rfl⟩ : syracuseStep 2568941 = 963353) B963353
theorem B1127297 : Blo 263822 1127297 := bstep (se 2 (by rfl) ⟨422736, by rfl⟩ : syracuseStep 1127297 = 845473) B845473
theorem B406409 : Blo 263822 406409 := bstep (se 2 (by rfl) ⟨152403, by rfl⟩ : syracuseStep 406409 = 304807) B304807
theorem B504787 : Blo 263822 504787 := bstep (se 1 (by rfl) ⟨378590, by rfl⟩ : syracuseStep 504787 = 757181) B757181
theorem B6534449 : Blo 263822 6534449 := bstep (se 2 (by rfl) ⟨2450418, by rfl⟩ : syracuseStep 6534449 = 4900837) B4900837
theorem B1095277 : Blo 263822 1095277 := bstep (se 3 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 1095277 = 410729) B410729
theorem B898721 : Blo 263822 898721 := bstep (se 2 (by rfl) ⟨337020, by rfl⟩ : syracuseStep 898721 = 674041) B674041
theorem B505577 : Blo 263822 505577 := bstep (se 2 (by rfl) ⟨189591, by rfl⟩ : syracuseStep 505577 = 379183) B379183
theorem B571627 : Blo 263822 571627 := bstep (se 1 (by rfl) ⟨428720, by rfl⟩ : syracuseStep 571627 = 857441) B857441
theorem B669991 : Blo 263822 669991 := bstep (se 1 (by rfl) ⟨502493, by rfl⟩ : syracuseStep 669991 = 1004987) B1004987
theorem B2275847 : Blo 263822 2275847 := bstep (se 1 (by rfl) ⟨1706885, by rfl⟩ : syracuseStep 2275847 = 3413771) B3413771
theorem B900071 : Blo 263822 900071 := bstep (se 1 (by rfl) ⟨675053, by rfl⟩ : syracuseStep 900071 = 1350107) B1350107
theorem B1522745 : Blo 263822 1522745 := bstep (se 2 (by rfl) ⟨571029, by rfl⟩ : syracuseStep 1522745 = 1142059) B1142059
theorem B2571365 : Blo 263822 2571365 := bstep (se 4 (by rfl) ⟨241065, by rfl⟩ : syracuseStep 2571365 = 482131) B482131
theorem B4602997 : Blo 263822 4602997 := bstep (se 5 (by rfl) ⟨215765, by rfl⟩ : syracuseStep 4602997 = 431531) B431531
theorem B1457297 : Blo 263822 1457297 := bstep (se 2 (by rfl) ⟨546486, by rfl⟩ : syracuseStep 1457297 = 1092973) B1092973
theorem B376039 : Blo 263822 376039 := bstep (se 1 (by rfl) ⟨282029, by rfl⟩ : syracuseStep 376039 = 564059) B564059
theorem B1621235 : Blo 263822 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B671935 : Blo 263822 671935 := bstep (se 1 (by rfl) ⟨503951, by rfl⟩ : syracuseStep 671935 = 1007903) B1007903
theorem B1622207 : Blo 263822 1622207 := bstep (se 1 (by rfl) ⟨1216655, by rfl⟩ : syracuseStep 1622207 = 2433311) B2433311
theorem B475753 : Blo 263822 475753 := bstep (se 2 (by rfl) ⟨178407, by rfl⟩ : syracuseStep 475753 = 356815) B356815
theorem B902177 : Blo 263822 902177 := bstep (se 2 (by rfl) ⟨338316, by rfl⟩ : syracuseStep 902177 = 676633) B676633
theorem B1525229 : Blo 263822 1525229 := bstep (se 3 (by rfl) ⟨285980, by rfl⟩ : syracuseStep 1525229 = 571961) B571961
theorem B673343 : Blo 263822 673343 := bstep (se 1 (by rfl) ⟨505007, by rfl⟩ : syracuseStep 673343 = 1010015) B1010015
theorem B1132319 : Blo 263822 1132319 := bstep (se 1 (by rfl) ⟨849239, by rfl⟩ : syracuseStep 1132319 = 1698479) B1698479
theorem B673991 : Blo 263822 673991 := bstep (se 1 (by rfl) ⟨505493, by rfl⟩ : syracuseStep 673991 = 1010987) B1010987
theorem B477467 : Blo 263822 477467 := bstep (se 1 (by rfl) ⟨358100, by rfl⟩ : syracuseStep 477467 = 716201) B716201
theorem B2279947 : Blo 263822 2279947 := bstep (se 1 (by rfl) ⟨1709960, by rfl⟩ : syracuseStep 2279947 = 3419921) B3419921
theorem B445223 : Blo 263822 445223 := bstep (se 1 (by rfl) ⟨333917, by rfl⟩ : syracuseStep 445223 = 667835) B667835
theorem B674689 : Blo 263822 674689 := bstep (se 2 (by rfl) ⟨253008, by rfl⟩ : syracuseStep 674689 = 506017) B506017
theorem B445547 : Blo 263822 445547 := bstep (se 1 (by rfl) ⟨334160, by rfl⟩ : syracuseStep 445547 = 668321) B668321
theorem B445817 : Blo 263822 445817 := bstep (se 2 (by rfl) ⟨167181, by rfl⟩ : syracuseStep 445817 = 334363) B334363
theorem B2280905 : Blo 263822 2280905 := bstep (se 2 (by rfl) ⟨855339, by rfl⟩ : syracuseStep 2280905 = 1710679) B1710679
theorem B609761 : Blo 263822 609761 := bstep (se 2 (by rfl) ⟨228660, by rfl⟩ : syracuseStep 609761 = 457321) B457321
theorem B675499 : Blo 263822 675499 := bstep (se 1 (by rfl) ⟨506624, by rfl⟩ : syracuseStep 675499 = 1013249) B1013249
theorem B282619 : Blo 263822 282619 := bstep (se 1 (by rfl) ⟨211964, by rfl⟩ : syracuseStep 282619 = 423929) B423929
theorem B446519 : Blo 263822 446519 := bstep (se 1 (by rfl) ⟨334889, by rfl⟩ : syracuseStep 446519 = 669779) B669779
theorem B675935 : Blo 263822 675935 := bstep (se 1 (by rfl) ⟨506951, by rfl⟩ : syracuseStep 675935 = 1013903) B1013903
theorem B446843 : Blo 263822 446843 := bstep (se 1 (by rfl) ⟨335132, by rfl⟩ : syracuseStep 446843 = 670265) B670265
theorem B1134985 : Blo 263822 1134985 := bstep (se 2 (by rfl) ⟨425619, by rfl⟩ : syracuseStep 1134985 = 851239) B851239
theorem B447113 : Blo 263822 447113 := bstep (se 2 (by rfl) ⟨167667, by rfl⟩ : syracuseStep 447113 = 335335) B335335
theorem B1430891 : Blo 263822 1430891 := bstep (se 1 (by rfl) ⟨1073168, by rfl⟩ : syracuseStep 1430891 = 2146337) B2146337
theorem B53106353 : Blo 263822 53106353 := bstep (se 2 (by rfl) ⟨19914882, by rfl⟩ : syracuseStep 53106353 = 39829765) B39829765
theorem B481115 : Blo 263822 481115 := bstep (se 1 (by rfl) ⟨360836, by rfl⟩ : syracuseStep 481115 = 721673) B721673
theorem B2284321 : Blo 263822 2284321 := bstep (se 2 (by rfl) ⟨856620, by rfl⟩ : syracuseStep 2284321 = 1713241) B1713241
theorem B1006415 : Blo 263822 1006415 := bstep (se 1 (by rfl) ⟨754811, by rfl⟩ : syracuseStep 1006415 = 1509623) B1509623
theorem B4120001 : Blo 263822 4120001 := bstep (se 2 (by rfl) ⟨1545000, by rfl⟩ : syracuseStep 4120001 = 3090001) B3090001
theorem B3825731 : Blo 263822 3825731 := bstep (se 1 (by rfl) ⟨2869298, by rfl⟩ : syracuseStep 3825731 = 5738597) B5738597
theorem B1335689 : Blo 263822 1335689 := bstep (se 2 (by rfl) ⟨500883, by rfl⟩ : syracuseStep 1335689 = 1001767) B1001767
theorem B451291 : Blo 263822 451291 := bstep (se 1 (by rfl) ⟨338468, by rfl⟩ : syracuseStep 451291 = 676937) B676937
theorem B2024189 : Blo 263822 2024189 := bstep (se 3 (by rfl) ⟨379535, by rfl⟩ : syracuseStep 2024189 = 759071) B759071
theorem B1205561 : Blo 263822 1205561 := bstep (se 2 (by rfl) ⟨452085, by rfl⟩ : syracuseStep 1205561 = 904171) B904171
theorem B3007853 : Blo 263822 3007853 := bstep (se 3 (by rfl) ⟨563972, by rfl⟩ : syracuseStep 3007853 = 1127945) B1127945
theorem B48850289 : Blo 263822 48850289 := bstep (se 2 (by rfl) ⟨18318858, by rfl⟩ : syracuseStep 48850289 = 36637717) B36637717
theorem B2713171 : Blo 263822 2713171 := bstep (se 1 (by rfl) ⟨2034878, by rfl⟩ : syracuseStep 2713171 = 4069757) B4069757
theorem B1336985 : Blo 263822 1336985 := bstep (se 2 (by rfl) ⟨501369, by rfl⟩ : syracuseStep 1336985 = 1002739) B1002739
theorem B2746075 : Blo 263822 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B2877605 : Blo 263822 2877605 := bstep (se 4 (by rfl) ⟨269775, by rfl⟩ : syracuseStep 2877605 = 539551) B539551
theorem B4548959 : Blo 263822 4548959 := bstep (se 1 (by rfl) ⟨3411719, by rfl⟩ : syracuseStep 4548959 = 6823439) B6823439
theorem B1010029 : Blo 263822 1010029 := bstep (se 3 (by rfl) ⟨189380, by rfl⟩ : syracuseStep 1010029 = 378761) B378761
theorem B2550179 : Blo 263822 2550179 := bstep (se 1 (by rfl) ⟨1912634, by rfl⟩ : syracuseStep 2550179 = 3825269) B3825269
theorem B1698889 : Blo 263822 1698889 := bstep (se 2 (by rfl) ⟨637083, by rfl⟩ : syracuseStep 1698889 = 1274167) B1274167
theorem B12415169 : Blo 263822 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B1143017 : Blo 263822 1143017 := bstep (se 2 (by rfl) ⟨428631, by rfl⟩ : syracuseStep 1143017 = 857263) B857263
theorem B1143391 : Blo 263822 1143391 := bstep (se 1 (by rfl) ⟨857543, by rfl⟩ : syracuseStep 1143391 = 1715087) B1715087
theorem B1012459 : Blo 263822 1012459 := bstep (se 1 (by rfl) ⟨759344, by rfl⟩ : syracuseStep 1012459 = 1518689) B1518689
theorem B6452027 : Blo 263822 6452027 := bstep (se 1 (by rfl) ⟨4839020, by rfl⟩ : syracuseStep 6452027 = 9678041) B9678041
theorem B1012945 : Blo 263822 1012945 := bstep (se 2 (by rfl) ⟨379854, by rfl⟩ : syracuseStep 1012945 = 759709) B759709
theorem B1275227 : Blo 263822 1275227 := bstep (se 1 (by rfl) ⟨956420, by rfl⟩ : syracuseStep 1275227 = 1912841) B1912841
theorem B423851 : Blo 263822 423851 := bstep (se 1 (by rfl) ⟨317888, by rfl⟩ : syracuseStep 423851 = 635777) B635777
theorem B1014191 : Blo 263822 1014191 := bstep (se 1 (by rfl) ⟨760643, by rfl⟩ : syracuseStep 1014191 = 1521287) B1521287
theorem B5110199 : Blo 263822 5110199 := bstep (se 1 (by rfl) ⟨3832649, by rfl⟩ : syracuseStep 5110199 = 7665299) B7665299
theorem B2718305 : Blo 263822 2718305 := bstep (se 2 (by rfl) ⟨1019364, by rfl⟩ : syracuseStep 2718305 = 2038729) B2038729
theorem B1211219 : Blo 263822 1211219 := bstep (se 1 (by rfl) ⟨908414, by rfl⟩ : syracuseStep 1211219 = 1816829) B1816829
theorem B916703 : Blo 263822 916703 := bstep (se 1 (by rfl) ⟨687527, by rfl⟩ : syracuseStep 916703 = 1375055) B1375055
theorem B752921 : Blo 263822 752921 := bstep (se 2 (by rfl) ⟨282345, by rfl⟩ : syracuseStep 752921 = 564691) B564691
theorem B1015375 : Blo 263822 1015375 := bstep (se 1 (by rfl) ⟨761531, by rfl⟩ : syracuseStep 1015375 = 1523063) B1523063
theorem B753263 : Blo 263822 753263 := bstep (se 1 (by rfl) ⟨564947, by rfl⟩ : syracuseStep 753263 = 1129895) B1129895
theorem B9273041 : Blo 263822 9273041 := bstep (se 2 (by rfl) ⟨3477390, by rfl⟩ : syracuseStep 9273041 = 6954781) B6954781
theorem B851791 : Blo 263822 851791 := bstep (se 1 (by rfl) ⟨638843, by rfl⟩ : syracuseStep 851791 = 1277687) B1277687
theorem B2883833 : Blo 263822 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B4325885 : Blo 263822 4325885 := bstep (se 3 (by rfl) ⟨811103, by rfl⟩ : syracuseStep 4325885 = 1622207) B1622207
theorem B4817569 : Blo 263822 4817569 := bstep (se 2 (by rfl) ⟨1806588, by rfl⟩ : syracuseStep 4817569 = 3613177) B3613177
theorem B1016819 : Blo 263822 1016819 := bstep (se 1 (by rfl) ⟨762614, by rfl⟩ : syracuseStep 1016819 = 1525229) B1525229
theorem B754697 : Blo 263822 754697 := bstep (se 2 (by rfl) ⟨283011, by rfl⟩ : syracuseStep 754697 = 566023) B566023
theorem B3048677 : Blo 263822 3048677 := bstep (se 4 (by rfl) ⟨285813, by rfl⟩ : syracuseStep 3048677 = 571627) B571627
theorem B722255 : Blo 263822 722255 := bstep (se 1 (by rfl) ⟨541691, by rfl⟩ : syracuseStep 722255 = 1083383) B1083383
theorem B1902143 : Blo 263822 1902143 := bstep (se 1 (by rfl) ⟨1426607, by rfl⟩ : syracuseStep 1902143 = 2853215) B2853215
theorem B263919 : Blo 263822 263919 := bstep (se 1 (by rfl) ⟨197939, by rfl⟩ : syracuseStep 263919 = 395879) B395879
theorem B296815 : Blo 263822 296815 := bstep (se 1 (by rfl) ⟨222611, by rfl⟩ : syracuseStep 296815 = 445223) B445223
theorem B264047 : Blo 263822 264047 := bstep (se 1 (by rfl) ⟨198035, by rfl⟩ : syracuseStep 264047 = 396071) B396071
theorem B3409775 : Blo 263822 3409775 := bstep (se 1 (by rfl) ⟨2557331, by rfl⟩ : syracuseStep 3409775 = 5114663) B5114663
theorem B297031 : Blo 263822 297031 := bstep (se 1 (by rfl) ⟨222773, by rfl⟩ : syracuseStep 297031 = 445547) B445547
theorem B264263 : Blo 263822 264263 := bstep (se 1 (by rfl) ⟨198197, by rfl⟩ : syracuseStep 264263 = 396395) B396395
theorem B264423 : Blo 263822 264423 := bstep (se 1 (by rfl) ⟨198317, by rfl⟩ : syracuseStep 264423 = 396635) B396635
theorem B297211 : Blo 263822 297211 := bstep (se 1 (by rfl) ⟨222908, by rfl⟩ : syracuseStep 297211 = 445817) B445817
theorem B264443 : Blo 263822 264443 := bstep (se 1 (by rfl) ⟨198332, by rfl⟩ : syracuseStep 264443 = 396665) B396665
theorem B264447 : Blo 263822 264447 := bstep (se 1 (by rfl) ⟨198335, by rfl⟩ : syracuseStep 264447 = 396671) B396671
theorem B264863 : Blo 263822 264863 := bstep (se 1 (by rfl) ⟨198647, by rfl⟩ : syracuseStep 264863 = 397295) B397295
theorem B264871 : Blo 263822 264871 := bstep (se 1 (by rfl) ⟨198653, by rfl⟩ : syracuseStep 264871 = 397307) B397307
theorem B297679 : Blo 263822 297679 := bstep (se 1 (by rfl) ⟨223259, by rfl⟩ : syracuseStep 297679 = 446519) B446519
theorem B264911 : Blo 263822 264911 := bstep (se 1 (by rfl) ⟨198683, by rfl⟩ : syracuseStep 264911 = 397367) B397367
theorem B264943 : Blo 263822 264943 := bstep (se 1 (by rfl) ⟨198707, by rfl⟩ : syracuseStep 264943 = 397415) B397415
theorem B264991 : Blo 263822 264991 := bstep (se 1 (by rfl) ⟨198743, by rfl⟩ : syracuseStep 264991 = 397487) B397487
theorem B297895 : Blo 263822 297895 := bstep (se 1 (by rfl) ⟨223421, by rfl⟩ : syracuseStep 297895 = 446843) B446843
theorem B265127 : Blo 263822 265127 := bstep (se 1 (by rfl) ⟨198845, by rfl⟩ : syracuseStep 265127 = 397691) B397691
theorem B1706939 : Blo 263822 1706939 := bstep (se 1 (by rfl) ⟨1280204, by rfl⟩ : syracuseStep 1706939 = 2560409) B2560409
theorem B298075 : Blo 263822 298075 := bstep (se 1 (by rfl) ⟨223556, by rfl⟩ : syracuseStep 298075 = 447113) B447113
theorem B265307 : Blo 263822 265307 := bstep (se 1 (by rfl) ⟨198980, by rfl⟩ : syracuseStep 265307 = 397961) B397961
theorem B1346705 : Blo 263822 1346705 := bstep (se 2 (by rfl) ⟨505014, by rfl⟩ : syracuseStep 1346705 = 1010029) B1010029
theorem B265447 : Blo 263822 265447 := bstep (se 1 (by rfl) ⟨199085, by rfl⟩ : syracuseStep 265447 = 398171) B398171
theorem B1707479 : Blo 263822 1707479 := bstep (se 1 (by rfl) ⟨1280609, by rfl⟩ : syracuseStep 1707479 = 2561219) B2561219
theorem B396767 : Blo 263822 396767 := bstep (se 1 (by rfl) ⟨297575, by rfl⟩ : syracuseStep 396767 = 595151) B595151
theorem B3214829 : Blo 263822 3214829 := bstep (se 3 (by rfl) ⟨602780, by rfl⟩ : syracuseStep 3214829 = 1205561) B1205561
theorem B396827 : Blo 263822 396827 := bstep (se 1 (by rfl) ⟨297620, by rfl⟩ : syracuseStep 396827 = 595241) B595241
theorem B265755 : Blo 263822 265755 := bstep (se 1 (by rfl) ⟨199316, by rfl⟩ : syracuseStep 265755 = 398633) B398633
theorem B953927 : Blo 263822 953927 := bstep (se 1 (by rfl) ⟨715445, by rfl⟩ : syracuseStep 953927 = 1430891) B1430891
theorem B396959 : Blo 263822 396959 := bstep (se 1 (by rfl) ⟨297719, by rfl⟩ : syracuseStep 396959 = 595439) B595439
theorem B265887 : Blo 263822 265887 := bstep (se 1 (by rfl) ⟨199415, by rfl⟩ : syracuseStep 265887 = 398831) B398831
theorem B397223 : Blo 263822 397223 := bstep (se 1 (by rfl) ⟨297917, by rfl⟩ : syracuseStep 397223 = 595835) B595835
theorem B266151 : Blo 263822 266151 := bstep (se 1 (by rfl) ⟨199613, by rfl⟩ : syracuseStep 266151 = 399227) B399227
theorem B593855 : Blo 263822 593855 := bstep (se 1 (by rfl) ⟨445391, by rfl⟩ : syracuseStep 593855 = 890783) B890783
theorem B397247 : Blo 263822 397247 := bstep (se 1 (by rfl) ⟨297935, by rfl⟩ : syracuseStep 397247 = 595871) B595871
theorem B266175 : Blo 263822 266175 := bstep (se 1 (by rfl) ⟨199631, by rfl⟩ : syracuseStep 266175 = 399263) B399263
theorem B397403 : Blo 263822 397403 := bstep (se 1 (by rfl) ⟨298052, by rfl⟩ : syracuseStep 397403 = 596105) B596105
theorem B266331 : Blo 263822 266331 := bstep (se 1 (by rfl) ⟨199748, by rfl⟩ : syracuseStep 266331 = 399497) B399497
theorem B2265185 : Blo 263822 2265185 := bstep (se 2 (by rfl) ⟨849444, by rfl⟩ : syracuseStep 2265185 = 1698889) B1698889
theorem B266431 : Blo 263822 266431 := bstep (se 1 (by rfl) ⟨199823, by rfl⟩ : syracuseStep 266431 = 399647) B399647
theorem B397547 : Blo 263822 397547 := bstep (se 1 (by rfl) ⟨298160, by rfl⟩ : syracuseStep 397547 = 596321) B596321
theorem B397607 : Blo 263822 397607 := bstep (se 1 (by rfl) ⟨298205, by rfl⟩ : syracuseStep 397607 = 596411) B596411
theorem B5771735 : Blo 263822 5771735 := bstep (se 1 (by rfl) ⟨4328801, by rfl⟩ : syracuseStep 5771735 = 8657603) B8657603
theorem B397871 : Blo 263822 397871 := bstep (se 1 (by rfl) ⟨298403, by rfl⟩ : syracuseStep 397871 = 596807) B596807
theorem B266799 : Blo 263822 266799 := bstep (se 1 (by rfl) ⟨200099, by rfl⟩ : syracuseStep 266799 = 400199) B400199
theorem B594683 : Blo 263822 594683 := bstep (se 1 (by rfl) ⟨446012, by rfl⟩ : syracuseStep 594683 = 892025) B892025
theorem B398075 : Blo 263822 398075 := bstep (se 1 (by rfl) ⟨298556, by rfl⟩ : syracuseStep 398075 = 597113) B597113
theorem B3019517 : Blo 263822 3019517 := bstep (se 3 (by rfl) ⟨566159, by rfl⟩ : syracuseStep 3019517 = 1132319) B1132319
theorem B758753 : Blo 263822 758753 := bstep (se 2 (by rfl) ⟨284532, by rfl⟩ : syracuseStep 758753 = 569065) B569065
theorem B398447 : Blo 263822 398447 := bstep (se 1 (by rfl) ⟨298835, by rfl⟩ : syracuseStep 398447 = 597671) B597671
theorem B267375 : Blo 263822 267375 := bstep (se 1 (by rfl) ⟨200531, by rfl⟩ : syracuseStep 267375 = 401063) B401063
theorem B398519 : Blo 263822 398519 := bstep (se 1 (by rfl) ⟨298889, by rfl⟩ : syracuseStep 398519 = 597779) B597779
theorem B267455 : Blo 263822 267455 := bstep (se 1 (by rfl) ⟨200591, by rfl⟩ : syracuseStep 267455 = 401183) B401183
theorem B398759 : Blo 263822 398759 := bstep (se 1 (by rfl) ⟨299069, by rfl⟩ : syracuseStep 398759 = 598139) B598139
theorem B267743 : Blo 263822 267743 := bstep (se 1 (by rfl) ⟨200807, by rfl⟩ : syracuseStep 267743 = 401615) B401615
theorem B267775 : Blo 263822 267775 := bstep (se 1 (by rfl) ⟨200831, by rfl⟩ : syracuseStep 267775 = 401663) B401663
theorem B890459 : Blo 263822 890459 := bstep (se 1 (by rfl) ⟨667844, by rfl⟩ : syracuseStep 890459 = 1335689) B1335689
theorem B398939 : Blo 263822 398939 := bstep (se 1 (by rfl) ⟨299204, by rfl⟩ : syracuseStep 398939 = 598409) B598409
theorem B1349459 : Blo 263822 1349459 := bstep (se 1 (by rfl) ⟨1012094, by rfl⟩ : syracuseStep 1349459 = 2024189) B2024189
theorem B1513313 : Blo 263822 1513313 := bstep (se 2 (by rfl) ⟨567492, by rfl⟩ : syracuseStep 1513313 = 1134985) B1134985
theorem B24549317 : Blo 263822 24549317 := bstep (se 4 (by rfl) ⟨2301498, by rfl⟩ : syracuseStep 24549317 = 4602997) B4602997
theorem B2005235 : Blo 263822 2005235 := bstep (se 1 (by rfl) ⟨1503926, by rfl⟩ : syracuseStep 2005235 = 3007853) B3007853
theorem B1349945 : Blo 263822 1349945 := bstep (se 2 (by rfl) ⟨506229, by rfl⟩ : syracuseStep 1349945 = 1012459) B1012459
theorem B399695 : Blo 263822 399695 := bstep (se 1 (by rfl) ⟨299771, by rfl⟩ : syracuseStep 399695 = 599543) B599543
theorem B399719 : Blo 263822 399719 := bstep (se 1 (by rfl) ⟨299789, by rfl⟩ : syracuseStep 399719 = 599579) B599579
theorem B399785 : Blo 263822 399785 := bstep (se 2 (by rfl) ⟨149919, by rfl⟩ : syracuseStep 399785 = 299839) B299839
theorem B891323 : Blo 263822 891323 := bstep (se 1 (by rfl) ⟨668492, by rfl⟩ : syracuseStep 891323 = 1336985) B1336985
theorem B400169 : Blo 263822 400169 := bstep (se 2 (by rfl) ⟨150063, by rfl⟩ : syracuseStep 400169 = 300127) B300127
theorem B1350593 : Blo 263822 1350593 := bstep (se 2 (by rfl) ⟨506472, by rfl⟩ : syracuseStep 1350593 = 1012945) B1012945
theorem B596987 : Blo 263822 596987 := bstep (se 1 (by rfl) ⟨447740, by rfl⟩ : syracuseStep 596987 = 895481) B895481
theorem B400379 : Blo 263822 400379 := bstep (se 1 (by rfl) ⟨300284, by rfl⟩ : syracuseStep 400379 = 600569) B600569
theorem B400415 : Blo 263822 400415 := bstep (se 1 (by rfl) ⟨300311, by rfl⟩ : syracuseStep 400415 = 600623) B600623
theorem B400439 : Blo 263822 400439 := bstep (se 1 (by rfl) ⟨300329, by rfl⟩ : syracuseStep 400439 = 600659) B600659
theorem B597167 : Blo 263822 597167 := bstep (se 1 (by rfl) ⟨447875, by rfl⟩ : syracuseStep 597167 = 895751) B895751
theorem B400559 : Blo 263822 400559 := bstep (se 1 (by rfl) ⟨300419, by rfl⟩ : syracuseStep 400559 = 600839) B600839
theorem B597311 : Blo 263822 597311 := bstep (se 1 (by rfl) ⟨447983, by rfl⟩ : syracuseStep 597311 = 895967) B895967
theorem B400703 : Blo 263822 400703 := bstep (se 1 (by rfl) ⟨300527, by rfl⟩ : syracuseStep 400703 = 601055) B601055
theorem B597419 : Blo 263822 597419 := bstep (se 1 (by rfl) ⟨448064, by rfl⟩ : syracuseStep 597419 = 896129) B896129
theorem B400847 : Blo 263822 400847 := bstep (se 1 (by rfl) ⟨300635, by rfl⟩ : syracuseStep 400847 = 601271) B601271
theorem B401231 : Blo 263822 401231 := bstep (se 1 (by rfl) ⟨300923, by rfl⟩ : syracuseStep 401231 = 601847) B601847
theorem B597887 : Blo 263822 597887 := bstep (se 1 (by rfl) ⟨448415, by rfl⟩ : syracuseStep 597887 = 896831) B896831
theorem B401279 : Blo 263822 401279 := bstep (se 1 (by rfl) ⟨300959, by rfl⟩ : syracuseStep 401279 = 601919) B601919
theorem B597959 : Blo 263822 597959 := bstep (se 1 (by rfl) ⟨448469, by rfl⟩ : syracuseStep 597959 = 896939) B896939
theorem B401351 : Blo 263822 401351 := bstep (se 1 (by rfl) ⟨301013, by rfl⟩ : syracuseStep 401351 = 602027) B602027
theorem B335927 : Blo 263822 335927 := bstep (se 1 (by rfl) ⟨251945, by rfl⟩ : syracuseStep 335927 = 503891) B503891
theorem B762011 : Blo 263822 762011 := bstep (se 1 (by rfl) ⟨571508, by rfl⟩ : syracuseStep 762011 = 1143017) B1143017
theorem B401591 : Blo 263822 401591 := bstep (se 1 (by rfl) ⟨301193, by rfl⟩ : syracuseStep 401591 = 602387) B602387
theorem B598319 : Blo 263822 598319 := bstep (se 1 (by rfl) ⟨448739, by rfl⟩ : syracuseStep 598319 = 897479) B897479
theorem B401711 : Blo 263822 401711 := bstep (se 1 (by rfl) ⟨301283, by rfl⟩ : syracuseStep 401711 = 602567) B602567
theorem B893321 : Blo 263822 893321 := bstep (se 2 (by rfl) ⟨334995, by rfl⟩ : syracuseStep 893321 = 669991) B669991
theorem B1712627 : Blo 263822 1712627 := bstep (se 1 (by rfl) ⟨1284470, by rfl⟩ : syracuseStep 1712627 = 2568941) B2568941
theorem B4301351 : Blo 263822 4301351 := bstep (se 1 (by rfl) ⟨3226013, by rfl⟩ : syracuseStep 4301351 = 6452027) B6452027
theorem B599147 : Blo 263822 599147 := bstep (se 1 (by rfl) ⟨449360, by rfl⟩ : syracuseStep 599147 = 898721) B898721
theorem B337051 : Blo 263822 337051 := bstep (se 1 (by rfl) ⟨252788, by rfl⟩ : syracuseStep 337051 = 505577) B505577
theorem B4335029 : Blo 263822 4335029 := bstep (se 5 (by rfl) ⟨203204, by rfl⟩ : syracuseStep 4335029 = 406409) B406409
theorem B501385 : Blo 263822 501385 := bstep (se 2 (by rfl) ⟨188019, by rfl⟩ : syracuseStep 501385 = 376039) B376039
theorem B1517231 : Blo 263822 1517231 := bstep (se 1 (by rfl) ⟨1137923, by rfl⟩ : syracuseStep 1517231 = 2275847) B2275847
theorem B1812203 : Blo 263822 1812203 := bstep (se 1 (by rfl) ⟨1359152, by rfl⟩ : syracuseStep 1812203 = 2718305) B2718305
theorem B600047 : Blo 263822 600047 := bstep (se 1 (by rfl) ⟨450035, by rfl⟩ : syracuseStep 600047 = 900071) B900071
theorem B1714243 : Blo 263822 1714243 := bstep (se 1 (by rfl) ⟨1285682, by rfl⟩ : syracuseStep 1714243 = 2571365) B2571365
theorem B1353833 : Blo 263822 1353833 := bstep (se 2 (by rfl) ⟨507687, by rfl⟩ : syracuseStep 1353833 = 1015375) B1015375
theorem B501947 : Blo 263822 501947 := bstep (se 1 (by rfl) ⟨376460, by rfl⟩ : syracuseStep 501947 = 752921) B752921
theorem B502175 : Blo 263822 502175 := bstep (se 1 (by rfl) ⟨376631, by rfl⟩ : syracuseStep 502175 = 753263) B753263
theorem B895913 : Blo 263822 895913 := bstep (se 2 (by rfl) ⟨335967, by rfl⟩ : syracuseStep 895913 = 671935) B671935
theorem B601451 : Blo 263822 601451 := bstep (se 1 (by rfl) ⟨451088, by rfl⟩ : syracuseStep 601451 = 902177) B902177
theorem B634337 : Blo 263822 634337 := bstep (se 2 (by rfl) ⟨237876, by rfl⟩ : syracuseStep 634337 = 475753) B475753
theorem B601721 : Blo 263822 601721 := bstep (se 2 (by rfl) ⟨225645, by rfl⟩ : syracuseStep 601721 = 451291) B451291
theorem B1617583 : Blo 263822 1617583 := bstep (se 1 (by rfl) ⟨1213187, by rfl⟩ : syracuseStep 1617583 = 2426375) B2426375
theorem B11448125 : Blo 263822 11448125 := bstep (se 3 (by rfl) ⟨2146523, by rfl⟩ : syracuseStep 11448125 = 4293047) B4293047
theorem B7712819 : Blo 263822 7712819 := bstep (se 1 (by rfl) ⟨5784614, by rfl⟩ : syracuseStep 7712819 = 11569229) B11569229
theorem B569911 : Blo 263822 569911 := bstep (se 1 (by rfl) ⟨427433, by rfl⟩ : syracuseStep 569911 = 854867) B854867
theorem B3617561 : Blo 263822 3617561 := bstep (se 2 (by rfl) ⟨1356585, by rfl⟩ : syracuseStep 3617561 = 2713171) B2713171
theorem B1520603 : Blo 263822 1520603 := bstep (se 1 (by rfl) ⟨1140452, by rfl⟩ : syracuseStep 1520603 = 2280905) B2280905
theorem B406507 : Blo 263822 406507 := bstep (se 1 (by rfl) ⟨304880, by rfl⟩ : syracuseStep 406507 = 609761) B609761
theorem B668969 : Blo 263822 668969 := bstep (se 2 (by rfl) ⟨250863, by rfl⟩ : syracuseStep 668969 = 501727) B501727
theorem B3421561 : Blo 263822 3421561 := bstep (se 2 (by rfl) ⟨1283085, by rfl⟩ : syracuseStep 3421561 = 2566171) B2566171
theorem B35404235 : Blo 263822 35404235 := bstep (se 1 (by rfl) ⟨26553176, by rfl⟩ : syracuseStep 35404235 = 53106353) B53106353
theorem B899585 : Blo 263822 899585 := bstep (se 2 (by rfl) ⟨337344, by rfl⟩ : syracuseStep 899585 = 674689) B674689
theorem B670943 : Blo 263822 670943 := bstep (se 1 (by rfl) ⟨503207, by rfl⟩ : syracuseStep 670943 = 1006415) B1006415
theorem B1359335 : Blo 263822 1359335 := bstep (se 1 (by rfl) ⟨1019501, by rfl⟩ : syracuseStep 1359335 = 2039003) B2039003
theorem B900665 : Blo 263822 900665 := bstep (se 2 (by rfl) ⟨337749, by rfl⟩ : syracuseStep 900665 = 675499) B675499
theorem B900827 : Blo 263822 900827 := bstep (se 1 (by rfl) ⟨675620, by rfl⟩ : syracuseStep 900827 = 1351241) B1351241
theorem B1130269 : Blo 263822 1130269 := bstep (se 3 (by rfl) ⟨211925, by rfl⟩ : syracuseStep 1130269 = 423851) B423851
theorem B2146267 : Blo 263822 2146267 := bstep (se 1 (by rfl) ⟨1609700, by rfl⟩ : syracuseStep 2146267 = 3219401) B3219401
theorem B376825 : Blo 263822 376825 := bstep (se 2 (by rfl) ⟨141309, by rfl⟩ : syracuseStep 376825 = 282619) B282619
theorem B1524521 : Blo 263822 1524521 := bstep (se 2 (by rfl) ⟨571695, by rfl⟩ : syracuseStep 1524521 = 1143391) B1143391
theorem B5424205 : Blo 263822 5424205 := bstep (se 3 (by rfl) ⟨1017038, by rfl⟩ : syracuseStep 5424205 = 2034077) B2034077
theorem B673049 : Blo 263822 673049 := bstep (se 2 (by rfl) ⟨252393, by rfl⟩ : syracuseStep 673049 = 504787) B504787
theorem B1918403 : Blo 263822 1918403 := bstep (se 1 (by rfl) ⟨1438802, by rfl⟩ : syracuseStep 1918403 = 2877605) B2877605
theorem B3032639 : Blo 263822 3032639 := bstep (se 1 (by rfl) ⟨2274479, by rfl⟩ : syracuseStep 3032639 = 4548959) B4548959
theorem B378847 : Blo 263822 378847 := bstep (se 1 (by rfl) ⟨284135, by rfl⟩ : syracuseStep 378847 = 568271) B568271
theorem B2017385 : Blo 263822 2017385 := bstep (se 2 (by rfl) ⟨756519, by rfl⟩ : syracuseStep 2017385 = 1513039) B1513039
theorem B1460369 : Blo 263822 1460369 := bstep (se 2 (by rfl) ⟨547638, by rfl⟩ : syracuseStep 1460369 = 1095277) B1095277
theorem B3852947 : Blo 263822 3852947 := bstep (se 1 (by rfl) ⟨2889710, by rfl⟩ : syracuseStep 3852947 = 5779421) B5779421
theorem B8276779 : Blo 263822 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B676127 : Blo 263822 676127 := bstep (se 1 (by rfl) ⟨507095, by rfl⟩ : syracuseStep 676127 = 1014191) B1014191
theorem B807479 : Blo 263822 807479 := bstep (se 1 (by rfl) ⟨605609, by rfl⟩ : syracuseStep 807479 = 1211219) B1211219
theorem B971531 : Blo 263822 971531 := bstep (se 1 (by rfl) ⟨728648, by rfl⟩ : syracuseStep 971531 = 1457297) B1457297
theorem B611135 : Blo 263822 611135 := bstep (se 1 (by rfl) ⟨458351, by rfl⟩ : syracuseStep 611135 = 916703) B916703
theorem B1135721 : Blo 263822 1135721 := bstep (se 2 (by rfl) ⟨425895, by rfl⟩ : syracuseStep 1135721 = 851791) B851791
theorem B6182027 : Blo 263822 6182027 := bstep (se 1 (by rfl) ⟨4636520, by rfl⟩ : syracuseStep 6182027 = 9273041) B9273041
theorem B16602457 : Blo 263822 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B448105 : Blo 263822 448105 := bstep (se 2 (by rfl) ⟨168039, by rfl⟩ : syracuseStep 448105 = 336079) B336079
theorem B448895 : Blo 263822 448895 := bstep (se 1 (by rfl) ⟨336671, by rfl⟩ : syracuseStep 448895 = 673343) B673343
theorem B449327 : Blo 263822 449327 := bstep (se 1 (by rfl) ⟨336995, by rfl⟩ : syracuseStep 449327 = 673991) B673991
theorem B318311 : Blo 263822 318311 := bstep (se 1 (by rfl) ⟨238733, by rfl⟩ : syracuseStep 318311 = 477467) B477467
theorem B2907011 : Blo 263822 2907011 := bstep (se 1 (by rfl) ⟨2180258, by rfl⟩ : syracuseStep 2907011 = 4360517) B4360517
theorem B3824927 : Blo 263822 3824927 := bstep (se 1 (by rfl) ⟨2868695, by rfl⟩ : syracuseStep 3824927 = 5737391) B5737391
theorem B1465847 : Blo 263822 1465847 := bstep (se 1 (by rfl) ⟨1099385, by rfl⟩ : syracuseStep 1465847 = 2198771) B2198771
theorem B3661433 : Blo 263822 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B1925153 : Blo 263822 1925153 := bstep (se 2 (by rfl) ⟨721932, by rfl⟩ : syracuseStep 1925153 = 1443865) B1443865
theorem B450623 : Blo 263822 450623 := bstep (se 1 (by rfl) ⟨337967, by rfl⟩ : syracuseStep 450623 = 675935) B675935
theorem B1008071 : Blo 263822 1008071 := bstep (se 1 (by rfl) ⟨756053, by rfl⟩ : syracuseStep 1008071 = 1512107) B1512107
theorem B1139359 : Blo 263822 1139359 := bstep (se 1 (by rfl) ⟨854519, by rfl⟩ : syracuseStep 1139359 = 1709039) B1709039
theorem B3039929 : Blo 263822 3039929 := bstep (se 2 (by rfl) ⟨1139973, by rfl⟩ : syracuseStep 3039929 = 2279947) B2279947
theorem B1368857 : Blo 263822 1368857 := bstep (se 2 (by rfl) ⟨513321, by rfl⟩ : syracuseStep 1368857 = 1026643) B1026643
theorem B320743 : Blo 263822 320743 := bstep (se 1 (by rfl) ⟨240557, by rfl⟩ : syracuseStep 320743 = 481115) B481115
theorem B27453329 : Blo 263822 27453329 := bstep (se 2 (by rfl) ⟨10294998, by rfl⟩ : syracuseStep 27453329 = 20589997) B20589997
theorem B2746667 : Blo 263822 2746667 := bstep (se 1 (by rfl) ⟨2060000, by rfl⟩ : syracuseStep 2746667 = 4120001) B4120001
theorem B2550487 : Blo 263822 2550487 := bstep (se 1 (by rfl) ⟨1912865, by rfl⟩ : syracuseStep 2550487 = 3825731) B3825731
theorem B1338119 : Blo 263822 1338119 := bstep (se 1 (by rfl) ⟨1003589, by rfl⟩ : syracuseStep 1338119 = 2007179) B2007179
theorem B3238865 : Blo 263822 3238865 := bstep (se 2 (by rfl) ⟨1214574, by rfl⟩ : syracuseStep 3238865 = 2429149) B2429149
theorem B32566859 : Blo 263822 32566859 := bstep (se 1 (by rfl) ⟨24425144, by rfl⟩ : syracuseStep 32566859 = 48850289) B48850289
theorem B3239837 : Blo 263822 3239837 := bstep (se 3 (by rfl) ⟨607469, by rfl⟩ : syracuseStep 3239837 = 1214939) B1214939
theorem B1536185 : Blo 263822 1536185 := bstep (se 2 (by rfl) ⟨576069, by rfl⟩ : syracuseStep 1536185 = 1152139) B1152139
theorem B1700119 : Blo 263822 1700119 := bstep (se 1 (by rfl) ⟨1275089, by rfl⟩ : syracuseStep 1700119 = 2550179) B2550179
theorem B1275689 : Blo 263822 1275689 := bstep (se 2 (by rfl) ⟨478383, by rfl⟩ : syracuseStep 1275689 = 956767) B956767
theorem B751531 : Blo 263822 751531 := bstep (se 1 (by rfl) ⟨563648, by rfl⟩ : syracuseStep 751531 = 1127297) B1127297
theorem B4356299 : Blo 263822 4356299 := bstep (se 1 (by rfl) ⟨3267224, by rfl⟩ : syracuseStep 4356299 = 6534449) B6534449
theorem B850151 : Blo 263822 850151 := bstep (se 1 (by rfl) ⟨637613, by rfl⟩ : syracuseStep 850151 = 1275227) B1275227
theorem B3045761 : Blo 263822 3045761 := bstep (se 2 (by rfl) ⟨1142160, by rfl⟩ : syracuseStep 3045761 = 2284321) B2284321
theorem B3406799 : Blo 263822 3406799 := bstep (se 1 (by rfl) ⟨2555099, by rfl⟩ : syracuseStep 3406799 = 5110199) B5110199
theorem B1015163 : Blo 263822 1015163 := bstep (se 1 (by rfl) ⟨761372, by rfl⟩ : syracuseStep 1015163 = 1522745) B1522745
theorem B1080823 : Blo 263822 1080823 := bstep (se 1 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 1080823 = 1621235) B1621235
theorem B2883923 : Blo 263822 2883923 := bstep (se 1 (by rfl) ⟨2162942, by rfl⟩ : syracuseStep 2883923 = 4325885) B4325885
theorem B4096493 : Blo 263822 4096493 := bstep (se 3 (by rfl) ⟨768092, by rfl⟩ : syracuseStep 4096493 = 1536185) B1536185
theorem B1016347 : Blo 263822 1016347 := bstep (se 1 (by rfl) ⟨762260, by rfl⟩ : syracuseStep 1016347 = 1524521) B1524521
theorem B2032451 : Blo 263822 2032451 := bstep (se 1 (by rfl) ⟨1524338, by rfl⟩ : syracuseStep 2032451 = 3048677) B3048677
theorem B6423425 : Blo 263822 6423425 := bstep (se 2 (by rfl) ⟨2408784, by rfl⟩ : syracuseStep 6423425 = 4817569) B4817569
theorem B1278935 : Blo 263822 1278935 := bstep (se 1 (by rfl) ⟨959201, by rfl⟩ : syracuseStep 1278935 = 1918403) B1918403
theorem B1344923 : Blo 263822 1344923 := bstep (se 1 (by rfl) ⟨1008692, by rfl⟩ : syracuseStep 1344923 = 2017385) B2017385
theorem B264511 : Blo 263822 264511 := bstep (se 1 (by rfl) ⟨198383, by rfl⟩ : syracuseStep 264511 = 396767) B396767
theorem B264551 : Blo 263822 264551 := bstep (se 1 (by rfl) ⟨198413, by rfl⟩ : syracuseStep 264551 = 396827) B396827
theorem B264639 : Blo 263822 264639 := bstep (se 1 (by rfl) ⟨198479, by rfl⟩ : syracuseStep 264639 = 396959) B396959
theorem B395753 : Blo 263822 395753 := bstep (se 2 (by rfl) ⟨148407, by rfl⟩ : syracuseStep 395753 = 296815) B296815
theorem B264815 : Blo 263822 264815 := bstep (se 1 (by rfl) ⟨198611, by rfl⟩ : syracuseStep 264815 = 397223) B397223
theorem B395903 : Blo 263822 395903 := bstep (se 1 (by rfl) ⟨296927, by rfl⟩ : syracuseStep 395903 = 593855) B593855
theorem B264831 : Blo 263822 264831 := bstep (se 1 (by rfl) ⟨198623, by rfl⟩ : syracuseStep 264831 = 397247) B397247
theorem B264935 : Blo 263822 264935 := bstep (se 1 (by rfl) ⟨198701, by rfl⟩ : syracuseStep 264935 = 397403) B397403
theorem B1510123 : Blo 263822 1510123 := bstep (se 1 (by rfl) ⟨1132592, by rfl⟩ : syracuseStep 1510123 = 2265185) B2265185
theorem B396041 : Blo 263822 396041 := bstep (se 2 (by rfl) ⟨148515, by rfl⟩ : syracuseStep 396041 = 297031) B297031
theorem B265031 : Blo 263822 265031 := bstep (se 1 (by rfl) ⟨198773, by rfl⟩ : syracuseStep 265031 = 397547) B397547
theorem B265071 : Blo 263822 265071 := bstep (se 1 (by rfl) ⟨198803, by rfl⟩ : syracuseStep 265071 = 397607) B397607
theorem B396281 : Blo 263822 396281 := bstep (se 2 (by rfl) ⟨148605, by rfl⟩ : syracuseStep 396281 = 297211) B297211
theorem B265247 : Blo 263822 265247 := bstep (se 1 (by rfl) ⟨198935, by rfl⟩ : syracuseStep 265247 = 397871) B397871
theorem B396455 : Blo 263822 396455 := bstep (se 1 (by rfl) ⟨297341, by rfl⟩ : syracuseStep 396455 = 594683) B594683
theorem B265383 : Blo 263822 265383 := bstep (se 1 (by rfl) ⟨199037, by rfl⟩ : syracuseStep 265383 = 398075) B398075
theorem B757147 : Blo 263822 757147 := bstep (se 1 (by rfl) ⟨567860, by rfl⟩ : syracuseStep 757147 = 1135721) B1135721
theorem B265631 : Blo 263822 265631 := bstep (se 1 (by rfl) ⟨199223, by rfl⟩ : syracuseStep 265631 = 398447) B398447
theorem B265679 : Blo 263822 265679 := bstep (se 1 (by rfl) ⟨199259, by rfl⟩ : syracuseStep 265679 = 398519) B398519
theorem B396905 : Blo 263822 396905 := bstep (se 2 (by rfl) ⟨148839, by rfl⟩ : syracuseStep 396905 = 297679) B297679
theorem B265839 : Blo 263822 265839 := bstep (se 1 (by rfl) ⟨199379, by rfl⟩ : syracuseStep 265839 = 398759) B398759
theorem B593639 : Blo 263822 593639 := bstep (se 1 (by rfl) ⟨445229, by rfl⟩ : syracuseStep 593639 = 890459) B890459
theorem B265959 : Blo 263822 265959 := bstep (se 1 (by rfl) ⟨199469, by rfl⟩ : syracuseStep 265959 = 398939) B398939
theorem B397193 : Blo 263822 397193 := bstep (se 2 (by rfl) ⟨148947, by rfl⟩ : syracuseStep 397193 = 297895) B297895
theorem B397433 : Blo 263822 397433 := bstep (se 2 (by rfl) ⟨149037, by rfl⟩ : syracuseStep 397433 = 298075) B298075
theorem B266463 : Blo 263822 266463 := bstep (se 1 (by rfl) ⟨199847, by rfl⟩ : syracuseStep 266463 = 399695) B399695
theorem B266479 : Blo 263822 266479 := bstep (se 1 (by rfl) ⟨199859, by rfl⟩ : syracuseStep 266479 = 399719) B399719
theorem B299263 : Blo 263822 299263 := bstep (se 1 (by rfl) ⟨224447, by rfl⟩ : syracuseStep 299263 = 448895) B448895
theorem B266523 : Blo 263822 266523 := bstep (se 1 (by rfl) ⟨199892, by rfl⟩ : syracuseStep 266523 = 399785) B399785
theorem B594215 : Blo 263822 594215 := bstep (se 1 (by rfl) ⟨445661, by rfl⟩ : syracuseStep 594215 = 891323) B891323
theorem B266779 : Blo 263822 266779 := bstep (se 1 (by rfl) ⟨200084, by rfl⟩ : syracuseStep 266779 = 400169) B400169
theorem B299551 : Blo 263822 299551 := bstep (se 1 (by rfl) ⟨224663, by rfl⟩ : syracuseStep 299551 = 449327) B449327
theorem B1938007 : Blo 263822 1938007 := bstep (se 1 (by rfl) ⟨1453505, by rfl⟩ : syracuseStep 1938007 = 2907011) B2907011
theorem B397991 : Blo 263822 397991 := bstep (se 1 (by rfl) ⟨298493, by rfl⟩ : syracuseStep 397991 = 596987) B596987
theorem B266919 : Blo 263822 266919 := bstep (se 1 (by rfl) ⟨200189, by rfl⟩ : syracuseStep 266919 = 400379) B400379
theorem B266943 : Blo 263822 266943 := bstep (se 1 (by rfl) ⟨200207, by rfl⟩ : syracuseStep 266943 = 400415) B400415
theorem B266959 : Blo 263822 266959 := bstep (se 1 (by rfl) ⟨200219, by rfl⟩ : syracuseStep 266959 = 400439) B400439
theorem B398111 : Blo 263822 398111 := bstep (se 1 (by rfl) ⟨298583, by rfl⟩ : syracuseStep 398111 = 597167) B597167
theorem B267039 : Blo 263822 267039 := bstep (se 1 (by rfl) ⟨200279, by rfl⟩ : syracuseStep 267039 = 400559) B400559
theorem B398207 : Blo 263822 398207 := bstep (se 1 (by rfl) ⟨298655, by rfl⟩ : syracuseStep 398207 = 597311) B597311
theorem B267135 : Blo 263822 267135 := bstep (se 1 (by rfl) ⟨200351, by rfl⟩ : syracuseStep 267135 = 400703) B400703
theorem B398279 : Blo 263822 398279 := bstep (se 1 (by rfl) ⟨298709, by rfl⟩ : syracuseStep 398279 = 597419) B597419
theorem B267231 : Blo 263822 267231 := bstep (se 1 (by rfl) ⟨200423, by rfl⟩ : syracuseStep 267231 = 400847) B400847
theorem B267487 : Blo 263822 267487 := bstep (se 1 (by rfl) ⟨200615, by rfl⟩ : syracuseStep 267487 = 401231) B401231
theorem B398591 : Blo 263822 398591 := bstep (se 1 (by rfl) ⟨298943, by rfl⟩ : syracuseStep 398591 = 597887) B597887
theorem B267519 : Blo 263822 267519 := bstep (se 1 (by rfl) ⟨200639, by rfl⟩ : syracuseStep 267519 = 401279) B401279
theorem B398639 : Blo 263822 398639 := bstep (se 1 (by rfl) ⟨298979, by rfl⟩ : syracuseStep 398639 = 597959) B597959
theorem B267567 : Blo 263822 267567 := bstep (se 1 (by rfl) ⟨200675, by rfl⟩ : syracuseStep 267567 = 401351) B401351
theorem B1283435 : Blo 263822 1283435 := bstep (se 1 (by rfl) ⟨962576, by rfl⟩ : syracuseStep 1283435 = 1925153) B1925153
theorem B300415 : Blo 263822 300415 := bstep (se 1 (by rfl) ⟨225311, by rfl⟩ : syracuseStep 300415 = 450623) B450623
theorem B267727 : Blo 263822 267727 := bstep (se 1 (by rfl) ⟨200795, by rfl⟩ : syracuseStep 267727 = 401591) B401591
theorem B398879 : Blo 263822 398879 := bstep (se 1 (by rfl) ⟨299159, by rfl⟩ : syracuseStep 398879 = 598319) B598319
theorem B267807 : Blo 263822 267807 := bstep (se 1 (by rfl) ⟨200855, by rfl⟩ : syracuseStep 267807 = 401711) B401711
theorem B595547 : Blo 263822 595547 := bstep (se 1 (by rfl) ⟨446660, by rfl⟩ : syracuseStep 595547 = 893321) B893321
theorem B2266825 : Blo 263822 2266825 := bstep (se 2 (by rfl) ⟨850059, by rfl⟩ : syracuseStep 2266825 = 1700119) B1700119
theorem B399431 : Blo 263822 399431 := bstep (se 1 (by rfl) ⟨299573, by rfl⟩ : syracuseStep 399431 = 599147) B599147
theorem B759881 : Blo 263822 759881 := bstep (se 2 (by rfl) ⟨284955, by rfl⟩ : syracuseStep 759881 = 569911) B569911
theorem B2890019 : Blo 263822 2890019 := bstep (se 1 (by rfl) ⟨2167514, by rfl⟩ : syracuseStep 2890019 = 4335029) B4335029
theorem B1710629 : Blo 263822 1710629 := bstep (se 4 (by rfl) ⟨160371, by rfl⟩ : syracuseStep 1710629 = 320743) B320743
theorem B400031 : Blo 263822 400031 := bstep (se 1 (by rfl) ⟨300023, by rfl⟩ : syracuseStep 400031 = 600047) B600047
theorem B334631 : Blo 263822 334631 := bstep (se 1 (by rfl) ⟨250973, by rfl⟩ : syracuseStep 334631 = 501947) B501947
theorem B334783 : Blo 263822 334783 := bstep (se 1 (by rfl) ⟨251087, by rfl⟩ : syracuseStep 334783 = 502175) B502175
theorem B4562081 : Blo 263822 4562081 := bstep (se 2 (by rfl) ⟨1710780, by rfl⟩ : syracuseStep 4562081 = 3421561) B3421561
theorem B892079 : Blo 263822 892079 := bstep (se 1 (by rfl) ⟨669059, by rfl⟩ : syracuseStep 892079 = 1338119) B1338119
theorem B597275 : Blo 263822 597275 := bstep (se 1 (by rfl) ⟨447956, by rfl⟩ : syracuseStep 597275 = 895913) B895913
theorem B597473 : Blo 263822 597473 := bstep (se 2 (by rfl) ⟨224052, by rfl⟩ : syracuseStep 597473 = 448105) B448105
theorem B400967 : Blo 263822 400967 := bstep (se 1 (by rfl) ⟨300725, by rfl⟩ : syracuseStep 400967 = 601451) B601451
theorem B401147 : Blo 263822 401147 := bstep (se 1 (by rfl) ⟨300860, by rfl⟩ : syracuseStep 401147 = 601721) B601721
theorem B566767 : Blo 263822 566767 := bstep (se 1 (by rfl) ⟨425075, by rfl⟩ : syracuseStep 566767 = 850151) B850151
theorem B23602823 : Blo 263822 23602823 := bstep (se 1 (by rfl) ⟨17702117, by rfl⟩ : syracuseStep 23602823 = 35404235) B35404235
theorem B599723 : Blo 263822 599723 := bstep (se 1 (by rfl) ⟨449792, by rfl⟩ : syracuseStep 599723 = 899585) B899585
theorem B2271199 : Blo 263822 2271199 := bstep (se 1 (by rfl) ⟨1703399, by rfl⟩ : syracuseStep 2271199 = 3406799) B3406799
theorem B600443 : Blo 263822 600443 := bstep (se 1 (by rfl) ⟨450332, by rfl⟩ : syracuseStep 600443 = 900665) B900665
theorem B600551 : Blo 263822 600551 := bstep (se 1 (by rfl) ⟨450413, by rfl⟩ : syracuseStep 600551 = 900827) B900827
theorem B2861689 : Blo 263822 2861689 := bstep (se 2 (by rfl) ⟨1073133, by rfl⟩ : syracuseStep 2861689 = 2146267) B2146267
theorem B502433 : Blo 263822 502433 := bstep (se 2 (by rfl) ⟨188412, by rfl⟩ : syracuseStep 502433 = 376825) B376825
theorem B895805 : Blo 263822 895805 := bstep (se 3 (by rfl) ⟨167963, by rfl⟩ : syracuseStep 895805 = 335927) B335927
theorem B1519145 : Blo 263822 1519145 := bstep (se 2 (by rfl) ⟨569679, by rfl⟩ : syracuseStep 1519145 = 1139359) B1139359
theorem B2273183 : Blo 263822 2273183 := bstep (se 1 (by rfl) ⟨1704887, by rfl⟩ : syracuseStep 2273183 = 3409775) B3409775
theorem B3650285 : Blo 263822 3650285 := bstep (se 3 (by rfl) ⟨684428, by rfl⟩ : syracuseStep 3650285 = 1368857) B1368857
theorem B897803 : Blo 263822 897803 := bstep (se 1 (by rfl) ⟨673352, by rfl⟩ : syracuseStep 897803 = 1346705) B1346705
theorem B668513 : Blo 263822 668513 := bstep (se 2 (by rfl) ⟨250692, by rfl⟩ : syracuseStep 668513 = 501385) B501385
theorem B2143219 : Blo 263822 2143219 := bstep (se 1 (by rfl) ⟨1607414, by rfl⟩ : syracuseStep 2143219 = 3214829) B3214829
theorem B635951 : Blo 263822 635951 := bstep (se 1 (by rfl) ⟨476963, by rfl⟩ : syracuseStep 635951 = 953927) B953927
theorem B505129 : Blo 263822 505129 := bstep (se 2 (by rfl) ⟨189423, by rfl⟩ : syracuseStep 505129 = 378847) B378847
theorem B2012525 : Blo 263822 2012525 := bstep (se 3 (by rfl) ⟨377348, by rfl⟩ : syracuseStep 2012525 = 754697) B754697
theorem B3847823 : Blo 263822 3847823 := bstep (se 1 (by rfl) ⟨2885867, by rfl⟩ : syracuseStep 3847823 = 5771735) B5771735
theorem B538319 : Blo 263822 538319 := bstep (se 1 (by rfl) ⟨403739, by rfl⟩ : syracuseStep 538319 = 807479) B807479
theorem B2013011 : Blo 263822 2013011 := bstep (se 1 (by rfl) ⟨1509758, by rfl⟩ : syracuseStep 2013011 = 3019517) B3019517
theorem B407423 : Blo 263822 407423 := bstep (se 1 (by rfl) ⟨305567, by rfl⟩ : syracuseStep 407423 = 611135) B611135
theorem B505835 : Blo 263822 505835 := bstep (se 1 (by rfl) ⟨379376, by rfl⟩ : syracuseStep 505835 = 758753) B758753
theorem B899639 : Blo 263822 899639 := bstep (se 1 (by rfl) ⟨674729, by rfl⟩ : syracuseStep 899639 = 1349459) B1349459
theorem B16366211 : Blo 263822 16366211 := bstep (se 1 (by rfl) ⟨12274658, by rfl⟩ : syracuseStep 16366211 = 24549317) B24549317
theorem B899963 : Blo 263822 899963 := bstep (se 1 (by rfl) ⟨674972, by rfl⟩ : syracuseStep 899963 = 1349945) B1349945
theorem B900395 : Blo 263822 900395 := bstep (se 1 (by rfl) ⟨675296, by rfl⟩ : syracuseStep 900395 = 1350593) B1350593
theorem B2440955 : Blo 263822 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B508007 : Blo 263822 508007 := bstep (se 1 (by rfl) ⟨381005, by rfl⟩ : syracuseStep 508007 = 762011) B762011
theorem B672047 : Blo 263822 672047 := bstep (se 1 (by rfl) ⟨504035, by rfl⟩ : syracuseStep 672047 = 1008071) B1008071
theorem B2867567 : Blo 263822 2867567 := bstep (se 1 (by rfl) ⟨2150675, by rfl⟩ : syracuseStep 2867567 = 4301351) B4301351
theorem B11616797 : Blo 263822 11616797 := bstep (se 3 (by rfl) ⟨2178149, by rfl⟩ : syracuseStep 11616797 = 4356299) B4356299
theorem B7324445 : Blo 263822 7324445 := bstep (se 3 (by rfl) ⟨1373333, by rfl⟩ : syracuseStep 7324445 = 2746667) B2746667
theorem B18302219 : Blo 263822 18302219 := bstep (se 1 (by rfl) ⟨13726664, by rfl⟩ : syracuseStep 18302219 = 27453329) B27453329
theorem B542009 : Blo 263822 542009 := bstep (se 2 (by rfl) ⟨203253, by rfl⟩ : syracuseStep 542009 = 406507) B406507
theorem B902555 : Blo 263822 902555 := bstep (se 1 (by rfl) ⟨676916, by rfl⟩ : syracuseStep 902555 = 1353833) B1353833
theorem B10274525 : Blo 263822 10274525 := bstep (se 3 (by rfl) ⟨1926473, by rfl⟩ : syracuseStep 10274525 = 3852947) B3852947
theorem B22136609 : Blo 263822 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B21711239 : Blo 263822 21711239 := bstep (se 1 (by rfl) ⟨16283429, by rfl⟩ : syracuseStep 21711239 = 32566859) B32566859
theorem B1002041 : Blo 263822 1002041 := bstep (se 2 (by rfl) ⟨375765, by rfl⟩ : syracuseStep 1002041 = 751531) B751531
theorem B2411707 : Blo 263822 2411707 := bstep (se 1 (by rfl) ⟨1808780, by rfl⟩ : syracuseStep 2411707 = 3617561) B3617561
theorem B445979 : Blo 263822 445979 := bstep (se 1 (by rfl) ⟨334484, by rfl⟩ : syracuseStep 445979 = 668969) B668969
theorem B3395317 : Blo 263822 3395317 := bstep (se 5 (by rfl) ⟨159155, by rfl⟩ : syracuseStep 3395317 = 318311) B318311
theorem B447295 : Blo 263822 447295 := bstep (se 1 (by rfl) ⟨335471, by rfl⟩ : syracuseStep 447295 = 670943) B670943
theorem B676775 : Blo 263822 676775 := bstep (se 1 (by rfl) ⟨507581, by rfl⟩ : syracuseStep 676775 = 1015163) B1015163
theorem B906223 : Blo 263822 906223 := bstep (se 1 (by rfl) ⟨679667, by rfl⟩ : syracuseStep 906223 = 1359335) B1359335
theorem B1922555 : Blo 263822 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B677879 : Blo 263822 677879 := bstep (se 1 (by rfl) ⟨508409, by rfl⟩ : syracuseStep 677879 = 1016819) B1016819
theorem B448699 : Blo 263822 448699 := bstep (se 1 (by rfl) ⟨336524, by rfl⟩ : syracuseStep 448699 = 673049) B673049
theorem B1268095 : Blo 263822 1268095 := bstep (se 1 (by rfl) ⟨951071, by rfl⟩ : syracuseStep 1268095 = 1902143) B1902143
theorem B2021759 : Blo 263822 2021759 := bstep (se 1 (by rfl) ⟨1516319, by rfl⟩ : syracuseStep 2021759 = 3032639) B3032639
theorem B7232273 : Blo 263822 7232273 := bstep (se 2 (by rfl) ⟨2712102, by rfl⟩ : syracuseStep 7232273 = 5424205) B5424205
theorem B449401 : Blo 263822 449401 := bstep (se 2 (by rfl) ⟨168525, by rfl⟩ : syracuseStep 449401 = 337051) B337051
theorem B1137959 : Blo 263822 1137959 := bstep (se 1 (by rfl) ⟨853469, by rfl⟩ : syracuseStep 1137959 = 1706939) B1706939
theorem B1138319 : Blo 263822 1138319 := bstep (se 1 (by rfl) ⟨853739, by rfl⟩ : syracuseStep 1138319 = 1707479) B1707479
theorem B2285657 : Blo 263822 2285657 := bstep (se 2 (by rfl) ⟨857121, by rfl⟩ : syracuseStep 2285657 = 1714243) B1714243
theorem B450751 : Blo 263822 450751 := bstep (se 1 (by rfl) ⟨338063, by rfl⟩ : syracuseStep 450751 = 676127) B676127
theorem B647687 : Blo 263822 647687 := bstep (se 1 (by rfl) ⟨485765, by rfl⟩ : syracuseStep 647687 = 971531) B971531
theorem B4121351 : Blo 263822 4121351 := bstep (se 1 (by rfl) ⟨3091013, by rfl⟩ : syracuseStep 4121351 = 6182027) B6182027
theorem B1926013 : Blo 263822 1926013 := bstep (se 3 (by rfl) ⟨361127, by rfl⟩ : syracuseStep 1926013 = 722255) B722255
theorem B3400649 : Blo 263822 3400649 := bstep (se 2 (by rfl) ⟨1275243, by rfl⟩ : syracuseStep 3400649 = 2550487) B2550487
theorem B11035705 : Blo 263822 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B1008875 : Blo 263822 1008875 := bstep (se 1 (by rfl) ⟨756656, by rfl⟩ : syracuseStep 1008875 = 1513313) B1513313
theorem B1336823 : Blo 263822 1336823 := bstep (se 1 (by rfl) ⟨1002617, by rfl⟩ : syracuseStep 1336823 = 2005235) B2005235
theorem B2549951 : Blo 263822 2549951 := bstep (se 1 (by rfl) ⟨1912463, by rfl⟩ : syracuseStep 2549951 = 3824927) B3824927
theorem B2156777 : Blo 263822 2156777 := bstep (se 2 (by rfl) ⟨808791, by rfl⟩ : syracuseStep 2156777 = 1617583) B1617583
theorem B977231 : Blo 263822 977231 := bstep (se 1 (by rfl) ⟨732923, by rfl⟩ : syracuseStep 977231 = 1465847) B1465847
theorem B1141751 : Blo 263822 1141751 := bstep (se 1 (by rfl) ⟨856313, by rfl⟩ : syracuseStep 1141751 = 1712627) B1712627
theorem B3894317 : Blo 263822 3894317 := bstep (se 3 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 3894317 = 1460369) B1460369
theorem B2026619 : Blo 263822 2026619 := bstep (se 1 (by rfl) ⟨1519964, by rfl⟩ : syracuseStep 2026619 = 3039929) B3039929
theorem B1011487 : Blo 263822 1011487 := bstep (se 1 (by rfl) ⟨758615, by rfl⟩ : syracuseStep 1011487 = 1517231) B1517231
theorem B1208135 : Blo 263822 1208135 := bstep (se 1 (by rfl) ⟨906101, by rfl⟩ : syracuseStep 1208135 = 1812203) B1812203
theorem B2159243 : Blo 263822 2159243 := bstep (se 1 (by rfl) ⟨1619432, by rfl⟩ : syracuseStep 2159243 = 3238865) B3238865
theorem B422891 : Blo 263822 422891 := bstep (se 1 (by rfl) ⟨317168, by rfl⟩ : syracuseStep 422891 = 634337) B634337
theorem B7632083 : Blo 263822 7632083 := bstep (se 1 (by rfl) ⟨5724062, by rfl⟩ : syracuseStep 7632083 = 11448125) B11448125
theorem B2159891 : Blo 263822 2159891 := bstep (se 1 (by rfl) ⟨1619918, by rfl⟩ : syracuseStep 2159891 = 3239837) B3239837
theorem B5141879 : Blo 263822 5141879 := bstep (se 1 (by rfl) ⟨3856409, by rfl⟩ : syracuseStep 5141879 = 7712819) B7712819
theorem B1013735 : Blo 263822 1013735 := bstep (se 1 (by rfl) ⟨760301, by rfl⟩ : syracuseStep 1013735 = 1520603) B1520603
theorem B850459 : Blo 263822 850459 := bstep (se 1 (by rfl) ⟨637844, by rfl⟩ : syracuseStep 850459 = 1275689) B1275689
theorem B2030507 : Blo 263822 2030507 := bstep (se 1 (by rfl) ⟨1522880, by rfl⟩ : syracuseStep 2030507 = 3045761) B3045761
theorem B1441097 : Blo 263822 1441097 := bstep (se 2 (by rfl) ⟨540411, by rfl⟩ : syracuseStep 1441097 = 1080823) B1080823
theorem B1507025 : Blo 263822 1507025 := bstep (se 2 (by rfl) ⟨565134, by rfl⟩ : syracuseStep 1507025 = 1130269) B1130269
theorem B4882963 : Blo 263822 4882963 := bstep (se 1 (by rfl) ⟨3662222, by rfl⟩ : syracuseStep 4882963 = 7324445) B7324445
theorem B852623 : Blo 263822 852623 := bstep (se 1 (by rfl) ⟨639467, by rfl⟩ : syracuseStep 852623 = 1278935) B1278935
theorem B6849683 : Blo 263822 6849683 := bstep (se 1 (by rfl) ⟨5137262, by rfl⟩ : syracuseStep 6849683 = 10274525) B10274525
theorem B14714273 : Blo 263822 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B263835 : Blo 263822 263835 := bstep (se 1 (by rfl) ⟨197876, by rfl⟩ : syracuseStep 263835 = 395753) B395753
theorem B263935 : Blo 263822 263935 := bstep (se 1 (by rfl) ⟨197951, by rfl⟩ : syracuseStep 263935 = 395903) B395903
theorem B264027 : Blo 263822 264027 := bstep (se 1 (by rfl) ⟨198020, by rfl⟩ : syracuseStep 264027 = 396041) B396041
theorem B9734093 : Blo 263822 9734093 := bstep (se 3 (by rfl) ⟨1825142, by rfl⟩ : syracuseStep 9734093 = 3650285) B3650285
theorem B755689 : Blo 263822 755689 := bstep (se 2 (by rfl) ⟨283383, by rfl⟩ : syracuseStep 755689 = 566767) B566767
theorem B264187 : Blo 263822 264187 := bstep (se 1 (by rfl) ⟨198140, by rfl⟩ : syracuseStep 264187 = 396281) B396281
theorem B264303 : Blo 263822 264303 := bstep (se 1 (by rfl) ⟨198227, by rfl⟩ : syracuseStep 264303 = 396455) B396455
theorem B297319 : Blo 263822 297319 := bstep (se 1 (by rfl) ⟨222989, by rfl⟩ : syracuseStep 297319 = 445979) B445979
theorem B264603 : Blo 263822 264603 := bstep (se 1 (by rfl) ⟨198452, by rfl⟩ : syracuseStep 264603 = 396905) B396905
theorem B395759 : Blo 263822 395759 := bstep (se 1 (by rfl) ⟨296819, by rfl⟩ : syracuseStep 395759 = 593639) B593639
theorem B264795 : Blo 263822 264795 := bstep (se 1 (by rfl) ⟨198596, by rfl⟩ : syracuseStep 264795 = 397193) B397193
theorem B264955 : Blo 263822 264955 := bstep (se 1 (by rfl) ⟨198716, by rfl⟩ : syracuseStep 264955 = 397433) B397433
theorem B396143 : Blo 263822 396143 := bstep (se 1 (by rfl) ⟨297107, by rfl⟩ : syracuseStep 396143 = 594215) B594215
theorem B265327 : Blo 263822 265327 := bstep (se 1 (by rfl) ⟨198995, by rfl⟩ : syracuseStep 265327 = 397991) B397991
theorem B265407 : Blo 263822 265407 := bstep (se 1 (by rfl) ⟨199055, by rfl⟩ : syracuseStep 265407 = 398111) B398111
theorem B265471 : Blo 263822 265471 := bstep (se 1 (by rfl) ⟨199103, by rfl⟩ : syracuseStep 265471 = 398207) B398207
theorem B265519 : Blo 263822 265519 := bstep (se 1 (by rfl) ⟨199139, by rfl⟩ : syracuseStep 265519 = 398279) B398279
theorem B1445357 : Blo 263822 1445357 := bstep (se 3 (by rfl) ⟨271004, by rfl⟩ : syracuseStep 1445357 = 542009) B542009
theorem B265727 : Blo 263822 265727 := bstep (se 1 (by rfl) ⟨199295, by rfl⟩ : syracuseStep 265727 = 398591) B398591
theorem B265759 : Blo 263822 265759 := bstep (se 1 (by rfl) ⟨199319, by rfl⟩ : syracuseStep 265759 = 398639) B398639
theorem B855623 : Blo 263822 855623 := bstep (se 1 (by rfl) ⟨641717, by rfl⟩ : syracuseStep 855623 = 1283435) B1283435
theorem B1281703 : Blo 263822 1281703 := bstep (se 1 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 1281703 = 1922555) B1922555
theorem B265919 : Blo 263822 265919 := bstep (se 1 (by rfl) ⟨199439, by rfl⟩ : syracuseStep 265919 = 398879) B398879
theorem B397031 : Blo 263822 397031 := bstep (se 1 (by rfl) ⟨297773, by rfl⟩ : syracuseStep 397031 = 595547) B595547
theorem B266287 : Blo 263822 266287 := bstep (se 1 (by rfl) ⟨199715, by rfl⟩ : syracuseStep 266287 = 399431) B399431
theorem B3215609 : Blo 263822 3215609 := bstep (se 2 (by rfl) ⟨1205853, by rfl⟩ : syracuseStep 3215609 = 2411707) B2411707
theorem B1347839 : Blo 263822 1347839 := bstep (se 1 (by rfl) ⟨1010879, by rfl⟩ : syracuseStep 1347839 = 2021759) B2021759
theorem B266687 : Blo 263822 266687 := bstep (se 1 (by rfl) ⟨200015, by rfl⟩ : syracuseStep 266687 = 400031) B400031
theorem B4821515 : Blo 263822 4821515 := bstep (se 1 (by rfl) ⟨3616136, by rfl⟩ : syracuseStep 4821515 = 7232273) B7232273
theorem B594719 : Blo 263822 594719 := bstep (se 1 (by rfl) ⟨446039, by rfl⟩ : syracuseStep 594719 = 892079) B892079
theorem B398183 : Blo 263822 398183 := bstep (se 1 (by rfl) ⟨298637, by rfl⟩ : syracuseStep 398183 = 597275) B597275
theorem B758639 : Blo 263822 758639 := bstep (se 1 (by rfl) ⟨568979, by rfl⟩ : syracuseStep 758639 = 1137959) B1137959
theorem B398315 : Blo 263822 398315 := bstep (se 1 (by rfl) ⟨298736, by rfl⟩ : syracuseStep 398315 = 597473) B597473
theorem B4527089 : Blo 263822 4527089 := bstep (se 2 (by rfl) ⟨1697658, by rfl⟩ : syracuseStep 4527089 = 3395317) B3395317
theorem B1086461 : Blo 263822 1086461 := bstep (se 3 (by rfl) ⟨203711, by rfl⟩ : syracuseStep 1086461 = 407423) B407423
theorem B1348649 : Blo 263822 1348649 := bstep (se 2 (by rfl) ⟨505743, by rfl⟩ : syracuseStep 1348649 = 1011487) B1011487
theorem B267311 : Blo 263822 267311 := bstep (se 1 (by rfl) ⟨200483, by rfl⟩ : syracuseStep 267311 = 400967) B400967
theorem B758879 : Blo 263822 758879 := bstep (se 1 (by rfl) ⟨569159, by rfl⟩ : syracuseStep 758879 = 1138319) B1138319
theorem B267431 : Blo 263822 267431 := bstep (se 1 (by rfl) ⟨200573, by rfl⟩ : syracuseStep 267431 = 401147) B401147
theorem B399017 : Blo 263822 399017 := bstep (se 2 (by rfl) ⟨149631, by rfl⟩ : syracuseStep 399017 = 299263) B299263
theorem B2267099 : Blo 263822 2267099 := bstep (se 1 (by rfl) ⟨1700324, by rfl⟩ : syracuseStep 2267099 = 3400649) B3400649
theorem B399401 : Blo 263822 399401 := bstep (se 2 (by rfl) ⟨149775, by rfl⟩ : syracuseStep 399401 = 299551) B299551
theorem B891215 : Blo 263822 891215 := bstep (se 1 (by rfl) ⟨668411, by rfl⟩ : syracuseStep 891215 = 1336823) B1336823
theorem B596393 : Blo 263822 596393 := bstep (se 2 (by rfl) ⟨223647, by rfl⟩ : syracuseStep 596393 = 447295) B447295
theorem B15735215 : Blo 263822 15735215 := bstep (se 1 (by rfl) ⟨11801411, by rfl⟩ : syracuseStep 15735215 = 23602823) B23602823
theorem B399815 : Blo 263822 399815 := bstep (se 1 (by rfl) ⟨299861, by rfl⟩ : syracuseStep 399815 = 599723) B599723
theorem B2857625 : Blo 263822 2857625 := bstep (se 2 (by rfl) ⟨1071609, by rfl⟩ : syracuseStep 2857625 = 2143219) B2143219
theorem B400295 : Blo 263822 400295 := bstep (se 1 (by rfl) ⟨300221, by rfl⟩ : syracuseStep 400295 = 600443) B600443
theorem B400367 : Blo 263822 400367 := bstep (se 1 (by rfl) ⟨300275, by rfl⟩ : syracuseStep 400367 = 600551) B600551
theorem B334955 : Blo 263822 334955 := bstep (se 1 (by rfl) ⟨251216, by rfl⟩ : syracuseStep 334955 = 502433) B502433
theorem B400553 : Blo 263822 400553 := bstep (se 2 (by rfl) ⟨150207, by rfl⟩ : syracuseStep 400553 = 300415) B300415
theorem B597203 : Blo 263822 597203 := bstep (se 1 (by rfl) ⟨447902, by rfl⟩ : syracuseStep 597203 = 895805) B895805
theorem B761167 : Blo 263822 761167 := bstep (se 1 (by rfl) ⟨570875, by rfl⟩ : syracuseStep 761167 = 1141751) B1141751
theorem B2596211 : Blo 263822 2596211 := bstep (se 1 (by rfl) ⟨1947158, by rfl⟩ : syracuseStep 2596211 = 3894317) B3894317
theorem B1351079 : Blo 263822 1351079 := bstep (se 1 (by rfl) ⟨1013309, by rfl⟩ : syracuseStep 1351079 = 2026619) B2026619
theorem B892349 : Blo 263822 892349 := bstep (se 3 (by rfl) ⟨167315, by rfl⟩ : syracuseStep 892349 = 334631) B334631
theorem B3022433 : Blo 263822 3022433 := bstep (se 2 (by rfl) ⟨1133412, by rfl⟩ : syracuseStep 3022433 = 2266825) B2266825
theorem B1515455 : Blo 263822 1515455 := bstep (se 1 (by rfl) ⟨1136591, by rfl⟩ : syracuseStep 1515455 = 2273183) B2273183
theorem B598265 : Blo 263822 598265 := bstep (se 2 (by rfl) ⟨224349, by rfl⟩ : syracuseStep 598265 = 448699) B448699
theorem B598535 : Blo 263822 598535 := bstep (se 1 (by rfl) ⟨448901, by rfl⟩ : syracuseStep 598535 = 897803) B897803
theorem B5088055 : Blo 263822 5088055 := bstep (se 1 (by rfl) ⟨3816041, by rfl⟩ : syracuseStep 5088055 = 7632083) B7632083
theorem B2565215 : Blo 263822 2565215 := bstep (se 1 (by rfl) ⟨1923911, by rfl⟩ : syracuseStep 2565215 = 3847823) B3847823
theorem B599201 : Blo 263822 599201 := bstep (se 2 (by rfl) ⟨224700, by rfl⟩ : syracuseStep 599201 = 449401) B449401
theorem B337223 : Blo 263822 337223 := bstep (se 1 (by rfl) ⟨252917, by rfl⟩ : syracuseStep 337223 = 505835) B505835
theorem B599759 : Blo 263822 599759 := bstep (se 1 (by rfl) ⟨449819, by rfl⟩ : syracuseStep 599759 = 899639) B899639
theorem B599975 : Blo 263822 599975 := bstep (se 1 (by rfl) ⟨449981, by rfl⟩ : syracuseStep 599975 = 899963) B899963
theorem B1353671 : Blo 263822 1353671 := bstep (se 1 (by rfl) ⟨1015253, by rfl⟩ : syracuseStep 1353671 = 2030507) B2030507
theorem B3221693 : Blo 263822 3221693 := bstep (se 3 (by rfl) ⟨604067, by rfl⟩ : syracuseStep 3221693 = 1208135) B1208135
theorem B600263 : Blo 263822 600263 := bstep (se 1 (by rfl) ⟨450197, by rfl⟩ : syracuseStep 600263 = 900395) B900395
theorem B960731 : Blo 263822 960731 := bstep (se 1 (by rfl) ⟨720548, by rfl⟩ : syracuseStep 960731 = 1441097) B1441097
theorem B338671 : Blo 263822 338671 := bstep (se 1 (by rfl) ⟨254003, by rfl⟩ : syracuseStep 338671 = 508007) B508007
theorem B601001 : Blo 263822 601001 := bstep (se 2 (by rfl) ⟨225375, by rfl⟩ : syracuseStep 601001 = 450751) B450751
theorem B2730995 : Blo 263822 2730995 := bstep (se 1 (by rfl) ⟨2048246, by rfl⟩ : syracuseStep 2730995 = 4096493) B4096493
theorem B1354967 : Blo 263822 1354967 := bstep (se 1 (by rfl) ⟨1016225, by rfl⟩ : syracuseStep 1354967 = 2032451) B2032451
theorem B1355129 : Blo 263822 1355129 := bstep (se 2 (by rfl) ⟨508173, by rfl⟩ : syracuseStep 1355129 = 1016347) B1016347
theorem B12201479 : Blo 263822 12201479 := bstep (se 1 (by rfl) ⟨9151109, by rfl⟩ : syracuseStep 12201479 = 18302219) B18302219
theorem B896615 : Blo 263822 896615 := bstep (se 1 (by rfl) ⟨672461, by rfl⟩ : syracuseStep 896615 = 1344923) B1344923
theorem B601703 : Blo 263822 601703 := bstep (se 1 (by rfl) ⟨451277, by rfl⟩ : syracuseStep 601703 = 902555) B902555
theorem B7646845 : Blo 263822 7646845 := bstep (se 3 (by rfl) ⟨1433783, by rfl⟩ : syracuseStep 7646845 = 2867567) B2867567
theorem B2568017 : Blo 263822 2568017 := bstep (se 2 (by rfl) ⟨963006, by rfl⟩ : syracuseStep 2568017 = 1926013) B1926013
theorem B30978125 : Blo 263822 30978125 := bstep (se 3 (by rfl) ⟨5808398, by rfl⟩ : syracuseStep 30978125 = 11616797) B11616797
theorem B668027 : Blo 263822 668027 := bstep (se 1 (by rfl) ⟨501020, by rfl⟩ : syracuseStep 668027 = 1002041) B1002041
theorem B3028265 : Blo 263822 3028265 := bstep (se 2 (by rfl) ⟨1135599, by rfl⟩ : syracuseStep 3028265 = 2271199) B2271199
theorem B3815585 : Blo 263822 3815585 := bstep (se 2 (by rfl) ⟨1430844, by rfl⟩ : syracuseStep 3815585 = 2861689) B2861689
theorem B2013497 : Blo 263822 2013497 := bstep (se 2 (by rfl) ⟨755061, by rfl⟩ : syracuseStep 2013497 = 1510123) B1510123
theorem B506587 : Blo 263822 506587 := bstep (se 1 (by rfl) ⟨379940, by rfl⟩ : syracuseStep 506587 = 759881) B759881
theorem B59030957 : Blo 263822 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B1523771 : Blo 263822 1523771 := bstep (se 1 (by rfl) ⟨1142828, by rfl⟩ : syracuseStep 1523771 = 2285657) B2285657
theorem B672583 : Blo 263822 672583 := bstep (se 1 (by rfl) ⟨504437, by rfl⟩ : syracuseStep 672583 = 1008875) B1008875
theorem B673505 : Blo 263822 673505 := bstep (se 2 (by rfl) ⟨252564, by rfl⟩ : syracuseStep 673505 = 505129) B505129
theorem B1690793 : Blo 263822 1690793 := bstep (se 2 (by rfl) ⟨634047, by rfl⟩ : syracuseStep 1690793 = 1268095) B1268095
theorem B445675 : Blo 263822 445675 := bstep (se 1 (by rfl) ⟨334256, by rfl⟩ : syracuseStep 445675 = 668513) B668513
theorem B281927 : Blo 263822 281927 := bstep (se 1 (by rfl) ⟨211445, by rfl⟩ : syracuseStep 281927 = 422891) B422891
theorem B1133945 : Blo 263822 1133945 := bstep (se 2 (by rfl) ⟨425229, by rfl⟩ : syracuseStep 1133945 = 850459) B850459
theorem B3427919 : Blo 263822 3427919 := bstep (se 1 (by rfl) ⟨2570939, by rfl⟩ : syracuseStep 3427919 = 5141879) B5141879
theorem B446377 : Blo 263822 446377 := bstep (se 2 (by rfl) ⟨167391, by rfl⟩ : syracuseStep 446377 = 334783) B334783
theorem B675823 : Blo 263822 675823 := bstep (se 1 (by rfl) ⟨506867, by rfl⟩ : syracuseStep 675823 = 1013735) B1013735
theorem B1004683 : Blo 263822 1004683 := bstep (se 1 (by rfl) ⟨753512, by rfl⟩ : syracuseStep 1004683 = 1507025) B1507025
theorem B1627303 : Blo 263822 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B448031 : Blo 263822 448031 := bstep (se 1 (by rfl) ⟨336023, by rfl⟩ : syracuseStep 448031 = 672047) B672047
theorem B1922615 : Blo 263822 1922615 := bstep (se 1 (by rfl) ⟨1441961, by rfl⟩ : syracuseStep 1922615 = 2883923) B2883923
theorem B4282283 : Blo 263822 4282283 := bstep (se 1 (by rfl) ⟨3211712, by rfl⟩ : syracuseStep 4282283 = 6423425) B6423425
theorem B1727165 : Blo 263822 1727165 := bstep (se 3 (by rfl) ⟨323843, by rfl⟩ : syracuseStep 1727165 = 647687) B647687
theorem B14474159 : Blo 263822 14474159 := bstep (se 1 (by rfl) ⟨10855619, by rfl⟩ : syracuseStep 14474159 = 21711239) B21711239
theorem B451183 : Blo 263822 451183 := bstep (se 1 (by rfl) ⟨338387, by rfl⟩ : syracuseStep 451183 = 676775) B676775
theorem B451919 : Blo 263822 451919 := bstep (se 1 (by rfl) ⟨338939, by rfl⟩ : syracuseStep 451919 = 677879) B677879
theorem B1926679 : Blo 263822 1926679 := bstep (se 1 (by rfl) ⟨1445009, by rfl⟩ : syracuseStep 1926679 = 2890019) B2890019
theorem B1140419 : Blo 263822 1140419 := bstep (se 1 (by rfl) ⟨855314, by rfl⟩ : syracuseStep 1140419 = 1710629) B1710629
theorem B1009529 : Blo 263822 1009529 := bstep (se 2 (by rfl) ⟨378573, by rfl⟩ : syracuseStep 1009529 = 757147) B757147
theorem B3041387 : Blo 263822 3041387 := bstep (se 1 (by rfl) ⟨2281040, by rfl⟩ : syracuseStep 3041387 = 4562081) B4562081
theorem B2747567 : Blo 263822 2747567 := bstep (se 1 (by rfl) ⟨2060675, by rfl⟩ : syracuseStep 2747567 = 4121351) B4121351
theorem B2584009 : Blo 263822 2584009 := bstep (se 2 (by rfl) ⟨969003, by rfl⟩ : syracuseStep 2584009 = 1938007) B1938007
theorem B1208297 : Blo 263822 1208297 := bstep (se 2 (by rfl) ⟨453111, by rfl⟩ : syracuseStep 1208297 = 906223) B906223
theorem B1699967 : Blo 263822 1699967 := bstep (se 1 (by rfl) ⟨1274975, by rfl⟩ : syracuseStep 1699967 = 2549951) B2549951
theorem B1437851 : Blo 263822 1437851 := bstep (se 1 (by rfl) ⟨1078388, by rfl⟩ : syracuseStep 1437851 = 2156777) B2156777
theorem B651487 : Blo 263822 651487 := bstep (se 1 (by rfl) ⟨488615, by rfl⟩ : syracuseStep 651487 = 977231) B977231
theorem B1012763 : Blo 263822 1012763 := bstep (se 1 (by rfl) ⟨759572, by rfl⟩ : syracuseStep 1012763 = 1519145) B1519145
theorem B1439495 : Blo 263822 1439495 := bstep (se 1 (by rfl) ⟨1079621, by rfl⟩ : syracuseStep 1439495 = 2159243) B2159243
theorem B423967 : Blo 263822 423967 := bstep (se 1 (by rfl) ⟨317975, by rfl⟩ : syracuseStep 423967 = 635951) B635951
theorem B1439927 : Blo 263822 1439927 := bstep (se 1 (by rfl) ⟨1079945, by rfl⟩ : syracuseStep 1439927 = 2159891) B2159891
theorem B1341683 : Blo 263822 1341683 := bstep (se 1 (by rfl) ⟨1006262, by rfl⟩ : syracuseStep 1341683 = 2012525) B2012525
theorem B358879 : Blo 263822 358879 := bstep (se 1 (by rfl) ⟨269159, by rfl⟩ : syracuseStep 358879 = 538319) B538319
theorem B1342007 : Blo 263822 1342007 := bstep (se 1 (by rfl) ⟨1006505, by rfl⟩ : syracuseStep 1342007 = 2013011) B2013011
theorem B10910807 : Blo 263822 10910807 := bstep (se 1 (by rfl) ⟨8183105, by rfl⟩ : syracuseStep 10910807 = 16366211) B16366211
theorem B1015847 : Blo 263822 1015847 := bstep (se 1 (by rfl) ⟨761885, by rfl⟩ : syracuseStep 1015847 = 1523771) B1523771
theorem B6784073 : Blo 263822 6784073 := bstep (se 2 (by rfl) ⟨2544027, by rfl⟩ : syracuseStep 6784073 = 5088055) B5088055
theorem B6489395 : Blo 263822 6489395 := bstep (se 1 (by rfl) ⟨4867046, by rfl⟩ : syracuseStep 6489395 = 9734093) B9734093
theorem B263839 : Blo 263822 263839 := bstep (se 1 (by rfl) ⟨197879, by rfl⟩ : syracuseStep 263839 = 395759) B395759
theorem B264095 : Blo 263822 264095 := bstep (se 1 (by rfl) ⟨198071, by rfl⟩ : syracuseStep 264095 = 396143) B396143
theorem B755963 : Blo 263822 755963 := bstep (se 1 (by rfl) ⟨566972, by rfl⟩ : syracuseStep 755963 = 1133945) B1133945
theorem B264687 : Blo 263822 264687 := bstep (se 1 (by rfl) ⟨198515, by rfl⟩ : syracuseStep 264687 = 397031) B397031
theorem B3214343 : Blo 263822 3214343 := bstep (se 1 (by rfl) ⟨2410757, by rfl⟩ : syracuseStep 3214343 = 4821515) B4821515
theorem B396425 : Blo 263822 396425 := bstep (se 2 (by rfl) ⟨148659, by rfl⟩ : syracuseStep 396425 = 297319) B297319
theorem B396479 : Blo 263822 396479 := bstep (se 1 (by rfl) ⟨297359, by rfl⟩ : syracuseStep 396479 = 594719) B594719
theorem B265455 : Blo 263822 265455 := bstep (se 1 (by rfl) ⟨199091, by rfl⟩ : syracuseStep 265455 = 398183) B398183
theorem B265543 : Blo 263822 265543 := bstep (se 1 (by rfl) ⟨199157, by rfl⟩ : syracuseStep 265543 = 398315) B398315
theorem B3018059 : Blo 263822 3018059 := bstep (se 1 (by rfl) ⟨2263544, by rfl⟩ : syracuseStep 3018059 = 4527089) B4527089
theorem B724307 : Blo 263822 724307 := bstep (se 1 (by rfl) ⟨543230, by rfl⟩ : syracuseStep 724307 = 1086461) B1086461
theorem B298687 : Blo 263822 298687 := bstep (se 1 (by rfl) ⟨224015, by rfl⟩ : syracuseStep 298687 = 448031) B448031
theorem B1281743 : Blo 263822 1281743 := bstep (se 1 (by rfl) ⟨961307, by rfl⟩ : syracuseStep 1281743 = 1922615) B1922615
theorem B266011 : Blo 263822 266011 := bstep (se 1 (by rfl) ⟨199508, by rfl⟩ : syracuseStep 266011 = 399017) B399017
theorem B2854855 : Blo 263822 2854855 := bstep (se 1 (by rfl) ⟨2141141, by rfl⟩ : syracuseStep 2854855 = 4282283) B4282283
theorem B1511399 : Blo 263822 1511399 := bstep (se 1 (by rfl) ⟨1133549, by rfl⟩ : syracuseStep 1511399 = 2267099) B2267099
theorem B266267 : Blo 263822 266267 := bstep (se 1 (by rfl) ⟨199700, by rfl⟩ : syracuseStep 266267 = 399401) B399401
theorem B594143 : Blo 263822 594143 := bstep (se 1 (by rfl) ⟨445607, by rfl⟩ : syracuseStep 594143 = 891215) B891215
theorem B397595 : Blo 263822 397595 := bstep (se 1 (by rfl) ⟨298196, by rfl⟩ : syracuseStep 397595 = 596393) B596393
theorem B10490143 : Blo 263822 10490143 := bstep (se 1 (by rfl) ⟨7867607, by rfl⟩ : syracuseStep 10490143 = 15735215) B15735215
theorem B266543 : Blo 263822 266543 := bstep (se 1 (by rfl) ⟨199907, by rfl⟩ : syracuseStep 266543 = 399815) B399815
theorem B594233 : Blo 263822 594233 := bstep (se 2 (by rfl) ⟨222837, by rfl⟩ : syracuseStep 594233 = 445675) B445675
theorem B1905083 : Blo 263822 1905083 := bstep (se 1 (by rfl) ⟨1428812, by rfl⟩ : syracuseStep 1905083 = 2857625) B2857625
theorem B1151443 : Blo 263822 1151443 := bstep (se 1 (by rfl) ⟨863582, by rfl⟩ : syracuseStep 1151443 = 1727165) B1727165
theorem B3445345 : Blo 263822 3445345 := bstep (se 2 (by rfl) ⟨1292004, by rfl⟩ : syracuseStep 3445345 = 2584009) B2584009
theorem B266863 : Blo 263822 266863 := bstep (se 1 (by rfl) ⟨200147, by rfl⟩ : syracuseStep 266863 = 400295) B400295
theorem B266911 : Blo 263822 266911 := bstep (se 1 (by rfl) ⟨200183, by rfl⟩ : syracuseStep 266911 = 400367) B400367
theorem B267035 : Blo 263822 267035 := bstep (se 1 (by rfl) ⟨200276, by rfl⟩ : syracuseStep 267035 = 400553) B400553
theorem B398135 : Blo 263822 398135 := bstep (se 1 (by rfl) ⟨298601, by rfl⟩ : syracuseStep 398135 = 597203) B597203
theorem B10195793 : Blo 263822 10195793 := bstep (se 2 (by rfl) ⟨3823422, by rfl⟩ : syracuseStep 10195793 = 7646845) B7646845
theorem B1708937 : Blo 263822 1708937 := bstep (se 2 (by rfl) ⟨640851, by rfl⟩ : syracuseStep 1708937 = 1281703) B1281703
theorem B594899 : Blo 263822 594899 := bstep (se 1 (by rfl) ⟨446174, by rfl⟩ : syracuseStep 594899 = 892349) B892349
theorem B595169 : Blo 263822 595169 := bstep (se 2 (by rfl) ⟨223188, by rfl⟩ : syracuseStep 595169 = 446377) B446377
theorem B398843 : Blo 263822 398843 := bstep (se 1 (by rfl) ⟨299132, by rfl⟩ : syracuseStep 398843 = 598265) B598265
theorem B399023 : Blo 263822 399023 := bstep (se 1 (by rfl) ⟨299267, by rfl⟩ : syracuseStep 399023 = 598535) B598535
theorem B1710143 : Blo 263822 1710143 := bstep (se 1 (by rfl) ⟨1282607, by rfl⟩ : syracuseStep 1710143 = 2565215) B2565215
theorem B399467 : Blo 263822 399467 := bstep (se 1 (by rfl) ⟨299600, by rfl⟩ : syracuseStep 399467 = 599201) B599201
theorem B301279 : Blo 263822 301279 := bstep (se 1 (by rfl) ⟨225959, by rfl⟩ : syracuseStep 301279 = 451919) B451919
theorem B760279 : Blo 263822 760279 := bstep (se 1 (by rfl) ⟨570209, by rfl⟩ : syracuseStep 760279 = 1140419) B1140419
theorem B399839 : Blo 263822 399839 := bstep (se 1 (by rfl) ⟨299879, by rfl⟩ : syracuseStep 399839 = 599759) B599759
theorem B399983 : Blo 263822 399983 := bstep (se 1 (by rfl) ⟨299987, by rfl⟩ : syracuseStep 399983 = 599975) B599975
theorem B400175 : Blo 263822 400175 := bstep (se 1 (by rfl) ⟨300131, by rfl⟩ : syracuseStep 400175 = 600263) B600263
theorem B2169737 : Blo 263822 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B400667 : Blo 263822 400667 := bstep (se 1 (by rfl) ⟨300500, by rfl⟩ : syracuseStep 400667 = 601001) B601001
theorem B8134319 : Blo 263822 8134319 := bstep (se 1 (by rfl) ⟨6100739, by rfl⟩ : syracuseStep 8134319 = 12201479) B12201479
theorem B597743 : Blo 263822 597743 := bstep (se 1 (by rfl) ⟨448307, by rfl⟩ : syracuseStep 597743 = 896615) B896615
theorem B401135 : Blo 263822 401135 := bstep (se 1 (by rfl) ⟨300851, by rfl⟩ : syracuseStep 401135 = 601703) B601703
theorem B1712011 : Blo 263822 1712011 := bstep (se 1 (by rfl) ⟨1284008, by rfl⟩ : syracuseStep 1712011 = 2568017) B2568017
theorem B565289 : Blo 263822 565289 := bstep (se 2 (by rfl) ⟨211983, by rfl⟩ : syracuseStep 565289 = 423967) B423967
theorem B20652083 : Blo 263822 20652083 := bstep (se 1 (by rfl) ⟨15489062, by rfl⟩ : syracuseStep 20652083 = 30978125) B30978125
theorem B958567 : Blo 263822 958567 := bstep (se 1 (by rfl) ⟨718925, by rfl⟩ : syracuseStep 958567 = 1437851) B1437851
theorem B893213 : Blo 263822 893213 := bstep (se 3 (by rfl) ⟨167477, by rfl⟩ : syracuseStep 893213 = 334955) B334955
theorem B959663 : Blo 263822 959663 := bstep (se 1 (by rfl) ⟨719747, by rfl⟩ : syracuseStep 959663 = 1439495) B1439495
theorem B959951 : Blo 263822 959951 := bstep (se 1 (by rfl) ⟨719963, by rfl⟩ : syracuseStep 959951 = 1439927) B1439927
theorem B894455 : Blo 263822 894455 := bstep (se 1 (by rfl) ⟨670841, by rfl⟩ : syracuseStep 894455 = 1341683) B1341683
theorem B894671 : Blo 263822 894671 := bstep (se 1 (by rfl) ⟨671003, by rfl⟩ : syracuseStep 894671 = 1342007) B1342007
theorem B3222125 : Blo 263822 3222125 := bstep (se 3 (by rfl) ⟨604148, by rfl⟩ : syracuseStep 3222125 = 1208297) B1208297
theorem B568415 : Blo 263822 568415 := bstep (se 1 (by rfl) ⟨426311, by rfl⟩ : syracuseStep 568415 = 852623) B852623
theorem B4566455 : Blo 263822 4566455 := bstep (se 1 (by rfl) ⟨3424841, by rfl⟩ : syracuseStep 4566455 = 6849683) B6849683
theorem B601577 : Blo 263822 601577 := bstep (se 2 (by rfl) ⟨225591, by rfl⟩ : syracuseStep 601577 = 451183) B451183
theorem B9809515 : Blo 263822 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B896777 : Blo 263822 896777 := bstep (se 2 (by rfl) ⟨336291, by rfl⟩ : syracuseStep 896777 = 672583) B672583
theorem B2568905 : Blo 263822 2568905 := bstep (se 2 (by rfl) ⟨963339, by rfl⟩ : syracuseStep 2568905 = 1926679) B1926679
theorem B1127195 : Blo 263822 1127195 := bstep (se 1 (by rfl) ⟨845396, by rfl⟩ : syracuseStep 1127195 = 1690793) B1690793
theorem B963571 : Blo 263822 963571 := bstep (se 1 (by rfl) ⟨722678, by rfl⟩ : syracuseStep 963571 = 1445357) B1445357
theorem B570415 : Blo 263822 570415 := bstep (se 1 (by rfl) ⟨427811, by rfl⟩ : syracuseStep 570415 = 855623) B855623
theorem B2143739 : Blo 263822 2143739 := bstep (se 1 (by rfl) ⟨1607804, by rfl⟩ : syracuseStep 2143739 = 3215609) B3215609
theorem B898559 : Blo 263822 898559 := bstep (se 1 (by rfl) ⟨673919, by rfl⟩ : syracuseStep 898559 = 1347839) B1347839
theorem B505759 : Blo 263822 505759 := bstep (se 1 (by rfl) ⟨379319, by rfl⟩ : syracuseStep 505759 = 758639) B758639
theorem B899099 : Blo 263822 899099 := bstep (se 1 (by rfl) ⟨674324, by rfl⟩ : syracuseStep 899099 = 1348649) B1348649
theorem B505919 : Blo 263822 505919 := bstep (se 1 (by rfl) ⟨379439, by rfl⟩ : syracuseStep 505919 = 758879) B758879
theorem B899261 : Blo 263822 899261 := bstep (se 3 (by rfl) ⟨168611, by rfl⟩ : syracuseStep 899261 = 337223) B337223
theorem B9649439 : Blo 263822 9649439 := bstep (se 1 (by rfl) ⟨7237079, by rfl⟩ : syracuseStep 9649439 = 14474159) B14474159
theorem B900719 : Blo 263822 900719 := bstep (se 1 (by rfl) ⟨675539, by rfl⟩ : syracuseStep 900719 = 1351079) B1351079
theorem B2014955 : Blo 263822 2014955 := bstep (se 1 (by rfl) ⟨1511216, by rfl⟩ : syracuseStep 2014955 = 3022433) B3022433
theorem B901097 : Blo 263822 901097 := bstep (se 2 (by rfl) ⟨337911, by rfl⟩ : syracuseStep 901097 = 675823) B675823
theorem B868649 : Blo 263822 868649 := bstep (se 2 (by rfl) ⟨325743, by rfl⟩ : syracuseStep 868649 = 651487) B651487
theorem B673019 : Blo 263822 673019 := bstep (se 1 (by rfl) ⟨504764, by rfl⟩ : syracuseStep 673019 = 1009529) B1009529
theorem B902447 : Blo 263822 902447 := bstep (se 1 (by rfl) ⟨676835, by rfl⟩ : syracuseStep 902447 = 1353671) B1353671
theorem B2147795 : Blo 263822 2147795 := bstep (se 1 (by rfl) ⟨1610846, by rfl⟩ : syracuseStep 2147795 = 3221693) B3221693
theorem B640487 : Blo 263822 640487 := bstep (se 1 (by rfl) ⟨480365, by rfl⟩ : syracuseStep 640487 = 960731) B960731
theorem B1820663 : Blo 263822 1820663 := bstep (se 1 (by rfl) ⟨1365497, by rfl⟩ : syracuseStep 1820663 = 2730995) B2730995
theorem B903311 : Blo 263822 903311 := bstep (se 1 (by rfl) ⟨677483, by rfl⟩ : syracuseStep 903311 = 1354967) B1354967
theorem B903419 : Blo 263822 903419 := bstep (se 1 (by rfl) ⟨677564, by rfl⟩ : syracuseStep 903419 = 1355129) B1355129
theorem B1133311 : Blo 263822 1133311 := bstep (se 1 (by rfl) ⟨849983, by rfl⟩ : syracuseStep 1133311 = 1699967) B1699967
theorem B445351 : Blo 263822 445351 := bstep (se 1 (by rfl) ⟨334013, by rfl⟩ : syracuseStep 445351 = 668027) B668027
theorem B7326845 : Blo 263822 7326845 := bstep (se 3 (by rfl) ⟨1373783, by rfl⟩ : syracuseStep 7326845 = 2747567) B2747567
theorem B478505 : Blo 263822 478505 := bstep (se 2 (by rfl) ⟨179439, by rfl⟩ : syracuseStep 478505 = 358879) B358879
theorem B675175 : Blo 263822 675175 := bstep (se 1 (by rfl) ⟨506381, by rfl⟩ : syracuseStep 675175 = 1012763) B1012763
theorem B2018843 : Blo 263822 2018843 := bstep (se 1 (by rfl) ⟨1514132, by rfl⟩ : syracuseStep 2018843 = 3028265) B3028265
theorem B675449 : Blo 263822 675449 := bstep (se 2 (by rfl) ⟨253293, by rfl⟩ : syracuseStep 675449 = 506587) B506587
theorem B2543723 : Blo 263822 2543723 := bstep (se 1 (by rfl) ⟨1907792, by rfl⟩ : syracuseStep 2543723 = 3815585) B3815585
theorem B6510617 : Blo 263822 6510617 := bstep (se 2 (by rfl) ⟨2441481, by rfl⟩ : syracuseStep 6510617 = 4882963) B4882963
theorem B449003 : Blo 263822 449003 := bstep (se 1 (by rfl) ⟨336752, by rfl⟩ : syracuseStep 449003 = 673505) B673505
theorem B2285279 : Blo 263822 2285279 := bstep (se 1 (by rfl) ⟨1713959, by rfl⟩ : syracuseStep 2285279 = 3427919) B3427919
theorem B1007585 : Blo 263822 1007585 := bstep (se 2 (by rfl) ⟨377844, by rfl⟩ : syracuseStep 1007585 = 755689) B755689
theorem B451561 : Blo 263822 451561 := bstep (se 2 (by rfl) ⟨169335, by rfl⟩ : syracuseStep 451561 = 338671) B338671
theorem B1730807 : Blo 263822 1730807 := bstep (se 1 (by rfl) ⟨1298105, by rfl⟩ : syracuseStep 1730807 = 2596211) B2596211
theorem B1010303 : Blo 263822 1010303 := bstep (se 1 (by rfl) ⟨757727, by rfl⟩ : syracuseStep 1010303 = 1515455) B1515455
theorem B2027591 : Blo 263822 2027591 := bstep (se 1 (by rfl) ⟨1520693, by rfl⟩ : syracuseStep 2027591 = 3041387) B3041387
theorem B1339577 : Blo 263822 1339577 := bstep (se 2 (by rfl) ⟨502341, by rfl⟩ : syracuseStep 1339577 = 1004683) B1004683
theorem B751805 : Blo 263822 751805 := bstep (se 3 (by rfl) ⟨140963, by rfl⟩ : syracuseStep 751805 = 281927) B281927
theorem B1342331 : Blo 263822 1342331 := bstep (se 1 (by rfl) ⟨1006748, by rfl⟩ : syracuseStep 1342331 = 2013497) B2013497
theorem B1014889 : Blo 263822 1014889 := bstep (se 2 (by rfl) ⟨380583, by rfl⟩ : syracuseStep 1014889 = 761167) B761167
theorem B7273871 : Blo 263822 7273871 := bstep (se 1 (by rfl) ⟨5455403, by rfl⟩ : syracuseStep 7273871 = 10910807) B10910807
theorem B39353971 : Blo 263822 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B1278089 : Blo 263822 1278089 := bstep (se 2 (by rfl) ⟨479283, by rfl⟩ : syracuseStep 1278089 = 958567) B958567
theorem B4522715 : Blo 263822 4522715 := bstep (se 1 (by rfl) ⟨3392036, by rfl⟩ : syracuseStep 4522715 = 6784073) B6784073
theorem B4326263 : Blo 263822 4326263 := bstep (se 1 (by rfl) ⟨3244697, by rfl⟩ : syracuseStep 4326263 = 6489395) B6489395
theorem B1213775 : Blo 263822 1213775 := bstep (se 1 (by rfl) ⟨910331, by rfl⟩ : syracuseStep 1213775 = 1820663) B1820663
theorem B4884563 : Blo 263822 4884563 := bstep (se 1 (by rfl) ⟨3663422, by rfl⟩ : syracuseStep 4884563 = 7326845) B7326845
theorem B264283 : Blo 263822 264283 := bstep (se 1 (by rfl) ⟨198212, by rfl⟩ : syracuseStep 264283 = 396425) B396425
theorem B264319 : Blo 263822 264319 := bstep (se 1 (by rfl) ⟨198239, by rfl⟩ : syracuseStep 264319 = 396479) B396479
theorem B1345895 : Blo 263822 1345895 := bstep (se 1 (by rfl) ⟨1009421, by rfl⟩ : syracuseStep 1345895 = 2018843) B2018843
theorem B854495 : Blo 263822 854495 := bstep (se 1 (by rfl) ⟨640871, by rfl⟩ : syracuseStep 854495 = 1281743) B1281743
theorem B396095 : Blo 263822 396095 := bstep (se 1 (by rfl) ⟨297071, by rfl⟩ : syracuseStep 396095 = 594143) B594143
theorem B265063 : Blo 263822 265063 := bstep (se 1 (by rfl) ⟨198797, by rfl⟩ : syracuseStep 265063 = 397595) B397595
theorem B396155 : Blo 263822 396155 := bstep (se 1 (by rfl) ⟨297116, by rfl⟩ : syracuseStep 396155 = 594233) B594233
theorem B265423 : Blo 263822 265423 := bstep (se 1 (by rfl) ⟨199067, by rfl⟩ : syracuseStep 265423 = 398135) B398135
theorem B396599 : Blo 263822 396599 := bstep (se 1 (by rfl) ⟨297449, by rfl⟩ : syracuseStep 396599 = 594899) B594899
theorem B396779 : Blo 263822 396779 := bstep (se 1 (by rfl) ⟨297584, by rfl⟩ : syracuseStep 396779 = 595169) B595169
theorem B265895 : Blo 263822 265895 := bstep (se 1 (by rfl) ⟨199421, by rfl⟩ : syracuseStep 265895 = 398843) B398843
theorem B1511081 : Blo 263822 1511081 := bstep (se 2 (by rfl) ⟨566655, by rfl⟩ : syracuseStep 1511081 = 1133311) B1133311
theorem B266015 : Blo 263822 266015 := bstep (se 1 (by rfl) ⟨199511, by rfl⟩ : syracuseStep 266015 = 399023) B399023
theorem B2559869 : Blo 263822 2559869 := bstep (se 3 (by rfl) ⟨479975, by rfl⟩ : syracuseStep 2559869 = 959951) B959951
theorem B593801 : Blo 263822 593801 := bstep (se 2 (by rfl) ⟨222675, by rfl⟩ : syracuseStep 593801 = 445351) B445351
theorem B1707965 : Blo 263822 1707965 := bstep (se 3 (by rfl) ⟨320243, by rfl⟩ : syracuseStep 1707965 = 640487) B640487
theorem B266311 : Blo 263822 266311 := bstep (se 1 (by rfl) ⟨199733, by rfl⟩ : syracuseStep 266311 = 399467) B399467
theorem B266559 : Blo 263822 266559 := bstep (se 1 (by rfl) ⟨199919, by rfl⟩ : syracuseStep 266559 = 399839) B399839
theorem B299335 : Blo 263822 299335 := bstep (se 1 (by rfl) ⟨224501, by rfl⟩ : syracuseStep 299335 = 449003) B449003
theorem B266655 : Blo 263822 266655 := bstep (se 1 (by rfl) ⟨199991, by rfl⟩ : syracuseStep 266655 = 399983) B399983
theorem B266783 : Blo 263822 266783 := bstep (se 1 (by rfl) ⟨200087, by rfl⟩ : syracuseStep 266783 = 400175) B400175
theorem B1446491 : Blo 263822 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B267111 : Blo 263822 267111 := bstep (se 1 (by rfl) ⟨200333, by rfl⟩ : syracuseStep 267111 = 400667) B400667
theorem B398249 : Blo 263822 398249 := bstep (se 2 (by rfl) ⟨149343, by rfl⟩ : syracuseStep 398249 = 298687) B298687
theorem B398495 : Blo 263822 398495 := bstep (se 1 (by rfl) ⟨298871, by rfl⟩ : syracuseStep 398495 = 597743) B597743
theorem B267423 : Blo 263822 267423 := bstep (se 1 (by rfl) ⟨200567, by rfl⟩ : syracuseStep 267423 = 401135) B401135
theorem B3806473 : Blo 263822 3806473 := bstep (se 2 (by rfl) ⟨1427427, by rfl⟩ : syracuseStep 3806473 = 2854855) B2854855
theorem B13768055 : Blo 263822 13768055 := bstep (se 1 (by rfl) ⟨10326041, by rfl⟩ : syracuseStep 13768055 = 20652083) B20652083
theorem B595475 : Blo 263822 595475 := bstep (se 1 (by rfl) ⟨446606, by rfl⟩ : syracuseStep 595475 = 893213) B893213
theorem B4593793 : Blo 263822 4593793 := bstep (se 2 (by rfl) ⟨1722672, by rfl⟩ : syracuseStep 4593793 = 3445345) B3445345
theorem B596303 : Blo 263822 596303 := bstep (se 1 (by rfl) ⟨447227, by rfl⟩ : syracuseStep 596303 = 894455) B894455
theorem B596447 : Blo 263822 596447 := bstep (se 1 (by rfl) ⟨447335, by rfl⟩ : syracuseStep 596447 = 894671) B894671
theorem B1284761 : Blo 263822 1284761 := bstep (se 2 (by rfl) ⟨481785, by rfl⟩ : syracuseStep 1284761 = 963571) B963571
theorem B760553 : Blo 263822 760553 := bstep (se 2 (by rfl) ⟨285207, by rfl⟩ : syracuseStep 760553 = 570415) B570415
theorem B1153871 : Blo 263822 1153871 := bstep (se 1 (by rfl) ⟨865403, by rfl⟩ : syracuseStep 1153871 = 1730807) B1730807
theorem B401051 : Blo 263822 401051 := bstep (se 1 (by rfl) ⟨300788, by rfl⟩ : syracuseStep 401051 = 601577) B601577
theorem B597851 : Blo 263822 597851 := bstep (se 1 (by rfl) ⟨448388, by rfl⟩ : syracuseStep 597851 = 896777) B896777
theorem B1351727 : Blo 263822 1351727 := bstep (se 1 (by rfl) ⟨1013795, by rfl⟩ : syracuseStep 1351727 = 2027591) B2027591
theorem B893051 : Blo 263822 893051 := bstep (se 1 (by rfl) ⟨669788, by rfl⟩ : syracuseStep 893051 = 1339577) B1339577
theorem B1515773 : Blo 263822 1515773 := bstep (se 3 (by rfl) ⟨284207, by rfl⟩ : syracuseStep 1515773 = 568415) B568415
theorem B401705 : Blo 263822 401705 := bstep (se 2 (by rfl) ⟨150639, by rfl⟩ : syracuseStep 401705 = 301279) B301279
theorem B1712603 : Blo 263822 1712603 := bstep (se 1 (by rfl) ⟨1284452, by rfl⟩ : syracuseStep 1712603 = 2568905) B2568905
theorem B599039 : Blo 263822 599039 := bstep (se 1 (by rfl) ⟨449279, by rfl⟩ : syracuseStep 599039 = 898559) B898559
theorem B599399 : Blo 263822 599399 := bstep (se 1 (by rfl) ⟨449549, by rfl⟩ : syracuseStep 599399 = 899099) B899099
theorem B337279 : Blo 263822 337279 := bstep (se 1 (by rfl) ⟨252959, by rfl⟩ : syracuseStep 337279 = 505919) B505919
theorem B501203 : Blo 263822 501203 := bstep (se 1 (by rfl) ⟨375902, by rfl⟩ : syracuseStep 501203 = 751805) B751805
theorem B599507 : Blo 263822 599507 := bstep (se 1 (by rfl) ⟨449630, by rfl⟩ : syracuseStep 599507 = 899261) B899261
theorem B1353185 : Blo 263822 1353185 := bstep (se 2 (by rfl) ⟨507444, by rfl⟩ : syracuseStep 1353185 = 1014889) B1014889
theorem B894887 : Blo 263822 894887 := bstep (se 1 (by rfl) ⟨671165, by rfl⟩ : syracuseStep 894887 = 1342331) B1342331
theorem B52471961 : Blo 263822 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B6432959 : Blo 263822 6432959 := bstep (se 1 (by rfl) ⟨4824719, by rfl⟩ : syracuseStep 6432959 = 9649439) B9649439
theorem B600479 : Blo 263822 600479 := bstep (se 1 (by rfl) ⟨450359, by rfl⟩ : syracuseStep 600479 = 900719) B900719
theorem B600731 : Blo 263822 600731 := bstep (se 1 (by rfl) ⟨450548, by rfl⟩ : syracuseStep 600731 = 901097) B901097
theorem B601631 : Blo 263822 601631 := bstep (se 1 (by rfl) ⟨451223, by rfl⟩ : syracuseStep 601631 = 902447) B902447
theorem B602081 : Blo 263822 602081 := bstep (se 2 (by rfl) ⟨225780, by rfl⟩ : syracuseStep 602081 = 451561) B451561
theorem B602207 : Blo 263822 602207 := bstep (se 1 (by rfl) ⟨451655, by rfl⟩ : syracuseStep 602207 = 903311) B903311
theorem B503975 : Blo 263822 503975 := bstep (se 1 (by rfl) ⟨377981, by rfl⟩ : syracuseStep 503975 = 755963) B755963
theorem B602279 : Blo 263822 602279 := bstep (se 1 (by rfl) ⟨451709, by rfl⟩ : syracuseStep 602279 = 903419) B903419
theorem B2142895 : Blo 263822 2142895 := bstep (se 1 (by rfl) ⟨1607171, by rfl⟩ : syracuseStep 2142895 = 3214343) B3214343
theorem B2012039 : Blo 263822 2012039 := bstep (se 1 (by rfl) ⟨1509029, by rfl⟩ : syracuseStep 2012039 = 3018059) B3018059
theorem B6797195 : Blo 263822 6797195 := bstep (se 1 (by rfl) ⟨5097896, by rfl⟩ : syracuseStep 6797195 = 10195793) B10195793
theorem B4340411 : Blo 263822 4340411 := bstep (se 1 (by rfl) ⟨3255308, by rfl⟩ : syracuseStep 4340411 = 6510617) B6510617
theorem B900233 : Blo 263822 900233 := bstep (se 2 (by rfl) ⟨337587, by rfl⟩ : syracuseStep 900233 = 675175) B675175
theorem B5422879 : Blo 263822 5422879 := bstep (se 1 (by rfl) ⟨4067159, by rfl⟩ : syracuseStep 5422879 = 8134319) B8134319
theorem B1523519 : Blo 263822 1523519 := bstep (se 1 (by rfl) ⟨1142639, by rfl⟩ : syracuseStep 1523519 = 2285279) B2285279
theorem B671723 : Blo 263822 671723 := bstep (se 1 (by rfl) ⟨503792, by rfl⟩ : syracuseStep 671723 = 1007585) B1007585
theorem B376859 : Blo 263822 376859 := bstep (se 1 (by rfl) ⟨282644, by rfl⟩ : syracuseStep 376859 = 565289) B565289
theorem B639775 : Blo 263822 639775 := bstep (se 1 (by rfl) ⟨479831, by rfl⟩ : syracuseStep 639775 = 959663) B959663
theorem B2148083 : Blo 263822 2148083 := bstep (se 1 (by rfl) ⟨1611062, by rfl⟩ : syracuseStep 2148083 = 3222125) B3222125
theorem B673535 : Blo 263822 673535 := bstep (se 1 (by rfl) ⟨505151, by rfl⟩ : syracuseStep 673535 = 1010303) B1010303
theorem B674345 : Blo 263822 674345 := bstep (se 2 (by rfl) ⟨252879, by rfl⟩ : syracuseStep 674345 = 505759) B505759
theorem B52317413 : Blo 263822 52317413 := bstep (se 4 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 52317413 = 9809515) B9809515
theorem B1429159 : Blo 263822 1429159 := bstep (se 1 (by rfl) ⟨1071869, by rfl⟩ : syracuseStep 1429159 = 2143739) B2143739
theorem B2282681 : Blo 263822 2282681 := bstep (se 2 (by rfl) ⟨856005, by rfl⟩ : syracuseStep 2282681 = 1712011) B1712011
theorem B677231 : Blo 263822 677231 := bstep (se 1 (by rfl) ⟨507923, by rfl⟩ : syracuseStep 677231 = 1015847) B1015847
theorem B448679 : Blo 263822 448679 := bstep (se 1 (by rfl) ⟨336509, by rfl⟩ : syracuseStep 448679 = 673019) B673019
theorem B1431863 : Blo 263822 1431863 := bstep (se 1 (by rfl) ⟨1073897, by rfl⟩ : syracuseStep 1431863 = 2147795) B2147795
theorem B450299 : Blo 263822 450299 := bstep (se 1 (by rfl) ⟨337724, by rfl⟩ : syracuseStep 450299 = 675449) B675449
theorem B1007599 : Blo 263822 1007599 := bstep (se 1 (by rfl) ⟨755699, by rfl⟩ : syracuseStep 1007599 = 1511399) B1511399
theorem B1695815 : Blo 263822 1695815 := bstep (se 1 (by rfl) ⟨1271861, by rfl⟩ : syracuseStep 1695815 = 2543723) B2543723
theorem B1270055 : Blo 263822 1270055 := bstep (se 1 (by rfl) ⟨952541, by rfl⟩ : syracuseStep 1270055 = 1905083) B1905083
theorem B9265589 : Blo 263822 9265589 := bstep (se 5 (by rfl) ⟨434324, by rfl⟩ : syracuseStep 9265589 = 868649) B868649
theorem B1139291 : Blo 263822 1139291 := bstep (se 1 (by rfl) ⟨854468, by rfl⟩ : syracuseStep 1139291 = 1708937) B1708937
theorem B7725941 : Blo 263822 7725941 := bstep (se 5 (by rfl) ⟨362153, by rfl⟩ : syracuseStep 7725941 = 724307) B724307
theorem B1140095 : Blo 263822 1140095 := bstep (se 1 (by rfl) ⟨855071, by rfl⟩ : syracuseStep 1140095 = 1710143) B1710143
theorem B13986857 : Blo 263822 13986857 := bstep (se 2 (by rfl) ⟨5245071, by rfl⟩ : syracuseStep 13986857 = 10490143) B10490143
theorem B1535257 : Blo 263822 1535257 := bstep (se 2 (by rfl) ⟨575721, by rfl⟩ : syracuseStep 1535257 = 1151443) B1151443
theorem B3044303 : Blo 263822 3044303 := bstep (se 1 (by rfl) ⟨2283227, by rfl⟩ : syracuseStep 3044303 = 4566455) B4566455
theorem B751463 : Blo 263822 751463 := bstep (se 1 (by rfl) ⟨563597, by rfl⟩ : syracuseStep 751463 = 1127195) B1127195
theorem B1013705 : Blo 263822 1013705 := bstep (se 2 (by rfl) ⟨380139, by rfl⟩ : syracuseStep 1013705 = 760279) B760279
theorem B1276013 : Blo 263822 1276013 := bstep (se 3 (by rfl) ⟨239252, by rfl⟩ : syracuseStep 1276013 = 478505) B478505
theorem B4849247 : Blo 263822 4849247 := bstep (se 1 (by rfl) ⟨3636935, by rfl⟩ : syracuseStep 4849247 = 7273871) B7273871
theorem B1343303 : Blo 263822 1343303 := bstep (se 1 (by rfl) ⟨1007477, by rfl⟩ : syracuseStep 1343303 = 2014955) B2014955
theorem B852059 : Blo 263822 852059 := bstep (se 1 (by rfl) ⟨639044, by rfl⟩ : syracuseStep 852059 = 1278089) B1278089
theorem B3015143 : Blo 263822 3015143 := bstep (se 1 (by rfl) ⟨2261357, by rfl⟩ : syracuseStep 3015143 = 4522715) B4522715
theorem B2884175 : Blo 263822 2884175 := bstep (se 1 (by rfl) ⟨2163131, by rfl⟩ : syracuseStep 2884175 = 4326263) B4326263
theorem B853033 : Blo 263822 853033 := bstep (se 2 (by rfl) ⟨319887, by rfl⟩ : syracuseStep 853033 = 639775) B639775
theorem B264063 : Blo 263822 264063 := bstep (se 1 (by rfl) ⟨198047, by rfl⟩ : syracuseStep 264063 = 396095) B396095
theorem B264103 : Blo 263822 264103 := bstep (se 1 (by rfl) ⟨198077, by rfl⟩ : syracuseStep 264103 = 396155) B396155
theorem B264399 : Blo 263822 264399 := bstep (se 1 (by rfl) ⟨198299, by rfl⟩ : syracuseStep 264399 = 396599) B396599
theorem B264519 : Blo 263822 264519 := bstep (se 1 (by rfl) ⟨198389, by rfl⟩ : syracuseStep 264519 = 396779) B396779
theorem B1706579 : Blo 263822 1706579 := bstep (se 1 (by rfl) ⟨1279934, by rfl⟩ : syracuseStep 1706579 = 2559869) B2559869
theorem B395867 : Blo 263822 395867 := bstep (se 1 (by rfl) ⟨296900, by rfl⟩ : syracuseStep 395867 = 593801) B593801
theorem B265499 : Blo 263822 265499 := bstep (se 1 (by rfl) ⟨199124, by rfl⟩ : syracuseStep 265499 = 398249) B398249
theorem B265663 : Blo 263822 265663 := bstep (se 1 (by rfl) ⟨199247, by rfl⟩ : syracuseStep 265663 = 398495) B398495
theorem B9178703 : Blo 263822 9178703 := bstep (se 1 (by rfl) ⟨6884027, by rfl⟩ : syracuseStep 9178703 = 13768055) B13768055
theorem B396983 : Blo 263822 396983 := bstep (se 1 (by rfl) ⟨297737, by rfl⟩ : syracuseStep 396983 = 595475) B595475
theorem B299119 : Blo 263822 299119 := bstep (se 1 (by rfl) ⟨224339, by rfl⟩ : syracuseStep 299119 = 448679) B448679
theorem B954575 : Blo 263822 954575 := bstep (se 1 (by rfl) ⟨715931, by rfl⟩ : syracuseStep 954575 = 1431863) B1431863
theorem B397535 : Blo 263822 397535 := bstep (se 1 (by rfl) ⟨298151, by rfl⟩ : syracuseStep 397535 = 596303) B596303
theorem B397631 : Blo 263822 397631 := bstep (se 1 (by rfl) ⟨298223, by rfl⟩ : syracuseStep 397631 = 596447) B596447
theorem B856507 : Blo 263822 856507 := bstep (se 1 (by rfl) ⟨642380, by rfl⟩ : syracuseStep 856507 = 1284761) B1284761
theorem B1905545 : Blo 263822 1905545 := bstep (se 2 (by rfl) ⟨714579, by rfl⟩ : syracuseStep 1905545 = 1429159) B1429159
theorem B267367 : Blo 263822 267367 := bstep (se 1 (by rfl) ⟨200525, by rfl⟩ : syracuseStep 267367 = 401051) B401051
theorem B300199 : Blo 263822 300199 := bstep (se 1 (by rfl) ⟨225149, by rfl⟩ : syracuseStep 300199 = 450299) B450299
theorem B398567 : Blo 263822 398567 := bstep (se 1 (by rfl) ⟨298925, by rfl⟩ : syracuseStep 398567 = 597851) B597851
theorem B595367 : Blo 263822 595367 := bstep (se 1 (by rfl) ⟨446525, by rfl⟩ : syracuseStep 595367 = 893051) B893051
theorem B267803 : Blo 263822 267803 := bstep (se 1 (by rfl) ⟨200852, by rfl⟩ : syracuseStep 267803 = 401705) B401705
theorem B759527 : Blo 263822 759527 := bstep (se 1 (by rfl) ⟨569645, by rfl⟩ : syracuseStep 759527 = 1139291) B1139291
theorem B399113 : Blo 263822 399113 := bstep (se 2 (by rfl) ⟨149667, by rfl⟩ : syracuseStep 399113 = 299335) B299335
theorem B5150627 : Blo 263822 5150627 := bstep (se 1 (by rfl) ⟨3862970, by rfl⟩ : syracuseStep 5150627 = 7725941) B7725941
theorem B399359 : Blo 263822 399359 := bstep (se 1 (by rfl) ⟨299519, by rfl⟩ : syracuseStep 399359 = 599039) B599039
theorem B2857193 : Blo 263822 2857193 := bstep (se 2 (by rfl) ⟨1071447, by rfl⟩ : syracuseStep 2857193 = 2142895) B2142895
theorem B399599 : Blo 263822 399599 := bstep (se 1 (by rfl) ⟨299699, by rfl⟩ : syracuseStep 399599 = 599399) B599399
theorem B760063 : Blo 263822 760063 := bstep (se 1 (by rfl) ⟨570047, by rfl⟩ : syracuseStep 760063 = 1140095) B1140095
theorem B334135 : Blo 263822 334135 := bstep (se 1 (by rfl) ⟨250601, by rfl⟩ : syracuseStep 334135 = 501203) B501203
theorem B399671 : Blo 263822 399671 := bstep (se 1 (by rfl) ⟨299753, by rfl⟩ : syracuseStep 399671 = 599507) B599507
theorem B596591 : Blo 263822 596591 := bstep (se 1 (by rfl) ⟨447443, by rfl⟩ : syracuseStep 596591 = 894887) B894887
theorem B400319 : Blo 263822 400319 := bstep (se 1 (by rfl) ⟨300239, by rfl⟩ : syracuseStep 400319 = 600479) B600479
theorem B400487 : Blo 263822 400487 := bstep (se 1 (by rfl) ⟨300365, by rfl⟩ : syracuseStep 400487 = 600731) B600731
theorem B401087 : Blo 263822 401087 := bstep (se 1 (by rfl) ⟨300815, by rfl⟩ : syracuseStep 401087 = 601631) B601631
theorem B401387 : Blo 263822 401387 := bstep (se 1 (by rfl) ⟨301040, by rfl⟩ : syracuseStep 401387 = 602081) B602081
theorem B401471 : Blo 263822 401471 := bstep (se 1 (by rfl) ⟨301103, by rfl⟩ : syracuseStep 401471 = 602207) B602207
theorem B335983 : Blo 263822 335983 := bstep (se 1 (by rfl) ⟨251987, by rfl⟩ : syracuseStep 335983 = 503975) B503975
theorem B401519 : Blo 263822 401519 := bstep (se 1 (by rfl) ⟨301139, by rfl⟩ : syracuseStep 401519 = 602279) B602279
theorem B500975 : Blo 263822 500975 := bstep (se 1 (by rfl) ⟨375731, by rfl⟩ : syracuseStep 500975 = 751463) B751463
theorem B4531463 : Blo 263822 4531463 := bstep (se 1 (by rfl) ⟨3398597, by rfl⟩ : syracuseStep 4531463 = 6797195) B6797195
theorem B2893607 : Blo 263822 2893607 := bstep (se 1 (by rfl) ⟨2170205, by rfl⟩ : syracuseStep 2893607 = 4340411) B4340411
theorem B600155 : Blo 263822 600155 := bstep (se 1 (by rfl) ⟨450116, by rfl⟩ : syracuseStep 600155 = 900233) B900233
theorem B895535 : Blo 263822 895535 := bstep (se 1 (by rfl) ⟨671651, by rfl⟩ : syracuseStep 895535 = 1343303) B1343303
theorem B3256375 : Blo 263822 3256375 := bstep (se 1 (by rfl) ⟨2442281, by rfl⟩ : syracuseStep 3256375 = 4884563) B4884563
theorem B897263 : Blo 263822 897263 := bstep (se 1 (by rfl) ⟨672947, by rfl⟩ : syracuseStep 897263 = 1345895) B1345895
theorem B569663 : Blo 263822 569663 := bstep (se 1 (by rfl) ⟨427247, by rfl⟩ : syracuseStep 569663 = 854495) B854495
theorem B34878275 : Blo 263822 34878275 := bstep (se 1 (by rfl) ⟨26158706, by rfl⟩ : syracuseStep 34878275 = 52317413) B52317413
theorem B964327 : Blo 263822 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B1521787 : Blo 263822 1521787 := bstep (se 1 (by rfl) ⟨1141340, by rfl⟩ : syracuseStep 1521787 = 2282681) B2282681
theorem B507035 : Blo 263822 507035 := bstep (se 1 (by rfl) ⟨380276, by rfl⟩ : syracuseStep 507035 = 760553) B760553
theorem B769247 : Blo 263822 769247 := bstep (se 1 (by rfl) ⟨576935, by rfl⟩ : syracuseStep 769247 = 1153871) B1153871
theorem B901151 : Blo 263822 901151 := bstep (se 1 (by rfl) ⟨675863, by rfl⟩ : syracuseStep 901151 = 1351727) B1351727
theorem B1130543 : Blo 263822 1130543 := bstep (se 1 (by rfl) ⟨847907, by rfl⟩ : syracuseStep 1130543 = 1695815) B1695815
theorem B6177059 : Blo 263822 6177059 := bstep (se 1 (by rfl) ⟨4632794, by rfl⟩ : syracuseStep 6177059 = 9265589) B9265589
theorem B902123 : Blo 263822 902123 := bstep (se 1 (by rfl) ⟨676592, by rfl⟩ : syracuseStep 902123 = 1353185) B1353185
theorem B34981307 : Blo 263822 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B9324571 : Blo 263822 9324571 := bstep (se 1 (by rfl) ⟨6993428, by rfl⟩ : syracuseStep 9324571 = 13986857) B13986857
theorem B675803 : Blo 263822 675803 := bstep (se 1 (by rfl) ⟨506852, by rfl⟩ : syracuseStep 675803 = 1013705) B1013705
theorem B7230505 : Blo 263822 7230505 := bstep (se 2 (by rfl) ⟨2711439, by rfl⟩ : syracuseStep 7230505 = 5422879) B5422879
theorem B3232831 : Blo 263822 3232831 := bstep (se 1 (by rfl) ⟨2424623, by rfl⟩ : syracuseStep 3232831 = 4849247) B4849247
theorem B447815 : Blo 263822 447815 := bstep (se 1 (by rfl) ⟨335861, by rfl⟩ : syracuseStep 447815 = 671723) B671723
theorem B1004957 : Blo 263822 1004957 := bstep (se 3 (by rfl) ⟨188429, by rfl⟩ : syracuseStep 1004957 = 376859) B376859
theorem B809183 : Blo 263822 809183 := bstep (se 1 (by rfl) ⟨606887, by rfl⟩ : syracuseStep 809183 = 1213775) B1213775
theorem B1432055 : Blo 263822 1432055 := bstep (se 1 (by rfl) ⟨1074041, by rfl⟩ : syracuseStep 1432055 = 2148083) B2148083
theorem B449023 : Blo 263822 449023 := bstep (se 1 (by rfl) ⟨336767, by rfl⟩ : syracuseStep 449023 = 673535) B673535
theorem B449563 : Blo 263822 449563 := bstep (se 1 (by rfl) ⟨337172, by rfl⟩ : syracuseStep 449563 = 674345) B674345
theorem B449705 : Blo 263822 449705 := bstep (se 2 (by rfl) ⟨168639, by rfl⟩ : syracuseStep 449705 = 337279) B337279
theorem B1007387 : Blo 263822 1007387 := bstep (se 1 (by rfl) ⟨755540, by rfl⟩ : syracuseStep 1007387 = 1511081) B1511081
theorem B1138643 : Blo 263822 1138643 := bstep (se 1 (by rfl) ⟨853982, by rfl⟩ : syracuseStep 1138643 = 1707965) B1707965
theorem B451487 : Blo 263822 451487 := bstep (se 1 (by rfl) ⟨338615, by rfl⟩ : syracuseStep 451487 = 677231) B677231
theorem B1010515 : Blo 263822 1010515 := bstep (se 1 (by rfl) ⟨757886, by rfl⟩ : syracuseStep 1010515 = 1515773) B1515773
theorem B846703 : Blo 263822 846703 := bstep (se 1 (by rfl) ⟨635027, by rfl⟩ : syracuseStep 846703 = 1270055) B1270055
theorem B1141735 : Blo 263822 1141735 := bstep (se 1 (by rfl) ⟨856301, by rfl⟩ : syracuseStep 1141735 = 1712603) B1712603
theorem B4288639 : Blo 263822 4288639 := bstep (se 1 (by rfl) ⟨3216479, by rfl⟩ : syracuseStep 4288639 = 6432959) B6432959
theorem B8188037 : Blo 263822 8188037 := bstep (se 4 (by rfl) ⟨767628, by rfl⟩ : syracuseStep 8188037 = 1535257) B1535257
theorem B5075297 : Blo 263822 5075297 := bstep (se 2 (by rfl) ⟨1903236, by rfl⟩ : syracuseStep 5075297 = 3806473) B3806473
theorem B6125057 : Blo 263822 6125057 := bstep (se 2 (by rfl) ⟨2296896, by rfl⟩ : syracuseStep 6125057 = 4593793) B4593793
theorem B1341359 : Blo 263822 1341359 := bstep (se 1 (by rfl) ⟨1006019, by rfl⟩ : syracuseStep 1341359 = 2012039) B2012039
theorem B2029535 : Blo 263822 2029535 := bstep (se 1 (by rfl) ⟨1522151, by rfl⟩ : syracuseStep 2029535 = 3044303) B3044303
theorem B850675 : Blo 263822 850675 := bstep (se 1 (by rfl) ⟨638006, by rfl⟩ : syracuseStep 850675 = 1276013) B1276013
theorem B1015679 : Blo 263822 1015679 := bstep (se 1 (by rfl) ⟨761759, by rfl⟩ : syracuseStep 1015679 = 1523519) B1523519
theorem B1343465 : Blo 263822 1343465 := bstep (se 2 (by rfl) ⟨503799, by rfl⟩ : syracuseStep 1343465 = 1007599) B1007599
theorem B753695 : Blo 263822 753695 := bstep (se 1 (by rfl) ⟨565271, by rfl⟩ : syracuseStep 753695 = 1130543) B1130543
theorem B263911 : Blo 263822 263911 := bstep (se 1 (by rfl) ⟨197933, by rfl⟩ : syracuseStep 263911 = 395867) B395867
theorem B264655 : Blo 263822 264655 := bstep (se 1 (by rfl) ⟨198491, by rfl⟩ : syracuseStep 264655 = 396983) B396983
theorem B265023 : Blo 263822 265023 := bstep (se 1 (by rfl) ⟨198767, by rfl⟩ : syracuseStep 265023 = 397535) B397535
theorem B265087 : Blo 263822 265087 := bstep (se 1 (by rfl) ⟨198815, by rfl⟩ : syracuseStep 265087 = 397631) B397631
theorem B265711 : Blo 263822 265711 := bstep (se 1 (by rfl) ⟨199283, by rfl⟩ : syracuseStep 265711 = 398567) B398567
theorem B298543 : Blo 263822 298543 := bstep (se 1 (by rfl) ⟨223907, by rfl⟩ : syracuseStep 298543 = 447815) B447815
theorem B396911 : Blo 263822 396911 := bstep (se 1 (by rfl) ⟨297683, by rfl⟩ : syracuseStep 396911 = 595367) B595367
theorem B1347353 : Blo 263822 1347353 := bstep (se 2 (by rfl) ⟨505257, by rfl⟩ : syracuseStep 1347353 = 1010515) B1010515
theorem B266075 : Blo 263822 266075 := bstep (se 1 (by rfl) ⟨199556, by rfl⟩ : syracuseStep 266075 = 399113) B399113
theorem B266239 : Blo 263822 266239 := bstep (se 1 (by rfl) ⟨199679, by rfl⟩ : syracuseStep 266239 = 399359) B399359
theorem B1904795 : Blo 263822 1904795 := bstep (se 1 (by rfl) ⟨1428596, by rfl⟩ : syracuseStep 1904795 = 2857193) B2857193
theorem B266399 : Blo 263822 266399 := bstep (se 1 (by rfl) ⟨199799, by rfl⟩ : syracuseStep 266399 = 399599) B399599
theorem B266447 : Blo 263822 266447 := bstep (se 1 (by rfl) ⟨199835, by rfl⟩ : syracuseStep 266447 = 399671) B399671
theorem B954703 : Blo 263822 954703 := bstep (se 1 (by rfl) ⟨716027, by rfl⟩ : syracuseStep 954703 = 1432055) B1432055
theorem B397727 : Blo 263822 397727 := bstep (se 1 (by rfl) ⟨298295, by rfl⟩ : syracuseStep 397727 = 596591) B596591
theorem B266879 : Blo 263822 266879 := bstep (se 1 (by rfl) ⟨200159, by rfl⟩ : syracuseStep 266879 = 400319) B400319
theorem B266991 : Blo 263822 266991 := bstep (se 1 (by rfl) ⟨200243, by rfl⟩ : syracuseStep 266991 = 400487) B400487
theorem B299803 : Blo 263822 299803 := bstep (se 1 (by rfl) ⟨224852, by rfl⟩ : syracuseStep 299803 = 449705) B449705
theorem B267391 : Blo 263822 267391 := bstep (se 1 (by rfl) ⟨200543, by rfl⟩ : syracuseStep 267391 = 401087) B401087
theorem B759095 : Blo 263822 759095 := bstep (se 1 (by rfl) ⟨569321, by rfl⟩ : syracuseStep 759095 = 1138643) B1138643
theorem B267591 : Blo 263822 267591 := bstep (se 1 (by rfl) ⟨200693, by rfl⟩ : syracuseStep 267591 = 401387) B401387
theorem B267647 : Blo 263822 267647 := bstep (se 1 (by rfl) ⟨200735, by rfl⟩ : syracuseStep 267647 = 401471) B401471
theorem B267679 : Blo 263822 267679 := bstep (se 1 (by rfl) ⟨200759, by rfl⟩ : syracuseStep 267679 = 401519) B401519
theorem B398825 : Blo 263822 398825 := bstep (se 2 (by rfl) ⟨149559, by rfl⟩ : syracuseStep 398825 = 299119) B299119
theorem B300991 : Blo 263822 300991 := bstep (se 1 (by rfl) ⟨225743, by rfl⟩ : syracuseStep 300991 = 451487) B451487
theorem B333983 : Blo 263822 333983 := bstep (se 1 (by rfl) ⟨250487, by rfl⟩ : syracuseStep 333983 = 500975) B500975
theorem B3020975 : Blo 263822 3020975 := bstep (se 1 (by rfl) ⟨2265731, by rfl⟩ : syracuseStep 3020975 = 4531463) B4531463
theorem B9640673 : Blo 263822 9640673 := bstep (se 2 (by rfl) ⟨3615252, by rfl⟩ : syracuseStep 9640673 = 7230505) B7230505
theorem B400103 : Blo 263822 400103 := bstep (se 1 (by rfl) ⟨300077, by rfl⟩ : syracuseStep 400103 = 600155) B600155
theorem B400265 : Blo 263822 400265 := bstep (se 2 (by rfl) ⟨150099, by rfl⟩ : syracuseStep 400265 = 300199) B300199
theorem B597023 : Blo 263822 597023 := bstep (se 1 (by rfl) ⟨447767, by rfl⟩ : syracuseStep 597023 = 895535) B895535
theorem B1285769 : Blo 263822 1285769 := bstep (se 2 (by rfl) ⟨482163, by rfl⟩ : syracuseStep 1285769 = 964327) B964327
theorem B598175 : Blo 263822 598175 := bstep (se 1 (by rfl) ⟨448631, by rfl⟩ : syracuseStep 598175 = 897263) B897263
theorem B3383531 : Blo 263822 3383531 := bstep (se 1 (by rfl) ⟨2537648, by rfl⟩ : syracuseStep 3383531 = 5075297) B5075297
theorem B598697 : Blo 263822 598697 := bstep (se 2 (by rfl) ⟨224511, by rfl⟩ : syracuseStep 598697 = 449023) B449023
theorem B894239 : Blo 263822 894239 := bstep (se 1 (by rfl) ⟨670679, by rfl⟩ : syracuseStep 894239 = 1341359) B1341359
theorem B1353023 : Blo 263822 1353023 := bstep (se 1 (by rfl) ⟨1014767, by rfl⟩ : syracuseStep 1353023 = 2029535) B2029535
theorem B599417 : Blo 263822 599417 := bstep (se 2 (by rfl) ⟨224781, by rfl⟩ : syracuseStep 599417 = 449563) B449563
theorem B338023 : Blo 263822 338023 := bstep (se 1 (by rfl) ⟨253517, by rfl⟩ : syracuseStep 338023 = 507035) B507035
theorem B895643 : Blo 263822 895643 := bstep (se 1 (by rfl) ⟨671732, by rfl⟩ : syracuseStep 895643 = 1343465) B1343465
theorem B600767 : Blo 263822 600767 := bstep (se 1 (by rfl) ⟨450575, by rfl⟩ : syracuseStep 600767 = 901151) B901151
theorem B2272157 : Blo 263822 2272157 := bstep (se 3 (by rfl) ⟨426029, by rfl⟩ : syracuseStep 2272157 = 852059) B852059
theorem B2010095 : Blo 263822 2010095 := bstep (se 1 (by rfl) ⟨1507571, by rfl⟩ : syracuseStep 2010095 = 3015143) B3015143
theorem B601415 : Blo 263822 601415 := bstep (se 1 (by rfl) ⟨451061, by rfl⟩ : syracuseStep 601415 = 902123) B902123
theorem B12432761 : Blo 263822 12432761 := bstep (se 2 (by rfl) ⟨4662285, by rfl⟩ : syracuseStep 12432761 = 9324571) B9324571
theorem B636383 : Blo 263822 636383 := bstep (se 1 (by rfl) ⟨477287, by rfl⟩ : syracuseStep 636383 = 954575) B954575
theorem B669971 : Blo 263822 669971 := bstep (se 1 (by rfl) ⟨502478, by rfl⟩ : syracuseStep 669971 = 1004957) B1004957
theorem B1128937 : Blo 263822 1128937 := bstep (se 2 (by rfl) ⟨423351, by rfl⟩ : syracuseStep 1128937 = 846703) B846703
theorem B506351 : Blo 263822 506351 := bstep (se 1 (by rfl) ⟨379763, by rfl⟩ : syracuseStep 506351 = 759527) B759527
theorem B1522313 : Blo 263822 1522313 := bstep (se 2 (by rfl) ⟨570867, by rfl⟩ : syracuseStep 1522313 = 1141735) B1141735
theorem B539455 : Blo 263822 539455 := bstep (se 1 (by rfl) ⟨404591, by rfl⟩ : syracuseStep 539455 = 809183) B809183
theorem B671591 : Blo 263822 671591 := bstep (se 1 (by rfl) ⟨503693, by rfl⟩ : syracuseStep 671591 = 1007387) B1007387
theorem B4341833 : Blo 263822 4341833 := bstep (se 2 (by rfl) ⟨1628187, by rfl⟩ : syracuseStep 4341833 = 3256375) B3256375
theorem B5718185 : Blo 263822 5718185 := bstep (se 2 (by rfl) ⟨2144319, by rfl⟩ : syracuseStep 5718185 = 4288639) B4288639
theorem B4310441 : Blo 263822 4310441 := bstep (se 2 (by rfl) ⟨1616415, by rfl⟩ : syracuseStep 4310441 = 3232831) B3232831
theorem B5458691 : Blo 263822 5458691 := bstep (se 1 (by rfl) ⟨4094018, by rfl⟩ : syracuseStep 5458691 = 8188037) B8188037
theorem B379775 : Blo 263822 379775 := bstep (se 1 (by rfl) ⟨284831, by rfl⟩ : syracuseStep 379775 = 569663) B569663
theorem B445513 : Blo 263822 445513 := bstep (se 2 (by rfl) ⟨167067, by rfl⟩ : syracuseStep 445513 = 334135) B334135
theorem B23252183 : Blo 263822 23252183 := bstep (se 1 (by rfl) ⟨17439137, by rfl⟩ : syracuseStep 23252183 = 34878275) B34878275
theorem B1134233 : Blo 263822 1134233 := bstep (se 2 (by rfl) ⟨425337, by rfl⟩ : syracuseStep 1134233 = 850675) B850675
theorem B4083371 : Blo 263822 4083371 := bstep (se 1 (by rfl) ⟨3062528, by rfl⟩ : syracuseStep 4083371 = 6125057) B6125057
theorem B512831 : Blo 263822 512831 := bstep (se 1 (by rfl) ⟨384623, by rfl⟩ : syracuseStep 512831 = 769247) B769247
theorem B677119 : Blo 263822 677119 := bstep (se 1 (by rfl) ⟨507839, by rfl⟩ : syracuseStep 677119 = 1015679) B1015679
theorem B447977 : Blo 263822 447977 := bstep (se 2 (by rfl) ⟨167991, by rfl⟩ : syracuseStep 447977 = 335983) B335983
theorem B4118039 : Blo 263822 4118039 := bstep (se 1 (by rfl) ⟨3088529, by rfl⟩ : syracuseStep 4118039 = 6177059) B6177059
theorem B1922783 : Blo 263822 1922783 := bstep (se 1 (by rfl) ⟨1442087, by rfl⟩ : syracuseStep 1922783 = 2884175) B2884175
theorem B23320871 : Blo 263822 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B1137377 : Blo 263822 1137377 := bstep (se 2 (by rfl) ⟨426516, by rfl⟩ : syracuseStep 1137377 = 853033) B853033
theorem B1137719 : Blo 263822 1137719 := bstep (se 1 (by rfl) ⟨853289, by rfl⟩ : syracuseStep 1137719 = 1706579) B1706579
theorem B6119135 : Blo 263822 6119135 := bstep (se 1 (by rfl) ⟨4589351, by rfl⟩ : syracuseStep 6119135 = 9178703) B9178703
theorem B450535 : Blo 263822 450535 := bstep (se 1 (by rfl) ⟨337901, by rfl⟩ : syracuseStep 450535 = 675803) B675803
theorem B1270363 : Blo 263822 1270363 := bstep (se 1 (by rfl) ⟨952772, by rfl⟩ : syracuseStep 1270363 = 1905545) B1905545
theorem B3433751 : Blo 263822 3433751 := bstep (se 1 (by rfl) ⟨2575313, by rfl⟩ : syracuseStep 3433751 = 5150627) B5150627
theorem B1142009 : Blo 263822 1142009 := bstep (se 2 (by rfl) ⟨428253, by rfl⟩ : syracuseStep 1142009 = 856507) B856507
theorem B1929071 : Blo 263822 1929071 := bstep (se 1 (by rfl) ⟨1446803, by rfl⟩ : syracuseStep 1929071 = 2893607) B2893607
theorem B2029049 : Blo 263822 2029049 := bstep (se 2 (by rfl) ⟨760893, by rfl⟩ : syracuseStep 2029049 = 1521787) B1521787
theorem B1013417 : Blo 263822 1013417 := bstep (se 2 (by rfl) ⟨380031, by rfl⟩ : syracuseStep 1013417 = 760063) B760063
theorem B3639127 : Blo 263822 3639127 := bstep (se 1 (by rfl) ⟨2729345, by rfl⟩ : syracuseStep 3639127 = 5458691) B5458691
theorem B15501455 : Blo 263822 15501455 := bstep (se 1 (by rfl) ⟨11626091, by rfl⟩ : syracuseStep 15501455 = 23252183) B23252183
theorem B264607 : Blo 263822 264607 := bstep (se 1 (by rfl) ⟨198455, by rfl⟩ : syracuseStep 264607 = 396911) B396911
theorem B756155 : Blo 263822 756155 := bstep (se 1 (by rfl) ⟨567116, by rfl⟩ : syracuseStep 756155 = 1134233) B1134233
theorem B2722247 : Blo 263822 2722247 := bstep (se 1 (by rfl) ⟨2041685, by rfl⟩ : syracuseStep 2722247 = 4083371) B4083371
theorem B265151 : Blo 263822 265151 := bstep (se 1 (by rfl) ⟨198863, by rfl⟩ : syracuseStep 265151 = 397727) B397727
theorem B298651 : Blo 263822 298651 := bstep (se 1 (by rfl) ⟨223988, by rfl⟩ : syracuseStep 298651 = 447977) B447977
theorem B265883 : Blo 263822 265883 := bstep (se 1 (by rfl) ⟨199412, by rfl⟩ : syracuseStep 265883 = 398825) B398825
theorem B594017 : Blo 263822 594017 := bstep (se 2 (by rfl) ⟨222756, by rfl⟩ : syracuseStep 594017 = 445513) B445513
theorem B6427115 : Blo 263822 6427115 := bstep (se 1 (by rfl) ⟨4820336, by rfl⟩ : syracuseStep 6427115 = 9640673) B9640673
theorem B758251 : Blo 263822 758251 := bstep (se 1 (by rfl) ⟨568688, by rfl⟩ : syracuseStep 758251 = 1137377) B1137377
theorem B266735 : Blo 263822 266735 := bstep (se 1 (by rfl) ⟨200051, by rfl⟩ : syracuseStep 266735 = 400103) B400103
theorem B266843 : Blo 263822 266843 := bstep (se 1 (by rfl) ⟨200132, by rfl⟩ : syracuseStep 266843 = 400265) B400265
theorem B398015 : Blo 263822 398015 := bstep (se 1 (by rfl) ⟨298511, by rfl⟩ : syracuseStep 398015 = 597023) B597023
theorem B758479 : Blo 263822 758479 := bstep (se 1 (by rfl) ⟨568859, by rfl⟩ : syracuseStep 758479 = 1137719) B1137719
theorem B398057 : Blo 263822 398057 := bstep (se 2 (by rfl) ⟨149271, by rfl⟩ : syracuseStep 398057 = 298543) B298543
theorem B857179 : Blo 263822 857179 := bstep (se 1 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 857179 = 1285769) B1285769
theorem B398783 : Blo 263822 398783 := bstep (se 1 (by rfl) ⟨299087, by rfl⟩ : syracuseStep 398783 = 598175) B598175
theorem B890621 : Blo 263822 890621 := bstep (se 3 (by rfl) ⟨166991, by rfl⟩ : syracuseStep 890621 = 333983) B333983
theorem B399131 : Blo 263822 399131 := bstep (se 1 (by rfl) ⟨299348, by rfl⟩ : syracuseStep 399131 = 598697) B598697
theorem B596159 : Blo 263822 596159 := bstep (se 1 (by rfl) ⟨447119, by rfl⟩ : syracuseStep 596159 = 894239) B894239
theorem B399611 : Blo 263822 399611 := bstep (se 1 (by rfl) ⟨299708, by rfl⟩ : syracuseStep 399611 = 599417) B599417
theorem B399737 : Blo 263822 399737 := bstep (se 2 (by rfl) ⟨149901, by rfl⟩ : syracuseStep 399737 = 299803) B299803
theorem B1350269 : Blo 263822 1350269 := bstep (se 3 (by rfl) ⟨253175, by rfl⟩ : syracuseStep 1350269 = 506351) B506351
theorem B597095 : Blo 263822 597095 := bstep (se 1 (by rfl) ⟨447821, by rfl⟩ : syracuseStep 597095 = 895643) B895643
theorem B400511 : Blo 263822 400511 := bstep (se 1 (by rfl) ⟨300383, by rfl⟩ : syracuseStep 400511 = 600767) B600767
theorem B1514771 : Blo 263822 1514771 := bstep (se 1 (by rfl) ⟨1136078, by rfl⟩ : syracuseStep 1514771 = 2272157) B2272157
theorem B761339 : Blo 263822 761339 := bstep (se 1 (by rfl) ⟨571004, by rfl⟩ : syracuseStep 761339 = 1142009) B1142009
theorem B400943 : Blo 263822 400943 := bstep (se 1 (by rfl) ⟨300707, by rfl⟩ : syracuseStep 400943 = 601415) B601415
theorem B1286047 : Blo 263822 1286047 := bstep (se 1 (by rfl) ⟨964535, by rfl⟩ : syracuseStep 1286047 = 1929071) B1929071
theorem B401321 : Blo 263822 401321 := bstep (se 2 (by rfl) ⟨150495, by rfl⟩ : syracuseStep 401321 = 300991) B300991
theorem B1352699 : Blo 263822 1352699 := bstep (se 1 (by rfl) ⟨1014524, by rfl⟩ : syracuseStep 1352699 = 2029049) B2029049
theorem B600713 : Blo 263822 600713 := bstep (se 2 (by rfl) ⟨225267, by rfl⟩ : syracuseStep 600713 = 450535) B450535
theorem B502463 : Blo 263822 502463 := bstep (se 1 (by rfl) ⟨376847, by rfl⟩ : syracuseStep 502463 = 753695) B753695
theorem B2894555 : Blo 263822 2894555 := bstep (se 1 (by rfl) ⟨2170916, by rfl⟩ : syracuseStep 2894555 = 4341833) B4341833
theorem B3812123 : Blo 263822 3812123 := bstep (se 1 (by rfl) ⟨2859092, by rfl⟩ : syracuseStep 3812123 = 5718185) B5718185
theorem B898235 : Blo 263822 898235 := bstep (se 1 (by rfl) ⟨673676, by rfl⟩ : syracuseStep 898235 = 1347353) B1347353
theorem B506063 : Blo 263822 506063 := bstep (se 1 (by rfl) ⟨379547, by rfl⟩ : syracuseStep 506063 = 759095) B759095
theorem B2013983 : Blo 263822 2013983 := bstep (se 1 (by rfl) ⟨1510487, by rfl⟩ : syracuseStep 2013983 = 3020975) B3020975
theorem B15547247 : Blo 263822 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B5127421 : Blo 263822 5127421 := bstep (se 3 (by rfl) ⟨961391, by rfl⟩ : syracuseStep 5127421 = 1922783) B1922783
theorem B4079423 : Blo 263822 4079423 := bstep (se 1 (by rfl) ⟨3059567, by rfl⟩ : syracuseStep 4079423 = 6119135) B6119135
theorem B902015 : Blo 263822 902015 := bstep (se 1 (by rfl) ⟨676511, by rfl⟩ : syracuseStep 902015 = 1353023) B1353023
theorem B902825 : Blo 263822 902825 := bstep (se 2 (by rfl) ⟨338559, by rfl⟩ : syracuseStep 902825 = 677119) B677119
theorem B675611 : Blo 263822 675611 := bstep (se 1 (by rfl) ⟨506708, by rfl⟩ : syracuseStep 675611 = 1013417) B1013417
theorem B446647 : Blo 263822 446647 := bstep (se 1 (by rfl) ⟨334985, by rfl⟩ : syracuseStep 446647 = 669971) B669971
theorem B447727 : Blo 263822 447727 := bstep (se 1 (by rfl) ⟨335795, by rfl⟩ : syracuseStep 447727 = 671591) B671591
theorem B1693817 : Blo 263822 1693817 := bstep (se 2 (by rfl) ⟨635181, by rfl⟩ : syracuseStep 1693817 = 1270363) B1270363
theorem B2873627 : Blo 263822 2873627 := bstep (se 1 (by rfl) ⟨2155220, by rfl⟩ : syracuseStep 2873627 = 4310441) B4310441
theorem B1367549 : Blo 263822 1367549 := bstep (se 3 (by rfl) ⟨256415, by rfl⟩ : syracuseStep 1367549 = 512831) B512831
theorem B1269863 : Blo 263822 1269863 := bstep (se 1 (by rfl) ⟨952397, by rfl⟩ : syracuseStep 1269863 = 1904795) B1904795
theorem B450697 : Blo 263822 450697 := bstep (se 2 (by rfl) ⟨169011, by rfl⟩ : syracuseStep 450697 = 338023) B338023
theorem B2745359 : Blo 263822 2745359 := bstep (se 1 (by rfl) ⟨2059019, by rfl⟩ : syracuseStep 2745359 = 4118039) B4118039
theorem B1697021 : Blo 263822 1697021 := bstep (se 3 (by rfl) ⟨318191, by rfl⟩ : syracuseStep 1697021 = 636383) B636383
theorem B2255687 : Blo 263822 2255687 := bstep (se 1 (by rfl) ⟨1691765, by rfl⟩ : syracuseStep 2255687 = 3383531) B3383531
theorem B1272937 : Blo 263822 1272937 := bstep (se 2 (by rfl) ⟨477351, by rfl⟩ : syracuseStep 1272937 = 954703) B954703
theorem B2289167 : Blo 263822 2289167 := bstep (se 1 (by rfl) ⟨1716875, by rfl⟩ : syracuseStep 2289167 = 3433751) B3433751
theorem B1340063 : Blo 263822 1340063 := bstep (se 1 (by rfl) ⟨1005047, by rfl⟩ : syracuseStep 1340063 = 2010095) B2010095
theorem B1012733 : Blo 263822 1012733 := bstep (se 3 (by rfl) ⟨189887, by rfl⟩ : syracuseStep 1012733 = 379775) B379775
theorem B1505249 : Blo 263822 1505249 := bstep (se 2 (by rfl) ⟨564468, by rfl⟩ : syracuseStep 1505249 = 1128937) B1128937
theorem B8288507 : Blo 263822 8288507 := bstep (se 1 (by rfl) ⟨6216380, by rfl⟩ : syracuseStep 8288507 = 12432761) B12432761
theorem B719273 : Blo 263822 719273 := bstep (se 2 (by rfl) ⟨269727, by rfl⟩ : syracuseStep 719273 = 539455) B539455
theorem B1014875 : Blo 263822 1014875 := bstep (se 1 (by rfl) ⟨761156, by rfl⟩ : syracuseStep 1014875 = 1522313) B1522313
theorem B4852169 : Blo 263822 4852169 := bstep (se 2 (by rfl) ⟨1819563, by rfl⟩ : syracuseStep 4852169 = 3639127) B3639127
theorem B396011 : Blo 263822 396011 := bstep (se 1 (by rfl) ⟨297008, by rfl⟩ : syracuseStep 396011 = 594017) B594017
theorem B265343 : Blo 263822 265343 := bstep (se 1 (by rfl) ⟨199007, by rfl⟩ : syracuseStep 265343 = 398015) B398015
theorem B265371 : Blo 263822 265371 := bstep (se 1 (by rfl) ⟨199028, by rfl⟩ : syracuseStep 265371 = 398057) B398057
theorem B265855 : Blo 263822 265855 := bstep (se 1 (by rfl) ⟨199391, by rfl⟩ : syracuseStep 265855 = 398783) B398783
theorem B593747 : Blo 263822 593747 := bstep (se 1 (by rfl) ⟨445310, by rfl⟩ : syracuseStep 593747 = 890621) B890621
theorem B266087 : Blo 263822 266087 := bstep (se 1 (by rfl) ⟨199565, by rfl⟩ : syracuseStep 266087 = 399131) B399131
theorem B397439 : Blo 263822 397439 := bstep (se 1 (by rfl) ⟨298079, by rfl⟩ : syracuseStep 397439 = 596159) B596159
theorem B266407 : Blo 263822 266407 := bstep (se 1 (by rfl) ⟨199805, by rfl⟩ : syracuseStep 266407 = 399611) B399611
theorem B266491 : Blo 263822 266491 := bstep (se 1 (by rfl) ⟨199868, by rfl⟩ : syracuseStep 266491 = 399737) B399737
theorem B398063 : Blo 263822 398063 := bstep (se 1 (by rfl) ⟨298547, by rfl⟩ : syracuseStep 398063 = 597095) B597095
theorem B267007 : Blo 263822 267007 := bstep (se 1 (by rfl) ⟨200255, by rfl⟩ : syracuseStep 267007 = 400511) B400511
theorem B398201 : Blo 263822 398201 := bstep (se 2 (by rfl) ⟨149325, by rfl⟩ : syracuseStep 398201 = 298651) B298651
theorem B267295 : Blo 263822 267295 := bstep (se 1 (by rfl) ⟨200471, by rfl⟩ : syracuseStep 267295 = 400943) B400943
theorem B267547 : Blo 263822 267547 := bstep (se 1 (by rfl) ⟨200660, by rfl⟩ : syracuseStep 267547 = 401321) B401321
theorem B595529 : Blo 263822 595529 := bstep (se 2 (by rfl) ⟨223323, by rfl⟩ : syracuseStep 595529 = 446647) B446647
theorem B596969 : Blo 263822 596969 := bstep (se 2 (by rfl) ⟨223863, by rfl⟩ : syracuseStep 596969 = 447727) B447727
theorem B400475 : Blo 263822 400475 := bstep (se 1 (by rfl) ⟨300356, by rfl⟩ : syracuseStep 400475 = 600713) B600713
theorem B893375 : Blo 263822 893375 := bstep (se 1 (by rfl) ⟨670031, by rfl⟩ : syracuseStep 893375 = 1340063) B1340063
theorem B598823 : Blo 263822 598823 := bstep (se 1 (by rfl) ⟨449117, by rfl⟩ : syracuseStep 598823 = 898235) B898235
theorem B337375 : Blo 263822 337375 := bstep (se 1 (by rfl) ⟨253031, by rfl⟩ : syracuseStep 337375 = 506063) B506063
theorem B10364831 : Blo 263822 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B1714729 : Blo 263822 1714729 := bstep (se 2 (by rfl) ⟨643023, by rfl⟩ : syracuseStep 1714729 = 1286047) B1286047
theorem B600929 : Blo 263822 600929 := bstep (se 2 (by rfl) ⟨225348, by rfl⟩ : syracuseStep 600929 = 450697) B450697
theorem B601343 : Blo 263822 601343 := bstep (se 1 (by rfl) ⟨451007, by rfl⟩ : syracuseStep 601343 = 902015) B902015
theorem B601883 : Blo 263822 601883 := bstep (se 1 (by rfl) ⟨451412, by rfl⟩ : syracuseStep 601883 = 902825) B902825
theorem B10334303 : Blo 263822 10334303 := bstep (se 1 (by rfl) ⟨7750727, by rfl⟩ : syracuseStep 10334303 = 15501455) B15501455
theorem B1814831 : Blo 263822 1814831 := bstep (se 1 (by rfl) ⟨1361123, by rfl⟩ : syracuseStep 1814831 = 2722247) B2722247
theorem B1129211 : Blo 263822 1129211 := bstep (se 1 (by rfl) ⟨846908, by rfl⟩ : syracuseStep 1129211 = 1693817) B1693817
theorem B1915751 : Blo 263822 1915751 := bstep (se 1 (by rfl) ⟨1436813, by rfl⟩ : syracuseStep 1915751 = 2873627) B2873627
theorem B900179 : Blo 263822 900179 := bstep (se 1 (by rfl) ⟨675134, by rfl⟩ : syracuseStep 900179 = 1350269) B1350269
theorem B507559 : Blo 263822 507559 := bstep (se 1 (by rfl) ⟨380669, by rfl⟩ : syracuseStep 507559 = 761339) B761339
theorem B901799 : Blo 263822 901799 := bstep (se 1 (by rfl) ⟨676349, by rfl⟩ : syracuseStep 901799 = 1352699) B1352699
theorem B1131347 : Blo 263822 1131347 := bstep (se 1 (by rfl) ⟨848510, by rfl⟩ : syracuseStep 1131347 = 1697021) B1697021
theorem B2016413 : Blo 263822 2016413 := bstep (se 3 (by rfl) ⟨378077, by rfl⟩ : syracuseStep 2016413 = 756155) B756155
theorem B2541415 : Blo 263822 2541415 := bstep (se 1 (by rfl) ⟨1906061, by rfl⟩ : syracuseStep 2541415 = 3812123) B3812123
theorem B7718813 : Blo 263822 7718813 := bstep (se 3 (by rfl) ⟨1447277, by rfl⟩ : syracuseStep 7718813 = 2894555) B2894555
theorem B1526111 : Blo 263822 1526111 := bstep (se 1 (by rfl) ⟨1144583, by rfl⟩ : syracuseStep 1526111 = 2289167) B2289167
theorem B675155 : Blo 263822 675155 := bstep (se 1 (by rfl) ⟨506366, by rfl⟩ : syracuseStep 675155 = 1012733) B1012733
theorem B1003499 : Blo 263822 1003499 := bstep (se 1 (by rfl) ⟨752624, by rfl⟩ : syracuseStep 1003499 = 1505249) B1505249
theorem B5525671 : Blo 263822 5525671 := bstep (se 1 (by rfl) ⟨4144253, by rfl⟩ : syracuseStep 5525671 = 8288507) B8288507
theorem B479515 : Blo 263822 479515 := bstep (se 1 (by rfl) ⟨359636, by rfl⟩ : syracuseStep 479515 = 719273) B719273
theorem B6836561 : Blo 263822 6836561 := bstep (se 2 (by rfl) ⟨2563710, by rfl⟩ : syracuseStep 6836561 = 5127421) B5127421
theorem B676583 : Blo 263822 676583 := bstep (se 1 (by rfl) ⟨507437, by rfl⟩ : syracuseStep 676583 = 1014875) B1014875
theorem B450407 : Blo 263822 450407 := bstep (se 1 (by rfl) ⟨337805, by rfl⟩ : syracuseStep 450407 = 675611) B675611
theorem B4284743 : Blo 263822 4284743 := bstep (se 1 (by rfl) ⟨3213557, by rfl⟩ : syracuseStep 4284743 = 6427115) B6427115
theorem B1697249 : Blo 263822 1697249 := bstep (se 2 (by rfl) ⟨636468, by rfl⟩ : syracuseStep 1697249 = 1272937) B1272937
theorem B1009847 : Blo 263822 1009847 := bstep (se 1 (by rfl) ⟨757385, by rfl⟩ : syracuseStep 1009847 = 1514771) B1514771
theorem B911699 : Blo 263822 911699 := bstep (se 1 (by rfl) ⟨683774, by rfl⟩ : syracuseStep 911699 = 1367549) B1367549
theorem B846575 : Blo 263822 846575 := bstep (se 1 (by rfl) ⟨634931, by rfl⟩ : syracuseStep 846575 = 1269863) B1269863
theorem B1011001 : Blo 263822 1011001 := bstep (se 2 (by rfl) ⟨379125, by rfl⟩ : syracuseStep 1011001 = 758251) B758251
theorem B1830239 : Blo 263822 1830239 := bstep (se 1 (by rfl) ⟨1372679, by rfl⟩ : syracuseStep 1830239 = 2745359) B2745359
theorem B1011305 : Blo 263822 1011305 := bstep (se 2 (by rfl) ⟨379239, by rfl⟩ : syracuseStep 1011305 = 758479) B758479
theorem B1142905 : Blo 263822 1142905 := bstep (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) B857179
theorem B1339901 : Blo 263822 1339901 := bstep (se 3 (by rfl) ⟨251231, by rfl⟩ : syracuseStep 1339901 = 502463) B502463
theorem B1503791 : Blo 263822 1503791 := bstep (se 1 (by rfl) ⟨1127843, by rfl⟩ : syracuseStep 1503791 = 2255687) B2255687
theorem B1342655 : Blo 263822 1342655 := bstep (se 1 (by rfl) ⟨1006991, by rfl⟩ : syracuseStep 1342655 = 2013983) B2013983
theorem B2719615 : Blo 263822 2719615 := bstep (se 1 (by rfl) ⟨2039711, by rfl⟩ : syracuseStep 2719615 = 4079423) B4079423
theorem B754231 : Blo 263822 754231 := bstep (se 1 (by rfl) ⟨565673, by rfl⟩ : syracuseStep 754231 = 1131347) B1131347
theorem B1344275 : Blo 263822 1344275 := bstep (se 1 (by rfl) ⟨1008206, by rfl⟩ : syracuseStep 1344275 = 2016413) B2016413
theorem B5145875 : Blo 263822 5145875 := bstep (se 1 (by rfl) ⟨3859406, by rfl⟩ : syracuseStep 5145875 = 7718813) B7718813
theorem B1017407 : Blo 263822 1017407 := bstep (se 1 (by rfl) ⟨763055, by rfl⟩ : syracuseStep 1017407 = 1526111) B1526111
theorem B264007 : Blo 263822 264007 := bstep (se 1 (by rfl) ⟨198005, by rfl⟩ : syracuseStep 264007 = 396011) B396011
theorem B395831 : Blo 263822 395831 := bstep (se 1 (by rfl) ⟨296873, by rfl⟩ : syracuseStep 395831 = 593747) B593747
theorem B264959 : Blo 263822 264959 := bstep (se 1 (by rfl) ⟨198719, by rfl⟩ : syracuseStep 264959 = 397439) B397439
theorem B4557707 : Blo 263822 4557707 := bstep (se 1 (by rfl) ⟨3418280, by rfl⟩ : syracuseStep 4557707 = 6836561) B6836561
theorem B265375 : Blo 263822 265375 := bstep (se 1 (by rfl) ⟨199031, by rfl⟩ : syracuseStep 265375 = 398063) B398063
theorem B265467 : Blo 263822 265467 := bstep (se 1 (by rfl) ⟨199100, by rfl⟩ : syracuseStep 265467 = 398201) B398201
theorem B397019 : Blo 263822 397019 := bstep (se 1 (by rfl) ⟨297764, by rfl⟩ : syracuseStep 397019 = 595529) B595529
theorem B1348001 : Blo 263822 1348001 := bstep (se 2 (by rfl) ⟨505500, by rfl⟩ : syracuseStep 1348001 = 1011001) B1011001
theorem B397979 : Blo 263822 397979 := bstep (se 1 (by rfl) ⟨298484, by rfl⟩ : syracuseStep 397979 = 596969) B596969
theorem B266983 : Blo 263822 266983 := bstep (se 1 (by rfl) ⟨200237, by rfl⟩ : syracuseStep 266983 = 400475) B400475
theorem B300271 : Blo 263822 300271 := bstep (se 1 (by rfl) ⟨225203, by rfl⟩ : syracuseStep 300271 = 450407) B450407
theorem B595583 : Blo 263822 595583 := bstep (se 1 (by rfl) ⟨446687, by rfl⟩ : syracuseStep 595583 = 893375) B893375
theorem B399215 : Blo 263822 399215 := bstep (se 1 (by rfl) ⟨299411, by rfl⟩ : syracuseStep 399215 = 598823) B598823
theorem B564383 : Blo 263822 564383 := bstep (se 1 (by rfl) ⟨423287, by rfl⟩ : syracuseStep 564383 = 846575) B846575
theorem B400619 : Blo 263822 400619 := bstep (se 1 (by rfl) ⟨300464, by rfl⟩ : syracuseStep 400619 = 600929) B600929
theorem B400895 : Blo 263822 400895 := bstep (se 1 (by rfl) ⟨300671, by rfl⟩ : syracuseStep 400895 = 601343) B601343
theorem B1220159 : Blo 263822 1220159 := bstep (se 1 (by rfl) ⟨915119, by rfl⟩ : syracuseStep 1220159 = 1830239) B1830239
theorem B401255 : Blo 263822 401255 := bstep (se 1 (by rfl) ⟨300941, by rfl⟩ : syracuseStep 401255 = 601883) B601883
theorem B6889535 : Blo 263822 6889535 := bstep (se 1 (by rfl) ⟨5167151, by rfl⟩ : syracuseStep 6889535 = 10334303) B10334303
theorem B893267 : Blo 263822 893267 := bstep (se 1 (by rfl) ⟨669950, by rfl⟩ : syracuseStep 893267 = 1339901) B1339901
theorem B600119 : Blo 263822 600119 := bstep (se 1 (by rfl) ⟨450089, by rfl⟩ : syracuseStep 600119 = 900179) B900179
theorem B895103 : Blo 263822 895103 := bstep (se 1 (by rfl) ⟨671327, by rfl⟩ : syracuseStep 895103 = 1342655) B1342655
theorem B601199 : Blo 263822 601199 := bstep (se 1 (by rfl) ⟨450899, by rfl⟩ : syracuseStep 601199 = 901799) B901799
theorem B3388553 : Blo 263822 3388553 := bstep (se 2 (by rfl) ⟨1270707, by rfl⟩ : syracuseStep 3388553 = 2541415) B2541415
theorem B668999 : Blo 263822 668999 := bstep (se 1 (by rfl) ⟨501749, by rfl⟩ : syracuseStep 668999 = 1003499) B1003499
theorem B1523873 : Blo 263822 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B639353 : Blo 263822 639353 := bstep (se 2 (by rfl) ⟨239757, by rfl⟩ : syracuseStep 639353 = 479515) B479515
theorem B1131499 : Blo 263822 1131499 := bstep (se 1 (by rfl) ⟨848624, by rfl⟩ : syracuseStep 1131499 = 1697249) B1697249
theorem B673231 : Blo 263822 673231 := bstep (se 1 (by rfl) ⟨504923, by rfl⟩ : syracuseStep 673231 = 1009847) B1009847
theorem B607799 : Blo 263822 607799 := bstep (se 1 (by rfl) ⟨455849, by rfl⟩ : syracuseStep 607799 = 911699) B911699
theorem B674203 : Blo 263822 674203 := bstep (se 1 (by rfl) ⟨505652, by rfl⟩ : syracuseStep 674203 = 1011305) B1011305
theorem B1002527 : Blo 263822 1002527 := bstep (se 1 (by rfl) ⟨751895, by rfl⟩ : syracuseStep 1002527 = 1503791) B1503791
theorem B676745 : Blo 263822 676745 := bstep (se 2 (by rfl) ⟨253779, by rfl⟩ : syracuseStep 676745 = 507559) B507559
theorem B3626153 : Blo 263822 3626153 := bstep (se 2 (by rfl) ⟨1359807, by rfl⟩ : syracuseStep 3626153 = 2719615) B2719615
theorem B11425981 : Blo 263822 11425981 := bstep (se 3 (by rfl) ⟨2142371, by rfl⟩ : syracuseStep 11425981 = 4284743) B4284743
theorem B3234779 : Blo 263822 3234779 := bstep (se 1 (by rfl) ⟨2426084, by rfl⟩ : syracuseStep 3234779 = 4852169) B4852169
theorem B449833 : Blo 263822 449833 := bstep (se 2 (by rfl) ⟨168687, by rfl⟩ : syracuseStep 449833 = 337375) B337375
theorem B450103 : Blo 263822 450103 := bstep (se 1 (by rfl) ⟨337577, by rfl⟩ : syracuseStep 450103 = 675155) B675155
theorem B451055 : Blo 263822 451055 := bstep (se 1 (by rfl) ⟨338291, by rfl⟩ : syracuseStep 451055 = 676583) B676583
theorem B2286305 : Blo 263822 2286305 := bstep (se 2 (by rfl) ⟨857364, by rfl⟩ : syracuseStep 2286305 = 1714729) B1714729
theorem B7367561 : Blo 263822 7367561 := bstep (se 2 (by rfl) ⟨2762835, by rfl⟩ : syracuseStep 7367561 = 5525671) B5525671
theorem B6909887 : Blo 263822 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B1209887 : Blo 263822 1209887 := bstep (se 1 (by rfl) ⟨907415, by rfl⟩ : syracuseStep 1209887 = 1814831) B1814831
theorem B752807 : Blo 263822 752807 := bstep (se 1 (by rfl) ⟨564605, by rfl⟩ : syracuseStep 752807 = 1129211) B1129211
theorem B1277167 : Blo 263822 1277167 := bstep (se 1 (by rfl) ⟨957875, by rfl⟩ : syracuseStep 1277167 = 1915751) B1915751
theorem B1015915 : Blo 263822 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B426235 : Blo 263822 426235 := bstep (se 1 (by rfl) ⟨319676, by rfl⟩ : syracuseStep 426235 = 639353) B639353
theorem B1508665 : Blo 263822 1508665 := bstep (se 2 (by rfl) ⟨565749, by rfl⟩ : syracuseStep 1508665 = 1131499) B1131499
theorem B263887 : Blo 263822 263887 := bstep (se 1 (by rfl) ⟨197915, by rfl⟩ : syracuseStep 263887 = 395831) B395831
theorem B264679 : Blo 263822 264679 := bstep (se 1 (by rfl) ⟨198509, by rfl⟩ : syracuseStep 264679 = 397019) B397019
theorem B265319 : Blo 263822 265319 := bstep (se 1 (by rfl) ⟨198989, by rfl⟩ : syracuseStep 265319 = 397979) B397979
theorem B397055 : Blo 263822 397055 := bstep (se 1 (by rfl) ⟨297791, by rfl⟩ : syracuseStep 397055 = 595583) B595583
theorem B266143 : Blo 263822 266143 := bstep (se 1 (by rfl) ⟨199607, by rfl⟩ : syracuseStep 266143 = 399215) B399215
theorem B267079 : Blo 263822 267079 := bstep (se 1 (by rfl) ⟨200309, by rfl⟩ : syracuseStep 267079 = 400619) B400619
theorem B267263 : Blo 263822 267263 := bstep (se 1 (by rfl) ⟨200447, by rfl⟩ : syracuseStep 267263 = 400895) B400895
theorem B267503 : Blo 263822 267503 := bstep (se 1 (by rfl) ⟨200627, by rfl⟩ : syracuseStep 267503 = 401255) B401255
theorem B4593023 : Blo 263822 4593023 := bstep (se 1 (by rfl) ⟨3444767, by rfl⟩ : syracuseStep 4593023 = 6889535) B6889535
theorem B595511 : Blo 263822 595511 := bstep (se 1 (by rfl) ⟨446633, by rfl⟩ : syracuseStep 595511 = 893267) B893267
theorem B300703 : Blo 263822 300703 := bstep (se 1 (by rfl) ⟨225527, by rfl⟩ : syracuseStep 300703 = 451055) B451055
theorem B400079 : Blo 263822 400079 := bstep (se 1 (by rfl) ⟨300059, by rfl⟩ : syracuseStep 400079 = 600119) B600119
theorem B596735 : Blo 263822 596735 := bstep (se 1 (by rfl) ⟨447551, by rfl⟩ : syracuseStep 596735 = 895103) B895103
theorem B400361 : Blo 263822 400361 := bstep (se 2 (by rfl) ⟨150135, by rfl⟩ : syracuseStep 400361 = 300271) B300271
theorem B400799 : Blo 263822 400799 := bstep (se 1 (by rfl) ⟨300599, by rfl⟩ : syracuseStep 400799 = 601199) B601199
theorem B599777 : Blo 263822 599777 := bstep (se 2 (by rfl) ⟨224916, by rfl⟩ : syracuseStep 599777 = 449833) B449833
theorem B600137 : Blo 263822 600137 := bstep (se 2 (by rfl) ⟨225051, by rfl⟩ : syracuseStep 600137 = 450103) B450103
theorem B501871 : Blo 263822 501871 := bstep (se 1 (by rfl) ⟨376403, by rfl⟩ : syracuseStep 501871 = 752807) B752807
theorem B18426365 : Blo 263822 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B896183 : Blo 263822 896183 := bstep (se 1 (by rfl) ⟨672137, by rfl⟩ : syracuseStep 896183 = 1344275) B1344275
theorem B405199 : Blo 263822 405199 := bstep (se 1 (by rfl) ⟨303899, by rfl⟩ : syracuseStep 405199 = 607799) B607799
theorem B897641 : Blo 263822 897641 := bstep (se 2 (by rfl) ⟨336615, by rfl⟩ : syracuseStep 897641 = 673231) B673231
theorem B668351 : Blo 263822 668351 := bstep (se 1 (by rfl) ⟨501263, by rfl⟩ : syracuseStep 668351 = 1002527) B1002527
theorem B898667 : Blo 263822 898667 := bstep (se 1 (by rfl) ⟨674000, by rfl⟩ : syracuseStep 898667 = 1348001) B1348001
theorem B898937 : Blo 263822 898937 := bstep (se 2 (by rfl) ⟨337101, by rfl⟩ : syracuseStep 898937 = 674203) B674203
theorem B376255 : Blo 263822 376255 := bstep (se 1 (by rfl) ⟨282191, by rfl⟩ : syracuseStep 376255 = 564383) B564383
theorem B1524203 : Blo 263822 1524203 := bstep (se 1 (by rfl) ⟨1143152, by rfl⟩ : syracuseStep 1524203 = 2286305) B2286305
theorem B445999 : Blo 263822 445999 := bstep (se 1 (by rfl) ⟨334499, by rfl⟩ : syracuseStep 445999 = 668999) B668999
theorem B806591 : Blo 263822 806591 := bstep (se 1 (by rfl) ⟨604943, by rfl⟩ : syracuseStep 806591 = 1209887) B1209887
theorem B1005641 : Blo 263822 1005641 := bstep (se 2 (by rfl) ⟨377115, by rfl⟩ : syracuseStep 1005641 = 754231) B754231
theorem B3430583 : Blo 263822 3430583 := bstep (se 1 (by rfl) ⟨2572937, by rfl⟩ : syracuseStep 3430583 = 5145875) B5145875
theorem B3038471 : Blo 263822 3038471 := bstep (se 1 (by rfl) ⟨2278853, by rfl⟩ : syracuseStep 3038471 = 4557707) B4557707
theorem B451163 : Blo 263822 451163 := bstep (se 1 (by rfl) ⟨338372, by rfl⟩ : syracuseStep 451163 = 676745) B676745
theorem B2417435 : Blo 263822 2417435 := bstep (se 1 (by rfl) ⟨1813076, by rfl⟩ : syracuseStep 2417435 = 3626153) B3626153
theorem B2713085 : Blo 263822 2713085 := bstep (se 3 (by rfl) ⟨508703, by rfl⟩ : syracuseStep 2713085 = 1017407) B1017407
theorem B2156519 : Blo 263822 2156519 := bstep (se 1 (by rfl) ⟨1617389, by rfl⟩ : syracuseStep 2156519 = 3234779) B3234779
theorem B813439 : Blo 263822 813439 := bstep (se 1 (by rfl) ⟨610079, by rfl⟩ : syracuseStep 813439 = 1220159) B1220159
theorem B4911707 : Blo 263822 4911707 := bstep (se 1 (by rfl) ⟨3683780, by rfl⟩ : syracuseStep 4911707 = 7367561) B7367561
theorem B15234641 : Blo 263822 15234641 := bstep (se 2 (by rfl) ⟨5712990, by rfl⟩ : syracuseStep 15234641 = 11425981) B11425981
theorem B2259035 : Blo 263822 2259035 := bstep (se 1 (by rfl) ⟨1694276, by rfl⟩ : syracuseStep 2259035 = 3388553) B3388553
theorem B1702889 : Blo 263822 1702889 := bstep (se 2 (by rfl) ⟨638583, by rfl⟩ : syracuseStep 1702889 = 1277167) B1277167
theorem B1016135 : Blo 263822 1016135 := bstep (se 1 (by rfl) ⟨762101, by rfl⟩ : syracuseStep 1016135 = 1524203) B1524203
theorem B264703 : Blo 263822 264703 := bstep (se 1 (by rfl) ⟨198527, by rfl⟩ : syracuseStep 264703 = 397055) B397055
theorem B1084585 : Blo 263822 1084585 := bstep (se 2 (by rfl) ⟨406719, by rfl⟩ : syracuseStep 1084585 = 813439) B813439
theorem B397007 : Blo 263822 397007 := bstep (se 1 (by rfl) ⟨297755, by rfl⟩ : syracuseStep 397007 = 595511) B595511
theorem B266719 : Blo 263822 266719 := bstep (se 1 (by rfl) ⟨200039, by rfl⟩ : syracuseStep 266719 = 400079) B400079
theorem B397823 : Blo 263822 397823 := bstep (se 1 (by rfl) ⟨298367, by rfl⟩ : syracuseStep 397823 = 596735) B596735
theorem B266907 : Blo 263822 266907 := bstep (se 1 (by rfl) ⟨200180, by rfl⟩ : syracuseStep 266907 = 400361) B400361
theorem B594665 : Blo 263822 594665 := bstep (se 2 (by rfl) ⟨222999, by rfl⟩ : syracuseStep 594665 = 445999) B445999
theorem B267199 : Blo 263822 267199 := bstep (se 1 (by rfl) ⟨200399, by rfl⟩ : syracuseStep 267199 = 400799) B400799
theorem B300775 : Blo 263822 300775 := bstep (se 1 (by rfl) ⟨225581, by rfl⟩ : syracuseStep 300775 = 451163) B451163
theorem B1611623 : Blo 263822 1611623 := bstep (se 1 (by rfl) ⟨1208717, by rfl⟩ : syracuseStep 1611623 = 2417435) B2417435
theorem B1808723 : Blo 263822 1808723 := bstep (se 1 (by rfl) ⟨1356542, by rfl⟩ : syracuseStep 1808723 = 2713085) B2713085
theorem B399851 : Blo 263822 399851 := bstep (se 1 (by rfl) ⟨299888, by rfl⟩ : syracuseStep 399851 = 599777) B599777
theorem B400091 : Blo 263822 400091 := bstep (se 1 (by rfl) ⟨300068, by rfl⟩ : syracuseStep 400091 = 600137) B600137
theorem B597455 : Blo 263822 597455 := bstep (se 1 (by rfl) ⟨448091, by rfl⟩ : syracuseStep 597455 = 896183) B896183
theorem B400937 : Blo 263822 400937 := bstep (se 2 (by rfl) ⟨150351, by rfl⟩ : syracuseStep 400937 = 300703) B300703
theorem B2006693 : Blo 263822 2006693 := bstep (se 4 (by rfl) ⟨188127, by rfl⟩ : syracuseStep 2006693 = 376255) B376255
theorem B598427 : Blo 263822 598427 := bstep (se 1 (by rfl) ⟨448820, by rfl⟩ : syracuseStep 598427 = 897641) B897641
theorem B599111 : Blo 263822 599111 := bstep (se 1 (by rfl) ⟨449333, by rfl⟩ : syracuseStep 599111 = 898667) B898667
theorem B599291 : Blo 263822 599291 := bstep (se 1 (by rfl) ⟨449468, by rfl⟩ : syracuseStep 599291 = 898937) B898937
theorem B1354553 : Blo 263822 1354553 := bstep (se 2 (by rfl) ⟨507957, by rfl⟩ : syracuseStep 1354553 = 1015915) B1015915
theorem B568313 : Blo 263822 568313 := bstep (se 2 (by rfl) ⟨213117, by rfl⟩ : syracuseStep 568313 = 426235) B426235
theorem B2011553 : Blo 263822 2011553 := bstep (se 2 (by rfl) ⟨754332, by rfl⟩ : syracuseStep 2011553 = 1508665) B1508665
theorem B537727 : Blo 263822 537727 := bstep (se 1 (by rfl) ⟨403295, by rfl⟩ : syracuseStep 537727 = 806591) B806591
theorem B669161 : Blo 263822 669161 := bstep (se 2 (by rfl) ⟨250935, by rfl⟩ : syracuseStep 669161 = 501871) B501871
theorem B3062015 : Blo 263822 3062015 := bstep (se 1 (by rfl) ⟨2296511, by rfl⟩ : syracuseStep 3062015 = 4593023) B4593023
theorem B670427 : Blo 263822 670427 := bstep (se 1 (by rfl) ⟨502820, by rfl⟩ : syracuseStep 670427 = 1005641) B1005641
theorem B540265 : Blo 263822 540265 := bstep (se 2 (by rfl) ⟨202599, by rfl⟩ : syracuseStep 540265 = 405199) B405199
theorem B445567 : Blo 263822 445567 := bstep (se 1 (by rfl) ⟨334175, by rfl⟩ : syracuseStep 445567 = 668351) B668351
theorem B1135259 : Blo 263822 1135259 := bstep (se 1 (by rfl) ⟨851444, by rfl⟩ : syracuseStep 1135259 = 1702889) B1702889
theorem B2287055 : Blo 263822 2287055 := bstep (se 1 (by rfl) ⟨1715291, by rfl⟩ : syracuseStep 2287055 = 3430583) B3430583
theorem B2025647 : Blo 263822 2025647 := bstep (se 1 (by rfl) ⟨1519235, by rfl⟩ : syracuseStep 2025647 = 3038471) B3038471
theorem B1437679 : Blo 263822 1437679 := bstep (se 1 (by rfl) ⟨1078259, by rfl⟩ : syracuseStep 1437679 = 2156519) B2156519
theorem B12284243 : Blo 263822 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B3274471 : Blo 263822 3274471 := bstep (se 1 (by rfl) ⟨2455853, by rfl⟩ : syracuseStep 3274471 = 4911707) B4911707
theorem B10156427 : Blo 263822 10156427 := bstep (se 1 (by rfl) ⟨7617320, by rfl⟩ : syracuseStep 10156427 = 15234641) B15234641
theorem B1506023 : Blo 263822 1506023 := bstep (se 1 (by rfl) ⟨1129517, by rfl⟩ : syracuseStep 1506023 = 2259035) B2259035
theorem B264671 : Blo 263822 264671 := bstep (se 1 (by rfl) ⟨198503, by rfl⟩ : syracuseStep 264671 = 397007) B397007
theorem B265215 : Blo 263822 265215 := bstep (se 1 (by rfl) ⟨198911, by rfl⟩ : syracuseStep 265215 = 397823) B397823
theorem B756839 : Blo 263822 756839 := bstep (se 1 (by rfl) ⟨567629, by rfl⟩ : syracuseStep 756839 = 1135259) B1135259
theorem B396443 : Blo 263822 396443 := bstep (se 1 (by rfl) ⟨297332, by rfl⟩ : syracuseStep 396443 = 594665) B594665
theorem B594089 : Blo 263822 594089 := bstep (se 2 (by rfl) ⟨222783, by rfl⟩ : syracuseStep 594089 = 445567) B445567
theorem B1446113 : Blo 263822 1446113 := bstep (se 2 (by rfl) ⟨542292, by rfl⟩ : syracuseStep 1446113 = 1084585) B1084585
theorem B266567 : Blo 263822 266567 := bstep (se 1 (by rfl) ⟨199925, by rfl⟩ : syracuseStep 266567 = 399851) B399851
theorem B266727 : Blo 263822 266727 := bstep (se 1 (by rfl) ⟨200045, by rfl⟩ : syracuseStep 266727 = 400091) B400091
theorem B4297661 : Blo 263822 4297661 := bstep (se 3 (by rfl) ⟨805811, by rfl⟩ : syracuseStep 4297661 = 1611623) B1611623
theorem B398303 : Blo 263822 398303 := bstep (se 1 (by rfl) ⟨298727, by rfl⟩ : syracuseStep 398303 = 597455) B597455
theorem B267291 : Blo 263822 267291 := bstep (se 1 (by rfl) ⟨200468, by rfl⟩ : syracuseStep 267291 = 400937) B400937
theorem B398951 : Blo 263822 398951 := bstep (se 1 (by rfl) ⟨299213, by rfl⟩ : syracuseStep 398951 = 598427) B598427
theorem B399407 : Blo 263822 399407 := bstep (se 1 (by rfl) ⟨299555, by rfl⟩ : syracuseStep 399407 = 599111) B599111
theorem B399527 : Blo 263822 399527 := bstep (se 1 (by rfl) ⟨299645, by rfl⟩ : syracuseStep 399527 = 599291) B599291
theorem B1350431 : Blo 263822 1350431 := bstep (se 1 (by rfl) ⟨1012823, by rfl⟩ : syracuseStep 1350431 = 2025647) B2025647
theorem B401033 : Blo 263822 401033 := bstep (se 2 (by rfl) ⟨150387, by rfl⟩ : syracuseStep 401033 = 300775) B300775
theorem B2041343 : Blo 263822 2041343 := bstep (se 1 (by rfl) ⟨1531007, by rfl⟩ : syracuseStep 2041343 = 3062015) B3062015
theorem B1916905 : Blo 263822 1916905 := bstep (se 2 (by rfl) ⟨718839, by rfl⟩ : syracuseStep 1916905 = 1437679) B1437679
theorem B1524703 : Blo 263822 1524703 := bstep (se 1 (by rfl) ⟨1143527, by rfl⟩ : syracuseStep 1524703 = 2287055) B2287055
theorem B903035 : Blo 263822 903035 := bstep (se 1 (by rfl) ⟨677276, by rfl⟩ : syracuseStep 903035 = 1354553) B1354553
theorem B378875 : Blo 263822 378875 := bstep (se 1 (by rfl) ⟨284156, by rfl⟩ : syracuseStep 378875 = 568313) B568313
theorem B446107 : Blo 263822 446107 := bstep (se 1 (by rfl) ⟨334580, by rfl⟩ : syracuseStep 446107 = 669161) B669161
theorem B6770951 : Blo 263822 6770951 := bstep (se 1 (by rfl) ⟨5078213, by rfl⟩ : syracuseStep 6770951 = 10156427) B10156427
theorem B446951 : Blo 263822 446951 := bstep (se 1 (by rfl) ⟨335213, by rfl⟩ : syracuseStep 446951 = 670427) B670427
theorem B1004015 : Blo 263822 1004015 := bstep (se 1 (by rfl) ⟨753011, by rfl⟩ : syracuseStep 1004015 = 1506023) B1506023
theorem B677423 : Blo 263822 677423 := bstep (se 1 (by rfl) ⟨508067, by rfl⟩ : syracuseStep 677423 = 1016135) B1016135
theorem B1205815 : Blo 263822 1205815 := bstep (se 1 (by rfl) ⟨904361, by rfl⟩ : syracuseStep 1205815 = 1808723) B1808723
theorem B1337795 : Blo 263822 1337795 := bstep (se 1 (by rfl) ⟨1003346, by rfl⟩ : syracuseStep 1337795 = 2006693) B2006693
theorem B716969 : Blo 263822 716969 := bstep (se 2 (by rfl) ⟨268863, by rfl⟩ : syracuseStep 716969 = 537727) B537727
theorem B8189495 : Blo 263822 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B1341035 : Blo 263822 1341035 := bstep (se 1 (by rfl) ⟨1005776, by rfl⟩ : syracuseStep 1341035 = 2011553) B2011553
theorem B17463845 : Blo 263822 17463845 := bstep (se 4 (by rfl) ⟨1637235, by rfl⟩ : syracuseStep 17463845 = 3274471) B3274471
theorem B720353 : Blo 263822 720353 := bstep (se 2 (by rfl) ⟨270132, by rfl⟩ : syracuseStep 720353 = 540265) B540265
theorem B2032937 : Blo 263822 2032937 := bstep (se 2 (by rfl) ⟨762351, by rfl⟩ : syracuseStep 2032937 = 1524703) B1524703
theorem B1607753 : Blo 263822 1607753 := bstep (se 2 (by rfl) ⟨602907, by rfl⟩ : syracuseStep 1607753 = 1205815) B1205815
theorem B264295 : Blo 263822 264295 := bstep (se 1 (by rfl) ⟨198221, by rfl⟩ : syracuseStep 264295 = 396443) B396443
theorem B396059 : Blo 263822 396059 := bstep (se 1 (by rfl) ⟨297044, by rfl⟩ : syracuseStep 396059 = 594089) B594089
theorem B297967 : Blo 263822 297967 := bstep (se 1 (by rfl) ⟨223475, by rfl⟩ : syracuseStep 297967 = 446951) B446951
theorem B265535 : Blo 263822 265535 := bstep (se 1 (by rfl) ⟨199151, by rfl⟩ : syracuseStep 265535 = 398303) B398303
theorem B265967 : Blo 263822 265967 := bstep (se 1 (by rfl) ⟨199475, by rfl⟩ : syracuseStep 265967 = 398951) B398951
theorem B266271 : Blo 263822 266271 := bstep (se 1 (by rfl) ⟨199703, by rfl⟩ : syracuseStep 266271 = 399407) B399407
theorem B266351 : Blo 263822 266351 := bstep (se 1 (by rfl) ⟨199763, by rfl⟩ : syracuseStep 266351 = 399527) B399527
theorem B594809 : Blo 263822 594809 := bstep (se 2 (by rfl) ⟨223053, by rfl⟩ : syracuseStep 594809 = 446107) B446107
theorem B267355 : Blo 263822 267355 := bstep (se 1 (by rfl) ⟨200516, by rfl⟩ : syracuseStep 267355 = 401033) B401033
theorem B891863 : Blo 263822 891863 := bstep (se 1 (by rfl) ⟨668897, by rfl⟩ : syracuseStep 891863 = 1337795) B1337795
theorem B894023 : Blo 263822 894023 := bstep (se 1 (by rfl) ⟨670517, by rfl⟩ : syracuseStep 894023 = 1341035) B1341035
theorem B11642563 : Blo 263822 11642563 := bstep (se 1 (by rfl) ⟨8731922, by rfl⟩ : syracuseStep 11642563 = 17463845) B17463845
theorem B1911917 : Blo 263822 1911917 := bstep (se 3 (by rfl) ⟨358484, by rfl⟩ : syracuseStep 1911917 = 716969) B716969
theorem B602023 : Blo 263822 602023 := bstep (se 1 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 602023 = 903035) B903035
theorem B504559 : Blo 263822 504559 := bstep (se 1 (by rfl) ⟨378419, by rfl⟩ : syracuseStep 504559 = 756839) B756839
theorem B964075 : Blo 263822 964075 := bstep (se 1 (by rfl) ⟨723056, by rfl⟩ : syracuseStep 964075 = 1446113) B1446113
theorem B669343 : Blo 263822 669343 := bstep (se 1 (by rfl) ⟨502007, by rfl⟩ : syracuseStep 669343 = 1004015) B1004015
theorem B2865107 : Blo 263822 2865107 := bstep (se 1 (by rfl) ⟨2148830, by rfl⟩ : syracuseStep 2865107 = 4297661) B4297661
theorem B900287 : Blo 263822 900287 := bstep (se 1 (by rfl) ⟨675215, by rfl⟩ : syracuseStep 900287 = 1350431) B1350431
theorem B1360895 : Blo 263822 1360895 := bstep (se 1 (by rfl) ⟨1020671, by rfl⟩ : syracuseStep 1360895 = 2041343) B2041343
theorem B5459663 : Blo 263822 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B480235 : Blo 263822 480235 := bstep (se 1 (by rfl) ⟨360176, by rfl⟩ : syracuseStep 480235 = 720353) B720353
theorem B4513967 : Blo 263822 4513967 := bstep (se 1 (by rfl) ⟨3385475, by rfl⟩ : syracuseStep 4513967 = 6770951) B6770951
theorem B451615 : Blo 263822 451615 := bstep (se 1 (by rfl) ⟨338711, by rfl⟩ : syracuseStep 451615 = 677423) B677423
theorem B1010333 : Blo 263822 1010333 := bstep (se 3 (by rfl) ⟨189437, by rfl⟩ : syracuseStep 1010333 = 378875) B378875
theorem B2555873 : Blo 263822 2555873 := bstep (se 2 (by rfl) ⟨958452, by rfl⟩ : syracuseStep 2555873 = 1916905) B1916905
theorem B264039 : Blo 263822 264039 := bstep (se 1 (by rfl) ⟨198029, by rfl⟩ : syracuseStep 264039 = 396059) B396059
theorem B396539 : Blo 263822 396539 := bstep (se 1 (by rfl) ⟨297404, by rfl⟩ : syracuseStep 396539 = 594809) B594809
theorem B397289 : Blo 263822 397289 := bstep (se 2 (by rfl) ⟨148983, by rfl⟩ : syracuseStep 397289 = 297967) B297967
theorem B594575 : Blo 263822 594575 := bstep (se 1 (by rfl) ⟨445931, by rfl⟩ : syracuseStep 594575 = 891863) B891863
theorem B596015 : Blo 263822 596015 := bstep (se 1 (by rfl) ⟨447011, by rfl⟩ : syracuseStep 596015 = 894023) B894023
theorem B1285433 : Blo 263822 1285433 := bstep (se 2 (by rfl) ⟨482037, by rfl⟩ : syracuseStep 1285433 = 964075) B964075
theorem B892457 : Blo 263822 892457 := bstep (se 2 (by rfl) ⟨334671, by rfl⟩ : syracuseStep 892457 = 669343) B669343
theorem B1910071 : Blo 263822 1910071 := bstep (se 1 (by rfl) ⟨1432553, by rfl⟩ : syracuseStep 1910071 = 2865107) B2865107
theorem B14559101 : Blo 263822 14559101 := bstep (se 3 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 14559101 = 5459663) B5459663
theorem B600191 : Blo 263822 600191 := bstep (se 1 (by rfl) ⟨450143, by rfl⟩ : syracuseStep 600191 = 900287) B900287
theorem B1355291 : Blo 263822 1355291 := bstep (se 1 (by rfl) ⟨1016468, by rfl⟩ : syracuseStep 1355291 = 2032937) B2032937
theorem B602153 : Blo 263822 602153 := bstep (se 2 (by rfl) ⟨225807, by rfl⟩ : syracuseStep 602153 = 451615) B451615
theorem B672745 : Blo 263822 672745 := bstep (se 2 (by rfl) ⟨252279, by rfl⟩ : syracuseStep 672745 = 504559) B504559
theorem B640313 : Blo 263822 640313 := bstep (se 2 (by rfl) ⟨240117, by rfl⟩ : syracuseStep 640313 = 480235) B480235
theorem B673555 : Blo 263822 673555 := bstep (se 1 (by rfl) ⟨505166, by rfl⟩ : syracuseStep 673555 = 1010333) B1010333
theorem B1071835 : Blo 263822 1071835 := bstep (se 1 (by rfl) ⟨803876, by rfl⟩ : syracuseStep 1071835 = 1607753) B1607753
theorem B15523417 : Blo 263822 15523417 := bstep (se 2 (by rfl) ⟨5821281, by rfl⟩ : syracuseStep 15523417 = 11642563) B11642563
theorem B3629053 : Blo 263822 3629053 := bstep (se 3 (by rfl) ⟨680447, by rfl⟩ : syracuseStep 3629053 = 1360895) B1360895
theorem B3009311 : Blo 263822 3009311 := bstep (se 1 (by rfl) ⟨2256983, by rfl⟩ : syracuseStep 3009311 = 4513967) B4513967
theorem B1274611 : Blo 263822 1274611 := bstep (se 1 (by rfl) ⟨955958, by rfl⟩ : syracuseStep 1274611 = 1911917) B1911917
theorem B12843157 : Blo 263822 12843157 := bstep (se 6 (by rfl) ⟨301011, by rfl⟩ : syracuseStep 12843157 = 602023) B602023
theorem B1703915 : Blo 263822 1703915 := bstep (se 1 (by rfl) ⟨1277936, by rfl⟩ : syracuseStep 1703915 = 2555873) B2555873
theorem B426875 : Blo 263822 426875 := bstep (se 1 (by rfl) ⟨320156, by rfl⟩ : syracuseStep 426875 = 640313) B640313
theorem B264359 : Blo 263822 264359 := bstep (se 1 (by rfl) ⟨198269, by rfl⟩ : syracuseStep 264359 = 396539) B396539
theorem B264859 : Blo 263822 264859 := bstep (se 1 (by rfl) ⟨198644, by rfl⟩ : syracuseStep 264859 = 397289) B397289
theorem B396383 : Blo 263822 396383 := bstep (se 1 (by rfl) ⟨297287, by rfl⟩ : syracuseStep 396383 = 594575) B594575
theorem B397343 : Blo 263822 397343 := bstep (se 1 (by rfl) ⟨298007, by rfl⟩ : syracuseStep 397343 = 596015) B596015
theorem B856955 : Blo 263822 856955 := bstep (se 1 (by rfl) ⟨642716, by rfl⟩ : syracuseStep 856955 = 1285433) B1285433
theorem B594971 : Blo 263822 594971 := bstep (se 1 (by rfl) ⟨446228, by rfl⟩ : syracuseStep 594971 = 892457) B892457
theorem B9706067 : Blo 263822 9706067 := bstep (se 1 (by rfl) ⟨7279550, by rfl⟩ : syracuseStep 9706067 = 14559101) B14559101
theorem B400127 : Blo 263822 400127 := bstep (se 1 (by rfl) ⟨300095, by rfl⟩ : syracuseStep 400127 = 600191) B600191
theorem B2006207 : Blo 263822 2006207 := bstep (se 1 (by rfl) ⟨1504655, by rfl⟩ : syracuseStep 2006207 = 3009311) B3009311
theorem B401435 : Blo 263822 401435 := bstep (se 1 (by rfl) ⟨301076, by rfl⟩ : syracuseStep 401435 = 602153) B602153
theorem B896993 : Blo 263822 896993 := bstep (se 2 (by rfl) ⟨336372, by rfl⟩ : syracuseStep 896993 = 672745) B672745
theorem B898073 : Blo 263822 898073 := bstep (se 2 (by rfl) ⟨336777, by rfl⟩ : syracuseStep 898073 = 673555) B673555
theorem B5716453 : Blo 263822 5716453 := bstep (se 4 (by rfl) ⟨535917, by rfl⟩ : syracuseStep 5716453 = 1071835) B1071835
theorem B903527 : Blo 263822 903527 := bstep (se 1 (by rfl) ⟨677645, by rfl⟩ : syracuseStep 903527 = 1355291) B1355291
theorem B17124209 : Blo 263822 17124209 := bstep (se 2 (by rfl) ⟨6421578, by rfl⟩ : syracuseStep 17124209 = 12843157) B12843157
theorem B20697889 : Blo 263822 20697889 := bstep (se 2 (by rfl) ⟨7761708, by rfl⟩ : syracuseStep 20697889 = 15523417) B15523417
theorem B1135943 : Blo 263822 1135943 := bstep (se 1 (by rfl) ⟨851957, by rfl⟩ : syracuseStep 1135943 = 1703915) B1703915
theorem B4838737 : Blo 263822 4838737 := bstep (se 2 (by rfl) ⟨1814526, by rfl⟩ : syracuseStep 4838737 = 3629053) B3629053
theorem B2546761 : Blo 263822 2546761 := bstep (se 2 (by rfl) ⟨955035, by rfl⟩ : syracuseStep 2546761 = 1910071) B1910071
theorem B1699481 : Blo 263822 1699481 := bstep (se 2 (by rfl) ⟨637305, by rfl⟩ : syracuseStep 1699481 = 1274611) B1274611
theorem B264255 : Blo 263822 264255 := bstep (se 1 (by rfl) ⟨198191, by rfl⟩ : syracuseStep 264255 = 396383) B396383
theorem B264895 : Blo 263822 264895 := bstep (se 1 (by rfl) ⟨198671, by rfl⟩ : syracuseStep 264895 = 397343) B397343
theorem B396647 : Blo 263822 396647 := bstep (se 1 (by rfl) ⟨297485, by rfl⟩ : syracuseStep 396647 = 594971) B594971
theorem B757295 : Blo 263822 757295 := bstep (se 1 (by rfl) ⟨567971, by rfl⟩ : syracuseStep 757295 = 1135943) B1135943
theorem B266751 : Blo 263822 266751 := bstep (se 1 (by rfl) ⟨200063, by rfl⟩ : syracuseStep 266751 = 400127) B400127
theorem B267623 : Blo 263822 267623 := bstep (se 1 (by rfl) ⟨200717, by rfl⟩ : syracuseStep 267623 = 401435) B401435
theorem B27597185 : Blo 263822 27597185 := bstep (se 2 (by rfl) ⟨10348944, by rfl⟩ : syracuseStep 27597185 = 20697889) B20697889
theorem B597995 : Blo 263822 597995 := bstep (se 1 (by rfl) ⟨448496, by rfl⟩ : syracuseStep 597995 = 896993) B896993
theorem B598715 : Blo 263822 598715 := bstep (se 1 (by rfl) ⟨449036, by rfl⟩ : syracuseStep 598715 = 898073) B898073
theorem B602351 : Blo 263822 602351 := bstep (se 1 (by rfl) ⟨451763, by rfl⟩ : syracuseStep 602351 = 903527) B903527
theorem B11416139 : Blo 263822 11416139 := bstep (se 1 (by rfl) ⟨8562104, by rfl⟩ : syracuseStep 11416139 = 17124209) B17124209
theorem B571303 : Blo 263822 571303 := bstep (se 1 (by rfl) ⟨428477, by rfl⟩ : syracuseStep 571303 = 856955) B856955
theorem B6470711 : Blo 263822 6470711 := bstep (se 1 (by rfl) ⟨4853033, by rfl⟩ : syracuseStep 6470711 = 9706067) B9706067
theorem B1132987 : Blo 263822 1132987 := bstep (se 1 (by rfl) ⟨849740, by rfl⟩ : syracuseStep 1132987 = 1699481) B1699481
theorem B7621937 : Blo 263822 7621937 := bstep (se 2 (by rfl) ⟨2858226, by rfl⟩ : syracuseStep 7621937 = 5716453) B5716453
theorem B3395681 : Blo 263822 3395681 := bstep (se 2 (by rfl) ⟨1273380, by rfl⟩ : syracuseStep 3395681 = 2546761) B2546761
theorem B1337471 : Blo 263822 1337471 := bstep (se 1 (by rfl) ⟨1003103, by rfl⟩ : syracuseStep 1337471 = 2006207) B2006207
theorem B6451649 : Blo 263822 6451649 := bstep (se 2 (by rfl) ⟨2419368, by rfl⟩ : syracuseStep 6451649 = 4838737) B4838737
theorem B4553333 : Blo 263822 4553333 := bstep (se 5 (by rfl) ⟨213437, by rfl⟩ : syracuseStep 4553333 = 426875) B426875
theorem B5081291 : Blo 263822 5081291 := bstep (se 1 (by rfl) ⟨3810968, by rfl⟩ : syracuseStep 5081291 = 7621937) B7621937
theorem B264431 : Blo 263822 264431 := bstep (se 1 (by rfl) ⟨198323, by rfl⟩ : syracuseStep 264431 = 396647) B396647
theorem B2263787 : Blo 263822 2263787 := bstep (se 1 (by rfl) ⟨1697840, by rfl⟩ : syracuseStep 2263787 = 3395681) B3395681
theorem B1510649 : Blo 263822 1510649 := bstep (se 2 (by rfl) ⟨566493, by rfl⟩ : syracuseStep 1510649 = 1132987) B1132987
theorem B398663 : Blo 263822 398663 := bstep (se 1 (by rfl) ⟨298997, by rfl⟩ : syracuseStep 398663 = 597995) B597995
theorem B399143 : Blo 263822 399143 := bstep (se 1 (by rfl) ⟨299357, by rfl⟩ : syracuseStep 399143 = 598715) B598715
theorem B891647 : Blo 263822 891647 := bstep (se 1 (by rfl) ⟨668735, by rfl⟩ : syracuseStep 891647 = 1337471) B1337471
theorem B761737 : Blo 263822 761737 := bstep (se 2 (by rfl) ⟨285651, by rfl⟩ : syracuseStep 761737 = 571303) B571303
theorem B401567 : Blo 263822 401567 := bstep (se 1 (by rfl) ⟨301175, by rfl⟩ : syracuseStep 401567 = 602351) B602351
theorem B4301099 : Blo 263822 4301099 := bstep (se 1 (by rfl) ⟨3225824, by rfl⟩ : syracuseStep 4301099 = 6451649) B6451649
theorem B7610759 : Blo 263822 7610759 := bstep (se 1 (by rfl) ⟨5708069, by rfl⟩ : syracuseStep 7610759 = 11416139) B11416139
theorem B504863 : Blo 263822 504863 := bstep (se 1 (by rfl) ⟨378647, by rfl⟩ : syracuseStep 504863 = 757295) B757295
theorem B18398123 : Blo 263822 18398123 := bstep (se 1 (by rfl) ⟨13798592, by rfl⟩ : syracuseStep 18398123 = 27597185) B27597185
theorem B3035555 : Blo 263822 3035555 := bstep (se 1 (by rfl) ⟨2276666, by rfl⟩ : syracuseStep 3035555 = 4553333) B4553333
theorem B4313807 : Blo 263822 4313807 := bstep (se 1 (by rfl) ⟨3235355, by rfl⟩ : syracuseStep 4313807 = 6470711) B6470711
theorem B1509191 : Blo 263822 1509191 := bstep (se 1 (by rfl) ⟨1131893, by rfl⟩ : syracuseStep 1509191 = 2263787) B2263787
theorem B265775 : Blo 263822 265775 := bstep (se 1 (by rfl) ⟨199331, by rfl⟩ : syracuseStep 265775 = 398663) B398663
theorem B266095 : Blo 263822 266095 := bstep (se 1 (by rfl) ⟨199571, by rfl⟩ : syracuseStep 266095 = 399143) B399143
theorem B594431 : Blo 263822 594431 := bstep (se 1 (by rfl) ⟨445823, by rfl⟩ : syracuseStep 594431 = 891647) B891647
theorem B267711 : Blo 263822 267711 := bstep (se 1 (by rfl) ⟨200783, by rfl⟩ : syracuseStep 267711 = 401567) B401567
theorem B336575 : Blo 263822 336575 := bstep (se 1 (by rfl) ⟨252431, by rfl⟩ : syracuseStep 336575 = 504863) B504863
theorem B12265415 : Blo 263822 12265415 := bstep (se 1 (by rfl) ⟨9199061, by rfl⟩ : syracuseStep 12265415 = 18398123) B18398123
theorem B3387527 : Blo 263822 3387527 := bstep (se 1 (by rfl) ⟨2540645, by rfl⟩ : syracuseStep 3387527 = 5081291) B5081291
theorem B2867399 : Blo 263822 2867399 := bstep (se 1 (by rfl) ⟨2150549, by rfl⟩ : syracuseStep 2867399 = 4301099) B4301099
theorem B1007099 : Blo 263822 1007099 := bstep (se 1 (by rfl) ⟨755324, by rfl⟩ : syracuseStep 1007099 = 1510649) B1510649
theorem B2023703 : Blo 263822 2023703 := bstep (se 1 (by rfl) ⟨1517777, by rfl⟩ : syracuseStep 2023703 = 3035555) B3035555
theorem B2875871 : Blo 263822 2875871 := bstep (se 1 (by rfl) ⟨2156903, by rfl⟩ : syracuseStep 2875871 = 4313807) B4313807
theorem B5073839 : Blo 263822 5073839 := bstep (se 1 (by rfl) ⟨3805379, by rfl⟩ : syracuseStep 5073839 = 7610759) B7610759
theorem B1015649 : Blo 263822 1015649 := bstep (se 2 (by rfl) ⟨380868, by rfl⟩ : syracuseStep 1015649 = 761737) B761737
theorem B7668989 : Blo 263822 7668989 := bstep (se 3 (by rfl) ⟨1437935, by rfl⟩ : syracuseStep 7668989 = 2875871) B2875871
theorem B396287 : Blo 263822 396287 := bstep (se 1 (by rfl) ⟨297215, by rfl⟩ : syracuseStep 396287 = 594431) B594431
theorem B1349135 : Blo 263822 1349135 := bstep (se 1 (by rfl) ⟨1011851, by rfl⟩ : syracuseStep 1349135 = 2023703) B2023703
theorem B3382559 : Blo 263822 3382559 := bstep (se 1 (by rfl) ⟨2536919, by rfl⟩ : syracuseStep 3382559 = 5073839) B5073839
theorem B1911599 : Blo 263822 1911599 := bstep (se 1 (by rfl) ⟨1433699, by rfl⟩ : syracuseStep 1911599 = 2867399) B2867399
theorem B897533 : Blo 263822 897533 := bstep (se 3 (by rfl) ⟨168287, by rfl⟩ : syracuseStep 897533 = 336575) B336575
theorem B671399 : Blo 263822 671399 := bstep (se 1 (by rfl) ⟨503549, by rfl⟩ : syracuseStep 671399 = 1007099) B1007099
theorem B8176943 : Blo 263822 8176943 := bstep (se 1 (by rfl) ⟨6132707, by rfl⟩ : syracuseStep 8176943 = 12265415) B12265415
theorem B677099 : Blo 263822 677099 := bstep (se 1 (by rfl) ⟨507824, by rfl⟩ : syracuseStep 677099 = 1015649) B1015649
theorem B1006127 : Blo 263822 1006127 := bstep (se 1 (by rfl) ⟨754595, by rfl⟩ : syracuseStep 1006127 = 1509191) B1509191
theorem B2258351 : Blo 263822 2258351 := bstep (se 1 (by rfl) ⟨1693763, by rfl⟩ : syracuseStep 2258351 = 3387527) B3387527
theorem B5112659 : Blo 263822 5112659 := bstep (se 1 (by rfl) ⟨3834494, by rfl⟩ : syracuseStep 5112659 = 7668989) B7668989
theorem B264191 : Blo 263822 264191 := bstep (se 1 (by rfl) ⟨198143, by rfl⟩ : syracuseStep 264191 = 396287) B396287
theorem B598355 : Blo 263822 598355 := bstep (se 1 (by rfl) ⟨448766, by rfl⟩ : syracuseStep 598355 = 897533) B897533
theorem B5451295 : Blo 263822 5451295 := bstep (se 1 (by rfl) ⟨4088471, by rfl⟩ : syracuseStep 5451295 = 8176943) B8176943
theorem B899423 : Blo 263822 899423 := bstep (se 1 (by rfl) ⟨674567, by rfl⟩ : syracuseStep 899423 = 1349135) B1349135
theorem B670751 : Blo 263822 670751 := bstep (se 1 (by rfl) ⟨503063, by rfl⟩ : syracuseStep 670751 = 1006127) B1006127
theorem B447599 : Blo 263822 447599 := bstep (se 1 (by rfl) ⟨335699, by rfl⟩ : syracuseStep 447599 = 671399) B671399
theorem B451399 : Blo 263822 451399 := bstep (se 1 (by rfl) ⟨338549, by rfl⟩ : syracuseStep 451399 = 677099) B677099
theorem B2255039 : Blo 263822 2255039 := bstep (se 1 (by rfl) ⟨1691279, by rfl⟩ : syracuseStep 2255039 = 3382559) B3382559
theorem B1274399 : Blo 263822 1274399 := bstep (se 1 (by rfl) ⟨955799, by rfl⟩ : syracuseStep 1274399 = 1911599) B1911599
theorem B1505567 : Blo 263822 1505567 := bstep (se 1 (by rfl) ⟨1129175, by rfl⟩ : syracuseStep 1505567 = 2258351) B2258351
theorem B3408439 : Blo 263822 3408439 := bstep (se 1 (by rfl) ⟨2556329, by rfl⟩ : syracuseStep 3408439 = 5112659) B5112659
theorem B298399 : Blo 263822 298399 := bstep (se 1 (by rfl) ⟨223799, by rfl⟩ : syracuseStep 298399 = 447599) B447599
theorem B398903 : Blo 263822 398903 := bstep (se 1 (by rfl) ⟨299177, by rfl⟩ : syracuseStep 398903 = 598355) B598355
theorem B599615 : Blo 263822 599615 := bstep (se 1 (by rfl) ⟨449711, by rfl⟩ : syracuseStep 599615 = 899423) B899423
theorem B601865 : Blo 263822 601865 := bstep (se 2 (by rfl) ⟨225699, by rfl⟩ : syracuseStep 601865 = 451399) B451399
theorem B1003711 : Blo 263822 1003711 := bstep (se 1 (by rfl) ⟨752783, by rfl⟩ : syracuseStep 1003711 = 1505567) B1505567
theorem B447167 : Blo 263822 447167 := bstep (se 1 (by rfl) ⟨335375, by rfl⟩ : syracuseStep 447167 = 670751) B670751
theorem B7268393 : Blo 263822 7268393 := bstep (se 2 (by rfl) ⟨2725647, by rfl⟩ : syracuseStep 7268393 = 5451295) B5451295
theorem B1503359 : Blo 263822 1503359 := bstep (se 1 (by rfl) ⟨1127519, by rfl⟩ : syracuseStep 1503359 = 2255039) B2255039
theorem B849599 : Blo 263822 849599 := bstep (se 1 (by rfl) ⟨637199, by rfl⟩ : syracuseStep 849599 = 1274399) B1274399
theorem B298111 : Blo 263822 298111 := bstep (se 1 (by rfl) ⟨223583, by rfl⟩ : syracuseStep 298111 = 447167) B447167
theorem B265935 : Blo 263822 265935 := bstep (se 1 (by rfl) ⟨199451, by rfl⟩ : syracuseStep 265935 = 398903) B398903
theorem B397865 : Blo 263822 397865 := bstep (se 2 (by rfl) ⟨149199, by rfl⟩ : syracuseStep 397865 = 298399) B298399
theorem B399743 : Blo 263822 399743 := bstep (se 1 (by rfl) ⟨299807, by rfl⟩ : syracuseStep 399743 = 599615) B599615
theorem B401243 : Blo 263822 401243 := bstep (se 1 (by rfl) ⟨300932, by rfl⟩ : syracuseStep 401243 = 601865) B601865
theorem B566399 : Blo 263822 566399 := bstep (se 1 (by rfl) ⟨424799, by rfl⟩ : syracuseStep 566399 = 849599) B849599
theorem B1002239 : Blo 263822 1002239 := bstep (se 1 (by rfl) ⟨751679, by rfl⟩ : syracuseStep 1002239 = 1503359) B1503359
theorem B4544585 : Blo 263822 4544585 := bstep (se 2 (by rfl) ⟨1704219, by rfl⟩ : syracuseStep 4544585 = 3408439) B3408439
theorem B1338281 : Blo 263822 1338281 := bstep (se 2 (by rfl) ⟨501855, by rfl⟩ : syracuseStep 1338281 = 1003711) B1003711
theorem B4845595 : Blo 263822 4845595 := bstep (se 1 (by rfl) ⟨3634196, by rfl⟩ : syracuseStep 4845595 = 7268393) B7268393
theorem B1510397 : Blo 263822 1510397 := bstep (se 3 (by rfl) ⟨283199, by rfl⟩ : syracuseStep 1510397 = 566399) B566399
theorem B265243 : Blo 263822 265243 := bstep (se 1 (by rfl) ⟨198932, by rfl⟩ : syracuseStep 265243 = 397865) B397865
theorem B397481 : Blo 263822 397481 := bstep (se 2 (by rfl) ⟨149055, by rfl⟩ : syracuseStep 397481 = 298111) B298111
theorem B266495 : Blo 263822 266495 := bstep (se 1 (by rfl) ⟨199871, by rfl⟩ : syracuseStep 266495 = 399743) B399743
theorem B267495 : Blo 263822 267495 := bstep (se 1 (by rfl) ⟨200621, by rfl⟩ : syracuseStep 267495 = 401243) B401243
theorem B6460793 : Blo 263822 6460793 := bstep (se 2 (by rfl) ⟨2422797, by rfl⟩ : syracuseStep 6460793 = 4845595) B4845595
theorem B892187 : Blo 263822 892187 := bstep (se 1 (by rfl) ⟨669140, by rfl⟩ : syracuseStep 892187 = 1338281) B1338281
theorem B668159 : Blo 263822 668159 := bstep (se 1 (by rfl) ⟨501119, by rfl⟩ : syracuseStep 668159 = 1002239) B1002239
theorem B3029723 : Blo 263822 3029723 := bstep (se 1 (by rfl) ⟨2272292, by rfl⟩ : syracuseStep 3029723 = 4544585) B4544585
theorem B264987 : Blo 263822 264987 := bstep (se 1 (by rfl) ⟨198740, by rfl⟩ : syracuseStep 264987 = 397481) B397481
theorem B594791 : Blo 263822 594791 := bstep (se 1 (by rfl) ⟨446093, by rfl⟩ : syracuseStep 594791 = 892187) B892187
theorem B4307195 : Blo 263822 4307195 := bstep (se 1 (by rfl) ⟨3230396, by rfl⟩ : syracuseStep 4307195 = 6460793) B6460793
theorem B445439 : Blo 263822 445439 := bstep (se 1 (by rfl) ⟨334079, by rfl⟩ : syracuseStep 445439 = 668159) B668159
theorem B2019815 : Blo 263822 2019815 := bstep (se 1 (by rfl) ⟨1514861, by rfl⟩ : syracuseStep 2019815 = 3029723) B3029723
theorem B1006931 : Blo 263822 1006931 := bstep (se 1 (by rfl) ⟨755198, by rfl⟩ : syracuseStep 1006931 = 1510397) B1510397
theorem B296959 : Blo 263822 296959 := bstep (se 1 (by rfl) ⟨222719, by rfl⟩ : syracuseStep 296959 = 445439) B445439
theorem B1346543 : Blo 263822 1346543 := bstep (se 1 (by rfl) ⟨1009907, by rfl⟩ : syracuseStep 1346543 = 2019815) B2019815
theorem B396527 : Blo 263822 396527 := bstep (se 1 (by rfl) ⟨297395, by rfl⟩ : syracuseStep 396527 = 594791) B594791
theorem B671287 : Blo 263822 671287 := bstep (se 1 (by rfl) ⟨503465, by rfl⟩ : syracuseStep 671287 = 1006931) B1006931
theorem B2871463 : Blo 263822 2871463 := bstep (se 1 (by rfl) ⟨2153597, by rfl⟩ : syracuseStep 2871463 = 4307195) B4307195
theorem B264351 : Blo 263822 264351 := bstep (se 1 (by rfl) ⟨198263, by rfl⟩ : syracuseStep 264351 = 396527) B396527
theorem B395945 : Blo 263822 395945 := bstep (se 2 (by rfl) ⟨148479, by rfl⟩ : syracuseStep 395945 = 296959) B296959
theorem B895049 : Blo 263822 895049 := bstep (se 2 (by rfl) ⟨335643, by rfl⟩ : syracuseStep 895049 = 671287) B671287
theorem B897695 : Blo 263822 897695 := bstep (se 1 (by rfl) ⟨673271, by rfl⟩ : syracuseStep 897695 = 1346543) B1346543
theorem B3828617 : Blo 263822 3828617 := bstep (se 2 (by rfl) ⟨1435731, by rfl⟩ : syracuseStep 3828617 = 2871463) B2871463
theorem B263963 : Blo 263822 263963 := bstep (se 1 (by rfl) ⟨197972, by rfl⟩ : syracuseStep 263963 = 395945) B395945
theorem B596699 : Blo 263822 596699 := bstep (se 1 (by rfl) ⟨447524, by rfl⟩ : syracuseStep 596699 = 895049) B895049
theorem B598463 : Blo 263822 598463 := bstep (se 1 (by rfl) ⟨448847, by rfl⟩ : syracuseStep 598463 = 897695) B897695
theorem B2552411 : Blo 263822 2552411 := bstep (se 1 (by rfl) ⟨1914308, by rfl⟩ : syracuseStep 2552411 = 3828617) B3828617
theorem B397799 : Blo 263822 397799 := bstep (se 1 (by rfl) ⟨298349, by rfl⟩ : syracuseStep 397799 = 596699) B596699
theorem B398975 : Blo 263822 398975 := bstep (se 1 (by rfl) ⟨299231, by rfl⟩ : syracuseStep 398975 = 598463) B598463
theorem B1701607 : Blo 263822 1701607 := bstep (se 1 (by rfl) ⟨1276205, by rfl⟩ : syracuseStep 1701607 = 2552411) B2552411
theorem B265199 : Blo 263822 265199 := bstep (se 1 (by rfl) ⟨198899, by rfl⟩ : syracuseStep 265199 = 397799) B397799
theorem B265983 : Blo 263822 265983 := bstep (se 1 (by rfl) ⟨199487, by rfl⟩ : syracuseStep 265983 = 398975) B398975
theorem B2268809 : Blo 263822 2268809 := bstep (se 2 (by rfl) ⟨850803, by rfl⟩ : syracuseStep 2268809 = 1701607) B1701607
theorem B1512539 : Blo 263822 1512539 := bstep (se 1 (by rfl) ⟨1134404, by rfl⟩ : syracuseStep 1512539 = 2268809) B2268809
theorem B1008359 : Blo 263822 1008359 := bstep (se 1 (by rfl) ⟨756269, by rfl⟩ : syracuseStep 1008359 = 1512539) B1512539
theorem B672239 : Blo 263822 672239 := bstep (se 1 (by rfl) ⟨504179, by rfl⟩ : syracuseStep 672239 = 1008359) B1008359
theorem B448159 : Blo 263822 448159 := bstep (se 1 (by rfl) ⟨336119, by rfl⟩ : syracuseStep 448159 = 672239) B672239
theorem B597545 : Blo 263822 597545 := bstep (se 2 (by rfl) ⟨224079, by rfl⟩ : syracuseStep 597545 = 448159) B448159
theorem B398363 : Blo 263822 398363 := bstep (se 1 (by rfl) ⟨298772, by rfl⟩ : syracuseStep 398363 = 597545) B597545
theorem B265575 : Blo 263822 265575 := bstep (se 1 (by rfl) ⟨199181, by rfl⟩ : syracuseStep 265575 = 398363) B398363

theorem C0 (j : ℕ) (h1 : 65955 ≤ j) (h2 : j ≤ 66654) : Blo 263822 (4 * j + 3) := by
  interval_cases j
  · exact B263823
  · exact B263827
  · exact B263831
  · exact B263835
  · exact B263839
  · exact B263843
  · exact B263847
  · exact B263851
  · exact B263855
  · exact B263859
  · exact B263863
  · exact B263867
  · exact B263871
  · exact B263875
  · exact B263879
  · exact B263883
  · exact B263887
  · exact B263891
  · exact B263895
  · exact B263899
  · exact B263903
  · exact B263907
  · exact B263911
  · exact B263915
  · exact B263919
  · exact B263923
  · exact B263927
  · exact B263931
  · exact B263935
  · exact B263939
  · exact B263943
  · exact B263947
  · exact B263951
  · exact B263955
  · exact B263959
  · exact B263963
  · exact B263967
  · exact B263971
  · exact B263975
  · exact B263979
  · exact B263983
  · exact B263987
  · exact B263991
  · exact B263995
  · exact B263999
  · exact B264003
  · exact B264007
  · exact B264011
  · exact B264015
  · exact B264019
  · exact B264023
  · exact B264027
  · exact B264031
  · exact B264035
  · exact B264039
  · exact B264043
  · exact B264047
  · exact B264051
  · exact B264055
  · exact B264059
  · exact B264063
  · exact B264067
  · exact B264071
  · exact B264075
  · exact B264079
  · exact B264083
  · exact B264087
  · exact B264091
  · exact B264095
  · exact B264099
  · exact B264103
  · exact B264107
  · exact B264111
  · exact B264115
  · exact B264119
  · exact B264123
  · exact B264127
  · exact B264131
  · exact B264135
  · exact B264139
  · exact B264143
  · exact B264147
  · exact B264151
  · exact B264155
  · exact B264159
  · exact B264163
  · exact B264167
  · exact B264171
  · exact B264175
  · exact B264179
  · exact B264183
  · exact B264187
  · exact B264191
  · exact B264195
  · exact B264199
  · exact B264203
  · exact B264207
  · exact B264211
  · exact B264215
  · exact B264219
  · exact B264223
  · exact B264227
  · exact B264231
  · exact B264235
  · exact B264239
  · exact B264243
  · exact B264247
  · exact B264251
  · exact B264255
  · exact B264259
  · exact B264263
  · exact B264267
  · exact B264271
  · exact B264275
  · exact B264279
  · exact B264283
  · exact B264287
  · exact B264291
  · exact B264295
  · exact B264299
  · exact B264303
  · exact B264307
  · exact B264311
  · exact B264315
  · exact B264319
  · exact B264323
  · exact B264327
  · exact B264331
  · exact B264335
  · exact B264339
  · exact B264343
  · exact B264347
  · exact B264351
  · exact B264355
  · exact B264359
  · exact B264363
  · exact B264367
  · exact B264371
  · exact B264375
  · exact B264379
  · exact B264383
  · exact B264387
  · exact B264391
  · exact B264395
  · exact B264399
  · exact B264403
  · exact B264407
  · exact B264411
  · exact B264415
  · exact B264419
  · exact B264423
  · exact B264427
  · exact B264431
  · exact B264435
  · exact B264439
  · exact B264443
  · exact B264447
  · exact B264451
  · exact B264455
  · exact B264459
  · exact B264463
  · exact B264467
  · exact B264471
  · exact B264475
  · exact B264479
  · exact B264483
  · exact B264487
  · exact B264491
  · exact B264495
  · exact B264499
  · exact B264503
  · exact B264507
  · exact B264511
  · exact B264515
  · exact B264519
  · exact B264523
  · exact B264527
  · exact B264531
  · exact B264535
  · exact B264539
  · exact B264543
  · exact B264547
  · exact B264551
  · exact B264555
  · exact B264559
  · exact B264563
  · exact B264567
  · exact B264571
  · exact B264575
  · exact B264579
  · exact B264583
  · exact B264587
  · exact B264591
  · exact B264595
  · exact B264599
  · exact B264603
  · exact B264607
  · exact B264611
  · exact B264615
  · exact B264619
  · exact B264623
  · exact B264627
  · exact B264631
  · exact B264635
  · exact B264639
  · exact B264643
  · exact B264647
  · exact B264651
  · exact B264655
  · exact B264659
  · exact B264663
  · exact B264667
  · exact B264671
  · exact B264675
  · exact B264679
  · exact B264683
  · exact B264687
  · exact B264691
  · exact B264695
  · exact B264699
  · exact B264703
  · exact B264707
  · exact B264711
  · exact B264715
  · exact B264719
  · exact B264723
  · exact B264727
  · exact B264731
  · exact B264735
  · exact B264739
  · exact B264743
  · exact B264747
  · exact B264751
  · exact B264755
  · exact B264759
  · exact B264763
  · exact B264767
  · exact B264771
  · exact B264775
  · exact B264779
  · exact B264783
  · exact B264787
  · exact B264791
  · exact B264795
  · exact B264799
  · exact B264803
  · exact B264807
  · exact B264811
  · exact B264815
  · exact B264819
  · exact B264823
  · exact B264827
  · exact B264831
  · exact B264835
  · exact B264839
  · exact B264843
  · exact B264847
  · exact B264851
  · exact B264855
  · exact B264859
  · exact B264863
  · exact B264867
  · exact B264871
  · exact B264875
  · exact B264879
  · exact B264883
  · exact B264887
  · exact B264891
  · exact B264895
  · exact B264899
  · exact B264903
  · exact B264907
  · exact B264911
  · exact B264915
  · exact B264919
  · exact B264923
  · exact B264927
  · exact B264931
  · exact B264935
  · exact B264939
  · exact B264943
  · exact B264947
  · exact B264951
  · exact B264955
  · exact B264959
  · exact B264963
  · exact B264967
  · exact B264971
  · exact B264975
  · exact B264979
  · exact B264983
  · exact B264987
  · exact B264991
  · exact B264995
  · exact B264999
  · exact B265003
  · exact B265007
  · exact B265011
  · exact B265015
  · exact B265019
  · exact B265023
  · exact B265027
  · exact B265031
  · exact B265035
  · exact B265039
  · exact B265043
  · exact B265047
  · exact B265051
  · exact B265055
  · exact B265059
  · exact B265063
  · exact B265067
  · exact B265071
  · exact B265075
  · exact B265079
  · exact B265083
  · exact B265087
  · exact B265091
  · exact B265095
  · exact B265099
  · exact B265103
  · exact B265107
  · exact B265111
  · exact B265115
  · exact B265119
  · exact B265123
  · exact B265127
  · exact B265131
  · exact B265135
  · exact B265139
  · exact B265143
  · exact B265147
  · exact B265151
  · exact B265155
  · exact B265159
  · exact B265163
  · exact B265167
  · exact B265171
  · exact B265175
  · exact B265179
  · exact B265183
  · exact B265187
  · exact B265191
  · exact B265195
  · exact B265199
  · exact B265203
  · exact B265207
  · exact B265211
  · exact B265215
  · exact B265219
  · exact B265223
  · exact B265227
  · exact B265231
  · exact B265235
  · exact B265239
  · exact B265243
  · exact B265247
  · exact B265251
  · exact B265255
  · exact B265259
  · exact B265263
  · exact B265267
  · exact B265271
  · exact B265275
  · exact B265279
  · exact B265283
  · exact B265287
  · exact B265291
  · exact B265295
  · exact B265299
  · exact B265303
  · exact B265307
  · exact B265311
  · exact B265315
  · exact B265319
  · exact B265323
  · exact B265327
  · exact B265331
  · exact B265335
  · exact B265339
  · exact B265343
  · exact B265347
  · exact B265351
  · exact B265355
  · exact B265359
  · exact B265363
  · exact B265367
  · exact B265371
  · exact B265375
  · exact B265379
  · exact B265383
  · exact B265387
  · exact B265391
  · exact B265395
  · exact B265399
  · exact B265403
  · exact B265407
  · exact B265411
  · exact B265415
  · exact B265419
  · exact B265423
  · exact B265427
  · exact B265431
  · exact B265435
  · exact B265439
  · exact B265443
  · exact B265447
  · exact B265451
  · exact B265455
  · exact B265459
  · exact B265463
  · exact B265467
  · exact B265471
  · exact B265475
  · exact B265479
  · exact B265483
  · exact B265487
  · exact B265491
  · exact B265495
  · exact B265499
  · exact B265503
  · exact B265507
  · exact B265511
  · exact B265515
  · exact B265519
  · exact B265523
  · exact B265527
  · exact B265531
  · exact B265535
  · exact B265539
  · exact B265543
  · exact B265547
  · exact B265551
  · exact B265555
  · exact B265559
  · exact B265563
  · exact B265567
  · exact B265571
  · exact B265575
  · exact B265579
  · exact B265583
  · exact B265587
  · exact B265591
  · exact B265595
  · exact B265599
  · exact B265603
  · exact B265607
  · exact B265611
  · exact B265615
  · exact B265619
  · exact B265623
  · exact B265627
  · exact B265631
  · exact B265635
  · exact B265639
  · exact B265643
  · exact B265647
  · exact B265651
  · exact B265655
  · exact B265659
  · exact B265663
  · exact B265667
  · exact B265671
  · exact B265675
  · exact B265679
  · exact B265683
  · exact B265687
  · exact B265691
  · exact B265695
  · exact B265699
  · exact B265703
  · exact B265707
  · exact B265711
  · exact B265715
  · exact B265719
  · exact B265723
  · exact B265727
  · exact B265731
  · exact B265735
  · exact B265739
  · exact B265743
  · exact B265747
  · exact B265751
  · exact B265755
  · exact B265759
  · exact B265763
  · exact B265767
  · exact B265771
  · exact B265775
  · exact B265779
  · exact B265783
  · exact B265787
  · exact B265791
  · exact B265795
  · exact B265799
  · exact B265803
  · exact B265807
  · exact B265811
  · exact B265815
  · exact B265819
  · exact B265823
  · exact B265827
  · exact B265831
  · exact B265835
  · exact B265839
  · exact B265843
  · exact B265847
  · exact B265851
  · exact B265855
  · exact B265859
  · exact B265863
  · exact B265867
  · exact B265871
  · exact B265875
  · exact B265879
  · exact B265883
  · exact B265887
  · exact B265891
  · exact B265895
  · exact B265899
  · exact B265903
  · exact B265907
  · exact B265911
  · exact B265915
  · exact B265919
  · exact B265923
  · exact B265927
  · exact B265931
  · exact B265935
  · exact B265939
  · exact B265943
  · exact B265947
  · exact B265951
  · exact B265955
  · exact B265959
  · exact B265963
  · exact B265967
  · exact B265971
  · exact B265975
  · exact B265979
  · exact B265983
  · exact B265987
  · exact B265991
  · exact B265995
  · exact B265999
  · exact B266003
  · exact B266007
  · exact B266011
  · exact B266015
  · exact B266019
  · exact B266023
  · exact B266027
  · exact B266031
  · exact B266035
  · exact B266039
  · exact B266043
  · exact B266047
  · exact B266051
  · exact B266055
  · exact B266059
  · exact B266063
  · exact B266067
  · exact B266071
  · exact B266075
  · exact B266079
  · exact B266083
  · exact B266087
  · exact B266091
  · exact B266095
  · exact B266099
  · exact B266103
  · exact B266107
  · exact B266111
  · exact B266115
  · exact B266119
  · exact B266123
  · exact B266127
  · exact B266131
  · exact B266135
  · exact B266139
  · exact B266143
  · exact B266147
  · exact B266151
  · exact B266155
  · exact B266159
  · exact B266163
  · exact B266167
  · exact B266171
  · exact B266175
  · exact B266179
  · exact B266183
  · exact B266187
  · exact B266191
  · exact B266195
  · exact B266199
  · exact B266203
  · exact B266207
  · exact B266211
  · exact B266215
  · exact B266219
  · exact B266223
  · exact B266227
  · exact B266231
  · exact B266235
  · exact B266239
  · exact B266243
  · exact B266247
  · exact B266251
  · exact B266255
  · exact B266259
  · exact B266263
  · exact B266267
  · exact B266271
  · exact B266275
  · exact B266279
  · exact B266283
  · exact B266287
  · exact B266291
  · exact B266295
  · exact B266299
  · exact B266303
  · exact B266307
  · exact B266311
  · exact B266315
  · exact B266319
  · exact B266323
  · exact B266327
  · exact B266331
  · exact B266335
  · exact B266339
  · exact B266343
  · exact B266347
  · exact B266351
  · exact B266355
  · exact B266359
  · exact B266363
  · exact B266367
  · exact B266371
  · exact B266375
  · exact B266379
  · exact B266383
  · exact B266387
  · exact B266391
  · exact B266395
  · exact B266399
  · exact B266403
  · exact B266407
  · exact B266411
  · exact B266415
  · exact B266419
  · exact B266423
  · exact B266427
  · exact B266431
  · exact B266435
  · exact B266439
  · exact B266443
  · exact B266447
  · exact B266451
  · exact B266455
  · exact B266459
  · exact B266463
  · exact B266467
  · exact B266471
  · exact B266475
  · exact B266479
  · exact B266483
  · exact B266487
  · exact B266491
  · exact B266495
  · exact B266499
  · exact B266503
  · exact B266507
  · exact B266511
  · exact B266515
  · exact B266519
  · exact B266523
  · exact B266527
  · exact B266531
  · exact B266535
  · exact B266539
  · exact B266543
  · exact B266547
  · exact B266551
  · exact B266555
  · exact B266559
  · exact B266563
  · exact B266567
  · exact B266571
  · exact B266575
  · exact B266579
  · exact B266583
  · exact B266587
  · exact B266591
  · exact B266595
  · exact B266599
  · exact B266603
  · exact B266607
  · exact B266611
  · exact B266615
  · exact B266619

theorem C1 (j : ℕ) (h1 : 66655 ≤ j) (h2 : j ≤ 66954) : Blo 263822 (4 * j + 3) := by
  interval_cases j
  · exact B266623
  · exact B266627
  · exact B266631
  · exact B266635
  · exact B266639
  · exact B266643
  · exact B266647
  · exact B266651
  · exact B266655
  · exact B266659
  · exact B266663
  · exact B266667
  · exact B266671
  · exact B266675
  · exact B266679
  · exact B266683
  · exact B266687
  · exact B266691
  · exact B266695
  · exact B266699
  · exact B266703
  · exact B266707
  · exact B266711
  · exact B266715
  · exact B266719
  · exact B266723
  · exact B266727
  · exact B266731
  · exact B266735
  · exact B266739
  · exact B266743
  · exact B266747
  · exact B266751
  · exact B266755
  · exact B266759
  · exact B266763
  · exact B266767
  · exact B266771
  · exact B266775
  · exact B266779
  · exact B266783
  · exact B266787
  · exact B266791
  · exact B266795
  · exact B266799
  · exact B266803
  · exact B266807
  · exact B266811
  · exact B266815
  · exact B266819
  · exact B266823
  · exact B266827
  · exact B266831
  · exact B266835
  · exact B266839
  · exact B266843
  · exact B266847
  · exact B266851
  · exact B266855
  · exact B266859
  · exact B266863
  · exact B266867
  · exact B266871
  · exact B266875
  · exact B266879
  · exact B266883
  · exact B266887
  · exact B266891
  · exact B266895
  · exact B266899
  · exact B266903
  · exact B266907
  · exact B266911
  · exact B266915
  · exact B266919
  · exact B266923
  · exact B266927
  · exact B266931
  · exact B266935
  · exact B266939
  · exact B266943
  · exact B266947
  · exact B266951
  · exact B266955
  · exact B266959
  · exact B266963
  · exact B266967
  · exact B266971
  · exact B266975
  · exact B266979
  · exact B266983
  · exact B266987
  · exact B266991
  · exact B266995
  · exact B266999
  · exact B267003
  · exact B267007
  · exact B267011
  · exact B267015
  · exact B267019
  · exact B267023
  · exact B267027
  · exact B267031
  · exact B267035
  · exact B267039
  · exact B267043
  · exact B267047
  · exact B267051
  · exact B267055
  · exact B267059
  · exact B267063
  · exact B267067
  · exact B267071
  · exact B267075
  · exact B267079
  · exact B267083
  · exact B267087
  · exact B267091
  · exact B267095
  · exact B267099
  · exact B267103
  · exact B267107
  · exact B267111
  · exact B267115
  · exact B267119
  · exact B267123
  · exact B267127
  · exact B267131
  · exact B267135
  · exact B267139
  · exact B267143
  · exact B267147
  · exact B267151
  · exact B267155
  · exact B267159
  · exact B267163
  · exact B267167
  · exact B267171
  · exact B267175
  · exact B267179
  · exact B267183
  · exact B267187
  · exact B267191
  · exact B267195
  · exact B267199
  · exact B267203
  · exact B267207
  · exact B267211
  · exact B267215
  · exact B267219
  · exact B267223
  · exact B267227
  · exact B267231
  · exact B267235
  · exact B267239
  · exact B267243
  · exact B267247
  · exact B267251
  · exact B267255
  · exact B267259
  · exact B267263
  · exact B267267
  · exact B267271
  · exact B267275
  · exact B267279
  · exact B267283
  · exact B267287
  · exact B267291
  · exact B267295
  · exact B267299
  · exact B267303
  · exact B267307
  · exact B267311
  · exact B267315
  · exact B267319
  · exact B267323
  · exact B267327
  · exact B267331
  · exact B267335
  · exact B267339
  · exact B267343
  · exact B267347
  · exact B267351
  · exact B267355
  · exact B267359
  · exact B267363
  · exact B267367
  · exact B267371
  · exact B267375
  · exact B267379
  · exact B267383
  · exact B267387
  · exact B267391
  · exact B267395
  · exact B267399
  · exact B267403
  · exact B267407
  · exact B267411
  · exact B267415
  · exact B267419
  · exact B267423
  · exact B267427
  · exact B267431
  · exact B267435
  · exact B267439
  · exact B267443
  · exact B267447
  · exact B267451
  · exact B267455
  · exact B267459
  · exact B267463
  · exact B267467
  · exact B267471
  · exact B267475
  · exact B267479
  · exact B267483
  · exact B267487
  · exact B267491
  · exact B267495
  · exact B267499
  · exact B267503
  · exact B267507
  · exact B267511
  · exact B267515
  · exact B267519
  · exact B267523
  · exact B267527
  · exact B267531
  · exact B267535
  · exact B267539
  · exact B267543
  · exact B267547
  · exact B267551
  · exact B267555
  · exact B267559
  · exact B267563
  · exact B267567
  · exact B267571
  · exact B267575
  · exact B267579
  · exact B267583
  · exact B267587
  · exact B267591
  · exact B267595
  · exact B267599
  · exact B267603
  · exact B267607
  · exact B267611
  · exact B267615
  · exact B267619
  · exact B267623
  · exact B267627
  · exact B267631
  · exact B267635
  · exact B267639
  · exact B267643
  · exact B267647
  · exact B267651
  · exact B267655
  · exact B267659
  · exact B267663
  · exact B267667
  · exact B267671
  · exact B267675
  · exact B267679
  · exact B267683
  · exact B267687
  · exact B267691
  · exact B267695
  · exact B267699
  · exact B267703
  · exact B267707
  · exact B267711
  · exact B267715
  · exact B267719
  · exact B267723
  · exact B267727
  · exact B267731
  · exact B267735
  · exact B267739
  · exact B267743
  · exact B267747
  · exact B267751
  · exact B267755
  · exact B267759
  · exact B267763
  · exact B267767
  · exact B267771
  · exact B267775
  · exact B267779
  · exact B267783
  · exact B267787
  · exact B267791
  · exact B267795
  · exact B267799
  · exact B267803
  · exact B267807
  · exact B267811
  · exact B267815
  · exact B267819

theorem solution (m : ℕ) (hlo : 263822 ≤ m) (hhi : m ≤ 267822) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 65955 ≤ j := by omega
    have hj2 : j ≤ 66954 := by omega
    have hb : Blo 263822 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 66655 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
