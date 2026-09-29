-- Prove2me | solution 1 for syracuse_descends_range_235815_239815
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:59.692685+00:00
-- url     : https://prove2.me/submissions/bbeba7ee-1b9e-4d1f-a385-6a5a890c11bb

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


theorem B983125 : Blo 235815 983125 := bbase (se 8 (by rfl) ⟨5760, by rfl⟩ : syracuseStep 983125 = 11521) (by norm_num)
theorem B4063445 : Blo 235815 4063445 := bbase (se 7 (by rfl) ⟨47618, by rfl⟩ : syracuseStep 4063445 = 95237) (by norm_num)
theorem B360821 : Blo 235815 360821 := bbase (se 5 (by rfl) ⟨16913, by rfl⟩ : syracuseStep 360821 = 33827) (by norm_num)
theorem B3277205 : Blo 235815 3277205 := bbase (se 6 (by rfl) ⟨76809, by rfl⟩ : syracuseStep 3277205 = 153619) (by norm_num)
theorem B721349 : Blo 235815 721349 := bbase (se 4 (by rfl) ⟨67626, by rfl⟩ : syracuseStep 721349 = 135253) (by norm_num)
theorem B262769 : Blo 235815 262769 := bbase (se 2 (by rfl) ⟨98538, by rfl⟩ : syracuseStep 262769 = 197077) (by norm_num)
theorem B361117 : Blo 235815 361117 := bbase (se 3 (by rfl) ⟨67709, by rfl⟩ : syracuseStep 361117 = 135419) (by norm_num)
theorem B426773 : Blo 235815 426773 := bbase (se 6 (by rfl) ⟨10002, by rfl⟩ : syracuseStep 426773 = 20005) (by norm_num)
theorem B1147765 : Blo 235815 1147765 := bbase (se 5 (by rfl) ⟨53801, by rfl⟩ : syracuseStep 1147765 = 107603) (by norm_num)
theorem B1344437 : Blo 235815 1344437 := bbase (se 5 (by rfl) ⟨63020, by rfl⟩ : syracuseStep 1344437 = 126041) (by norm_num)
theorem B1213541 : Blo 235815 1213541 := bbase (se 4 (by rfl) ⟨113769, by rfl⟩ : syracuseStep 1213541 = 227539) (by norm_num)
theorem B787573 : Blo 235815 787573 := bbase (se 5 (by rfl) ⟨36917, by rfl⟩ : syracuseStep 787573 = 73835) (by norm_num)
theorem B1836533 : Blo 235815 1836533 := bbase (se 5 (by rfl) ⟨86087, by rfl⟩ : syracuseStep 1836533 = 172175) (by norm_num)
theorem B1312405 : Blo 235815 1312405 := bbase (se 6 (by rfl) ⟨30759, by rfl⟩ : syracuseStep 1312405 = 61519) (by norm_num)
theorem B362285 : Blo 235815 362285 := bbase (se 3 (by rfl) ⟨67928, by rfl⟩ : syracuseStep 362285 = 135857) (by norm_num)
theorem B1640245 : Blo 235815 1640245 := bbase (se 5 (by rfl) ⟨76886, by rfl⟩ : syracuseStep 1640245 = 153773) (by norm_num)
theorem B427933 : Blo 235815 427933 := bbase (se 3 (by rfl) ⟨80237, by rfl⟩ : syracuseStep 427933 = 160475) (by norm_num)
theorem B460733 : Blo 235815 460733 := bbase (se 3 (by rfl) ⟨86387, by rfl⟩ : syracuseStep 460733 = 172775) (by norm_num)
theorem B755669 : Blo 235815 755669 := bbase (se 7 (by rfl) ⟨8855, by rfl⟩ : syracuseStep 755669 = 17711) (by norm_num)
theorem B1017845 : Blo 235815 1017845 := bbase (se 5 (by rfl) ⟨47711, by rfl⟩ : syracuseStep 1017845 = 95423) (by norm_num)
theorem B428237 : Blo 235815 428237 := bbase (se 3 (by rfl) ⟨80294, by rfl⟩ : syracuseStep 428237 = 160589) (by norm_num)
theorem B854309 : Blo 235815 854309 := bbase (se 4 (by rfl) ⟨80091, by rfl⟩ : syracuseStep 854309 = 160183) (by norm_num)
theorem B1215157 : Blo 235815 1215157 := bbase (se 5 (by rfl) ⟨56960, by rfl⟩ : syracuseStep 1215157 = 113921) (by norm_num)
theorem B1084229 : Blo 235815 1084229 := bbase (se 4 (by rfl) ⟨101646, by rfl⟩ : syracuseStep 1084229 = 203293) (by norm_num)
theorem B265297 : Blo 235815 265297 := bbase (se 2 (by rfl) ⟨99486, by rfl⟩ : syracuseStep 265297 = 198973) (by norm_num)
theorem B1346645 : Blo 235815 1346645 := bbase (se 8 (by rfl) ⟨7890, by rfl⟩ : syracuseStep 1346645 = 15781) (by norm_num)
theorem B265333 : Blo 235815 265333 := bbase (se 5 (by rfl) ⟨12437, by rfl⟩ : syracuseStep 265333 = 24875) (by norm_num)
theorem B265369 : Blo 235815 265369 := bbase (se 2 (by rfl) ⟨99513, by rfl⟩ : syracuseStep 265369 = 199027) (by norm_num)
theorem B724133 : Blo 235815 724133 := bbase (se 4 (by rfl) ⟨67887, by rfl⟩ : syracuseStep 724133 = 135775) (by norm_num)
theorem B265405 : Blo 235815 265405 := bbase (se 3 (by rfl) ⟨49763, by rfl⟩ : syracuseStep 265405 = 99527) (by norm_num)
theorem B265441 : Blo 235815 265441 := bbase (se 2 (by rfl) ⟨99540, by rfl⟩ : syracuseStep 265441 = 199081) (by norm_num)
theorem B756965 : Blo 235815 756965 := bbase (se 4 (by rfl) ⟨70965, by rfl⟩ : syracuseStep 756965 = 141931) (by norm_num)
theorem B265477 : Blo 235815 265477 := bbase (se 4 (by rfl) ⟨24888, by rfl⟩ : syracuseStep 265477 = 49777) (by norm_num)
theorem B429317 : Blo 235815 429317 := bbase (se 4 (by rfl) ⟨40248, by rfl⟩ : syracuseStep 429317 = 80497) (by norm_num)
theorem B265513 : Blo 235815 265513 := bbase (se 2 (by rfl) ⟨99567, by rfl⟩ : syracuseStep 265513 = 199135) (by norm_num)
theorem B265549 : Blo 235815 265549 := bbase (se 3 (by rfl) ⟨49790, by rfl⟩ : syracuseStep 265549 = 99581) (by norm_num)
theorem B265585 : Blo 235815 265585 := bbase (se 2 (by rfl) ⟨99594, by rfl⟩ : syracuseStep 265585 = 199189) (by norm_num)
theorem B265621 : Blo 235815 265621 := bbase (se 6 (by rfl) ⟨6225, by rfl⟩ : syracuseStep 265621 = 12451) (by norm_num)
theorem B265657 : Blo 235815 265657 := bbase (se 2 (by rfl) ⟨99621, by rfl⟩ : syracuseStep 265657 = 199243) (by norm_num)
theorem B265693 : Blo 235815 265693 := bbase (se 3 (by rfl) ⟨49817, by rfl⟩ : syracuseStep 265693 = 99635) (by norm_num)
theorem B265729 : Blo 235815 265729 := bbase (se 2 (by rfl) ⟨99648, by rfl⟩ : syracuseStep 265729 = 199297) (by norm_num)
theorem B298505 : Blo 235815 298505 := bbase (se 2 (by rfl) ⟨111939, by rfl⟩ : syracuseStep 298505 = 223879) (by norm_num)
theorem B265765 : Blo 235815 265765 := bbase (se 4 (by rfl) ⟨24915, by rfl⟩ : syracuseStep 265765 = 49831) (by norm_num)
theorem B298561 : Blo 235815 298561 := bbase (se 2 (by rfl) ⟨111960, by rfl⟩ : syracuseStep 298561 = 223921) (by norm_num)
theorem B265801 : Blo 235815 265801 := bbase (se 2 (by rfl) ⟨99675, by rfl⟩ : syracuseStep 265801 = 199351) (by norm_num)
theorem B265837 : Blo 235815 265837 := bbase (se 3 (by rfl) ⟨49844, by rfl⟩ : syracuseStep 265837 = 99689) (by norm_num)
theorem B1707637 : Blo 235815 1707637 := bbase (se 5 (by rfl) ⟨80045, by rfl⟩ : syracuseStep 1707637 = 160091) (by norm_num)
theorem B265873 : Blo 235815 265873 := bbase (se 2 (by rfl) ⟨99702, by rfl⟩ : syracuseStep 265873 = 199405) (by norm_num)
theorem B298657 : Blo 235815 298657 := bbase (se 2 (by rfl) ⟨111996, by rfl⟩ : syracuseStep 298657 = 223993) (by norm_num)
theorem B265909 : Blo 235815 265909 := bbase (se 5 (by rfl) ⟨12464, by rfl⟩ : syracuseStep 265909 = 24929) (by norm_num)
theorem B265945 : Blo 235815 265945 := bbase (se 2 (by rfl) ⟨99729, by rfl⟩ : syracuseStep 265945 = 199459) (by norm_num)
theorem B1019621 : Blo 235815 1019621 := bbase (se 4 (by rfl) ⟨95589, by rfl⟩ : syracuseStep 1019621 = 191179) (by norm_num)
theorem B265981 : Blo 235815 265981 := bbase (se 3 (by rfl) ⟨49871, by rfl⟩ : syracuseStep 265981 = 99743) (by norm_num)
theorem B266017 : Blo 235815 266017 := bbase (se 2 (by rfl) ⟨99756, by rfl⟩ : syracuseStep 266017 = 199513) (by norm_num)
theorem B266053 : Blo 235815 266053 := bbase (se 4 (by rfl) ⟨24942, by rfl⟩ : syracuseStep 266053 = 49885) (by norm_num)
theorem B298829 : Blo 235815 298829 := bbase (se 3 (by rfl) ⟨56030, by rfl⟩ : syracuseStep 298829 = 112061) (by norm_num)
theorem B266069 : Blo 235815 266069 := bbase (se 9 (by rfl) ⟨779, by rfl⟩ : syracuseStep 266069 = 1559) (by norm_num)
theorem B266089 : Blo 235815 266089 := bbase (se 2 (by rfl) ⟨99783, by rfl⟩ : syracuseStep 266089 = 199567) (by norm_num)
theorem B298885 : Blo 235815 298885 := bbase (se 4 (by rfl) ⟨28020, by rfl⟩ : syracuseStep 298885 = 56041) (by norm_num)
theorem B266125 : Blo 235815 266125 := bbase (se 3 (by rfl) ⟨49898, by rfl⟩ : syracuseStep 266125 = 99797) (by norm_num)
theorem B266161 : Blo 235815 266161 := bbase (se 2 (by rfl) ⟨99810, by rfl⟩ : syracuseStep 266161 = 199621) (by norm_num)
theorem B266197 : Blo 235815 266197 := bbase (se 7 (by rfl) ⟨3119, by rfl⟩ : syracuseStep 266197 = 6239) (by norm_num)
theorem B1019861 : Blo 235815 1019861 := bbase (se 7 (by rfl) ⟨11951, by rfl⟩ : syracuseStep 1019861 = 23903) (by norm_num)
theorem B298981 : Blo 235815 298981 := bbase (se 4 (by rfl) ⟨28029, by rfl⟩ : syracuseStep 298981 = 56059) (by norm_num)
theorem B266233 : Blo 235815 266233 := bbase (se 2 (by rfl) ⟨99837, by rfl⟩ : syracuseStep 266233 = 199675) (by norm_num)
theorem B266269 : Blo 235815 266269 := bbase (se 3 (by rfl) ⟨49925, by rfl⟩ : syracuseStep 266269 = 99851) (by norm_num)
theorem B626741 : Blo 235815 626741 := bbase (se 5 (by rfl) ⟨29378, by rfl⟩ : syracuseStep 626741 = 58757) (by norm_num)
theorem B266305 : Blo 235815 266305 := bbase (se 2 (by rfl) ⟨99864, by rfl⟩ : syracuseStep 266305 = 199729) (by norm_num)
theorem B266341 : Blo 235815 266341 := bbase (se 4 (by rfl) ⟨24969, by rfl⟩ : syracuseStep 266341 = 49939) (by norm_num)
theorem B266377 : Blo 235815 266377 := bbase (se 2 (by rfl) ⟨99891, by rfl⟩ : syracuseStep 266377 = 199783) (by norm_num)
theorem B299153 : Blo 235815 299153 := bbase (se 2 (by rfl) ⟨112182, by rfl⟩ : syracuseStep 299153 = 224365) (by norm_num)
theorem B266413 : Blo 235815 266413 := bbase (se 3 (by rfl) ⟨49952, by rfl⟩ : syracuseStep 266413 = 99905) (by norm_num)
theorem B299209 : Blo 235815 299209 := bbase (se 2 (by rfl) ⟨112203, by rfl⟩ : syracuseStep 299209 = 224407) (by norm_num)
theorem B266449 : Blo 235815 266449 := bbase (se 2 (by rfl) ⟨99918, by rfl⟩ : syracuseStep 266449 = 199837) (by norm_num)
theorem B266485 : Blo 235815 266485 := bbase (se 5 (by rfl) ⟨12491, by rfl⟩ : syracuseStep 266485 = 24983) (by norm_num)
theorem B266521 : Blo 235815 266521 := bbase (se 2 (by rfl) ⟨99945, by rfl⟩ : syracuseStep 266521 = 199891) (by norm_num)
theorem B299305 : Blo 235815 299305 := bbase (se 2 (by rfl) ⟨112239, by rfl⟩ : syracuseStep 299305 = 224479) (by norm_num)
theorem B266557 : Blo 235815 266557 := bbase (se 3 (by rfl) ⟨49979, by rfl⟩ : syracuseStep 266557 = 99959) (by norm_num)
theorem B266593 : Blo 235815 266593 := bbase (se 2 (by rfl) ⟨99972, by rfl⟩ : syracuseStep 266593 = 199945) (by norm_num)
theorem B266629 : Blo 235815 266629 := bbase (se 4 (by rfl) ⟨24996, by rfl⟩ : syracuseStep 266629 = 49993) (by norm_num)
theorem B266665 : Blo 235815 266665 := bbase (se 2 (by rfl) ⟨99999, by rfl⟩ : syracuseStep 266665 = 199999) (by norm_num)
theorem B266701 : Blo 235815 266701 := bbase (se 3 (by rfl) ⟨50006, by rfl⟩ : syracuseStep 266701 = 100013) (by norm_num)
theorem B299477 : Blo 235815 299477 := bbase (se 7 (by rfl) ⟨3509, by rfl⟩ : syracuseStep 299477 = 7019) (by norm_num)
theorem B266737 : Blo 235815 266737 := bbase (se 2 (by rfl) ⟨100026, by rfl⟩ : syracuseStep 266737 = 200053) (by norm_num)
theorem B299533 : Blo 235815 299533 := bbase (se 3 (by rfl) ⟨56162, by rfl⟩ : syracuseStep 299533 = 112325) (by norm_num)
theorem B266773 : Blo 235815 266773 := bbase (se 6 (by rfl) ⟨6252, by rfl⟩ : syracuseStep 266773 = 12505) (by norm_num)
theorem B266809 : Blo 235815 266809 := bbase (se 2 (by rfl) ⟨100053, by rfl⟩ : syracuseStep 266809 = 200107) (by norm_num)
theorem B266845 : Blo 235815 266845 := bbase (se 3 (by rfl) ⟨50033, by rfl⟩ : syracuseStep 266845 = 100067) (by norm_num)
theorem B299629 : Blo 235815 299629 := bbase (se 3 (by rfl) ⟨56180, by rfl⟩ : syracuseStep 299629 = 112361) (by norm_num)
theorem B266881 : Blo 235815 266881 := bbase (se 2 (by rfl) ⟨100080, by rfl⟩ : syracuseStep 266881 = 200161) (by norm_num)
theorem B332429 : Blo 235815 332429 := bbase (se 3 (by rfl) ⟨62330, by rfl⟩ : syracuseStep 332429 = 124661) (by norm_num)
theorem B397973 : Blo 235815 397973 := bbase (se 6 (by rfl) ⟨9327, by rfl⟩ : syracuseStep 397973 = 18655) (by norm_num)
theorem B266917 : Blo 235815 266917 := bbase (se 4 (by rfl) ⟨25023, by rfl⟩ : syracuseStep 266917 = 50047) (by norm_num)
theorem B266953 : Blo 235815 266953 := bbase (se 2 (by rfl) ⟨100107, by rfl⟩ : syracuseStep 266953 = 200215) (by norm_num)
theorem B266989 : Blo 235815 266989 := bbase (se 3 (by rfl) ⟨50060, by rfl⟩ : syracuseStep 266989 = 100121) (by norm_num)
theorem B267025 : Blo 235815 267025 := bbase (se 2 (by rfl) ⟨100134, by rfl⟩ : syracuseStep 267025 = 200269) (by norm_num)
theorem B398101 : Blo 235815 398101 := bbase (se 6 (by rfl) ⟨9330, by rfl⟩ : syracuseStep 398101 = 18661) (by norm_num)
theorem B1151765 : Blo 235815 1151765 := bbase (se 6 (by rfl) ⟨26994, by rfl⟩ : syracuseStep 1151765 = 53989) (by norm_num)
theorem B299801 : Blo 235815 299801 := bbase (se 2 (by rfl) ⟨112425, by rfl⟩ : syracuseStep 299801 = 224851) (by norm_num)
theorem B267061 : Blo 235815 267061 := bbase (se 5 (by rfl) ⟨12518, by rfl⟩ : syracuseStep 267061 = 25037) (by norm_num)
theorem B299857 : Blo 235815 299857 := bbase (se 2 (by rfl) ⟨112446, by rfl⟩ : syracuseStep 299857 = 224893) (by norm_num)
theorem B267097 : Blo 235815 267097 := bbase (se 2 (by rfl) ⟨100161, by rfl⟩ : syracuseStep 267097 = 200323) (by norm_num)
theorem B725861 : Blo 235815 725861 := bbase (se 4 (by rfl) ⟨68049, by rfl⟩ : syracuseStep 725861 = 136099) (by norm_num)
theorem B398189 : Blo 235815 398189 := bbase (se 3 (by rfl) ⟨74660, by rfl⟩ : syracuseStep 398189 = 149321) (by norm_num)
theorem B267133 : Blo 235815 267133 := bbase (se 3 (by rfl) ⟨50087, by rfl⟩ : syracuseStep 267133 = 100175) (by norm_num)
theorem B267169 : Blo 235815 267169 := bbase (se 2 (by rfl) ⟨100188, by rfl⟩ : syracuseStep 267169 = 200377) (by norm_num)
theorem B299953 : Blo 235815 299953 := bbase (se 2 (by rfl) ⟨112482, by rfl⟩ : syracuseStep 299953 = 224965) (by norm_num)
theorem B267205 : Blo 235815 267205 := bbase (se 4 (by rfl) ⟨25050, by rfl⟩ : syracuseStep 267205 = 50101) (by norm_num)
theorem B1151957 : Blo 235815 1151957 := bbase (se 7 (by rfl) ⟨13499, by rfl⟩ : syracuseStep 1151957 = 26999) (by norm_num)
theorem B267241 : Blo 235815 267241 := bbase (se 2 (by rfl) ⟨100215, by rfl⟩ : syracuseStep 267241 = 200431) (by norm_num)
theorem B398317 : Blo 235815 398317 := bbase (se 3 (by rfl) ⟨74684, by rfl⟩ : syracuseStep 398317 = 149369) (by norm_num)
theorem B267277 : Blo 235815 267277 := bbase (se 3 (by rfl) ⟨50114, by rfl⟩ : syracuseStep 267277 = 100229) (by norm_num)
theorem B758821 : Blo 235815 758821 := bbase (se 4 (by rfl) ⟨71139, by rfl⟩ : syracuseStep 758821 = 142279) (by norm_num)
theorem B267313 : Blo 235815 267313 := bbase (se 2 (by rfl) ⟨100242, by rfl⟩ : syracuseStep 267313 = 200485) (by norm_num)
theorem B398405 : Blo 235815 398405 := bbase (se 4 (by rfl) ⟨37350, by rfl⟩ : syracuseStep 398405 = 74701) (by norm_num)
theorem B267349 : Blo 235815 267349 := bbase (se 8 (by rfl) ⟨1566, by rfl⟩ : syracuseStep 267349 = 3133) (by norm_num)
theorem B300125 : Blo 235815 300125 := bbase (se 3 (by rfl) ⟨56273, by rfl⟩ : syracuseStep 300125 = 112547) (by norm_num)
theorem B267385 : Blo 235815 267385 := bbase (se 2 (by rfl) ⟨100269, by rfl⟩ : syracuseStep 267385 = 200539) (by norm_num)
theorem B300181 : Blo 235815 300181 := bbase (se 6 (by rfl) ⟨7035, by rfl⟩ : syracuseStep 300181 = 14071) (by norm_num)
theorem B267421 : Blo 235815 267421 := bbase (se 3 (by rfl) ⟨50141, by rfl⟩ : syracuseStep 267421 = 100283) (by norm_num)
theorem B267457 : Blo 235815 267457 := bbase (se 2 (by rfl) ⟨100296, by rfl⟩ : syracuseStep 267457 = 200593) (by norm_num)
theorem B398533 : Blo 235815 398533 := bbase (se 4 (by rfl) ⟨37362, by rfl⟩ : syracuseStep 398533 = 74725) (by norm_num)
theorem B267493 : Blo 235815 267493 := bbase (se 4 (by rfl) ⟨25077, by rfl⟩ : syracuseStep 267493 = 50155) (by norm_num)
theorem B300277 : Blo 235815 300277 := bbase (se 5 (by rfl) ⟨14075, by rfl⟩ : syracuseStep 300277 = 28151) (by norm_num)
theorem B267529 : Blo 235815 267529 := bbase (se 2 (by rfl) ⟨100323, by rfl⟩ : syracuseStep 267529 = 200647) (by norm_num)
theorem B398621 : Blo 235815 398621 := bbase (se 3 (by rfl) ⟨74741, by rfl⟩ : syracuseStep 398621 = 149483) (by norm_num)
theorem B267565 : Blo 235815 267565 := bbase (se 3 (by rfl) ⟨50168, by rfl⟩ : syracuseStep 267565 = 100337) (by norm_num)
theorem B267601 : Blo 235815 267601 := bbase (se 2 (by rfl) ⟨100350, by rfl⟩ : syracuseStep 267601 = 200701) (by norm_num)
theorem B267637 : Blo 235815 267637 := bbase (se 5 (by rfl) ⟨12545, by rfl⟩ : syracuseStep 267637 = 25091) (by norm_num)
theorem B267673 : Blo 235815 267673 := bbase (se 2 (by rfl) ⟨100377, by rfl⟩ : syracuseStep 267673 = 200755) (by norm_num)
theorem B398749 : Blo 235815 398749 := bbase (se 3 (by rfl) ⟨74765, by rfl⟩ : syracuseStep 398749 = 149531) (by norm_num)
theorem B300449 : Blo 235815 300449 := bbase (se 2 (by rfl) ⟨112668, by rfl⟩ : syracuseStep 300449 = 225337) (by norm_num)
theorem B267709 : Blo 235815 267709 := bbase (se 3 (by rfl) ⟨50195, by rfl⟩ : syracuseStep 267709 = 100391) (by norm_num)
theorem B300505 : Blo 235815 300505 := bbase (se 2 (by rfl) ⟨112689, by rfl⟩ : syracuseStep 300505 = 225379) (by norm_num)
theorem B267745 : Blo 235815 267745 := bbase (se 2 (by rfl) ⟨100404, by rfl⟩ : syracuseStep 267745 = 200809) (by norm_num)
theorem B398837 : Blo 235815 398837 := bbase (se 5 (by rfl) ⟨18695, by rfl⟩ : syracuseStep 398837 = 37391) (by norm_num)
theorem B2168309 : Blo 235815 2168309 := bbase (se 5 (by rfl) ⟨101639, by rfl⟩ : syracuseStep 2168309 = 203279) (by norm_num)
theorem B267781 : Blo 235815 267781 := bbase (se 4 (by rfl) ⟨25104, by rfl⟩ : syracuseStep 267781 = 50209) (by norm_num)
theorem B267817 : Blo 235815 267817 := bbase (se 2 (by rfl) ⟨100431, by rfl⟩ : syracuseStep 267817 = 200863) (by norm_num)
theorem B300601 : Blo 235815 300601 := bbase (se 2 (by rfl) ⟨112725, by rfl⟩ : syracuseStep 300601 = 225451) (by norm_num)
theorem B267853 : Blo 235815 267853 := bbase (se 3 (by rfl) ⟨50222, by rfl⟩ : syracuseStep 267853 = 100445) (by norm_num)
theorem B267889 : Blo 235815 267889 := bbase (se 2 (by rfl) ⟨100458, by rfl⟩ : syracuseStep 267889 = 200917) (by norm_num)
theorem B398965 : Blo 235815 398965 := bbase (se 5 (by rfl) ⟨18701, by rfl⟩ : syracuseStep 398965 = 37403) (by norm_num)
theorem B267925 : Blo 235815 267925 := bbase (se 6 (by rfl) ⟨6279, by rfl⟩ : syracuseStep 267925 = 12559) (by norm_num)
theorem B267961 : Blo 235815 267961 := bbase (se 2 (by rfl) ⟨100485, by rfl⟩ : syracuseStep 267961 = 200971) (by norm_num)
theorem B399053 : Blo 235815 399053 := bbase (se 3 (by rfl) ⟨74822, by rfl⟩ : syracuseStep 399053 = 149645) (by norm_num)
theorem B267997 : Blo 235815 267997 := bbase (se 3 (by rfl) ⟨50249, by rfl⟩ : syracuseStep 267997 = 100499) (by norm_num)
theorem B300773 : Blo 235815 300773 := bbase (se 4 (by rfl) ⟨28197, by rfl⟩ : syracuseStep 300773 = 56395) (by norm_num)
theorem B268033 : Blo 235815 268033 := bbase (se 2 (by rfl) ⟨100512, by rfl⟩ : syracuseStep 268033 = 201025) (by norm_num)
theorem B300829 : Blo 235815 300829 := bbase (se 3 (by rfl) ⟨56405, by rfl⟩ : syracuseStep 300829 = 112811) (by norm_num)
theorem B268069 : Blo 235815 268069 := bbase (se 4 (by rfl) ⟨25131, by rfl⟩ : syracuseStep 268069 = 50263) (by norm_num)
theorem B268105 : Blo 235815 268105 := bbase (se 2 (by rfl) ⟨100539, by rfl⟩ : syracuseStep 268105 = 201079) (by norm_num)
theorem B399181 : Blo 235815 399181 := bbase (se 3 (by rfl) ⟨74846, by rfl⟩ : syracuseStep 399181 = 149693) (by norm_num)
theorem B268141 : Blo 235815 268141 := bbase (se 3 (by rfl) ⟨50276, by rfl⟩ : syracuseStep 268141 = 100553) (by norm_num)
theorem B300925 : Blo 235815 300925 := bbase (se 3 (by rfl) ⟨56423, by rfl⟩ : syracuseStep 300925 = 112847) (by norm_num)
theorem B268177 : Blo 235815 268177 := bbase (se 2 (by rfl) ⟨100566, by rfl⟩ : syracuseStep 268177 = 201133) (by norm_num)
theorem B399269 : Blo 235815 399269 := bbase (se 4 (by rfl) ⟨37431, by rfl⟩ : syracuseStep 399269 = 74863) (by norm_num)
theorem B268213 : Blo 235815 268213 := bbase (se 5 (by rfl) ⟨12572, by rfl⟩ : syracuseStep 268213 = 25145) (by norm_num)
theorem B268249 : Blo 235815 268249 := bbase (se 2 (by rfl) ⟨100593, by rfl⟩ : syracuseStep 268249 = 201187) (by norm_num)
theorem B268285 : Blo 235815 268285 := bbase (se 3 (by rfl) ⟨50303, by rfl⟩ : syracuseStep 268285 = 100607) (by norm_num)
theorem B1808405 : Blo 235815 1808405 := bbase (se 6 (by rfl) ⟨42384, by rfl⟩ : syracuseStep 1808405 = 84769) (by norm_num)
theorem B268321 : Blo 235815 268321 := bbase (se 2 (by rfl) ⟨100620, by rfl⟩ : syracuseStep 268321 = 201241) (by norm_num)
theorem B399397 : Blo 235815 399397 := bbase (se 4 (by rfl) ⟨37443, by rfl⟩ : syracuseStep 399397 = 74887) (by norm_num)
theorem B301097 : Blo 235815 301097 := bbase (se 2 (by rfl) ⟨112911, by rfl⟩ : syracuseStep 301097 = 225823) (by norm_num)
theorem B268357 : Blo 235815 268357 := bbase (se 4 (by rfl) ⟨25158, by rfl⟩ : syracuseStep 268357 = 50317) (by norm_num)
theorem B301153 : Blo 235815 301153 := bbase (se 2 (by rfl) ⟨112932, by rfl⟩ : syracuseStep 301153 = 225865) (by norm_num)
theorem B268393 : Blo 235815 268393 := bbase (se 2 (by rfl) ⟨100647, by rfl⟩ : syracuseStep 268393 = 201295) (by norm_num)
theorem B399485 : Blo 235815 399485 := bbase (se 3 (by rfl) ⟨74903, by rfl⟩ : syracuseStep 399485 = 149807) (by norm_num)
theorem B268429 : Blo 235815 268429 := bbase (se 3 (by rfl) ⟨50330, by rfl⟩ : syracuseStep 268429 = 100661) (by norm_num)
theorem B268465 : Blo 235815 268465 := bbase (se 2 (by rfl) ⟨100674, by rfl⟩ : syracuseStep 268465 = 201349) (by norm_num)
theorem B530621 : Blo 235815 530621 := bbase (se 3 (by rfl) ⟨99491, by rfl⟩ : syracuseStep 530621 = 198983) (by norm_num)
theorem B301249 : Blo 235815 301249 := bbase (se 2 (by rfl) ⟨112968, by rfl⟩ : syracuseStep 301249 = 225937) (by norm_num)
theorem B1022149 : Blo 235815 1022149 := bbase (se 4 (by rfl) ⟨95826, by rfl⟩ : syracuseStep 1022149 = 191653) (by norm_num)
theorem B268501 : Blo 235815 268501 := bbase (se 7 (by rfl) ⟨3146, by rfl⟩ : syracuseStep 268501 = 6293) (by norm_num)
theorem B268537 : Blo 235815 268537 := bbase (se 2 (by rfl) ⟨100701, by rfl⟩ : syracuseStep 268537 = 201403) (by norm_num)
theorem B399613 : Blo 235815 399613 := bbase (se 3 (by rfl) ⟨74927, by rfl⟩ : syracuseStep 399613 = 149855) (by norm_num)
theorem B530693 : Blo 235815 530693 := bbase (se 4 (by rfl) ⟨49752, by rfl⟩ : syracuseStep 530693 = 99505) (by norm_num)
theorem B268573 : Blo 235815 268573 := bbase (se 3 (by rfl) ⟨50357, by rfl⟩ : syracuseStep 268573 = 100715) (by norm_num)
theorem B268609 : Blo 235815 268609 := bbase (se 2 (by rfl) ⟨100728, by rfl⟩ : syracuseStep 268609 = 201457) (by norm_num)
theorem B530765 : Blo 235815 530765 := bbase (se 3 (by rfl) ⟨99518, by rfl⟩ : syracuseStep 530765 = 199037) (by norm_num)
theorem B399701 : Blo 235815 399701 := bbase (se 10 (by rfl) ⟨585, by rfl⟩ : syracuseStep 399701 = 1171) (by norm_num)
theorem B268645 : Blo 235815 268645 := bbase (se 4 (by rfl) ⟨25185, by rfl⟩ : syracuseStep 268645 = 50371) (by norm_num)
theorem B301421 : Blo 235815 301421 := bbase (se 3 (by rfl) ⟨56516, by rfl⟩ : syracuseStep 301421 = 113033) (by norm_num)
theorem B268681 : Blo 235815 268681 := bbase (se 2 (by rfl) ⟨100755, by rfl⟩ : syracuseStep 268681 = 201511) (by norm_num)
theorem B530837 : Blo 235815 530837 := bbase (se 6 (by rfl) ⟨12441, by rfl⟩ : syracuseStep 530837 = 24883) (by norm_num)
theorem B301477 : Blo 235815 301477 := bbase (se 4 (by rfl) ⟨28263, by rfl⟩ : syracuseStep 301477 = 56527) (by norm_num)
theorem B268717 : Blo 235815 268717 := bbase (se 3 (by rfl) ⟨50384, by rfl⟩ : syracuseStep 268717 = 100769) (by norm_num)
theorem B268753 : Blo 235815 268753 := bbase (se 2 (by rfl) ⟨100782, by rfl⟩ : syracuseStep 268753 = 201565) (by norm_num)
theorem B399829 : Blo 235815 399829 := bbase (se 7 (by rfl) ⟨4685, by rfl⟩ : syracuseStep 399829 = 9371) (by norm_num)
theorem B530909 : Blo 235815 530909 := bbase (se 3 (by rfl) ⟨99545, by rfl⟩ : syracuseStep 530909 = 199091) (by norm_num)
theorem B268789 : Blo 235815 268789 := bbase (se 5 (by rfl) ⟨12599, by rfl⟩ : syracuseStep 268789 = 25199) (by norm_num)
theorem B301573 : Blo 235815 301573 := bbase (se 4 (by rfl) ⟨28272, by rfl⟩ : syracuseStep 301573 = 56545) (by norm_num)
theorem B268825 : Blo 235815 268825 := bbase (se 2 (by rfl) ⟨100809, by rfl⟩ : syracuseStep 268825 = 201619) (by norm_num)
theorem B530981 : Blo 235815 530981 := bbase (se 4 (by rfl) ⟨49779, by rfl⟩ : syracuseStep 530981 = 99559) (by norm_num)
theorem B399917 : Blo 235815 399917 := bbase (se 3 (by rfl) ⟨74984, by rfl⟩ : syracuseStep 399917 = 149969) (by norm_num)
theorem B268861 : Blo 235815 268861 := bbase (se 3 (by rfl) ⟨50411, by rfl⟩ : syracuseStep 268861 = 100823) (by norm_num)
theorem B268897 : Blo 235815 268897 := bbase (se 2 (by rfl) ⟨100836, by rfl⟩ : syracuseStep 268897 = 201673) (by norm_num)
theorem B531053 : Blo 235815 531053 := bbase (se 3 (by rfl) ⟨99572, by rfl⟩ : syracuseStep 531053 = 199145) (by norm_num)
theorem B268933 : Blo 235815 268933 := bbase (se 4 (by rfl) ⟨25212, by rfl⟩ : syracuseStep 268933 = 50425) (by norm_num)
theorem B268969 : Blo 235815 268969 := bbase (se 2 (by rfl) ⟨100863, by rfl⟩ : syracuseStep 268969 = 201727) (by norm_num)
theorem B400045 : Blo 235815 400045 := bbase (se 3 (by rfl) ⟨75008, by rfl⟩ : syracuseStep 400045 = 150017) (by norm_num)
theorem B301745 : Blo 235815 301745 := bbase (se 2 (by rfl) ⟨113154, by rfl⟩ : syracuseStep 301745 = 226309) (by norm_num)
theorem B531125 : Blo 235815 531125 := bbase (se 5 (by rfl) ⟨24896, by rfl⟩ : syracuseStep 531125 = 49793) (by norm_num)
theorem B269005 : Blo 235815 269005 := bbase (se 3 (by rfl) ⟨50438, by rfl⟩ : syracuseStep 269005 = 100877) (by norm_num)
theorem B301801 : Blo 235815 301801 := bbase (se 2 (by rfl) ⟨113175, by rfl⟩ : syracuseStep 301801 = 226351) (by norm_num)
theorem B269041 : Blo 235815 269041 := bbase (se 2 (by rfl) ⟨100890, by rfl⟩ : syracuseStep 269041 = 201781) (by norm_num)
theorem B531197 : Blo 235815 531197 := bbase (se 3 (by rfl) ⟨99599, by rfl⟩ : syracuseStep 531197 = 199199) (by norm_num)
theorem B400133 : Blo 235815 400133 := bbase (se 4 (by rfl) ⟨37512, by rfl⟩ : syracuseStep 400133 = 75025) (by norm_num)
theorem B269077 : Blo 235815 269077 := bbase (se 6 (by rfl) ⟨6306, by rfl⟩ : syracuseStep 269077 = 12613) (by norm_num)
theorem B269113 : Blo 235815 269113 := bbase (se 2 (by rfl) ⟨100917, by rfl⟩ : syracuseStep 269113 = 201835) (by norm_num)
theorem B531269 : Blo 235815 531269 := bbase (se 4 (by rfl) ⟨49806, by rfl⟩ : syracuseStep 531269 = 99613) (by norm_num)
theorem B301897 : Blo 235815 301897 := bbase (se 2 (by rfl) ⟨113211, by rfl⟩ : syracuseStep 301897 = 226423) (by norm_num)
theorem B269149 : Blo 235815 269149 := bbase (se 3 (by rfl) ⟨50465, by rfl⟩ : syracuseStep 269149 = 100931) (by norm_num)
theorem B269185 : Blo 235815 269185 := bbase (se 2 (by rfl) ⟨100944, by rfl⟩ : syracuseStep 269185 = 201889) (by norm_num)
theorem B400261 : Blo 235815 400261 := bbase (se 4 (by rfl) ⟨37524, by rfl⟩ : syracuseStep 400261 = 75049) (by norm_num)
theorem B531341 : Blo 235815 531341 := bbase (se 3 (by rfl) ⟨99626, by rfl⟩ : syracuseStep 531341 = 199253) (by norm_num)
theorem B269221 : Blo 235815 269221 := bbase (se 4 (by rfl) ⟨25239, by rfl⟩ : syracuseStep 269221 = 50479) (by norm_num)
theorem B596909 : Blo 235815 596909 := bbase (se 3 (by rfl) ⟨111920, by rfl⟩ : syracuseStep 596909 = 223841) (by norm_num)
theorem B269257 : Blo 235815 269257 := bbase (se 2 (by rfl) ⟨100971, by rfl⟩ : syracuseStep 269257 = 201943) (by norm_num)
theorem B531413 : Blo 235815 531413 := bbase (se 7 (by rfl) ⟨6227, by rfl⟩ : syracuseStep 531413 = 12455) (by norm_num)
theorem B400349 : Blo 235815 400349 := bbase (se 3 (by rfl) ⟨75065, by rfl⟩ : syracuseStep 400349 = 150131) (by norm_num)
theorem B269293 : Blo 235815 269293 := bbase (se 3 (by rfl) ⟨50492, by rfl⟩ : syracuseStep 269293 = 100985) (by norm_num)
theorem B302069 : Blo 235815 302069 := bbase (se 5 (by rfl) ⟨14159, by rfl⟩ : syracuseStep 302069 = 28319) (by norm_num)
theorem B269329 : Blo 235815 269329 := bbase (se 2 (by rfl) ⟨100998, by rfl⟩ : syracuseStep 269329 = 201997) (by norm_num)
theorem B531485 : Blo 235815 531485 := bbase (se 3 (by rfl) ⟨99653, by rfl⟩ : syracuseStep 531485 = 199307) (by norm_num)
theorem B302125 : Blo 235815 302125 := bbase (se 3 (by rfl) ⟨56648, by rfl⟩ : syracuseStep 302125 = 113297) (by norm_num)
theorem B269365 : Blo 235815 269365 := bbase (se 5 (by rfl) ⟨12626, by rfl⟩ : syracuseStep 269365 = 25253) (by norm_num)
theorem B269401 : Blo 235815 269401 := bbase (se 2 (by rfl) ⟨101025, by rfl⟩ : syracuseStep 269401 = 202051) (by norm_num)
theorem B400477 : Blo 235815 400477 := bbase (se 3 (by rfl) ⟨75089, by rfl⟩ : syracuseStep 400477 = 150179) (by norm_num)
theorem B531557 : Blo 235815 531557 := bbase (se 4 (by rfl) ⟨49833, by rfl⟩ : syracuseStep 531557 = 99667) (by norm_num)
theorem B269437 : Blo 235815 269437 := bbase (se 3 (by rfl) ⟨50519, by rfl⟩ : syracuseStep 269437 = 101039) (by norm_num)
theorem B302221 : Blo 235815 302221 := bbase (se 3 (by rfl) ⟨56666, by rfl⟩ : syracuseStep 302221 = 113333) (by norm_num)
theorem B269473 : Blo 235815 269473 := bbase (se 2 (by rfl) ⟨101052, by rfl⟩ : syracuseStep 269473 = 202105) (by norm_num)
theorem B531629 : Blo 235815 531629 := bbase (se 3 (by rfl) ⟨99680, by rfl⟩ : syracuseStep 531629 = 199361) (by norm_num)
theorem B400565 : Blo 235815 400565 := bbase (se 5 (by rfl) ⟨18776, by rfl⟩ : syracuseStep 400565 = 37553) (by norm_num)
theorem B269509 : Blo 235815 269509 := bbase (se 4 (by rfl) ⟨25266, by rfl⟩ : syracuseStep 269509 = 50533) (by norm_num)
theorem B269525 : Blo 235815 269525 := bbase (se 7 (by rfl) ⟨3158, by rfl⟩ : syracuseStep 269525 = 6317) (by norm_num)
theorem B269545 : Blo 235815 269545 := bbase (se 2 (by rfl) ⟨101079, by rfl⟩ : syracuseStep 269545 = 202159) (by norm_num)
theorem B531701 : Blo 235815 531701 := bbase (se 5 (by rfl) ⟨24923, by rfl⟩ : syracuseStep 531701 = 49847) (by norm_num)
theorem B597253 : Blo 235815 597253 := bbase (se 4 (by rfl) ⟨55992, by rfl⟩ : syracuseStep 597253 = 111985) (by norm_num)
theorem B269581 : Blo 235815 269581 := bbase (se 3 (by rfl) ⟨50546, by rfl⟩ : syracuseStep 269581 = 101093) (by norm_num)
theorem B269617 : Blo 235815 269617 := bbase (se 2 (by rfl) ⟨101106, by rfl⟩ : syracuseStep 269617 = 202213) (by norm_num)
theorem B400693 : Blo 235815 400693 := bbase (se 5 (by rfl) ⟨18782, by rfl⟩ : syracuseStep 400693 = 37565) (by norm_num)
theorem B302393 : Blo 235815 302393 := bbase (se 2 (by rfl) ⟨113397, by rfl⟩ : syracuseStep 302393 = 226795) (by norm_num)
theorem B531773 : Blo 235815 531773 := bbase (se 3 (by rfl) ⟨99707, by rfl⟩ : syracuseStep 531773 = 199415) (by norm_num)
theorem B269653 : Blo 235815 269653 := bbase (se 11 (by rfl) ⟨197, by rfl⟩ : syracuseStep 269653 = 395) (by norm_num)
theorem B302449 : Blo 235815 302449 := bbase (se 2 (by rfl) ⟨113418, by rfl⟩ : syracuseStep 302449 = 226837) (by norm_num)
theorem B597365 : Blo 235815 597365 := bbase (se 5 (by rfl) ⟨28001, by rfl⟩ : syracuseStep 597365 = 56003) (by norm_num)
theorem B269689 : Blo 235815 269689 := bbase (se 2 (by rfl) ⟨101133, by rfl⟩ : syracuseStep 269689 = 202267) (by norm_num)
theorem B531845 : Blo 235815 531845 := bbase (se 4 (by rfl) ⟨49860, by rfl⟩ : syracuseStep 531845 = 99721) (by norm_num)
theorem B400781 : Blo 235815 400781 := bbase (se 3 (by rfl) ⟨75146, by rfl⟩ : syracuseStep 400781 = 150293) (by norm_num)
theorem B269725 : Blo 235815 269725 := bbase (se 3 (by rfl) ⟨50573, by rfl⟩ : syracuseStep 269725 = 101147) (by norm_num)
theorem B269761 : Blo 235815 269761 := bbase (se 2 (by rfl) ⟨101160, by rfl⟩ : syracuseStep 269761 = 202321) (by norm_num)
theorem B531917 : Blo 235815 531917 := bbase (se 3 (by rfl) ⟨99734, by rfl⟩ : syracuseStep 531917 = 199469) (by norm_num)
theorem B302545 : Blo 235815 302545 := bbase (se 2 (by rfl) ⟨113454, by rfl⟩ : syracuseStep 302545 = 226909) (by norm_num)
theorem B400909 : Blo 235815 400909 := bbase (se 3 (by rfl) ⟨75170, by rfl⟩ : syracuseStep 400909 = 150341) (by norm_num)
theorem B531989 : Blo 235815 531989 := bbase (se 6 (by rfl) ⟨12468, by rfl⟩ : syracuseStep 531989 = 24937) (by norm_num)
theorem B3317269 : Blo 235815 3317269 := bbase (se 6 (by rfl) ⟨77748, by rfl⟩ : syracuseStep 3317269 = 155497) (by norm_num)
theorem B597557 : Blo 235815 597557 := bbase (se 5 (by rfl) ⟨28010, by rfl⟩ : syracuseStep 597557 = 56021) (by norm_num)
theorem B532061 : Blo 235815 532061 := bbase (se 3 (by rfl) ⟨99761, by rfl⟩ : syracuseStep 532061 = 199523) (by norm_num)
theorem B400997 : Blo 235815 400997 := bbase (se 4 (by rfl) ⟨37593, by rfl⟩ : syracuseStep 400997 = 75187) (by norm_num)
theorem B302717 : Blo 235815 302717 := bbase (se 3 (by rfl) ⟨56759, by rfl⟩ : syracuseStep 302717 = 113519) (by norm_num)
theorem B1023637 : Blo 235815 1023637 := bbase (se 6 (by rfl) ⟨23991, by rfl⟩ : syracuseStep 1023637 = 47983) (by norm_num)
theorem B532133 : Blo 235815 532133 := bbase (se 4 (by rfl) ⟨49887, by rfl⟩ : syracuseStep 532133 = 99775) (by norm_num)
theorem B1023653 : Blo 235815 1023653 := bbase (se 4 (by rfl) ⟨95967, by rfl⟩ : syracuseStep 1023653 = 191935) (by norm_num)
theorem B302773 : Blo 235815 302773 := bbase (se 5 (by rfl) ⟨14192, by rfl⟩ : syracuseStep 302773 = 28385) (by norm_num)
theorem B401125 : Blo 235815 401125 := bbase (se 4 (by rfl) ⟨37605, by rfl⟩ : syracuseStep 401125 = 75211) (by norm_num)
theorem B532205 : Blo 235815 532205 := bbase (se 3 (by rfl) ⟨99788, by rfl⟩ : syracuseStep 532205 = 199577) (by norm_num)
theorem B499469 : Blo 235815 499469 := bbase (se 3 (by rfl) ⟨93650, by rfl⟩ : syracuseStep 499469 = 187301) (by norm_num)
theorem B1154837 : Blo 235815 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B302869 : Blo 235815 302869 := bbase (se 6 (by rfl) ⟨7098, by rfl⟩ : syracuseStep 302869 = 14197) (by norm_num)
theorem B532277 : Blo 235815 532277 := bbase (se 5 (by rfl) ⟨24950, by rfl⟩ : syracuseStep 532277 = 49901) (by norm_num)
theorem B401213 : Blo 235815 401213 := bbase (se 3 (by rfl) ⟨75227, by rfl⟩ : syracuseStep 401213 = 150455) (by norm_num)
theorem B532349 : Blo 235815 532349 := bbase (se 3 (by rfl) ⟨99815, by rfl⟩ : syracuseStep 532349 = 199631) (by norm_num)
theorem B597901 : Blo 235815 597901 := bbase (se 3 (by rfl) ⟨112106, by rfl⟩ : syracuseStep 597901 = 224213) (by norm_num)
theorem B335773 : Blo 235815 335773 := bbase (se 3 (by rfl) ⟨62957, by rfl⟩ : syracuseStep 335773 = 125915) (by norm_num)
theorem B303005 : Blo 235815 303005 := bbase (se 3 (by rfl) ⟨56813, by rfl⟩ : syracuseStep 303005 = 113627) (by norm_num)
theorem B401341 : Blo 235815 401341 := bbase (se 3 (by rfl) ⟨75251, by rfl⟩ : syracuseStep 401341 = 150503) (by norm_num)
theorem B303041 : Blo 235815 303041 := bbase (se 2 (by rfl) ⟨113640, by rfl⟩ : syracuseStep 303041 = 227281) (by norm_num)
theorem B532421 : Blo 235815 532421 := bbase (se 4 (by rfl) ⟨49914, by rfl⟩ : syracuseStep 532421 = 99829) (by norm_num)
theorem B303097 : Blo 235815 303097 := bbase (se 2 (by rfl) ⟨113661, by rfl⟩ : syracuseStep 303097 = 227323) (by norm_num)
theorem B598013 : Blo 235815 598013 := bbase (se 3 (by rfl) ⟨112127, by rfl⟩ : syracuseStep 598013 = 224255) (by norm_num)
theorem B860165 : Blo 235815 860165 := bbase (se 4 (by rfl) ⟨80640, by rfl⟩ : syracuseStep 860165 = 161281) (by norm_num)
theorem B532493 : Blo 235815 532493 := bbase (se 3 (by rfl) ⟨99842, by rfl⟩ : syracuseStep 532493 = 199685) (by norm_num)
theorem B401429 : Blo 235815 401429 := bbase (se 6 (by rfl) ⟨9408, by rfl⟩ : syracuseStep 401429 = 18817) (by norm_num)
theorem B532565 : Blo 235815 532565 := bbase (se 8 (by rfl) ⟨3120, by rfl⟩ : syracuseStep 532565 = 6241) (by norm_num)
theorem B303193 : Blo 235815 303193 := bbase (se 2 (by rfl) ⟨113697, by rfl⟩ : syracuseStep 303193 = 227395) (by norm_num)
theorem B401557 : Blo 235815 401557 := bbase (se 6 (by rfl) ⟨9411, by rfl⟩ : syracuseStep 401557 = 18823) (by norm_num)
theorem B532637 : Blo 235815 532637 := bbase (se 3 (by rfl) ⟨99869, by rfl⟩ : syracuseStep 532637 = 199739) (by norm_num)
theorem B598205 : Blo 235815 598205 := bbase (se 3 (by rfl) ⟨112163, by rfl⟩ : syracuseStep 598205 = 224327) (by norm_num)
theorem B532709 : Blo 235815 532709 := bbase (se 4 (by rfl) ⟨49941, by rfl⟩ : syracuseStep 532709 = 99883) (by norm_num)
theorem B401645 : Blo 235815 401645 := bbase (se 3 (by rfl) ⟨75308, by rfl⟩ : syracuseStep 401645 = 150617) (by norm_num)
theorem B303365 : Blo 235815 303365 := bbase (se 4 (by rfl) ⟨28440, by rfl⟩ : syracuseStep 303365 = 56881) (by norm_num)
theorem B1515797 : Blo 235815 1515797 := bbase (se 6 (by rfl) ⟨35526, by rfl⟩ : syracuseStep 1515797 = 71053) (by norm_num)
theorem B532781 : Blo 235815 532781 := bbase (se 3 (by rfl) ⟨99896, by rfl⟩ : syracuseStep 532781 = 199793) (by norm_num)
theorem B303421 : Blo 235815 303421 := bbase (se 3 (by rfl) ⟨56891, by rfl⟩ : syracuseStep 303421 = 113783) (by norm_num)
theorem B401773 : Blo 235815 401773 := bbase (se 3 (by rfl) ⟨75332, by rfl⟩ : syracuseStep 401773 = 150665) (by norm_num)
theorem B532853 : Blo 235815 532853 := bbase (se 5 (by rfl) ⟨24977, by rfl⟩ : syracuseStep 532853 = 49955) (by norm_num)
theorem B1286549 : Blo 235815 1286549 := bbase (se 6 (by rfl) ⟨30153, by rfl⟩ : syracuseStep 1286549 = 60307) (by norm_num)
theorem B303517 : Blo 235815 303517 := bbase (se 3 (by rfl) ⟨56909, by rfl⟩ : syracuseStep 303517 = 113819) (by norm_num)
theorem B303545 : Blo 235815 303545 := bbase (se 2 (by rfl) ⟨113829, by rfl⟩ : syracuseStep 303545 = 227659) (by norm_num)
theorem B532925 : Blo 235815 532925 := bbase (se 3 (by rfl) ⟨99923, by rfl⟩ : syracuseStep 532925 = 199847) (by norm_num)
theorem B401861 : Blo 235815 401861 := bbase (se 4 (by rfl) ⟨37674, by rfl⟩ : syracuseStep 401861 = 75349) (by norm_num)
theorem B532997 : Blo 235815 532997 := bbase (se 4 (by rfl) ⟨49968, by rfl⟩ : syracuseStep 532997 = 99937) (by norm_num)
theorem B598549 : Blo 235815 598549 := bbase (se 6 (by rfl) ⟨14028, by rfl⟩ : syracuseStep 598549 = 28057) (by norm_num)
theorem B401989 : Blo 235815 401989 := bbase (se 4 (by rfl) ⟨37686, by rfl⟩ : syracuseStep 401989 = 75373) (by norm_num)
theorem B533069 : Blo 235815 533069 := bbase (se 3 (by rfl) ⟨99950, by rfl⟩ : syracuseStep 533069 = 199901) (by norm_num)
theorem B598661 : Blo 235815 598661 := bbase (se 4 (by rfl) ⟨56124, by rfl⟩ : syracuseStep 598661 = 112249) (by norm_num)
theorem B533141 : Blo 235815 533141 := bbase (se 6 (by rfl) ⟨12495, by rfl⟩ : syracuseStep 533141 = 24991) (by norm_num)
theorem B303769 : Blo 235815 303769 := bbase (se 2 (by rfl) ⟨113913, by rfl⟩ : syracuseStep 303769 = 227827) (by norm_num)
theorem B402077 : Blo 235815 402077 := bbase (se 3 (by rfl) ⟨75389, by rfl⟩ : syracuseStep 402077 = 150779) (by norm_num)
theorem B336565 : Blo 235815 336565 := bbase (se 5 (by rfl) ⟨15776, by rfl⟩ : syracuseStep 336565 = 31553) (by norm_num)
theorem B533213 : Blo 235815 533213 := bbase (se 3 (by rfl) ⟨99977, by rfl⟩ : syracuseStep 533213 = 199955) (by norm_num)
theorem B303853 : Blo 235815 303853 := bbase (se 3 (by rfl) ⟨56972, by rfl⟩ : syracuseStep 303853 = 113945) (by norm_num)
theorem B402205 : Blo 235815 402205 := bbase (se 3 (by rfl) ⟨75413, by rfl⟩ : syracuseStep 402205 = 150827) (by norm_num)
theorem B533285 : Blo 235815 533285 := bbase (se 4 (by rfl) ⟨49995, by rfl⟩ : syracuseStep 533285 = 99991) (by norm_num)
theorem B598853 : Blo 235815 598853 := bbase (se 4 (by rfl) ⟨56142, by rfl⟩ : syracuseStep 598853 = 112285) (by norm_num)
theorem B533357 : Blo 235815 533357 := bbase (se 3 (by rfl) ⟨100004, by rfl⟩ : syracuseStep 533357 = 200009) (by norm_num)
theorem B402293 : Blo 235815 402293 := bbase (se 5 (by rfl) ⟨18857, by rfl⟩ : syracuseStep 402293 = 37715) (by norm_num)
theorem B533429 : Blo 235815 533429 := bbase (se 5 (by rfl) ⟨25004, by rfl⟩ : syracuseStep 533429 = 50009) (by norm_num)
theorem B402421 : Blo 235815 402421 := bbase (se 5 (by rfl) ⟨18863, by rfl⟩ : syracuseStep 402421 = 37727) (by norm_num)
theorem B533501 : Blo 235815 533501 := bbase (se 3 (by rfl) ⟨100031, by rfl⟩ : syracuseStep 533501 = 200063) (by norm_num)
theorem B336901 : Blo 235815 336901 := bbase (se 4 (by rfl) ⟨31584, by rfl⟩ : syracuseStep 336901 = 63169) (by norm_num)
theorem B533573 : Blo 235815 533573 := bbase (se 4 (by rfl) ⟨50022, by rfl⟩ : syracuseStep 533573 = 100045) (by norm_num)
theorem B402509 : Blo 235815 402509 := bbase (se 3 (by rfl) ⟨75470, by rfl⟩ : syracuseStep 402509 = 150941) (by norm_num)
theorem B763013 : Blo 235815 763013 := bbase (se 4 (by rfl) ⟨71532, by rfl⟩ : syracuseStep 763013 = 143065) (by norm_num)
theorem B533645 : Blo 235815 533645 := bbase (se 3 (by rfl) ⟨100058, by rfl⟩ : syracuseStep 533645 = 200117) (by norm_num)
theorem B599197 : Blo 235815 599197 := bbase (se 3 (by rfl) ⟨112349, by rfl⟩ : syracuseStep 599197 = 224699) (by norm_num)
theorem B402637 : Blo 235815 402637 := bbase (se 3 (by rfl) ⟨75494, by rfl⟩ : syracuseStep 402637 = 150989) (by norm_num)
theorem B533717 : Blo 235815 533717 := bbase (se 7 (by rfl) ⟨6254, by rfl⟩ : syracuseStep 533717 = 12509) (by norm_num)
theorem B337117 : Blo 235815 337117 := bbase (se 3 (by rfl) ⟨63209, by rfl⟩ : syracuseStep 337117 = 126419) (by norm_num)
theorem B599309 : Blo 235815 599309 := bbase (se 3 (by rfl) ⟨112370, by rfl⟩ : syracuseStep 599309 = 224741) (by norm_num)
theorem B533789 : Blo 235815 533789 := bbase (se 3 (by rfl) ⟨100085, by rfl⟩ : syracuseStep 533789 = 200171) (by norm_num)
theorem B402725 : Blo 235815 402725 := bbase (se 4 (by rfl) ⟨37755, by rfl⟩ : syracuseStep 402725 = 75511) (by norm_num)
theorem B533861 : Blo 235815 533861 := bbase (se 4 (by rfl) ⟨50049, by rfl⟩ : syracuseStep 533861 = 100099) (by norm_num)
theorem B402853 : Blo 235815 402853 := bbase (se 4 (by rfl) ⟨37767, by rfl⟩ : syracuseStep 402853 = 75535) (by norm_num)
theorem B533933 : Blo 235815 533933 := bbase (se 3 (by rfl) ⟨100112, by rfl⟩ : syracuseStep 533933 = 200225) (by norm_num)
theorem B599501 : Blo 235815 599501 := bbase (se 3 (by rfl) ⟨112406, by rfl⟩ : syracuseStep 599501 = 224813) (by norm_num)
theorem B534005 : Blo 235815 534005 := bbase (se 5 (by rfl) ⟨25031, by rfl⟩ : syracuseStep 534005 = 50063) (by norm_num)
theorem B402941 : Blo 235815 402941 := bbase (se 3 (by rfl) ⟨75551, by rfl⟩ : syracuseStep 402941 = 151103) (by norm_num)
theorem B534077 : Blo 235815 534077 := bbase (se 3 (by rfl) ⟨100139, by rfl⟩ : syracuseStep 534077 = 200279) (by norm_num)
theorem B796229 : Blo 235815 796229 := bbase (se 4 (by rfl) ⟨74646, by rfl⟩ : syracuseStep 796229 = 149293) (by norm_num)
theorem B337493 : Blo 235815 337493 := bbase (se 8 (by rfl) ⟨1977, by rfl⟩ : syracuseStep 337493 = 3955) (by norm_num)
theorem B403069 : Blo 235815 403069 := bbase (se 3 (by rfl) ⟨75575, by rfl⟩ : syracuseStep 403069 = 151151) (by norm_num)
theorem B534149 : Blo 235815 534149 := bbase (se 4 (by rfl) ⟨50076, by rfl⟩ : syracuseStep 534149 = 100153) (by norm_num)
theorem B534221 : Blo 235815 534221 := bbase (se 3 (by rfl) ⟨100166, by rfl⟩ : syracuseStep 534221 = 200333) (by norm_num)
theorem B403157 : Blo 235815 403157 := bbase (se 7 (by rfl) ⟨4724, by rfl⟩ : syracuseStep 403157 = 9449) (by norm_num)
theorem B534293 : Blo 235815 534293 := bbase (se 6 (by rfl) ⟨12522, by rfl⟩ : syracuseStep 534293 = 25045) (by norm_num)
theorem B599845 : Blo 235815 599845 := bbase (se 4 (by rfl) ⟨56235, by rfl⟩ : syracuseStep 599845 = 112471) (by norm_num)
theorem B403285 : Blo 235815 403285 := bbase (se 9 (by rfl) ⟨1181, by rfl⟩ : syracuseStep 403285 = 2363) (by norm_num)
theorem B534365 : Blo 235815 534365 := bbase (se 3 (by rfl) ⟨100193, by rfl⟩ : syracuseStep 534365 = 200387) (by norm_num)
theorem B599957 : Blo 235815 599957 := bbase (se 6 (by rfl) ⟨14061, by rfl⟩ : syracuseStep 599957 = 28123) (by norm_num)
theorem B534437 : Blo 235815 534437 := bbase (se 4 (by rfl) ⟨50103, by rfl⟩ : syracuseStep 534437 = 100207) (by norm_num)
theorem B403373 : Blo 235815 403373 := bbase (se 3 (by rfl) ⟨75632, by rfl⟩ : syracuseStep 403373 = 151265) (by norm_num)
theorem B239545 : Blo 235815 239545 := bbase (se 2 (by rfl) ⟨89829, by rfl⟩ : syracuseStep 239545 = 179659) (by norm_num)
theorem B534509 : Blo 235815 534509 := bbase (se 3 (by rfl) ⟨100220, by rfl⟩ : syracuseStep 534509 = 200441) (by norm_num)
theorem B796661 : Blo 235815 796661 := bbase (se 5 (by rfl) ⟨37343, by rfl⟩ : syracuseStep 796661 = 74687) (by norm_num)
theorem B403501 : Blo 235815 403501 := bbase (se 3 (by rfl) ⟨75656, by rfl⟩ : syracuseStep 403501 = 151313) (by norm_num)
theorem B534581 : Blo 235815 534581 := bbase (se 5 (by rfl) ⟨25058, by rfl⟩ : syracuseStep 534581 = 50117) (by norm_num)
theorem B600149 : Blo 235815 600149 := bbase (se 8 (by rfl) ⟨3516, by rfl⟩ : syracuseStep 600149 = 7033) (by norm_num)
theorem B534653 : Blo 235815 534653 := bbase (se 3 (by rfl) ⟨100247, by rfl⟩ : syracuseStep 534653 = 200495) (by norm_num)
theorem B403589 : Blo 235815 403589 := bbase (se 4 (by rfl) ⟨37836, by rfl⟩ : syracuseStep 403589 = 75673) (by norm_num)
theorem B534725 : Blo 235815 534725 := bbase (se 4 (by rfl) ⟨50130, by rfl⟩ : syracuseStep 534725 = 100261) (by norm_num)
theorem B403685 : Blo 235815 403685 := bbase (se 4 (by rfl) ⟨37845, by rfl⟩ : syracuseStep 403685 = 75691) (by norm_num)
theorem B403717 : Blo 235815 403717 := bbase (se 4 (by rfl) ⟨37848, by rfl⟩ : syracuseStep 403717 = 75697) (by norm_num)
theorem B534797 : Blo 235815 534797 := bbase (se 3 (by rfl) ⟨100274, by rfl⟩ : syracuseStep 534797 = 200549) (by norm_num)
theorem B534869 : Blo 235815 534869 := bbase (se 10 (by rfl) ⟨783, by rfl⟩ : syracuseStep 534869 = 1567) (by norm_num)
theorem B403805 : Blo 235815 403805 := bbase (se 3 (by rfl) ⟨75713, by rfl⟩ : syracuseStep 403805 = 151427) (by norm_num)
theorem B862613 : Blo 235815 862613 := bbase (se 6 (by rfl) ⟨20217, by rfl⟩ : syracuseStep 862613 = 40435) (by norm_num)
theorem B534941 : Blo 235815 534941 := bbase (se 3 (by rfl) ⟨100301, by rfl⟩ : syracuseStep 534941 = 200603) (by norm_num)
theorem B797093 : Blo 235815 797093 := bbase (se 4 (by rfl) ⟨74727, by rfl⟩ : syracuseStep 797093 = 149455) (by norm_num)
theorem B993701 : Blo 235815 993701 := bbase (se 4 (by rfl) ⟨93159, by rfl⟩ : syracuseStep 993701 = 186319) (by norm_num)
theorem B600493 : Blo 235815 600493 := bbase (se 3 (by rfl) ⟨112592, by rfl⟩ : syracuseStep 600493 = 225185) (by norm_num)
theorem B403933 : Blo 235815 403933 := bbase (se 3 (by rfl) ⟨75737, by rfl⟩ : syracuseStep 403933 = 151475) (by norm_num)
theorem B535013 : Blo 235815 535013 := bbase (se 4 (by rfl) ⟨50157, by rfl⟩ : syracuseStep 535013 = 100315) (by norm_num)
theorem B600605 : Blo 235815 600605 := bbase (se 3 (by rfl) ⟨112613, by rfl⟩ : syracuseStep 600605 = 225227) (by norm_num)
theorem B535085 : Blo 235815 535085 := bbase (se 3 (by rfl) ⟨100328, by rfl⟩ : syracuseStep 535085 = 200657) (by norm_num)
theorem B404021 : Blo 235815 404021 := bbase (se 5 (by rfl) ⟨18938, by rfl⟩ : syracuseStep 404021 = 37877) (by norm_num)
theorem B535157 : Blo 235815 535157 := bbase (se 5 (by rfl) ⟨25085, by rfl⟩ : syracuseStep 535157 = 50171) (by norm_num)
theorem B305797 : Blo 235815 305797 := bbase (se 4 (by rfl) ⟨28668, by rfl⟩ : syracuseStep 305797 = 57337) (by norm_num)
theorem B895637 : Blo 235815 895637 := bbase (se 6 (by rfl) ⟨20991, by rfl⟩ : syracuseStep 895637 = 41983) (by norm_num)
theorem B404149 : Blo 235815 404149 := bbase (se 5 (by rfl) ⟨18944, by rfl⟩ : syracuseStep 404149 = 37889) (by norm_num)
theorem B535229 : Blo 235815 535229 := bbase (se 3 (by rfl) ⟨100355, by rfl⟩ : syracuseStep 535229 = 200711) (by norm_num)
theorem B600797 : Blo 235815 600797 := bbase (se 3 (by rfl) ⟨112649, by rfl⟩ : syracuseStep 600797 = 225299) (by norm_num)
theorem B535301 : Blo 235815 535301 := bbase (se 4 (by rfl) ⟨50184, by rfl⟩ : syracuseStep 535301 = 100369) (by norm_num)
theorem B404237 : Blo 235815 404237 := bbase (se 3 (by rfl) ⟨75794, by rfl⟩ : syracuseStep 404237 = 151589) (by norm_num)
theorem B535373 : Blo 235815 535373 := bbase (se 3 (by rfl) ⟨100382, by rfl⟩ : syracuseStep 535373 = 200765) (by norm_num)
theorem B797525 : Blo 235815 797525 := bbase (se 9 (by rfl) ⟨2336, by rfl⟩ : syracuseStep 797525 = 4673) (by norm_num)
theorem B404365 : Blo 235815 404365 := bbase (se 3 (by rfl) ⟨75818, by rfl⟩ : syracuseStep 404365 = 151637) (by norm_num)
theorem B535445 : Blo 235815 535445 := bbase (se 6 (by rfl) ⟨12549, by rfl⟩ : syracuseStep 535445 = 25099) (by norm_num)
theorem B535517 : Blo 235815 535517 := bbase (se 3 (by rfl) ⟨100409, by rfl⟩ : syracuseStep 535517 = 200819) (by norm_num)
theorem B338917 : Blo 235815 338917 := bbase (se 4 (by rfl) ⟨31773, by rfl⟩ : syracuseStep 338917 = 63547) (by norm_num)
theorem B928741 : Blo 235815 928741 := bbase (se 4 (by rfl) ⟨87069, by rfl⟩ : syracuseStep 928741 = 174139) (by norm_num)
theorem B404453 : Blo 235815 404453 := bbase (se 4 (by rfl) ⟨37917, by rfl⟩ : syracuseStep 404453 = 75835) (by norm_num)
theorem B568309 : Blo 235815 568309 := bbase (se 5 (by rfl) ⟨26639, by rfl⟩ : syracuseStep 568309 = 53279) (by norm_num)
theorem B1027093 : Blo 235815 1027093 := bbase (se 6 (by rfl) ⟨24072, by rfl⟩ : syracuseStep 1027093 = 48145) (by norm_num)
theorem B535589 : Blo 235815 535589 := bbase (se 4 (by rfl) ⟨50211, by rfl⟩ : syracuseStep 535589 = 100423) (by norm_num)
theorem B601141 : Blo 235815 601141 := bbase (se 5 (by rfl) ⟨28178, by rfl⟩ : syracuseStep 601141 = 56357) (by norm_num)
theorem B404581 : Blo 235815 404581 := bbase (se 4 (by rfl) ⟨37929, by rfl⟩ : syracuseStep 404581 = 75859) (by norm_num)
theorem B535661 : Blo 235815 535661 := bbase (se 3 (by rfl) ⟨100436, by rfl⟩ : syracuseStep 535661 = 200873) (by norm_num)
theorem B601253 : Blo 235815 601253 := bbase (se 4 (by rfl) ⟨56367, by rfl⟩ : syracuseStep 601253 = 112735) (by norm_num)
theorem B535733 : Blo 235815 535733 := bbase (se 5 (by rfl) ⟨25112, by rfl⟩ : syracuseStep 535733 = 50225) (by norm_num)
theorem B404669 : Blo 235815 404669 := bbase (se 3 (by rfl) ⟨75875, by rfl⟩ : syracuseStep 404669 = 151751) (by norm_num)
theorem B535805 : Blo 235815 535805 := bbase (se 3 (by rfl) ⟨100463, by rfl⟩ : syracuseStep 535805 = 200927) (by norm_num)
theorem B797957 : Blo 235815 797957 := bbase (se 4 (by rfl) ⟨74808, by rfl⟩ : syracuseStep 797957 = 149617) (by norm_num)
theorem B535877 : Blo 235815 535877 := bbase (se 4 (by rfl) ⟨50238, by rfl⟩ : syracuseStep 535877 = 100477) (by norm_num)
theorem B3026261 : Blo 235815 3026261 := bbase (se 11 (by rfl) ⟨2216, by rfl⟩ : syracuseStep 3026261 = 4433) (by norm_num)
theorem B601445 : Blo 235815 601445 := bbase (se 4 (by rfl) ⟨56385, by rfl⟩ : syracuseStep 601445 = 112771) (by norm_num)
theorem B535949 : Blo 235815 535949 := bbase (se 3 (by rfl) ⟨100490, by rfl⟩ : syracuseStep 535949 = 200981) (by norm_num)
theorem B536021 : Blo 235815 536021 := bbase (se 7 (by rfl) ⟨6281, by rfl⟩ : syracuseStep 536021 = 12563) (by norm_num)
theorem B536093 : Blo 235815 536093 := bbase (se 3 (by rfl) ⟨100517, by rfl⟩ : syracuseStep 536093 = 201035) (by norm_num)
theorem B339509 : Blo 235815 339509 := bbase (se 5 (by rfl) ⟨15914, by rfl⟩ : syracuseStep 339509 = 31829) (by norm_num)
theorem B536165 : Blo 235815 536165 := bbase (se 4 (by rfl) ⟨50265, by rfl⟩ : syracuseStep 536165 = 100531) (by norm_num)
theorem B339589 : Blo 235815 339589 := bbase (se 4 (by rfl) ⟨31836, by rfl⟩ : syracuseStep 339589 = 63673) (by norm_num)
theorem B536237 : Blo 235815 536237 := bbase (se 3 (by rfl) ⟨100544, by rfl⟩ : syracuseStep 536237 = 201089) (by norm_num)
theorem B798389 : Blo 235815 798389 := bbase (se 5 (by rfl) ⟨37424, by rfl⟩ : syracuseStep 798389 = 74849) (by norm_num)
theorem B601789 : Blo 235815 601789 := bbase (se 3 (by rfl) ⟨112835, by rfl⟩ : syracuseStep 601789 = 225671) (by norm_num)
theorem B437981 : Blo 235815 437981 := bbase (se 3 (by rfl) ⟨82121, by rfl⟩ : syracuseStep 437981 = 164243) (by norm_num)
theorem B536309 : Blo 235815 536309 := bbase (se 5 (by rfl) ⟨25139, by rfl⟩ : syracuseStep 536309 = 50279) (by norm_num)
theorem B339709 : Blo 235815 339709 := bbase (se 3 (by rfl) ⟨63695, by rfl⟩ : syracuseStep 339709 = 127391) (by norm_num)
theorem B3059477 : Blo 235815 3059477 := bbase (se 6 (by rfl) ⟨71706, by rfl⟩ : syracuseStep 3059477 = 143413) (by norm_num)
theorem B601901 : Blo 235815 601901 := bbase (se 3 (by rfl) ⟨112856, by rfl⟩ : syracuseStep 601901 = 225713) (by norm_num)
theorem B1945397 : Blo 235815 1945397 := bbase (se 5 (by rfl) ⟨91190, by rfl⟩ : syracuseStep 1945397 = 182381) (by norm_num)
theorem B536381 : Blo 235815 536381 := bbase (se 3 (by rfl) ⟨100571, by rfl⟩ : syracuseStep 536381 = 201143) (by norm_num)
theorem B339805 : Blo 235815 339805 := bbase (se 3 (by rfl) ⟨63713, by rfl⟩ : syracuseStep 339805 = 127427) (by norm_num)
theorem B1027957 : Blo 235815 1027957 := bbase (se 5 (by rfl) ⟨48185, by rfl⟩ : syracuseStep 1027957 = 96371) (by norm_num)
theorem B536453 : Blo 235815 536453 := bbase (se 4 (by rfl) ⟨50292, by rfl⟩ : syracuseStep 536453 = 100585) (by norm_num)
theorem B765845 : Blo 235815 765845 := bbase (se 6 (by rfl) ⟨17949, by rfl⟩ : syracuseStep 765845 = 35899) (by norm_num)
theorem B536525 : Blo 235815 536525 := bbase (se 3 (by rfl) ⟨100598, by rfl⟩ : syracuseStep 536525 = 201197) (by norm_num)
theorem B602093 : Blo 235815 602093 := bbase (se 3 (by rfl) ⟨112892, by rfl⟩ : syracuseStep 602093 = 225785) (by norm_num)
theorem B536597 : Blo 235815 536597 := bbase (se 6 (by rfl) ⟨12576, by rfl⟩ : syracuseStep 536597 = 25153) (by norm_num)
theorem B536669 : Blo 235815 536669 := bbase (se 3 (by rfl) ⟨100625, by rfl⟩ : syracuseStep 536669 = 201251) (by norm_num)
theorem B798821 : Blo 235815 798821 := bbase (se 4 (by rfl) ⟨74889, by rfl⟩ : syracuseStep 798821 = 149779) (by norm_num)
theorem B569501 : Blo 235815 569501 := bbase (se 3 (by rfl) ⟨106781, by rfl⟩ : syracuseStep 569501 = 213563) (by norm_num)
theorem B536741 : Blo 235815 536741 := bbase (se 4 (by rfl) ⟨50319, by rfl⟩ : syracuseStep 536741 = 100639) (by norm_num)
theorem B536813 : Blo 235815 536813 := bbase (se 3 (by rfl) ⟨100652, by rfl⟩ : syracuseStep 536813 = 201305) (by norm_num)
theorem B504053 : Blo 235815 504053 := bbase (se 5 (by rfl) ⟨23627, by rfl⟩ : syracuseStep 504053 = 47255) (by norm_num)
theorem B536885 : Blo 235815 536885 := bbase (se 5 (by rfl) ⟨25166, by rfl⟩ : syracuseStep 536885 = 50333) (by norm_num)
theorem B602437 : Blo 235815 602437 := bbase (se 4 (by rfl) ⟨56478, by rfl⟩ : syracuseStep 602437 = 112957) (by norm_num)
theorem B340301 : Blo 235815 340301 := bbase (se 3 (by rfl) ⟨63806, by rfl⟩ : syracuseStep 340301 = 127613) (by norm_num)
theorem B569693 : Blo 235815 569693 := bbase (se 3 (by rfl) ⟨106817, by rfl⟩ : syracuseStep 569693 = 213635) (by norm_num)
theorem B536957 : Blo 235815 536957 := bbase (se 3 (by rfl) ⟨100679, by rfl⟩ : syracuseStep 536957 = 201359) (by norm_num)
theorem B602549 : Blo 235815 602549 := bbase (se 5 (by rfl) ⟨28244, by rfl⟩ : syracuseStep 602549 = 56489) (by norm_num)
theorem B537029 : Blo 235815 537029 := bbase (se 4 (by rfl) ⟨50346, by rfl⟩ : syracuseStep 537029 = 100693) (by norm_num)
theorem B504301 : Blo 235815 504301 := bbase (se 3 (by rfl) ⟨94556, by rfl⟩ : syracuseStep 504301 = 189113) (by norm_num)
theorem B537101 : Blo 235815 537101 := bbase (se 3 (by rfl) ⟨100706, by rfl⟩ : syracuseStep 537101 = 201413) (by norm_num)
theorem B799253 : Blo 235815 799253 := bbase (se 6 (by rfl) ⟨18732, by rfl⟩ : syracuseStep 799253 = 37465) (by norm_num)
theorem B242237 : Blo 235815 242237 := bbase (se 3 (by rfl) ⟨45419, by rfl⟩ : syracuseStep 242237 = 90839) (by norm_num)
theorem B537173 : Blo 235815 537173 := bbase (se 8 (by rfl) ⟨3147, by rfl⟩ : syracuseStep 537173 = 6295) (by norm_num)
theorem B602741 : Blo 235815 602741 := bbase (se 5 (by rfl) ⟨28253, by rfl⟩ : syracuseStep 602741 = 56507) (by norm_num)
theorem B537245 : Blo 235815 537245 := bbase (se 3 (by rfl) ⟨100733, by rfl⟩ : syracuseStep 537245 = 201467) (by norm_num)
theorem B897749 : Blo 235815 897749 := bbase (se 7 (by rfl) ⟨10520, by rfl⟩ : syracuseStep 897749 = 21041) (by norm_num)
theorem B537317 : Blo 235815 537317 := bbase (se 4 (by rfl) ⟨50373, by rfl⟩ : syracuseStep 537317 = 100747) (by norm_num)
theorem B1356533 : Blo 235815 1356533 := bbase (se 5 (by rfl) ⟨63587, by rfl⟩ : syracuseStep 1356533 = 127175) (by norm_num)
theorem B766741 : Blo 235815 766741 := bbase (se 6 (by rfl) ⟨17970, by rfl⟩ : syracuseStep 766741 = 35941) (by norm_num)
theorem B242461 : Blo 235815 242461 := bbase (se 3 (by rfl) ⟨45461, by rfl⟩ : syracuseStep 242461 = 90923) (by norm_num)
theorem B537389 : Blo 235815 537389 := bbase (se 3 (by rfl) ⟨100760, by rfl⟩ : syracuseStep 537389 = 201521) (by norm_num)
theorem B537461 : Blo 235815 537461 := bbase (se 5 (by rfl) ⟨25193, by rfl⟩ : syracuseStep 537461 = 50387) (by norm_num)
theorem B340853 : Blo 235815 340853 := bbase (se 5 (by rfl) ⟨15977, by rfl⟩ : syracuseStep 340853 = 31955) (by norm_num)
theorem B537533 : Blo 235815 537533 := bbase (se 3 (by rfl) ⟨100787, by rfl⟩ : syracuseStep 537533 = 201575) (by norm_num)
theorem B799685 : Blo 235815 799685 := bbase (se 4 (by rfl) ⟨74970, by rfl⟩ : syracuseStep 799685 = 149941) (by norm_num)
theorem B603085 : Blo 235815 603085 := bbase (se 3 (by rfl) ⟨113078, by rfl⟩ : syracuseStep 603085 = 226157) (by norm_num)
theorem B504805 : Blo 235815 504805 := bbase (se 4 (by rfl) ⟨47325, by rfl⟩ : syracuseStep 504805 = 94651) (by norm_num)
theorem B898037 : Blo 235815 898037 := bbase (se 5 (by rfl) ⟨42095, by rfl⟩ : syracuseStep 898037 = 84191) (by norm_num)
theorem B406525 : Blo 235815 406525 := bbase (se 3 (by rfl) ⟨76223, by rfl⟩ : syracuseStep 406525 = 152447) (by norm_num)
theorem B537605 : Blo 235815 537605 := bbase (se 4 (by rfl) ⟨50400, by rfl⟩ : syracuseStep 537605 = 100801) (by norm_num)
theorem B603197 : Blo 235815 603197 := bbase (se 3 (by rfl) ⟨113099, by rfl⟩ : syracuseStep 603197 = 226199) (by norm_num)
theorem B537677 : Blo 235815 537677 := bbase (se 3 (by rfl) ⟨100814, by rfl⟩ : syracuseStep 537677 = 201629) (by norm_num)
theorem B2274389 : Blo 235815 2274389 := bbase (se 8 (by rfl) ⟨13326, by rfl⟩ : syracuseStep 2274389 = 26653) (by norm_num)
theorem B537749 : Blo 235815 537749 := bbase (se 6 (by rfl) ⟨12603, by rfl⟩ : syracuseStep 537749 = 25207) (by norm_num)
theorem B537821 : Blo 235815 537821 := bbase (se 3 (by rfl) ⟨100841, by rfl⟩ : syracuseStep 537821 = 201683) (by norm_num)
theorem B603389 : Blo 235815 603389 := bbase (se 3 (by rfl) ⟨113135, by rfl⟩ : syracuseStep 603389 = 226271) (by norm_num)
theorem B537893 : Blo 235815 537893 := bbase (se 4 (by rfl) ⟨50427, by rfl⟩ : syracuseStep 537893 = 100855) (by norm_num)
theorem B537965 : Blo 235815 537965 := bbase (se 3 (by rfl) ⟨100868, by rfl⟩ : syracuseStep 537965 = 201737) (by norm_num)
theorem B800117 : Blo 235815 800117 := bbase (se 5 (by rfl) ⟨37505, by rfl⟩ : syracuseStep 800117 = 75011) (by norm_num)
theorem B538037 : Blo 235815 538037 := bbase (se 5 (by rfl) ⟨25220, by rfl⟩ : syracuseStep 538037 = 50441) (by norm_num)
theorem B538093 : Blo 235815 538093 := bbase (se 3 (by rfl) ⟨100892, by rfl⟩ : syracuseStep 538093 = 201785) (by norm_num)
theorem B538109 : Blo 235815 538109 := bbase (se 3 (by rfl) ⟨100895, by rfl⟩ : syracuseStep 538109 = 201791) (by norm_num)
theorem B538181 : Blo 235815 538181 := bbase (se 4 (by rfl) ⟨50454, by rfl⟩ : syracuseStep 538181 = 100909) (by norm_num)
theorem B603733 : Blo 235815 603733 := bbase (se 8 (by rfl) ⟨3537, by rfl⟩ : syracuseStep 603733 = 7075) (by norm_num)
theorem B1816181 : Blo 235815 1816181 := bbase (se 5 (by rfl) ⟨85133, by rfl⟩ : syracuseStep 1816181 = 170267) (by norm_num)
theorem B538253 : Blo 235815 538253 := bbase (se 3 (by rfl) ⟨100922, by rfl⟩ : syracuseStep 538253 = 201845) (by norm_num)
theorem B407189 : Blo 235815 407189 := bbase (se 6 (by rfl) ⟨9543, by rfl⟩ : syracuseStep 407189 = 19087) (by norm_num)
theorem B603845 : Blo 235815 603845 := bbase (se 4 (by rfl) ⟨56610, by rfl⟩ : syracuseStep 603845 = 113221) (by norm_num)
theorem B538325 : Blo 235815 538325 := bbase (se 7 (by rfl) ⟨6308, by rfl⟩ : syracuseStep 538325 = 12617) (by norm_num)
theorem B538397 : Blo 235815 538397 := bbase (se 3 (by rfl) ⟨100949, by rfl⟩ : syracuseStep 538397 = 201899) (by norm_num)
theorem B800549 : Blo 235815 800549 := bbase (se 4 (by rfl) ⟨75051, by rfl⟩ : syracuseStep 800549 = 150103) (by norm_num)
theorem B505693 : Blo 235815 505693 := bbase (se 3 (by rfl) ⟨94817, by rfl⟩ : syracuseStep 505693 = 189635) (by norm_num)
theorem B538469 : Blo 235815 538469 := bbase (se 4 (by rfl) ⟨50481, by rfl⟩ : syracuseStep 538469 = 100963) (by norm_num)
theorem B2176885 : Blo 235815 2176885 := bbase (se 5 (by rfl) ⟨102041, by rfl⟩ : syracuseStep 2176885 = 204083) (by norm_num)
theorem B604037 : Blo 235815 604037 := bbase (se 4 (by rfl) ⟨56628, by rfl⟩ : syracuseStep 604037 = 113257) (by norm_num)
theorem B538541 : Blo 235815 538541 := bbase (se 3 (by rfl) ⟨100976, by rfl⟩ : syracuseStep 538541 = 201953) (by norm_num)
theorem B538613 : Blo 235815 538613 := bbase (se 5 (by rfl) ⟨25247, by rfl⟩ : syracuseStep 538613 = 50495) (by norm_num)
theorem B538685 : Blo 235815 538685 := bbase (se 3 (by rfl) ⟨101003, by rfl⟩ : syracuseStep 538685 = 202007) (by norm_num)
theorem B1194101 : Blo 235815 1194101 := bbase (se 5 (by rfl) ⟨55973, by rfl⟩ : syracuseStep 1194101 = 111947) (by norm_num)
theorem B538757 : Blo 235815 538757 := bbase (se 4 (by rfl) ⟨50508, by rfl⟩ : syracuseStep 538757 = 101017) (by norm_num)
theorem B899221 : Blo 235815 899221 := bbase (se 6 (by rfl) ⟨21075, by rfl⟩ : syracuseStep 899221 = 42151) (by norm_num)
theorem B538829 : Blo 235815 538829 := bbase (se 3 (by rfl) ⟨101030, by rfl⟩ : syracuseStep 538829 = 202061) (by norm_num)
theorem B800981 : Blo 235815 800981 := bbase (se 7 (by rfl) ⟨9386, by rfl⟩ : syracuseStep 800981 = 18773) (by norm_num)
theorem B604381 : Blo 235815 604381 := bbase (se 3 (by rfl) ⟨113321, by rfl⟩ : syracuseStep 604381 = 226643) (by norm_num)
theorem B538901 : Blo 235815 538901 := bbase (se 6 (by rfl) ⟨12630, by rfl⟩ : syracuseStep 538901 = 25261) (by norm_num)
theorem B506189 : Blo 235815 506189 := bbase (se 3 (by rfl) ⟨94910, by rfl⟩ : syracuseStep 506189 = 189821) (by norm_num)
theorem B604493 : Blo 235815 604493 := bbase (se 3 (by rfl) ⟨113342, by rfl⟩ : syracuseStep 604493 = 226685) (by norm_num)
theorem B538973 : Blo 235815 538973 := bbase (se 3 (by rfl) ⟨101057, by rfl⟩ : syracuseStep 538973 = 202115) (by norm_num)
theorem B539045 : Blo 235815 539045 := bbase (se 4 (by rfl) ⟨50535, by rfl⟩ : syracuseStep 539045 = 101071) (by norm_num)
theorem B899525 : Blo 235815 899525 := bbase (se 4 (by rfl) ⟨84330, by rfl⟩ : syracuseStep 899525 = 168661) (by norm_num)
theorem B539117 : Blo 235815 539117 := bbase (se 3 (by rfl) ⟨101084, by rfl⟩ : syracuseStep 539117 = 202169) (by norm_num)
theorem B604685 : Blo 235815 604685 := bbase (se 3 (by rfl) ⟨113378, by rfl⟩ : syracuseStep 604685 = 226757) (by norm_num)
theorem B2046485 : Blo 235815 2046485 := bbase (se 6 (by rfl) ⟨47964, by rfl⟩ : syracuseStep 2046485 = 95929) (by norm_num)
theorem B539189 : Blo 235815 539189 := bbase (se 5 (by rfl) ⟨25274, by rfl⟩ : syracuseStep 539189 = 50549) (by norm_num)
theorem B571981 : Blo 235815 571981 := bbase (se 3 (by rfl) ⟨107246, by rfl⟩ : syracuseStep 571981 = 214493) (by norm_num)
theorem B539261 : Blo 235815 539261 := bbase (se 3 (by rfl) ⟨101111, by rfl⟩ : syracuseStep 539261 = 202223) (by norm_num)
theorem B801413 : Blo 235815 801413 := bbase (se 4 (by rfl) ⟨75132, by rfl⟩ : syracuseStep 801413 = 150265) (by norm_num)
theorem B539333 : Blo 235815 539333 := bbase (se 4 (by rfl) ⟨50562, by rfl⟩ : syracuseStep 539333 = 101125) (by norm_num)
theorem B539405 : Blo 235815 539405 := bbase (se 3 (by rfl) ⟨101138, by rfl⟩ : syracuseStep 539405 = 202277) (by norm_num)
theorem B539477 : Blo 235815 539477 := bbase (se 9 (by rfl) ⟨1580, by rfl⟩ : syracuseStep 539477 = 3161) (by norm_num)
theorem B605029 : Blo 235815 605029 := bbase (se 4 (by rfl) ⟨56721, by rfl⟩ : syracuseStep 605029 = 113443) (by norm_num)
theorem B539549 : Blo 235815 539549 := bbase (se 3 (by rfl) ⟨101165, by rfl⟩ : syracuseStep 539549 = 202331) (by norm_num)
theorem B605141 : Blo 235815 605141 := bbase (se 7 (by rfl) ⟨7091, by rfl⟩ : syracuseStep 605141 = 14183) (by norm_num)
theorem B801845 : Blo 235815 801845 := bbase (se 5 (by rfl) ⟨37586, by rfl⟩ : syracuseStep 801845 = 75173) (by norm_num)
theorem B605333 : Blo 235815 605333 := bbase (se 6 (by rfl) ⟨14187, by rfl⟩ : syracuseStep 605333 = 28375) (by norm_num)
theorem B507077 : Blo 235815 507077 := bbase (se 4 (by rfl) ⟨47538, by rfl⟩ : syracuseStep 507077 = 95077) (by norm_num)
theorem B572645 : Blo 235815 572645 := bbase (se 4 (by rfl) ⟨53685, by rfl⟩ : syracuseStep 572645 = 107371) (by norm_num)
theorem B507197 : Blo 235815 507197 := bbase (se 3 (by rfl) ⟨95099, by rfl⟩ : syracuseStep 507197 = 190199) (by norm_num)
theorem B1195397 : Blo 235815 1195397 := bbase (se 4 (by rfl) ⟨112068, by rfl⟩ : syracuseStep 1195397 = 224137) (by norm_num)
theorem B802277 : Blo 235815 802277 := bbase (se 4 (by rfl) ⟨75213, by rfl⟩ : syracuseStep 802277 = 150427) (by norm_num)
theorem B605677 : Blo 235815 605677 := bbase (se 3 (by rfl) ⟨113564, by rfl⟩ : syracuseStep 605677 = 227129) (by norm_num)
theorem B605789 : Blo 235815 605789 := bbase (se 3 (by rfl) ⟨113585, by rfl⟩ : syracuseStep 605789 = 227171) (by norm_num)
theorem B605981 : Blo 235815 605981 := bbase (se 3 (by rfl) ⟨113621, by rfl⟩ : syracuseStep 605981 = 227243) (by norm_num)
theorem B802709 : Blo 235815 802709 := bbase (se 6 (by rfl) ⟨18813, by rfl⟩ : syracuseStep 802709 = 37627) (by norm_num)
theorem B507829 : Blo 235815 507829 := bbase (se 5 (by rfl) ⟨23804, by rfl⟩ : syracuseStep 507829 = 47609) (by norm_num)
theorem B966613 : Blo 235815 966613 := bbase (se 7 (by rfl) ⟨11327, by rfl⟩ : syracuseStep 966613 = 22655) (by norm_num)
theorem B638981 : Blo 235815 638981 := bbase (se 4 (by rfl) ⟨59904, by rfl⟩ : syracuseStep 638981 = 119809) (by norm_num)
theorem B3686485 : Blo 235815 3686485 := bbase (se 8 (by rfl) ⟨21600, by rfl⟩ : syracuseStep 3686485 = 43201) (by norm_num)
theorem B606325 : Blo 235815 606325 := bbase (se 5 (by rfl) ⟨28421, by rfl⟩ : syracuseStep 606325 = 56843) (by norm_num)
theorem B606341 : Blo 235815 606341 := bbase (se 4 (by rfl) ⟨56844, by rfl⟩ : syracuseStep 606341 = 113689) (by norm_num)
theorem B606437 : Blo 235815 606437 := bbase (se 4 (by rfl) ⟨56853, by rfl⟩ : syracuseStep 606437 = 113707) (by norm_num)
theorem B1294613 : Blo 235815 1294613 := bbase (se 6 (by rfl) ⟨30342, by rfl⟩ : syracuseStep 1294613 = 60685) (by norm_num)
theorem B803141 : Blo 235815 803141 := bbase (se 4 (by rfl) ⟨75294, by rfl⟩ : syracuseStep 803141 = 150589) (by norm_num)
theorem B541093 : Blo 235815 541093 := bbase (se 4 (by rfl) ⟨50727, by rfl⟩ : syracuseStep 541093 = 101455) (by norm_num)
theorem B606629 : Blo 235815 606629 := bbase (se 4 (by rfl) ⟨56871, by rfl⟩ : syracuseStep 606629 = 113743) (by norm_num)
theorem B672229 : Blo 235815 672229 := bbase (se 4 (by rfl) ⟨63021, by rfl⟩ : syracuseStep 672229 = 126043) (by norm_num)
theorem B901637 : Blo 235815 901637 := bbase (se 4 (by rfl) ⟨84528, by rfl⟩ : syracuseStep 901637 = 169057) (by norm_num)
theorem B770629 : Blo 235815 770629 := bbase (se 4 (by rfl) ⟨72246, by rfl⟩ : syracuseStep 770629 = 144493) (by norm_num)
theorem B574037 : Blo 235815 574037 := bbase (se 8 (by rfl) ⟨3363, by rfl⟩ : syracuseStep 574037 = 6727) (by norm_num)
theorem B1196693 : Blo 235815 1196693 := bbase (se 6 (by rfl) ⟨28047, by rfl⟩ : syracuseStep 1196693 = 56095) (by norm_num)
theorem B574133 : Blo 235815 574133 := bbase (se 5 (by rfl) ⟨26912, by rfl⟩ : syracuseStep 574133 = 53825) (by norm_num)
theorem B803573 : Blo 235815 803573 := bbase (se 5 (by rfl) ⟨37667, by rfl⟩ : syracuseStep 803573 = 75335) (by norm_num)
theorem B606973 : Blo 235815 606973 := bbase (se 3 (by rfl) ⟨113807, by rfl⟩ : syracuseStep 606973 = 227615) (by norm_num)
theorem B901925 : Blo 235815 901925 := bbase (se 4 (by rfl) ⟨84555, by rfl⟩ : syracuseStep 901925 = 169111) (by norm_num)
theorem B508717 : Blo 235815 508717 := bbase (se 3 (by rfl) ⟨95384, by rfl⟩ : syracuseStep 508717 = 190769) (by norm_num)
theorem B770933 : Blo 235815 770933 := bbase (se 5 (by rfl) ⟨36137, by rfl⟩ : syracuseStep 770933 = 72275) (by norm_num)
theorem B934789 : Blo 235815 934789 := bbase (se 4 (by rfl) ⟨87636, by rfl⟩ : syracuseStep 934789 = 175273) (by norm_num)
theorem B508837 : Blo 235815 508837 := bbase (se 4 (by rfl) ⟨47703, by rfl⟩ : syracuseStep 508837 = 95407) (by norm_num)
theorem B607333 : Blo 235815 607333 := bbase (se 4 (by rfl) ⟨56937, by rfl⟩ : syracuseStep 607333 = 113875) (by norm_num)
theorem B804005 : Blo 235815 804005 := bbase (se 4 (by rfl) ⟨75375, by rfl⟩ : syracuseStep 804005 = 150751) (by norm_num)
theorem B509093 : Blo 235815 509093 := bbase (se 4 (by rfl) ⟨47727, by rfl⟩ : syracuseStep 509093 = 95455) (by norm_num)
theorem B967909 : Blo 235815 967909 := bbase (se 4 (by rfl) ⟨90741, by rfl⟩ : syracuseStep 967909 = 181483) (by norm_num)
theorem B378245 : Blo 235815 378245 := bbase (se 4 (by rfl) ⟨35460, by rfl⟩ : syracuseStep 378245 = 70921) (by norm_num)
theorem B771461 : Blo 235815 771461 := bbase (se 4 (by rfl) ⟨72324, by rfl⟩ : syracuseStep 771461 = 144649) (by norm_num)
theorem B2803157 : Blo 235815 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B804437 : Blo 235815 804437 := bbase (se 8 (by rfl) ⟨4713, by rfl⟩ : syracuseStep 804437 = 9427) (by norm_num)
theorem B1197989 : Blo 235815 1197989 := bbase (se 4 (by rfl) ⟨112311, by rfl⟩ : syracuseStep 1197989 = 224623) (by norm_num)
theorem B542645 : Blo 235815 542645 := bbase (se 5 (by rfl) ⟨25436, by rfl⟩ : syracuseStep 542645 = 50873) (by norm_num)
theorem B673733 : Blo 235815 673733 := bbase (se 4 (by rfl) ⟨63162, by rfl⟩ : syracuseStep 673733 = 126325) (by norm_num)
theorem B903109 : Blo 235815 903109 := bbase (se 4 (by rfl) ⟨84666, by rfl⟩ : syracuseStep 903109 = 169333) (by norm_num)
theorem B804869 : Blo 235815 804869 := bbase (se 4 (by rfl) ⟨75456, by rfl⟩ : syracuseStep 804869 = 150913) (by norm_num)
theorem B378893 : Blo 235815 378893 := bbase (se 3 (by rfl) ⟨71042, by rfl⟩ : syracuseStep 378893 = 142085) (by norm_num)
theorem B509981 : Blo 235815 509981 := bbase (se 3 (by rfl) ⟨95621, by rfl⟩ : syracuseStep 509981 = 191243) (by norm_num)
theorem B247861 : Blo 235815 247861 := bbase (se 5 (by rfl) ⟨11618, by rfl⟩ : syracuseStep 247861 = 23237) (by norm_num)
theorem B575549 : Blo 235815 575549 := bbase (se 3 (by rfl) ⟨107915, by rfl⟩ : syracuseStep 575549 = 215831) (by norm_num)
theorem B1099909 : Blo 235815 1099909 := bbase (se 4 (by rfl) ⟨103116, by rfl⟩ : syracuseStep 1099909 = 206233) (by norm_num)
theorem B1230997 : Blo 235815 1230997 := bbase (se 6 (by rfl) ⟨28851, by rfl⟩ : syracuseStep 1230997 = 57703) (by norm_num)
theorem B903413 : Blo 235815 903413 := bbase (se 5 (by rfl) ⟨42347, by rfl⟩ : syracuseStep 903413 = 84695) (by norm_num)
theorem B510221 : Blo 235815 510221 := bbase (se 3 (by rfl) ⟨95666, by rfl⟩ : syracuseStep 510221 = 191333) (by norm_num)
theorem B969077 : Blo 235815 969077 := bbase (se 5 (by rfl) ⟨45425, by rfl⟩ : syracuseStep 969077 = 90851) (by norm_num)
theorem B805301 : Blo 235815 805301 := bbase (se 5 (by rfl) ⟨37748, by rfl⟩ : syracuseStep 805301 = 75497) (by norm_num)
theorem B2017781 : Blo 235815 2017781 := bbase (se 5 (by rfl) ⟨94583, by rfl⟩ : syracuseStep 2017781 = 189167) (by norm_num)
theorem B510725 : Blo 235815 510725 := bbase (se 4 (by rfl) ⟨47880, by rfl⟩ : syracuseStep 510725 = 95761) (by norm_num)
theorem B510733 : Blo 235815 510733 := bbase (se 3 (by rfl) ⟨95762, by rfl⟩ : syracuseStep 510733 = 191525) (by norm_num)
theorem B805733 : Blo 235815 805733 := bbase (se 4 (by rfl) ⟨75537, by rfl⟩ : syracuseStep 805733 = 151075) (by norm_num)
theorem B379885 : Blo 235815 379885 := bbase (se 3 (by rfl) ⟨71228, by rfl⟩ : syracuseStep 379885 = 142457) (by norm_num)
theorem B1199285 : Blo 235815 1199285 := bbase (se 5 (by rfl) ⟨56216, by rfl⟩ : syracuseStep 1199285 = 112433) (by norm_num)
theorem B543941 : Blo 235815 543941 := bbase (se 4 (by rfl) ⟨50994, by rfl⟩ : syracuseStep 543941 = 101989) (by norm_num)
theorem B806165 : Blo 235815 806165 := bbase (se 6 (by rfl) ⟨18894, by rfl⟩ : syracuseStep 806165 = 37789) (by norm_num)
theorem B544085 : Blo 235815 544085 := bbase (se 11 (by rfl) ⟨398, by rfl⟩ : syracuseStep 544085 = 797) (by norm_num)
theorem B380333 : Blo 235815 380333 := bbase (se 3 (by rfl) ⟨71312, by rfl⟩ : syracuseStep 380333 = 142625) (by norm_num)
theorem B675317 : Blo 235815 675317 := bbase (se 5 (by rfl) ⟨31655, by rfl⟩ : syracuseStep 675317 = 63311) (by norm_num)
theorem B380413 : Blo 235815 380413 := bbase (se 3 (by rfl) ⟨71327, by rfl⟩ : syracuseStep 380413 = 142655) (by norm_num)
theorem B380533 : Blo 235815 380533 := bbase (se 5 (by rfl) ⟨17837, by rfl⟩ : syracuseStep 380533 = 35675) (by norm_num)
theorem B806597 : Blo 235815 806597 := bbase (se 4 (by rfl) ⟨75618, by rfl⟩ : syracuseStep 806597 = 151237) (by norm_num)
theorem B380789 : Blo 235815 380789 := bbase (se 5 (by rfl) ⟨17849, by rfl⟩ : syracuseStep 380789 = 35699) (by norm_num)
theorem B511861 : Blo 235815 511861 := bbase (se 5 (by rfl) ⟨23993, by rfl⟩ : syracuseStep 511861 = 47987) (by norm_num)
theorem B1527893 : Blo 235815 1527893 := bbase (se 8 (by rfl) ⟨8952, by rfl⟩ : syracuseStep 1527893 = 17905) (by norm_num)
theorem B807029 : Blo 235815 807029 := bbase (se 5 (by rfl) ⟨37829, by rfl⟩ : syracuseStep 807029 = 75659) (by norm_num)
theorem B675989 : Blo 235815 675989 := bbase (se 6 (by rfl) ⟨15843, by rfl⟩ : syracuseStep 675989 = 31687) (by norm_num)
theorem B774293 : Blo 235815 774293 := bbase (se 6 (by rfl) ⟨18147, by rfl⟩ : syracuseStep 774293 = 36295) (by norm_num)
theorem B1134773 : Blo 235815 1134773 := bbase (se 5 (by rfl) ⟨53192, by rfl⟩ : syracuseStep 1134773 = 106385) (by norm_num)
theorem B905525 : Blo 235815 905525 := bbase (se 5 (by rfl) ⟨42446, by rfl⟩ : syracuseStep 905525 = 84893) (by norm_num)
theorem B971189 : Blo 235815 971189 := bbase (se 5 (by rfl) ⟨45524, by rfl⟩ : syracuseStep 971189 = 91049) (by norm_num)
theorem B1200581 : Blo 235815 1200581 := bbase (se 4 (by rfl) ⟨112554, by rfl⟩ : syracuseStep 1200581 = 225109) (by norm_num)
theorem B807461 : Blo 235815 807461 := bbase (se 4 (by rfl) ⟨75699, by rfl⟩ : syracuseStep 807461 = 151399) (by norm_num)
theorem B676421 : Blo 235815 676421 := bbase (se 4 (by rfl) ⟨63414, by rfl⟩ : syracuseStep 676421 = 126829) (by norm_num)
theorem B905813 : Blo 235815 905813 := bbase (se 8 (by rfl) ⟨5307, by rfl⟩ : syracuseStep 905813 = 10615) (by norm_num)
theorem B479861 : Blo 235815 479861 := bbase (se 5 (by rfl) ⟨22493, by rfl⟩ : syracuseStep 479861 = 44987) (by norm_num)
theorem B1364597 : Blo 235815 1364597 := bbase (se 5 (by rfl) ⟨63965, by rfl⟩ : syracuseStep 1364597 = 127931) (by norm_num)
theorem B479933 : Blo 235815 479933 := bbase (se 3 (by rfl) ⟨89987, by rfl⟩ : syracuseStep 479933 = 179975) (by norm_num)
theorem B283405 : Blo 235815 283405 := bbase (se 3 (by rfl) ⟨53138, by rfl⟩ : syracuseStep 283405 = 106277) (by norm_num)
theorem B807893 : Blo 235815 807893 := bbase (se 7 (by rfl) ⟨9467, by rfl⟩ : syracuseStep 807893 = 18935) (by norm_num)
theorem B381917 : Blo 235815 381917 := bbase (se 3 (by rfl) ⟨71609, by rfl⟩ : syracuseStep 381917 = 143219) (by norm_num)
theorem B283789 : Blo 235815 283789 := bbase (se 3 (by rfl) ⟨53210, by rfl⟩ : syracuseStep 283789 = 106421) (by norm_num)
theorem B447781 : Blo 235815 447781 := bbase (se 4 (by rfl) ⟨41979, by rfl⟩ : syracuseStep 447781 = 83959) (by norm_num)
theorem B677173 : Blo 235815 677173 := bbase (se 5 (by rfl) ⟨31742, by rfl⟩ : syracuseStep 677173 = 63485) (by norm_num)
theorem B480581 : Blo 235815 480581 := bbase (se 4 (by rfl) ⟨45054, by rfl⟩ : syracuseStep 480581 = 90109) (by norm_num)
theorem B808325 : Blo 235815 808325 := bbase (se 4 (by rfl) ⟨75780, by rfl⟩ : syracuseStep 808325 = 151561) (by norm_num)
theorem B447925 : Blo 235815 447925 := bbase (se 5 (by rfl) ⟨20996, by rfl⟩ : syracuseStep 447925 = 41993) (by norm_num)
theorem B382429 : Blo 235815 382429 := bbase (se 3 (by rfl) ⟨71705, by rfl⟩ : syracuseStep 382429 = 143411) (by norm_num)
theorem B448085 : Blo 235815 448085 := bbase (se 8 (by rfl) ⟨2625, by rfl⟩ : syracuseStep 448085 = 5251) (by norm_num)
theorem B1201877 : Blo 235815 1201877 := bbase (se 7 (by rfl) ⟨14084, by rfl⟩ : syracuseStep 1201877 = 28169) (by norm_num)
theorem B1038037 : Blo 235815 1038037 := bbase (se 7 (by rfl) ⟨12164, by rfl⟩ : syracuseStep 1038037 = 24329) (by norm_num)
theorem B448229 : Blo 235815 448229 := bbase (se 4 (by rfl) ⟨42021, by rfl⟩ : syracuseStep 448229 = 84043) (by norm_num)
theorem B906997 : Blo 235815 906997 := bbase (se 5 (by rfl) ⟨42515, by rfl⟩ : syracuseStep 906997 = 85031) (by norm_num)
theorem B644885 : Blo 235815 644885 := bbase (se 6 (by rfl) ⟨15114, by rfl⟩ : syracuseStep 644885 = 30229) (by norm_num)
theorem B1365781 : Blo 235815 1365781 := bbase (se 6 (by rfl) ⟨32010, by rfl⟩ : syracuseStep 1365781 = 64021) (by norm_num)
theorem B808757 : Blo 235815 808757 := bbase (se 5 (by rfl) ⟨37910, by rfl⟩ : syracuseStep 808757 = 75821) (by norm_num)
theorem B284477 : Blo 235815 284477 := bbase (se 3 (by rfl) ⟨53339, by rfl⟩ : syracuseStep 284477 = 106679) (by norm_num)
theorem B645013 : Blo 235815 645013 := bbase (se 6 (by rfl) ⟨15117, by rfl⟩ : syracuseStep 645013 = 30235) (by norm_num)
theorem B382925 : Blo 235815 382925 := bbase (se 3 (by rfl) ⟨71798, by rfl⟩ : syracuseStep 382925 = 143597) (by norm_num)
theorem B382973 : Blo 235815 382973 := bbase (se 3 (by rfl) ⟨71807, by rfl⟩ : syracuseStep 382973 = 143615) (by norm_num)
theorem B448517 : Blo 235815 448517 := bbase (se 4 (by rfl) ⟨42048, by rfl⟩ : syracuseStep 448517 = 84097) (by norm_num)
theorem B907301 : Blo 235815 907301 := bbase (se 4 (by rfl) ⟨85059, by rfl⟩ : syracuseStep 907301 = 170119) (by norm_num)
theorem B252001 : Blo 235815 252001 := bbase (se 2 (by rfl) ⟨94500, by rfl⟩ : syracuseStep 252001 = 189001) (by norm_num)
theorem B448669 : Blo 235815 448669 := bbase (se 3 (by rfl) ⟨84125, by rfl⟩ : syracuseStep 448669 = 168251) (by norm_num)
theorem B809189 : Blo 235815 809189 := bbase (se 4 (by rfl) ⟨75861, by rfl⟩ : syracuseStep 809189 = 151723) (by norm_num)
theorem B6838613 : Blo 235815 6838613 := bbase (se 10 (by rfl) ⟨10017, by rfl⟩ : syracuseStep 6838613 = 20035) (by norm_num)
theorem B285077 : Blo 235815 285077 := bbase (se 6 (by rfl) ⟨6681, by rfl⟩ : syracuseStep 285077 = 13363) (by norm_num)
theorem B481717 : Blo 235815 481717 := bbase (se 5 (by rfl) ⟨22580, by rfl⟩ : syracuseStep 481717 = 45161) (by norm_num)
theorem B448973 : Blo 235815 448973 := bbase (se 3 (by rfl) ⟨84182, by rfl⟩ : syracuseStep 448973 = 168365) (by norm_num)
theorem B252445 : Blo 235815 252445 := bbase (se 3 (by rfl) ⟨47333, by rfl⟩ : syracuseStep 252445 = 94667) (by norm_num)
theorem B383525 : Blo 235815 383525 := bbase (se 4 (by rfl) ⟨35955, by rfl⟩ : syracuseStep 383525 = 71911) (by norm_num)
theorem B383557 : Blo 235815 383557 := bbase (se 4 (by rfl) ⟨35958, by rfl⟩ : syracuseStep 383557 = 71917) (by norm_num)
theorem B252505 : Blo 235815 252505 := bbase (se 2 (by rfl) ⟨94689, by rfl⟩ : syracuseStep 252505 = 189379) (by norm_num)
theorem B613021 : Blo 235815 613021 := bbase (se 3 (by rfl) ⟨114941, by rfl⟩ : syracuseStep 613021 = 229883) (by norm_num)
theorem B285385 : Blo 235815 285385 := bbase (se 2 (by rfl) ⟨107019, by rfl⟩ : syracuseStep 285385 = 214039) (by norm_num)
theorem B285481 : Blo 235815 285481 := bbase (se 2 (by rfl) ⟨107055, by rfl⟩ : syracuseStep 285481 = 214111) (by norm_num)
theorem B1792853 : Blo 235815 1792853 := bbase (se 9 (by rfl) ⟨5252, by rfl⟩ : syracuseStep 1792853 = 10505) (by norm_num)
theorem B285529 : Blo 235815 285529 := bbase (se 2 (by rfl) ⟨107073, by rfl⟩ : syracuseStep 285529 = 214147) (by norm_num)
theorem B252821 : Blo 235815 252821 := bbase (se 6 (by rfl) ⟨5925, by rfl⟩ : syracuseStep 252821 = 11851) (by norm_num)
theorem B2710421 : Blo 235815 2710421 := bbase (se 6 (by rfl) ⟨63525, by rfl⟩ : syracuseStep 2710421 = 127051) (by norm_num)
theorem B1203173 : Blo 235815 1203173 := bbase (se 4 (by rfl) ⟨112797, by rfl⟩ : syracuseStep 1203173 = 225595) (by norm_num)
theorem B482285 : Blo 235815 482285 := bbase (se 3 (by rfl) ⟨90428, by rfl⟩ : syracuseStep 482285 = 180857) (by norm_num)
theorem B580645 : Blo 235815 580645 := bbase (se 4 (by rfl) ⟨54435, by rfl⟩ : syracuseStep 580645 = 108871) (by norm_num)
theorem B449725 : Blo 235815 449725 := bbase (se 3 (by rfl) ⟨84323, by rfl⟩ : syracuseStep 449725 = 168647) (by norm_num)
theorem B875717 : Blo 235815 875717 := bbase (se 4 (by rfl) ⟨82098, by rfl⟩ : syracuseStep 875717 = 164197) (by norm_num)
theorem B449869 : Blo 235815 449869 := bbase (se 3 (by rfl) ⟨84350, by rfl⟩ : syracuseStep 449869 = 168701) (by norm_num)
theorem B253265 : Blo 235815 253265 := bbase (se 2 (by rfl) ⟨94974, by rfl⟩ : syracuseStep 253265 = 189949) (by norm_num)
theorem B253325 : Blo 235815 253325 := bbase (se 3 (by rfl) ⟨47498, by rfl⟩ : syracuseStep 253325 = 94997) (by norm_num)
theorem B450029 : Blo 235815 450029 := bbase (se 3 (by rfl) ⟨84380, by rfl⟩ : syracuseStep 450029 = 168761) (by norm_num)
theorem B253453 : Blo 235815 253453 := bbase (se 3 (by rfl) ⟨47522, by rfl⟩ : syracuseStep 253453 = 95045) (by norm_num)
theorem B319069 : Blo 235815 319069 := bbase (se 3 (by rfl) ⟨59825, by rfl⟩ : syracuseStep 319069 = 119651) (by norm_num)
theorem B450173 : Blo 235815 450173 := bbase (se 3 (by rfl) ⟨84407, by rfl⟩ : syracuseStep 450173 = 168815) (by norm_num)
theorem B319285 : Blo 235815 319285 := bbase (se 5 (by rfl) ⟨14966, by rfl⟩ : syracuseStep 319285 = 29933) (by norm_num)
theorem B450461 : Blo 235815 450461 := bbase (se 3 (by rfl) ⟨84461, by rfl⟩ : syracuseStep 450461 = 168923) (by norm_num)
theorem B253897 : Blo 235815 253897 := bbase (se 2 (by rfl) ⟨95211, by rfl⟩ : syracuseStep 253897 = 190423) (by norm_num)
theorem B1138693 : Blo 235815 1138693 := bbase (se 4 (by rfl) ⟨106752, by rfl⟩ : syracuseStep 1138693 = 213505) (by norm_num)
theorem B286745 : Blo 235815 286745 := bbase (se 2 (by rfl) ⟨107529, by rfl⟩ : syracuseStep 286745 = 215059) (by norm_num)
theorem B450613 : Blo 235815 450613 := bbase (se 5 (by rfl) ⟨21122, by rfl⟩ : syracuseStep 450613 = 42245) (by norm_num)
theorem B254017 : Blo 235815 254017 := bbase (se 2 (by rfl) ⟨95256, by rfl⟩ : syracuseStep 254017 = 190513) (by norm_num)
theorem B811093 : Blo 235815 811093 := bbase (se 8 (by rfl) ⟨4752, by rfl⟩ : syracuseStep 811093 = 9505) (by norm_num)
theorem B680021 : Blo 235815 680021 := bbase (se 8 (by rfl) ⟨3984, by rfl⟩ : syracuseStep 680021 = 7969) (by norm_num)
theorem B909413 : Blo 235815 909413 := bbase (se 4 (by rfl) ⟨85257, by rfl⟩ : syracuseStep 909413 = 170515) (by norm_num)
theorem B1007797 : Blo 235815 1007797 := bbase (se 5 (by rfl) ⟨47240, by rfl⟩ : syracuseStep 1007797 = 94481) (by norm_num)
theorem B286913 : Blo 235815 286913 := bbase (se 2 (by rfl) ⟨107592, by rfl⟩ : syracuseStep 286913 = 215185) (by norm_num)
theorem B1204469 : Blo 235815 1204469 := bbase (se 5 (by rfl) ⟨56459, by rfl⟩ : syracuseStep 1204469 = 112919) (by norm_num)
theorem B254269 : Blo 235815 254269 := bbase (se 3 (by rfl) ⟨47675, by rfl⟩ : syracuseStep 254269 = 95351) (by norm_num)
theorem B254273 : Blo 235815 254273 := bbase (se 2 (by rfl) ⟨95352, by rfl⟩ : syracuseStep 254273 = 190705) (by norm_num)
theorem B450917 : Blo 235815 450917 := bbase (se 4 (by rfl) ⟨42273, by rfl⟩ : syracuseStep 450917 = 84547) (by norm_num)
theorem B909701 : Blo 235815 909701 := bbase (se 4 (by rfl) ⟨85284, by rfl⟩ : syracuseStep 909701 = 170569) (by norm_num)
theorem B287221 : Blo 235815 287221 := bbase (se 5 (by rfl) ⟨13463, by rfl⟩ : syracuseStep 287221 = 26927) (by norm_num)
theorem B647765 : Blo 235815 647765 := bbase (se 8 (by rfl) ⟨3795, by rfl⟩ : syracuseStep 647765 = 7591) (by norm_num)
theorem B1532533 : Blo 235815 1532533 := bbase (se 5 (by rfl) ⟨71837, by rfl⟩ : syracuseStep 1532533 = 143675) (by norm_num)
theorem B287437 : Blo 235815 287437 := bbase (se 3 (by rfl) ⟨53894, by rfl⟩ : syracuseStep 287437 = 107789) (by norm_num)
theorem B254837 : Blo 235815 254837 := bbase (se 5 (by rfl) ⟨11945, by rfl⟩ : syracuseStep 254837 = 23891) (by norm_num)
theorem B3072917 : Blo 235815 3072917 := bbase (se 6 (by rfl) ⟨72021, by rfl⟩ : syracuseStep 3072917 = 144043) (by norm_num)
theorem B517045 : Blo 235815 517045 := bbase (se 5 (by rfl) ⟨24236, by rfl⟩ : syracuseStep 517045 = 48473) (by norm_num)
theorem B287749 : Blo 235815 287749 := bbase (se 4 (by rfl) ⟨26976, by rfl⟩ : syracuseStep 287749 = 53953) (by norm_num)
theorem B255025 : Blo 235815 255025 := bbase (se 2 (by rfl) ⟨95634, by rfl⟩ : syracuseStep 255025 = 191269) (by norm_num)
theorem B451669 : Blo 235815 451669 := bbase (se 8 (by rfl) ⟨2646, by rfl⟩ : syracuseStep 451669 = 5293) (by norm_num)
theorem B451813 : Blo 235815 451813 := bbase (se 4 (by rfl) ⟨42357, by rfl⟩ : syracuseStep 451813 = 84715) (by norm_num)
theorem B681205 : Blo 235815 681205 := bbase (se 5 (by rfl) ⟨31931, by rfl⟩ : syracuseStep 681205 = 63863) (by norm_num)
theorem B550253 : Blo 235815 550253 := bbase (se 3 (by rfl) ⟨103172, by rfl⟩ : syracuseStep 550253 = 206345) (by norm_num)
theorem B484733 : Blo 235815 484733 := bbase (se 3 (by rfl) ⟨90887, by rfl⟩ : syracuseStep 484733 = 181775) (by norm_num)
theorem B451973 : Blo 235815 451973 := bbase (se 4 (by rfl) ⟨42372, by rfl⟩ : syracuseStep 451973 = 84745) (by norm_num)
theorem B681365 : Blo 235815 681365 := bbase (se 6 (by rfl) ⟨15969, by rfl⟩ : syracuseStep 681365 = 31939) (by norm_num)
theorem B517565 : Blo 235815 517565 := bbase (se 3 (by rfl) ⟨97043, by rfl⟩ : syracuseStep 517565 = 194087) (by norm_num)
theorem B353741 : Blo 235815 353741 := bbase (se 3 (by rfl) ⟨66326, by rfl⟩ : syracuseStep 353741 = 132653) (by norm_num)
theorem B353765 : Blo 235815 353765 := bbase (se 4 (by rfl) ⟨33165, by rfl⟩ : syracuseStep 353765 = 66331) (by norm_num)
theorem B353789 : Blo 235815 353789 := bbase (se 3 (by rfl) ⟨66335, by rfl⟩ : syracuseStep 353789 = 132671) (by norm_num)
theorem B288257 : Blo 235815 288257 := bbase (se 2 (by rfl) ⟨108096, by rfl⟩ : syracuseStep 288257 = 216193) (by norm_num)
theorem B1205765 : Blo 235815 1205765 := bbase (se 4 (by rfl) ⟨113040, by rfl⟩ : syracuseStep 1205765 = 226081) (by norm_num)
theorem B353813 : Blo 235815 353813 := bbase (se 6 (by rfl) ⟨8292, by rfl⟩ : syracuseStep 353813 = 16585) (by norm_num)
theorem B452117 : Blo 235815 452117 := bbase (se 6 (by rfl) ⟨10596, by rfl⟩ : syracuseStep 452117 = 21193) (by norm_num)
theorem B353837 : Blo 235815 353837 := bbase (se 3 (by rfl) ⟨66344, by rfl⟩ : syracuseStep 353837 = 132689) (by norm_num)
theorem B353861 : Blo 235815 353861 := bbase (se 4 (by rfl) ⟨33174, by rfl⟩ : syracuseStep 353861 = 66349) (by norm_num)
theorem B3434069 : Blo 235815 3434069 := bbase (se 8 (by rfl) ⟨20121, by rfl⟩ : syracuseStep 3434069 = 40243) (by norm_num)
theorem B353885 : Blo 235815 353885 := bbase (se 3 (by rfl) ⟨66353, by rfl⟩ : syracuseStep 353885 = 132707) (by norm_num)
theorem B353909 : Blo 235815 353909 := bbase (se 5 (by rfl) ⟨16589, by rfl⟩ : syracuseStep 353909 = 33179) (by norm_num)
theorem B681605 : Blo 235815 681605 := bbase (se 4 (by rfl) ⟨63900, by rfl⟩ : syracuseStep 681605 = 127801) (by norm_num)
theorem B353933 : Blo 235815 353933 := bbase (se 3 (by rfl) ⟨66362, by rfl⟩ : syracuseStep 353933 = 132725) (by norm_num)
theorem B353957 : Blo 235815 353957 := bbase (se 4 (by rfl) ⟨33183, by rfl⟩ : syracuseStep 353957 = 66367) (by norm_num)
theorem B353981 : Blo 235815 353981 := bbase (se 3 (by rfl) ⟨66371, by rfl⟩ : syracuseStep 353981 = 132743) (by norm_num)
theorem B354005 : Blo 235815 354005 := bbase (se 7 (by rfl) ⟨4148, by rfl⟩ : syracuseStep 354005 = 8297) (by norm_num)
theorem B354029 : Blo 235815 354029 := bbase (se 3 (by rfl) ⟨66380, by rfl⟩ : syracuseStep 354029 = 132761) (by norm_num)
theorem B354053 : Blo 235815 354053 := bbase (se 4 (by rfl) ⟨33192, by rfl⟩ : syracuseStep 354053 = 66385) (by norm_num)
theorem B354077 : Blo 235815 354077 := bbase (se 3 (by rfl) ⟨66389, by rfl⟩ : syracuseStep 354077 = 132779) (by norm_num)
theorem B354101 : Blo 235815 354101 := bbase (se 5 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 354101 = 33197) (by norm_num)
theorem B452405 : Blo 235815 452405 := bbase (se 5 (by rfl) ⟨21206, by rfl⟩ : syracuseStep 452405 = 42413) (by norm_num)
theorem B681797 : Blo 235815 681797 := bbase (se 4 (by rfl) ⟨63918, by rfl⟩ : syracuseStep 681797 = 127837) (by norm_num)
theorem B354125 : Blo 235815 354125 := bbase (se 3 (by rfl) ⟨66398, by rfl⟩ : syracuseStep 354125 = 132797) (by norm_num)
theorem B354149 : Blo 235815 354149 := bbase (se 4 (by rfl) ⟨33201, by rfl⟩ : syracuseStep 354149 = 66403) (by norm_num)
theorem B255845 : Blo 235815 255845 := bbase (se 4 (by rfl) ⟨23985, by rfl⟩ : syracuseStep 255845 = 47971) (by norm_num)
theorem B354173 : Blo 235815 354173 := bbase (se 3 (by rfl) ⟨66407, by rfl⟩ : syracuseStep 354173 = 132815) (by norm_num)
theorem B354197 : Blo 235815 354197 := bbase (se 6 (by rfl) ⟨8301, by rfl⟩ : syracuseStep 354197 = 16603) (by norm_num)
theorem B354221 : Blo 235815 354221 := bbase (se 3 (by rfl) ⟨66416, by rfl⟩ : syracuseStep 354221 = 132833) (by norm_num)
theorem B354245 : Blo 235815 354245 := bbase (se 4 (by rfl) ⟨33210, by rfl⟩ : syracuseStep 354245 = 66421) (by norm_num)
theorem B452557 : Blo 235815 452557 := bbase (se 3 (by rfl) ⟨84854, by rfl⟩ : syracuseStep 452557 = 169709) (by norm_num)
theorem B354269 : Blo 235815 354269 := bbase (se 3 (by rfl) ⟨66425, by rfl⟩ : syracuseStep 354269 = 132851) (by norm_num)
theorem B354293 : Blo 235815 354293 := bbase (se 5 (by rfl) ⟨16607, by rfl⟩ : syracuseStep 354293 = 33215) (by norm_num)
theorem B354317 : Blo 235815 354317 := bbase (se 3 (by rfl) ⟨66434, by rfl⟩ : syracuseStep 354317 = 132869) (by norm_num)
theorem B354341 : Blo 235815 354341 := bbase (se 4 (by rfl) ⟨33219, by rfl⟩ : syracuseStep 354341 = 66439) (by norm_num)
theorem B354365 : Blo 235815 354365 := bbase (se 3 (by rfl) ⟨66443, by rfl⟩ : syracuseStep 354365 = 132887) (by norm_num)
theorem B354389 : Blo 235815 354389 := bbase (se 8 (by rfl) ⟨2076, by rfl⟩ : syracuseStep 354389 = 4153) (by norm_num)
theorem B354413 : Blo 235815 354413 := bbase (se 3 (by rfl) ⟨66452, by rfl⟩ : syracuseStep 354413 = 132905) (by norm_num)
theorem B354437 : Blo 235815 354437 := bbase (se 4 (by rfl) ⟨33228, by rfl⟩ : syracuseStep 354437 = 66457) (by norm_num)
theorem B354461 : Blo 235815 354461 := bbase (se 3 (by rfl) ⟨66461, by rfl⟩ : syracuseStep 354461 = 132923) (by norm_num)
theorem B354485 : Blo 235815 354485 := bbase (se 5 (by rfl) ⟨16616, by rfl⟩ : syracuseStep 354485 = 33233) (by norm_num)
theorem B354509 : Blo 235815 354509 := bbase (se 3 (by rfl) ⟨66470, by rfl⟩ : syracuseStep 354509 = 132941) (by norm_num)
theorem B354533 : Blo 235815 354533 := bbase (se 4 (by rfl) ⟨33237, by rfl⟩ : syracuseStep 354533 = 66475) (by norm_num)
theorem B354557 : Blo 235815 354557 := bbase (se 3 (by rfl) ⟨66479, by rfl⟩ : syracuseStep 354557 = 132959) (by norm_num)
theorem B289021 : Blo 235815 289021 := bbase (se 3 (by rfl) ⟨54191, by rfl⟩ : syracuseStep 289021 = 108383) (by norm_num)
theorem B452861 : Blo 235815 452861 := bbase (se 3 (by rfl) ⟨84911, by rfl⟩ : syracuseStep 452861 = 169823) (by norm_num)
theorem B354581 : Blo 235815 354581 := bbase (se 6 (by rfl) ⟨8310, by rfl⟩ : syracuseStep 354581 = 16621) (by norm_num)
theorem B354605 : Blo 235815 354605 := bbase (se 3 (by rfl) ⟨66488, by rfl⟩ : syracuseStep 354605 = 132977) (by norm_num)
theorem B354629 : Blo 235815 354629 := bbase (se 4 (by rfl) ⟨33246, by rfl⟩ : syracuseStep 354629 = 66493) (by norm_num)
theorem B354653 : Blo 235815 354653 := bbase (se 3 (by rfl) ⟨66497, by rfl⟩ : syracuseStep 354653 = 132995) (by norm_num)
theorem B354677 : Blo 235815 354677 := bbase (se 5 (by rfl) ⟨16625, by rfl⟩ : syracuseStep 354677 = 33251) (by norm_num)
theorem B485765 : Blo 235815 485765 := bbase (se 4 (by rfl) ⟨45540, by rfl⟩ : syracuseStep 485765 = 91081) (by norm_num)
theorem B354701 : Blo 235815 354701 := bbase (se 3 (by rfl) ⟨66506, by rfl⟩ : syracuseStep 354701 = 133013) (by norm_num)
theorem B354725 : Blo 235815 354725 := bbase (se 4 (by rfl) ⟨33255, by rfl⟩ : syracuseStep 354725 = 66511) (by norm_num)
theorem B354749 : Blo 235815 354749 := bbase (se 3 (by rfl) ⟨66515, by rfl⟩ : syracuseStep 354749 = 133031) (by norm_num)
theorem B354773 : Blo 235815 354773 := bbase (se 7 (by rfl) ⟨4157, by rfl⟩ : syracuseStep 354773 = 8315) (by norm_num)
theorem B354797 : Blo 235815 354797 := bbase (se 3 (by rfl) ⟨66524, by rfl⟩ : syracuseStep 354797 = 133049) (by norm_num)
theorem B256493 : Blo 235815 256493 := bbase (se 3 (by rfl) ⟨48092, by rfl⟩ : syracuseStep 256493 = 96185) (by norm_num)
theorem B354821 : Blo 235815 354821 := bbase (se 4 (by rfl) ⟨33264, by rfl⟩ : syracuseStep 354821 = 66529) (by norm_num)
theorem B354845 : Blo 235815 354845 := bbase (se 3 (by rfl) ⟨66533, by rfl⟩ : syracuseStep 354845 = 133067) (by norm_num)
theorem B354869 : Blo 235815 354869 := bbase (se 5 (by rfl) ⟨16634, by rfl⟩ : syracuseStep 354869 = 33269) (by norm_num)
theorem B322117 : Blo 235815 322117 := bbase (se 4 (by rfl) ⟨30198, by rfl⟩ : syracuseStep 322117 = 60397) (by norm_num)
theorem B354893 : Blo 235815 354893 := bbase (se 3 (by rfl) ⟨66542, by rfl⟩ : syracuseStep 354893 = 133085) (by norm_num)
theorem B354917 : Blo 235815 354917 := bbase (se 4 (by rfl) ⟨33273, by rfl⟩ : syracuseStep 354917 = 66547) (by norm_num)
theorem B354941 : Blo 235815 354941 := bbase (se 3 (by rfl) ⟨66551, by rfl⟩ : syracuseStep 354941 = 133103) (by norm_num)
theorem B354965 : Blo 235815 354965 := bbase (se 6 (by rfl) ⟨8319, by rfl⟩ : syracuseStep 354965 = 16639) (by norm_num)
theorem B354989 : Blo 235815 354989 := bbase (se 3 (by rfl) ⟨66560, by rfl⟩ : syracuseStep 354989 = 133121) (by norm_num)
theorem B355013 : Blo 235815 355013 := bbase (se 4 (by rfl) ⟨33282, by rfl⟩ : syracuseStep 355013 = 66565) (by norm_num)
theorem B355037 : Blo 235815 355037 := bbase (se 3 (by rfl) ⟨66569, by rfl⟩ : syracuseStep 355037 = 133139) (by norm_num)
theorem B355061 : Blo 235815 355061 := bbase (se 5 (by rfl) ⟨16643, by rfl⟩ : syracuseStep 355061 = 33287) (by norm_num)
theorem B355085 : Blo 235815 355085 := bbase (se 3 (by rfl) ⟨66578, by rfl⟩ : syracuseStep 355085 = 133157) (by norm_num)
theorem B1207061 : Blo 235815 1207061 := bbase (se 6 (by rfl) ⟨28290, by rfl⟩ : syracuseStep 1207061 = 56581) (by norm_num)
theorem B355109 : Blo 235815 355109 := bbase (se 4 (by rfl) ⟨33291, by rfl⟩ : syracuseStep 355109 = 66583) (by norm_num)
theorem B682789 : Blo 235815 682789 := bbase (se 4 (by rfl) ⟨64011, by rfl⟩ : syracuseStep 682789 = 128023) (by norm_num)
theorem B355133 : Blo 235815 355133 := bbase (se 3 (by rfl) ⟨66587, by rfl⟩ : syracuseStep 355133 = 133175) (by norm_num)
theorem B355157 : Blo 235815 355157 := bbase (se 9 (by rfl) ⟨1040, by rfl⟩ : syracuseStep 355157 = 2081) (by norm_num)
theorem B355181 : Blo 235815 355181 := bbase (se 3 (by rfl) ⟨66596, by rfl⟩ : syracuseStep 355181 = 133193) (by norm_num)
theorem B355205 : Blo 235815 355205 := bbase (se 4 (by rfl) ⟨33300, by rfl⟩ : syracuseStep 355205 = 66601) (by norm_num)
theorem B355229 : Blo 235815 355229 := bbase (se 3 (by rfl) ⟨66605, by rfl⟩ : syracuseStep 355229 = 133211) (by norm_num)
theorem B519077 : Blo 235815 519077 := bbase (se 4 (by rfl) ⟨48663, by rfl⟩ : syracuseStep 519077 = 97327) (by norm_num)
theorem B355253 : Blo 235815 355253 := bbase (se 5 (by rfl) ⟨16652, by rfl⟩ : syracuseStep 355253 = 33305) (by norm_num)
theorem B355277 : Blo 235815 355277 := bbase (se 3 (by rfl) ⟨66614, by rfl⟩ : syracuseStep 355277 = 133229) (by norm_num)
theorem B355301 : Blo 235815 355301 := bbase (se 4 (by rfl) ⟨33309, by rfl⟩ : syracuseStep 355301 = 66619) (by norm_num)
theorem B453613 : Blo 235815 453613 := bbase (se 3 (by rfl) ⟨85052, by rfl⟩ : syracuseStep 453613 = 170105) (by norm_num)
theorem B355325 : Blo 235815 355325 := bbase (se 3 (by rfl) ⟨66623, by rfl⟩ : syracuseStep 355325 = 133247) (by norm_num)
theorem B355349 : Blo 235815 355349 := bbase (se 6 (by rfl) ⟨8328, by rfl⟩ : syracuseStep 355349 = 16657) (by norm_num)
theorem B355373 : Blo 235815 355373 := bbase (se 3 (by rfl) ⟨66632, by rfl⟩ : syracuseStep 355373 = 133265) (by norm_num)
theorem B355397 : Blo 235815 355397 := bbase (se 4 (by rfl) ⟨33318, by rfl⟩ : syracuseStep 355397 = 66637) (by norm_num)
theorem B355421 : Blo 235815 355421 := bbase (se 3 (by rfl) ⟨66641, by rfl⟩ : syracuseStep 355421 = 133283) (by norm_num)
theorem B1010789 : Blo 235815 1010789 := bbase (se 4 (by rfl) ⟨94761, by rfl⟩ : syracuseStep 1010789 = 189523) (by norm_num)
theorem B355445 : Blo 235815 355445 := bbase (se 5 (by rfl) ⟨16661, by rfl⟩ : syracuseStep 355445 = 33323) (by norm_num)
theorem B453757 : Blo 235815 453757 := bbase (se 3 (by rfl) ⟨85079, by rfl⟩ : syracuseStep 453757 = 170159) (by norm_num)
theorem B355469 : Blo 235815 355469 := bbase (se 3 (by rfl) ⟨66650, by rfl⟩ : syracuseStep 355469 = 133301) (by norm_num)
theorem B257185 : Blo 235815 257185 := bbase (se 2 (by rfl) ⟨96444, by rfl⟩ : syracuseStep 257185 = 192889) (by norm_num)
theorem B355493 : Blo 235815 355493 := bbase (se 4 (by rfl) ⟨33327, by rfl⟩ : syracuseStep 355493 = 66655) (by norm_num)
theorem B257189 : Blo 235815 257189 := bbase (se 4 (by rfl) ⟨24111, by rfl⟩ : syracuseStep 257189 = 48223) (by norm_num)
theorem B355517 : Blo 235815 355517 := bbase (se 3 (by rfl) ⟨66659, by rfl⟩ : syracuseStep 355517 = 133319) (by norm_num)
theorem B355541 : Blo 235815 355541 := bbase (se 7 (by rfl) ⟨4166, by rfl⟩ : syracuseStep 355541 = 8333) (by norm_num)
theorem B453853 : Blo 235815 453853 := bbase (se 3 (by rfl) ⟨85097, by rfl⟩ : syracuseStep 453853 = 170195) (by norm_num)
theorem B355565 : Blo 235815 355565 := bbase (se 3 (by rfl) ⟨66668, by rfl⟩ : syracuseStep 355565 = 133337) (by norm_num)
theorem B322805 : Blo 235815 322805 := bbase (se 5 (by rfl) ⟨15131, by rfl⟩ : syracuseStep 322805 = 30263) (by norm_num)
theorem B355589 : Blo 235815 355589 := bbase (se 4 (by rfl) ⟨33336, by rfl⟩ : syracuseStep 355589 = 66673) (by norm_num)
theorem B3665173 : Blo 235815 3665173 := bbase (se 6 (by rfl) ⟨85902, by rfl⟩ : syracuseStep 3665173 = 171805) (by norm_num)
theorem B355613 : Blo 235815 355613 := bbase (se 3 (by rfl) ⟨66677, by rfl⟩ : syracuseStep 355613 = 133355) (by norm_num)
theorem B453917 : Blo 235815 453917 := bbase (se 3 (by rfl) ⟨85109, by rfl⟩ : syracuseStep 453917 = 170219) (by norm_num)
theorem B355637 : Blo 235815 355637 := bbase (se 5 (by rfl) ⟨16670, by rfl⟩ : syracuseStep 355637 = 33341) (by norm_num)
theorem B355661 : Blo 235815 355661 := bbase (se 3 (by rfl) ⟨66686, by rfl⟩ : syracuseStep 355661 = 133373) (by norm_num)
theorem B355685 : Blo 235815 355685 := bbase (se 4 (by rfl) ⟨33345, by rfl⟩ : syracuseStep 355685 = 66691) (by norm_num)
theorem B355709 : Blo 235815 355709 := bbase (se 3 (by rfl) ⟨66695, by rfl⟩ : syracuseStep 355709 = 133391) (by norm_num)
theorem B355733 : Blo 235815 355733 := bbase (se 6 (by rfl) ⟨8337, by rfl⟩ : syracuseStep 355733 = 16675) (by norm_num)
theorem B355757 : Blo 235815 355757 := bbase (se 3 (by rfl) ⟨66704, by rfl⟩ : syracuseStep 355757 = 133409) (by norm_num)
theorem B454061 : Blo 235815 454061 := bbase (se 3 (by rfl) ⟨85136, by rfl⟩ : syracuseStep 454061 = 170273) (by norm_num)
theorem B355781 : Blo 235815 355781 := bbase (se 4 (by rfl) ⟨33354, by rfl⟩ : syracuseStep 355781 = 66709) (by norm_num)
theorem B355805 : Blo 235815 355805 := bbase (se 3 (by rfl) ⟨66713, by rfl⟩ : syracuseStep 355805 = 133427) (by norm_num)
theorem B355829 : Blo 235815 355829 := bbase (se 5 (by rfl) ⟨16679, by rfl⟩ : syracuseStep 355829 = 33359) (by norm_num)
theorem B355853 : Blo 235815 355853 := bbase (se 3 (by rfl) ⟨66722, by rfl⟩ : syracuseStep 355853 = 133445) (by norm_num)
theorem B355877 : Blo 235815 355877 := bbase (se 4 (by rfl) ⟨33363, by rfl⟩ : syracuseStep 355877 = 66727) (by norm_num)
theorem B355901 : Blo 235815 355901 := bbase (se 3 (by rfl) ⟨66731, by rfl⟩ : syracuseStep 355901 = 133463) (by norm_num)
theorem B355925 : Blo 235815 355925 := bbase (se 8 (by rfl) ⟨2085, by rfl⟩ : syracuseStep 355925 = 4171) (by norm_num)
theorem B355949 : Blo 235815 355949 := bbase (se 3 (by rfl) ⟨66740, by rfl⟩ : syracuseStep 355949 = 133481) (by norm_num)
theorem B355973 : Blo 235815 355973 := bbase (se 4 (by rfl) ⟨33372, by rfl⟩ : syracuseStep 355973 = 66745) (by norm_num)
theorem B355997 : Blo 235815 355997 := bbase (se 3 (by rfl) ⟨66749, by rfl⟩ : syracuseStep 355997 = 133499) (by norm_num)
theorem B356021 : Blo 235815 356021 := bbase (se 5 (by rfl) ⟨16688, by rfl⟩ : syracuseStep 356021 = 33377) (by norm_num)
theorem B356045 : Blo 235815 356045 := bbase (se 3 (by rfl) ⟨66758, by rfl⟩ : syracuseStep 356045 = 133517) (by norm_num)
theorem B454349 : Blo 235815 454349 := bbase (se 3 (by rfl) ⟨85190, by rfl⟩ : syracuseStep 454349 = 170381) (by norm_num)
theorem B356069 : Blo 235815 356069 := bbase (se 4 (by rfl) ⟨33381, by rfl⟩ : syracuseStep 356069 = 66763) (by norm_num)
theorem B356093 : Blo 235815 356093 := bbase (se 3 (by rfl) ⟨66767, by rfl⟩ : syracuseStep 356093 = 133535) (by norm_num)
theorem B913157 : Blo 235815 913157 := bbase (se 4 (by rfl) ⟨85608, by rfl⟩ : syracuseStep 913157 = 171217) (by norm_num)
theorem B356117 : Blo 235815 356117 := bbase (se 6 (by rfl) ⟨8346, by rfl⟩ : syracuseStep 356117 = 16693) (by norm_num)
theorem B323357 : Blo 235815 323357 := bbase (se 3 (by rfl) ⟨60629, by rfl⟩ : syracuseStep 323357 = 121259) (by norm_num)
theorem B356141 : Blo 235815 356141 := bbase (se 3 (by rfl) ⟨66776, by rfl⟩ : syracuseStep 356141 = 133553) (by norm_num)
theorem B356165 : Blo 235815 356165 := bbase (se 4 (by rfl) ⟨33390, by rfl⟩ : syracuseStep 356165 = 66781) (by norm_num)
theorem B356189 : Blo 235815 356189 := bbase (se 3 (by rfl) ⟨66785, by rfl⟩ : syracuseStep 356189 = 133571) (by norm_num)
theorem B454501 : Blo 235815 454501 := bbase (se 4 (by rfl) ⟨42609, by rfl⟩ : syracuseStep 454501 = 85219) (by norm_num)
theorem B323437 : Blo 235815 323437 := bbase (se 3 (by rfl) ⟨60644, by rfl⟩ : syracuseStep 323437 = 121289) (by norm_num)
theorem B356213 : Blo 235815 356213 := bbase (se 5 (by rfl) ⟨16697, by rfl⟩ : syracuseStep 356213 = 33395) (by norm_num)
theorem B356237 : Blo 235815 356237 := bbase (se 3 (by rfl) ⟨66794, by rfl⟩ : syracuseStep 356237 = 133589) (by norm_num)
theorem B356261 : Blo 235815 356261 := bbase (se 4 (by rfl) ⟨33399, by rfl⟩ : syracuseStep 356261 = 66799) (by norm_num)
theorem B1142693 : Blo 235815 1142693 := bbase (se 4 (by rfl) ⟨107127, by rfl⟩ : syracuseStep 1142693 = 214255) (by norm_num)
theorem B323501 : Blo 235815 323501 := bbase (se 3 (by rfl) ⟨60656, by rfl⟩ : syracuseStep 323501 = 121313) (by norm_num)
theorem B356285 : Blo 235815 356285 := bbase (se 3 (by rfl) ⟨66803, by rfl⟩ : syracuseStep 356285 = 133607) (by norm_num)
theorem B356309 : Blo 235815 356309 := bbase (se 7 (by rfl) ⟨4175, by rfl⟩ : syracuseStep 356309 = 8351) (by norm_num)
theorem B356333 : Blo 235815 356333 := bbase (se 3 (by rfl) ⟨66812, by rfl⟩ : syracuseStep 356333 = 133625) (by norm_num)
theorem B2289653 : Blo 235815 2289653 := bbase (se 5 (by rfl) ⟨107327, by rfl⟩ : syracuseStep 2289653 = 214655) (by norm_num)
theorem B356357 : Blo 235815 356357 := bbase (se 4 (by rfl) ⟨33408, by rfl⟩ : syracuseStep 356357 = 66817) (by norm_num)
theorem B356381 : Blo 235815 356381 := bbase (se 3 (by rfl) ⟨66821, by rfl⟩ : syracuseStep 356381 = 133643) (by norm_num)
theorem B1208357 : Blo 235815 1208357 := bbase (se 4 (by rfl) ⟨113283, by rfl⟩ : syracuseStep 1208357 = 226567) (by norm_num)
theorem B356405 : Blo 235815 356405 := bbase (se 5 (by rfl) ⟨16706, by rfl⟩ : syracuseStep 356405 = 33413) (by norm_num)
theorem B356429 : Blo 235815 356429 := bbase (se 3 (by rfl) ⟨66830, by rfl⟩ : syracuseStep 356429 = 133661) (by norm_num)
theorem B1011797 : Blo 235815 1011797 := bbase (se 8 (by rfl) ⟨5928, by rfl⟩ : syracuseStep 1011797 = 11857) (by norm_num)
theorem B356453 : Blo 235815 356453 := bbase (se 4 (by rfl) ⟨33417, by rfl⟩ : syracuseStep 356453 = 66835) (by norm_num)
theorem B356477 : Blo 235815 356477 := bbase (se 3 (by rfl) ⟨66839, by rfl⟩ : syracuseStep 356477 = 133679) (by norm_num)
theorem B356501 : Blo 235815 356501 := bbase (se 6 (by rfl) ⟨8355, by rfl⟩ : syracuseStep 356501 = 16711) (by norm_num)
theorem B454805 : Blo 235815 454805 := bbase (se 6 (by rfl) ⟨10659, by rfl⟩ : syracuseStep 454805 = 21319) (by norm_num)
theorem B356525 : Blo 235815 356525 := bbase (se 3 (by rfl) ⟨66848, by rfl⟩ : syracuseStep 356525 = 133697) (by norm_num)
theorem B913589 : Blo 235815 913589 := bbase (se 5 (by rfl) ⟨42824, by rfl⟩ : syracuseStep 913589 = 85649) (by norm_num)
theorem B356549 : Blo 235815 356549 := bbase (se 4 (by rfl) ⟨33426, by rfl⟩ : syracuseStep 356549 = 66853) (by norm_num)
theorem B1142981 : Blo 235815 1142981 := bbase (se 4 (by rfl) ⟨107154, by rfl⟩ : syracuseStep 1142981 = 214309) (by norm_num)
theorem B356573 : Blo 235815 356573 := bbase (se 3 (by rfl) ⟨66857, by rfl⟩ : syracuseStep 356573 = 133715) (by norm_num)
theorem B356597 : Blo 235815 356597 := bbase (se 5 (by rfl) ⟨16715, by rfl⟩ : syracuseStep 356597 = 33431) (by norm_num)
theorem B356621 : Blo 235815 356621 := bbase (se 3 (by rfl) ⟨66866, by rfl⟩ : syracuseStep 356621 = 133733) (by norm_num)
theorem B356645 : Blo 235815 356645 := bbase (se 4 (by rfl) ⟨33435, by rfl⟩ : syracuseStep 356645 = 66871) (by norm_num)
theorem B356669 : Blo 235815 356669 := bbase (se 3 (by rfl) ⟨66875, by rfl⟩ : syracuseStep 356669 = 133751) (by norm_num)
theorem B356693 : Blo 235815 356693 := bbase (se 10 (by rfl) ⟨522, by rfl⟩ : syracuseStep 356693 = 1045) (by norm_num)
theorem B356717 : Blo 235815 356717 := bbase (se 3 (by rfl) ⟨66884, by rfl⟩ : syracuseStep 356717 = 133769) (by norm_num)
theorem B356741 : Blo 235815 356741 := bbase (se 4 (by rfl) ⟨33444, by rfl⟩ : syracuseStep 356741 = 66889) (by norm_num)
theorem B356765 : Blo 235815 356765 := bbase (se 3 (by rfl) ⟨66893, by rfl⟩ : syracuseStep 356765 = 133787) (by norm_num)
theorem B356789 : Blo 235815 356789 := bbase (se 5 (by rfl) ⟨16724, by rfl⟩ : syracuseStep 356789 = 33449) (by norm_num)
theorem B356813 : Blo 235815 356813 := bbase (se 3 (by rfl) ⟨66902, by rfl⟩ : syracuseStep 356813 = 133805) (by norm_num)
theorem B356837 : Blo 235815 356837 := bbase (se 4 (by rfl) ⟨33453, by rfl⟩ : syracuseStep 356837 = 66907) (by norm_num)
theorem B356861 : Blo 235815 356861 := bbase (se 3 (by rfl) ⟨66911, by rfl⟩ : syracuseStep 356861 = 133823) (by norm_num)
theorem B356885 : Blo 235815 356885 := bbase (se 6 (by rfl) ⟨8364, by rfl⟩ : syracuseStep 356885 = 16729) (by norm_num)
theorem B356909 : Blo 235815 356909 := bbase (se 3 (by rfl) ⟨66920, by rfl⟩ : syracuseStep 356909 = 133841) (by norm_num)
theorem B356933 : Blo 235815 356933 := bbase (se 4 (by rfl) ⟨33462, by rfl⟩ : syracuseStep 356933 = 66925) (by norm_num)
theorem B356957 : Blo 235815 356957 := bbase (se 3 (by rfl) ⟨66929, by rfl⟩ : syracuseStep 356957 = 133859) (by norm_num)
theorem B356981 : Blo 235815 356981 := bbase (se 5 (by rfl) ⟨16733, by rfl⟩ : syracuseStep 356981 = 33467) (by norm_num)
theorem B357005 : Blo 235815 357005 := bbase (se 3 (by rfl) ⟨66938, by rfl⟩ : syracuseStep 357005 = 133877) (by norm_num)
theorem B357029 : Blo 235815 357029 := bbase (se 4 (by rfl) ⟨33471, by rfl⟩ : syracuseStep 357029 = 66943) (by norm_num)
theorem B357053 : Blo 235815 357053 := bbase (se 3 (by rfl) ⟨66947, by rfl⟩ : syracuseStep 357053 = 133895) (by norm_num)
theorem B357077 : Blo 235815 357077 := bbase (se 7 (by rfl) ⟨4184, by rfl⟩ : syracuseStep 357077 = 8369) (by norm_num)
theorem B357101 : Blo 235815 357101 := bbase (se 3 (by rfl) ⟨66956, by rfl⟩ : syracuseStep 357101 = 133913) (by norm_num)
theorem B357125 : Blo 235815 357125 := bbase (se 4 (by rfl) ⟨33480, by rfl⟩ : syracuseStep 357125 = 66961) (by norm_num)
theorem B1372949 : Blo 235815 1372949 := bbase (se 6 (by rfl) ⟨32178, by rfl⟩ : syracuseStep 1372949 = 64357) (by norm_num)
theorem B357149 : Blo 235815 357149 := bbase (se 3 (by rfl) ⟨66965, by rfl⟩ : syracuseStep 357149 = 133931) (by norm_num)
theorem B357173 : Blo 235815 357173 := bbase (se 5 (by rfl) ⟨16742, by rfl⟩ : syracuseStep 357173 = 33485) (by norm_num)
theorem B357197 : Blo 235815 357197 := bbase (se 3 (by rfl) ⟨66974, by rfl⟩ : syracuseStep 357197 = 133949) (by norm_num)
theorem B357221 : Blo 235815 357221 := bbase (se 4 (by rfl) ⟨33489, by rfl⟩ : syracuseStep 357221 = 66979) (by norm_num)
theorem B357245 : Blo 235815 357245 := bbase (se 3 (by rfl) ⟨66983, by rfl⟩ : syracuseStep 357245 = 133967) (by norm_num)
theorem B357269 : Blo 235815 357269 := bbase (se 6 (by rfl) ⟨8373, by rfl⟩ : syracuseStep 357269 = 16747) (by norm_num)
theorem B357293 : Blo 235815 357293 := bbase (se 3 (by rfl) ⟨66992, by rfl⟩ : syracuseStep 357293 = 133985) (by norm_num)
theorem B357317 : Blo 235815 357317 := bbase (se 4 (by rfl) ⟨33498, by rfl⟩ : syracuseStep 357317 = 66997) (by norm_num)
theorem B357341 : Blo 235815 357341 := bbase (se 3 (by rfl) ⟨67001, by rfl⟩ : syracuseStep 357341 = 134003) (by norm_num)
theorem B357365 : Blo 235815 357365 := bbase (se 5 (by rfl) ⟨16751, by rfl⟩ : syracuseStep 357365 = 33503) (by norm_num)
theorem B357389 : Blo 235815 357389 := bbase (se 3 (by rfl) ⟨67010, by rfl⟩ : syracuseStep 357389 = 134021) (by norm_num)
theorem B357413 : Blo 235815 357413 := bbase (se 4 (by rfl) ⟨33507, by rfl⟩ : syracuseStep 357413 = 67015) (by norm_num)
theorem B291881 : Blo 235815 291881 := bbase (se 2 (by rfl) ⟨109455, by rfl⟩ : syracuseStep 291881 = 218911) (by norm_num)
theorem B357437 : Blo 235815 357437 := bbase (se 3 (by rfl) ⟨67019, by rfl⟩ : syracuseStep 357437 = 134039) (by norm_num)
theorem B357461 : Blo 235815 357461 := bbase (se 8 (by rfl) ⟨2094, by rfl⟩ : syracuseStep 357461 = 4189) (by norm_num)
theorem B357485 : Blo 235815 357485 := bbase (se 3 (by rfl) ⟨67028, by rfl⟩ : syracuseStep 357485 = 134057) (by norm_num)
theorem B357509 : Blo 235815 357509 := bbase (se 4 (by rfl) ⟨33516, by rfl⟩ : syracuseStep 357509 = 67033) (by norm_num)
theorem B357533 : Blo 235815 357533 := bbase (se 3 (by rfl) ⟨67037, by rfl⟩ : syracuseStep 357533 = 134075) (by norm_num)
theorem B357557 : Blo 235815 357557 := bbase (se 5 (by rfl) ⟨16760, by rfl⟩ : syracuseStep 357557 = 33521) (by norm_num)
theorem B357581 : Blo 235815 357581 := bbase (se 3 (by rfl) ⟨67046, by rfl⟩ : syracuseStep 357581 = 134093) (by norm_num)
theorem B357605 : Blo 235815 357605 := bbase (se 4 (by rfl) ⟨33525, by rfl⟩ : syracuseStep 357605 = 67051) (by norm_num)
theorem B357629 : Blo 235815 357629 := bbase (se 3 (by rfl) ⟨67055, by rfl⟩ : syracuseStep 357629 = 134111) (by norm_num)
theorem B357653 : Blo 235815 357653 := bbase (se 6 (by rfl) ⟨8382, by rfl⟩ : syracuseStep 357653 = 16765) (by norm_num)
theorem B619805 : Blo 235815 619805 := bbase (se 3 (by rfl) ⟨116213, by rfl⟩ : syracuseStep 619805 = 232427) (by norm_num)
theorem B357677 : Blo 235815 357677 := bbase (se 3 (by rfl) ⟨67064, by rfl⟩ : syracuseStep 357677 = 134129) (by norm_num)
theorem B1209653 : Blo 235815 1209653 := bbase (se 5 (by rfl) ⟨56702, by rfl⟩ : syracuseStep 1209653 = 113405) (by norm_num)
theorem B357701 : Blo 235815 357701 := bbase (se 4 (by rfl) ⟨33534, by rfl⟩ : syracuseStep 357701 = 67069) (by norm_num)
theorem B357725 : Blo 235815 357725 := bbase (se 3 (by rfl) ⟨67073, by rfl⟩ : syracuseStep 357725 = 134147) (by norm_num)
theorem B357749 : Blo 235815 357749 := bbase (se 5 (by rfl) ⟨16769, by rfl⟩ : syracuseStep 357749 = 33539) (by norm_num)
theorem B357773 : Blo 235815 357773 := bbase (se 3 (by rfl) ⟨67082, by rfl⟩ : syracuseStep 357773 = 134165) (by norm_num)
theorem B357797 : Blo 235815 357797 := bbase (se 4 (by rfl) ⟨33543, by rfl⟩ : syracuseStep 357797 = 67087) (by norm_num)
theorem B357821 : Blo 235815 357821 := bbase (se 3 (by rfl) ⟨67091, by rfl⟩ : syracuseStep 357821 = 134183) (by norm_num)
theorem B521677 : Blo 235815 521677 := bbase (se 3 (by rfl) ⟨97814, by rfl⟩ : syracuseStep 521677 = 195629) (by norm_num)
theorem B357845 : Blo 235815 357845 := bbase (se 7 (by rfl) ⟨4193, by rfl⟩ : syracuseStep 357845 = 8387) (by norm_num)
theorem B357869 : Blo 235815 357869 := bbase (se 3 (by rfl) ⟨67100, by rfl⟩ : syracuseStep 357869 = 134201) (by norm_num)
theorem B357893 : Blo 235815 357893 := bbase (se 4 (by rfl) ⟨33552, by rfl⟩ : syracuseStep 357893 = 67105) (by norm_num)
theorem B357917 : Blo 235815 357917 := bbase (se 3 (by rfl) ⟨67109, by rfl⟩ : syracuseStep 357917 = 134219) (by norm_num)
theorem B357941 : Blo 235815 357941 := bbase (se 5 (by rfl) ⟨16778, by rfl⟩ : syracuseStep 357941 = 33557) (by norm_num)
theorem B357965 : Blo 235815 357965 := bbase (se 3 (by rfl) ⟨67118, by rfl⟩ : syracuseStep 357965 = 134237) (by norm_num)
theorem B357989 : Blo 235815 357989 := bbase (se 4 (by rfl) ⟨33561, by rfl⟩ : syracuseStep 357989 = 67123) (by norm_num)
theorem B358013 : Blo 235815 358013 := bbase (se 3 (by rfl) ⟨67127, by rfl⟩ : syracuseStep 358013 = 134255) (by norm_num)
theorem B358037 : Blo 235815 358037 := bbase (se 6 (by rfl) ⟨8391, by rfl⟩ : syracuseStep 358037 = 16783) (by norm_num)
theorem B358061 : Blo 235815 358061 := bbase (se 3 (by rfl) ⟨67136, by rfl⟩ : syracuseStep 358061 = 134273) (by norm_num)
theorem B358085 : Blo 235815 358085 := bbase (se 4 (by rfl) ⟨33570, by rfl⟩ : syracuseStep 358085 = 67141) (by norm_num)
theorem B358109 : Blo 235815 358109 := bbase (se 3 (by rfl) ⟨67145, by rfl⟩ : syracuseStep 358109 = 134291) (by norm_num)
theorem B358133 : Blo 235815 358133 := bbase (se 5 (by rfl) ⟨16787, by rfl⟩ : syracuseStep 358133 = 33575) (by norm_num)
theorem B358157 : Blo 235815 358157 := bbase (se 3 (by rfl) ⟨67154, by rfl⟩ : syracuseStep 358157 = 134309) (by norm_num)
theorem B358181 : Blo 235815 358181 := bbase (se 4 (by rfl) ⟨33579, by rfl⟩ : syracuseStep 358181 = 67159) (by norm_num)
theorem B358205 : Blo 235815 358205 := bbase (se 3 (by rfl) ⟨67163, by rfl⟩ : syracuseStep 358205 = 134327) (by norm_num)
theorem B1013573 : Blo 235815 1013573 := bbase (se 4 (by rfl) ⟨95022, by rfl⟩ : syracuseStep 1013573 = 190045) (by norm_num)
theorem B358229 : Blo 235815 358229 := bbase (se 9 (by rfl) ⟨1049, by rfl⟩ : syracuseStep 358229 = 2099) (by norm_num)
theorem B358253 : Blo 235815 358253 := bbase (se 3 (by rfl) ⟨67172, by rfl⟩ : syracuseStep 358253 = 134345) (by norm_num)
theorem B358277 : Blo 235815 358277 := bbase (se 4 (by rfl) ⟨33588, by rfl⟩ : syracuseStep 358277 = 67177) (by norm_num)
theorem B358301 : Blo 235815 358301 := bbase (se 3 (by rfl) ⟨67181, by rfl⟩ : syracuseStep 358301 = 134363) (by norm_num)
theorem B358325 : Blo 235815 358325 := bbase (se 5 (by rfl) ⟨16796, by rfl⟩ : syracuseStep 358325 = 33593) (by norm_num)
theorem B358349 : Blo 235815 358349 := bbase (se 3 (by rfl) ⟨67190, by rfl⟩ : syracuseStep 358349 = 134381) (by norm_num)
theorem B358373 : Blo 235815 358373 := bbase (se 4 (by rfl) ⟨33597, by rfl⟩ : syracuseStep 358373 = 67195) (by norm_num)
theorem B358397 : Blo 235815 358397 := bbase (se 3 (by rfl) ⟨67199, by rfl⟩ : syracuseStep 358397 = 134399) (by norm_num)
theorem B358421 : Blo 235815 358421 := bbase (se 6 (by rfl) ⟨8400, by rfl⟩ : syracuseStep 358421 = 16801) (by norm_num)
theorem B358445 : Blo 235815 358445 := bbase (se 3 (by rfl) ⟨67208, by rfl⟩ : syracuseStep 358445 = 134417) (by norm_num)
theorem B358469 : Blo 235815 358469 := bbase (se 4 (by rfl) ⟨33606, by rfl⟩ : syracuseStep 358469 = 67213) (by norm_num)
theorem B358493 : Blo 235815 358493 := bbase (se 3 (by rfl) ⟨67217, by rfl⟩ : syracuseStep 358493 = 134435) (by norm_num)
theorem B358517 : Blo 235815 358517 := bbase (se 5 (by rfl) ⟨16805, by rfl⟩ : syracuseStep 358517 = 33611) (by norm_num)
theorem B358541 : Blo 235815 358541 := bbase (se 3 (by rfl) ⟨67226, by rfl⟩ : syracuseStep 358541 = 134453) (by norm_num)
theorem B358565 : Blo 235815 358565 := bbase (se 4 (by rfl) ⟨33615, by rfl⟩ : syracuseStep 358565 = 67231) (by norm_num)
theorem B358589 : Blo 235815 358589 := bbase (se 3 (by rfl) ⟨67235, by rfl⟩ : syracuseStep 358589 = 134471) (by norm_num)
theorem B358613 : Blo 235815 358613 := bbase (se 7 (by rfl) ⟨4202, by rfl⟩ : syracuseStep 358613 = 8405) (by norm_num)
theorem B358637 : Blo 235815 358637 := bbase (se 3 (by rfl) ⟨67244, by rfl⟩ : syracuseStep 358637 = 134489) (by norm_num)
theorem B358661 : Blo 235815 358661 := bbase (se 4 (by rfl) ⟨33624, by rfl⟩ : syracuseStep 358661 = 67249) (by norm_num)
theorem B358685 : Blo 235815 358685 := bbase (se 3 (by rfl) ⟨67253, by rfl⟩ : syracuseStep 358685 = 134507) (by norm_num)
theorem B358709 : Blo 235815 358709 := bbase (se 5 (by rfl) ⟨16814, by rfl⟩ : syracuseStep 358709 = 33629) (by norm_num)
theorem B358733 : Blo 235815 358733 := bbase (se 3 (by rfl) ⟨67262, by rfl⟩ : syracuseStep 358733 = 134525) (by norm_num)
theorem B358757 : Blo 235815 358757 := bbase (se 4 (by rfl) ⟨33633, by rfl⟩ : syracuseStep 358757 = 67267) (by norm_num)
theorem B358781 : Blo 235815 358781 := bbase (se 3 (by rfl) ⟨67271, by rfl⟩ : syracuseStep 358781 = 134543) (by norm_num)
theorem B358805 : Blo 235815 358805 := bbase (se 6 (by rfl) ⟨8409, by rfl⟩ : syracuseStep 358805 = 16819) (by norm_num)
theorem B358829 : Blo 235815 358829 := bbase (se 3 (by rfl) ⟨67280, by rfl⟩ : syracuseStep 358829 = 134561) (by norm_num)
theorem B1800629 : Blo 235815 1800629 := bbase (se 5 (by rfl) ⟨84404, by rfl⟩ : syracuseStep 1800629 = 168809) (by norm_num)
theorem B358853 : Blo 235815 358853 := bbase (se 4 (by rfl) ⟨33642, by rfl⟩ : syracuseStep 358853 = 67285) (by norm_num)
theorem B358877 : Blo 235815 358877 := bbase (se 3 (by rfl) ⟨67289, by rfl⟩ : syracuseStep 358877 = 134579) (by norm_num)
theorem B358901 : Blo 235815 358901 := bbase (se 5 (by rfl) ⟨16823, by rfl⟩ : syracuseStep 358901 = 33647) (by norm_num)
theorem B358925 : Blo 235815 358925 := bbase (se 3 (by rfl) ⟨67298, by rfl⟩ : syracuseStep 358925 = 134597) (by norm_num)
theorem B358949 : Blo 235815 358949 := bbase (se 4 (by rfl) ⟨33651, by rfl⟩ : syracuseStep 358949 = 67303) (by norm_num)
theorem B358973 : Blo 235815 358973 := bbase (se 3 (by rfl) ⟨67307, by rfl⟩ : syracuseStep 358973 = 134615) (by norm_num)
theorem B1210949 : Blo 235815 1210949 := bbase (se 4 (by rfl) ⟨113526, by rfl⟩ : syracuseStep 1210949 = 227053) (by norm_num)
theorem B358997 : Blo 235815 358997 := bbase (se 8 (by rfl) ⟨2103, by rfl⟩ : syracuseStep 358997 = 4207) (by norm_num)
theorem B359021 : Blo 235815 359021 := bbase (se 3 (by rfl) ⟨67316, by rfl⟩ : syracuseStep 359021 = 134633) (by norm_num)
theorem B359045 : Blo 235815 359045 := bbase (se 4 (by rfl) ⟨33660, by rfl⟩ : syracuseStep 359045 = 67321) (by norm_num)
theorem B359069 : Blo 235815 359069 := bbase (se 3 (by rfl) ⟨67325, by rfl⟩ : syracuseStep 359069 = 134651) (by norm_num)
theorem B359093 : Blo 235815 359093 := bbase (se 5 (by rfl) ⟨16832, by rfl⟩ : syracuseStep 359093 = 33665) (by norm_num)
theorem B359117 : Blo 235815 359117 := bbase (se 3 (by rfl) ⟨67334, by rfl⟩ : syracuseStep 359117 = 134669) (by norm_num)
theorem B359141 : Blo 235815 359141 := bbase (se 4 (by rfl) ⟨33669, by rfl⟩ : syracuseStep 359141 = 67339) (by norm_num)
theorem B359165 : Blo 235815 359165 := bbase (se 3 (by rfl) ⟨67343, by rfl⟩ : syracuseStep 359165 = 134687) (by norm_num)
theorem B359189 : Blo 235815 359189 := bbase (se 6 (by rfl) ⟨8418, by rfl⟩ : syracuseStep 359189 = 16837) (by norm_num)
theorem B359213 : Blo 235815 359213 := bbase (se 3 (by rfl) ⟨67352, by rfl⟩ : syracuseStep 359213 = 134705) (by norm_num)
theorem B359237 : Blo 235815 359237 := bbase (se 4 (by rfl) ⟨33678, by rfl⟩ : syracuseStep 359237 = 67357) (by norm_num)
theorem B359261 : Blo 235815 359261 := bbase (se 3 (by rfl) ⟨67361, by rfl⟩ : syracuseStep 359261 = 134723) (by norm_num)
theorem B359285 : Blo 235815 359285 := bbase (se 5 (by rfl) ⟨16841, by rfl⟩ : syracuseStep 359285 = 33683) (by norm_num)
theorem B359309 : Blo 235815 359309 := bbase (se 3 (by rfl) ⟨67370, by rfl⟩ : syracuseStep 359309 = 134741) (by norm_num)
theorem B359333 : Blo 235815 359333 := bbase (se 4 (by rfl) ⟨33687, by rfl⟩ : syracuseStep 359333 = 67375) (by norm_num)
theorem B359357 : Blo 235815 359357 := bbase (se 3 (by rfl) ⟨67379, by rfl⟩ : syracuseStep 359357 = 134759) (by norm_num)
theorem B359381 : Blo 235815 359381 := bbase (se 7 (by rfl) ⟨4211, by rfl⟩ : syracuseStep 359381 = 8423) (by norm_num)
theorem B359405 : Blo 235815 359405 := bbase (se 3 (by rfl) ⟨67388, by rfl⟩ : syracuseStep 359405 = 134777) (by norm_num)
theorem B359429 : Blo 235815 359429 := bbase (se 4 (by rfl) ⟨33696, by rfl⟩ : syracuseStep 359429 = 67393) (by norm_num)
theorem B359453 : Blo 235815 359453 := bbase (se 3 (by rfl) ⟨67397, by rfl⟩ : syracuseStep 359453 = 134795) (by norm_num)
theorem B359477 : Blo 235815 359477 := bbase (se 5 (by rfl) ⟨16850, by rfl⟩ : syracuseStep 359477 = 33701) (by norm_num)
theorem B359501 : Blo 235815 359501 := bbase (se 3 (by rfl) ⟨67406, by rfl⟩ : syracuseStep 359501 = 134813) (by norm_num)
theorem B359525 : Blo 235815 359525 := bbase (se 4 (by rfl) ⟨33705, by rfl⟩ : syracuseStep 359525 = 67411) (by norm_num)
theorem B359549 : Blo 235815 359549 := bbase (se 3 (by rfl) ⟨67415, by rfl⟩ : syracuseStep 359549 = 134831) (by norm_num)
theorem B359573 : Blo 235815 359573 := bbase (se 6 (by rfl) ⟨8427, by rfl⟩ : syracuseStep 359573 = 16855) (by norm_num)
theorem B359597 : Blo 235815 359597 := bbase (se 3 (by rfl) ⟨67424, by rfl⟩ : syracuseStep 359597 = 134849) (by norm_num)
theorem B359621 : Blo 235815 359621 := bbase (se 4 (by rfl) ⟨33714, by rfl⟩ : syracuseStep 359621 = 67429) (by norm_num)
theorem B359645 : Blo 235815 359645 := bbase (se 3 (by rfl) ⟨67433, by rfl⟩ : syracuseStep 359645 = 134867) (by norm_num)
theorem B359669 : Blo 235815 359669 := bbase (se 5 (by rfl) ⟨16859, by rfl⟩ : syracuseStep 359669 = 33719) (by norm_num)
theorem B359693 : Blo 235815 359693 := bbase (se 3 (by rfl) ⟨67442, by rfl⟩ : syracuseStep 359693 = 134885) (by norm_num)
theorem B359717 : Blo 235815 359717 := bbase (se 4 (by rfl) ⟨33723, by rfl⟩ : syracuseStep 359717 = 67447) (by norm_num)
theorem B425309 : Blo 235815 425309 := bbase (se 3 (by rfl) ⟨79745, by rfl⟩ : syracuseStep 425309 = 159491) (by norm_num)
theorem B1375829 : Blo 235815 1375829 := bbase (se 8 (by rfl) ⟨8061, by rfl⟩ : syracuseStep 1375829 = 16123) (by norm_num)
theorem B720485 : Blo 235815 720485 := bbase (se 4 (by rfl) ⟨67545, by rfl⟩ : syracuseStep 720485 = 135091) (by norm_num)
theorem B1212245 : Blo 235815 1212245 := bbase (se 9 (by rfl) ⟨3551, by rfl⟩ : syracuseStep 1212245 = 7103) (by norm_num)
theorem B3047381 : Blo 235815 3047381 := bbase (se 7 (by rfl) ⟨35711, by rfl⟩ : syracuseStep 3047381 = 71423) (by norm_num)
theorem B425987 : Blo 235815 425987 := bstep (se 1 (by rfl) ⟨319490, by rfl⟩ : syracuseStep 425987 = 638981) B638981
theorem B1081457 : Blo 235815 1081457 := bstep (se 2 (by rfl) ⟨405546, by rfl⟩ : syracuseStep 1081457 = 811093) B811093
theorem B1310833 : Blo 235815 1310833 := bstep (se 2 (by rfl) ⟨491562, by rfl⟩ : syracuseStep 1310833 = 983125) B983125
theorem B4915313 : Blo 235815 4915313 := bstep (se 2 (by rfl) ⟨1843242, by rfl⟩ : syracuseStep 4915313 = 3686485) B3686485
theorem B1343729 : Blo 235815 1343729 := bstep (se 2 (by rfl) ⟨503898, by rfl⟩ : syracuseStep 1343729 = 1007797) B1007797
theorem B2064781 : Blo 235815 2064781 := bstep (se 3 (by rfl) ⟨387146, by rfl⟩ : syracuseStep 2064781 = 774293) B774293
theorem B721457 : Blo 235815 721457 := bstep (se 2 (by rfl) ⟨270546, by rfl⟩ : syracuseStep 721457 = 541093) B541093
theorem B1868771 : Blo 235815 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B1246385 : Blo 235815 1246385 := bstep (se 2 (by rfl) ⟨467394, by rfl⟩ : syracuseStep 1246385 = 934789) B934789
theorem B689393 : Blo 235815 689393 := bstep (se 2 (by rfl) ⟨258522, by rfl⟩ : syracuseStep 689393 = 517045) B517045
theorem B361763 : Blo 235815 361763 := bstep (se 1 (by rfl) ⟨271322, by rfl⟩ : syracuseStep 361763 = 542645) B542645
theorem B1050097 : Blo 235815 1050097 := bstep (se 2 (by rfl) ⟨393786, by rfl⟩ : syracuseStep 1050097 = 787573) B787573
theorem B1345187 : Blo 235815 1345187 := bstep (se 1 (by rfl) ⟨1008890, by rfl⟩ : syracuseStep 1345187 = 2017781) B2017781
theorem B886477 : Blo 235815 886477 := bstep (se 3 (by rfl) ⟨166214, by rfl⟩ : syracuseStep 886477 = 332429) B332429
theorem B722819 : Blo 235815 722819 := bstep (se 1 (by rfl) ⟨542114, by rfl⟩ : syracuseStep 722819 = 1084229) B1084229
theorem B362627 : Blo 235815 362627 := bstep (se 1 (by rfl) ⟨271970, by rfl⟩ : syracuseStep 362627 = 543941) B543941
theorem B362723 : Blo 235815 362723 := bstep (se 1 (by rfl) ⟨272042, by rfl⟩ : syracuseStep 362723 = 544085) B544085
theorem B1018595 : Blo 235815 1018595 := bstep (se 1 (by rfl) ⟨763946, by rfl⟩ : syracuseStep 1018595 = 1527893) B1527893
theorem B330481 : Blo 235815 330481 := bstep (se 2 (by rfl) ⟨123930, by rfl⟩ : syracuseStep 330481 = 247861) B247861
theorem B756515 : Blo 235815 756515 := bstep (se 1 (by rfl) ⟨567386, by rfl⟩ : syracuseStep 756515 = 1134773) B1134773
theorem B1641329 : Blo 235815 1641329 := bstep (se 2 (by rfl) ⟨615498, by rfl⟩ : syracuseStep 1641329 = 1230997) B1230997
theorem B265315 : Blo 235815 265315 := bstep (se 1 (by rfl) ⟨198986, by rfl⟩ : syracuseStep 265315 = 397973) B397973
theorem B265459 : Blo 235815 265459 := bstep (se 1 (by rfl) ⟨199094, by rfl⟩ : syracuseStep 265459 = 398189) B398189
theorem B265603 : Blo 235815 265603 := bstep (se 1 (by rfl) ⟨199202, by rfl⟩ : syracuseStep 265603 = 398405) B398405
theorem B265747 : Blo 235815 265747 := bstep (se 1 (by rfl) ⟨199310, by rfl⟩ : syracuseStep 265747 = 398621) B398621
theorem B265891 : Blo 235815 265891 := bstep (se 1 (by rfl) ⟨199418, by rfl⟩ : syracuseStep 265891 = 398837) B398837
theorem B1445539 : Blo 235815 1445539 := bstep (se 1 (by rfl) ⟨1084154, by rfl⟩ : syracuseStep 1445539 = 2168309) B2168309
theorem B298723 : Blo 235815 298723 := bstep (se 1 (by rfl) ⟨224042, by rfl⟩ : syracuseStep 298723 = 448085) B448085
theorem B266035 : Blo 235815 266035 := bstep (se 1 (by rfl) ⟨199526, by rfl⟩ : syracuseStep 266035 = 399053) B399053
theorem B298819 : Blo 235815 298819 := bstep (se 1 (by rfl) ⟨224114, by rfl⟩ : syracuseStep 298819 = 448229) B448229
theorem B429923 : Blo 235815 429923 := bstep (se 1 (by rfl) ⟨322442, by rfl⟩ : syracuseStep 429923 = 644885) B644885
theorem B266179 : Blo 235815 266179 := bstep (se 1 (by rfl) ⟨199634, by rfl⟩ : syracuseStep 266179 = 399269) B399269
theorem B757745 : Blo 235815 757745 := bstep (se 2 (by rfl) ⟨284154, by rfl⟩ : syracuseStep 757745 = 568309) B568309
theorem B266323 : Blo 235815 266323 := bstep (se 1 (by rfl) ⟨199742, by rfl⟩ : syracuseStep 266323 = 399485) B399485
theorem B266467 : Blo 235815 266467 := bstep (se 1 (by rfl) ⟨199850, by rfl⟩ : syracuseStep 266467 = 399701) B399701
theorem B4559075 : Blo 235815 4559075 := bstep (se 1 (by rfl) ⟨3419306, by rfl⟩ : syracuseStep 4559075 = 6838613) B6838613
theorem B299315 : Blo 235815 299315 := bstep (se 1 (by rfl) ⟨224486, by rfl⟩ : syracuseStep 299315 = 448973) B448973
theorem B4886897 : Blo 235815 4886897 := bstep (se 2 (by rfl) ⟨1832586, by rfl⟩ : syracuseStep 4886897 = 3665173) B3665173
theorem B266611 : Blo 235815 266611 := bstep (se 1 (by rfl) ⟨199958, by rfl⟩ : syracuseStep 266611 = 399917) B399917
theorem B266755 : Blo 235815 266755 := bstep (se 1 (by rfl) ⟨200066, by rfl⟩ : syracuseStep 266755 = 400133) B400133
theorem B1806947 : Blo 235815 1806947 := bstep (se 1 (by rfl) ⟨1355210, by rfl⟩ : syracuseStep 1806947 = 2710421) B2710421
theorem B397939 : Blo 235815 397939 := bstep (se 1 (by rfl) ⟨298454, by rfl⟩ : syracuseStep 397939 = 596909) B596909
theorem B266899 : Blo 235815 266899 := bstep (se 1 (by rfl) ⟨200174, by rfl⟩ : syracuseStep 266899 = 400349) B400349
theorem B398081 : Blo 235815 398081 := bstep (se 2 (by rfl) ⟨149280, by rfl⟩ : syracuseStep 398081 = 298561) B298561
theorem B267043 : Blo 235815 267043 := bstep (se 1 (by rfl) ⟨200282, by rfl⟩ : syracuseStep 267043 = 400565) B400565
theorem B758605 : Blo 235815 758605 := bstep (se 3 (by rfl) ⟨142238, by rfl⟩ : syracuseStep 758605 = 284477) B284477
theorem B398209 : Blo 235815 398209 := bstep (se 2 (by rfl) ⟨149328, by rfl⟩ : syracuseStep 398209 = 298657) B298657
theorem B398243 : Blo 235815 398243 := bstep (se 1 (by rfl) ⟨298682, by rfl⟩ : syracuseStep 398243 = 597365) B597365
theorem B267187 : Blo 235815 267187 := bstep (se 1 (by rfl) ⟨200390, by rfl⟩ : syracuseStep 267187 = 400781) B400781
theorem B300019 : Blo 235815 300019 := bstep (se 1 (by rfl) ⟨225014, by rfl⟩ : syracuseStep 300019 = 450029) B450029
theorem B398371 : Blo 235815 398371 := bstep (se 1 (by rfl) ⟨298778, by rfl⟩ : syracuseStep 398371 = 597557) B597557
theorem B267331 : Blo 235815 267331 := bstep (se 1 (by rfl) ⟨200498, by rfl⟩ : syracuseStep 267331 = 400997) B400997
theorem B300115 : Blo 235815 300115 := bstep (se 1 (by rfl) ⟨225086, by rfl⟩ : syracuseStep 300115 = 450173) B450173
theorem B431249 : Blo 235815 431249 := bstep (se 2 (by rfl) ⟨161718, by rfl⟩ : syracuseStep 431249 = 323437) B323437
theorem B398513 : Blo 235815 398513 := bstep (se 2 (by rfl) ⟨149442, by rfl⟩ : syracuseStep 398513 = 298885) B298885
theorem B1021133 : Blo 235815 1021133 := bstep (se 3 (by rfl) ⟨191462, by rfl⟩ : syracuseStep 1021133 = 382925) B382925
theorem B267475 : Blo 235815 267475 := bstep (se 1 (by rfl) ⟨200606, by rfl⟩ : syracuseStep 267475 = 401213) B401213
theorem B398641 : Blo 235815 398641 := bstep (se 2 (by rfl) ⟨149490, by rfl⟩ : syracuseStep 398641 = 298981) B298981
theorem B1021261 : Blo 235815 1021261 := bstep (se 3 (by rfl) ⟨191486, by rfl⟩ : syracuseStep 1021261 = 382973) B382973
theorem B398675 : Blo 235815 398675 := bstep (se 1 (by rfl) ⟨299006, by rfl⟩ : syracuseStep 398675 = 598013) B598013
theorem B267619 : Blo 235815 267619 := bstep (se 1 (by rfl) ⟨200714, by rfl⟩ : syracuseStep 267619 = 401429) B401429
theorem B398803 : Blo 235815 398803 := bstep (se 1 (by rfl) ⟨299102, by rfl⟩ : syracuseStep 398803 = 598205) B598205
theorem B267763 : Blo 235815 267763 := bstep (se 1 (by rfl) ⟨200822, by rfl⟩ : syracuseStep 267763 = 401645) B401645
theorem B300611 : Blo 235815 300611 := bstep (se 1 (by rfl) ⟨225458, by rfl⟩ : syracuseStep 300611 = 450917) B450917
theorem B398945 : Blo 235815 398945 := bstep (se 2 (by rfl) ⟨149604, by rfl⟩ : syracuseStep 398945 = 299209) B299209
theorem B857699 : Blo 235815 857699 := bstep (se 1 (by rfl) ⟨643274, by rfl⟩ : syracuseStep 857699 = 1286549) B1286549
theorem B267907 : Blo 235815 267907 := bstep (se 1 (by rfl) ⟨200930, by rfl⟩ : syracuseStep 267907 = 401861) B401861
theorem B399073 : Blo 235815 399073 := bstep (se 2 (by rfl) ⟨149652, by rfl⟩ : syracuseStep 399073 = 299305) B299305
theorem B431843 : Blo 235815 431843 := bstep (se 1 (by rfl) ⟨323882, by rfl⟩ : syracuseStep 431843 = 647765) B647765
theorem B399107 : Blo 235815 399107 := bstep (se 1 (by rfl) ⟨299330, by rfl⟩ : syracuseStep 399107 = 598661) B598661
theorem B268051 : Blo 235815 268051 := bstep (se 1 (by rfl) ⟨201038, by rfl⟩ : syracuseStep 268051 = 402077) B402077
theorem B399235 : Blo 235815 399235 := bstep (se 1 (by rfl) ⟨299426, by rfl⟩ : syracuseStep 399235 = 598853) B598853
theorem B268195 : Blo 235815 268195 := bstep (se 1 (by rfl) ⟨201146, by rfl⟩ : syracuseStep 268195 = 402293) B402293
theorem B399377 : Blo 235815 399377 := bstep (se 2 (by rfl) ⟨149766, by rfl⟩ : syracuseStep 399377 = 299533) B299533
theorem B268339 : Blo 235815 268339 := bstep (se 1 (by rfl) ⟨201254, by rfl⟩ : syracuseStep 268339 = 402509) B402509
theorem B1513541 : Blo 235815 1513541 := bstep (se 4 (by rfl) ⟨141894, by rfl⟩ : syracuseStep 1513541 = 283789) B283789
theorem B399505 : Blo 235815 399505 := bstep (se 2 (by rfl) ⟨149814, by rfl⟩ : syracuseStep 399505 = 299629) B299629
theorem B399539 : Blo 235815 399539 := bstep (se 1 (by rfl) ⟨299654, by rfl⟩ : syracuseStep 399539 = 599309) B599309
theorem B268483 : Blo 235815 268483 := bstep (se 1 (by rfl) ⟨201362, by rfl⟩ : syracuseStep 268483 = 402725) B402725
theorem B301315 : Blo 235815 301315 := bstep (se 1 (by rfl) ⟨225986, by rfl⟩ : syracuseStep 301315 = 451973) B451973
theorem B235827 : Blo 235815 235827 := bstep (se 1 (by rfl) ⟨176870, by rfl⟩ : syracuseStep 235827 = 353741) B353741
theorem B399667 : Blo 235815 399667 := bstep (se 1 (by rfl) ⟨299750, by rfl⟩ : syracuseStep 399667 = 599501) B599501
theorem B235843 : Blo 235815 235843 := bstep (se 1 (by rfl) ⟨176882, by rfl⟩ : syracuseStep 235843 = 353765) B353765
theorem B235859 : Blo 235815 235859 := bstep (se 1 (by rfl) ⟨176894, by rfl⟩ : syracuseStep 235859 = 353789) B353789
theorem B268627 : Blo 235815 268627 := bstep (se 1 (by rfl) ⟨201470, by rfl⟩ : syracuseStep 268627 = 402941) B402941
theorem B235875 : Blo 235815 235875 := bstep (se 1 (by rfl) ⟨176906, by rfl⟩ : syracuseStep 235875 = 353813) B353813
theorem B301411 : Blo 235815 301411 := bstep (se 1 (by rfl) ⟨226058, by rfl⟩ : syracuseStep 301411 = 452117) B452117
theorem B530801 : Blo 235815 530801 := bstep (se 2 (by rfl) ⟨199050, by rfl⟩ : syracuseStep 530801 = 398101) B398101
theorem B1022321 : Blo 235815 1022321 := bstep (se 2 (by rfl) ⟨383370, by rfl⟩ : syracuseStep 1022321 = 766741) B766741
theorem B235891 : Blo 235815 235891 := bstep (se 1 (by rfl) ⟨176918, by rfl⟩ : syracuseStep 235891 = 353837) B353837
theorem B235907 : Blo 235815 235907 := bstep (se 1 (by rfl) ⟨176930, by rfl⟩ : syracuseStep 235907 = 353861) B353861
theorem B530819 : Blo 235815 530819 := bstep (se 1 (by rfl) ⟨398114, by rfl⟩ : syracuseStep 530819 = 796229) B796229
theorem B760205 : Blo 235815 760205 := bstep (se 3 (by rfl) ⟨142538, by rfl⟩ : syracuseStep 760205 = 285077) B285077
theorem B235923 : Blo 235815 235923 := bstep (se 1 (by rfl) ⟨176942, by rfl⟩ : syracuseStep 235923 = 353885) B353885
theorem B235939 : Blo 235815 235939 := bstep (se 1 (by rfl) ⟨176954, by rfl⟩ : syracuseStep 235939 = 353909) B353909
theorem B235955 : Blo 235815 235955 := bstep (se 1 (by rfl) ⟨176966, by rfl⟩ : syracuseStep 235955 = 353933) B353933
theorem B399809 : Blo 235815 399809 := bstep (se 2 (by rfl) ⟨149928, by rfl⟩ : syracuseStep 399809 = 299857) B299857
theorem B235971 : Blo 235815 235971 := bstep (se 1 (by rfl) ⟨176978, by rfl⟩ : syracuseStep 235971 = 353957) B353957
theorem B235987 : Blo 235815 235987 := bstep (se 1 (by rfl) ⟨176990, by rfl⟩ : syracuseStep 235987 = 353981) B353981
theorem B236003 : Blo 235815 236003 := bstep (se 1 (by rfl) ⟨177002, by rfl⟩ : syracuseStep 236003 = 354005) B354005
theorem B268771 : Blo 235815 268771 := bstep (se 1 (by rfl) ⟨201578, by rfl⟩ : syracuseStep 268771 = 403157) B403157
theorem B236019 : Blo 235815 236019 := bstep (se 1 (by rfl) ⟨177014, by rfl⟩ : syracuseStep 236019 = 354029) B354029
theorem B236035 : Blo 235815 236035 := bstep (se 1 (by rfl) ⟨177026, by rfl⟩ : syracuseStep 236035 = 354053) B354053
theorem B236051 : Blo 235815 236051 := bstep (se 1 (by rfl) ⟨177038, by rfl⟩ : syracuseStep 236051 = 354077) B354077
theorem B236067 : Blo 235815 236067 := bstep (se 1 (by rfl) ⟨177050, by rfl⟩ : syracuseStep 236067 = 354101) B354101
theorem B236083 : Blo 235815 236083 := bstep (se 1 (by rfl) ⟨177062, by rfl⟩ : syracuseStep 236083 = 354125) B354125
theorem B399937 : Blo 235815 399937 := bstep (se 2 (by rfl) ⟨149976, by rfl⟩ : syracuseStep 399937 = 299953) B299953
theorem B236099 : Blo 235815 236099 := bstep (se 1 (by rfl) ⟨177074, by rfl⟩ : syracuseStep 236099 = 354149) B354149
theorem B236115 : Blo 235815 236115 := bstep (se 1 (by rfl) ⟨177086, by rfl⟩ : syracuseStep 236115 = 354173) B354173
theorem B236131 : Blo 235815 236131 := bstep (se 1 (by rfl) ⟨177098, by rfl⟩ : syracuseStep 236131 = 354197) B354197
theorem B399971 : Blo 235815 399971 := bstep (se 1 (by rfl) ⟨299978, by rfl⟩ : syracuseStep 399971 = 599957) B599957
theorem B236147 : Blo 235815 236147 := bstep (se 1 (by rfl) ⟨177110, by rfl⟩ : syracuseStep 236147 = 354221) B354221
theorem B268915 : Blo 235815 268915 := bstep (se 1 (by rfl) ⟨201686, by rfl⟩ : syracuseStep 268915 = 403373) B403373
theorem B236163 : Blo 235815 236163 := bstep (se 1 (by rfl) ⟨177122, by rfl⟩ : syracuseStep 236163 = 354245) B354245
theorem B531089 : Blo 235815 531089 := bstep (se 2 (by rfl) ⟨199158, by rfl⟩ : syracuseStep 531089 = 398317) B398317
theorem B236179 : Blo 235815 236179 := bstep (se 1 (by rfl) ⟨177134, by rfl⟩ : syracuseStep 236179 = 354269) B354269
theorem B531107 : Blo 235815 531107 := bstep (se 1 (by rfl) ⟨398330, by rfl⟩ : syracuseStep 531107 = 796661) B796661
theorem B236195 : Blo 235815 236195 := bstep (se 1 (by rfl) ⟨177146, by rfl⟩ : syracuseStep 236195 = 354293) B354293
theorem B236211 : Blo 235815 236211 := bstep (se 1 (by rfl) ⟨177158, by rfl⟩ : syracuseStep 236211 = 354317) B354317
theorem B236227 : Blo 235815 236227 := bstep (se 1 (by rfl) ⟨177170, by rfl⟩ : syracuseStep 236227 = 354341) B354341
theorem B236243 : Blo 235815 236243 := bstep (se 1 (by rfl) ⟨177182, by rfl⟩ : syracuseStep 236243 = 354365) B354365
theorem B236259 : Blo 235815 236259 := bstep (se 1 (by rfl) ⟨177194, by rfl⟩ : syracuseStep 236259 = 354389) B354389
theorem B400099 : Blo 235815 400099 := bstep (se 1 (by rfl) ⟨300074, by rfl⟩ : syracuseStep 400099 = 600149) B600149
theorem B236275 : Blo 235815 236275 := bstep (se 1 (by rfl) ⟨177206, by rfl⟩ : syracuseStep 236275 = 354413) B354413
theorem B236291 : Blo 235815 236291 := bstep (se 1 (by rfl) ⟨177218, by rfl⟩ : syracuseStep 236291 = 354437) B354437
theorem B269059 : Blo 235815 269059 := bstep (se 1 (by rfl) ⟨201794, by rfl⟩ : syracuseStep 269059 = 403589) B403589
theorem B236307 : Blo 235815 236307 := bstep (se 1 (by rfl) ⟨177230, by rfl⟩ : syracuseStep 236307 = 354461) B354461
theorem B236323 : Blo 235815 236323 := bstep (se 1 (by rfl) ⟨177242, by rfl⟩ : syracuseStep 236323 = 354485) B354485
theorem B236339 : Blo 235815 236339 := bstep (se 1 (by rfl) ⟨177254, by rfl⟩ : syracuseStep 236339 = 354509) B354509
theorem B269123 : Blo 235815 269123 := bstep (se 1 (by rfl) ⟨201842, by rfl⟩ : syracuseStep 269123 = 403685) B403685
theorem B236355 : Blo 235815 236355 := bstep (se 1 (by rfl) ⟨177266, by rfl⟩ : syracuseStep 236355 = 354533) B354533
theorem B236371 : Blo 235815 236371 := bstep (se 1 (by rfl) ⟨177278, by rfl⟩ : syracuseStep 236371 = 354557) B354557
theorem B301907 : Blo 235815 301907 := bstep (se 1 (by rfl) ⟨226430, by rfl⟩ : syracuseStep 301907 = 452861) B452861
theorem B236387 : Blo 235815 236387 := bstep (se 1 (by rfl) ⟨177290, by rfl⟩ : syracuseStep 236387 = 354581) B354581
theorem B400241 : Blo 235815 400241 := bstep (se 2 (by rfl) ⟨150090, by rfl⟩ : syracuseStep 400241 = 300181) B300181
theorem B236403 : Blo 235815 236403 := bstep (se 1 (by rfl) ⟨177302, by rfl⟩ : syracuseStep 236403 = 354605) B354605
theorem B236419 : Blo 235815 236419 := bstep (se 1 (by rfl) ⟨177314, by rfl⟩ : syracuseStep 236419 = 354629) B354629
theorem B236435 : Blo 235815 236435 := bstep (se 1 (by rfl) ⟨177326, by rfl⟩ : syracuseStep 236435 = 354653) B354653
theorem B269203 : Blo 235815 269203 := bstep (se 1 (by rfl) ⟨201902, by rfl⟩ : syracuseStep 269203 = 403805) B403805
theorem B236451 : Blo 235815 236451 := bstep (se 1 (by rfl) ⟨177338, by rfl⟩ : syracuseStep 236451 = 354677) B354677
theorem B531377 : Blo 235815 531377 := bstep (se 2 (by rfl) ⟨199266, by rfl⟩ : syracuseStep 531377 = 398533) B398533
theorem B236467 : Blo 235815 236467 := bstep (se 1 (by rfl) ⟨177350, by rfl⟩ : syracuseStep 236467 = 354701) B354701
theorem B531395 : Blo 235815 531395 := bstep (se 1 (by rfl) ⟨398546, by rfl⟩ : syracuseStep 531395 = 797093) B797093
theorem B236483 : Blo 235815 236483 := bstep (se 1 (by rfl) ⟨177362, by rfl⟩ : syracuseStep 236483 = 354725) B354725
theorem B662467 : Blo 235815 662467 := bstep (se 1 (by rfl) ⟨496850, by rfl⟩ : syracuseStep 662467 = 993701) B993701
theorem B236499 : Blo 235815 236499 := bstep (se 1 (by rfl) ⟨177374, by rfl⟩ : syracuseStep 236499 = 354749) B354749
theorem B236515 : Blo 235815 236515 := bstep (se 1 (by rfl) ⟨177386, by rfl⟩ : syracuseStep 236515 = 354773) B354773
theorem B400369 : Blo 235815 400369 := bstep (se 2 (by rfl) ⟨150138, by rfl⟩ : syracuseStep 400369 = 300277) B300277
theorem B236531 : Blo 235815 236531 := bstep (se 1 (by rfl) ⟨177398, by rfl⟩ : syracuseStep 236531 = 354797) B354797
theorem B236547 : Blo 235815 236547 := bstep (se 1 (by rfl) ⟨177410, by rfl⟩ : syracuseStep 236547 = 354821) B354821
theorem B236563 : Blo 235815 236563 := bstep (se 1 (by rfl) ⟨177422, by rfl⟩ : syracuseStep 236563 = 354845) B354845
theorem B400403 : Blo 235815 400403 := bstep (se 1 (by rfl) ⟨300302, by rfl⟩ : syracuseStep 400403 = 600605) B600605
theorem B236579 : Blo 235815 236579 := bstep (se 1 (by rfl) ⟨177434, by rfl⟩ : syracuseStep 236579 = 354869) B354869
theorem B269347 : Blo 235815 269347 := bstep (se 1 (by rfl) ⟨202010, by rfl⟩ : syracuseStep 269347 = 404021) B404021
theorem B597041 : Blo 235815 597041 := bstep (se 2 (by rfl) ⟨223890, by rfl⟩ : syracuseStep 597041 = 447781) B447781
theorem B236595 : Blo 235815 236595 := bstep (se 1 (by rfl) ⟨177446, by rfl⟩ : syracuseStep 236595 = 354893) B354893
theorem B236611 : Blo 235815 236611 := bstep (se 1 (by rfl) ⟨177458, by rfl⟩ : syracuseStep 236611 = 354917) B354917
theorem B236627 : Blo 235815 236627 := bstep (se 1 (by rfl) ⟨177470, by rfl⟩ : syracuseStep 236627 = 354941) B354941
theorem B597091 : Blo 235815 597091 := bstep (se 1 (by rfl) ⟨447818, by rfl⟩ : syracuseStep 597091 = 895637) B895637
theorem B236643 : Blo 235815 236643 := bstep (se 1 (by rfl) ⟨177482, by rfl⟩ : syracuseStep 236643 = 354965) B354965
theorem B236659 : Blo 235815 236659 := bstep (se 1 (by rfl) ⟨177494, by rfl⟩ : syracuseStep 236659 = 354989) B354989
theorem B236675 : Blo 235815 236675 := bstep (se 1 (by rfl) ⟨177506, by rfl⟩ : syracuseStep 236675 = 355013) B355013
theorem B236691 : Blo 235815 236691 := bstep (se 1 (by rfl) ⟨177518, by rfl⟩ : syracuseStep 236691 = 355037) B355037
theorem B400531 : Blo 235815 400531 := bstep (se 1 (by rfl) ⟨300398, by rfl⟩ : syracuseStep 400531 = 600797) B600797
theorem B236707 : Blo 235815 236707 := bstep (se 1 (by rfl) ⟨177530, by rfl⟩ : syracuseStep 236707 = 355061) B355061
theorem B236723 : Blo 235815 236723 := bstep (se 1 (by rfl) ⟨177542, by rfl⟩ : syracuseStep 236723 = 355085) B355085
theorem B269491 : Blo 235815 269491 := bstep (se 1 (by rfl) ⟨202118, by rfl⟩ : syracuseStep 269491 = 404237) B404237
theorem B236739 : Blo 235815 236739 := bstep (se 1 (by rfl) ⟨177554, by rfl⟩ : syracuseStep 236739 = 355109) B355109
theorem B531665 : Blo 235815 531665 := bstep (se 2 (by rfl) ⟨199374, by rfl⟩ : syracuseStep 531665 = 398749) B398749
theorem B236755 : Blo 235815 236755 := bstep (se 1 (by rfl) ⟨177566, by rfl⟩ : syracuseStep 236755 = 355133) B355133
theorem B531683 : Blo 235815 531683 := bstep (se 1 (by rfl) ⟨398762, by rfl⟩ : syracuseStep 531683 = 797525) B797525
theorem B236771 : Blo 235815 236771 := bstep (se 1 (by rfl) ⟨177578, by rfl⟩ : syracuseStep 236771 = 355157) B355157
theorem B597233 : Blo 235815 597233 := bstep (se 2 (by rfl) ⟨223962, by rfl⟩ : syracuseStep 597233 = 447925) B447925
theorem B236787 : Blo 235815 236787 := bstep (se 1 (by rfl) ⟨177590, by rfl⟩ : syracuseStep 236787 = 355181) B355181
theorem B236803 : Blo 235815 236803 := bstep (se 1 (by rfl) ⟨177602, by rfl⟩ : syracuseStep 236803 = 355205) B355205
theorem B695569 : Blo 235815 695569 := bstep (se 2 (by rfl) ⟨260838, by rfl⟩ : syracuseStep 695569 = 521677) B521677
theorem B236819 : Blo 235815 236819 := bstep (se 1 (by rfl) ⟨177614, by rfl⟩ : syracuseStep 236819 = 355229) B355229
theorem B400673 : Blo 235815 400673 := bstep (se 2 (by rfl) ⟨150252, by rfl⟩ : syracuseStep 400673 = 300505) B300505
theorem B236835 : Blo 235815 236835 := bstep (se 1 (by rfl) ⟨177626, by rfl⟩ : syracuseStep 236835 = 355253) B355253
theorem B236851 : Blo 235815 236851 := bstep (se 1 (by rfl) ⟨177638, by rfl⟩ : syracuseStep 236851 = 355277) B355277
theorem B236867 : Blo 235815 236867 := bstep (se 1 (by rfl) ⟨177650, by rfl⟩ : syracuseStep 236867 = 355301) B355301
theorem B269635 : Blo 235815 269635 := bstep (se 1 (by rfl) ⟨202226, by rfl⟩ : syracuseStep 269635 = 404453) B404453
theorem B236883 : Blo 235815 236883 := bstep (se 1 (by rfl) ⟨177662, by rfl⟩ : syracuseStep 236883 = 355325) B355325
theorem B236899 : Blo 235815 236899 := bstep (se 1 (by rfl) ⟨177674, by rfl⟩ : syracuseStep 236899 = 355349) B355349
theorem B236915 : Blo 235815 236915 := bstep (se 1 (by rfl) ⟨177686, by rfl⟩ : syracuseStep 236915 = 355373) B355373
theorem B236931 : Blo 235815 236931 := bstep (se 1 (by rfl) ⟨177698, by rfl⟩ : syracuseStep 236931 = 355397) B355397
theorem B236947 : Blo 235815 236947 := bstep (se 1 (by rfl) ⟨177710, by rfl⟩ : syracuseStep 236947 = 355421) B355421
theorem B400801 : Blo 235815 400801 := bstep (se 2 (by rfl) ⟨150300, by rfl⟩ : syracuseStep 400801 = 300601) B300601
theorem B236963 : Blo 235815 236963 := bstep (se 1 (by rfl) ⟨177722, by rfl⟩ : syracuseStep 236963 = 355445) B355445
theorem B236979 : Blo 235815 236979 := bstep (se 1 (by rfl) ⟨177734, by rfl⟩ : syracuseStep 236979 = 355469) B355469
theorem B236995 : Blo 235815 236995 := bstep (se 1 (by rfl) ⟨177746, by rfl⟩ : syracuseStep 236995 = 355493) B355493
theorem B400835 : Blo 235815 400835 := bstep (se 1 (by rfl) ⟨300626, by rfl⟩ : syracuseStep 400835 = 601253) B601253
theorem B237011 : Blo 235815 237011 := bstep (se 1 (by rfl) ⟨177758, by rfl⟩ : syracuseStep 237011 = 355517) B355517
theorem B269779 : Blo 235815 269779 := bstep (se 1 (by rfl) ⟨202334, by rfl⟩ : syracuseStep 269779 = 404669) B404669
theorem B237027 : Blo 235815 237027 := bstep (se 1 (by rfl) ⟨177770, by rfl⟩ : syracuseStep 237027 = 355541) B355541
theorem B531953 : Blo 235815 531953 := bstep (se 2 (by rfl) ⟨199482, by rfl⟩ : syracuseStep 531953 = 398965) B398965
theorem B237043 : Blo 235815 237043 := bstep (se 1 (by rfl) ⟨177782, by rfl⟩ : syracuseStep 237043 = 355565) B355565
theorem B531971 : Blo 235815 531971 := bstep (se 1 (by rfl) ⟨398978, by rfl⟩ : syracuseStep 531971 = 797957) B797957
theorem B237059 : Blo 235815 237059 := bstep (se 1 (by rfl) ⟨177794, by rfl⟩ : syracuseStep 237059 = 355589) B355589
theorem B237075 : Blo 235815 237075 := bstep (se 1 (by rfl) ⟨177806, by rfl⟩ : syracuseStep 237075 = 355613) B355613
theorem B302611 : Blo 235815 302611 := bstep (se 1 (by rfl) ⟨226958, by rfl⟩ : syracuseStep 302611 = 453917) B453917
theorem B237091 : Blo 235815 237091 := bstep (se 1 (by rfl) ⟨177818, by rfl⟩ : syracuseStep 237091 = 355637) B355637
theorem B237107 : Blo 235815 237107 := bstep (se 1 (by rfl) ⟨177830, by rfl⟩ : syracuseStep 237107 = 355661) B355661
theorem B237123 : Blo 235815 237123 := bstep (se 1 (by rfl) ⟨177842, by rfl⟩ : syracuseStep 237123 = 355685) B355685
theorem B400963 : Blo 235815 400963 := bstep (se 1 (by rfl) ⟨300722, by rfl⟩ : syracuseStep 400963 = 601445) B601445
theorem B237139 : Blo 235815 237139 := bstep (se 1 (by rfl) ⟨177854, by rfl⟩ : syracuseStep 237139 = 355709) B355709
theorem B237155 : Blo 235815 237155 := bstep (se 1 (by rfl) ⟨177866, by rfl⟩ : syracuseStep 237155 = 355733) B355733
theorem B1384049 : Blo 235815 1384049 := bstep (se 2 (by rfl) ⟨519018, by rfl⟩ : syracuseStep 1384049 = 1038037) B1038037
theorem B237171 : Blo 235815 237171 := bstep (se 1 (by rfl) ⟨177878, by rfl⟩ : syracuseStep 237171 = 355757) B355757
theorem B302707 : Blo 235815 302707 := bstep (se 1 (by rfl) ⟨227030, by rfl⟩ : syracuseStep 302707 = 454061) B454061
theorem B237187 : Blo 235815 237187 := bstep (se 1 (by rfl) ⟨177890, by rfl⟩ : syracuseStep 237187 = 355781) B355781
theorem B237203 : Blo 235815 237203 := bstep (se 1 (by rfl) ⟨177902, by rfl⟩ : syracuseStep 237203 = 355805) B355805
theorem B237219 : Blo 235815 237219 := bstep (se 1 (by rfl) ⟨177914, by rfl⟩ : syracuseStep 237219 = 355829) B355829
theorem B237235 : Blo 235815 237235 := bstep (se 1 (by rfl) ⟨177926, by rfl⟩ : syracuseStep 237235 = 355853) B355853
theorem B237251 : Blo 235815 237251 := bstep (se 1 (by rfl) ⟨177938, by rfl⟩ : syracuseStep 237251 = 355877) B355877
theorem B401105 : Blo 235815 401105 := bstep (se 2 (by rfl) ⟨150414, by rfl⟩ : syracuseStep 401105 = 300829) B300829
theorem B237267 : Blo 235815 237267 := bstep (se 1 (by rfl) ⟨177950, by rfl⟩ : syracuseStep 237267 = 355901) B355901
theorem B237283 : Blo 235815 237283 := bstep (se 1 (by rfl) ⟨177962, by rfl⟩ : syracuseStep 237283 = 355925) B355925
theorem B237299 : Blo 235815 237299 := bstep (se 1 (by rfl) ⟨177974, by rfl⟩ : syracuseStep 237299 = 355949) B355949
theorem B237315 : Blo 235815 237315 := bstep (se 1 (by rfl) ⟨177986, by rfl⟩ : syracuseStep 237315 = 355973) B355973
theorem B532241 : Blo 235815 532241 := bstep (se 2 (by rfl) ⟨199590, by rfl⟩ : syracuseStep 532241 = 399181) B399181
theorem B237331 : Blo 235815 237331 := bstep (se 1 (by rfl) ⟨177998, by rfl⟩ : syracuseStep 237331 = 355997) B355997
theorem B532259 : Blo 235815 532259 := bstep (se 1 (by rfl) ⟨399194, by rfl⟩ : syracuseStep 532259 = 798389) B798389
theorem B237347 : Blo 235815 237347 := bstep (se 1 (by rfl) ⟨178010, by rfl⟩ : syracuseStep 237347 = 356021) B356021
theorem B237363 : Blo 235815 237363 := bstep (se 1 (by rfl) ⟨178022, by rfl⟩ : syracuseStep 237363 = 356045) B356045
theorem B237379 : Blo 235815 237379 := bstep (se 1 (by rfl) ⟨178034, by rfl⟩ : syracuseStep 237379 = 356069) B356069
theorem B401233 : Blo 235815 401233 := bstep (se 2 (by rfl) ⟨150462, by rfl⟩ : syracuseStep 401233 = 300925) B300925
theorem B237395 : Blo 235815 237395 := bstep (se 1 (by rfl) ⟨178046, by rfl⟩ : syracuseStep 237395 = 356093) B356093
theorem B237411 : Blo 235815 237411 := bstep (se 1 (by rfl) ⟨178058, by rfl⟩ : syracuseStep 237411 = 356117) B356117
theorem B2039651 : Blo 235815 2039651 := bstep (se 1 (by rfl) ⟨1529738, by rfl⟩ : syracuseStep 2039651 = 3059477) B3059477
theorem B237427 : Blo 235815 237427 := bstep (se 1 (by rfl) ⟨178070, by rfl⟩ : syracuseStep 237427 = 356141) B356141
theorem B401267 : Blo 235815 401267 := bstep (se 1 (by rfl) ⟨300950, by rfl⟩ : syracuseStep 401267 = 601901) B601901
theorem B237443 : Blo 235815 237443 := bstep (se 1 (by rfl) ⟨178082, by rfl⟩ : syracuseStep 237443 = 356165) B356165
theorem B237459 : Blo 235815 237459 := bstep (se 1 (by rfl) ⟨178094, by rfl⟩ : syracuseStep 237459 = 356189) B356189
theorem B237475 : Blo 235815 237475 := bstep (se 1 (by rfl) ⟨178106, by rfl⟩ : syracuseStep 237475 = 356213) B356213
theorem B237491 : Blo 235815 237491 := bstep (se 1 (by rfl) ⟨178118, by rfl⟩ : syracuseStep 237491 = 356237) B356237
theorem B237507 : Blo 235815 237507 := bstep (se 1 (by rfl) ⟨178130, by rfl⟩ : syracuseStep 237507 = 356261) B356261
theorem B761795 : Blo 235815 761795 := bstep (se 1 (by rfl) ⟨571346, by rfl⟩ : syracuseStep 761795 = 1142693) B1142693
theorem B1286093 : Blo 235815 1286093 := bstep (se 3 (by rfl) ⟨241142, by rfl⟩ : syracuseStep 1286093 = 482285) B482285
theorem B237523 : Blo 235815 237523 := bstep (se 1 (by rfl) ⟨178142, by rfl⟩ : syracuseStep 237523 = 356285) B356285
theorem B237539 : Blo 235815 237539 := bstep (se 1 (by rfl) ⟨178154, by rfl⟩ : syracuseStep 237539 = 356309) B356309
theorem B237555 : Blo 235815 237555 := bstep (se 1 (by rfl) ⟨178166, by rfl⟩ : syracuseStep 237555 = 356333) B356333
theorem B401395 : Blo 235815 401395 := bstep (se 1 (by rfl) ⟨301046, by rfl⟩ : syracuseStep 401395 = 602093) B602093
theorem B237571 : Blo 235815 237571 := bstep (se 1 (by rfl) ⟨178178, by rfl⟩ : syracuseStep 237571 = 356357) B356357
theorem B237587 : Blo 235815 237587 := bstep (se 1 (by rfl) ⟨178190, by rfl⟩ : syracuseStep 237587 = 356381) B356381
theorem B237603 : Blo 235815 237603 := bstep (se 1 (by rfl) ⟨178202, by rfl⟩ : syracuseStep 237603 = 356405) B356405
theorem B532529 : Blo 235815 532529 := bstep (se 2 (by rfl) ⟨199698, by rfl⟩ : syracuseStep 532529 = 399397) B399397
theorem B237619 : Blo 235815 237619 := bstep (se 1 (by rfl) ⟨178214, by rfl⟩ : syracuseStep 237619 = 356429) B356429
theorem B532547 : Blo 235815 532547 := bstep (se 1 (by rfl) ⟨399410, by rfl⟩ : syracuseStep 532547 = 798821) B798821
theorem B237635 : Blo 235815 237635 := bstep (se 1 (by rfl) ⟨178226, by rfl⟩ : syracuseStep 237635 = 356453) B356453
theorem B237651 : Blo 235815 237651 := bstep (se 1 (by rfl) ⟨178238, by rfl⟩ : syracuseStep 237651 = 356477) B356477
theorem B237667 : Blo 235815 237667 := bstep (se 1 (by rfl) ⟨178250, by rfl⟩ : syracuseStep 237667 = 356501) B356501
theorem B303203 : Blo 235815 303203 := bstep (se 1 (by rfl) ⟨227402, by rfl⟩ : syracuseStep 303203 = 454805) B454805
theorem B237683 : Blo 235815 237683 := bstep (se 1 (by rfl) ⟨178262, by rfl⟩ : syracuseStep 237683 = 356525) B356525
theorem B336001 : Blo 235815 336001 := bstep (se 2 (by rfl) ⟨126000, by rfl⟩ : syracuseStep 336001 = 252001) B252001
theorem B401537 : Blo 235815 401537 := bstep (se 2 (by rfl) ⟨150576, by rfl⟩ : syracuseStep 401537 = 301153) B301153
theorem B237699 : Blo 235815 237699 := bstep (se 1 (by rfl) ⟨178274, by rfl⟩ : syracuseStep 237699 = 356549) B356549
theorem B761987 : Blo 235815 761987 := bstep (se 1 (by rfl) ⟨571490, by rfl⟩ : syracuseStep 761987 = 1142981) B1142981
theorem B237715 : Blo 235815 237715 := bstep (se 1 (by rfl) ⟨178286, by rfl⟩ : syracuseStep 237715 = 356573) B356573
theorem B336035 : Blo 235815 336035 := bstep (se 1 (by rfl) ⟨252026, by rfl⟩ : syracuseStep 336035 = 504053) B504053
theorem B237731 : Blo 235815 237731 := bstep (se 1 (by rfl) ⟨178298, by rfl⟩ : syracuseStep 237731 = 356597) B356597
theorem B237747 : Blo 235815 237747 := bstep (se 1 (by rfl) ⟨178310, by rfl⟩ : syracuseStep 237747 = 356621) B356621
theorem B237763 : Blo 235815 237763 := bstep (se 1 (by rfl) ⟨178322, by rfl⟩ : syracuseStep 237763 = 356645) B356645
theorem B598225 : Blo 235815 598225 := bstep (se 2 (by rfl) ⟨224334, by rfl⟩ : syracuseStep 598225 = 448669) B448669
theorem B237779 : Blo 235815 237779 := bstep (se 1 (by rfl) ⟨178334, by rfl⟩ : syracuseStep 237779 = 356669) B356669
theorem B237795 : Blo 235815 237795 := bstep (se 1 (by rfl) ⟨178346, by rfl⟩ : syracuseStep 237795 = 356693) B356693
theorem B237811 : Blo 235815 237811 := bstep (se 1 (by rfl) ⟨178358, by rfl⟩ : syracuseStep 237811 = 356717) B356717
theorem B401665 : Blo 235815 401665 := bstep (se 2 (by rfl) ⟨150624, by rfl⟩ : syracuseStep 401665 = 301249) B301249
theorem B237827 : Blo 235815 237827 := bstep (se 1 (by rfl) ⟨178370, by rfl⟩ : syracuseStep 237827 = 356741) B356741
theorem B237843 : Blo 235815 237843 := bstep (se 1 (by rfl) ⟨178382, by rfl⟩ : syracuseStep 237843 = 356765) B356765
theorem B237859 : Blo 235815 237859 := bstep (se 1 (by rfl) ⟨178394, by rfl⟩ : syracuseStep 237859 = 356789) B356789
theorem B401699 : Blo 235815 401699 := bstep (se 1 (by rfl) ⟨301274, by rfl⟩ : syracuseStep 401699 = 602549) B602549
theorem B237875 : Blo 235815 237875 := bstep (se 1 (by rfl) ⟨178406, by rfl⟩ : syracuseStep 237875 = 356813) B356813
theorem B3449141 : Blo 235815 3449141 := bstep (se 5 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 3449141 = 323357) B323357
theorem B237891 : Blo 235815 237891 := bstep (se 1 (by rfl) ⟨178418, by rfl⟩ : syracuseStep 237891 = 356837) B356837
theorem B532817 : Blo 235815 532817 := bstep (se 2 (by rfl) ⟨199806, by rfl⟩ : syracuseStep 532817 = 399613) B399613
theorem B237907 : Blo 235815 237907 := bstep (se 1 (by rfl) ⟨178430, by rfl⟩ : syracuseStep 237907 = 356861) B356861
theorem B532835 : Blo 235815 532835 := bstep (se 1 (by rfl) ⟨399626, by rfl⟩ : syracuseStep 532835 = 799253) B799253
theorem B237923 : Blo 235815 237923 := bstep (se 1 (by rfl) ⟨178442, by rfl⟩ : syracuseStep 237923 = 356885) B356885
theorem B237939 : Blo 235815 237939 := bstep (se 1 (by rfl) ⟨178454, by rfl⟩ : syracuseStep 237939 = 356909) B356909
theorem B237955 : Blo 235815 237955 := bstep (se 1 (by rfl) ⟨178466, by rfl⟩ : syracuseStep 237955 = 356933) B356933
theorem B237971 : Blo 235815 237971 := bstep (se 1 (by rfl) ⟨178478, by rfl⟩ : syracuseStep 237971 = 356957) B356957
theorem B237987 : Blo 235815 237987 := bstep (se 1 (by rfl) ⟨178490, by rfl⟩ : syracuseStep 237987 = 356981) B356981
theorem B401827 : Blo 235815 401827 := bstep (se 1 (by rfl) ⟨301370, by rfl⟩ : syracuseStep 401827 = 602741) B602741
theorem B238003 : Blo 235815 238003 := bstep (se 1 (by rfl) ⟨178502, by rfl⟩ : syracuseStep 238003 = 357005) B357005
theorem B238019 : Blo 235815 238019 := bstep (se 1 (by rfl) ⟨178514, by rfl⟩ : syracuseStep 238019 = 357029) B357029
theorem B238035 : Blo 235815 238035 := bstep (se 1 (by rfl) ⟨178526, by rfl⟩ : syracuseStep 238035 = 357053) B357053
theorem B598499 : Blo 235815 598499 := bstep (se 1 (by rfl) ⟨448874, by rfl⟩ : syracuseStep 598499 = 897749) B897749
theorem B238051 : Blo 235815 238051 := bstep (se 1 (by rfl) ⟨178538, by rfl⟩ : syracuseStep 238051 = 357077) B357077
theorem B238067 : Blo 235815 238067 := bstep (se 1 (by rfl) ⟨178550, by rfl⟩ : syracuseStep 238067 = 357101) B357101
theorem B238083 : Blo 235815 238083 := bstep (se 1 (by rfl) ⟨178562, by rfl⟩ : syracuseStep 238083 = 357125) B357125
theorem B238099 : Blo 235815 238099 := bstep (se 1 (by rfl) ⟨178574, by rfl⟩ : syracuseStep 238099 = 357149) B357149
theorem B238115 : Blo 235815 238115 := bstep (se 1 (by rfl) ⟨178586, by rfl⟩ : syracuseStep 238115 = 357173) B357173
theorem B401969 : Blo 235815 401969 := bstep (se 2 (by rfl) ⟨150738, by rfl⟩ : syracuseStep 401969 = 301477) B301477
theorem B238131 : Blo 235815 238131 := bstep (se 1 (by rfl) ⟨178598, by rfl⟩ : syracuseStep 238131 = 357197) B357197
theorem B238147 : Blo 235815 238147 := bstep (se 1 (by rfl) ⟨178610, by rfl⟩ : syracuseStep 238147 = 357221) B357221
theorem B238163 : Blo 235815 238163 := bstep (se 1 (by rfl) ⟨178622, by rfl⟩ : syracuseStep 238163 = 357245) B357245
theorem B238179 : Blo 235815 238179 := bstep (se 1 (by rfl) ⟨178634, by rfl⟩ : syracuseStep 238179 = 357269) B357269
theorem B533105 : Blo 235815 533105 := bstep (se 2 (by rfl) ⟨199914, by rfl⟩ : syracuseStep 533105 = 399829) B399829
theorem B238195 : Blo 235815 238195 := bstep (se 1 (by rfl) ⟨178646, by rfl⟩ : syracuseStep 238195 = 357293) B357293
theorem B533123 : Blo 235815 533123 := bstep (se 1 (by rfl) ⟨399842, by rfl⟩ : syracuseStep 533123 = 799685) B799685
theorem B238211 : Blo 235815 238211 := bstep (se 1 (by rfl) ⟨178658, by rfl⟩ : syracuseStep 238211 = 357317) B357317
theorem B860813 : Blo 235815 860813 := bstep (se 3 (by rfl) ⟨161402, by rfl⟩ : syracuseStep 860813 = 322805) B322805
theorem B238227 : Blo 235815 238227 := bstep (se 1 (by rfl) ⟨178670, by rfl⟩ : syracuseStep 238227 = 357341) B357341
theorem B598691 : Blo 235815 598691 := bstep (se 1 (by rfl) ⟨449018, by rfl⟩ : syracuseStep 598691 = 898037) B898037
theorem B238243 : Blo 235815 238243 := bstep (se 1 (by rfl) ⟨178682, by rfl⟩ : syracuseStep 238243 = 357365) B357365
theorem B402097 : Blo 235815 402097 := bstep (se 2 (by rfl) ⟨150786, by rfl⟩ : syracuseStep 402097 = 301573) B301573
theorem B238259 : Blo 235815 238259 := bstep (se 1 (by rfl) ⟨178694, by rfl⟩ : syracuseStep 238259 = 357389) B357389
theorem B238275 : Blo 235815 238275 := bstep (se 1 (by rfl) ⟨178706, by rfl⟩ : syracuseStep 238275 = 357413) B357413
theorem B336593 : Blo 235815 336593 := bstep (se 2 (by rfl) ⟨126222, by rfl⟩ : syracuseStep 336593 = 252445) B252445
theorem B238291 : Blo 235815 238291 := bstep (se 1 (by rfl) ⟨178718, by rfl⟩ : syracuseStep 238291 = 357437) B357437
theorem B402131 : Blo 235815 402131 := bstep (se 1 (by rfl) ⟨301598, by rfl⟩ : syracuseStep 402131 = 603197) B603197
theorem B1516259 : Blo 235815 1516259 := bstep (se 1 (by rfl) ⟨1137194, by rfl⟩ : syracuseStep 1516259 = 2274389) B2274389
theorem B238307 : Blo 235815 238307 := bstep (se 1 (by rfl) ⟨178730, by rfl⟩ : syracuseStep 238307 = 357461) B357461
theorem B238323 : Blo 235815 238323 := bstep (se 1 (by rfl) ⟨178742, by rfl⟩ : syracuseStep 238323 = 357485) B357485
theorem B238339 : Blo 235815 238339 := bstep (se 1 (by rfl) ⟨178754, by rfl⟩ : syracuseStep 238339 = 357509) B357509
theorem B762641 : Blo 235815 762641 := bstep (se 2 (by rfl) ⟨285990, by rfl⟩ : syracuseStep 762641 = 571981) B571981
theorem B238355 : Blo 235815 238355 := bstep (se 1 (by rfl) ⟨178766, by rfl⟩ : syracuseStep 238355 = 357533) B357533
theorem B336673 : Blo 235815 336673 := bstep (se 2 (by rfl) ⟨126252, by rfl⟩ : syracuseStep 336673 = 252505) B252505
theorem B238371 : Blo 235815 238371 := bstep (se 1 (by rfl) ⟨178778, by rfl⟩ : syracuseStep 238371 = 357557) B357557
theorem B238387 : Blo 235815 238387 := bstep (se 1 (by rfl) ⟨178790, by rfl⟩ : syracuseStep 238387 = 357581) B357581
theorem B238403 : Blo 235815 238403 := bstep (se 1 (by rfl) ⟨178802, by rfl⟩ : syracuseStep 238403 = 357605) B357605
theorem B402259 : Blo 235815 402259 := bstep (se 1 (by rfl) ⟨301694, by rfl⟩ : syracuseStep 402259 = 603389) B603389
theorem B238419 : Blo 235815 238419 := bstep (se 1 (by rfl) ⟨178814, by rfl⟩ : syracuseStep 238419 = 357629) B357629
theorem B238435 : Blo 235815 238435 := bstep (se 1 (by rfl) ⟨178826, by rfl⟩ : syracuseStep 238435 = 357653) B357653
theorem B238451 : Blo 235815 238451 := bstep (se 1 (by rfl) ⟨178838, by rfl⟩ : syracuseStep 238451 = 357677) B357677
theorem B238467 : Blo 235815 238467 := bstep (se 1 (by rfl) ⟨178850, by rfl⟩ : syracuseStep 238467 = 357701) B357701
theorem B533393 : Blo 235815 533393 := bstep (se 2 (by rfl) ⟨200022, by rfl⟩ : syracuseStep 533393 = 400045) B400045
theorem B238483 : Blo 235815 238483 := bstep (se 1 (by rfl) ⟨178862, by rfl⟩ : syracuseStep 238483 = 357725) B357725
theorem B533411 : Blo 235815 533411 := bstep (se 1 (by rfl) ⟨400058, by rfl⟩ : syracuseStep 533411 = 800117) B800117
theorem B238499 : Blo 235815 238499 := bstep (se 1 (by rfl) ⟨178874, by rfl⟩ : syracuseStep 238499 = 357749) B357749
theorem B238515 : Blo 235815 238515 := bstep (se 1 (by rfl) ⟨178886, by rfl⟩ : syracuseStep 238515 = 357773) B357773
theorem B238531 : Blo 235815 238531 := bstep (se 1 (by rfl) ⟨178898, by rfl⟩ : syracuseStep 238531 = 357797) B357797
theorem B238547 : Blo 235815 238547 := bstep (se 1 (by rfl) ⟨178910, by rfl⟩ : syracuseStep 238547 = 357821) B357821
theorem B402401 : Blo 235815 402401 := bstep (se 2 (by rfl) ⟨150900, by rfl⟩ : syracuseStep 402401 = 301801) B301801
theorem B238563 : Blo 235815 238563 := bstep (se 1 (by rfl) ⟨178922, by rfl⟩ : syracuseStep 238563 = 357845) B357845
theorem B238579 : Blo 235815 238579 := bstep (se 1 (by rfl) ⟨178934, by rfl⟩ : syracuseStep 238579 = 357869) B357869
theorem B238595 : Blo 235815 238595 := bstep (se 1 (by rfl) ⟨178946, by rfl⟩ : syracuseStep 238595 = 357893) B357893
theorem B238611 : Blo 235815 238611 := bstep (se 1 (by rfl) ⟨178958, by rfl⟩ : syracuseStep 238611 = 357917) B357917
theorem B238627 : Blo 235815 238627 := bstep (se 1 (by rfl) ⟨178970, by rfl⟩ : syracuseStep 238627 = 357941) B357941
theorem B238643 : Blo 235815 238643 := bstep (se 1 (by rfl) ⟨178982, by rfl⟩ : syracuseStep 238643 = 357965) B357965
theorem B238659 : Blo 235815 238659 := bstep (se 1 (by rfl) ⟨178994, by rfl⟩ : syracuseStep 238659 = 357989) B357989
theorem B238675 : Blo 235815 238675 := bstep (se 1 (by rfl) ⟨179006, by rfl⟩ : syracuseStep 238675 = 358013) B358013
theorem B402529 : Blo 235815 402529 := bstep (se 2 (by rfl) ⟨150948, by rfl⟩ : syracuseStep 402529 = 301897) B301897
theorem B271459 : Blo 235815 271459 := bstep (se 1 (by rfl) ⟨203594, by rfl⟩ : syracuseStep 271459 = 407189) B407189
theorem B238691 : Blo 235815 238691 := bstep (se 1 (by rfl) ⟨179018, by rfl⟩ : syracuseStep 238691 = 358037) B358037
theorem B238707 : Blo 235815 238707 := bstep (se 1 (by rfl) ⟨179030, by rfl⟩ : syracuseStep 238707 = 358061) B358061
theorem B402563 : Blo 235815 402563 := bstep (se 1 (by rfl) ⟨301922, by rfl⟩ : syracuseStep 402563 = 603845) B603845
theorem B238723 : Blo 235815 238723 := bstep (se 1 (by rfl) ⟨179042, by rfl⟩ : syracuseStep 238723 = 358085) B358085
theorem B238739 : Blo 235815 238739 := bstep (se 1 (by rfl) ⟨179054, by rfl⟩ : syracuseStep 238739 = 358109) B358109
theorem B238755 : Blo 235815 238755 := bstep (se 1 (by rfl) ⟨179066, by rfl⟩ : syracuseStep 238755 = 358133) B358133
theorem B533681 : Blo 235815 533681 := bstep (se 2 (by rfl) ⟨200130, by rfl⟩ : syracuseStep 533681 = 400261) B400261
theorem B238771 : Blo 235815 238771 := bstep (se 1 (by rfl) ⟨179078, by rfl⟩ : syracuseStep 238771 = 358157) B358157
theorem B533699 : Blo 235815 533699 := bstep (se 1 (by rfl) ⟨400274, by rfl⟩ : syracuseStep 533699 = 800549) B800549
theorem B238787 : Blo 235815 238787 := bstep (se 1 (by rfl) ⟨179090, by rfl⟩ : syracuseStep 238787 = 358181) B358181
theorem B238803 : Blo 235815 238803 := bstep (se 1 (by rfl) ⟨179102, by rfl⟩ : syracuseStep 238803 = 358205) B358205
theorem B238819 : Blo 235815 238819 := bstep (se 1 (by rfl) ⟨179114, by rfl⟩ : syracuseStep 238819 = 358229) B358229
theorem B238835 : Blo 235815 238835 := bstep (se 1 (by rfl) ⟨179126, by rfl⟩ : syracuseStep 238835 = 358253) B358253
theorem B402691 : Blo 235815 402691 := bstep (se 1 (by rfl) ⟨302018, by rfl⟩ : syracuseStep 402691 = 604037) B604037
theorem B238851 : Blo 235815 238851 := bstep (se 1 (by rfl) ⟨179138, by rfl⟩ : syracuseStep 238851 = 358277) B358277
theorem B238867 : Blo 235815 238867 := bstep (se 1 (by rfl) ⟨179150, by rfl⟩ : syracuseStep 238867 = 358301) B358301
theorem B238883 : Blo 235815 238883 := bstep (se 1 (by rfl) ⟨179162, by rfl⟩ : syracuseStep 238883 = 358325) B358325
theorem B238899 : Blo 235815 238899 := bstep (se 1 (by rfl) ⟨179174, by rfl⟩ : syracuseStep 238899 = 358349) B358349
theorem B238915 : Blo 235815 238915 := bstep (se 1 (by rfl) ⟨179186, by rfl⟩ : syracuseStep 238915 = 358373) B358373
theorem B238931 : Blo 235815 238931 := bstep (se 1 (by rfl) ⟨179198, by rfl⟩ : syracuseStep 238931 = 358397) B358397
theorem B238947 : Blo 235815 238947 := bstep (se 1 (by rfl) ⟨179210, by rfl⟩ : syracuseStep 238947 = 358421) B358421
theorem B796013 : Blo 235815 796013 := bstep (se 3 (by rfl) ⟨149252, by rfl⟩ : syracuseStep 796013 = 298505) B298505
theorem B238963 : Blo 235815 238963 := bstep (se 1 (by rfl) ⟨179222, by rfl⟩ : syracuseStep 238963 = 358445) B358445
theorem B238979 : Blo 235815 238979 := bstep (se 1 (by rfl) ⟨179234, by rfl⟩ : syracuseStep 238979 = 358469) B358469
theorem B402833 : Blo 235815 402833 := bstep (se 2 (by rfl) ⟨151062, by rfl⟩ : syracuseStep 402833 = 302125) B302125
theorem B238995 : Blo 235815 238995 := bstep (se 1 (by rfl) ⟨179246, by rfl⟩ : syracuseStep 238995 = 358493) B358493
theorem B796067 : Blo 235815 796067 := bstep (se 1 (by rfl) ⟨597050, by rfl⟩ : syracuseStep 796067 = 1194101) B1194101
theorem B239011 : Blo 235815 239011 := bstep (se 1 (by rfl) ⟨179258, by rfl⟩ : syracuseStep 239011 = 358517) B358517
theorem B239027 : Blo 235815 239027 := bstep (se 1 (by rfl) ⟨179270, by rfl⟩ : syracuseStep 239027 = 358541) B358541
theorem B239043 : Blo 235815 239043 := bstep (se 1 (by rfl) ⟨179282, by rfl⟩ : syracuseStep 239043 = 358565) B358565
theorem B533969 : Blo 235815 533969 := bstep (se 2 (by rfl) ⟨200238, by rfl⟩ : syracuseStep 533969 = 400477) B400477
theorem B239059 : Blo 235815 239059 := bstep (se 1 (by rfl) ⟨179294, by rfl⟩ : syracuseStep 239059 = 358589) B358589
theorem B533987 : Blo 235815 533987 := bstep (se 1 (by rfl) ⟨400490, by rfl⟩ : syracuseStep 533987 = 800981) B800981
theorem B239075 : Blo 235815 239075 := bstep (se 1 (by rfl) ⟨179306, by rfl⟩ : syracuseStep 239075 = 358613) B358613
theorem B239091 : Blo 235815 239091 := bstep (se 1 (by rfl) ⟨179318, by rfl⟩ : syracuseStep 239091 = 358637) B358637
theorem B239107 : Blo 235815 239107 := bstep (se 1 (by rfl) ⟨179330, by rfl⟩ : syracuseStep 239107 = 358661) B358661
theorem B402961 : Blo 235815 402961 := bstep (se 2 (by rfl) ⟨151110, by rfl⟩ : syracuseStep 402961 = 302221) B302221
theorem B239123 : Blo 235815 239123 := bstep (se 1 (by rfl) ⟨179342, by rfl⟩ : syracuseStep 239123 = 358685) B358685
theorem B239139 : Blo 235815 239139 := bstep (se 1 (by rfl) ⟨179354, by rfl⟩ : syracuseStep 239139 = 358709) B358709
theorem B337459 : Blo 235815 337459 := bstep (se 1 (by rfl) ⟨253094, by rfl⟩ : syracuseStep 337459 = 506189) B506189
theorem B402995 : Blo 235815 402995 := bstep (se 1 (by rfl) ⟨302246, by rfl⟩ : syracuseStep 402995 = 604493) B604493
theorem B239155 : Blo 235815 239155 := bstep (se 1 (by rfl) ⟨179366, by rfl⟩ : syracuseStep 239155 = 358733) B358733
theorem B239171 : Blo 235815 239171 := bstep (se 1 (by rfl) ⟨179378, by rfl⟩ : syracuseStep 239171 = 358757) B358757
theorem B599633 : Blo 235815 599633 := bstep (se 2 (by rfl) ⟨224862, by rfl⟩ : syracuseStep 599633 = 449725) B449725
theorem B239187 : Blo 235815 239187 := bstep (se 1 (by rfl) ⟨179390, by rfl⟩ : syracuseStep 239187 = 358781) B358781
theorem B239203 : Blo 235815 239203 := bstep (se 1 (by rfl) ⟨179402, by rfl⟩ : syracuseStep 239203 = 358805) B358805
theorem B239219 : Blo 235815 239219 := bstep (se 1 (by rfl) ⟨179414, by rfl⟩ : syracuseStep 239219 = 358829) B358829
theorem B599683 : Blo 235815 599683 := bstep (se 1 (by rfl) ⟨449762, by rfl⟩ : syracuseStep 599683 = 899525) B899525
theorem B239235 : Blo 235815 239235 := bstep (se 1 (by rfl) ⟨179426, by rfl⟩ : syracuseStep 239235 = 358853) B358853
theorem B239251 : Blo 235815 239251 := bstep (se 1 (by rfl) ⟨179438, by rfl⟩ : syracuseStep 239251 = 358877) B358877
theorem B239267 : Blo 235815 239267 := bstep (se 1 (by rfl) ⟨179450, by rfl⟩ : syracuseStep 239267 = 358901) B358901
theorem B796337 : Blo 235815 796337 := bstep (se 2 (by rfl) ⟨298626, by rfl⟩ : syracuseStep 796337 = 597253) B597253
theorem B403123 : Blo 235815 403123 := bstep (se 1 (by rfl) ⟨302342, by rfl⟩ : syracuseStep 403123 = 604685) B604685
theorem B239283 : Blo 235815 239283 := bstep (se 1 (by rfl) ⟨179462, by rfl⟩ : syracuseStep 239283 = 358925) B358925
theorem B239299 : Blo 235815 239299 := bstep (se 1 (by rfl) ⟨179474, by rfl⟩ : syracuseStep 239299 = 358949) B358949
theorem B239315 : Blo 235815 239315 := bstep (se 1 (by rfl) ⟨179486, by rfl⟩ : syracuseStep 239315 = 358973) B358973
theorem B239331 : Blo 235815 239331 := bstep (se 1 (by rfl) ⟨179498, by rfl⟩ : syracuseStep 239331 = 358997) B358997
theorem B534257 : Blo 235815 534257 := bstep (se 2 (by rfl) ⟨200346, by rfl⟩ : syracuseStep 534257 = 400693) B400693
theorem B239347 : Blo 235815 239347 := bstep (se 1 (by rfl) ⟨179510, by rfl⟩ : syracuseStep 239347 = 359021) B359021
theorem B534275 : Blo 235815 534275 := bstep (se 1 (by rfl) ⟨400706, by rfl⟩ : syracuseStep 534275 = 801413) B801413
theorem B239363 : Blo 235815 239363 := bstep (se 1 (by rfl) ⟨179522, by rfl⟩ : syracuseStep 239363 = 359045) B359045
theorem B599825 : Blo 235815 599825 := bstep (se 2 (by rfl) ⟨224934, by rfl⟩ : syracuseStep 599825 = 449869) B449869
theorem B239379 : Blo 235815 239379 := bstep (se 1 (by rfl) ⟨179534, by rfl⟩ : syracuseStep 239379 = 359069) B359069
theorem B239395 : Blo 235815 239395 := bstep (se 1 (by rfl) ⟨179546, by rfl⟩ : syracuseStep 239395 = 359093) B359093
theorem B239411 : Blo 235815 239411 := bstep (se 1 (by rfl) ⟨179558, by rfl⟩ : syracuseStep 239411 = 359117) B359117
theorem B403265 : Blo 235815 403265 := bstep (se 2 (by rfl) ⟨151224, by rfl⟩ : syracuseStep 403265 = 302449) B302449
theorem B239427 : Blo 235815 239427 := bstep (se 1 (by rfl) ⟨179570, by rfl⟩ : syracuseStep 239427 = 359141) B359141
theorem B1812293 : Blo 235815 1812293 := bstep (se 4 (by rfl) ⟨169902, by rfl⟩ : syracuseStep 1812293 = 339805) B339805
theorem B239443 : Blo 235815 239443 := bstep (se 1 (by rfl) ⟨179582, by rfl⟩ : syracuseStep 239443 = 359165) B359165
theorem B239459 : Blo 235815 239459 := bstep (se 1 (by rfl) ⟨179594, by rfl⟩ : syracuseStep 239459 = 359189) B359189
theorem B239475 : Blo 235815 239475 := bstep (se 1 (by rfl) ⟨179606, by rfl⟩ : syracuseStep 239475 = 359213) B359213
theorem B239491 : Blo 235815 239491 := bstep (se 1 (by rfl) ⟨179618, by rfl⟩ : syracuseStep 239491 = 359237) B359237
theorem B239507 : Blo 235815 239507 := bstep (se 1 (by rfl) ⟨179630, by rfl⟩ : syracuseStep 239507 = 359261) B359261
theorem B239523 : Blo 235815 239523 := bstep (se 1 (by rfl) ⟨179642, by rfl⟩ : syracuseStep 239523 = 359285) B359285
theorem B239539 : Blo 235815 239539 := bstep (se 1 (by rfl) ⟨179654, by rfl⟩ : syracuseStep 239539 = 359309) B359309
theorem B403393 : Blo 235815 403393 := bstep (se 2 (by rfl) ⟨151272, by rfl⟩ : syracuseStep 403393 = 302545) B302545
theorem B239555 : Blo 235815 239555 := bstep (se 1 (by rfl) ⟨179666, by rfl⟩ : syracuseStep 239555 = 359333) B359333
theorem B11610053 : Blo 235815 11610053 := bstep (se 4 (by rfl) ⟨1088442, by rfl⟩ : syracuseStep 11610053 = 2176885) B2176885
theorem B239571 : Blo 235815 239571 := bstep (se 1 (by rfl) ⟨179678, by rfl⟩ : syracuseStep 239571 = 359357) B359357
theorem B403427 : Blo 235815 403427 := bstep (se 1 (by rfl) ⟨302570, by rfl⟩ : syracuseStep 403427 = 605141) B605141
theorem B239587 : Blo 235815 239587 := bstep (se 1 (by rfl) ⟨179690, by rfl⟩ : syracuseStep 239587 = 359381) B359381
theorem B239603 : Blo 235815 239603 := bstep (se 1 (by rfl) ⟨179702, by rfl⟩ : syracuseStep 239603 = 359405) B359405
theorem B239619 : Blo 235815 239619 := bstep (se 1 (by rfl) ⟨179714, by rfl⟩ : syracuseStep 239619 = 359429) B359429
theorem B337937 : Blo 235815 337937 := bstep (se 2 (by rfl) ⟨126726, by rfl⟩ : syracuseStep 337937 = 253453) B253453
theorem B534545 : Blo 235815 534545 := bstep (se 2 (by rfl) ⟨200454, by rfl⟩ : syracuseStep 534545 = 400909) B400909
theorem B239635 : Blo 235815 239635 := bstep (se 1 (by rfl) ⟨179726, by rfl⟩ : syracuseStep 239635 = 359453) B359453
theorem B534563 : Blo 235815 534563 := bstep (se 1 (by rfl) ⟨400922, by rfl⟩ : syracuseStep 534563 = 801845) B801845
theorem B239651 : Blo 235815 239651 := bstep (se 1 (by rfl) ⟨179738, by rfl⟩ : syracuseStep 239651 = 359477) B359477
theorem B239667 : Blo 235815 239667 := bstep (se 1 (by rfl) ⟨179750, by rfl⟩ : syracuseStep 239667 = 359501) B359501
theorem B239683 : Blo 235815 239683 := bstep (se 1 (by rfl) ⟨179762, by rfl⟩ : syracuseStep 239683 = 359525) B359525
theorem B239699 : Blo 235815 239699 := bstep (se 1 (by rfl) ⟨179774, by rfl⟩ : syracuseStep 239699 = 359549) B359549
theorem B403555 : Blo 235815 403555 := bstep (se 1 (by rfl) ⟨302666, by rfl⟩ : syracuseStep 403555 = 605333) B605333
theorem B239715 : Blo 235815 239715 := bstep (se 1 (by rfl) ⟨179786, by rfl⟩ : syracuseStep 239715 = 359573) B359573
theorem B239731 : Blo 235815 239731 := bstep (se 1 (by rfl) ⟨179798, by rfl⟩ : syracuseStep 239731 = 359597) B359597
theorem B338051 : Blo 235815 338051 := bstep (se 1 (by rfl) ⟨253538, by rfl⟩ : syracuseStep 338051 = 507077) B507077
theorem B239747 : Blo 235815 239747 := bstep (se 1 (by rfl) ⟨179810, by rfl⟩ : syracuseStep 239747 = 359621) B359621
theorem B5187725 : Blo 235815 5187725 := bstep (se 3 (by rfl) ⟨972698, by rfl⟩ : syracuseStep 5187725 = 1945397) B1945397
theorem B239763 : Blo 235815 239763 := bstep (se 1 (by rfl) ⟨179822, by rfl⟩ : syracuseStep 239763 = 359645) B359645
theorem B239779 : Blo 235815 239779 := bstep (se 1 (by rfl) ⟨179834, by rfl⟩ : syracuseStep 239779 = 359669) B359669
theorem B239795 : Blo 235815 239795 := bstep (se 1 (by rfl) ⟨179846, by rfl⟩ : syracuseStep 239795 = 359693) B359693
theorem B239811 : Blo 235815 239811 := bstep (se 1 (by rfl) ⟨179858, by rfl⟩ : syracuseStep 239811 = 359717) B359717
theorem B796877 : Blo 235815 796877 := bstep (se 3 (by rfl) ⟨149414, by rfl⟩ : syracuseStep 796877 = 298829) B298829
theorem B338131 : Blo 235815 338131 := bstep (se 1 (by rfl) ⟨253598, by rfl⟩ : syracuseStep 338131 = 507197) B507197
theorem B403697 : Blo 235815 403697 := bstep (se 2 (by rfl) ⟨151386, by rfl⟩ : syracuseStep 403697 = 302773) B302773
theorem B796931 : Blo 235815 796931 := bstep (se 1 (by rfl) ⟨597698, by rfl⟩ : syracuseStep 796931 = 1195397) B1195397
theorem B534833 : Blo 235815 534833 := bstep (se 2 (by rfl) ⟨200562, by rfl⟩ : syracuseStep 534833 = 401125) B401125
theorem B534851 : Blo 235815 534851 := bstep (se 1 (by rfl) ⟨401138, by rfl⟩ : syracuseStep 534851 = 802277) B802277
theorem B403825 : Blo 235815 403825 := bstep (se 2 (by rfl) ⟨151434, by rfl⟩ : syracuseStep 403825 = 302869) B302869
theorem B1354117 : Blo 235815 1354117 := bstep (se 4 (by rfl) ⟨126948, by rfl⟩ : syracuseStep 1354117 = 253897) B253897
theorem B403859 : Blo 235815 403859 := bstep (se 1 (by rfl) ⟨302894, by rfl⟩ : syracuseStep 403859 = 605789) B605789
theorem B862669 : Blo 235815 862669 := bstep (se 3 (by rfl) ⟨161750, by rfl⟩ : syracuseStep 862669 = 323501) B323501
theorem B797201 : Blo 235815 797201 := bstep (se 2 (by rfl) ⟨298950, by rfl⟩ : syracuseStep 797201 = 597901) B597901
theorem B403987 : Blo 235815 403987 := bstep (se 1 (by rfl) ⟨302990, by rfl⟩ : syracuseStep 403987 = 605981) B605981
theorem B535121 : Blo 235815 535121 := bstep (se 2 (by rfl) ⟨200670, by rfl⟩ : syracuseStep 535121 = 401341) B401341
theorem B535139 : Blo 235815 535139 := bstep (se 1 (by rfl) ⟨401354, by rfl⟩ : syracuseStep 535139 = 802709) B802709
theorem B1288817 : Blo 235815 1288817 := bstep (se 2 (by rfl) ⟨483306, by rfl⟩ : syracuseStep 1288817 = 966613) B966613
theorem B404129 : Blo 235815 404129 := bstep (se 2 (by rfl) ⟨151548, by rfl⟩ : syracuseStep 404129 = 303097) B303097
theorem B1518257 : Blo 235815 1518257 := bstep (se 2 (by rfl) ⟨569346, by rfl⟩ : syracuseStep 1518257 = 1138693) B1138693
theorem B764653 : Blo 235815 764653 := bstep (se 3 (by rfl) ⟨143372, by rfl⟩ : syracuseStep 764653 = 286745) B286745
theorem B600817 : Blo 235815 600817 := bstep (se 2 (by rfl) ⟨225306, by rfl⟩ : syracuseStep 600817 = 450613) B450613
theorem B338689 : Blo 235815 338689 := bstep (se 2 (by rfl) ⟨127008, by rfl⟩ : syracuseStep 338689 = 254017) B254017
theorem B404227 : Blo 235815 404227 := bstep (se 1 (by rfl) ⟨303170, by rfl⟩ : syracuseStep 404227 = 606341) B606341
theorem B404257 : Blo 235815 404257 := bstep (se 2 (by rfl) ⟨151596, by rfl⟩ : syracuseStep 404257 = 303193) B303193
theorem B404291 : Blo 235815 404291 := bstep (se 1 (by rfl) ⟨303218, by rfl⟩ : syracuseStep 404291 = 606437) B606437
theorem B863075 : Blo 235815 863075 := bstep (se 1 (by rfl) ⟨647306, by rfl⟩ : syracuseStep 863075 = 1294613) B1294613
theorem B535409 : Blo 235815 535409 := bstep (se 2 (by rfl) ⟨200778, by rfl⟩ : syracuseStep 535409 = 401557) B401557
theorem B535427 : Blo 235815 535427 := bstep (se 1 (by rfl) ⟨401570, by rfl⟩ : syracuseStep 535427 = 803141) B803141
theorem B404419 : Blo 235815 404419 := bstep (se 1 (by rfl) ⟨303314, by rfl⟩ : syracuseStep 404419 = 606629) B606629
theorem B601091 : Blo 235815 601091 := bstep (se 1 (by rfl) ⟨450818, by rfl⟩ : syracuseStep 601091 = 901637) B901637
theorem B797741 : Blo 235815 797741 := bstep (se 3 (by rfl) ⟨149576, by rfl⟩ : syracuseStep 797741 = 299153) B299153
theorem B404561 : Blo 235815 404561 := bstep (se 2 (by rfl) ⟨151710, by rfl⟩ : syracuseStep 404561 = 303421) B303421
theorem B797795 : Blo 235815 797795 := bstep (se 1 (by rfl) ⟨598346, by rfl⟩ : syracuseStep 797795 = 1196693) B1196693
theorem B535697 : Blo 235815 535697 := bstep (se 2 (by rfl) ⟨200886, by rfl⟩ : syracuseStep 535697 = 401773) B401773
theorem B535715 : Blo 235815 535715 := bstep (se 1 (by rfl) ⟨401786, by rfl⟩ : syracuseStep 535715 = 803573) B803573
theorem B765101 : Blo 235815 765101 := bstep (se 3 (by rfl) ⟨143456, by rfl⟩ : syracuseStep 765101 = 286913) B286913
theorem B601283 : Blo 235815 601283 := bstep (se 1 (by rfl) ⟨450962, by rfl⟩ : syracuseStep 601283 = 901925) B901925
theorem B404689 : Blo 235815 404689 := bstep (se 2 (by rfl) ⟨151758, by rfl⟩ : syracuseStep 404689 = 303517) B303517
theorem B896291 : Blo 235815 896291 := bstep (se 1 (by rfl) ⟨672218, by rfl⟩ : syracuseStep 896291 = 1344437) B1344437
theorem B896305 : Blo 235815 896305 := bstep (se 2 (by rfl) ⟨336114, by rfl⟩ : syracuseStep 896305 = 672229) B672229
theorem B798065 : Blo 235815 798065 := bstep (se 2 (by rfl) ⟨299274, by rfl⟩ : syracuseStep 798065 = 598549) B598549
theorem B1027505 : Blo 235815 1027505 := bstep (se 2 (by rfl) ⟨385314, by rfl⟩ : syracuseStep 1027505 = 770629) B770629
theorem B535985 : Blo 235815 535985 := bstep (se 2 (by rfl) ⟨200994, by rfl⟩ : syracuseStep 535985 = 401989) B401989
theorem B536003 : Blo 235815 536003 := bstep (se 1 (by rfl) ⟨402002, by rfl⟩ : syracuseStep 536003 = 804005) B804005
theorem B339395 : Blo 235815 339395 := bstep (se 1 (by rfl) ⟨254546, by rfl⟩ : syracuseStep 339395 = 509093) B509093
theorem B2043377 : Blo 235815 2043377 := bstep (se 2 (by rfl) ⟨766266, by rfl⟩ : syracuseStep 2043377 = 1532533) B1532533
theorem B1519181 : Blo 235815 1519181 := bstep (se 3 (by rfl) ⟨284846, by rfl⟩ : syracuseStep 1519181 = 569693) B569693
theorem B962189 : Blo 235815 962189 := bstep (se 3 (by rfl) ⟨180410, by rfl⟩ : syracuseStep 962189 = 360821) B360821
theorem B405137 : Blo 235815 405137 := bstep (se 2 (by rfl) ⟨151926, by rfl⟩ : syracuseStep 405137 = 303853) B303853
theorem B1224355 : Blo 235815 1224355 := bstep (se 1 (by rfl) ⟨918266, by rfl⟩ : syracuseStep 1224355 = 1836533) B1836533
theorem B536273 : Blo 235815 536273 := bstep (se 2 (by rfl) ⟨201102, by rfl⟩ : syracuseStep 536273 = 402205) B402205
theorem B536291 : Blo 235815 536291 := bstep (se 1 (by rfl) ⟨402218, by rfl⟩ : syracuseStep 536291 = 804437) B804437
theorem B241523 : Blo 235815 241523 := bstep (se 1 (by rfl) ⟨181142, by rfl⟩ : syracuseStep 241523 = 362285) B362285
theorem B798605 : Blo 235815 798605 := bstep (se 3 (by rfl) ⟨149738, by rfl⟩ : syracuseStep 798605 = 299477) B299477
theorem B798659 : Blo 235815 798659 := bstep (se 1 (by rfl) ⟨598994, by rfl⟩ : syracuseStep 798659 = 1197989) B1197989
theorem B536561 : Blo 235815 536561 := bstep (se 2 (by rfl) ⟨201210, by rfl⟩ : syracuseStep 536561 = 402421) B402421
theorem B536579 : Blo 235815 536579 := bstep (se 1 (by rfl) ⟨402434, by rfl⟩ : syracuseStep 536579 = 804869) B804869
theorem B340033 : Blo 235815 340033 := bstep (se 2 (by rfl) ⟨127512, by rfl⟩ : syracuseStep 340033 = 255025) B255025
theorem B602225 : Blo 235815 602225 := bstep (se 2 (by rfl) ⟨225834, by rfl⟩ : syracuseStep 602225 = 451669) B451669
theorem B602275 : Blo 235815 602275 := bstep (se 1 (by rfl) ⟨451706, by rfl⟩ : syracuseStep 602275 = 903413) B903413
theorem B340147 : Blo 235815 340147 := bstep (se 1 (by rfl) ⟨255110, by rfl⟩ : syracuseStep 340147 = 510221) B510221
theorem B569539 : Blo 235815 569539 := bstep (se 1 (by rfl) ⟨427154, by rfl⟩ : syracuseStep 569539 = 854309) B854309
theorem B798929 : Blo 235815 798929 := bstep (se 2 (by rfl) ⟨299598, by rfl⟩ : syracuseStep 798929 = 599197) B599197
theorem B536849 : Blo 235815 536849 := bstep (se 2 (by rfl) ⟨201318, by rfl⟩ : syracuseStep 536849 = 402637) B402637
theorem B536867 : Blo 235815 536867 := bstep (se 1 (by rfl) ⟨402650, by rfl⟩ : syracuseStep 536867 = 805301) B805301
theorem B602417 : Blo 235815 602417 := bstep (se 2 (by rfl) ⟨225906, by rfl⟩ : syracuseStep 602417 = 451813) B451813
theorem B1290545 : Blo 235815 1290545 := bstep (se 2 (by rfl) ⟨483954, by rfl⟩ : syracuseStep 1290545 = 967909) B967909
theorem B1356101 : Blo 235815 1356101 := bstep (se 4 (by rfl) ⟨127134, by rfl⟩ : syracuseStep 1356101 = 254269) B254269
theorem B537137 : Blo 235815 537137 := bstep (se 2 (by rfl) ⟨201426, by rfl⟩ : syracuseStep 537137 = 402853) B402853
theorem B537155 : Blo 235815 537155 := bstep (se 1 (by rfl) ⟨402866, by rfl⟩ : syracuseStep 537155 = 805733) B805733
theorem B897763 : Blo 235815 897763 := bstep (se 1 (by rfl) ⟨673322, by rfl⟩ : syracuseStep 897763 = 1346645) B1346645
theorem B799469 : Blo 235815 799469 := bstep (se 3 (by rfl) ⟨149900, by rfl⟩ : syracuseStep 799469 = 299801) B299801
theorem B799523 : Blo 235815 799523 := bstep (se 1 (by rfl) ⟨599642, by rfl⟩ : syracuseStep 799523 = 1199285) B1199285
theorem B504643 : Blo 235815 504643 := bstep (se 1 (by rfl) ⟨378482, by rfl⟩ : syracuseStep 504643 = 756965) B756965
theorem B537425 : Blo 235815 537425 := bstep (se 2 (by rfl) ⟨201534, by rfl⟩ : syracuseStep 537425 = 403069) B403069
theorem B537443 : Blo 235815 537443 := bstep (se 1 (by rfl) ⟨403082, by rfl⟩ : syracuseStep 537443 = 806165) B806165
theorem B2569157 : Blo 235815 2569157 := bstep (se 4 (by rfl) ⟨240858, by rfl⟩ : syracuseStep 2569157 = 481717) B481717
theorem B799793 : Blo 235815 799793 := bstep (se 2 (by rfl) ⟨299922, by rfl⟩ : syracuseStep 799793 = 599845) B599845
theorem B537713 : Blo 235815 537713 := bstep (se 2 (by rfl) ⟨201642, by rfl⟩ : syracuseStep 537713 = 403285) B403285
theorem B537731 : Blo 235815 537731 := bstep (se 1 (by rfl) ⟨403298, by rfl⟩ : syracuseStep 537731 = 806597) B806597
theorem B570577 : Blo 235815 570577 := bstep (se 2 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 570577 = 427933) B427933
theorem B603409 : Blo 235815 603409 := bstep (se 2 (by rfl) ⟨226278, by rfl⟩ : syracuseStep 603409 = 452557) B452557
theorem B538001 : Blo 235815 538001 := bstep (se 2 (by rfl) ⟨201750, by rfl⟩ : syracuseStep 538001 = 403501) B403501
theorem B538019 : Blo 235815 538019 := bstep (se 1 (by rfl) ⟨403514, by rfl⟩ : syracuseStep 538019 = 807029) B807029
theorem B603683 : Blo 235815 603683 := bstep (se 1 (by rfl) ⟨452762, by rfl⟩ : syracuseStep 603683 = 905525) B905525
theorem B800333 : Blo 235815 800333 := bstep (se 3 (by rfl) ⟨150062, by rfl⟩ : syracuseStep 800333 = 300125) B300125
theorem B800387 : Blo 235815 800387 := bstep (se 1 (by rfl) ⟨600290, by rfl⟩ : syracuseStep 800387 = 1200581) B1200581
theorem B538289 : Blo 235815 538289 := bstep (se 2 (by rfl) ⟨201858, by rfl⟩ : syracuseStep 538289 = 403717) B403717
theorem B538307 : Blo 235815 538307 := bstep (se 1 (by rfl) ⟨403730, by rfl⟩ : syracuseStep 538307 = 807461) B807461
theorem B1717957 : Blo 235815 1717957 := bstep (se 4 (by rfl) ⟨161058, by rfl⟩ : syracuseStep 1717957 = 322117) B322117
theorem B603875 : Blo 235815 603875 := bstep (se 1 (by rfl) ⟨452906, by rfl⟩ : syracuseStep 603875 = 905813) B905813
theorem B27997973 : Blo 235815 27997973 := bstep (se 6 (by rfl) ⟨656202, by rfl⟩ : syracuseStep 27997973 = 1312405) B1312405
theorem B767843 : Blo 235815 767843 := bstep (se 1 (by rfl) ⟨575882, by rfl⟩ : syracuseStep 767843 = 1151765) B1151765
theorem B800657 : Blo 235815 800657 := bstep (se 2 (by rfl) ⟨300246, by rfl⟩ : syracuseStep 800657 = 600493) B600493
theorem B538577 : Blo 235815 538577 := bstep (se 2 (by rfl) ⟨201966, by rfl⟩ : syracuseStep 538577 = 403933) B403933
theorem B538595 : Blo 235815 538595 := bstep (se 1 (by rfl) ⟨403946, by rfl⟩ : syracuseStep 538595 = 807893) B807893
theorem B767971 : Blo 235815 767971 := bstep (se 1 (by rfl) ⟨575978, by rfl⟩ : syracuseStep 767971 = 1151957) B1151957
theorem B1620101 : Blo 235815 1620101 := bstep (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) B303769
theorem B407729 : Blo 235815 407729 := bstep (se 2 (by rfl) ⟨152898, by rfl⟩ : syracuseStep 407729 = 305797) B305797
theorem B1620209 : Blo 235815 1620209 := bstep (se 2 (by rfl) ⟨607578, by rfl⟩ : syracuseStep 1620209 = 1215157) B1215157
theorem B538865 : Blo 235815 538865 := bstep (se 2 (by rfl) ⟨202074, by rfl⟩ : syracuseStep 538865 = 404149) B404149
theorem B538883 : Blo 235815 538883 := bstep (se 1 (by rfl) ⟨404162, by rfl⟩ : syracuseStep 538883 = 808325) B808325
theorem B801197 : Blo 235815 801197 := bstep (se 3 (by rfl) ⟨150224, by rfl⟩ : syracuseStep 801197 = 300449) B300449
theorem B801251 : Blo 235815 801251 := bstep (se 1 (by rfl) ⟨600938, by rfl⟩ : syracuseStep 801251 = 1201877) B1201877
theorem B539153 : Blo 235815 539153 := bstep (se 2 (by rfl) ⟨202182, by rfl⟩ : syracuseStep 539153 = 404365) B404365
theorem B539171 : Blo 235815 539171 := bstep (se 1 (by rfl) ⟨404378, by rfl⟩ : syracuseStep 539171 = 808757) B808757
theorem B506513 : Blo 235815 506513 := bstep (se 2 (by rfl) ⟨189942, by rfl⟩ : syracuseStep 506513 = 379885) B379885
theorem B604817 : Blo 235815 604817 := bstep (se 2 (by rfl) ⟨226806, by rfl⟩ : syracuseStep 604817 = 453613) B453613
theorem B768685 : Blo 235815 768685 := bstep (se 3 (by rfl) ⟨144128, by rfl⟩ : syracuseStep 768685 = 288257) B288257
theorem B604867 : Blo 235815 604867 := bstep (se 1 (by rfl) ⟨453650, by rfl⟩ : syracuseStep 604867 = 907301) B907301
theorem B801521 : Blo 235815 801521 := bstep (se 2 (by rfl) ⟨300570, by rfl⟩ : syracuseStep 801521 = 601141) B601141
theorem B539441 : Blo 235815 539441 := bstep (se 2 (by rfl) ⟨202290, by rfl⟩ : syracuseStep 539441 = 404581) B404581
theorem B539459 : Blo 235815 539459 := bstep (se 1 (by rfl) ⟨404594, by rfl⟩ : syracuseStep 539459 = 809189) B809189
theorem B605009 : Blo 235815 605009 := bstep (se 2 (by rfl) ⟨226878, by rfl⟩ : syracuseStep 605009 = 453757) B453757
theorem B899981 : Blo 235815 899981 := bstep (se 3 (by rfl) ⟨168746, by rfl⟩ : syracuseStep 899981 = 337493) B337493
theorem B1195235 : Blo 235815 1195235 := bstep (se 1 (by rfl) ⟨896426, by rfl⟩ : syracuseStep 1195235 = 1792853) B1792853
theorem B802061 : Blo 235815 802061 := bstep (se 3 (by rfl) ⟨150386, by rfl⟩ : syracuseStep 802061 = 300773) B300773
theorem B802115 : Blo 235815 802115 := bstep (se 1 (by rfl) ⟨601586, by rfl⟩ : syracuseStep 802115 = 1203173) B1203173
theorem B507217 : Blo 235815 507217 := bstep (se 2 (by rfl) ⟨190206, by rfl⟩ : syracuseStep 507217 = 380413) B380413
theorem B2276849 : Blo 235815 2276849 := bstep (se 2 (by rfl) ⟨853818, by rfl⟩ : syracuseStep 2276849 = 1707637) B1707637
theorem B507377 : Blo 235815 507377 := bstep (se 2 (by rfl) ⟨190266, by rfl⟩ : syracuseStep 507377 = 380533) B380533
theorem B1818125 : Blo 235815 1818125 := bstep (se 3 (by rfl) ⟨340898, by rfl⟩ : syracuseStep 1818125 = 681797) B681797
theorem B802385 : Blo 235815 802385 := bstep (se 2 (by rfl) ⟨300894, by rfl⟩ : syracuseStep 802385 = 601789) B601789
theorem B606001 : Blo 235815 606001 := bstep (se 2 (by rfl) ⟨227250, by rfl⟩ : syracuseStep 606001 = 454501) B454501
theorem B2015117 : Blo 235815 2015117 := bstep (se 3 (by rfl) ⟨377834, by rfl⟩ : syracuseStep 2015117 = 755669) B755669
theorem B573443 : Blo 235815 573443 := bstep (se 1 (by rfl) ⟨430082, by rfl⟩ : syracuseStep 573443 = 860165) B860165
theorem B1196045 : Blo 235815 1196045 := bstep (se 3 (by rfl) ⟨224258, by rfl⟩ : syracuseStep 1196045 = 448517) B448517
theorem B606275 : Blo 235815 606275 := bstep (se 1 (by rfl) ⟨454706, by rfl⟩ : syracuseStep 606275 = 909413) B909413
theorem B1359949 : Blo 235815 1359949 := bstep (se 3 (by rfl) ⟨254990, by rfl⟩ : syracuseStep 1359949 = 509981) B509981
theorem B802925 : Blo 235815 802925 := bstep (se 3 (by rfl) ⟨150548, by rfl⟩ : syracuseStep 802925 = 301097) B301097
theorem B802979 : Blo 235815 802979 := bstep (se 1 (by rfl) ⟨602234, by rfl⟩ : syracuseStep 802979 = 1204469) B1204469
theorem B606467 : Blo 235815 606467 := bstep (se 1 (by rfl) ⟨454850, by rfl⟩ : syracuseStep 606467 = 909701) B909701
theorem B803249 : Blo 235815 803249 := bstep (se 2 (by rfl) ⟨301218, by rfl⟩ : syracuseStep 803249 = 602437) B602437
theorem B2048611 : Blo 235815 2048611 := bstep (se 1 (by rfl) ⟨1536458, by rfl⟩ : syracuseStep 2048611 = 3072917) B3072917
theorem B672401 : Blo 235815 672401 := bstep (se 2 (by rfl) ⟨252150, by rfl⟩ : syracuseStep 672401 = 504301) B504301
theorem B508675 : Blo 235815 508675 := bstep (se 1 (by rfl) ⟨381506, by rfl⟩ : syracuseStep 508675 = 763013) B763013
theorem B803789 : Blo 235815 803789 := bstep (se 3 (by rfl) ⟨150710, by rfl⟩ : syracuseStep 803789 = 301421) B301421
theorem B345043 : Blo 235815 345043 := bstep (se 1 (by rfl) ⟨258782, by rfl⟩ : syracuseStep 345043 = 517565) B517565
theorem B803843 : Blo 235815 803843 := bstep (se 1 (by rfl) ⟨602882, by rfl⟩ : syracuseStep 803843 = 1205765) B1205765
theorem B377873 : Blo 235815 377873 := bstep (se 2 (by rfl) ⟨141702, by rfl⟩ : syracuseStep 377873 = 283405) B283405
theorem B2802869 : Blo 235815 2802869 := bstep (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) B262769
theorem B804113 : Blo 235815 804113 := bstep (se 2 (by rfl) ⟨301542, by rfl⟩ : syracuseStep 804113 = 603085) B603085
theorem B673073 : Blo 235815 673073 := bstep (se 2 (by rfl) ⟨252402, by rfl⟩ : syracuseStep 673073 = 504805) B504805
theorem B542033 : Blo 235815 542033 := bstep (se 2 (by rfl) ⟨203262, by rfl⟩ : syracuseStep 542033 = 406525) B406525
theorem B575075 : Blo 235815 575075 := bstep (se 1 (by rfl) ⟨431306, by rfl⟩ : syracuseStep 575075 = 862613) B862613
theorem B902897 : Blo 235815 902897 := bstep (se 2 (by rfl) ⟨338586, by rfl⟩ : syracuseStep 902897 = 677173) B677173
theorem B804653 : Blo 235815 804653 := bstep (se 3 (by rfl) ⟨150872, by rfl⟩ : syracuseStep 804653 = 301745) B301745
theorem B804707 : Blo 235815 804707 := bstep (se 1 (by rfl) ⟨603530, by rfl⟩ : syracuseStep 804707 = 1207061) B1207061
theorem B346051 : Blo 235815 346051 := bstep (se 1 (by rfl) ⟨259538, by rfl⟩ : syracuseStep 346051 = 519077) B519077
theorem B509905 : Blo 235815 509905 := bstep (se 2 (by rfl) ⟨191214, by rfl⟩ : syracuseStep 509905 = 382429) B382429
theorem B1361933 : Blo 235815 1361933 := bstep (se 3 (by rfl) ⟨255362, by rfl⟩ : syracuseStep 1361933 = 510725) B510725
theorem B673859 : Blo 235815 673859 := bstep (se 1 (by rfl) ⟨505394, by rfl⟩ : syracuseStep 673859 = 1010789) B1010789
theorem B804977 : Blo 235815 804977 := bstep (se 2 (by rfl) ⟨301866, by rfl⟩ : syracuseStep 804977 = 603733) B603733
theorem B2017507 : Blo 235815 2017507 := bstep (se 1 (by rfl) ⟨1513130, by rfl⟩ : syracuseStep 2017507 = 3026261) B3026261
theorem B1821041 : Blo 235815 1821041 := bstep (se 2 (by rfl) ⟨682890, by rfl⟩ : syracuseStep 1821041 = 1365781) B1365781
theorem B674189 : Blo 235815 674189 := bstep (se 3 (by rfl) ⟨126410, by rfl⟩ : syracuseStep 674189 = 252821) B252821
theorem B674257 : Blo 235815 674257 := bstep (se 2 (by rfl) ⟨252846, by rfl⟩ : syracuseStep 674257 = 505693) B505693
theorem B608771 : Blo 235815 608771 := bstep (se 1 (by rfl) ⟨456578, by rfl⟩ : syracuseStep 608771 = 913157) B913157
theorem B510563 : Blo 235815 510563 := bstep (se 1 (by rfl) ⟨382922, by rfl⟩ : syracuseStep 510563 = 765845) B765845
theorem B805517 : Blo 235815 805517 := bstep (se 3 (by rfl) ⟨151034, by rfl⟩ : syracuseStep 805517 = 302069) B302069
theorem B1526435 : Blo 235815 1526435 := bstep (se 1 (by rfl) ⟨1144826, by rfl⟩ : syracuseStep 1526435 = 2289653) B2289653
theorem B805571 : Blo 235815 805571 := bstep (se 1 (by rfl) ⟨604178, by rfl⟩ : syracuseStep 805571 = 1208357) B1208357
theorem B674531 : Blo 235815 674531 := bstep (se 1 (by rfl) ⟨505898, by rfl⟩ : syracuseStep 674531 = 1011797) B1011797
theorem B379667 : Blo 235815 379667 := bstep (se 1 (by rfl) ⟨284750, by rfl⟩ : syracuseStep 379667 = 569501) B569501
theorem B609059 : Blo 235815 609059 := bstep (se 1 (by rfl) ⟨456794, by rfl⟩ : syracuseStep 609059 = 913589) B913589
theorem B5327669 : Blo 235815 5327669 := bstep (se 5 (by rfl) ⟨249734, by rfl⟩ : syracuseStep 5327669 = 499469) B499469
theorem B1198961 : Blo 235815 1198961 := bstep (se 2 (by rfl) ⟨449610, by rfl⟩ : syracuseStep 1198961 = 899221) B899221
theorem B1362865 : Blo 235815 1362865 := bstep (se 2 (by rfl) ⟨511074, by rfl⟩ : syracuseStep 1362865 = 1022149) B1022149
theorem B805841 : Blo 235815 805841 := bstep (se 2 (by rfl) ⟨302190, by rfl⟩ : syracuseStep 805841 = 604381) B604381
theorem B904355 : Blo 235815 904355 := bstep (se 1 (by rfl) ⟨678266, by rfl⟩ : syracuseStep 904355 = 1356533) B1356533
theorem B511409 : Blo 235815 511409 := bstep (se 2 (by rfl) ⟨191778, by rfl⟩ : syracuseStep 511409 = 383557) B383557
theorem B806381 : Blo 235815 806381 := bstep (se 3 (by rfl) ⟨151196, by rfl⟩ : syracuseStep 806381 = 302393) B302393
theorem B413203 : Blo 235815 413203 := bstep (se 1 (by rfl) ⟨309902, by rfl⟩ : syracuseStep 413203 = 619805) B619805
theorem B806435 : Blo 235815 806435 := bstep (se 1 (by rfl) ⟨604826, by rfl⟩ : syracuseStep 806435 = 1209653) B1209653
theorem B675373 : Blo 235815 675373 := bstep (se 3 (by rfl) ⟨126632, by rfl⟩ : syracuseStep 675373 = 253265) B253265
theorem B1134157 : Blo 235815 1134157 := bstep (se 3 (by rfl) ⟨212654, by rfl⟩ : syracuseStep 1134157 = 425309) B425309
theorem B380513 : Blo 235815 380513 := bstep (se 2 (by rfl) ⟨142692, by rfl⟩ : syracuseStep 380513 = 285385) B285385
theorem B675533 : Blo 235815 675533 := bstep (se 3 (by rfl) ⟨126662, by rfl⟩ : syracuseStep 675533 = 253325) B253325
theorem B380641 : Blo 235815 380641 := bstep (se 2 (by rfl) ⟨142740, by rfl⟩ : syracuseStep 380641 = 285481) B285481
theorem B380705 : Blo 235815 380705 := bstep (se 2 (by rfl) ⟨142764, by rfl⟩ : syracuseStep 380705 = 285529) B285529
theorem B806705 : Blo 235815 806705 := bstep (se 2 (by rfl) ⟨302514, by rfl⟩ : syracuseStep 806705 = 605029) B605029
theorem B675715 : Blo 235815 675715 := bstep (se 1 (by rfl) ⟨506786, by rfl⟩ : syracuseStep 675715 = 1013573) B1013573
theorem B774193 : Blo 235815 774193 := bstep (se 2 (by rfl) ⟨290322, by rfl⟩ : syracuseStep 774193 = 580645) B580645
theorem B905357 : Blo 235815 905357 := bstep (se 3 (by rfl) ⟨169754, by rfl⟩ : syracuseStep 905357 = 339509) B339509
theorem B1200419 : Blo 235815 1200419 := bstep (se 1 (by rfl) ⟨900314, by rfl⟩ : syracuseStep 1200419 = 1800629) B1800629
theorem B807245 : Blo 235815 807245 := bstep (se 3 (by rfl) ⟨151358, by rfl⟩ : syracuseStep 807245 = 302717) B302717
theorem B1364323 : Blo 235815 1364323 := bstep (se 1 (by rfl) ⟨1023242, by rfl⟩ : syracuseStep 1364323 = 2046485) B2046485
theorem B807299 : Blo 235815 807299 := bstep (se 1 (by rfl) ⟨605474, by rfl⟩ : syracuseStep 807299 = 1210949) B1210949
theorem B1167949 : Blo 235815 1167949 := bstep (se 3 (by rfl) ⟨218990, by rfl⟩ : syracuseStep 1167949 = 437981) B437981
theorem B807569 : Blo 235815 807569 := bstep (se 2 (by rfl) ⟨302838, by rfl⟩ : syracuseStep 807569 = 605677) B605677
theorem B381763 : Blo 235815 381763 := bstep (se 1 (by rfl) ⟨286322, by rfl⟩ : syracuseStep 381763 = 572645) B572645
theorem B1364849 : Blo 235815 1364849 := bstep (se 2 (by rfl) ⟨511818, by rfl⟩ : syracuseStep 1364849 = 1023637) B1023637
theorem B709517 : Blo 235815 709517 := bstep (se 3 (by rfl) ⟨133034, by rfl⟩ : syracuseStep 709517 = 266069) B266069
theorem B480323 : Blo 235815 480323 := bstep (se 1 (by rfl) ⟨360242, by rfl⟩ : syracuseStep 480323 = 720485) B720485
theorem B808013 : Blo 235815 808013 := bstep (se 3 (by rfl) ⟨151502, by rfl⟩ : syracuseStep 808013 = 303005) B303005
theorem B1201229 : Blo 235815 1201229 := bstep (se 3 (by rfl) ⟨225230, by rfl⟩ : syracuseStep 1201229 = 450461) B450461
theorem B808109 : Blo 235815 808109 := bstep (se 3 (by rfl) ⟨151520, by rfl⟩ : syracuseStep 808109 = 303041) B303041
theorem B447697 : Blo 235815 447697 := bstep (se 2 (by rfl) ⟨167886, by rfl⟩ : syracuseStep 447697 = 335773) B335773
theorem B808163 : Blo 235815 808163 := bstep (se 1 (by rfl) ⟨606122, by rfl⟩ : syracuseStep 808163 = 1212245) B1212245
theorem B677105 : Blo 235815 677105 := bstep (se 2 (by rfl) ⟨253914, by rfl⟩ : syracuseStep 677105 = 507829) B507829
theorem B2708963 : Blo 235815 2708963 := bstep (se 1 (by rfl) ⟨2031722, by rfl⟩ : syracuseStep 2708963 = 4063445) B4063445
theorem B808433 : Blo 235815 808433 := bstep (se 2 (by rfl) ⟨303162, by rfl⟩ : syracuseStep 808433 = 606325) B606325
theorem B2184803 : Blo 235815 2184803 := bstep (se 1 (by rfl) ⟨1638602, by rfl⟩ : syracuseStep 2184803 = 3277205) B3277205
theorem B480899 : Blo 235815 480899 := bstep (se 1 (by rfl) ⟨360674, by rfl⟩ : syracuseStep 480899 = 721349) B721349
theorem B382691 : Blo 235815 382691 := bstep (se 1 (by rfl) ⟨287018, by rfl⟩ : syracuseStep 382691 = 574037) B574037
theorem B284515 : Blo 235815 284515 := bstep (se 1 (by rfl) ⟨213386, by rfl⟩ : syracuseStep 284515 = 426773) B426773
theorem B513955 : Blo 235815 513955 := bstep (se 1 (by rfl) ⟨385466, by rfl⟩ : syracuseStep 513955 = 770933) B770933
theorem B382961 : Blo 235815 382961 := bstep (se 2 (by rfl) ⟨143610, by rfl⟩ : syracuseStep 382961 = 287221) B287221
theorem B808973 : Blo 235815 808973 := bstep (se 3 (by rfl) ⟨151682, by rfl⟩ : syracuseStep 808973 = 303365) B303365
theorem B809027 : Blo 235815 809027 := bstep (se 1 (by rfl) ⟨606770, by rfl⟩ : syracuseStep 809027 = 1213541) B1213541
theorem B678061 : Blo 235815 678061 := bstep (se 3 (by rfl) ⟨127136, by rfl⟩ : syracuseStep 678061 = 254273) B254273
theorem B907469 : Blo 235815 907469 := bstep (se 3 (by rfl) ⟨170150, by rfl⟩ : syracuseStep 907469 = 340301) B340301
theorem B448753 : Blo 235815 448753 := bstep (se 2 (by rfl) ⟨168282, by rfl⟩ : syracuseStep 448753 = 336565) B336565
theorem B252163 : Blo 235815 252163 := bstep (se 1 (by rfl) ⟨189122, by rfl⟩ : syracuseStep 252163 = 378245) B378245
theorem B514307 : Blo 235815 514307 := bstep (se 1 (by rfl) ⟨385730, by rfl⟩ : syracuseStep 514307 = 771461) B771461
theorem B383249 : Blo 235815 383249 := bstep (se 2 (by rfl) ⟨143718, by rfl⟩ : syracuseStep 383249 = 287437) B287437
theorem B809297 : Blo 235815 809297 := bstep (se 2 (by rfl) ⟨303486, by rfl⟩ : syracuseStep 809297 = 606973) B606973
theorem B678289 : Blo 235815 678289 := bstep (se 2 (by rfl) ⟨254358, by rfl⟩ : syracuseStep 678289 = 508717) B508717
theorem B809453 : Blo 235815 809453 := bstep (se 3 (by rfl) ⟨151772, by rfl⟩ : syracuseStep 809453 = 303545) B303545
theorem B1530353 : Blo 235815 1530353 := bstep (se 2 (by rfl) ⟨573882, by rfl⟩ : syracuseStep 1530353 = 1147765) B1147765
theorem B678449 : Blo 235815 678449 := bstep (se 2 (by rfl) ⟨254418, by rfl⟩ : syracuseStep 678449 = 508837) B508837
theorem B449155 : Blo 235815 449155 := bstep (se 1 (by rfl) ⟨336866, by rfl⟩ : syracuseStep 449155 = 673733) B673733
theorem B678563 : Blo 235815 678563 := bstep (se 1 (by rfl) ⟨508922, by rfl⟩ : syracuseStep 678563 = 1017845) B1017845
theorem B449201 : Blo 235815 449201 := bstep (se 2 (by rfl) ⟨168450, by rfl⟩ : syracuseStep 449201 = 336901) B336901
theorem B383665 : Blo 235815 383665 := bstep (se 2 (by rfl) ⟨143874, by rfl⟩ : syracuseStep 383665 = 287749) B287749
theorem B252595 : Blo 235815 252595 := bstep (se 1 (by rfl) ⟨189446, by rfl⟩ : syracuseStep 252595 = 378893) B378893
theorem B383699 : Blo 235815 383699 := bstep (se 1 (by rfl) ⟨287774, by rfl⟩ : syracuseStep 383699 = 575549) B575549
theorem B809777 : Blo 235815 809777 := bstep (se 2 (by rfl) ⟨303666, by rfl⟩ : syracuseStep 809777 = 607333) B607333
theorem B285491 : Blo 235815 285491 := bstep (se 1 (by rfl) ⟨214118, by rfl⟩ : syracuseStep 285491 = 428237) B428237
theorem B645965 : Blo 235815 645965 := bstep (se 3 (by rfl) ⟨121118, by rfl⟩ : syracuseStep 645965 = 242237) B242237
theorem B646051 : Blo 235815 646051 := bstep (se 1 (by rfl) ⟨484538, by rfl⟩ : syracuseStep 646051 = 969077) B969077
theorem B449489 : Blo 235815 449489 := bstep (se 2 (by rfl) ⟨168558, by rfl⟩ : syracuseStep 449489 = 337117) B337117
theorem B908273 : Blo 235815 908273 := bstep (se 2 (by rfl) ⟨340602, by rfl⟩ : syracuseStep 908273 = 681205) B681205
theorem B1531021 : Blo 235815 1531021 := bstep (se 3 (by rfl) ⟨287066, by rfl⟩ : syracuseStep 1531021 = 574133) B574133
theorem B482755 : Blo 235815 482755 := bstep (se 1 (by rfl) ⟨362066, by rfl⟩ : syracuseStep 482755 = 724133) B724133
theorem B286211 : Blo 235815 286211 := bstep (se 1 (by rfl) ⟨214658, by rfl⟩ : syracuseStep 286211 = 429317) B429317
theorem B679565 : Blo 235815 679565 := bstep (se 3 (by rfl) ⟨127418, by rfl⟩ : syracuseStep 679565 = 254837) B254837
theorem B908941 : Blo 235815 908941 := bstep (se 3 (by rfl) ⟨170426, by rfl⟩ : syracuseStep 908941 = 340853) B340853
theorem B450211 : Blo 235815 450211 := bstep (se 1 (by rfl) ⟨337658, by rfl⟩ : syracuseStep 450211 = 675317) B675317
theorem B2186993 : Blo 235815 2186993 := bstep (se 2 (by rfl) ⟨820122, by rfl⟩ : syracuseStep 2186993 = 1640245) B1640245
theorem B679747 : Blo 235815 679747 := bstep (se 1 (by rfl) ⟨509810, by rfl⟩ : syracuseStep 679747 = 1019621) B1019621
theorem B319393 : Blo 235815 319393 := bstep (se 2 (by rfl) ⟨119772, by rfl⟩ : syracuseStep 319393 = 239545) B239545
theorem B253859 : Blo 235815 253859 := bstep (se 1 (by rfl) ⟨190394, by rfl⟩ : syracuseStep 253859 = 380789) B380789
theorem B1204145 : Blo 235815 1204145 := bstep (se 2 (by rfl) ⟨451554, by rfl⟩ : syracuseStep 1204145 = 903109) B903109
theorem B679907 : Blo 235815 679907 := bstep (se 1 (by rfl) ⟨509930, by rfl⟩ : syracuseStep 679907 = 1019861) B1019861
theorem B417827 : Blo 235815 417827 := bstep (se 1 (by rfl) ⟨313370, by rfl⟩ : syracuseStep 417827 = 626741) B626741
theorem B450659 : Blo 235815 450659 := bstep (se 1 (by rfl) ⟨337994, by rfl⟩ : syracuseStep 450659 = 675989) B675989
theorem B778349 : Blo 235815 778349 := bstep (se 3 (by rfl) ⟨145940, by rfl⟩ : syracuseStep 778349 = 291881) B291881
theorem B1466545 : Blo 235815 1466545 := bstep (se 2 (by rfl) ⟨549954, by rfl⟩ : syracuseStep 1466545 = 1099909) B1099909
theorem B647459 : Blo 235815 647459 := bstep (se 1 (by rfl) ⟨485594, by rfl⟩ : syracuseStep 647459 = 971189) B971189
theorem B385361 : Blo 235815 385361 := bstep (se 2 (by rfl) ⟨144510, by rfl⟩ : syracuseStep 385361 = 289021) B289021
theorem B450947 : Blo 235815 450947 := bstep (se 1 (by rfl) ⟨338210, by rfl⟩ : syracuseStep 450947 = 676421) B676421
theorem B319907 : Blo 235815 319907 := bstep (se 1 (by rfl) ⟨239930, by rfl⟩ : syracuseStep 319907 = 479861) B479861
theorem B909731 : Blo 235815 909731 := bstep (se 1 (by rfl) ⟨682298, by rfl⟩ : syracuseStep 909731 = 1364597) B1364597
theorem B319955 : Blo 235815 319955 := bstep (se 1 (by rfl) ⟨239966, by rfl⟩ : syracuseStep 319955 = 479933) B479933
theorem B483907 : Blo 235815 483907 := bstep (se 1 (by rfl) ⟨362930, by rfl⟩ : syracuseStep 483907 = 725861) B725861
theorem B254611 : Blo 235815 254611 := bstep (se 1 (by rfl) ⟨190958, by rfl⟩ : syracuseStep 254611 = 381917) B381917
theorem B1925957 : Blo 235815 1925957 := bstep (se 4 (by rfl) ⟨180558, by rfl⟩ : syracuseStep 1925957 = 361117) B361117
theorem B320387 : Blo 235815 320387 := bstep (se 1 (by rfl) ⟨240290, by rfl⟩ : syracuseStep 320387 = 480581) B480581
theorem B1467341 : Blo 235815 1467341 := bstep (se 3 (by rfl) ⟨275126, by rfl⟩ : syracuseStep 1467341 = 550253) B550253
theorem B680977 : Blo 235815 680977 := bstep (se 2 (by rfl) ⟨255366, by rfl⟩ : syracuseStep 680977 = 510733) B510733
theorem B910385 : Blo 235815 910385 := bstep (se 2 (by rfl) ⟨341394, by rfl⟩ : syracuseStep 910385 = 682789) B682789
theorem B451889 : Blo 235815 451889 := bstep (se 2 (by rfl) ⟨169458, by rfl⟩ : syracuseStep 451889 = 338917) B338917
theorem B1238321 : Blo 235815 1238321 := bstep (se 2 (by rfl) ⟨464370, by rfl⟩ : syracuseStep 1238321 = 928741) B928741
theorem B1205603 : Blo 235815 1205603 := bstep (se 1 (by rfl) ⟨904202, by rfl⟩ : syracuseStep 1205603 = 1808405) B1808405
theorem B1369457 : Blo 235815 1369457 := bstep (se 2 (by rfl) ⟨513546, by rfl⟩ : syracuseStep 1369457 = 1027093) B1027093
theorem B353729 : Blo 235815 353729 := bstep (se 2 (by rfl) ⟨132648, by rfl⟩ : syracuseStep 353729 = 265297) B265297
theorem B353747 : Blo 235815 353747 := bstep (se 1 (by rfl) ⟨265310, by rfl⟩ : syracuseStep 353747 = 530621) B530621
theorem B353777 : Blo 235815 353777 := bstep (se 2 (by rfl) ⟨132666, by rfl⟩ : syracuseStep 353777 = 265333) B265333
theorem B353795 : Blo 235815 353795 := bstep (se 1 (by rfl) ⟨265346, by rfl⟩ : syracuseStep 353795 = 530693) B530693
theorem B353825 : Blo 235815 353825 := bstep (se 2 (by rfl) ⟨132684, by rfl⟩ : syracuseStep 353825 = 265369) B265369
theorem B353843 : Blo 235815 353843 := bstep (se 1 (by rfl) ⟨265382, by rfl⟩ : syracuseStep 353843 = 530765) B530765
theorem B353873 : Blo 235815 353873 := bstep (se 2 (by rfl) ⟨132702, by rfl⟩ : syracuseStep 353873 = 265405) B265405
theorem B353891 : Blo 235815 353891 := bstep (se 1 (by rfl) ⟨265418, by rfl⟩ : syracuseStep 353891 = 530837) B530837
theorem B353921 : Blo 235815 353921 := bstep (se 2 (by rfl) ⟨132720, by rfl⟩ : syracuseStep 353921 = 265441) B265441
theorem B353939 : Blo 235815 353939 := bstep (se 1 (by rfl) ⟨265454, by rfl⟩ : syracuseStep 353939 = 530909) B530909
theorem B353969 : Blo 235815 353969 := bstep (se 2 (by rfl) ⟨132738, by rfl⟩ : syracuseStep 353969 = 265477) B265477
theorem B353987 : Blo 235815 353987 := bstep (se 1 (by rfl) ⟨265490, by rfl⟩ : syracuseStep 353987 = 530981) B530981
theorem B255683 : Blo 235815 255683 := bstep (se 1 (by rfl) ⟨191762, by rfl⟩ : syracuseStep 255683 = 383525) B383525
theorem B354017 : Blo 235815 354017 := bstep (se 2 (by rfl) ⟨132756, by rfl⟩ : syracuseStep 354017 = 265513) B265513
theorem B354035 : Blo 235815 354035 := bstep (se 1 (by rfl) ⟨265526, by rfl⟩ : syracuseStep 354035 = 531053) B531053
theorem B354065 : Blo 235815 354065 := bstep (se 2 (by rfl) ⟨132774, by rfl⟩ : syracuseStep 354065 = 265549) B265549
theorem B354083 : Blo 235815 354083 := bstep (se 1 (by rfl) ⟨265562, by rfl⟩ : syracuseStep 354083 = 531125) B531125
theorem B354113 : Blo 235815 354113 := bstep (se 2 (by rfl) ⟨132792, by rfl⟩ : syracuseStep 354113 = 265585) B265585
theorem B354131 : Blo 235815 354131 := bstep (se 1 (by rfl) ⟨265598, by rfl⟩ : syracuseStep 354131 = 531197) B531197
theorem B354161 : Blo 235815 354161 := bstep (se 2 (by rfl) ⟨132810, by rfl⟩ : syracuseStep 354161 = 265621) B265621
theorem B354179 : Blo 235815 354179 := bstep (se 1 (by rfl) ⟨265634, by rfl⟩ : syracuseStep 354179 = 531269) B531269
theorem B354209 : Blo 235815 354209 := bstep (se 2 (by rfl) ⟨132828, by rfl⟩ : syracuseStep 354209 = 265657) B265657
theorem B354227 : Blo 235815 354227 := bstep (se 1 (by rfl) ⟨265670, by rfl⟩ : syracuseStep 354227 = 531341) B531341
theorem B354257 : Blo 235815 354257 := bstep (se 2 (by rfl) ⟨132846, by rfl⟩ : syracuseStep 354257 = 265693) B265693
theorem B354275 : Blo 235815 354275 := bstep (se 1 (by rfl) ⟨265706, by rfl⟩ : syracuseStep 354275 = 531413) B531413
theorem B354305 : Blo 235815 354305 := bstep (se 2 (by rfl) ⟨132864, by rfl⟩ : syracuseStep 354305 = 265729) B265729
theorem B354323 : Blo 235815 354323 := bstep (se 1 (by rfl) ⟨265742, by rfl⟩ : syracuseStep 354323 = 531485) B531485
theorem B354353 : Blo 235815 354353 := bstep (se 2 (by rfl) ⟨132882, by rfl⟩ : syracuseStep 354353 = 265765) B265765
theorem B354371 : Blo 235815 354371 := bstep (se 1 (by rfl) ⟨265778, by rfl⟩ : syracuseStep 354371 = 531557) B531557
theorem B354401 : Blo 235815 354401 := bstep (se 2 (by rfl) ⟨132900, by rfl⟩ : syracuseStep 354401 = 265801) B265801
theorem B354419 : Blo 235815 354419 := bstep (se 1 (by rfl) ⟨265814, by rfl⟩ : syracuseStep 354419 = 531629) B531629
theorem B583811 : Blo 235815 583811 := bstep (se 1 (by rfl) ⟨437858, by rfl⟩ : syracuseStep 583811 = 875717) B875717
theorem B1206413 : Blo 235815 1206413 := bstep (se 3 (by rfl) ⟨226202, by rfl⟩ : syracuseStep 1206413 = 452405) B452405
theorem B354449 : Blo 235815 354449 := bstep (se 2 (by rfl) ⟨132918, by rfl⟩ : syracuseStep 354449 = 265837) B265837
theorem B354467 : Blo 235815 354467 := bstep (se 1 (by rfl) ⟨265850, by rfl⟩ : syracuseStep 354467 = 531701) B531701
theorem B452785 : Blo 235815 452785 := bstep (se 2 (by rfl) ⟨169794, by rfl⟩ : syracuseStep 452785 = 339589) B339589
theorem B354497 : Blo 235815 354497 := bstep (se 2 (by rfl) ⟨132936, by rfl⟩ : syracuseStep 354497 = 265873) B265873
theorem B354515 : Blo 235815 354515 := bstep (se 1 (by rfl) ⟨265886, by rfl⟩ : syracuseStep 354515 = 531773) B531773
theorem B354545 : Blo 235815 354545 := bstep (se 2 (by rfl) ⟨132954, by rfl⟩ : syracuseStep 354545 = 265909) B265909
theorem B354563 : Blo 235815 354563 := bstep (se 1 (by rfl) ⟨265922, by rfl⟩ : syracuseStep 354563 = 531845) B531845
theorem B682253 : Blo 235815 682253 := bstep (se 3 (by rfl) ⟨127922, by rfl⟩ : syracuseStep 682253 = 255845) B255845
theorem B354593 : Blo 235815 354593 := bstep (se 2 (by rfl) ⟨132972, by rfl⟩ : syracuseStep 354593 = 265945) B265945
theorem B354611 : Blo 235815 354611 := bstep (se 1 (by rfl) ⟨265958, by rfl⟩ : syracuseStep 354611 = 531917) B531917
theorem B354641 : Blo 235815 354641 := bstep (se 2 (by rfl) ⟨132990, by rfl⟩ : syracuseStep 354641 = 265981) B265981
theorem B452945 : Blo 235815 452945 := bstep (se 2 (by rfl) ⟨169854, by rfl⟩ : syracuseStep 452945 = 339709) B339709
theorem B354659 : Blo 235815 354659 := bstep (se 1 (by rfl) ⟨265994, by rfl⟩ : syracuseStep 354659 = 531989) B531989
theorem B354689 : Blo 235815 354689 := bstep (se 2 (by rfl) ⟨133008, by rfl⟩ : syracuseStep 354689 = 266017) B266017
theorem B354707 : Blo 235815 354707 := bstep (se 1 (by rfl) ⟨266030, by rfl⟩ : syracuseStep 354707 = 532061) B532061
theorem B354737 : Blo 235815 354737 := bstep (se 2 (by rfl) ⟨133026, by rfl⟩ : syracuseStep 354737 = 266053) B266053
theorem B354755 : Blo 235815 354755 := bstep (se 1 (by rfl) ⟨266066, by rfl⟩ : syracuseStep 354755 = 532133) B532133
theorem B682435 : Blo 235815 682435 := bstep (se 1 (by rfl) ⟨511826, by rfl⟩ : syracuseStep 682435 = 1023653) B1023653
theorem B354785 : Blo 235815 354785 := bstep (se 2 (by rfl) ⟨133044, by rfl⟩ : syracuseStep 354785 = 266089) B266089
theorem B1370609 : Blo 235815 1370609 := bstep (se 2 (by rfl) ⟨513978, by rfl⟩ : syracuseStep 1370609 = 1027957) B1027957
theorem B354803 : Blo 235815 354803 := bstep (se 1 (by rfl) ⟨266102, by rfl⟩ : syracuseStep 354803 = 532205) B532205
theorem B682481 : Blo 235815 682481 := bstep (se 2 (by rfl) ⟨255930, by rfl⟩ : syracuseStep 682481 = 511861) B511861
theorem B354833 : Blo 235815 354833 := bstep (se 2 (by rfl) ⟨133062, by rfl⟩ : syracuseStep 354833 = 266125) B266125
theorem B354851 : Blo 235815 354851 := bstep (se 1 (by rfl) ⟨266138, by rfl⟩ : syracuseStep 354851 = 532277) B532277
theorem B354881 : Blo 235815 354881 := bstep (se 2 (by rfl) ⟨133080, by rfl⟩ : syracuseStep 354881 = 266161) B266161
theorem B354899 : Blo 235815 354899 := bstep (se 1 (by rfl) ⟨266174, by rfl⟩ : syracuseStep 354899 = 532349) B532349
theorem B354929 : Blo 235815 354929 := bstep (se 2 (by rfl) ⟨133098, by rfl⟩ : syracuseStep 354929 = 266197) B266197
theorem B354947 : Blo 235815 354947 := bstep (se 1 (by rfl) ⟨266210, by rfl⟩ : syracuseStep 354947 = 532421) B532421
theorem B354977 : Blo 235815 354977 := bstep (se 2 (by rfl) ⟨133116, by rfl⟩ : syracuseStep 354977 = 266233) B266233
theorem B354995 : Blo 235815 354995 := bstep (se 1 (by rfl) ⟨266246, by rfl⟩ : syracuseStep 354995 = 532493) B532493
theorem B355025 : Blo 235815 355025 := bstep (se 2 (by rfl) ⟨133134, by rfl⟩ : syracuseStep 355025 = 266269) B266269
theorem B355043 : Blo 235815 355043 := bstep (se 1 (by rfl) ⟨266282, by rfl⟩ : syracuseStep 355043 = 532565) B532565
theorem B453347 : Blo 235815 453347 := bstep (se 1 (by rfl) ⟨340010, by rfl⟩ : syracuseStep 453347 = 680021) B680021
theorem B355073 : Blo 235815 355073 := bstep (se 2 (by rfl) ⟨133152, by rfl⟩ : syracuseStep 355073 = 266305) B266305
theorem B355091 : Blo 235815 355091 := bstep (se 1 (by rfl) ⟨266318, by rfl⟩ : syracuseStep 355091 = 532637) B532637
theorem B355121 : Blo 235815 355121 := bstep (se 2 (by rfl) ⟨133170, by rfl⟩ : syracuseStep 355121 = 266341) B266341
theorem B355139 : Blo 235815 355139 := bstep (se 1 (by rfl) ⟨266354, by rfl⟩ : syracuseStep 355139 = 532709) B532709
theorem B355169 : Blo 235815 355169 := bstep (se 2 (by rfl) ⟨133188, by rfl⟩ : syracuseStep 355169 = 266377) B266377
theorem B1010531 : Blo 235815 1010531 := bstep (se 1 (by rfl) ⟨757898, by rfl⟩ : syracuseStep 1010531 = 1515797) B1515797
theorem B355187 : Blo 235815 355187 := bstep (se 1 (by rfl) ⟨266390, by rfl⟩ : syracuseStep 355187 = 532781) B532781
theorem B355217 : Blo 235815 355217 := bstep (se 2 (by rfl) ⟨133206, by rfl⟩ : syracuseStep 355217 = 266413) B266413
theorem B355235 : Blo 235815 355235 := bstep (se 1 (by rfl) ⟨266426, by rfl⟩ : syracuseStep 355235 = 532853) B532853
theorem B355265 : Blo 235815 355265 := bstep (se 2 (by rfl) ⟨133224, by rfl⟩ : syracuseStep 355265 = 266449) B266449
theorem B355283 : Blo 235815 355283 := bstep (se 1 (by rfl) ⟨266462, by rfl⟩ : syracuseStep 355283 = 532925) B532925
theorem B355313 : Blo 235815 355313 := bstep (se 2 (by rfl) ⟨133242, by rfl⟩ : syracuseStep 355313 = 266485) B266485
theorem B355331 : Blo 235815 355331 := bstep (se 1 (by rfl) ⟨266498, by rfl⟩ : syracuseStep 355331 = 532997) B532997
theorem B355361 : Blo 235815 355361 := bstep (se 2 (by rfl) ⟨133260, by rfl⟩ : syracuseStep 355361 = 266521) B266521
theorem B355379 : Blo 235815 355379 := bstep (se 1 (by rfl) ⟨266534, by rfl⟩ : syracuseStep 355379 = 533069) B533069
theorem B355409 : Blo 235815 355409 := bstep (se 2 (by rfl) ⟨133278, by rfl⟩ : syracuseStep 355409 = 266557) B266557
theorem B355427 : Blo 235815 355427 := bstep (se 1 (by rfl) ⟨266570, by rfl⟩ : syracuseStep 355427 = 533141) B533141
theorem B355457 : Blo 235815 355457 := bstep (se 2 (by rfl) ⟨133296, by rfl⟩ : syracuseStep 355457 = 266593) B266593
theorem B355475 : Blo 235815 355475 := bstep (se 1 (by rfl) ⟨266606, by rfl⟩ : syracuseStep 355475 = 533213) B533213
theorem B355505 : Blo 235815 355505 := bstep (se 2 (by rfl) ⟨133314, by rfl⟩ : syracuseStep 355505 = 266629) B266629
theorem B355523 : Blo 235815 355523 := bstep (se 1 (by rfl) ⟨266642, by rfl⟩ : syracuseStep 355523 = 533285) B533285
theorem B355553 : Blo 235815 355553 := bstep (se 2 (by rfl) ⟨133332, by rfl⟩ : syracuseStep 355553 = 266665) B266665
theorem B355571 : Blo 235815 355571 := bstep (se 1 (by rfl) ⟨266678, by rfl⟩ : syracuseStep 355571 = 533357) B533357
theorem B355601 : Blo 235815 355601 := bstep (se 2 (by rfl) ⟨133350, by rfl⟩ : syracuseStep 355601 = 266701) B266701
theorem B355619 : Blo 235815 355619 := bstep (se 1 (by rfl) ⟨266714, by rfl⟩ : syracuseStep 355619 = 533429) B533429
theorem B355649 : Blo 235815 355649 := bstep (se 2 (by rfl) ⟨133368, by rfl⟩ : syracuseStep 355649 = 266737) B266737
theorem B355667 : Blo 235815 355667 := bstep (se 1 (by rfl) ⟨266750, by rfl⟩ : syracuseStep 355667 = 533501) B533501
theorem B355697 : Blo 235815 355697 := bstep (se 2 (by rfl) ⟨133386, by rfl⟩ : syracuseStep 355697 = 266773) B266773
theorem B355715 : Blo 235815 355715 := bstep (se 1 (by rfl) ⟨266786, by rfl⟩ : syracuseStep 355715 = 533573) B533573
theorem B355745 : Blo 235815 355745 := bstep (se 2 (by rfl) ⟨133404, by rfl⟩ : syracuseStep 355745 = 266809) B266809
theorem B355763 : Blo 235815 355763 := bstep (se 1 (by rfl) ⟨266822, by rfl⟩ : syracuseStep 355763 = 533645) B533645
theorem B355793 : Blo 235815 355793 := bstep (se 2 (by rfl) ⟨133422, by rfl⟩ : syracuseStep 355793 = 266845) B266845
theorem B355811 : Blo 235815 355811 := bstep (se 1 (by rfl) ⟨266858, by rfl⟩ : syracuseStep 355811 = 533717) B533717
theorem B355841 : Blo 235815 355841 := bstep (se 2 (by rfl) ⟨133440, by rfl⟩ : syracuseStep 355841 = 266881) B266881
theorem B1371653 : Blo 235815 1371653 := bstep (se 4 (by rfl) ⟨128592, by rfl⟩ : syracuseStep 1371653 = 257185) B257185
theorem B355859 : Blo 235815 355859 := bstep (se 1 (by rfl) ⟨266894, by rfl⟩ : syracuseStep 355859 = 533789) B533789
theorem B355889 : Blo 235815 355889 := bstep (se 2 (by rfl) ⟨133458, by rfl⟩ : syracuseStep 355889 = 266917) B266917
theorem B355907 : Blo 235815 355907 := bstep (se 1 (by rfl) ⟨266930, by rfl⟩ : syracuseStep 355907 = 533861) B533861
theorem B323155 : Blo 235815 323155 := bstep (se 1 (by rfl) ⟨242366, by rfl⟩ : syracuseStep 323155 = 484733) B484733
theorem B355937 : Blo 235815 355937 := bstep (se 2 (by rfl) ⟨133476, by rfl⟩ : syracuseStep 355937 = 266953) B266953
theorem B454243 : Blo 235815 454243 := bstep (se 1 (by rfl) ⟨340682, by rfl⟩ : syracuseStep 454243 = 681365) B681365
theorem B355955 : Blo 235815 355955 := bstep (se 1 (by rfl) ⟨266966, by rfl⟩ : syracuseStep 355955 = 533933) B533933
theorem B355985 : Blo 235815 355985 := bstep (se 2 (by rfl) ⟨133494, by rfl⟩ : syracuseStep 355985 = 266989) B266989
theorem B356003 : Blo 235815 356003 := bstep (se 1 (by rfl) ⟨267002, by rfl⟩ : syracuseStep 356003 = 534005) B534005
theorem B356033 : Blo 235815 356033 := bstep (se 2 (by rfl) ⟨133512, by rfl⟩ : syracuseStep 356033 = 267025) B267025
theorem B323281 : Blo 235815 323281 := bstep (se 2 (by rfl) ⟨121230, by rfl⟩ : syracuseStep 323281 = 242461) B242461
theorem B356051 : Blo 235815 356051 := bstep (se 1 (by rfl) ⟨267038, by rfl⟩ : syracuseStep 356051 = 534077) B534077
theorem B2289379 : Blo 235815 2289379 := bstep (se 1 (by rfl) ⟨1717034, by rfl⟩ : syracuseStep 2289379 = 3434069) B3434069
theorem B356081 : Blo 235815 356081 := bstep (se 2 (by rfl) ⟨133530, by rfl⟩ : syracuseStep 356081 = 267061) B267061
theorem B356099 : Blo 235815 356099 := bstep (se 1 (by rfl) ⟨267074, by rfl⟩ : syracuseStep 356099 = 534149) B534149
theorem B454403 : Blo 235815 454403 := bstep (se 1 (by rfl) ⟨340802, by rfl⟩ : syracuseStep 454403 = 681605) B681605
theorem B356129 : Blo 235815 356129 := bstep (se 2 (by rfl) ⟨133548, by rfl⟩ : syracuseStep 356129 = 267097) B267097
theorem B356147 : Blo 235815 356147 := bstep (se 1 (by rfl) ⟨267110, by rfl⟩ : syracuseStep 356147 = 534221) B534221
theorem B2420549 : Blo 235815 2420549 := bstep (se 4 (by rfl) ⟨226926, by rfl⟩ : syracuseStep 2420549 = 453853) B453853
theorem B356177 : Blo 235815 356177 := bstep (se 2 (by rfl) ⟨133566, by rfl⟩ : syracuseStep 356177 = 267133) B267133
theorem B356195 : Blo 235815 356195 := bstep (se 1 (by rfl) ⟨267146, by rfl⟩ : syracuseStep 356195 = 534293) B534293
theorem B356225 : Blo 235815 356225 := bstep (se 2 (by rfl) ⟨133584, by rfl⟩ : syracuseStep 356225 = 267169) B267169
theorem B356243 : Blo 235815 356243 := bstep (se 1 (by rfl) ⟨267182, by rfl⟩ : syracuseStep 356243 = 534365) B534365
theorem B356273 : Blo 235815 356273 := bstep (se 2 (by rfl) ⟨133602, by rfl⟩ : syracuseStep 356273 = 267205) B267205
theorem B356291 : Blo 235815 356291 := bstep (se 1 (by rfl) ⟨267218, by rfl⟩ : syracuseStep 356291 = 534437) B534437
theorem B683981 : Blo 235815 683981 := bstep (se 3 (by rfl) ⟨128246, by rfl⟩ : syracuseStep 683981 = 256493) B256493
theorem B356321 : Blo 235815 356321 := bstep (se 2 (by rfl) ⟨133620, by rfl⟩ : syracuseStep 356321 = 267241) B267241
theorem B356339 : Blo 235815 356339 := bstep (se 1 (by rfl) ⟨267254, by rfl⟩ : syracuseStep 356339 = 534509) B534509
theorem B356369 : Blo 235815 356369 := bstep (se 2 (by rfl) ⟨133638, by rfl⟩ : syracuseStep 356369 = 267277) B267277
theorem B356387 : Blo 235815 356387 := bstep (se 1 (by rfl) ⟨267290, by rfl⟩ : syracuseStep 356387 = 534581) B534581
theorem B1011761 : Blo 235815 1011761 := bstep (se 2 (by rfl) ⟨379410, by rfl⟩ : syracuseStep 1011761 = 758821) B758821
theorem B356417 : Blo 235815 356417 := bstep (se 2 (by rfl) ⟨133656, by rfl⟩ : syracuseStep 356417 = 267313) B267313
theorem B356435 : Blo 235815 356435 := bstep (se 1 (by rfl) ⟨267326, by rfl⟩ : syracuseStep 356435 = 534653) B534653
theorem B356465 : Blo 235815 356465 := bstep (se 2 (by rfl) ⟨133674, by rfl⟩ : syracuseStep 356465 = 267349) B267349
theorem B356483 : Blo 235815 356483 := bstep (se 1 (by rfl) ⟨267362, by rfl⟩ : syracuseStep 356483 = 534725) B534725
theorem B356513 : Blo 235815 356513 := bstep (se 2 (by rfl) ⟨133692, by rfl⟩ : syracuseStep 356513 = 267385) B267385
theorem B356531 : Blo 235815 356531 := bstep (se 1 (by rfl) ⟨267398, by rfl⟩ : syracuseStep 356531 = 534797) B534797
theorem B356561 : Blo 235815 356561 := bstep (se 2 (by rfl) ⟨133710, by rfl⟩ : syracuseStep 356561 = 267421) B267421
theorem B356579 : Blo 235815 356579 := bstep (se 1 (by rfl) ⟨267434, by rfl⟩ : syracuseStep 356579 = 534869) B534869
theorem B356609 : Blo 235815 356609 := bstep (se 2 (by rfl) ⟨133728, by rfl⟩ : syracuseStep 356609 = 267457) B267457
theorem B323843 : Blo 235815 323843 := bstep (se 1 (by rfl) ⟨242882, by rfl⟩ : syracuseStep 323843 = 485765) B485765
theorem B356627 : Blo 235815 356627 := bstep (se 1 (by rfl) ⟨267470, by rfl⟩ : syracuseStep 356627 = 534941) B534941
theorem B356657 : Blo 235815 356657 := bstep (se 2 (by rfl) ⟨133746, by rfl⟩ : syracuseStep 356657 = 267493) B267493
theorem B356675 : Blo 235815 356675 := bstep (se 1 (by rfl) ⟨267506, by rfl⟩ : syracuseStep 356675 = 535013) B535013
theorem B356705 : Blo 235815 356705 := bstep (se 2 (by rfl) ⟨133764, by rfl⟩ : syracuseStep 356705 = 267529) B267529
theorem B356723 : Blo 235815 356723 := bstep (se 1 (by rfl) ⟨267542, by rfl⟩ : syracuseStep 356723 = 535085) B535085
theorem B356753 : Blo 235815 356753 := bstep (se 2 (by rfl) ⟨133782, by rfl⟩ : syracuseStep 356753 = 267565) B267565
theorem B356771 : Blo 235815 356771 := bstep (se 1 (by rfl) ⟨267578, by rfl⟩ : syracuseStep 356771 = 535157) B535157
theorem B356801 : Blo 235815 356801 := bstep (se 2 (by rfl) ⟨133800, by rfl⟩ : syracuseStep 356801 = 267601) B267601
theorem B356819 : Blo 235815 356819 := bstep (se 1 (by rfl) ⟨267614, by rfl⟩ : syracuseStep 356819 = 535229) B535229
theorem B356849 : Blo 235815 356849 := bstep (se 2 (by rfl) ⟨133818, by rfl⟩ : syracuseStep 356849 = 267637) B267637
theorem B356867 : Blo 235815 356867 := bstep (se 1 (by rfl) ⟨267650, by rfl⟩ : syracuseStep 356867 = 535301) B535301
theorem B356897 : Blo 235815 356897 := bstep (se 2 (by rfl) ⟨133836, by rfl⟩ : syracuseStep 356897 = 267673) B267673
theorem B356915 : Blo 235815 356915 := bstep (se 1 (by rfl) ⟨267686, by rfl⟩ : syracuseStep 356915 = 535373) B535373
theorem B356945 : Blo 235815 356945 := bstep (se 2 (by rfl) ⟨133854, by rfl⟩ : syracuseStep 356945 = 267709) B267709
theorem B356963 : Blo 235815 356963 := bstep (se 1 (by rfl) ⟨267722, by rfl⟩ : syracuseStep 356963 = 535445) B535445
theorem B356993 : Blo 235815 356993 := bstep (se 2 (by rfl) ⟨133872, by rfl⟩ : syracuseStep 356993 = 267745) B267745
theorem B717457 : Blo 235815 717457 := bstep (se 2 (by rfl) ⟨269046, by rfl⟩ : syracuseStep 717457 = 538093) B538093
theorem B357011 : Blo 235815 357011 := bstep (se 1 (by rfl) ⟨267758, by rfl⟩ : syracuseStep 357011 = 535517) B535517
theorem B357041 : Blo 235815 357041 := bstep (se 2 (by rfl) ⟨133890, by rfl⟩ : syracuseStep 357041 = 267781) B267781
theorem B357059 : Blo 235815 357059 := bstep (se 1 (by rfl) ⟨267794, by rfl⟩ : syracuseStep 357059 = 535589) B535589
theorem B357089 : Blo 235815 357089 := bstep (se 2 (by rfl) ⟨133908, by rfl⟩ : syracuseStep 357089 = 267817) B267817
theorem B357107 : Blo 235815 357107 := bstep (se 1 (by rfl) ⟨267830, by rfl⟩ : syracuseStep 357107 = 535661) B535661
theorem B357137 : Blo 235815 357137 := bstep (se 2 (by rfl) ⟨133926, by rfl⟩ : syracuseStep 357137 = 267853) B267853
theorem B357155 : Blo 235815 357155 := bstep (se 1 (by rfl) ⟨267866, by rfl⟩ : syracuseStep 357155 = 535733) B535733
theorem B357185 : Blo 235815 357185 := bstep (se 2 (by rfl) ⟨133944, by rfl⟩ : syracuseStep 357185 = 267889) B267889
theorem B357203 : Blo 235815 357203 := bstep (se 1 (by rfl) ⟨267902, by rfl⟩ : syracuseStep 357203 = 535805) B535805
theorem B357233 : Blo 235815 357233 := bstep (se 2 (by rfl) ⟨133962, by rfl⟩ : syracuseStep 357233 = 267925) B267925
theorem B357251 : Blo 235815 357251 := bstep (se 1 (by rfl) ⟨267938, by rfl⟩ : syracuseStep 357251 = 535877) B535877
theorem B357281 : Blo 235815 357281 := bstep (se 2 (by rfl) ⟨133980, by rfl⟩ : syracuseStep 357281 = 267961) B267961
theorem B357299 : Blo 235815 357299 := bstep (se 1 (by rfl) ⟨267974, by rfl⟩ : syracuseStep 357299 = 535949) B535949
theorem B357329 : Blo 235815 357329 := bstep (se 2 (by rfl) ⟨133998, by rfl⟩ : syracuseStep 357329 = 267997) B267997
theorem B357347 : Blo 235815 357347 := bstep (se 1 (by rfl) ⟨268010, by rfl⟩ : syracuseStep 357347 = 536021) B536021
theorem B1209329 : Blo 235815 1209329 := bstep (se 2 (by rfl) ⟨453498, by rfl⟩ : syracuseStep 1209329 = 906997) B906997
theorem B357377 : Blo 235815 357377 := bstep (se 2 (by rfl) ⟨134016, by rfl⟩ : syracuseStep 357377 = 268033) B268033
theorem B357395 : Blo 235815 357395 := bstep (se 1 (by rfl) ⟨268046, by rfl⟩ : syracuseStep 357395 = 536093) B536093
theorem B357425 : Blo 235815 357425 := bstep (se 2 (by rfl) ⟨134034, by rfl⟩ : syracuseStep 357425 = 268069) B268069
theorem B357443 : Blo 235815 357443 := bstep (se 1 (by rfl) ⟨268082, by rfl⟩ : syracuseStep 357443 = 536165) B536165
theorem B357473 : Blo 235815 357473 := bstep (se 2 (by rfl) ⟨134052, by rfl⟩ : syracuseStep 357473 = 268105) B268105
theorem B357491 : Blo 235815 357491 := bstep (se 1 (by rfl) ⟨268118, by rfl⟩ : syracuseStep 357491 = 536237) B536237
theorem B357521 : Blo 235815 357521 := bstep (se 2 (by rfl) ⟨134070, by rfl⟩ : syracuseStep 357521 = 268141) B268141
theorem B357539 : Blo 235815 357539 := bstep (se 1 (by rfl) ⟨268154, by rfl⟩ : syracuseStep 357539 = 536309) B536309
theorem B357569 : Blo 235815 357569 := bstep (se 2 (by rfl) ⟨134088, by rfl⟩ : syracuseStep 357569 = 268177) B268177
theorem B357587 : Blo 235815 357587 := bstep (se 1 (by rfl) ⟨268190, by rfl⟩ : syracuseStep 357587 = 536381) B536381
theorem B357617 : Blo 235815 357617 := bstep (se 2 (by rfl) ⟨134106, by rfl⟩ : syracuseStep 357617 = 268213) B268213
theorem B357635 : Blo 235815 357635 := bstep (se 1 (by rfl) ⟨268226, by rfl⟩ : syracuseStep 357635 = 536453) B536453
theorem B357665 : Blo 235815 357665 := bstep (se 2 (by rfl) ⟨134124, by rfl⟩ : syracuseStep 357665 = 268249) B268249
theorem B357683 : Blo 235815 357683 := bstep (se 1 (by rfl) ⟨268262, by rfl⟩ : syracuseStep 357683 = 536525) B536525
theorem B357713 : Blo 235815 357713 := bstep (se 2 (by rfl) ⟨134142, by rfl⟩ : syracuseStep 357713 = 268285) B268285
theorem B357731 : Blo 235815 357731 := bstep (se 1 (by rfl) ⟨268298, by rfl⟩ : syracuseStep 357731 = 536597) B536597
theorem B357761 : Blo 235815 357761 := bstep (se 2 (by rfl) ⟨134160, by rfl⟩ : syracuseStep 357761 = 268321) B268321
theorem B357779 : Blo 235815 357779 := bstep (se 1 (by rfl) ⟨268334, by rfl⟩ : syracuseStep 357779 = 536669) B536669
theorem B357809 : Blo 235815 357809 := bstep (se 2 (by rfl) ⟨134178, by rfl⟩ : syracuseStep 357809 = 268357) B268357
theorem B357827 : Blo 235815 357827 := bstep (se 1 (by rfl) ⟨268370, by rfl⟩ : syracuseStep 357827 = 536741) B536741
theorem B357857 : Blo 235815 357857 := bstep (se 2 (by rfl) ⟨134196, by rfl⟩ : syracuseStep 357857 = 268393) B268393
theorem B357875 : Blo 235815 357875 := bstep (se 1 (by rfl) ⟨268406, by rfl⟩ : syracuseStep 357875 = 536813) B536813
theorem B357905 : Blo 235815 357905 := bstep (se 2 (by rfl) ⟨134214, by rfl⟩ : syracuseStep 357905 = 268429) B268429
theorem B357923 : Blo 235815 357923 := bstep (se 1 (by rfl) ⟨268442, by rfl⟩ : syracuseStep 357923 = 536885) B536885
theorem B357953 : Blo 235815 357953 := bstep (se 2 (by rfl) ⟨134232, by rfl⟩ : syracuseStep 357953 = 268465) B268465
theorem B357971 : Blo 235815 357971 := bstep (se 1 (by rfl) ⟨268478, by rfl⟩ : syracuseStep 357971 = 536957) B536957
theorem B358001 : Blo 235815 358001 := bstep (se 2 (by rfl) ⟨134250, by rfl⟩ : syracuseStep 358001 = 268501) B268501
theorem B358019 : Blo 235815 358019 := bstep (se 1 (by rfl) ⟨268514, by rfl⟩ : syracuseStep 358019 = 537029) B537029
theorem B358049 : Blo 235815 358049 := bstep (se 2 (by rfl) ⟨134268, by rfl⟩ : syracuseStep 358049 = 268537) B268537
theorem B358067 : Blo 235815 358067 := bstep (se 1 (by rfl) ⟨268550, by rfl⟩ : syracuseStep 358067 = 537101) B537101
theorem B358097 : Blo 235815 358097 := bstep (se 2 (by rfl) ⟨134286, by rfl⟩ : syracuseStep 358097 = 268573) B268573
theorem B358115 : Blo 235815 358115 := bstep (se 1 (by rfl) ⟨268586, by rfl⟩ : syracuseStep 358115 = 537173) B537173
theorem B358145 : Blo 235815 358145 := bstep (se 2 (by rfl) ⟨134304, by rfl⟩ : syracuseStep 358145 = 268609) B268609
theorem B685837 : Blo 235815 685837 := bstep (se 3 (by rfl) ⟨128594, by rfl⟩ : syracuseStep 685837 = 257189) B257189
theorem B358163 : Blo 235815 358163 := bstep (se 1 (by rfl) ⟨268622, by rfl⟩ : syracuseStep 358163 = 537245) B537245
theorem B358193 : Blo 235815 358193 := bstep (se 2 (by rfl) ⟨134322, by rfl⟩ : syracuseStep 358193 = 268645) B268645
theorem B358211 : Blo 235815 358211 := bstep (se 1 (by rfl) ⟨268658, by rfl⟩ : syracuseStep 358211 = 537317) B537317
theorem B358241 : Blo 235815 358241 := bstep (se 2 (by rfl) ⟨134340, by rfl⟩ : syracuseStep 358241 = 268681) B268681
theorem B915299 : Blo 235815 915299 := bstep (se 1 (by rfl) ⟨686474, by rfl⟩ : syracuseStep 915299 = 1372949) B1372949
theorem B358259 : Blo 235815 358259 := bstep (se 1 (by rfl) ⟨268694, by rfl⟩ : syracuseStep 358259 = 537389) B537389
theorem B718733 : Blo 235815 718733 := bstep (se 3 (by rfl) ⟨134762, by rfl⟩ : syracuseStep 718733 = 269525) B269525
theorem B358289 : Blo 235815 358289 := bstep (se 2 (by rfl) ⟨134358, by rfl⟩ : syracuseStep 358289 = 268717) B268717
theorem B358307 : Blo 235815 358307 := bstep (se 1 (by rfl) ⟨268730, by rfl⟩ : syracuseStep 358307 = 537461) B537461
theorem B358337 : Blo 235815 358337 := bstep (se 2 (by rfl) ⟨134376, by rfl⟩ : syracuseStep 358337 = 268753) B268753
theorem B358355 : Blo 235815 358355 := bstep (se 1 (by rfl) ⟨268766, by rfl⟩ : syracuseStep 358355 = 537533) B537533
theorem B358385 : Blo 235815 358385 := bstep (se 2 (by rfl) ⟨134394, by rfl⟩ : syracuseStep 358385 = 268789) B268789
theorem B358403 : Blo 235815 358403 := bstep (se 1 (by rfl) ⟨268802, by rfl⟩ : syracuseStep 358403 = 537605) B537605
theorem B358433 : Blo 235815 358433 := bstep (se 2 (by rfl) ⟨134412, by rfl⟩ : syracuseStep 358433 = 268825) B268825
theorem B358451 : Blo 235815 358451 := bstep (se 1 (by rfl) ⟨268838, by rfl⟩ : syracuseStep 358451 = 537677) B537677
theorem B358481 : Blo 235815 358481 := bstep (se 2 (by rfl) ⟨134430, by rfl⟩ : syracuseStep 358481 = 268861) B268861
theorem B358499 : Blo 235815 358499 := bstep (se 1 (by rfl) ⟨268874, by rfl⟩ : syracuseStep 358499 = 537749) B537749
theorem B358529 : Blo 235815 358529 := bstep (se 2 (by rfl) ⟨134448, by rfl⟩ : syracuseStep 358529 = 268897) B268897
theorem B358547 : Blo 235815 358547 := bstep (se 1 (by rfl) ⟨268910, by rfl⟩ : syracuseStep 358547 = 537821) B537821
theorem B358577 : Blo 235815 358577 := bstep (se 2 (by rfl) ⟨134466, by rfl⟩ : syracuseStep 358577 = 268933) B268933
theorem B358595 : Blo 235815 358595 := bstep (se 1 (by rfl) ⟨268946, by rfl⟩ : syracuseStep 358595 = 537893) B537893
theorem B817361 : Blo 235815 817361 := bstep (se 2 (by rfl) ⟨306510, by rfl⟩ : syracuseStep 817361 = 613021) B613021
theorem B358625 : Blo 235815 358625 := bstep (se 2 (by rfl) ⟨134484, by rfl⟩ : syracuseStep 358625 = 268969) B268969
theorem B358643 : Blo 235815 358643 := bstep (se 1 (by rfl) ⟨268982, by rfl⟩ : syracuseStep 358643 = 537965) B537965
theorem B358673 : Blo 235815 358673 := bstep (se 2 (by rfl) ⟨134502, by rfl⟩ : syracuseStep 358673 = 269005) B269005
theorem B358691 : Blo 235815 358691 := bstep (se 1 (by rfl) ⟨269018, by rfl⟩ : syracuseStep 358691 = 538037) B538037
theorem B358721 : Blo 235815 358721 := bstep (se 2 (by rfl) ⟨134520, by rfl⟩ : syracuseStep 358721 = 269041) B269041
theorem B358739 : Blo 235815 358739 := bstep (se 1 (by rfl) ⟨269054, by rfl⟩ : syracuseStep 358739 = 538109) B538109
theorem B358769 : Blo 235815 358769 := bstep (se 2 (by rfl) ⟨134538, by rfl⟩ : syracuseStep 358769 = 269077) B269077
theorem B358787 : Blo 235815 358787 := bstep (se 1 (by rfl) ⟨269090, by rfl⟩ : syracuseStep 358787 = 538181) B538181
theorem B358817 : Blo 235815 358817 := bstep (se 2 (by rfl) ⟨134556, by rfl⟩ : syracuseStep 358817 = 269113) B269113
theorem B1210787 : Blo 235815 1210787 := bstep (se 1 (by rfl) ⟨908090, by rfl⟩ : syracuseStep 1210787 = 1816181) B1816181
theorem B358835 : Blo 235815 358835 := bstep (se 1 (by rfl) ⟨269126, by rfl⟩ : syracuseStep 358835 = 538253) B538253
theorem B1014221 : Blo 235815 1014221 := bstep (se 3 (by rfl) ⟨190166, by rfl⟩ : syracuseStep 1014221 = 380333) B380333
theorem B358865 : Blo 235815 358865 := bstep (se 2 (by rfl) ⟨134574, by rfl⟩ : syracuseStep 358865 = 269149) B269149
theorem B358883 : Blo 235815 358883 := bstep (se 1 (by rfl) ⟨269162, by rfl⟩ : syracuseStep 358883 = 538325) B538325
theorem B358913 : Blo 235815 358913 := bstep (se 2 (by rfl) ⟨134592, by rfl⟩ : syracuseStep 358913 = 269185) B269185
theorem B358931 : Blo 235815 358931 := bstep (se 1 (by rfl) ⟨269198, by rfl⟩ : syracuseStep 358931 = 538397) B538397
theorem B358961 : Blo 235815 358961 := bstep (se 2 (by rfl) ⟨134610, by rfl⟩ : syracuseStep 358961 = 269221) B269221
theorem B358979 : Blo 235815 358979 := bstep (se 1 (by rfl) ⟨269234, by rfl⟩ : syracuseStep 358979 = 538469) B538469
theorem B359009 : Blo 235815 359009 := bstep (se 2 (by rfl) ⟨134628, by rfl⟩ : syracuseStep 359009 = 269257) B269257
theorem B359027 : Blo 235815 359027 := bstep (se 1 (by rfl) ⟨269270, by rfl⟩ : syracuseStep 359027 = 538541) B538541
theorem B359057 : Blo 235815 359057 := bstep (se 2 (by rfl) ⟨134646, by rfl⟩ : syracuseStep 359057 = 269293) B269293
theorem B359075 : Blo 235815 359075 := bstep (se 1 (by rfl) ⟨269306, by rfl⟩ : syracuseStep 359075 = 538613) B538613
theorem B359105 : Blo 235815 359105 := bstep (se 2 (by rfl) ⟨134664, by rfl⟩ : syracuseStep 359105 = 269329) B269329
theorem B359123 : Blo 235815 359123 := bstep (se 1 (by rfl) ⟨269342, by rfl⟩ : syracuseStep 359123 = 538685) B538685
theorem B359153 : Blo 235815 359153 := bstep (se 2 (by rfl) ⟨134682, by rfl⟩ : syracuseStep 359153 = 269365) B269365
theorem B359171 : Blo 235815 359171 := bstep (se 1 (by rfl) ⟨269378, by rfl⟩ : syracuseStep 359171 = 538757) B538757
theorem B359201 : Blo 235815 359201 := bstep (se 2 (by rfl) ⟨134700, by rfl⟩ : syracuseStep 359201 = 269401) B269401
theorem B359219 : Blo 235815 359219 := bstep (se 1 (by rfl) ⟨269414, by rfl⟩ : syracuseStep 359219 = 538829) B538829
theorem B359249 : Blo 235815 359249 := bstep (se 2 (by rfl) ⟨134718, by rfl⟩ : syracuseStep 359249 = 269437) B269437
theorem B359267 : Blo 235815 359267 := bstep (se 1 (by rfl) ⟨269450, by rfl⟩ : syracuseStep 359267 = 538901) B538901
theorem B359297 : Blo 235815 359297 := bstep (se 2 (by rfl) ⟨134736, by rfl⟩ : syracuseStep 359297 = 269473) B269473
theorem B359315 : Blo 235815 359315 := bstep (se 1 (by rfl) ⟨269486, by rfl⟩ : syracuseStep 359315 = 538973) B538973
theorem B359345 : Blo 235815 359345 := bstep (se 2 (by rfl) ⟨134754, by rfl⟩ : syracuseStep 359345 = 269509) B269509
theorem B359363 : Blo 235815 359363 := bstep (se 1 (by rfl) ⟨269522, by rfl⟩ : syracuseStep 359363 = 539045) B539045
theorem B1702853 : Blo 235815 1702853 := bstep (se 4 (by rfl) ⟨159642, by rfl⟩ : syracuseStep 1702853 = 319285) B319285
theorem B359393 : Blo 235815 359393 := bstep (se 2 (by rfl) ⟨134772, by rfl⟩ : syracuseStep 359393 = 269545) B269545
theorem B359411 : Blo 235815 359411 := bstep (se 1 (by rfl) ⟨269558, by rfl⟩ : syracuseStep 359411 = 539117) B539117
theorem B359441 : Blo 235815 359441 := bstep (se 2 (by rfl) ⟨134790, by rfl⟩ : syracuseStep 359441 = 269581) B269581
theorem B359459 : Blo 235815 359459 := bstep (se 1 (by rfl) ⟨269594, by rfl⟩ : syracuseStep 359459 = 539189) B539189
theorem B359489 : Blo 235815 359489 := bstep (se 2 (by rfl) ⟨134808, by rfl⟩ : syracuseStep 359489 = 269617) B269617
theorem B359507 : Blo 235815 359507 := bstep (se 1 (by rfl) ⟨269630, by rfl⟩ : syracuseStep 359507 = 539261) B539261
theorem B359537 : Blo 235815 359537 := bstep (se 2 (by rfl) ⟨134826, by rfl⟩ : syracuseStep 359537 = 269653) B269653
theorem B359555 : Blo 235815 359555 := bstep (se 1 (by rfl) ⟨269666, by rfl⟩ : syracuseStep 359555 = 539333) B539333
theorem B359585 : Blo 235815 359585 := bstep (se 2 (by rfl) ⟨134844, by rfl⟩ : syracuseStep 359585 = 269689) B269689
theorem B359603 : Blo 235815 359603 := bstep (se 1 (by rfl) ⟨269702, by rfl⟩ : syracuseStep 359603 = 539405) B539405
theorem B1211597 : Blo 235815 1211597 := bstep (se 3 (by rfl) ⟨227174, by rfl⟩ : syracuseStep 1211597 = 454349) B454349
theorem B359633 : Blo 235815 359633 := bstep (se 2 (by rfl) ⟨134862, by rfl⟩ : syracuseStep 359633 = 269725) B269725
theorem B359651 : Blo 235815 359651 := bstep (se 1 (by rfl) ⟨269738, by rfl⟩ : syracuseStep 359651 = 539477) B539477
theorem B359681 : Blo 235815 359681 := bstep (se 2 (by rfl) ⟨134880, by rfl⟩ : syracuseStep 359681 = 269761) B269761
theorem B359699 : Blo 235815 359699 := bstep (se 1 (by rfl) ⟨269774, by rfl⟩ : syracuseStep 359699 = 539549) B539549
theorem B4914485 : Blo 235815 4914485 := bstep (se 5 (by rfl) ⟨230366, by rfl⟩ : syracuseStep 4914485 = 460733) B460733
theorem B4423025 : Blo 235815 4423025 := bstep (se 2 (by rfl) ⟨1658634, by rfl⟩ : syracuseStep 4423025 = 3317269) B3317269
theorem B3079565 : Blo 235815 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B3440069 : Blo 235815 3440069 := bstep (se 4 (by rfl) ⟨322506, by rfl⟩ : syracuseStep 3440069 = 645013) B645013
theorem B425425 : Blo 235815 425425 := bstep (se 2 (by rfl) ⟨159534, by rfl⟩ : syracuseStep 425425 = 319069) B319069
theorem B917219 : Blo 235815 917219 := bstep (se 1 (by rfl) ⟨687914, by rfl⟩ : syracuseStep 917219 = 1375829) B1375829
theorem B2031587 : Blo 235815 2031587 := bstep (se 1 (by rfl) ⟨1523690, by rfl⟩ : syracuseStep 2031587 = 3047381) B3047381
theorem B720971 : Blo 235815 720971 := bstep (se 1 (by rfl) ⟨540728, by rfl⟩ : syracuseStep 720971 = 1081457) B1081457
theorem B3276875 : Blo 235815 3276875 := bstep (se 1 (by rfl) ⟨2457656, by rfl⟩ : syracuseStep 3276875 = 4915313) B4915313
theorem B2031965 : Blo 235815 2031965 := bstep (se 3 (by rfl) ⟨380993, by rfl⟩ : syracuseStep 2031965 = 761987) B761987
theorem B2753041 : Blo 235815 2753041 := bstep (se 2 (by rfl) ⟨1032390, by rfl⟩ : syracuseStep 2753041 = 2064781) B2064781
theorem B1868579 : Blo 235815 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B459595 : Blo 235815 459595 := bstep (se 1 (by rfl) ⟨344696, by rfl⟩ : syracuseStep 459595 = 689393) B689393
theorem B361355 : Blo 235815 361355 := bstep (se 1 (by rfl) ⟨271016, by rfl⟩ : syracuseStep 361355 = 542033) B542033
theorem B853085 : Blo 235815 853085 := bstep (se 3 (by rfl) ⟨159953, by rfl⟩ : syracuseStep 853085 = 319907) B319907
theorem B853213 : Blo 235815 853213 := bstep (se 3 (by rfl) ⟨159977, by rfl⟩ : syracuseStep 853213 = 319955) B319955
theorem B1344869 : Blo 235815 1344869 := bstep (se 4 (by rfl) ⟨126081, by rfl⟩ : syracuseStep 1344869 = 252163) B252163
theorem B361945 : Blo 235815 361945 := bstep (se 2 (by rfl) ⟨135729, by rfl⟩ : syracuseStep 361945 = 271459) B271459
theorem B1214027 : Blo 235815 1214027 := bstep (se 1 (by rfl) ⟨910520, by rfl⟩ : syracuseStep 1214027 = 1821041) B1821041
theorem B1017623 : Blo 235815 1017623 := bstep (se 1 (by rfl) ⟨763217, by rfl⟩ : syracuseStep 1017623 = 1526435) B1526435
theorem B1181969 : Blo 235815 1181969 := bstep (se 2 (by rfl) ⟨443238, by rfl⟩ : syracuseStep 1181969 = 886477) B886477
theorem B3869045 : Blo 235815 3869045 := bstep (se 5 (by rfl) ⟨181361, by rfl⟩ : syracuseStep 3869045 = 362723) B362723
theorem B4983389 : Blo 235815 4983389 := bstep (se 3 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 4983389 = 1868771) B1868771
theorem B2690009 : Blo 235815 2690009 := bstep (se 2 (by rfl) ⟨1008753, by rfl⟩ : syracuseStep 2690009 = 2017507) B2017507
theorem B1149997 : Blo 235815 1149997 := bstep (se 3 (by rfl) ⟨215624, by rfl⟩ : syracuseStep 1149997 = 431249) B431249
theorem B265387 : Blo 235815 265387 := bstep (se 1 (by rfl) ⟨199040, by rfl⟩ : syracuseStep 265387 = 398081) B398081
theorem B1805489 : Blo 235815 1805489 := bstep (se 2 (by rfl) ⟨677058, by rfl⟩ : syracuseStep 1805489 = 1354117) B1354117
theorem B265495 : Blo 235815 265495 := bstep (se 1 (by rfl) ⟨199121, by rfl⟩ : syracuseStep 265495 = 398243) B398243
theorem B265675 : Blo 235815 265675 := bstep (se 1 (by rfl) ⟨199256, by rfl⟩ : syracuseStep 265675 = 398513) B398513
theorem B265783 : Blo 235815 265783 := bstep (se 1 (by rfl) ⟨199337, by rfl⟩ : syracuseStep 265783 = 398675) B398675
theorem B1019537 : Blo 235815 1019537 := bstep (se 2 (by rfl) ⟨382326, by rfl⟩ : syracuseStep 1019537 = 764653) B764653
theorem B1805975 : Blo 235815 1805975 := bstep (se 1 (by rfl) ⟨1354481, by rfl⟩ : syracuseStep 1805975 = 2708963) B2708963
theorem B265963 : Blo 235815 265963 := bstep (se 1 (by rfl) ⟨199472, by rfl⟩ : syracuseStep 265963 = 398945) B398945
theorem B266071 : Blo 235815 266071 := bstep (se 1 (by rfl) ⟨199553, by rfl⟩ : syracuseStep 266071 = 399107) B399107
theorem B266251 : Blo 235815 266251 := bstep (se 1 (by rfl) ⟨199688, by rfl⟩ : syracuseStep 266251 = 399377) B399377
theorem B266359 : Blo 235815 266359 := bstep (se 1 (by rfl) ⟨199769, by rfl⟩ : syracuseStep 266359 = 399539) B399539
theorem B266539 : Blo 235815 266539 := bstep (se 1 (by rfl) ⟨199904, by rfl⟩ : syracuseStep 266539 = 399809) B399809
theorem B266647 : Blo 235815 266647 := bstep (se 1 (by rfl) ⟨199985, by rfl⟩ : syracuseStep 266647 = 399971) B399971
theorem B299467 : Blo 235815 299467 := bstep (se 1 (by rfl) ⟨224600, by rfl⟩ : syracuseStep 299467 = 449201) B449201
theorem B430643 : Blo 235815 430643 := bstep (se 1 (by rfl) ⟨322982, by rfl⟩ : syracuseStep 430643 = 645965) B645965
theorem B266827 : Blo 235815 266827 := bstep (se 1 (by rfl) ⟨200120, by rfl⟩ : syracuseStep 266827 = 400241) B400241
theorem B1151581 : Blo 235815 1151581 := bstep (se 3 (by rfl) ⟨215921, by rfl⟩ : syracuseStep 1151581 = 431843) B431843
theorem B1020509 : Blo 235815 1020509 := bstep (se 3 (by rfl) ⟨191345, by rfl⟩ : syracuseStep 1020509 = 382691) B382691
theorem B266935 : Blo 235815 266935 := bstep (se 1 (by rfl) ⟨200201, by rfl⟩ : syracuseStep 266935 = 400403) B400403
theorem B398027 : Blo 235815 398027 := bstep (se 1 (by rfl) ⟨298520, by rfl⟩ : syracuseStep 398027 = 597041) B597041
theorem B1512209 : Blo 235815 1512209 := bstep (se 2 (by rfl) ⟨567078, by rfl⟩ : syracuseStep 1512209 = 1134157) B1134157
theorem B398155 : Blo 235815 398155 := bstep (se 1 (by rfl) ⟨298616, by rfl⟩ : syracuseStep 398155 = 597233) B597233
theorem B267115 : Blo 235815 267115 := bstep (se 1 (by rfl) ⟨200336, by rfl⟩ : syracuseStep 267115 = 400673) B400673
theorem B431041 : Blo 235815 431041 := bstep (se 2 (by rfl) ⟨161640, by rfl⟩ : syracuseStep 431041 = 323281) B323281
theorem B267223 : Blo 235815 267223 := bstep (se 1 (by rfl) ⟨200417, by rfl⟩ : syracuseStep 267223 = 400835) B400835
theorem B398297 : Blo 235815 398297 := bstep (se 2 (by rfl) ⟨149361, by rfl⟩ : syracuseStep 398297 = 298723) B298723
theorem B3052505 : Blo 235815 3052505 := bstep (se 2 (by rfl) ⟨1144689, by rfl⟩ : syracuseStep 3052505 = 2289379) B2289379
theorem B922699 : Blo 235815 922699 := bstep (se 1 (by rfl) ⟨692024, by rfl⟩ : syracuseStep 922699 = 1384049) B1384049
theorem B398425 : Blo 235815 398425 := bstep (se 2 (by rfl) ⟨149409, by rfl⟩ : syracuseStep 398425 = 298819) B298819
theorem B1840229 : Blo 235815 1840229 := bstep (se 4 (by rfl) ⟨172521, by rfl⟩ : syracuseStep 1840229 = 345043) B345043
theorem B267403 : Blo 235815 267403 := bstep (se 1 (by rfl) ⟨200552, by rfl⟩ : syracuseStep 267403 = 401105) B401105
theorem B267511 : Blo 235815 267511 := bstep (se 1 (by rfl) ⟨200633, by rfl⟩ : syracuseStep 267511 = 401267) B401267
theorem B857395 : Blo 235815 857395 := bstep (se 1 (by rfl) ⟨643046, by rfl⟩ : syracuseStep 857395 = 1286093) B1286093
theorem B300439 : Blo 235815 300439 := bstep (se 1 (by rfl) ⟨225329, by rfl⟩ : syracuseStep 300439 = 450659) B450659
theorem B267691 : Blo 235815 267691 := bstep (se 1 (by rfl) ⟨200768, by rfl⟩ : syracuseStep 267691 = 401537) B401537
theorem B267799 : Blo 235815 267799 := bstep (se 1 (by rfl) ⟨200849, by rfl⟩ : syracuseStep 267799 = 401699) B401699
theorem B431639 : Blo 235815 431639 := bstep (se 1 (by rfl) ⟨323729, by rfl⟩ : syracuseStep 431639 = 647459) B647459
theorem B2299427 : Blo 235815 2299427 := bstep (se 1 (by rfl) ⟨1724570, by rfl⟩ : syracuseStep 2299427 = 3449141) B3449141
theorem B759385 : Blo 235815 759385 := bstep (se 2 (by rfl) ⟨284769, by rfl⟩ : syracuseStep 759385 = 569539) B569539
theorem B398999 : Blo 235815 398999 := bstep (se 1 (by rfl) ⟨299249, by rfl⟩ : syracuseStep 398999 = 598499) B598499
theorem B267979 : Blo 235815 267979 := bstep (se 1 (by rfl) ⟨200984, by rfl⟩ : syracuseStep 267979 = 401969) B401969
theorem B399127 : Blo 235815 399127 := bstep (se 1 (by rfl) ⟨299345, by rfl⟩ : syracuseStep 399127 = 598691) B598691
theorem B268087 : Blo 235815 268087 := bstep (se 1 (by rfl) ⟨201065, by rfl⟩ : syracuseStep 268087 = 402131) B402131
theorem B1283971 : Blo 235815 1283971 := bstep (se 1 (by rfl) ⟨962978, by rfl⟩ : syracuseStep 1283971 = 1925957) B1925957
theorem B268267 : Blo 235815 268267 := bstep (se 1 (by rfl) ⟨201200, by rfl⟩ : syracuseStep 268267 = 402401) B402401
theorem B1021997 : Blo 235815 1021997 := bstep (se 3 (by rfl) ⟨191624, by rfl⟩ : syracuseStep 1021997 = 383249) B383249
theorem B268375 : Blo 235815 268375 := bstep (se 1 (by rfl) ⟨201281, by rfl⟩ : syracuseStep 268375 = 402563) B402563
theorem B530585 : Blo 235815 530585 := bstep (se 2 (by rfl) ⟨198969, by rfl⟩ : syracuseStep 530585 = 397939) B397939
theorem B956609 : Blo 235815 956609 := bstep (se 2 (by rfl) ⟨358728, by rfl⟩ : syracuseStep 956609 = 717457) B717457
theorem B301259 : Blo 235815 301259 := bstep (se 1 (by rfl) ⟨225944, by rfl⟩ : syracuseStep 301259 = 451889) B451889
theorem B825547 : Blo 235815 825547 := bstep (se 1 (by rfl) ⟨619160, by rfl⟩ : syracuseStep 825547 = 1238321) B1238321
theorem B530675 : Blo 235815 530675 := bstep (se 1 (by rfl) ⟨398006, by rfl⟩ : syracuseStep 530675 = 796013) B796013
theorem B268555 : Blo 235815 268555 := bstep (se 1 (by rfl) ⟨201416, by rfl⟩ : syracuseStep 268555 = 402833) B402833
theorem B530711 : Blo 235815 530711 := bstep (se 1 (by rfl) ⟨398033, by rfl⟩ : syracuseStep 530711 = 796067) B796067
theorem B235819 : Blo 235815 235819 := bstep (se 1 (by rfl) ⟨176864, by rfl⟩ : syracuseStep 235819 = 353729) B353729
theorem B235831 : Blo 235815 235831 := bstep (se 1 (by rfl) ⟨176873, by rfl⟩ : syracuseStep 235831 = 353747) B353747
theorem B235851 : Blo 235815 235851 := bstep (se 1 (by rfl) ⟨176888, by rfl⟩ : syracuseStep 235851 = 353777) B353777
theorem B235863 : Blo 235815 235863 := bstep (se 1 (by rfl) ⟨176897, by rfl⟩ : syracuseStep 235863 = 353795) B353795
theorem B235883 : Blo 235815 235883 := bstep (se 1 (by rfl) ⟨176912, by rfl⟩ : syracuseStep 235883 = 353825) B353825
theorem B235895 : Blo 235815 235895 := bstep (se 1 (by rfl) ⟨176921, by rfl⟩ : syracuseStep 235895 = 353843) B353843
theorem B268663 : Blo 235815 268663 := bstep (se 1 (by rfl) ⟨201497, by rfl⟩ : syracuseStep 268663 = 402995) B402995
theorem B235915 : Blo 235815 235915 := bstep (se 1 (by rfl) ⟨176936, by rfl⟩ : syracuseStep 235915 = 353873) B353873
theorem B399755 : Blo 235815 399755 := bstep (se 1 (by rfl) ⟨299816, by rfl⟩ : syracuseStep 399755 = 599633) B599633
theorem B235927 : Blo 235815 235927 := bstep (se 1 (by rfl) ⟨176945, by rfl⟩ : syracuseStep 235927 = 353891) B353891
theorem B235947 : Blo 235815 235947 := bstep (se 1 (by rfl) ⟨176960, by rfl⟩ : syracuseStep 235947 = 353921) B353921
theorem B235959 : Blo 235815 235959 := bstep (se 1 (by rfl) ⟨176969, by rfl⟩ : syracuseStep 235959 = 353939) B353939
theorem B530891 : Blo 235815 530891 := bstep (se 1 (by rfl) ⟨398168, by rfl⟩ : syracuseStep 530891 = 796337) B796337
theorem B235979 : Blo 235815 235979 := bstep (se 1 (by rfl) ⟨176984, by rfl⟩ : syracuseStep 235979 = 353969) B353969
theorem B235991 : Blo 235815 235991 := bstep (se 1 (by rfl) ⟨176993, by rfl⟩ : syracuseStep 235991 = 353987) B353987
theorem B236011 : Blo 235815 236011 := bstep (se 1 (by rfl) ⟨177008, by rfl⟩ : syracuseStep 236011 = 354017) B354017
theorem B236023 : Blo 235815 236023 := bstep (se 1 (by rfl) ⟨177017, by rfl⟩ : syracuseStep 236023 = 354035) B354035
theorem B530945 : Blo 235815 530945 := bstep (se 2 (by rfl) ⟨199104, by rfl⟩ : syracuseStep 530945 = 398209) B398209
theorem B236043 : Blo 235815 236043 := bstep (se 1 (by rfl) ⟨177032, by rfl⟩ : syracuseStep 236043 = 354065) B354065
theorem B399883 : Blo 235815 399883 := bstep (se 1 (by rfl) ⟨299912, by rfl⟩ : syracuseStep 399883 = 599825) B599825
theorem B236055 : Blo 235815 236055 := bstep (se 1 (by rfl) ⟨177041, by rfl⟩ : syracuseStep 236055 = 354083) B354083
theorem B236075 : Blo 235815 236075 := bstep (se 1 (by rfl) ⟨177056, by rfl⟩ : syracuseStep 236075 = 354113) B354113
theorem B268843 : Blo 235815 268843 := bstep (se 1 (by rfl) ⟨201632, by rfl⟩ : syracuseStep 268843 = 403265) B403265
theorem B236087 : Blo 235815 236087 := bstep (se 1 (by rfl) ⟨177065, by rfl⟩ : syracuseStep 236087 = 354131) B354131
theorem B236107 : Blo 235815 236107 := bstep (se 1 (by rfl) ⟨177080, by rfl⟩ : syracuseStep 236107 = 354161) B354161
theorem B236119 : Blo 235815 236119 := bstep (se 1 (by rfl) ⟨177089, by rfl⟩ : syracuseStep 236119 = 354179) B354179
theorem B236139 : Blo 235815 236139 := bstep (se 1 (by rfl) ⟨177104, by rfl⟩ : syracuseStep 236139 = 354209) B354209
theorem B236151 : Blo 235815 236151 := bstep (se 1 (by rfl) ⟨177113, by rfl⟩ : syracuseStep 236151 = 354227) B354227
theorem B7740035 : Blo 235815 7740035 := bstep (se 1 (by rfl) ⟨5805026, by rfl⟩ : syracuseStep 7740035 = 11610053) B11610053
theorem B236171 : Blo 235815 236171 := bstep (se 1 (by rfl) ⟨177128, by rfl⟩ : syracuseStep 236171 = 354257) B354257
theorem B236183 : Blo 235815 236183 := bstep (se 1 (by rfl) ⟨177137, by rfl⟩ : syracuseStep 236183 = 354275) B354275
theorem B268951 : Blo 235815 268951 := bstep (se 1 (by rfl) ⟨201713, by rfl⟩ : syracuseStep 268951 = 403427) B403427
theorem B400025 : Blo 235815 400025 := bstep (se 2 (by rfl) ⟨150009, by rfl⟩ : syracuseStep 400025 = 300019) B300019
theorem B236203 : Blo 235815 236203 := bstep (se 1 (by rfl) ⟨177152, by rfl⟩ : syracuseStep 236203 = 354305) B354305
theorem B236215 : Blo 235815 236215 := bstep (se 1 (by rfl) ⟨177161, by rfl⟩ : syracuseStep 236215 = 354323) B354323
theorem B236235 : Blo 235815 236235 := bstep (se 1 (by rfl) ⟨177176, by rfl⟩ : syracuseStep 236235 = 354353) B354353
theorem B236247 : Blo 235815 236247 := bstep (se 1 (by rfl) ⟨177185, by rfl⟩ : syracuseStep 236247 = 354371) B354371
theorem B531161 : Blo 235815 531161 := bstep (se 2 (by rfl) ⟨199185, by rfl⟩ : syracuseStep 531161 = 398371) B398371
theorem B236267 : Blo 235815 236267 := bstep (se 1 (by rfl) ⟨177200, by rfl⟩ : syracuseStep 236267 = 354401) B354401
theorem B236279 : Blo 235815 236279 := bstep (se 1 (by rfl) ⟨177209, by rfl⟩ : syracuseStep 236279 = 354419) B354419
theorem B236299 : Blo 235815 236299 := bstep (se 1 (by rfl) ⟨177224, by rfl⟩ : syracuseStep 236299 = 354449) B354449
theorem B236311 : Blo 235815 236311 := bstep (se 1 (by rfl) ⟨177233, by rfl⟩ : syracuseStep 236311 = 354467) B354467
theorem B400153 : Blo 235815 400153 := bstep (se 2 (by rfl) ⟨150057, by rfl⟩ : syracuseStep 400153 = 300115) B300115
theorem B236331 : Blo 235815 236331 := bstep (se 1 (by rfl) ⟨177248, by rfl⟩ : syracuseStep 236331 = 354497) B354497
theorem B531251 : Blo 235815 531251 := bstep (se 1 (by rfl) ⟨398438, by rfl⟩ : syracuseStep 531251 = 796877) B796877
theorem B236343 : Blo 235815 236343 := bstep (se 1 (by rfl) ⟨177257, by rfl⟩ : syracuseStep 236343 = 354515) B354515
theorem B236363 : Blo 235815 236363 := bstep (se 1 (by rfl) ⟨177272, by rfl⟩ : syracuseStep 236363 = 354545) B354545
theorem B269131 : Blo 235815 269131 := bstep (se 1 (by rfl) ⟨201848, by rfl⟩ : syracuseStep 269131 = 403697) B403697
theorem B531287 : Blo 235815 531287 := bstep (se 1 (by rfl) ⟨398465, by rfl⟩ : syracuseStep 531287 = 796931) B796931
theorem B236375 : Blo 235815 236375 := bstep (se 1 (by rfl) ⟨177281, by rfl⟩ : syracuseStep 236375 = 354563) B354563
theorem B236395 : Blo 235815 236395 := bstep (se 1 (by rfl) ⟨177296, by rfl⟩ : syracuseStep 236395 = 354593) B354593
theorem B236407 : Blo 235815 236407 := bstep (se 1 (by rfl) ⟨177305, by rfl⟩ : syracuseStep 236407 = 354611) B354611
theorem B236427 : Blo 235815 236427 := bstep (se 1 (by rfl) ⟨177320, by rfl⟩ : syracuseStep 236427 = 354641) B354641
theorem B301963 : Blo 235815 301963 := bstep (se 1 (by rfl) ⟨226472, by rfl⟩ : syracuseStep 301963 = 452945) B452945
theorem B236439 : Blo 235815 236439 := bstep (se 1 (by rfl) ⟨177329, by rfl⟩ : syracuseStep 236439 = 354659) B354659
theorem B236459 : Blo 235815 236459 := bstep (se 1 (by rfl) ⟨177344, by rfl⟩ : syracuseStep 236459 = 354689) B354689
theorem B236471 : Blo 235815 236471 := bstep (se 1 (by rfl) ⟨177353, by rfl⟩ : syracuseStep 236471 = 354707) B354707
theorem B269239 : Blo 235815 269239 := bstep (se 1 (by rfl) ⟨201929, by rfl⟩ : syracuseStep 269239 = 403859) B403859
theorem B596929 : Blo 235815 596929 := bstep (se 2 (by rfl) ⟨223848, by rfl⟩ : syracuseStep 596929 = 447697) B447697
theorem B760769 : Blo 235815 760769 := bstep (se 2 (by rfl) ⟨285288, by rfl⟩ : syracuseStep 760769 = 570577) B570577
theorem B236491 : Blo 235815 236491 := bstep (se 1 (by rfl) ⟨177368, by rfl⟩ : syracuseStep 236491 = 354737) B354737
theorem B236503 : Blo 235815 236503 := bstep (se 1 (by rfl) ⟨177377, by rfl⟩ : syracuseStep 236503 = 354755) B354755
theorem B236523 : Blo 235815 236523 := bstep (se 1 (by rfl) ⟨177392, by rfl⟩ : syracuseStep 236523 = 354785) B354785
theorem B236535 : Blo 235815 236535 := bstep (se 1 (by rfl) ⟨177401, by rfl⟩ : syracuseStep 236535 = 354803) B354803
theorem B531467 : Blo 235815 531467 := bstep (se 1 (by rfl) ⟨398600, by rfl⟩ : syracuseStep 531467 = 797201) B797201
theorem B236555 : Blo 235815 236555 := bstep (se 1 (by rfl) ⟨177416, by rfl⟩ : syracuseStep 236555 = 354833) B354833
theorem B236567 : Blo 235815 236567 := bstep (se 1 (by rfl) ⟨177425, by rfl⟩ : syracuseStep 236567 = 354851) B354851
theorem B236587 : Blo 235815 236587 := bstep (se 1 (by rfl) ⟨177440, by rfl⟩ : syracuseStep 236587 = 354881) B354881
theorem B1350701 : Blo 235815 1350701 := bstep (se 3 (by rfl) ⟨253256, by rfl⟩ : syracuseStep 1350701 = 506513) B506513
theorem B236599 : Blo 235815 236599 := bstep (se 1 (by rfl) ⟨177449, by rfl⟩ : syracuseStep 236599 = 354899) B354899
theorem B531521 : Blo 235815 531521 := bstep (se 2 (by rfl) ⟨199320, by rfl⟩ : syracuseStep 531521 = 398641) B398641
theorem B236619 : Blo 235815 236619 := bstep (se 1 (by rfl) ⟨177464, by rfl⟩ : syracuseStep 236619 = 354929) B354929
theorem B859211 : Blo 235815 859211 := bstep (se 1 (by rfl) ⟨644408, by rfl⟩ : syracuseStep 859211 = 1288817) B1288817
theorem B236631 : Blo 235815 236631 := bstep (se 1 (by rfl) ⟨177473, by rfl⟩ : syracuseStep 236631 = 354947) B354947
theorem B236651 : Blo 235815 236651 := bstep (se 1 (by rfl) ⟨177488, by rfl⟩ : syracuseStep 236651 = 354977) B354977
theorem B269419 : Blo 235815 269419 := bstep (se 1 (by rfl) ⟨202064, by rfl⟩ : syracuseStep 269419 = 404129) B404129
theorem B236663 : Blo 235815 236663 := bstep (se 1 (by rfl) ⟨177497, by rfl⟩ : syracuseStep 236663 = 354995) B354995
theorem B236683 : Blo 235815 236683 := bstep (se 1 (by rfl) ⟨177512, by rfl⟩ : syracuseStep 236683 = 355025) B355025
theorem B236695 : Blo 235815 236695 := bstep (se 1 (by rfl) ⟨177521, by rfl⟩ : syracuseStep 236695 = 355043) B355043
theorem B302231 : Blo 235815 302231 := bstep (se 1 (by rfl) ⟨226673, by rfl⟩ : syracuseStep 302231 = 453347) B453347
theorem B236715 : Blo 235815 236715 := bstep (se 1 (by rfl) ⟨177536, by rfl⟩ : syracuseStep 236715 = 355073) B355073
theorem B236727 : Blo 235815 236727 := bstep (se 1 (by rfl) ⟨177545, by rfl⟩ : syracuseStep 236727 = 355091) B355091
theorem B236747 : Blo 235815 236747 := bstep (se 1 (by rfl) ⟨177560, by rfl⟩ : syracuseStep 236747 = 355121) B355121
theorem B236759 : Blo 235815 236759 := bstep (se 1 (by rfl) ⟨177569, by rfl⟩ : syracuseStep 236759 = 355139) B355139
theorem B269527 : Blo 235815 269527 := bstep (se 1 (by rfl) ⟨202145, by rfl⟩ : syracuseStep 269527 = 404291) B404291
theorem B236779 : Blo 235815 236779 := bstep (se 1 (by rfl) ⟨177584, by rfl⟩ : syracuseStep 236779 = 355169) B355169
theorem B236791 : Blo 235815 236791 := bstep (se 1 (by rfl) ⟨177593, by rfl⟩ : syracuseStep 236791 = 355187) B355187
theorem B236811 : Blo 235815 236811 := bstep (se 1 (by rfl) ⟨177608, by rfl⟩ : syracuseStep 236811 = 355217) B355217
theorem B236823 : Blo 235815 236823 := bstep (se 1 (by rfl) ⟨177617, by rfl⟩ : syracuseStep 236823 = 355235) B355235
theorem B531737 : Blo 235815 531737 := bstep (se 2 (by rfl) ⟨199401, by rfl⟩ : syracuseStep 531737 = 398803) B398803
theorem B236843 : Blo 235815 236843 := bstep (se 1 (by rfl) ⟨177632, by rfl⟩ : syracuseStep 236843 = 355265) B355265
theorem B236855 : Blo 235815 236855 := bstep (se 1 (by rfl) ⟨177641, by rfl⟩ : syracuseStep 236855 = 355283) B355283
theorem B236875 : Blo 235815 236875 := bstep (se 1 (by rfl) ⟨177656, by rfl⟩ : syracuseStep 236875 = 355313) B355313
theorem B236887 : Blo 235815 236887 := bstep (se 1 (by rfl) ⟨177665, by rfl⟩ : syracuseStep 236887 = 355331) B355331
theorem B400727 : Blo 235815 400727 := bstep (se 1 (by rfl) ⟨300545, by rfl⟩ : syracuseStep 400727 = 601091) B601091
theorem B236907 : Blo 235815 236907 := bstep (se 1 (by rfl) ⟨177680, by rfl⟩ : syracuseStep 236907 = 355361) B355361
theorem B531827 : Blo 235815 531827 := bstep (se 1 (by rfl) ⟨398870, by rfl⟩ : syracuseStep 531827 = 797741) B797741
theorem B236919 : Blo 235815 236919 := bstep (se 1 (by rfl) ⟨177689, by rfl⟩ : syracuseStep 236919 = 355379) B355379
theorem B236939 : Blo 235815 236939 := bstep (se 1 (by rfl) ⟨177704, by rfl⟩ : syracuseStep 236939 = 355409) B355409
theorem B269707 : Blo 235815 269707 := bstep (se 1 (by rfl) ⟨202280, by rfl⟩ : syracuseStep 269707 = 404561) B404561
theorem B531863 : Blo 235815 531863 := bstep (se 1 (by rfl) ⟨398897, by rfl⟩ : syracuseStep 531863 = 797795) B797795
theorem B236951 : Blo 235815 236951 := bstep (se 1 (by rfl) ⟨177713, by rfl⟩ : syracuseStep 236951 = 355427) B355427
theorem B236971 : Blo 235815 236971 := bstep (se 1 (by rfl) ⟨177728, by rfl⟩ : syracuseStep 236971 = 355457) B355457
theorem B236983 : Blo 235815 236983 := bstep (se 1 (by rfl) ⟨177737, by rfl⟩ : syracuseStep 236983 = 355475) B355475
theorem B237003 : Blo 235815 237003 := bstep (se 1 (by rfl) ⟨177752, by rfl⟩ : syracuseStep 237003 = 355505) B355505
theorem B237015 : Blo 235815 237015 := bstep (se 1 (by rfl) ⟨177761, by rfl⟩ : syracuseStep 237015 = 355523) B355523
theorem B400855 : Blo 235815 400855 := bstep (se 1 (by rfl) ⟨300641, by rfl⟩ : syracuseStep 400855 = 601283) B601283
theorem B761309 : Blo 235815 761309 := bstep (se 3 (by rfl) ⟨142745, by rfl⟩ : syracuseStep 761309 = 285491) B285491
theorem B237035 : Blo 235815 237035 := bstep (se 1 (by rfl) ⟨177776, by rfl⟩ : syracuseStep 237035 = 355553) B355553
theorem B237047 : Blo 235815 237047 := bstep (se 1 (by rfl) ⟨177785, by rfl⟩ : syracuseStep 237047 = 355571) B355571
theorem B237067 : Blo 235815 237067 := bstep (se 1 (by rfl) ⟨177800, by rfl⟩ : syracuseStep 237067 = 355601) B355601
theorem B597527 : Blo 235815 597527 := bstep (se 1 (by rfl) ⟨448145, by rfl⟩ : syracuseStep 597527 = 896291) B896291
theorem B237079 : Blo 235815 237079 := bstep (se 1 (by rfl) ⟨177809, by rfl⟩ : syracuseStep 237079 = 355619) B355619
theorem B237099 : Blo 235815 237099 := bstep (se 1 (by rfl) ⟨177824, by rfl⟩ : syracuseStep 237099 = 355649) B355649
theorem B237111 : Blo 235815 237111 := bstep (se 1 (by rfl) ⟨177833, by rfl⟩ : syracuseStep 237111 = 355667) B355667
theorem B532043 : Blo 235815 532043 := bstep (se 1 (by rfl) ⟨399032, by rfl⟩ : syracuseStep 532043 = 798065) B798065
theorem B237131 : Blo 235815 237131 := bstep (se 1 (by rfl) ⟨177848, by rfl⟩ : syracuseStep 237131 = 355697) B355697
theorem B237143 : Blo 235815 237143 := bstep (se 1 (by rfl) ⟨177857, by rfl⟩ : syracuseStep 237143 = 355715) B355715
theorem B237163 : Blo 235815 237163 := bstep (se 1 (by rfl) ⟨177872, by rfl⟩ : syracuseStep 237163 = 355745) B355745
theorem B237175 : Blo 235815 237175 := bstep (se 1 (by rfl) ⟨177881, by rfl⟩ : syracuseStep 237175 = 355763) B355763
theorem B532097 : Blo 235815 532097 := bstep (se 2 (by rfl) ⟨199536, by rfl⟩ : syracuseStep 532097 = 399073) B399073
theorem B237195 : Blo 235815 237195 := bstep (se 1 (by rfl) ⟨177896, by rfl⟩ : syracuseStep 237195 = 355793) B355793
theorem B237207 : Blo 235815 237207 := bstep (se 1 (by rfl) ⟨177905, by rfl⟩ : syracuseStep 237207 = 355811) B355811
theorem B237227 : Blo 235815 237227 := bstep (se 1 (by rfl) ⟨177920, by rfl⟩ : syracuseStep 237227 = 355841) B355841
theorem B237239 : Blo 235815 237239 := bstep (se 1 (by rfl) ⟨177929, by rfl⟩ : syracuseStep 237239 = 355859) B355859
theorem B237259 : Blo 235815 237259 := bstep (se 1 (by rfl) ⟨177944, by rfl⟩ : syracuseStep 237259 = 355889) B355889
theorem B237271 : Blo 235815 237271 := bstep (se 1 (by rfl) ⟨177953, by rfl⟩ : syracuseStep 237271 = 355907) B355907
theorem B237291 : Blo 235815 237291 := bstep (se 1 (by rfl) ⟨177968, by rfl⟩ : syracuseStep 237291 = 355937) B355937
theorem B237303 : Blo 235815 237303 := bstep (se 1 (by rfl) ⟨177977, by rfl⟩ : syracuseStep 237303 = 355955) B355955
theorem B270091 : Blo 235815 270091 := bstep (se 1 (by rfl) ⟨202568, by rfl⟩ : syracuseStep 270091 = 405137) B405137
theorem B237323 : Blo 235815 237323 := bstep (se 1 (by rfl) ⟨177992, by rfl⟩ : syracuseStep 237323 = 355985) B355985
theorem B237335 : Blo 235815 237335 := bstep (se 1 (by rfl) ⟨178001, by rfl⟩ : syracuseStep 237335 = 356003) B356003
theorem B237355 : Blo 235815 237355 := bstep (se 1 (by rfl) ⟨178016, by rfl⟩ : syracuseStep 237355 = 356033) B356033
theorem B237367 : Blo 235815 237367 := bstep (se 1 (by rfl) ⟨178025, by rfl⟩ : syracuseStep 237367 = 356051) B356051
theorem B237387 : Blo 235815 237387 := bstep (se 1 (by rfl) ⟨178040, by rfl⟩ : syracuseStep 237387 = 356081) B356081
theorem B237399 : Blo 235815 237399 := bstep (se 1 (by rfl) ⟨178049, by rfl⟩ : syracuseStep 237399 = 356099) B356099
theorem B532313 : Blo 235815 532313 := bstep (se 2 (by rfl) ⟨199617, by rfl⟩ : syracuseStep 532313 = 399235) B399235
theorem B302935 : Blo 235815 302935 := bstep (se 1 (by rfl) ⟨227201, by rfl⟩ : syracuseStep 302935 = 454403) B454403
theorem B237419 : Blo 235815 237419 := bstep (se 1 (by rfl) ⟨178064, by rfl⟩ : syracuseStep 237419 = 356129) B356129
theorem B237431 : Blo 235815 237431 := bstep (se 1 (by rfl) ⟨178073, by rfl⟩ : syracuseStep 237431 = 356147) B356147
theorem B1613699 : Blo 235815 1613699 := bstep (se 1 (by rfl) ⟨1210274, by rfl⟩ : syracuseStep 1613699 = 2420549) B2420549
theorem B237451 : Blo 235815 237451 := bstep (se 1 (by rfl) ⟨178088, by rfl⟩ : syracuseStep 237451 = 356177) B356177
theorem B237463 : Blo 235815 237463 := bstep (se 1 (by rfl) ⟨178097, by rfl⟩ : syracuseStep 237463 = 356195) B356195
theorem B237483 : Blo 235815 237483 := bstep (se 1 (by rfl) ⟨178112, by rfl⟩ : syracuseStep 237483 = 356225) B356225
theorem B532403 : Blo 235815 532403 := bstep (se 1 (by rfl) ⟨399302, by rfl⟩ : syracuseStep 532403 = 798605) B798605
theorem B237495 : Blo 235815 237495 := bstep (se 1 (by rfl) ⟨178121, by rfl⟩ : syracuseStep 237495 = 356243) B356243
theorem B237515 : Blo 235815 237515 := bstep (se 1 (by rfl) ⟨178136, by rfl⟩ : syracuseStep 237515 = 356273) B356273
theorem B532439 : Blo 235815 532439 := bstep (se 1 (by rfl) ⟨399329, by rfl⟩ : syracuseStep 532439 = 798659) B798659
theorem B237527 : Blo 235815 237527 := bstep (se 1 (by rfl) ⟨178145, by rfl⟩ : syracuseStep 237527 = 356291) B356291
theorem B1023961 : Blo 235815 1023961 := bstep (se 2 (by rfl) ⟨383985, by rfl⟩ : syracuseStep 1023961 = 767971) B767971
theorem B237547 : Blo 235815 237547 := bstep (se 1 (by rfl) ⟨178160, by rfl⟩ : syracuseStep 237547 = 356321) B356321
theorem B237559 : Blo 235815 237559 := bstep (se 1 (by rfl) ⟨178169, by rfl⟩ : syracuseStep 237559 = 356339) B356339
theorem B237579 : Blo 235815 237579 := bstep (se 1 (by rfl) ⟨178184, by rfl⟩ : syracuseStep 237579 = 356369) B356369
theorem B237591 : Blo 235815 237591 := bstep (se 1 (by rfl) ⟨178193, by rfl⟩ : syracuseStep 237591 = 356387) B356387
theorem B237611 : Blo 235815 237611 := bstep (se 1 (by rfl) ⟨178208, by rfl⟩ : syracuseStep 237611 = 356417) B356417
theorem B237623 : Blo 235815 237623 := bstep (se 1 (by rfl) ⟨178217, by rfl⟩ : syracuseStep 237623 = 356435) B356435
theorem B237643 : Blo 235815 237643 := bstep (se 1 (by rfl) ⟨178232, by rfl⟩ : syracuseStep 237643 = 356465) B356465
theorem B401483 : Blo 235815 401483 := bstep (se 1 (by rfl) ⟨301112, by rfl⟩ : syracuseStep 401483 = 602225) B602225
theorem B237655 : Blo 235815 237655 := bstep (se 1 (by rfl) ⟨178241, by rfl⟩ : syracuseStep 237655 = 356483) B356483
theorem B237675 : Blo 235815 237675 := bstep (se 1 (by rfl) ⟨178256, by rfl⟩ : syracuseStep 237675 = 356513) B356513
theorem B237687 : Blo 235815 237687 := bstep (se 1 (by rfl) ⟨178265, by rfl⟩ : syracuseStep 237687 = 356531) B356531
theorem B532619 : Blo 235815 532619 := bstep (se 1 (by rfl) ⟨399464, by rfl⟩ : syracuseStep 532619 = 798929) B798929
theorem B237707 : Blo 235815 237707 := bstep (se 1 (by rfl) ⟨178280, by rfl⟩ : syracuseStep 237707 = 356561) B356561
theorem B237719 : Blo 235815 237719 := bstep (se 1 (by rfl) ⟨178289, by rfl⟩ : syracuseStep 237719 = 356579) B356579
theorem B237739 : Blo 235815 237739 := bstep (se 1 (by rfl) ⟨178304, by rfl⟩ : syracuseStep 237739 = 356609) B356609
theorem B237751 : Blo 235815 237751 := bstep (se 1 (by rfl) ⟨178313, by rfl⟩ : syracuseStep 237751 = 356627) B356627
theorem B532673 : Blo 235815 532673 := bstep (se 2 (by rfl) ⟨199752, by rfl⟩ : syracuseStep 532673 = 399505) B399505
theorem B237771 : Blo 235815 237771 := bstep (se 1 (by rfl) ⟨178328, by rfl⟩ : syracuseStep 237771 = 356657) B356657
theorem B401611 : Blo 235815 401611 := bstep (se 1 (by rfl) ⟨301208, by rfl⟩ : syracuseStep 401611 = 602417) B602417
theorem B860363 : Blo 235815 860363 := bstep (se 1 (by rfl) ⟨645272, by rfl⟩ : syracuseStep 860363 = 1290545) B1290545
theorem B237783 : Blo 235815 237783 := bstep (se 1 (by rfl) ⟨178337, by rfl⟩ : syracuseStep 237783 = 356675) B356675
theorem B237803 : Blo 235815 237803 := bstep (se 1 (by rfl) ⟨178352, by rfl⟩ : syracuseStep 237803 = 356705) B356705
theorem B237815 : Blo 235815 237815 := bstep (se 1 (by rfl) ⟨178361, by rfl⟩ : syracuseStep 237815 = 356723) B356723
theorem B237835 : Blo 235815 237835 := bstep (se 1 (by rfl) ⟨178376, by rfl⟩ : syracuseStep 237835 = 356753) B356753
theorem B237847 : Blo 235815 237847 := bstep (se 1 (by rfl) ⟨178385, by rfl⟩ : syracuseStep 237847 = 356771) B356771
theorem B237867 : Blo 235815 237867 := bstep (se 1 (by rfl) ⟨178400, by rfl⟩ : syracuseStep 237867 = 356801) B356801
theorem B237879 : Blo 235815 237879 := bstep (se 1 (by rfl) ⟨178409, by rfl⟩ : syracuseStep 237879 = 356819) B356819
theorem B598337 : Blo 235815 598337 := bstep (se 2 (by rfl) ⟨224376, by rfl⟩ : syracuseStep 598337 = 448753) B448753
theorem B237899 : Blo 235815 237899 := bstep (se 1 (by rfl) ⟨178424, by rfl⟩ : syracuseStep 237899 = 356849) B356849
theorem B237911 : Blo 235815 237911 := bstep (se 1 (by rfl) ⟨178433, by rfl⟩ : syracuseStep 237911 = 356867) B356867
theorem B401753 : Blo 235815 401753 := bstep (se 2 (by rfl) ⟨150657, by rfl⟩ : syracuseStep 401753 = 301315) B301315
theorem B237931 : Blo 235815 237931 := bstep (se 1 (by rfl) ⟨178448, by rfl⟩ : syracuseStep 237931 = 356897) B356897
theorem B237943 : Blo 235815 237943 := bstep (se 1 (by rfl) ⟨178457, by rfl⟩ : syracuseStep 237943 = 356915) B356915
theorem B237963 : Blo 235815 237963 := bstep (se 1 (by rfl) ⟨178472, by rfl⟩ : syracuseStep 237963 = 356945) B356945
theorem B237975 : Blo 235815 237975 := bstep (se 1 (by rfl) ⟨178481, by rfl⟩ : syracuseStep 237975 = 356963) B356963
theorem B532889 : Blo 235815 532889 := bstep (se 2 (by rfl) ⟨199833, by rfl⟩ : syracuseStep 532889 = 399667) B399667
theorem B237995 : Blo 235815 237995 := bstep (se 1 (by rfl) ⟨178496, by rfl⟩ : syracuseStep 237995 = 356993) B356993
theorem B238007 : Blo 235815 238007 := bstep (se 1 (by rfl) ⟨178505, by rfl⟩ : syracuseStep 238007 = 357011) B357011
theorem B238027 : Blo 235815 238027 := bstep (se 1 (by rfl) ⟨178520, by rfl⟩ : syracuseStep 238027 = 357041) B357041
theorem B238039 : Blo 235815 238039 := bstep (se 1 (by rfl) ⟨178529, by rfl⟩ : syracuseStep 238039 = 357059) B357059
theorem B401881 : Blo 235815 401881 := bstep (se 2 (by rfl) ⟨150705, by rfl⟩ : syracuseStep 401881 = 301411) B301411
theorem B238059 : Blo 235815 238059 := bstep (se 1 (by rfl) ⟨178544, by rfl⟩ : syracuseStep 238059 = 357089) B357089
theorem B532979 : Blo 235815 532979 := bstep (se 1 (by rfl) ⟨399734, by rfl⟩ : syracuseStep 532979 = 799469) B799469
theorem B238071 : Blo 235815 238071 := bstep (se 1 (by rfl) ⟨178553, by rfl⟩ : syracuseStep 238071 = 357107) B357107
theorem B238091 : Blo 235815 238091 := bstep (se 1 (by rfl) ⟨178568, by rfl⟩ : syracuseStep 238091 = 357137) B357137
theorem B533015 : Blo 235815 533015 := bstep (se 1 (by rfl) ⟨399761, by rfl⟩ : syracuseStep 533015 = 799523) B799523
theorem B238103 : Blo 235815 238103 := bstep (se 1 (by rfl) ⟨178577, by rfl⟩ : syracuseStep 238103 = 357155) B357155
theorem B238123 : Blo 235815 238123 := bstep (se 1 (by rfl) ⟨178592, by rfl⟩ : syracuseStep 238123 = 357185) B357185
theorem B238135 : Blo 235815 238135 := bstep (se 1 (by rfl) ⟨178601, by rfl⟩ : syracuseStep 238135 = 357203) B357203
theorem B238155 : Blo 235815 238155 := bstep (se 1 (by rfl) ⟨178616, by rfl⟩ : syracuseStep 238155 = 357233) B357233
theorem B238167 : Blo 235815 238167 := bstep (se 1 (by rfl) ⟨178625, by rfl⟩ : syracuseStep 238167 = 357251) B357251
theorem B238187 : Blo 235815 238187 := bstep (se 1 (by rfl) ⟨178640, by rfl⟩ : syracuseStep 238187 = 357281) B357281
theorem B238199 : Blo 235815 238199 := bstep (se 1 (by rfl) ⟨178649, by rfl⟩ : syracuseStep 238199 = 357299) B357299
theorem B1712771 : Blo 235815 1712771 := bstep (se 1 (by rfl) ⟨1284578, by rfl⟩ : syracuseStep 1712771 = 2569157) B2569157
theorem B238219 : Blo 235815 238219 := bstep (se 1 (by rfl) ⟨178664, by rfl⟩ : syracuseStep 238219 = 357329) B357329
theorem B238231 : Blo 235815 238231 := bstep (se 1 (by rfl) ⟨178673, by rfl⟩ : syracuseStep 238231 = 357347) B357347
theorem B238251 : Blo 235815 238251 := bstep (se 1 (by rfl) ⟨178688, by rfl⟩ : syracuseStep 238251 = 357377) B357377
theorem B238263 : Blo 235815 238263 := bstep (se 1 (by rfl) ⟨178697, by rfl⟩ : syracuseStep 238263 = 357395) B357395
theorem B533195 : Blo 235815 533195 := bstep (se 1 (by rfl) ⟨399896, by rfl⟩ : syracuseStep 533195 = 799793) B799793
theorem B238283 : Blo 235815 238283 := bstep (se 1 (by rfl) ⟨178712, by rfl⟩ : syracuseStep 238283 = 357425) B357425
theorem B238295 : Blo 235815 238295 := bstep (se 1 (by rfl) ⟨178721, by rfl⟩ : syracuseStep 238295 = 357443) B357443
theorem B238315 : Blo 235815 238315 := bstep (se 1 (by rfl) ⟨178736, by rfl⟩ : syracuseStep 238315 = 357473) B357473
theorem B238327 : Blo 235815 238327 := bstep (se 1 (by rfl) ⟨178745, by rfl⟩ : syracuseStep 238327 = 357491) B357491
theorem B533249 : Blo 235815 533249 := bstep (se 2 (by rfl) ⟨199968, by rfl⟩ : syracuseStep 533249 = 399937) B399937
theorem B238347 : Blo 235815 238347 := bstep (se 1 (by rfl) ⟨178760, by rfl⟩ : syracuseStep 238347 = 357521) B357521
theorem B238359 : Blo 235815 238359 := bstep (se 1 (by rfl) ⟨178769, by rfl⟩ : syracuseStep 238359 = 357539) B357539
theorem B238379 : Blo 235815 238379 := bstep (se 1 (by rfl) ⟨178784, by rfl⟩ : syracuseStep 238379 = 357569) B357569
theorem B238391 : Blo 235815 238391 := bstep (se 1 (by rfl) ⟨178793, by rfl⟩ : syracuseStep 238391 = 357587) B357587
theorem B238411 : Blo 235815 238411 := bstep (se 1 (by rfl) ⟨178808, by rfl⟩ : syracuseStep 238411 = 357617) B357617
theorem B238423 : Blo 235815 238423 := bstep (se 1 (by rfl) ⟨178817, by rfl⟩ : syracuseStep 238423 = 357635) B357635
theorem B598873 : Blo 235815 598873 := bstep (se 2 (by rfl) ⟨224577, by rfl⟩ : syracuseStep 598873 = 449155) B449155
theorem B238443 : Blo 235815 238443 := bstep (se 1 (by rfl) ⟨178832, by rfl⟩ : syracuseStep 238443 = 357665) B357665
theorem B238455 : Blo 235815 238455 := bstep (se 1 (by rfl) ⟨178841, by rfl⟩ : syracuseStep 238455 = 357683) B357683
theorem B238475 : Blo 235815 238475 := bstep (se 1 (by rfl) ⟨178856, by rfl⟩ : syracuseStep 238475 = 357713) B357713
theorem B1024913 : Blo 235815 1024913 := bstep (se 2 (by rfl) ⟨384342, by rfl⟩ : syracuseStep 1024913 = 768685) B768685
theorem B238487 : Blo 235815 238487 := bstep (se 1 (by rfl) ⟨178865, by rfl⟩ : syracuseStep 238487 = 357731) B357731
theorem B336793 : Blo 235815 336793 := bstep (se 2 (by rfl) ⟨126297, by rfl⟩ : syracuseStep 336793 = 252595) B252595
theorem B238507 : Blo 235815 238507 := bstep (se 1 (by rfl) ⟨178880, by rfl⟩ : syracuseStep 238507 = 357761) B357761
theorem B238519 : Blo 235815 238519 := bstep (se 1 (by rfl) ⟨178889, by rfl⟩ : syracuseStep 238519 = 357779) B357779
theorem B238539 : Blo 235815 238539 := bstep (se 1 (by rfl) ⟨178904, by rfl⟩ : syracuseStep 238539 = 357809) B357809
theorem B238551 : Blo 235815 238551 := bstep (se 1 (by rfl) ⟨178913, by rfl⟩ : syracuseStep 238551 = 357827) B357827
theorem B533465 : Blo 235815 533465 := bstep (se 2 (by rfl) ⟨200049, by rfl⟩ : syracuseStep 533465 = 400099) B400099
theorem B238571 : Blo 235815 238571 := bstep (se 1 (by rfl) ⟨178928, by rfl⟩ : syracuseStep 238571 = 357857) B357857
theorem B238583 : Blo 235815 238583 := bstep (se 1 (by rfl) ⟨178937, by rfl⟩ : syracuseStep 238583 = 357875) B357875
theorem B238603 : Blo 235815 238603 := bstep (se 1 (by rfl) ⟨178952, by rfl⟩ : syracuseStep 238603 = 357905) B357905
theorem B402455 : Blo 235815 402455 := bstep (se 1 (by rfl) ⟨301841, by rfl⟩ : syracuseStep 402455 = 603683) B603683
theorem B238615 : Blo 235815 238615 := bstep (se 1 (by rfl) ⟨178961, by rfl⟩ : syracuseStep 238615 = 357923) B357923
theorem B238635 : Blo 235815 238635 := bstep (se 1 (by rfl) ⟨178976, by rfl⟩ : syracuseStep 238635 = 357953) B357953
theorem B533555 : Blo 235815 533555 := bstep (se 1 (by rfl) ⟨400166, by rfl⟩ : syracuseStep 533555 = 800333) B800333
theorem B238647 : Blo 235815 238647 := bstep (se 1 (by rfl) ⟨178985, by rfl⟩ : syracuseStep 238647 = 357971) B357971
theorem B238667 : Blo 235815 238667 := bstep (se 1 (by rfl) ⟨179000, by rfl⟩ : syracuseStep 238667 = 358001) B358001
theorem B533591 : Blo 235815 533591 := bstep (se 1 (by rfl) ⟨400193, by rfl⟩ : syracuseStep 533591 = 800387) B800387
theorem B238679 : Blo 235815 238679 := bstep (se 1 (by rfl) ⟨179009, by rfl⟩ : syracuseStep 238679 = 358019) B358019
theorem B238699 : Blo 235815 238699 := bstep (se 1 (by rfl) ⟨179024, by rfl⟩ : syracuseStep 238699 = 358049) B358049
theorem B238711 : Blo 235815 238711 := bstep (se 1 (by rfl) ⟨179033, by rfl⟩ : syracuseStep 238711 = 358067) B358067
theorem B238731 : Blo 235815 238731 := bstep (se 1 (by rfl) ⟨179048, by rfl⟩ : syracuseStep 238731 = 358097) B358097
theorem B402583 : Blo 235815 402583 := bstep (se 1 (by rfl) ⟨301937, by rfl⟩ : syracuseStep 402583 = 603875) B603875
theorem B238743 : Blo 235815 238743 := bstep (se 1 (by rfl) ⟨179057, by rfl⟩ : syracuseStep 238743 = 358115) B358115
theorem B238763 : Blo 235815 238763 := bstep (se 1 (by rfl) ⟨179072, by rfl⟩ : syracuseStep 238763 = 358145) B358145
theorem B238775 : Blo 235815 238775 := bstep (se 1 (by rfl) ⟨179081, by rfl⟩ : syracuseStep 238775 = 358163) B358163
theorem B238795 : Blo 235815 238795 := bstep (se 1 (by rfl) ⟨179096, by rfl⟩ : syracuseStep 238795 = 358193) B358193
theorem B238807 : Blo 235815 238807 := bstep (se 1 (by rfl) ⟨179105, by rfl⟩ : syracuseStep 238807 = 358211) B358211
theorem B861401 : Blo 235815 861401 := bstep (se 2 (by rfl) ⟨323025, by rfl⟩ : syracuseStep 861401 = 646051) B646051
theorem B238827 : Blo 235815 238827 := bstep (se 1 (by rfl) ⟨179120, by rfl⟩ : syracuseStep 238827 = 358241) B358241
theorem B238839 : Blo 235815 238839 := bstep (se 1 (by rfl) ⟨179129, by rfl⟩ : syracuseStep 238839 = 358259) B358259
theorem B533771 : Blo 235815 533771 := bstep (se 1 (by rfl) ⟨400328, by rfl⟩ : syracuseStep 533771 = 800657) B800657
theorem B238859 : Blo 235815 238859 := bstep (se 1 (by rfl) ⟨179144, by rfl⟩ : syracuseStep 238859 = 358289) B358289
theorem B238871 : Blo 235815 238871 := bstep (se 1 (by rfl) ⟨179153, by rfl⟩ : syracuseStep 238871 = 358307) B358307
theorem B238891 : Blo 235815 238891 := bstep (se 1 (by rfl) ⟨179168, by rfl⟩ : syracuseStep 238891 = 358337) B358337
theorem B238903 : Blo 235815 238903 := bstep (se 1 (by rfl) ⟨179177, by rfl⟩ : syracuseStep 238903 = 358355) B358355
theorem B533825 : Blo 235815 533825 := bstep (se 2 (by rfl) ⟨200184, by rfl⟩ : syracuseStep 533825 = 400369) B400369
theorem B238923 : Blo 235815 238923 := bstep (se 1 (by rfl) ⟨179192, by rfl⟩ : syracuseStep 238923 = 358385) B358385
theorem B238935 : Blo 235815 238935 := bstep (se 1 (by rfl) ⟨179201, by rfl⟩ : syracuseStep 238935 = 358403) B358403
theorem B763229 : Blo 235815 763229 := bstep (se 3 (by rfl) ⟨143105, by rfl⟩ : syracuseStep 763229 = 286211) B286211
theorem B238955 : Blo 235815 238955 := bstep (se 1 (by rfl) ⟨179216, by rfl⟩ : syracuseStep 238955 = 358433) B358433
theorem B3417461 : Blo 235815 3417461 := bstep (se 5 (by rfl) ⟨160193, by rfl⟩ : syracuseStep 3417461 = 320387) B320387
theorem B238967 : Blo 235815 238967 := bstep (se 1 (by rfl) ⟨179225, by rfl⟩ : syracuseStep 238967 = 358451) B358451
theorem B238987 : Blo 235815 238987 := bstep (se 1 (by rfl) ⟨179240, by rfl⟩ : syracuseStep 238987 = 358481) B358481
theorem B238999 : Blo 235815 238999 := bstep (se 1 (by rfl) ⟨179249, by rfl⟩ : syracuseStep 238999 = 358499) B358499
theorem B239019 : Blo 235815 239019 := bstep (se 1 (by rfl) ⟨179264, by rfl⟩ : syracuseStep 239019 = 358529) B358529
theorem B239031 : Blo 235815 239031 := bstep (se 1 (by rfl) ⟨179273, by rfl⟩ : syracuseStep 239031 = 358547) B358547
theorem B271819 : Blo 235815 271819 := bstep (se 1 (by rfl) ⟨203864, by rfl⟩ : syracuseStep 271819 = 407729) B407729
theorem B239051 : Blo 235815 239051 := bstep (se 1 (by rfl) ⟨179288, by rfl⟩ : syracuseStep 239051 = 358577) B358577
theorem B239063 : Blo 235815 239063 := bstep (se 1 (by rfl) ⟨179297, by rfl⟩ : syracuseStep 239063 = 358595) B358595
theorem B796121 : Blo 235815 796121 := bstep (se 2 (by rfl) ⟨298545, by rfl⟩ : syracuseStep 796121 = 597091) B597091
theorem B239083 : Blo 235815 239083 := bstep (se 1 (by rfl) ⟨179312, by rfl⟩ : syracuseStep 239083 = 358625) B358625
theorem B239095 : Blo 235815 239095 := bstep (se 1 (by rfl) ⟨179321, by rfl⟩ : syracuseStep 239095 = 358643) B358643
theorem B239115 : Blo 235815 239115 := bstep (se 1 (by rfl) ⟨179336, by rfl⟩ : syracuseStep 239115 = 358673) B358673
theorem B2041361 : Blo 235815 2041361 := bstep (se 2 (by rfl) ⟨765510, by rfl⟩ : syracuseStep 2041361 = 1531021) B1531021
theorem B239127 : Blo 235815 239127 := bstep (se 1 (by rfl) ⟨179345, by rfl⟩ : syracuseStep 239127 = 358691) B358691
theorem B534041 : Blo 235815 534041 := bstep (se 2 (by rfl) ⟨200265, by rfl⟩ : syracuseStep 534041 = 400531) B400531
theorem B239147 : Blo 235815 239147 := bstep (se 1 (by rfl) ⟨179360, by rfl⟩ : syracuseStep 239147 = 358721) B358721
theorem B239159 : Blo 235815 239159 := bstep (se 1 (by rfl) ⟨179369, by rfl⟩ : syracuseStep 239159 = 358739) B358739
theorem B239179 : Blo 235815 239179 := bstep (se 1 (by rfl) ⟨179384, by rfl⟩ : syracuseStep 239179 = 358769) B358769
theorem B239191 : Blo 235815 239191 := bstep (se 1 (by rfl) ⟨179393, by rfl⟩ : syracuseStep 239191 = 358787) B358787
theorem B239211 : Blo 235815 239211 := bstep (se 1 (by rfl) ⟨179408, by rfl⟩ : syracuseStep 239211 = 358817) B358817
theorem B534131 : Blo 235815 534131 := bstep (se 1 (by rfl) ⟨400598, by rfl⟩ : syracuseStep 534131 = 801197) B801197
theorem B239223 : Blo 235815 239223 := bstep (se 1 (by rfl) ⟨179417, by rfl⟩ : syracuseStep 239223 = 358835) B358835
theorem B239243 : Blo 235815 239243 := bstep (se 1 (by rfl) ⟨179432, by rfl⟩ : syracuseStep 239243 = 358865) B358865
theorem B534167 : Blo 235815 534167 := bstep (se 1 (by rfl) ⟨400625, by rfl⟩ : syracuseStep 534167 = 801251) B801251
theorem B239255 : Blo 235815 239255 := bstep (se 1 (by rfl) ⟨179441, by rfl⟩ : syracuseStep 239255 = 358883) B358883
theorem B239275 : Blo 235815 239275 := bstep (se 1 (by rfl) ⟨179456, by rfl⟩ : syracuseStep 239275 = 358913) B358913
theorem B239287 : Blo 235815 239287 := bstep (se 1 (by rfl) ⟨179465, by rfl⟩ : syracuseStep 239287 = 358931) B358931
theorem B927425 : Blo 235815 927425 := bstep (se 2 (by rfl) ⟨347784, by rfl⟩ : syracuseStep 927425 = 695569) B695569
theorem B239307 : Blo 235815 239307 := bstep (se 1 (by rfl) ⟨179480, by rfl⟩ : syracuseStep 239307 = 358961) B358961
theorem B239319 : Blo 235815 239319 := bstep (se 1 (by rfl) ⟨179489, by rfl⟩ : syracuseStep 239319 = 358979) B358979
theorem B239339 : Blo 235815 239339 := bstep (se 1 (by rfl) ⟨179504, by rfl⟩ : syracuseStep 239339 = 359009) B359009
theorem B239351 : Blo 235815 239351 := bstep (se 1 (by rfl) ⟨179513, by rfl⟩ : syracuseStep 239351 = 359027) B359027
theorem B403211 : Blo 235815 403211 := bstep (se 1 (by rfl) ⟨302408, by rfl⟩ : syracuseStep 403211 = 604817) B604817
theorem B239371 : Blo 235815 239371 := bstep (se 1 (by rfl) ⟨179528, by rfl⟩ : syracuseStep 239371 = 359057) B359057
theorem B239383 : Blo 235815 239383 := bstep (se 1 (by rfl) ⟨179537, by rfl⟩ : syracuseStep 239383 = 359075) B359075
theorem B239403 : Blo 235815 239403 := bstep (se 1 (by rfl) ⟨179552, by rfl⟩ : syracuseStep 239403 = 359105) B359105
theorem B239415 : Blo 235815 239415 := bstep (se 1 (by rfl) ⟨179561, by rfl⟩ : syracuseStep 239415 = 359123) B359123
theorem B534347 : Blo 235815 534347 := bstep (se 1 (by rfl) ⟨400760, by rfl⟩ : syracuseStep 534347 = 801521) B801521
theorem B239435 : Blo 235815 239435 := bstep (se 1 (by rfl) ⟨179576, by rfl⟩ : syracuseStep 239435 = 359153) B359153
theorem B239447 : Blo 235815 239447 := bstep (se 1 (by rfl) ⟨179585, by rfl⟩ : syracuseStep 239447 = 359171) B359171
theorem B1517413 : Blo 235815 1517413 := bstep (se 4 (by rfl) ⟨142257, by rfl⟩ : syracuseStep 1517413 = 284515) B284515
theorem B239467 : Blo 235815 239467 := bstep (se 1 (by rfl) ⟨179600, by rfl⟩ : syracuseStep 239467 = 359201) B359201
theorem B239479 : Blo 235815 239479 := bstep (se 1 (by rfl) ⟨179609, by rfl⟩ : syracuseStep 239479 = 359219) B359219
theorem B534401 : Blo 235815 534401 := bstep (se 2 (by rfl) ⟨200400, by rfl⟩ : syracuseStep 534401 = 400801) B400801
theorem B403339 : Blo 235815 403339 := bstep (se 1 (by rfl) ⟨302504, by rfl⟩ : syracuseStep 403339 = 605009) B605009
theorem B239499 : Blo 235815 239499 := bstep (se 1 (by rfl) ⟨179624, by rfl⟩ : syracuseStep 239499 = 359249) B359249
theorem B239511 : Blo 235815 239511 := bstep (se 1 (by rfl) ⟨179633, by rfl⟩ : syracuseStep 239511 = 359267) B359267
theorem B239531 : Blo 235815 239531 := bstep (se 1 (by rfl) ⟨179648, by rfl⟩ : syracuseStep 239531 = 359297) B359297
theorem B599987 : Blo 235815 599987 := bstep (se 1 (by rfl) ⟨449990, by rfl⟩ : syracuseStep 599987 = 899981) B899981
theorem B239543 : Blo 235815 239543 := bstep (se 1 (by rfl) ⟨179657, by rfl⟩ : syracuseStep 239543 = 359315) B359315
theorem B567233 : Blo 235815 567233 := bstep (se 2 (by rfl) ⟨212712, by rfl⟩ : syracuseStep 567233 = 425425) B425425
theorem B239563 : Blo 235815 239563 := bstep (se 1 (by rfl) ⟨179672, by rfl⟩ : syracuseStep 239563 = 359345) B359345
theorem B239575 : Blo 235815 239575 := bstep (se 1 (by rfl) ⟨179681, by rfl⟩ : syracuseStep 239575 = 359363) B359363
theorem B239595 : Blo 235815 239595 := bstep (se 1 (by rfl) ⟨179696, by rfl⟩ : syracuseStep 239595 = 359393) B359393
theorem B239607 : Blo 235815 239607 := bstep (se 1 (by rfl) ⟨179705, by rfl⟩ : syracuseStep 239607 = 359411) B359411
theorem B239627 : Blo 235815 239627 := bstep (se 1 (by rfl) ⟨179720, by rfl⟩ : syracuseStep 239627 = 359441) B359441
theorem B239639 : Blo 235815 239639 := bstep (se 1 (by rfl) ⟨179729, by rfl⟩ : syracuseStep 239639 = 359459) B359459
theorem B403481 : Blo 235815 403481 := bstep (se 2 (by rfl) ⟨151305, by rfl⟩ : syracuseStep 403481 = 302611) B302611
theorem B239659 : Blo 235815 239659 := bstep (se 1 (by rfl) ⟨179744, by rfl⟩ : syracuseStep 239659 = 359489) B359489
theorem B239671 : Blo 235815 239671 := bstep (se 1 (by rfl) ⟨179753, by rfl⟩ : syracuseStep 239671 = 359507) B359507
theorem B239691 : Blo 235815 239691 := bstep (se 1 (by rfl) ⟨179768, by rfl⟩ : syracuseStep 239691 = 359537) B359537
theorem B239703 : Blo 235815 239703 := bstep (se 1 (by rfl) ⟨179777, by rfl⟩ : syracuseStep 239703 = 359555) B359555
theorem B534617 : Blo 235815 534617 := bstep (se 2 (by rfl) ⟨200481, by rfl⟩ : syracuseStep 534617 = 400963) B400963
theorem B239723 : Blo 235815 239723 := bstep (se 1 (by rfl) ⟨179792, by rfl⟩ : syracuseStep 239723 = 359585) B359585
theorem B239735 : Blo 235815 239735 := bstep (se 1 (by rfl) ⟨179801, by rfl⟩ : syracuseStep 239735 = 359603) B359603
theorem B239755 : Blo 235815 239755 := bstep (se 1 (by rfl) ⟨179816, by rfl⟩ : syracuseStep 239755 = 359633) B359633
theorem B796823 : Blo 235815 796823 := bstep (se 1 (by rfl) ⟨597617, by rfl⟩ : syracuseStep 796823 = 1195235) B1195235
theorem B239767 : Blo 235815 239767 := bstep (se 1 (by rfl) ⟨179825, by rfl⟩ : syracuseStep 239767 = 359651) B359651
theorem B403609 : Blo 235815 403609 := bstep (se 2 (by rfl) ⟨151353, by rfl⟩ : syracuseStep 403609 = 302707) B302707
theorem B239787 : Blo 235815 239787 := bstep (se 1 (by rfl) ⟨179840, by rfl⟩ : syracuseStep 239787 = 359681) B359681
theorem B534707 : Blo 235815 534707 := bstep (se 1 (by rfl) ⟨401030, by rfl⟩ : syracuseStep 534707 = 802061) B802061
theorem B239799 : Blo 235815 239799 := bstep (se 1 (by rfl) ⟨179849, by rfl⟩ : syracuseStep 239799 = 359699) B359699
theorem B534743 : Blo 235815 534743 := bstep (se 1 (by rfl) ⟨401057, by rfl⟩ : syracuseStep 534743 = 802115) B802115
theorem B600281 : Blo 235815 600281 := bstep (se 2 (by rfl) ⟨225105, by rfl⟩ : syracuseStep 600281 = 450211) B450211
theorem B1517899 : Blo 235815 1517899 := bstep (se 1 (by rfl) ⟨1138424, by rfl⟩ : syracuseStep 1517899 = 2276849) B2276849
theorem B338251 : Blo 235815 338251 := bstep (se 1 (by rfl) ⟨253688, by rfl⟩ : syracuseStep 338251 = 507377) B507377
theorem B1845605 : Blo 235815 1845605 := bstep (se 4 (by rfl) ⟨173025, by rfl⟩ : syracuseStep 1845605 = 346051) B346051
theorem B534923 : Blo 235815 534923 := bstep (se 1 (by rfl) ⟨401192, by rfl⟩ : syracuseStep 534923 = 802385) B802385
theorem B534977 : Blo 235815 534977 := bstep (se 2 (by rfl) ⟨200616, by rfl⟩ : syracuseStep 534977 = 401233) B401233
theorem B1354391 : Blo 235815 1354391 := bstep (se 1 (by rfl) ⟨1015793, by rfl⟩ : syracuseStep 1354391 = 2031587) B2031587
theorem B535193 : Blo 235815 535193 := bstep (se 2 (by rfl) ⟨200697, by rfl⟩ : syracuseStep 535193 = 401395) B401395
theorem B797363 : Blo 235815 797363 := bstep (se 1 (by rfl) ⟨598022, by rfl⟩ : syracuseStep 797363 = 1196045) B1196045
theorem B404183 : Blo 235815 404183 := bstep (se 1 (by rfl) ⟨303137, by rfl⟩ : syracuseStep 404183 = 606275) B606275
theorem B535283 : Blo 235815 535283 := bstep (se 1 (by rfl) ⟨401462, by rfl⟩ : syracuseStep 535283 = 802925) B802925
theorem B1813265 : Blo 235815 1813265 := bstep (se 2 (by rfl) ⟨679974, by rfl⟩ : syracuseStep 1813265 = 1359949) B1359949
theorem B535319 : Blo 235815 535319 := bstep (se 1 (by rfl) ⟨401489, by rfl⟩ : syracuseStep 535319 = 802979) B802979
theorem B895819 : Blo 235815 895819 := bstep (se 1 (by rfl) ⟨671864, by rfl⟩ : syracuseStep 895819 = 1343729) B1343729
theorem B404311 : Blo 235815 404311 := bstep (se 1 (by rfl) ⟨303233, by rfl⟩ : syracuseStep 404311 = 606467) B606467
theorem B797633 : Blo 235815 797633 := bstep (se 2 (by rfl) ⟨299112, by rfl⟩ : syracuseStep 797633 = 598225) B598225
theorem B535499 : Blo 235815 535499 := bstep (se 1 (by rfl) ⟨401624, by rfl⟩ : syracuseStep 535499 = 803249) B803249
theorem B2075597 : Blo 235815 2075597 := bstep (se 3 (by rfl) ⟨389174, by rfl⟩ : syracuseStep 2075597 = 778349) B778349
theorem B535553 : Blo 235815 535553 := bstep (se 2 (by rfl) ⟨200832, by rfl⟩ : syracuseStep 535553 = 401665) B401665
theorem B896093 : Blo 235815 896093 := bstep (se 3 (by rfl) ⟨168017, by rfl⟩ : syracuseStep 896093 = 336035) B336035
theorem B535769 : Blo 235815 535769 := bstep (se 2 (by rfl) ⟨200913, by rfl⟩ : syracuseStep 535769 = 401827) B401827
theorem B6991109 : Blo 235815 6991109 := bstep (se 4 (by rfl) ⟨655416, by rfl⟩ : syracuseStep 6991109 = 1310833) B1310833
theorem B535859 : Blo 235815 535859 := bstep (se 1 (by rfl) ⟨401894, by rfl⟩ : syracuseStep 535859 = 803789) B803789
theorem B535895 : Blo 235815 535895 := bstep (se 1 (by rfl) ⟨401921, by rfl⟩ : syracuseStep 535895 = 803843) B803843
theorem B863581 : Blo 235815 863581 := bstep (se 3 (by rfl) ⟨161921, by rfl⟩ : syracuseStep 863581 = 323843) B323843
theorem B2731481 : Blo 235815 2731481 := bstep (se 2 (by rfl) ⟨1024305, by rfl⟩ : syracuseStep 2731481 = 2048611) B2048611
theorem B798173 : Blo 235815 798173 := bstep (se 3 (by rfl) ⟨149657, by rfl⟩ : syracuseStep 798173 = 299315) B299315
theorem B536075 : Blo 235815 536075 := bstep (se 1 (by rfl) ⟨402056, by rfl⟩ : syracuseStep 536075 = 804113) B804113
theorem B241175 : Blo 235815 241175 := bstep (se 1 (by rfl) ⟨180881, by rfl⟩ : syracuseStep 241175 = 361763) B361763
theorem B339481 : Blo 235815 339481 := bstep (se 2 (by rfl) ⟨127305, by rfl⟩ : syracuseStep 339481 = 254611) B254611
theorem B536129 : Blo 235815 536129 := bstep (se 2 (by rfl) ⟨201048, by rfl⟩ : syracuseStep 536129 = 402097) B402097
theorem B896791 : Blo 235815 896791 := bstep (se 1 (by rfl) ⟨672593, by rfl⟩ : syracuseStep 896791 = 1345187) B1345187
theorem B536345 : Blo 235815 536345 := bstep (se 2 (by rfl) ⟨201129, by rfl⟩ : syracuseStep 536345 = 402259) B402259
theorem B601931 : Blo 235815 601931 := bstep (se 1 (by rfl) ⟨451448, by rfl⟩ : syracuseStep 601931 = 902897) B902897
theorem B536435 : Blo 235815 536435 := bstep (se 1 (by rfl) ⟨402326, by rfl⟩ : syracuseStep 536435 = 804653) B804653
theorem B536471 : Blo 235815 536471 := bstep (se 1 (by rfl) ⟨402353, by rfl⟩ : syracuseStep 536471 = 804707) B804707
theorem B536651 : Blo 235815 536651 := bstep (se 1 (by rfl) ⟨402488, by rfl⟩ : syracuseStep 536651 = 804977) B804977
theorem B241751 : Blo 235815 241751 := bstep (se 1 (by rfl) ⟨181313, by rfl⟩ : syracuseStep 241751 = 362627) B362627
theorem B536705 : Blo 235815 536705 := bstep (se 2 (by rfl) ⟨201264, by rfl⟩ : syracuseStep 536705 = 402529) B402529
theorem B405847 : Blo 235815 405847 := bstep (se 1 (by rfl) ⟨304385, by rfl⟩ : syracuseStep 405847 = 608771) B608771
theorem B536921 : Blo 235815 536921 := bstep (se 2 (by rfl) ⟨201345, by rfl⟩ : syracuseStep 536921 = 402691) B402691
theorem B340375 : Blo 235815 340375 := bstep (se 1 (by rfl) ⟨255281, by rfl⟩ : syracuseStep 340375 = 510563) B510563
theorem B537011 : Blo 235815 537011 := bstep (se 1 (by rfl) ⟨402758, by rfl⟩ : syracuseStep 537011 = 805517) B805517
theorem B537047 : Blo 235815 537047 := bstep (se 1 (by rfl) ⟨402785, by rfl⟩ : syracuseStep 537047 = 805571) B805571
theorem B504343 : Blo 235815 504343 := bstep (se 1 (by rfl) ⟨378257, by rfl⟩ : syracuseStep 504343 = 756515) B756515
theorem B3551779 : Blo 235815 3551779 := bstep (se 1 (by rfl) ⟨2663834, by rfl⟩ : syracuseStep 3551779 = 5327669) B5327669
theorem B897581 : Blo 235815 897581 := bstep (se 3 (by rfl) ⟨168296, by rfl⟩ : syracuseStep 897581 = 336593) B336593
theorem B1094219 : Blo 235815 1094219 := bstep (se 1 (by rfl) ⟨820664, by rfl⟩ : syracuseStep 1094219 = 1641329) B1641329
theorem B799307 : Blo 235815 799307 := bstep (se 1 (by rfl) ⟨599480, by rfl⟩ : syracuseStep 799307 = 1198961) B1198961
theorem B537227 : Blo 235815 537227 := bstep (se 1 (by rfl) ⟨402920, by rfl⟩ : syracuseStep 537227 = 805841) B805841
theorem B537281 : Blo 235815 537281 := bstep (se 2 (by rfl) ⟨201480, by rfl⟩ : syracuseStep 537281 = 402961) B402961
theorem B602903 : Blo 235815 602903 := bstep (se 1 (by rfl) ⟨452177, by rfl⟩ : syracuseStep 602903 = 904355) B904355
theorem B799577 : Blo 235815 799577 := bstep (se 2 (by rfl) ⟨299841, by rfl⟩ : syracuseStep 799577 = 599683) B599683
theorem B537497 : Blo 235815 537497 := bstep (se 2 (by rfl) ⟨201561, by rfl⟩ : syracuseStep 537497 = 403123) B403123
theorem B340939 : Blo 235815 340939 := bstep (se 1 (by rfl) ⟨255704, by rfl⟩ : syracuseStep 340939 = 511409) B511409
theorem B537587 : Blo 235815 537587 := bstep (se 1 (by rfl) ⟨403190, by rfl⟩ : syracuseStep 537587 = 806381) B806381
theorem B537623 : Blo 235815 537623 := bstep (se 1 (by rfl) ⟨403217, by rfl⟩ : syracuseStep 537623 = 806435) B806435
theorem B4600901 : Blo 235815 4600901 := bstep (se 4 (by rfl) ⟨431334, by rfl⟩ : syracuseStep 4600901 = 862669) B862669
theorem B537803 : Blo 235815 537803 := bstep (se 1 (by rfl) ⟨403352, by rfl⟩ : syracuseStep 537803 = 806705) B806705
theorem B537857 : Blo 235815 537857 := bstep (se 2 (by rfl) ⟨201696, by rfl⟩ : syracuseStep 537857 = 403393) B403393
theorem B505163 : Blo 235815 505163 := bstep (se 1 (by rfl) ⟨378872, by rfl⟩ : syracuseStep 505163 = 757745) B757745
theorem B603571 : Blo 235815 603571 := bstep (se 1 (by rfl) ⟨452678, by rfl⟩ : syracuseStep 603571 = 905357) B905357
theorem B538073 : Blo 235815 538073 := bstep (se 2 (by rfl) ⟨201777, by rfl⟩ : syracuseStep 538073 = 403555) B403555
theorem B800279 : Blo 235815 800279 := bstep (se 1 (by rfl) ⟨600209, by rfl⟩ : syracuseStep 800279 = 1200419) B1200419
theorem B538163 : Blo 235815 538163 := bstep (se 1 (by rfl) ⟨403622, by rfl⟩ : syracuseStep 538163 = 807245) B807245
theorem B603713 : Blo 235815 603713 := bstep (se 2 (by rfl) ⟨226392, by rfl⟩ : syracuseStep 603713 = 452785) B452785
theorem B538199 : Blo 235815 538199 := bstep (se 1 (by rfl) ⟨403649, by rfl⟩ : syracuseStep 538199 = 807299) B807299
theorem B538379 : Blo 235815 538379 := bstep (se 1 (by rfl) ⟨403784, by rfl⟩ : syracuseStep 538379 = 807569) B807569
theorem B3323693 : Blo 235815 3323693 := bstep (se 3 (by rfl) ⟨623192, by rfl⟩ : syracuseStep 3323693 = 1246385) B1246385
theorem B538433 : Blo 235815 538433 := bstep (se 2 (by rfl) ⟨201912, by rfl⟩ : syracuseStep 538433 = 403825) B403825
theorem B899009 : Blo 235815 899009 := bstep (se 2 (by rfl) ⟨337128, by rfl⟩ : syracuseStep 899009 = 674257) B674257
theorem B538649 : Blo 235815 538649 := bstep (se 2 (by rfl) ⟨201993, by rfl⟩ : syracuseStep 538649 = 403987) B403987
theorem B800819 : Blo 235815 800819 := bstep (se 1 (by rfl) ⟨600614, by rfl⟩ : syracuseStep 800819 = 1201229) B1201229
theorem B538739 : Blo 235815 538739 := bstep (se 1 (by rfl) ⟨404054, by rfl⟩ : syracuseStep 538739 = 808109) B808109
theorem B538775 : Blo 235815 538775 := bstep (se 1 (by rfl) ⟨404081, by rfl⟩ : syracuseStep 538775 = 808163) B808163
theorem B801089 : Blo 235815 801089 := bstep (se 2 (by rfl) ⟨300408, by rfl⟩ : syracuseStep 801089 = 600817) B600817
theorem B440641 : Blo 235815 440641 := bstep (se 2 (by rfl) ⟨165240, by rfl⟩ : syracuseStep 440641 = 330481) B330481
theorem B538955 : Blo 235815 538955 := bstep (se 1 (by rfl) ⟨404216, by rfl⟩ : syracuseStep 538955 = 808433) B808433
theorem B538969 : Blo 235815 538969 := bstep (se 2 (by rfl) ⟨202113, by rfl⟩ : syracuseStep 538969 = 404227) B404227
theorem B539009 : Blo 235815 539009 := bstep (se 2 (by rfl) ⟨202128, by rfl⟩ : syracuseStep 539009 = 404257) B404257
theorem B571799 : Blo 235815 571799 := bstep (se 1 (by rfl) ⟨428849, by rfl⟩ : syracuseStep 571799 = 857699) B857699
theorem B1456535 : Blo 235815 1456535 := bstep (se 1 (by rfl) ⟨1092401, by rfl⟩ : syracuseStep 1456535 = 2184803) B2184803
theorem B1817153 : Blo 235815 1817153 := bstep (se 2 (by rfl) ⟨681432, by rfl⟩ : syracuseStep 1817153 = 1362865) B1362865
theorem B539225 : Blo 235815 539225 := bstep (se 2 (by rfl) ⟨202209, by rfl⟩ : syracuseStep 539225 = 404419) B404419
theorem B539315 : Blo 235815 539315 := bstep (se 1 (by rfl) ⟨404486, by rfl⟩ : syracuseStep 539315 = 808973) B808973
theorem B539351 : Blo 235815 539351 := bstep (se 1 (by rfl) ⟨404513, by rfl⟩ : syracuseStep 539351 = 809027) B809027
theorem B604979 : Blo 235815 604979 := bstep (se 1 (by rfl) ⟨453734, by rfl⟩ : syracuseStep 604979 = 907469) B907469
theorem B342871 : Blo 235815 342871 := bstep (se 1 (by rfl) ⟨257153, by rfl⟩ : syracuseStep 342871 = 514307) B514307
theorem B801629 : Blo 235815 801629 := bstep (se 3 (by rfl) ⟨150305, by rfl⟩ : syracuseStep 801629 = 300611) B300611
theorem B539531 : Blo 235815 539531 := bstep (se 1 (by rfl) ⟨404648, by rfl⟩ : syracuseStep 539531 = 809297) B809297
theorem B539585 : Blo 235815 539585 := bstep (se 2 (by rfl) ⟨202344, by rfl⟩ : syracuseStep 539585 = 404689) B404689
theorem B539635 : Blo 235815 539635 := bstep (se 1 (by rfl) ⟨404726, by rfl⟩ : syracuseStep 539635 = 809453) B809453
theorem B1195073 : Blo 235815 1195073 := bstep (se 2 (by rfl) ⟨448152, by rfl⟩ : syracuseStep 1195073 = 896305) B896305
theorem B605515 : Blo 235815 605515 := bstep (se 1 (by rfl) ⟨454136, by rfl⟩ : syracuseStep 605515 = 908273) B908273
theorem B900497 : Blo 235815 900497 := bstep (se 2 (by rfl) ⟨337686, by rfl⟩ : syracuseStep 900497 = 675373) B675373
theorem B605657 : Blo 235815 605657 := bstep (se 2 (by rfl) ⟨227121, by rfl⟩ : syracuseStep 605657 = 454243) B454243
theorem B507521 : Blo 235815 507521 := bstep (se 2 (by rfl) ⟨190320, by rfl⟩ : syracuseStep 507521 = 380641) B380641
theorem B1457995 : Blo 235815 1457995 := bstep (se 1 (by rfl) ⟨1093496, by rfl⟩ : syracuseStep 1457995 = 2186993) B2186993
theorem B900953 : Blo 235815 900953 := bstep (se 2 (by rfl) ⟨337857, by rfl⟩ : syracuseStep 900953 = 675715) B675715
theorem B1359767 : Blo 235815 1359767 := bstep (se 1 (by rfl) ⟨1019825, by rfl⟩ : syracuseStep 1359767 = 2039651) B2039651
theorem B802763 : Blo 235815 802763 := bstep (se 1 (by rfl) ⟨602072, by rfl⟩ : syracuseStep 802763 = 1204145) B1204145
theorem B507863 : Blo 235815 507863 := bstep (se 1 (by rfl) ⟨380897, by rfl⟩ : syracuseStep 507863 = 761795) B761795
theorem B278551 : Blo 235815 278551 := bstep (se 1 (by rfl) ⟨208913, by rfl⟩ : syracuseStep 278551 = 417827) B417827
theorem B901165 : Blo 235815 901165 := bstep (se 3 (by rfl) ⟨168968, by rfl⟩ : syracuseStep 901165 = 337937) B337937
theorem B1032257 : Blo 235815 1032257 := bstep (se 2 (by rfl) ⟨387096, by rfl⟩ : syracuseStep 1032257 = 774193) B774193
theorem B803033 : Blo 235815 803033 := bstep (se 2 (by rfl) ⟨301137, by rfl⟩ : syracuseStep 803033 = 602275) B602275
theorem B606487 : Blo 235815 606487 := bstep (se 1 (by rfl) ⟨454865, by rfl⟩ : syracuseStep 606487 = 909731) B909731
theorem B901469 : Blo 235815 901469 := bstep (se 3 (by rfl) ⟨169025, by rfl⟩ : syracuseStep 901469 = 338051) B338051
theorem B573875 : Blo 235815 573875 := bstep (se 1 (by rfl) ⟨430406, by rfl⟩ : syracuseStep 573875 = 860813) B860813
theorem B1819097 : Blo 235815 1819097 := bstep (se 2 (by rfl) ⟨682161, by rfl⟩ : syracuseStep 1819097 = 1364323) B1364323
theorem B508427 : Blo 235815 508427 := bstep (se 1 (by rfl) ⟨381320, by rfl⟩ : syracuseStep 508427 = 762641) B762641
theorem B606923 : Blo 235815 606923 := bstep (se 1 (by rfl) ⟨455192, by rfl⟩ : syracuseStep 606923 = 910385) B910385
theorem B1557265 : Blo 235815 1557265 := bstep (se 2 (by rfl) ⟨583974, by rfl⟩ : syracuseStep 1557265 = 1167949) B1167949
theorem B803735 : Blo 235815 803735 := bstep (se 1 (by rfl) ⟨602801, by rfl⟩ : syracuseStep 803735 = 1205603) B1205603
theorem B1197017 : Blo 235815 1197017 := bstep (se 2 (by rfl) ⟨448881, by rfl⟩ : syracuseStep 1197017 = 897763) B897763
theorem B672857 : Blo 235815 672857 := bstep (se 2 (by rfl) ⟨252321, by rfl⟩ : syracuseStep 672857 = 504643) B504643
theorem B509017 : Blo 235815 509017 := bstep (se 2 (by rfl) ⟨190881, by rfl⟩ : syracuseStep 509017 = 381763) B381763
theorem B2704589 : Blo 235815 2704589 := bstep (se 3 (by rfl) ⟨507110, by rfl⟩ : syracuseStep 2704589 = 1014221) B1014221
theorem B4080941 : Blo 235815 4080941 := bstep (se 3 (by rfl) ⟨765176, by rfl⟩ : syracuseStep 4080941 = 1530353) B1530353
theorem B3458483 : Blo 235815 3458483 := bstep (se 1 (by rfl) ⟨2593862, by rfl⟩ : syracuseStep 3458483 = 5187725) B5187725
theorem B804275 : Blo 235815 804275 := bstep (se 1 (by rfl) ⟨603206, by rfl⟩ : syracuseStep 804275 = 1206413) B1206413
theorem B804545 : Blo 235815 804545 := bstep (se 2 (by rfl) ⟨301704, by rfl⟩ : syracuseStep 804545 = 603409) B603409
theorem B1361681 : Blo 235815 1361681 := bstep (se 2 (by rfl) ⟨510630, by rfl⟩ : syracuseStep 1361681 = 1021261) B1021261
theorem B673687 : Blo 235815 673687 := bstep (se 1 (by rfl) ⟨505265, by rfl⟩ : syracuseStep 673687 = 1010531) B1010531
theorem B575383 : Blo 235815 575383 := bstep (se 1 (by rfl) ⟨431537, by rfl⟩ : syracuseStep 575383 = 863075) B863075
theorem B1624157 : Blo 235815 1624157 := bstep (se 3 (by rfl) ⟨304529, by rfl⟩ : syracuseStep 1624157 = 609059) B609059
theorem B510067 : Blo 235815 510067 := bstep (se 1 (by rfl) ⟨382550, by rfl⟩ : syracuseStep 510067 = 765101) B765101
theorem B805085 : Blo 235815 805085 := bstep (se 3 (by rfl) ⟨150953, by rfl⟩ : syracuseStep 805085 = 301907) B301907
theorem B1362251 : Blo 235815 1362251 := bstep (se 1 (by rfl) ⟨1021688, by rfl⟩ : syracuseStep 1362251 = 2043377) B2043377
theorem B641459 : Blo 235815 641459 := bstep (se 1 (by rfl) ⟨481094, by rfl⟩ : syracuseStep 641459 = 962189) B962189
theorem B1198637 : Blo 235815 1198637 := bstep (se 3 (by rfl) ⟨224744, by rfl⟩ : syracuseStep 1198637 = 449489) B449489
theorem B674507 : Blo 235815 674507 := bstep (se 1 (by rfl) ⟨505880, by rfl⟩ : syracuseStep 674507 = 1011761) B1011761
theorem B904067 : Blo 235815 904067 := bstep (se 1 (by rfl) ⟨678050, by rfl⟩ : syracuseStep 904067 = 1356101) B1356101
theorem B904081 : Blo 235815 904081 := bstep (se 2 (by rfl) ⟨339030, by rfl⟩ : syracuseStep 904081 = 678061) B678061
theorem B1723493 : Blo 235815 1723493 := bstep (se 4 (by rfl) ⟨161577, by rfl⟩ : syracuseStep 1723493 = 323155) B323155
theorem B904385 : Blo 235815 904385 := bstep (se 2 (by rfl) ⟨339144, by rfl⟩ : syracuseStep 904385 = 678289) B678289
theorem B806219 : Blo 235815 806219 := bstep (se 1 (by rfl) ⟨604664, by rfl⟩ : syracuseStep 806219 = 1209329) B1209329
theorem B511553 : Blo 235815 511553 := bstep (se 2 (by rfl) ⟨191832, by rfl⟩ : syracuseStep 511553 = 383665) B383665
theorem B806489 : Blo 235815 806489 := bstep (se 2 (by rfl) ⟨302433, by rfl⟩ : syracuseStep 806489 = 604867) B604867
theorem B905053 : Blo 235815 905053 := bstep (se 3 (by rfl) ⟨169697, by rfl⟩ : syracuseStep 905053 = 339395) B339395
theorem B18665315 : Blo 235815 18665315 := bstep (se 1 (by rfl) ⟨13998986, by rfl⟩ : syracuseStep 18665315 = 27997973) B27997973
theorem B2576245 : Blo 235815 2576245 := bstep (se 5 (by rfl) ⟨120761, by rfl⟩ : syracuseStep 2576245 = 241523) B241523
theorem B610199 : Blo 235815 610199 := bstep (se 1 (by rfl) ⟨457649, by rfl⟩ : syracuseStep 610199 = 915299) B915299
theorem B511895 : Blo 235815 511895 := bstep (se 1 (by rfl) ⟨383921, by rfl⟩ : syracuseStep 511895 = 767843) B767843
theorem B479155 : Blo 235815 479155 := bstep (se 1 (by rfl) ⟨359366, by rfl⟩ : syracuseStep 479155 = 718733) B718733
theorem B544907 : Blo 235815 544907 := bstep (se 1 (by rfl) ⟨408680, by rfl⟩ : syracuseStep 544907 = 817361) B817361
theorem B807191 : Blo 235815 807191 := bstep (se 1 (by rfl) ⟨605393, by rfl⟩ : syracuseStep 807191 = 1210787) B1210787
theorem B676289 : Blo 235815 676289 := bstep (se 2 (by rfl) ⟨253608, by rfl⟩ : syracuseStep 676289 = 507217) B507217
theorem B643673 : Blo 235815 643673 := bstep (se 2 (by rfl) ⟨241377, by rfl⟩ : syracuseStep 643673 = 482755) B482755
theorem B1135235 : Blo 235815 1135235 := bstep (se 1 (by rfl) ⟨851426, by rfl⟩ : syracuseStep 1135235 = 1702853) B1702853
theorem B807731 : Blo 235815 807731 := bstep (se 1 (by rfl) ⟨605798, by rfl⟩ : syracuseStep 807731 = 1211597) B1211597
theorem B2053043 : Blo 235815 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B808001 : Blo 235815 808001 := bstep (se 2 (by rfl) ⟨303000, by rfl⟩ : syracuseStep 808001 = 606001) B606001
theorem B906329 : Blo 235815 906329 := bstep (se 2 (by rfl) ⟨339873, by rfl⟩ : syracuseStep 906329 = 679747) B679747
theorem B676957 : Blo 235815 676957 := bstep (se 3 (by rfl) ⟨126929, by rfl⟩ : syracuseStep 676957 = 253859) B253859
theorem B611479 : Blo 235815 611479 := bstep (se 1 (by rfl) ⟨458609, by rfl⟩ : syracuseStep 611479 = 917219) B917219
theorem B283991 : Blo 235815 283991 := bstep (se 1 (by rfl) ⟨212993, by rfl⟩ : syracuseStep 283991 = 425987) B425987
theorem B382295 : Blo 235815 382295 := bstep (se 1 (by rfl) ⟨286721, by rfl⟩ : syracuseStep 382295 = 573443) B573443
theorem B448001 : Blo 235815 448001 := bstep (se 2 (by rfl) ⟨168000, by rfl⟩ : syracuseStep 448001 = 336001) B336001
theorem B1955393 : Blo 235815 1955393 := bstep (se 2 (by rfl) ⟨733272, by rfl⟩ : syracuseStep 1955393 = 1466545) B1466545
theorem B808541 : Blo 235815 808541 := bstep (se 3 (by rfl) ⟨151601, by rfl⟩ : syracuseStep 808541 = 303203) B303203
theorem B480971 : Blo 235815 480971 := bstep (se 1 (by rfl) ⟨360728, by rfl⟩ : syracuseStep 480971 = 721457) B721457
theorem B448267 : Blo 235815 448267 := bstep (se 1 (by rfl) ⟨336200, by rfl⟩ : syracuseStep 448267 = 672401) B672401
theorem B251915 : Blo 235815 251915 := bstep (se 1 (by rfl) ⟨188936, by rfl⟩ : syracuseStep 251915 = 377873) B377873
theorem B645209 : Blo 235815 645209 := bstep (se 2 (by rfl) ⟨241953, by rfl⟩ : syracuseStep 645209 = 483907) B483907
theorem B448715 : Blo 235815 448715 := bstep (se 1 (by rfl) ⟨336536, by rfl⟩ : syracuseStep 448715 = 673073) B673073
theorem B13031725 : Blo 235815 13031725 := bstep (se 3 (by rfl) ⟨2443448, by rfl⟩ : syracuseStep 13031725 = 4886897) B4886897
theorem B678233 : Blo 235815 678233 := bstep (se 2 (by rfl) ⟨254337, by rfl⟩ : syracuseStep 678233 = 508675) B508675
theorem B1202525 : Blo 235815 1202525 := bstep (se 3 (by rfl) ⟨225473, by rfl⟩ : syracuseStep 1202525 = 450947) B450947
theorem B448897 : Blo 235815 448897 := bstep (se 2 (by rfl) ⟨168336, by rfl⟩ : syracuseStep 448897 = 336673) B336673
theorem B383383 : Blo 235815 383383 := bstep (se 1 (by rfl) ⟨287537, by rfl⟩ : syracuseStep 383383 = 575075) B575075
theorem B481879 : Blo 235815 481879 := bstep (se 1 (by rfl) ⟨361409, by rfl⟩ : syracuseStep 481879 = 722819) B722819
theorem B907955 : Blo 235815 907955 := bstep (se 1 (by rfl) ⟨680966, by rfl⟩ : syracuseStep 907955 = 1361933) B1361933
theorem B907969 : Blo 235815 907969 := bstep (se 2 (by rfl) ⟨340488, by rfl⟩ : syracuseStep 907969 = 680977) B680977
theorem B449239 : Blo 235815 449239 := bstep (se 1 (by rfl) ⟨336929, by rfl⟩ : syracuseStep 449239 = 673859) B673859
theorem B449459 : Blo 235815 449459 := bstep (se 1 (by rfl) ⟨337094, by rfl⟩ : syracuseStep 449459 = 674189) B674189
theorem B449687 : Blo 235815 449687 := bstep (se 1 (by rfl) ⟨337265, by rfl⟩ : syracuseStep 449687 = 674531) B674531
theorem B1400129 : Blo 235815 1400129 := bstep (se 2 (by rfl) ⟨525048, by rfl⟩ : syracuseStep 1400129 = 1050097) B1050097
theorem B449945 : Blo 235815 449945 := bstep (se 2 (by rfl) ⟨168729, by rfl⟩ : syracuseStep 449945 = 337459) B337459
theorem B1892045 : Blo 235815 1892045 := bstep (se 3 (by rfl) ⟨354758, by rfl⟩ : syracuseStep 1892045 = 709517) B709517
theorem B253675 : Blo 235815 253675 := bstep (se 1 (by rfl) ⟨190256, by rfl⟩ : syracuseStep 253675 = 380513) B380513
theorem B450355 : Blo 235815 450355 := bstep (se 1 (by rfl) ⟨337766, by rfl⟩ : syracuseStep 450355 = 675533) B675533
theorem B286615 : Blo 235815 286615 := bstep (se 1 (by rfl) ⟨214961, by rfl⟩ : syracuseStep 286615 = 429923) B429923
theorem B679873 : Blo 235815 679873 := bstep (se 2 (by rfl) ⟨254952, by rfl⟩ : syracuseStep 679873 = 509905) B509905
theorem B3039383 : Blo 235815 3039383 := bstep (se 1 (by rfl) ⟨2279537, by rfl⟩ : syracuseStep 3039383 = 4559075) B4559075
theorem B2154701 : Blo 235815 2154701 := bstep (se 3 (by rfl) ⟨404006, by rfl⟩ : syracuseStep 2154701 = 808013) B808013
theorem B450841 : Blo 235815 450841 := bstep (se 2 (by rfl) ⟨169065, by rfl⟩ : syracuseStep 450841 = 338131) B338131
theorem B1204631 : Blo 235815 1204631 := bstep (se 1 (by rfl) ⟨903473, by rfl⟩ : syracuseStep 1204631 = 1806947) B1806947
theorem B909899 : Blo 235815 909899 := bstep (se 1 (by rfl) ⟨682424, by rfl⟩ : syracuseStep 909899 = 1364849) B1364849
theorem B909913 : Blo 235815 909913 := bstep (se 2 (by rfl) ⟨341217, by rfl⟩ : syracuseStep 909913 = 682435) B682435
theorem B320215 : Blo 235815 320215 := bstep (se 1 (by rfl) ⟨240161, by rfl⟩ : syracuseStep 320215 = 480323) B480323
theorem B680755 : Blo 235815 680755 := bstep (se 1 (by rfl) ⟨510566, by rfl⟩ : syracuseStep 680755 = 1021133) B1021133
theorem B451403 : Blo 235815 451403 := bstep (se 1 (by rfl) ⟨338552, by rfl⟩ : syracuseStep 451403 = 677105) B677105
theorem B451585 : Blo 235815 451585 := bstep (se 2 (by rfl) ⟨169344, by rfl⟩ : syracuseStep 451585 = 338689) B338689
theorem B320599 : Blo 235815 320599 := bstep (se 1 (by rfl) ⟨240449, by rfl⟩ : syracuseStep 320599 = 480899) B480899
theorem B255307 : Blo 235815 255307 := bstep (se 1 (by rfl) ⟨191480, by rfl⟩ : syracuseStep 255307 = 382961) B382961
theorem B1009027 : Blo 235815 1009027 := bstep (se 1 (by rfl) ⟨756770, by rfl⟩ : syracuseStep 1009027 = 1513541) B1513541
theorem B353753 : Blo 235815 353753 := bstep (se 2 (by rfl) ⟨132657, by rfl⟩ : syracuseStep 353753 = 265315) B265315
theorem B353867 : Blo 235815 353867 := bstep (se 1 (by rfl) ⟨265400, by rfl⟩ : syracuseStep 353867 = 530801) B530801
theorem B681547 : Blo 235815 681547 := bstep (se 1 (by rfl) ⟨511160, by rfl⟩ : syracuseStep 681547 = 1022321) B1022321
theorem B353879 : Blo 235815 353879 := bstep (se 1 (by rfl) ⟨265409, by rfl⟩ : syracuseStep 353879 = 530819) B530819
theorem B353945 : Blo 235815 353945 := bstep (se 2 (by rfl) ⟨132729, by rfl⟩ : syracuseStep 353945 = 265459) B265459
theorem B452299 : Blo 235815 452299 := bstep (se 1 (by rfl) ⟨339224, by rfl⟩ : syracuseStep 452299 = 678449) B678449
theorem B354059 : Blo 235815 354059 := bstep (se 1 (by rfl) ⟨265544, by rfl⟩ : syracuseStep 354059 = 531089) B531089
theorem B354071 : Blo 235815 354071 := bstep (se 1 (by rfl) ⟨265553, by rfl⟩ : syracuseStep 354071 = 531107) B531107
theorem B452375 : Blo 235815 452375 := bstep (se 1 (by rfl) ⟨339281, by rfl⟩ : syracuseStep 452375 = 678563) B678563
theorem B255799 : Blo 235815 255799 := bstep (se 1 (by rfl) ⟨191849, by rfl⟩ : syracuseStep 255799 = 383699) B383699
theorem B354137 : Blo 235815 354137 := bstep (se 2 (by rfl) ⟨132801, by rfl⟩ : syracuseStep 354137 = 265603) B265603
theorem B681821 : Blo 235815 681821 := bstep (se 3 (by rfl) ⟨127841, by rfl⟩ : syracuseStep 681821 = 255683) B255683
theorem B354251 : Blo 235815 354251 := bstep (se 1 (by rfl) ⟨265688, by rfl⟩ : syracuseStep 354251 = 531377) B531377
theorem B354263 : Blo 235815 354263 := bstep (se 1 (by rfl) ⟨265697, by rfl⟩ : syracuseStep 354263 = 531395) B531395
theorem B354329 : Blo 235815 354329 := bstep (se 2 (by rfl) ⟨132873, by rfl⟩ : syracuseStep 354329 = 265747) B265747
theorem B550937 : Blo 235815 550937 := bstep (se 2 (by rfl) ⟨206601, by rfl⟩ : syracuseStep 550937 = 413203) B413203
theorem B354443 : Blo 235815 354443 := bstep (se 1 (by rfl) ⟨265832, by rfl⟩ : syracuseStep 354443 = 531665) B531665
theorem B354455 : Blo 235815 354455 := bstep (se 1 (by rfl) ⟨265841, by rfl⟩ : syracuseStep 354455 = 531683) B531683
theorem B354521 : Blo 235815 354521 := bstep (se 2 (by rfl) ⟨132945, by rfl⟩ : syracuseStep 354521 = 265891) B265891
theorem B1927385 : Blo 235815 1927385 := bstep (se 2 (by rfl) ⟨722769, by rfl⟩ : syracuseStep 1927385 = 1445539) B1445539
theorem B1632473 : Blo 235815 1632473 := bstep (se 2 (by rfl) ⟨612177, by rfl⟩ : syracuseStep 1632473 = 1224355) B1224355
theorem B354635 : Blo 235815 354635 := bstep (se 1 (by rfl) ⟨265976, by rfl⟩ : syracuseStep 354635 = 531953) B531953
theorem B354647 : Blo 235815 354647 := bstep (se 1 (by rfl) ⟨265985, by rfl⟩ : syracuseStep 354647 = 531971) B531971
theorem B354713 : Blo 235815 354713 := bstep (se 2 (by rfl) ⟨133017, by rfl⟩ : syracuseStep 354713 = 266035) B266035
theorem B453043 : Blo 235815 453043 := bstep (se 1 (by rfl) ⟨339782, by rfl⟩ : syracuseStep 453043 = 679565) B679565
theorem B354827 : Blo 235815 354827 := bstep (se 1 (by rfl) ⟨266120, by rfl⟩ : syracuseStep 354827 = 532241) B532241
theorem B354839 : Blo 235815 354839 := bstep (se 1 (by rfl) ⟨266129, by rfl⟩ : syracuseStep 354839 = 532259) B532259
theorem B354905 : Blo 235815 354905 := bstep (se 2 (by rfl) ⟨133089, by rfl⟩ : syracuseStep 354905 = 266179) B266179
theorem B453271 : Blo 235815 453271 := bstep (se 1 (by rfl) ⟨339953, by rfl⟩ : syracuseStep 453271 = 679907) B679907
theorem B355019 : Blo 235815 355019 := bstep (se 1 (by rfl) ⟨266264, by rfl⟩ : syracuseStep 355019 = 532529) B532529
theorem B355031 : Blo 235815 355031 := bstep (se 1 (by rfl) ⟨266273, by rfl⟩ : syracuseStep 355031 = 532547) B532547
theorem B453377 : Blo 235815 453377 := bstep (se 2 (by rfl) ⟨170016, by rfl⟩ : syracuseStep 453377 = 340033) B340033
theorem B355097 : Blo 235815 355097 := bstep (se 2 (by rfl) ⟨133161, by rfl⟩ : syracuseStep 355097 = 266323) B266323
theorem B355211 : Blo 235815 355211 := bstep (se 1 (by rfl) ⟨266408, by rfl⟩ : syracuseStep 355211 = 532817) B532817
theorem B256907 : Blo 235815 256907 := bstep (se 1 (by rfl) ⟨192680, by rfl⟩ : syracuseStep 256907 = 385361) B385361
theorem B355223 : Blo 235815 355223 := bstep (se 1 (by rfl) ⟨266417, by rfl⟩ : syracuseStep 355223 = 532835) B532835
theorem B453529 : Blo 235815 453529 := bstep (se 2 (by rfl) ⟨170073, by rfl⟩ : syracuseStep 453529 = 340147) B340147
theorem B355289 : Blo 235815 355289 := bstep (se 2 (by rfl) ⟨133233, by rfl⟩ : syracuseStep 355289 = 266467) B266467
theorem B355403 : Blo 235815 355403 := bstep (se 1 (by rfl) ⟨266552, by rfl⟩ : syracuseStep 355403 = 533105) B533105
theorem B355415 : Blo 235815 355415 := bstep (se 1 (by rfl) ⟨266561, by rfl⟩ : syracuseStep 355415 = 533123) B533123
theorem B1010839 : Blo 235815 1010839 := bstep (se 1 (by rfl) ⟨758129, by rfl⟩ : syracuseStep 1010839 = 1516259) B1516259
theorem B355481 : Blo 235815 355481 := bstep (se 2 (by rfl) ⟨133305, by rfl⟩ : syracuseStep 355481 = 266611) B266611
theorem B355595 : Blo 235815 355595 := bstep (se 1 (by rfl) ⟨266696, by rfl⟩ : syracuseStep 355595 = 533393) B533393
theorem B355607 : Blo 235815 355607 := bstep (se 1 (by rfl) ⟨266705, by rfl⟩ : syracuseStep 355607 = 533411) B533411
theorem B978227 : Blo 235815 978227 := bstep (se 1 (by rfl) ⟨733670, by rfl⟩ : syracuseStep 978227 = 1467341) B1467341
theorem B355673 : Blo 235815 355673 := bstep (se 2 (by rfl) ⟨133377, by rfl⟩ : syracuseStep 355673 = 266755) B266755
theorem B355787 : Blo 235815 355787 := bstep (se 1 (by rfl) ⟨266840, by rfl⟩ : syracuseStep 355787 = 533681) B533681
theorem B355799 : Blo 235815 355799 := bstep (se 1 (by rfl) ⟨266849, by rfl⟩ : syracuseStep 355799 = 533699) B533699
theorem B355865 : Blo 235815 355865 := bstep (se 2 (by rfl) ⟨133449, by rfl⟩ : syracuseStep 355865 = 266899) B266899
theorem B912971 : Blo 235815 912971 := bstep (se 1 (by rfl) ⟨684728, by rfl⟩ : syracuseStep 912971 = 1369457) B1369457
theorem B355979 : Blo 235815 355979 := bstep (se 1 (by rfl) ⟨266984, by rfl⟩ : syracuseStep 355979 = 533969) B533969
theorem B355991 : Blo 235815 355991 := bstep (se 1 (by rfl) ⟨266993, by rfl⟩ : syracuseStep 355991 = 533987) B533987
theorem B2027213 : Blo 235815 2027213 := bstep (se 3 (by rfl) ⟨380102, by rfl⟩ : syracuseStep 2027213 = 760205) B760205
theorem B356057 : Blo 235815 356057 := bstep (se 2 (by rfl) ⟨133521, by rfl⟩ : syracuseStep 356057 = 267043) B267043
theorem B1011473 : Blo 235815 1011473 := bstep (se 2 (by rfl) ⟨379302, by rfl⟩ : syracuseStep 1011473 = 758605) B758605
theorem B356171 : Blo 235815 356171 := bstep (se 1 (by rfl) ⟨267128, by rfl⟩ : syracuseStep 356171 = 534257) B534257
theorem B356183 : Blo 235815 356183 := bstep (se 1 (by rfl) ⟨267137, by rfl⟩ : syracuseStep 356183 = 534275) B534275
theorem B1208195 : Blo 235815 1208195 := bstep (se 1 (by rfl) ⟨906146, by rfl⟩ : syracuseStep 1208195 = 1812293) B1812293
theorem B356249 : Blo 235815 356249 := bstep (se 2 (by rfl) ⟨133593, by rfl⟩ : syracuseStep 356249 = 267187) B267187
theorem B356363 : Blo 235815 356363 := bstep (se 1 (by rfl) ⟨267272, by rfl⟩ : syracuseStep 356363 = 534545) B534545
theorem B356375 : Blo 235815 356375 := bstep (se 1 (by rfl) ⟨267281, by rfl⟩ : syracuseStep 356375 = 534563) B534563
theorem B389207 : Blo 235815 389207 := bstep (se 1 (by rfl) ⟨291905, by rfl⟩ : syracuseStep 389207 = 583811) B583811
theorem B356441 : Blo 235815 356441 := bstep (se 2 (by rfl) ⟨133665, by rfl⟩ : syracuseStep 356441 = 267331) B267331
theorem B454835 : Blo 235815 454835 := bstep (se 1 (by rfl) ⟨341126, by rfl⟩ : syracuseStep 454835 = 682253) B682253
theorem B356555 : Blo 235815 356555 := bstep (se 1 (by rfl) ⟨267416, by rfl⟩ : syracuseStep 356555 = 534833) B534833
theorem B356567 : Blo 235815 356567 := bstep (se 1 (by rfl) ⟨267425, by rfl⟩ : syracuseStep 356567 = 534851) B534851
theorem B356633 : Blo 235815 356633 := bstep (se 2 (by rfl) ⟨133737, by rfl⟩ : syracuseStep 356633 = 267475) B267475
theorem B913739 : Blo 235815 913739 := bstep (se 1 (by rfl) ⟨685304, by rfl⟩ : syracuseStep 913739 = 1370609) B1370609
theorem B454987 : Blo 235815 454987 := bstep (se 1 (by rfl) ⟨341240, by rfl⟩ : syracuseStep 454987 = 682481) B682481
theorem B356747 : Blo 235815 356747 := bstep (se 1 (by rfl) ⟨267560, by rfl⟩ : syracuseStep 356747 = 535121) B535121
theorem B356759 : Blo 235815 356759 := bstep (se 1 (by rfl) ⟨267569, by rfl⟩ : syracuseStep 356759 = 535139) B535139
theorem B1012171 : Blo 235815 1012171 := bstep (se 1 (by rfl) ⟨759128, by rfl⟩ : syracuseStep 1012171 = 1518257) B1518257
theorem B356825 : Blo 235815 356825 := bstep (se 2 (by rfl) ⟨133809, by rfl⟩ : syracuseStep 356825 = 267619) B267619
theorem B356939 : Blo 235815 356939 := bstep (se 1 (by rfl) ⟨267704, by rfl⟩ : syracuseStep 356939 = 535409) B535409
theorem B356951 : Blo 235815 356951 := bstep (se 1 (by rfl) ⟨267713, by rfl⟩ : syracuseStep 356951 = 535427) B535427
theorem B2716253 : Blo 235815 2716253 := bstep (se 3 (by rfl) ⟨509297, by rfl⟩ : syracuseStep 2716253 = 1018595) B1018595
theorem B357017 : Blo 235815 357017 := bstep (se 2 (by rfl) ⟨133881, by rfl⟩ : syracuseStep 357017 = 267763) B267763
theorem B1012445 : Blo 235815 1012445 := bstep (se 3 (by rfl) ⟨189833, by rfl⟩ : syracuseStep 1012445 = 379667) B379667
theorem B357131 : Blo 235815 357131 := bstep (se 1 (by rfl) ⟨267848, by rfl⟩ : syracuseStep 357131 = 535697) B535697
theorem B357143 : Blo 235815 357143 := bstep (se 1 (by rfl) ⟨267857, by rfl⟩ : syracuseStep 357143 = 535715) B535715
theorem B2159405 : Blo 235815 2159405 := bstep (se 3 (by rfl) ⟨404888, by rfl⟩ : syracuseStep 2159405 = 809777) B809777
theorem B357209 : Blo 235815 357209 := bstep (se 2 (by rfl) ⟨133953, by rfl⟩ : syracuseStep 357209 = 267907) B267907
theorem B717661 : Blo 235815 717661 := bstep (se 3 (by rfl) ⟨134561, by rfl⟩ : syracuseStep 717661 = 269123) B269123
theorem B2290609 : Blo 235815 2290609 := bstep (se 2 (by rfl) ⟨858978, by rfl⟩ : syracuseStep 2290609 = 1717957) B1717957
theorem B685003 : Blo 235815 685003 := bstep (se 1 (by rfl) ⟨513752, by rfl⟩ : syracuseStep 685003 = 1027505) B1027505
theorem B357323 : Blo 235815 357323 := bstep (se 1 (by rfl) ⟨267992, by rfl⟩ : syracuseStep 357323 = 535985) B535985
theorem B357335 : Blo 235815 357335 := bstep (se 1 (by rfl) ⟨268001, by rfl⟩ : syracuseStep 357335 = 536003) B536003
theorem B914435 : Blo 235815 914435 := bstep (se 1 (by rfl) ⟨685826, by rfl⟩ : syracuseStep 914435 = 1371653) B1371653
theorem B914449 : Blo 235815 914449 := bstep (se 2 (by rfl) ⟨342918, by rfl⟩ : syracuseStep 914449 = 685837) B685837
theorem B357401 : Blo 235815 357401 := bstep (se 2 (by rfl) ⟨134025, by rfl⟩ : syracuseStep 357401 = 268051) B268051
theorem B1012787 : Blo 235815 1012787 := bstep (se 1 (by rfl) ⟨759590, by rfl⟩ : syracuseStep 1012787 = 1519181) B1519181
theorem B357515 : Blo 235815 357515 := bstep (se 1 (by rfl) ⟨268136, by rfl⟩ : syracuseStep 357515 = 536273) B536273
theorem B357527 : Blo 235815 357527 := bstep (se 1 (by rfl) ⟨268145, by rfl⟩ : syracuseStep 357527 = 536291) B536291
theorem B685273 : Blo 235815 685273 := bstep (se 2 (by rfl) ⟨256977, by rfl⟩ : syracuseStep 685273 = 513955) B513955
theorem B357593 : Blo 235815 357593 := bstep (se 2 (by rfl) ⟨134097, by rfl⟩ : syracuseStep 357593 = 268195) B268195
theorem B455987 : Blo 235815 455987 := bstep (se 1 (by rfl) ⟨341990, by rfl⟩ : syracuseStep 455987 = 683981) B683981
theorem B357707 : Blo 235815 357707 := bstep (se 1 (by rfl) ⟨268280, by rfl⟩ : syracuseStep 357707 = 536561) B536561
theorem B357719 : Blo 235815 357719 := bstep (se 1 (by rfl) ⟨268289, by rfl⟩ : syracuseStep 357719 = 536579) B536579
theorem B357785 : Blo 235815 357785 := bstep (se 2 (by rfl) ⟨134169, by rfl⟩ : syracuseStep 357785 = 268339) B268339
theorem B357899 : Blo 235815 357899 := bstep (se 1 (by rfl) ⟨268424, by rfl⟩ : syracuseStep 357899 = 536849) B536849
theorem B357911 : Blo 235815 357911 := bstep (se 1 (by rfl) ⟨268433, by rfl⟩ : syracuseStep 357911 = 536867) B536867
theorem B1078829 : Blo 235815 1078829 := bstep (se 3 (by rfl) ⟨202280, by rfl⟩ : syracuseStep 1078829 = 404561) B404561
theorem B357977 : Blo 235815 357977 := bstep (se 2 (by rfl) ⟨134241, by rfl⟩ : syracuseStep 357977 = 268483) B268483
theorem B358091 : Blo 235815 358091 := bstep (se 1 (by rfl) ⟨268568, by rfl⟩ : syracuseStep 358091 = 537137) B537137
theorem B358103 : Blo 235815 358103 := bstep (se 1 (by rfl) ⟨268577, by rfl⟩ : syracuseStep 358103 = 537155) B537155
theorem B358169 : Blo 235815 358169 := bstep (se 2 (by rfl) ⟨134313, by rfl⟩ : syracuseStep 358169 = 268627) B268627
theorem B358283 : Blo 235815 358283 := bstep (se 1 (by rfl) ⟨268712, by rfl⟩ : syracuseStep 358283 = 537425) B537425
theorem B358295 : Blo 235815 358295 := bstep (se 1 (by rfl) ⟨268721, by rfl⟩ : syracuseStep 358295 = 537443) B537443
theorem B358361 : Blo 235815 358361 := bstep (se 2 (by rfl) ⟨134385, by rfl⟩ : syracuseStep 358361 = 268771) B268771
theorem B358475 : Blo 235815 358475 := bstep (se 1 (by rfl) ⟨268856, by rfl⟩ : syracuseStep 358475 = 537713) B537713
theorem B358487 : Blo 235815 358487 := bstep (se 1 (by rfl) ⟨268865, by rfl⟩ : syracuseStep 358487 = 537731) B537731
theorem B358553 : Blo 235815 358553 := bstep (se 2 (by rfl) ⟨134457, by rfl⟩ : syracuseStep 358553 = 268915) B268915
theorem B358667 : Blo 235815 358667 := bstep (se 1 (by rfl) ⟨269000, by rfl⟩ : syracuseStep 358667 = 538001) B538001
theorem B358679 : Blo 235815 358679 := bstep (se 1 (by rfl) ⟨269009, by rfl⟩ : syracuseStep 358679 = 538019) B538019
theorem B11794733 : Blo 235815 11794733 := bstep (se 3 (by rfl) ⟨2211512, by rfl⟩ : syracuseStep 11794733 = 4423025) B4423025
theorem B358745 : Blo 235815 358745 := bstep (se 2 (by rfl) ⟨134529, by rfl⟩ : syracuseStep 358745 = 269059) B269059
theorem B358859 : Blo 235815 358859 := bstep (se 1 (by rfl) ⟨269144, by rfl⟩ : syracuseStep 358859 = 538289) B538289
theorem B358871 : Blo 235815 358871 := bstep (se 1 (by rfl) ⟨269153, by rfl⟩ : syracuseStep 358871 = 538307) B538307
theorem B358937 : Blo 235815 358937 := bstep (se 2 (by rfl) ⟨134601, by rfl⟩ : syracuseStep 358937 = 269203) B269203
theorem B883289 : Blo 235815 883289 := bstep (se 2 (by rfl) ⟨331233, by rfl⟩ : syracuseStep 883289 = 662467) B662467
theorem B359051 : Blo 235815 359051 := bstep (se 1 (by rfl) ⟨269288, by rfl⟩ : syracuseStep 359051 = 538577) B538577
theorem B359063 : Blo 235815 359063 := bstep (se 1 (by rfl) ⟨269297, by rfl⟩ : syracuseStep 359063 = 538595) B538595
theorem B359129 : Blo 235815 359129 := bstep (se 2 (by rfl) ⟨134673, by rfl⟩ : syracuseStep 359129 = 269347) B269347
theorem B1080067 : Blo 235815 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B1080139 : Blo 235815 1080139 := bstep (se 1 (by rfl) ⟨810104, by rfl⟩ : syracuseStep 1080139 = 1620209) B1620209
theorem B359243 : Blo 235815 359243 := bstep (se 1 (by rfl) ⟨269432, by rfl⟩ : syracuseStep 359243 = 538865) B538865
theorem B359255 : Blo 235815 359255 := bstep (se 1 (by rfl) ⟨269441, by rfl⟩ : syracuseStep 359255 = 538883) B538883
theorem B359321 : Blo 235815 359321 := bstep (se 2 (by rfl) ⟨134745, by rfl⟩ : syracuseStep 359321 = 269491) B269491
theorem B359435 : Blo 235815 359435 := bstep (se 1 (by rfl) ⟨269576, by rfl⟩ : syracuseStep 359435 = 539153) B539153
theorem B359447 : Blo 235815 359447 := bstep (se 1 (by rfl) ⟨269585, by rfl⟩ : syracuseStep 359447 = 539171) B539171
theorem B359513 : Blo 235815 359513 := bstep (se 2 (by rfl) ⟨134817, by rfl⟩ : syracuseStep 359513 = 269635) B269635
theorem B359627 : Blo 235815 359627 := bstep (se 1 (by rfl) ⟨269720, by rfl⟩ : syracuseStep 359627 = 539441) B539441
theorem B359639 : Blo 235815 359639 := bstep (se 1 (by rfl) ⟨269729, by rfl⟩ : syracuseStep 359639 = 539459) B539459
theorem B359705 : Blo 235815 359705 := bstep (se 2 (by rfl) ⟨134889, by rfl⟩ : syracuseStep 359705 = 269779) B269779
theorem B1015213 : Blo 235815 1015213 := bstep (se 3 (by rfl) ⟨190352, by rfl⟩ : syracuseStep 1015213 = 380705) B380705
theorem B1703429 : Blo 235815 1703429 := bstep (se 4 (by rfl) ⟨159696, by rfl⟩ : syracuseStep 1703429 = 319393) B319393
theorem B1211921 : Blo 235815 1211921 := bstep (se 2 (by rfl) ⟨454470, by rfl⟩ : syracuseStep 1211921 = 908941) B908941
theorem B3276323 : Blo 235815 3276323 := bstep (se 1 (by rfl) ⟨2457242, by rfl⟩ : syracuseStep 3276323 = 4914485) B4914485
theorem B2293379 : Blo 235815 2293379 := bstep (se 1 (by rfl) ⟨1720034, by rfl⟩ : syracuseStep 2293379 = 3440069) B3440069
theorem B1212083 : Blo 235815 1212083 := bstep (se 1 (by rfl) ⟨909062, by rfl⟩ : syracuseStep 1212083 = 1818125) B1818125
theorem B1343411 : Blo 235815 1343411 := bstep (se 1 (by rfl) ⟨1007558, by rfl⟩ : syracuseStep 1343411 = 2015117) B2015117
theorem B688171 : Blo 235815 688171 := bstep (se 1 (by rfl) ⟨516128, by rfl⟩ : syracuseStep 688171 = 1032257) B1032257
theorem B2687093 : Blo 235815 2687093 := bstep (se 5 (by rfl) ⟨125957, by rfl⟩ : syracuseStep 2687093 = 251915) B251915
theorem B1212731 : Blo 235815 1212731 := bstep (se 1 (by rfl) ⟨909548, by rfl⟩ : syracuseStep 1212731 = 1819097) B1819097
theorem B1212893 : Blo 235815 1212893 := bstep (se 3 (by rfl) ⟨227417, by rfl⟩ : syracuseStep 1212893 = 454835) B454835
theorem B1245719 : Blo 235815 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B3670721 : Blo 235815 3670721 := bstep (se 2 (by rfl) ⟨1376520, by rfl⟩ : syracuseStep 3670721 = 2753041) B2753041
theorem B1213217 : Blo 235815 1213217 := bstep (se 2 (by rfl) ⟨454956, by rfl⟩ : syracuseStep 1213217 = 909913) B909913
theorem B1803059 : Blo 235815 1803059 := bstep (se 1 (by rfl) ⟨1352294, by rfl⟩ : syracuseStep 1803059 = 2704589) B2704589
theorem B2720627 : Blo 235815 2720627 := bstep (se 1 (by rfl) ⟨2040470, by rfl⟩ : syracuseStep 2720627 = 4080941) B4080941
theorem B426953 : Blo 235815 426953 := bstep (se 2 (by rfl) ⟨160107, by rfl⟩ : syracuseStep 426953 = 320215) B320215
theorem B1082771 : Blo 235815 1082771 := bstep (se 1 (by rfl) ⟨812078, by rfl⟩ : syracuseStep 1082771 = 1624157) B1624157
theorem B427465 : Blo 235815 427465 := bstep (se 2 (by rfl) ⟨160299, by rfl⟩ : syracuseStep 427465 = 320599) B320599
theorem B1148381 : Blo 235815 1148381 := bstep (se 3 (by rfl) ⟨215321, by rfl⟩ : syracuseStep 1148381 = 430643) B430643
theorem B787979 : Blo 235815 787979 := bstep (se 1 (by rfl) ⟨590984, by rfl⟩ : syracuseStep 787979 = 1181969) B1181969
theorem B427639 : Blo 235815 427639 := bstep (se 1 (by rfl) ⟨320729, by rfl⟩ : syracuseStep 427639 = 641459) B641459
theorem B1345369 : Blo 235815 1345369 := bstep (se 2 (by rfl) ⟨504513, by rfl⟩ : syracuseStep 1345369 = 1009027) B1009027
theorem B1148995 : Blo 235815 1148995 := bstep (se 1 (by rfl) ⟨861746, by rfl⟩ : syracuseStep 1148995 = 1723493) B1723493
theorem B756823 : Blo 235815 756823 := bstep (se 1 (by rfl) ⟨567617, by rfl⟩ : syracuseStep 756823 = 1135235) B1135235
theorem B265351 : Blo 235815 265351 := bstep (se 1 (by rfl) ⟨199013, by rfl⟩ : syracuseStep 265351 = 398027) B398027
theorem B2297069 : Blo 235815 2297069 := bstep (se 3 (by rfl) ⟨430700, by rfl⟩ : syracuseStep 2297069 = 861401) B861401
theorem B265531 : Blo 235815 265531 := bstep (se 1 (by rfl) ⟨199148, by rfl⟩ : syracuseStep 265531 = 398297) B398297
theorem B2035003 : Blo 235815 2035003 := bstep (se 1 (by rfl) ⟨1526252, by rfl⟩ : syracuseStep 2035003 = 3052505) B3052505
theorem B1215965 : Blo 235815 1215965 := bstep (se 3 (by rfl) ⟨227993, by rfl⟩ : syracuseStep 1215965 = 455987) B455987
theorem B1347101 : Blo 235815 1347101 := bstep (se 3 (by rfl) ⟨252581, by rfl⟩ : syracuseStep 1347101 = 505163) B505163
theorem B2035277 : Blo 235815 2035277 := bstep (se 3 (by rfl) ⟨381614, by rfl⟩ : syracuseStep 2035277 = 763229) B763229
theorem B298667 : Blo 235815 298667 := bstep (se 1 (by rfl) ⟨224000, by rfl⟩ : syracuseStep 298667 = 448001) B448001
theorem B265999 : Blo 235815 265999 := bstep (se 1 (by rfl) ⟨199499, by rfl⟩ : syracuseStep 265999 = 398999) B398999
theorem B430139 : Blo 235815 430139 := bstep (se 1 (by rfl) ⟨322604, by rfl⟩ : syracuseStep 430139 = 645209) B645209
theorem B299143 : Blo 235815 299143 := bstep (se 1 (by rfl) ⟨224357, by rfl⟩ : syracuseStep 299143 = 448715) B448715
theorem B1347785 : Blo 235815 1347785 := bstep (se 2 (by rfl) ⟨505419, by rfl⟩ : syracuseStep 1347785 = 1010839) B1010839
theorem B266503 : Blo 235815 266503 := bstep (se 1 (by rfl) ⟨199877, by rfl⟩ : syracuseStep 266503 = 399755) B399755
theorem B266683 : Blo 235815 266683 := bstep (se 1 (by rfl) ⟨200012, by rfl⟩ : syracuseStep 266683 = 400025) B400025
theorem B1151441 : Blo 235815 1151441 := bstep (se 2 (by rfl) ⟨431790, by rfl⟩ : syracuseStep 1151441 = 863581) B863581
theorem B299639 : Blo 235815 299639 := bstep (se 1 (by rfl) ⟨224729, by rfl⟩ : syracuseStep 299639 = 449459) B449459
theorem B299791 : Blo 235815 299791 := bstep (se 1 (by rfl) ⟨224843, by rfl⟩ : syracuseStep 299791 = 449687) B449687
theorem B267151 : Blo 235815 267151 := bstep (se 1 (by rfl) ⟨200363, by rfl⟩ : syracuseStep 267151 = 400727) B400727
theorem B299963 : Blo 235815 299963 := bstep (se 1 (by rfl) ⟨224972, by rfl⟩ : syracuseStep 299963 = 449945) B449945
theorem B398351 : Blo 235815 398351 := bstep (se 1 (by rfl) ⟨298763, by rfl⟩ : syracuseStep 398351 = 597527) B597527
theorem B267655 : Blo 235815 267655 := bstep (se 1 (by rfl) ⟨200741, by rfl⟩ : syracuseStep 267655 = 401483) B401483
theorem B398891 : Blo 235815 398891 := bstep (se 1 (by rfl) ⟨299168, by rfl⟩ : syracuseStep 398891 = 598337) B598337
theorem B267835 : Blo 235815 267835 := bstep (se 1 (by rfl) ⟨200876, by rfl⟩ : syracuseStep 267835 = 401753) B401753
theorem B300935 : Blo 235815 300935 := bstep (se 1 (by rfl) ⟨225701, by rfl⟩ : syracuseStep 300935 = 451403) B451403
theorem B399289 : Blo 235815 399289 := bstep (se 2 (by rfl) ⟨149733, by rfl⟩ : syracuseStep 399289 = 299467) B299467
theorem B1349561 : Blo 235815 1349561 := bstep (se 2 (by rfl) ⟨506085, by rfl⟩ : syracuseStep 1349561 = 1012171) B1012171
theorem B268303 : Blo 235815 268303 := bstep (se 1 (by rfl) ⟨201227, by rfl⟩ : syracuseStep 268303 = 402455) B402455
theorem B4921613 : Blo 235815 4921613 := bstep (se 3 (by rfl) ⟨922802, by rfl⟩ : syracuseStep 4921613 = 1845605) B1845605
theorem B235835 : Blo 235815 235835 := bstep (se 1 (by rfl) ⟨176876, by rfl⟩ : syracuseStep 235835 = 353753) B353753
theorem B530747 : Blo 235815 530747 := bstep (se 1 (by rfl) ⟨398060, by rfl⟩ : syracuseStep 530747 = 796121) B796121
theorem B235911 : Blo 235815 235911 := bstep (se 1 (by rfl) ⟨176933, by rfl⟩ : syracuseStep 235911 = 353867) B353867
theorem B235919 : Blo 235815 235919 := bstep (se 1 (by rfl) ⟨176939, by rfl⟩ : syracuseStep 235919 = 353879) B353879
theorem B14522773 : Blo 235815 14522773 := bstep (se 6 (by rfl) ⟨340377, by rfl⟩ : syracuseStep 14522773 = 680755) B680755
theorem B530873 : Blo 235815 530873 := bstep (se 2 (by rfl) ⟨199077, by rfl⟩ : syracuseStep 530873 = 398155) B398155
theorem B235963 : Blo 235815 235963 := bstep (se 1 (by rfl) ⟨176972, by rfl⟩ : syracuseStep 235963 = 353945) B353945
theorem B956881 : Blo 235815 956881 := bstep (se 2 (by rfl) ⟨358830, by rfl⟩ : syracuseStep 956881 = 717661) B717661
theorem B236039 : Blo 235815 236039 := bstep (se 1 (by rfl) ⟨177029, by rfl⟩ : syracuseStep 236039 = 354059) B354059
theorem B268807 : Blo 235815 268807 := bstep (se 1 (by rfl) ⟨201605, by rfl⟩ : syracuseStep 268807 = 403211) B403211
theorem B236047 : Blo 235815 236047 := bstep (se 1 (by rfl) ⟨177035, by rfl⟩ : syracuseStep 236047 = 354071) B354071
theorem B301583 : Blo 235815 301583 := bstep (se 1 (by rfl) ⟨226187, by rfl⟩ : syracuseStep 301583 = 452375) B452375
theorem B236091 : Blo 235815 236091 := bstep (se 1 (by rfl) ⟨177068, by rfl⟩ : syracuseStep 236091 = 354137) B354137
theorem B3054145 : Blo 235815 3054145 := bstep (se 2 (by rfl) ⟨1145304, by rfl⟩ : syracuseStep 3054145 = 2290609) B2290609
theorem B399991 : Blo 235815 399991 := bstep (se 1 (by rfl) ⟨299993, by rfl⟩ : syracuseStep 399991 = 599987) B599987
theorem B236167 : Blo 235815 236167 := bstep (se 1 (by rfl) ⟨177125, by rfl⟩ : syracuseStep 236167 = 354251) B354251
theorem B236175 : Blo 235815 236175 := bstep (se 1 (by rfl) ⟨177131, by rfl⟩ : syracuseStep 236175 = 354263) B354263
theorem B236219 : Blo 235815 236219 := bstep (se 1 (by rfl) ⟨177164, by rfl⟩ : syracuseStep 236219 = 354329) B354329
theorem B367291 : Blo 235815 367291 := bstep (se 1 (by rfl) ⟨275468, by rfl⟩ : syracuseStep 367291 = 550937) B550937
theorem B268987 : Blo 235815 268987 := bstep (se 1 (by rfl) ⟨201740, by rfl⟩ : syracuseStep 268987 = 403481) B403481
theorem B1219265 : Blo 235815 1219265 := bstep (se 2 (by rfl) ⟨457224, by rfl⟩ : syracuseStep 1219265 = 914449) B914449
theorem B236295 : Blo 235815 236295 := bstep (se 1 (by rfl) ⟨177221, by rfl⟩ : syracuseStep 236295 = 354443) B354443
theorem B531215 : Blo 235815 531215 := bstep (se 1 (by rfl) ⟨398411, by rfl⟩ : syracuseStep 531215 = 796823) B796823
theorem B236303 : Blo 235815 236303 := bstep (se 1 (by rfl) ⟨177227, by rfl⟩ : syracuseStep 236303 = 354455) B354455
theorem B531233 : Blo 235815 531233 := bstep (se 2 (by rfl) ⟨199212, by rfl⟩ : syracuseStep 531233 = 398425) B398425
theorem B236347 : Blo 235815 236347 := bstep (se 1 (by rfl) ⟨177260, by rfl⟩ : syracuseStep 236347 = 354521) B354521
theorem B400187 : Blo 235815 400187 := bstep (se 1 (by rfl) ⟨300140, by rfl⟩ : syracuseStep 400187 = 600281) B600281
theorem B1284923 : Blo 235815 1284923 := bstep (se 1 (by rfl) ⟨963692, by rfl⟩ : syracuseStep 1284923 = 1927385) B1927385
theorem B1088315 : Blo 235815 1088315 := bstep (se 1 (by rfl) ⟨816236, by rfl⟩ : syracuseStep 1088315 = 1632473) B1632473
theorem B236423 : Blo 235815 236423 := bstep (se 1 (by rfl) ⟨177317, by rfl⟩ : syracuseStep 236423 = 354635) B354635
theorem B236431 : Blo 235815 236431 := bstep (se 1 (by rfl) ⟨177323, by rfl⟩ : syracuseStep 236431 = 354647) B354647
theorem B236475 : Blo 235815 236475 := bstep (se 1 (by rfl) ⟨177356, by rfl⟩ : syracuseStep 236475 = 354713) B354713
theorem B236551 : Blo 235815 236551 := bstep (se 1 (by rfl) ⟨177413, by rfl⟩ : syracuseStep 236551 = 354827) B354827
theorem B236559 : Blo 235815 236559 := bstep (se 1 (by rfl) ⟨177419, by rfl⟩ : syracuseStep 236559 = 354839) B354839
theorem B236603 : Blo 235815 236603 := bstep (se 1 (by rfl) ⟨177452, by rfl⟩ : syracuseStep 236603 = 354905) B354905
theorem B531575 : Blo 235815 531575 := bstep (se 1 (by rfl) ⟨398681, by rfl⟩ : syracuseStep 531575 = 797363) B797363
theorem B236679 : Blo 235815 236679 := bstep (se 1 (by rfl) ⟨177509, by rfl⟩ : syracuseStep 236679 = 355019) B355019
theorem B236687 : Blo 235815 236687 := bstep (se 1 (by rfl) ⟨177515, by rfl⟩ : syracuseStep 236687 = 355031) B355031
theorem B269455 : Blo 235815 269455 := bstep (se 1 (by rfl) ⟨202091, by rfl⟩ : syracuseStep 269455 = 404183) B404183
theorem B236731 : Blo 235815 236731 := bstep (se 1 (by rfl) ⟨177548, by rfl⟩ : syracuseStep 236731 = 355097) B355097
theorem B400585 : Blo 235815 400585 := bstep (se 2 (by rfl) ⟨150219, by rfl⟩ : syracuseStep 400585 = 300439) B300439
theorem B236807 : Blo 235815 236807 := bstep (se 1 (by rfl) ⟨177605, by rfl⟩ : syracuseStep 236807 = 355211) B355211
theorem B236815 : Blo 235815 236815 := bstep (se 1 (by rfl) ⟨177611, by rfl⟩ : syracuseStep 236815 = 355223) B355223
theorem B531755 : Blo 235815 531755 := bstep (se 1 (by rfl) ⟨398816, by rfl⟩ : syracuseStep 531755 = 797633) B797633
theorem B1383731 : Blo 235815 1383731 := bstep (se 1 (by rfl) ⟨1037798, by rfl⟩ : syracuseStep 1383731 = 2075597) B2075597
theorem B236859 : Blo 235815 236859 := bstep (se 1 (by rfl) ⟨177644, by rfl⟩ : syracuseStep 236859 = 355289) B355289
theorem B236935 : Blo 235815 236935 := bstep (se 1 (by rfl) ⟨177701, by rfl⟩ : syracuseStep 236935 = 355403) B355403
theorem B236943 : Blo 235815 236943 := bstep (se 1 (by rfl) ⟨177707, by rfl⟩ : syracuseStep 236943 = 355415) B355415
theorem B597395 : Blo 235815 597395 := bstep (se 1 (by rfl) ⟨448046, by rfl⟩ : syracuseStep 597395 = 896093) B896093
theorem B236987 : Blo 235815 236987 := bstep (se 1 (by rfl) ⟨177740, by rfl⟩ : syracuseStep 236987 = 355481) B355481
theorem B4660739 : Blo 235815 4660739 := bstep (se 1 (by rfl) ⟨3495554, by rfl⟩ : syracuseStep 4660739 = 6991109) B6991109
theorem B237063 : Blo 235815 237063 := bstep (se 1 (by rfl) ⟨177797, by rfl⟩ : syracuseStep 237063 = 355595) B355595
theorem B237071 : Blo 235815 237071 := bstep (se 1 (by rfl) ⟨177803, by rfl⟩ : syracuseStep 237071 = 355607) B355607
theorem B237115 : Blo 235815 237115 := bstep (se 1 (by rfl) ⟨177836, by rfl⟩ : syracuseStep 237115 = 355673) B355673
theorem B237191 : Blo 235815 237191 := bstep (se 1 (by rfl) ⟨177893, by rfl⟩ : syracuseStep 237191 = 355787) B355787
theorem B237199 : Blo 235815 237199 := bstep (se 1 (by rfl) ⟨177899, by rfl⟩ : syracuseStep 237199 = 355799) B355799
theorem B532115 : Blo 235815 532115 := bstep (se 1 (by rfl) ⟨399086, by rfl⟩ : syracuseStep 532115 = 798173) B798173
theorem B597689 : Blo 235815 597689 := bstep (se 2 (by rfl) ⟨224133, by rfl⟩ : syracuseStep 597689 = 448267) B448267
theorem B237243 : Blo 235815 237243 := bstep (se 1 (by rfl) ⟨177932, by rfl⟩ : syracuseStep 237243 = 355865) B355865
theorem B532169 : Blo 235815 532169 := bstep (se 2 (by rfl) ⟨199563, by rfl⟩ : syracuseStep 532169 = 399127) B399127
theorem B1449701 : Blo 235815 1449701 := bstep (se 4 (by rfl) ⟨135909, by rfl⟩ : syracuseStep 1449701 = 271819) B271819
theorem B237319 : Blo 235815 237319 := bstep (se 1 (by rfl) ⟨177989, by rfl⟩ : syracuseStep 237319 = 355979) B355979
theorem B237327 : Blo 235815 237327 := bstep (se 1 (by rfl) ⟨177995, by rfl⟩ : syracuseStep 237327 = 355991) B355991
theorem B1351475 : Blo 235815 1351475 := bstep (se 1 (by rfl) ⟨1013606, by rfl⟩ : syracuseStep 1351475 = 2027213) B2027213
theorem B237371 : Blo 235815 237371 := bstep (se 1 (by rfl) ⟨178028, by rfl⟩ : syracuseStep 237371 = 356057) B356057
theorem B1711961 : Blo 235815 1711961 := bstep (se 2 (by rfl) ⟨641985, by rfl⟩ : syracuseStep 1711961 = 1283971) B1283971
theorem B237447 : Blo 235815 237447 := bstep (se 1 (by rfl) ⟨178085, by rfl⟩ : syracuseStep 237447 = 356171) B356171
theorem B401287 : Blo 235815 401287 := bstep (se 1 (by rfl) ⟨300965, by rfl⟩ : syracuseStep 401287 = 601931) B601931
theorem B237455 : Blo 235815 237455 := bstep (se 1 (by rfl) ⟨178091, by rfl⟩ : syracuseStep 237455 = 356183) B356183
theorem B237499 : Blo 235815 237499 := bstep (se 1 (by rfl) ⟨178124, by rfl⟩ : syracuseStep 237499 = 356249) B356249
theorem B237575 : Blo 235815 237575 := bstep (se 1 (by rfl) ⟨178181, by rfl⟩ : syracuseStep 237575 = 356363) B356363
theorem B237583 : Blo 235815 237583 := bstep (se 1 (by rfl) ⟨178187, by rfl⟩ : syracuseStep 237583 = 356375) B356375
theorem B237627 : Blo 235815 237627 := bstep (se 1 (by rfl) ⟨178220, by rfl⟩ : syracuseStep 237627 = 356441) B356441
theorem B237703 : Blo 235815 237703 := bstep (se 1 (by rfl) ⟨178277, by rfl⟩ : syracuseStep 237703 = 356555) B356555
theorem B237711 : Blo 235815 237711 := bstep (se 1 (by rfl) ⟨178283, by rfl⟩ : syracuseStep 237711 = 356567) B356567
theorem B237755 : Blo 235815 237755 := bstep (se 1 (by rfl) ⟨178316, by rfl⟩ : syracuseStep 237755 = 356633) B356633
theorem B237831 : Blo 235815 237831 := bstep (se 1 (by rfl) ⟨178373, by rfl⟩ : syracuseStep 237831 = 356747) B356747
theorem B237839 : Blo 235815 237839 := bstep (se 1 (by rfl) ⟨178379, by rfl⟩ : syracuseStep 237839 = 356759) B356759
theorem B237883 : Blo 235815 237883 := bstep (se 1 (by rfl) ⟨178412, by rfl⟩ : syracuseStep 237883 = 356825) B356825
theorem B598387 : Blo 235815 598387 := bstep (se 1 (by rfl) ⟨448790, by rfl⟩ : syracuseStep 598387 = 897581) B897581
theorem B729479 : Blo 235815 729479 := bstep (se 1 (by rfl) ⟨547109, by rfl⟩ : syracuseStep 729479 = 1094219) B1094219
theorem B532871 : Blo 235815 532871 := bstep (se 1 (by rfl) ⟨399653, by rfl⟩ : syracuseStep 532871 = 799307) B799307
theorem B237959 : Blo 235815 237959 := bstep (se 1 (by rfl) ⟨178469, by rfl⟩ : syracuseStep 237959 = 356939) B356939
theorem B237967 : Blo 235815 237967 := bstep (se 1 (by rfl) ⟨178475, by rfl⟩ : syracuseStep 237967 = 356951) B356951
theorem B17375633 : Blo 235815 17375633 := bstep (se 2 (by rfl) ⟨6515862, by rfl⟩ : syracuseStep 17375633 = 13031725) B13031725
theorem B1810835 : Blo 235815 1810835 := bstep (se 1 (by rfl) ⟨1358126, by rfl⟩ : syracuseStep 1810835 = 2716253) B2716253
theorem B238011 : Blo 235815 238011 := bstep (se 1 (by rfl) ⟨178508, by rfl⟩ : syracuseStep 238011 = 357017) B357017
theorem B598529 : Blo 235815 598529 := bstep (se 2 (by rfl) ⟨224448, by rfl⟩ : syracuseStep 598529 = 448897) B448897
theorem B238087 : Blo 235815 238087 := bstep (se 1 (by rfl) ⟨178565, by rfl⟩ : syracuseStep 238087 = 357131) B357131
theorem B238095 : Blo 235815 238095 := bstep (se 1 (by rfl) ⟨178571, by rfl⟩ : syracuseStep 238095 = 357143) B357143
theorem B401935 : Blo 235815 401935 := bstep (se 1 (by rfl) ⟨301451, by rfl⟩ : syracuseStep 401935 = 602903) B602903
theorem B533051 : Blo 235815 533051 := bstep (se 1 (by rfl) ⟨399788, by rfl⟩ : syracuseStep 533051 = 799577) B799577
theorem B238139 : Blo 235815 238139 := bstep (se 1 (by rfl) ⟨178604, by rfl⟩ : syracuseStep 238139 = 357209) B357209
theorem B238215 : Blo 235815 238215 := bstep (se 1 (by rfl) ⟨178661, by rfl⟩ : syracuseStep 238215 = 357323) B357323
theorem B238223 : Blo 235815 238223 := bstep (se 1 (by rfl) ⟨178667, by rfl⟩ : syracuseStep 238223 = 357335) B357335
theorem B533177 : Blo 235815 533177 := bstep (se 2 (by rfl) ⟨199941, by rfl⟩ : syracuseStep 533177 = 399883) B399883
theorem B238267 : Blo 235815 238267 := bstep (se 1 (by rfl) ⟨178700, by rfl⟩ : syracuseStep 238267 = 357401) B357401
theorem B238343 : Blo 235815 238343 := bstep (se 1 (by rfl) ⟨178757, by rfl⟩ : syracuseStep 238343 = 357515) B357515
theorem B238351 : Blo 235815 238351 := bstep (se 1 (by rfl) ⟨178763, by rfl⟩ : syracuseStep 238351 = 357527) B357527
theorem B238395 : Blo 235815 238395 := bstep (se 1 (by rfl) ⟨178796, by rfl⟩ : syracuseStep 238395 = 357593) B357593
theorem B238471 : Blo 235815 238471 := bstep (se 1 (by rfl) ⟨178853, by rfl⟩ : syracuseStep 238471 = 357707) B357707
theorem B238479 : Blo 235815 238479 := bstep (se 1 (by rfl) ⟨178859, by rfl⟩ : syracuseStep 238479 = 357719) B357719
theorem B238523 : Blo 235815 238523 := bstep (se 1 (by rfl) ⟨178892, by rfl⟩ : syracuseStep 238523 = 357785) B357785
theorem B598985 : Blo 235815 598985 := bstep (se 2 (by rfl) ⟨224619, by rfl⟩ : syracuseStep 598985 = 449239) B449239
theorem B238599 : Blo 235815 238599 := bstep (se 1 (by rfl) ⟨178949, by rfl⟩ : syracuseStep 238599 = 357899) B357899
theorem B533519 : Blo 235815 533519 := bstep (se 1 (by rfl) ⟨400139, by rfl⟩ : syracuseStep 533519 = 800279) B800279
theorem B238607 : Blo 235815 238607 := bstep (se 1 (by rfl) ⟨178955, by rfl⟩ : syracuseStep 238607 = 357911) B357911
theorem B533537 : Blo 235815 533537 := bstep (se 2 (by rfl) ⟨200076, by rfl⟩ : syracuseStep 533537 = 400153) B400153
theorem B402475 : Blo 235815 402475 := bstep (se 1 (by rfl) ⟨301856, by rfl⟩ : syracuseStep 402475 = 603713) B603713
theorem B238651 : Blo 235815 238651 := bstep (se 1 (by rfl) ⟨178988, by rfl⟩ : syracuseStep 238651 = 357977) B357977
theorem B238727 : Blo 235815 238727 := bstep (se 1 (by rfl) ⟨179045, by rfl⟩ : syracuseStep 238727 = 358091) B358091
theorem B238735 : Blo 235815 238735 := bstep (se 1 (by rfl) ⟨179051, by rfl⟩ : syracuseStep 238735 = 358103) B358103
theorem B402617 : Blo 235815 402617 := bstep (se 2 (by rfl) ⟨150981, by rfl⟩ : syracuseStep 402617 = 301963) B301963
theorem B238779 : Blo 235815 238779 := bstep (se 1 (by rfl) ⟨179084, by rfl⟩ : syracuseStep 238779 = 358169) B358169
theorem B1352933 : Blo 235815 1352933 := bstep (se 4 (by rfl) ⟨126837, by rfl⟩ : syracuseStep 1352933 = 253675) B253675
theorem B795905 : Blo 235815 795905 := bstep (se 2 (by rfl) ⟨298464, by rfl⟩ : syracuseStep 795905 = 596929) B596929
theorem B238855 : Blo 235815 238855 := bstep (se 1 (by rfl) ⟨179141, by rfl⟩ : syracuseStep 238855 = 358283) B358283
theorem B238863 : Blo 235815 238863 := bstep (se 1 (by rfl) ⟨179147, by rfl⟩ : syracuseStep 238863 = 358295) B358295
theorem B599339 : Blo 235815 599339 := bstep (se 1 (by rfl) ⟨449504, by rfl⟩ : syracuseStep 599339 = 899009) B899009
theorem B238907 : Blo 235815 238907 := bstep (se 1 (by rfl) ⟨179180, by rfl⟩ : syracuseStep 238907 = 358361) B358361
theorem B533879 : Blo 235815 533879 := bstep (se 1 (by rfl) ⟨400409, by rfl⟩ : syracuseStep 533879 = 800819) B800819
theorem B238983 : Blo 235815 238983 := bstep (se 1 (by rfl) ⟨179237, by rfl⟩ : syracuseStep 238983 = 358475) B358475
theorem B238991 : Blo 235815 238991 := bstep (se 1 (by rfl) ⟨179243, by rfl⟩ : syracuseStep 238991 = 358487) B358487
theorem B239035 : Blo 235815 239035 := bstep (se 1 (by rfl) ⟨179276, by rfl⟩ : syracuseStep 239035 = 358553) B358553
theorem B239111 : Blo 235815 239111 := bstep (se 1 (by rfl) ⟨179333, by rfl⟩ : syracuseStep 239111 = 358667) B358667
theorem B239119 : Blo 235815 239119 := bstep (se 1 (by rfl) ⟨179339, by rfl⟩ : syracuseStep 239119 = 358679) B358679
theorem B534059 : Blo 235815 534059 := bstep (se 1 (by rfl) ⟨400544, by rfl⟩ : syracuseStep 534059 = 801089) B801089
theorem B239163 : Blo 235815 239163 := bstep (se 1 (by rfl) ⟨179372, by rfl⟩ : syracuseStep 239163 = 358745) B358745
theorem B239239 : Blo 235815 239239 := bstep (se 1 (by rfl) ⟨179429, by rfl⟩ : syracuseStep 239239 = 358859) B358859
theorem B239247 : Blo 235815 239247 := bstep (se 1 (by rfl) ⟨179435, by rfl⟩ : syracuseStep 239247 = 358871) B358871
theorem B239291 : Blo 235815 239291 := bstep (se 1 (by rfl) ⟨179468, by rfl⟩ : syracuseStep 239291 = 358937) B358937
theorem B239367 : Blo 235815 239367 := bstep (se 1 (by rfl) ⟨179525, by rfl⟩ : syracuseStep 239367 = 359051) B359051
theorem B239375 : Blo 235815 239375 := bstep (se 1 (by rfl) ⟨179531, by rfl⟩ : syracuseStep 239375 = 359063) B359063
theorem B239419 : Blo 235815 239419 := bstep (se 1 (by rfl) ⟨179564, by rfl⟩ : syracuseStep 239419 = 359129) B359129
theorem B403319 : Blo 235815 403319 := bstep (se 1 (by rfl) ⟨302489, by rfl⟩ : syracuseStep 403319 = 604979) B604979
theorem B239495 : Blo 235815 239495 := bstep (se 1 (by rfl) ⟨179621, by rfl⟩ : syracuseStep 239495 = 359243) B359243
theorem B239503 : Blo 235815 239503 := bstep (se 1 (by rfl) ⟨179627, by rfl⟩ : syracuseStep 239503 = 359255) B359255
theorem B1353617 : Blo 235815 1353617 := bstep (se 2 (by rfl) ⟨507606, by rfl⟩ : syracuseStep 1353617 = 1015213) B1015213
theorem B534419 : Blo 235815 534419 := bstep (se 1 (by rfl) ⟨400814, by rfl⟩ : syracuseStep 534419 = 801629) B801629
theorem B239547 : Blo 235815 239547 := bstep (se 1 (by rfl) ⟨179660, by rfl⟩ : syracuseStep 239547 = 359321) B359321
theorem B534473 : Blo 235815 534473 := bstep (se 2 (by rfl) ⟨200427, by rfl⟩ : syracuseStep 534473 = 400855) B400855
theorem B239623 : Blo 235815 239623 := bstep (se 1 (by rfl) ⟨179717, by rfl⟩ : syracuseStep 239623 = 359435) B359435
theorem B239631 : Blo 235815 239631 := bstep (se 1 (by rfl) ⟨179723, by rfl⟩ : syracuseStep 239631 = 359447) B359447
theorem B796715 : Blo 235815 796715 := bstep (se 1 (by rfl) ⟨597536, by rfl⟩ : syracuseStep 796715 = 1195073) B1195073
theorem B239675 : Blo 235815 239675 := bstep (se 1 (by rfl) ⟨179756, by rfl⟩ : syracuseStep 239675 = 359513) B359513
theorem B239751 : Blo 235815 239751 := bstep (se 1 (by rfl) ⟨179813, by rfl⟩ : syracuseStep 239751 = 359627) B359627
theorem B239759 : Blo 235815 239759 := bstep (se 1 (by rfl) ⟨179819, by rfl⟩ : syracuseStep 239759 = 359639) B359639
theorem B239803 : Blo 235815 239803 := bstep (se 1 (by rfl) ⟨179852, by rfl⟩ : syracuseStep 239803 = 359705) B359705
theorem B600331 : Blo 235815 600331 := bstep (se 1 (by rfl) ⟨450248, by rfl⟩ : syracuseStep 600331 = 900497) B900497
theorem B403771 : Blo 235815 403771 := bstep (se 1 (by rfl) ⟨302828, by rfl⟩ : syracuseStep 403771 = 605657) B605657
theorem B600473 : Blo 235815 600473 := bstep (se 2 (by rfl) ⟨225177, by rfl⟩ : syracuseStep 600473 = 450355) B450355
theorem B338347 : Blo 235815 338347 := bstep (se 1 (by rfl) ⟨253760, by rfl⟩ : syracuseStep 338347 = 507521) B507521
theorem B1943993 : Blo 235815 1943993 := bstep (se 2 (by rfl) ⟨728997, by rfl⟩ : syracuseStep 1943993 = 1457995) B1457995
theorem B403913 : Blo 235815 403913 := bstep (se 2 (by rfl) ⟨151467, by rfl⟩ : syracuseStep 403913 = 302935) B302935
theorem B600635 : Blo 235815 600635 := bstep (se 1 (by rfl) ⟨450476, by rfl⟩ : syracuseStep 600635 = 900953) B900953
theorem B895607 : Blo 235815 895607 := bstep (se 1 (by rfl) ⟨671705, by rfl⟩ : syracuseStep 895607 = 1343411) B1343411
theorem B535175 : Blo 235815 535175 := bstep (se 1 (by rfl) ⟨401381, by rfl⟩ : syracuseStep 535175 = 802763) B802763
theorem B338575 : Blo 235815 338575 := bstep (se 1 (by rfl) ⟨253931, by rfl⟩ : syracuseStep 338575 = 507863) B507863
theorem B371401 : Blo 235815 371401 := bstep (se 2 (by rfl) ⟨139275, by rfl⟩ : syracuseStep 371401 = 278551) B278551
theorem B535355 : Blo 235815 535355 := bstep (se 1 (by rfl) ⟨401516, by rfl⟩ : syracuseStep 535355 = 803033) B803033
theorem B600979 : Blo 235815 600979 := bstep (se 1 (by rfl) ⟨450734, by rfl⟩ : syracuseStep 600979 = 901469) B901469
theorem B1354643 : Blo 235815 1354643 := bstep (se 1 (by rfl) ⟨1015982, by rfl⟩ : syracuseStep 1354643 = 2031965) B2031965
theorem B535481 : Blo 235815 535481 := bstep (se 2 (by rfl) ⟨200805, by rfl⟩ : syracuseStep 535481 = 401611) B401611
theorem B338951 : Blo 235815 338951 := bstep (se 1 (by rfl) ⟨254213, by rfl⟩ : syracuseStep 338951 = 508427) B508427
theorem B1453085 : Blo 235815 1453085 := bstep (se 3 (by rfl) ⟨272453, by rfl⟩ : syracuseStep 1453085 = 544907) B544907
theorem B601121 : Blo 235815 601121 := bstep (se 2 (by rfl) ⟨225420, by rfl⟩ : syracuseStep 601121 = 450841) B450841
theorem B404615 : Blo 235815 404615 := bstep (se 1 (by rfl) ⟨303461, by rfl⟩ : syracuseStep 404615 = 606923) B606923
theorem B535823 : Blo 235815 535823 := bstep (se 1 (by rfl) ⟨401867, by rfl⟩ : syracuseStep 535823 = 803735) B803735
theorem B535841 : Blo 235815 535841 := bstep (se 2 (by rfl) ⟨200940, by rfl⟩ : syracuseStep 535841 = 401881) B401881
theorem B798011 : Blo 235815 798011 := bstep (se 1 (by rfl) ⟨598508, by rfl⟩ : syracuseStep 798011 = 1197017) B1197017
theorem B568723 : Blo 235815 568723 := bstep (se 1 (by rfl) ⟨426542, by rfl⟩ : syracuseStep 568723 = 853085) B853085
theorem B2436637 : Blo 235815 2436637 := bstep (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) B913739
theorem B896579 : Blo 235815 896579 := bstep (se 1 (by rfl) ⟨672434, by rfl⟩ : syracuseStep 896579 = 1344869) B1344869
theorem B2305655 : Blo 235815 2305655 := bstep (se 1 (by rfl) ⟨1729241, by rfl⟩ : syracuseStep 2305655 = 3458483) B3458483
theorem B536183 : Blo 235815 536183 := bstep (se 1 (by rfl) ⟨402137, by rfl⟩ : syracuseStep 536183 = 804275) B804275
theorem B2076353 : Blo 235815 2076353 := bstep (se 2 (by rfl) ⟨778632, by rfl⟩ : syracuseStep 2076353 = 1557265) B1557265
theorem B798497 : Blo 235815 798497 := bstep (se 2 (by rfl) ⟨299436, by rfl⟩ : syracuseStep 798497 = 598873) B598873
theorem B536363 : Blo 235815 536363 := bstep (se 1 (by rfl) ⟨402272, by rfl⟩ : syracuseStep 536363 = 804545) B804545
theorem B602113 : Blo 235815 602113 := bstep (se 2 (by rfl) ⟨225792, by rfl⟩ : syracuseStep 602113 = 451585) B451585
theorem B536723 : Blo 235815 536723 := bstep (se 1 (by rfl) ⟨402542, by rfl⟩ : syracuseStep 536723 = 805085) B805085
theorem B536777 : Blo 235815 536777 := bstep (se 2 (by rfl) ⟨201291, by rfl⟩ : syracuseStep 536777 = 402583) B402583
theorem B1716461 : Blo 235815 1716461 := bstep (se 3 (by rfl) ⟨321836, by rfl⟩ : syracuseStep 1716461 = 643673) B643673
theorem B799091 : Blo 235815 799091 := bstep (se 1 (by rfl) ⟨599318, by rfl⟩ : syracuseStep 799091 = 1198637) B1198637
theorem B3322259 : Blo 235815 3322259 := bstep (se 1 (by rfl) ⟨2491694, by rfl⟩ : syracuseStep 3322259 = 4983389) B4983389
theorem B340409 : Blo 235815 340409 := bstep (se 2 (by rfl) ⟨127653, by rfl⟩ : syracuseStep 340409 = 255307) B255307
theorem B602711 : Blo 235815 602711 := bstep (se 1 (by rfl) ⟨452033, by rfl⟩ : syracuseStep 602711 = 904067) B904067
theorem B2044709 : Blo 235815 2044709 := bstep (se 4 (by rfl) ⟨191691, by rfl⟩ : syracuseStep 2044709 = 383383) B383383
theorem B602923 : Blo 235815 602923 := bstep (se 1 (by rfl) ⟨452192, by rfl⟩ : syracuseStep 602923 = 904385) B904385
theorem B537479 : Blo 235815 537479 := bstep (se 1 (by rfl) ⟨403109, by rfl⟩ : syracuseStep 537479 = 806219) B806219
theorem B603065 : Blo 235815 603065 := bstep (se 2 (by rfl) ⟨226149, by rfl⟩ : syracuseStep 603065 = 452299) B452299
theorem B963613 : Blo 235815 963613 := bstep (se 3 (by rfl) ⟨180677, by rfl⟩ : syracuseStep 963613 = 361355) B361355
theorem B537659 : Blo 235815 537659 := bstep (se 1 (by rfl) ⟨403244, by rfl⟩ : syracuseStep 537659 = 806489) B806489
theorem B341065 : Blo 235815 341065 := bstep (se 2 (by rfl) ⟨127899, by rfl⟩ : syracuseStep 341065 = 255799) B255799
theorem B537785 : Blo 235815 537785 := bstep (se 2 (by rfl) ⟨201669, by rfl⟩ : syracuseStep 537785 = 403339) B403339
theorem B898249 : Blo 235815 898249 := bstep (se 2 (by rfl) ⟨336843, by rfl⟩ : syracuseStep 898249 = 673687) B673687
theorem B767177 : Blo 235815 767177 := bstep (se 2 (by rfl) ⟨287691, by rfl⟩ : syracuseStep 767177 = 575383) B575383
theorem B406799 : Blo 235815 406799 := bstep (se 1 (by rfl) ⟨305099, by rfl⟩ : syracuseStep 406799 = 610199) B610199
theorem B341263 : Blo 235815 341263 := bstep (se 1 (by rfl) ⟨255947, by rfl⟩ : syracuseStep 341263 = 511895) B511895
theorem B538127 : Blo 235815 538127 := bstep (se 1 (by rfl) ⟨403595, by rfl⟩ : syracuseStep 538127 = 807191) B807191
theorem B538145 : Blo 235815 538145 := bstep (se 2 (by rfl) ⟨201804, by rfl⟩ : syracuseStep 538145 = 403609) B403609
theorem B538487 : Blo 235815 538487 := bstep (se 1 (by rfl) ⟨403865, by rfl⟩ : syracuseStep 538487 = 807731) B807731
theorem B604057 : Blo 235815 604057 := bstep (se 2 (by rfl) ⟨226521, by rfl⟩ : syracuseStep 604057 = 453043) B453043
theorem B538667 : Blo 235815 538667 := bstep (se 1 (by rfl) ⟨404000, by rfl⟩ : syracuseStep 538667 = 808001) B808001
theorem B604219 : Blo 235815 604219 := bstep (se 1 (by rfl) ⟨453164, by rfl⟩ : syracuseStep 604219 = 906329) B906329
theorem B1226819 : Blo 235815 1226819 := bstep (se 1 (by rfl) ⟨920114, by rfl⟩ : syracuseStep 1226819 = 1840229) B1840229
theorem B604361 : Blo 235815 604361 := bstep (se 2 (by rfl) ⟨226635, by rfl⟩ : syracuseStep 604361 = 453271) B453271
theorem B3029237 : Blo 235815 3029237 := bstep (se 5 (by rfl) ⟨141995, by rfl⟩ : syracuseStep 3029237 = 283991) B283991
theorem B539027 : Blo 235815 539027 := bstep (se 1 (by rfl) ⟨404270, by rfl⟩ : syracuseStep 539027 = 808541) B808541
theorem B1194425 : Blo 235815 1194425 := bstep (se 2 (by rfl) ⟨447909, by rfl⟩ : syracuseStep 1194425 = 895819) B895819
theorem B539081 : Blo 235815 539081 := bstep (se 2 (by rfl) ⟨202155, by rfl⟩ : syracuseStep 539081 = 404311) B404311
theorem B604705 : Blo 235815 604705 := bstep (se 2 (by rfl) ⟨226764, by rfl⟩ : syracuseStep 604705 = 453529) B453529
theorem B637739 : Blo 235815 637739 := bstep (se 1 (by rfl) ⟨478304, by rfl⟩ : syracuseStep 637739 = 956609) B956609
theorem B801683 : Blo 235815 801683 := bstep (se 1 (by rfl) ⟨601262, by rfl⟩ : syracuseStep 801683 = 1202525) B1202525
theorem B5160023 : Blo 235815 5160023 := bstep (se 1 (by rfl) ⟨3870017, by rfl⟩ : syracuseStep 5160023 = 7740035) B7740035
theorem B605303 : Blo 235815 605303 := bstep (se 1 (by rfl) ⟨453977, by rfl⟩ : syracuseStep 605303 = 907955) B907955
theorem B507179 : Blo 235815 507179 := bstep (se 1 (by rfl) ⟨380384, by rfl⟩ : syracuseStep 507179 = 760769) B760769
theorem B900467 : Blo 235815 900467 := bstep (se 1 (by rfl) ⟨675350, by rfl⟩ : syracuseStep 900467 = 1350701) B1350701
theorem B572807 : Blo 235815 572807 := bstep (se 1 (by rfl) ⟨429605, by rfl⟩ : syracuseStep 572807 = 859211) B859211
theorem B933419 : Blo 235815 933419 := bstep (se 1 (by rfl) ⟨700064, by rfl⟩ : syracuseStep 933419 = 1400129) B1400129
theorem B507539 : Blo 235815 507539 := bstep (se 1 (by rfl) ⟨380654, by rfl⟩ : syracuseStep 507539 = 761309) B761309
theorem B1195721 : Blo 235815 1195721 := bstep (se 2 (by rfl) ⟨448395, by rfl⟩ : syracuseStep 1195721 = 896791) B896791
theorem B1261363 : Blo 235815 1261363 := bstep (se 1 (by rfl) ⟨946022, by rfl⟩ : syracuseStep 1261363 = 1892045) B1892045
theorem B638873 : Blo 235815 638873 := bstep (se 2 (by rfl) ⟨239577, by rfl⟩ : syracuseStep 638873 = 479155) B479155
theorem B573575 : Blo 235815 573575 := bstep (se 1 (by rfl) ⟨430181, by rfl⟩ : syracuseStep 573575 = 860363) B860363
theorem B803087 : Blo 235815 803087 := bstep (se 1 (by rfl) ⟨602315, by rfl⟩ : syracuseStep 803087 = 1204631) B1204631
theorem B606599 : Blo 235815 606599 := bstep (se 1 (by rfl) ⟨454949, by rfl⟩ : syracuseStep 606599 = 909899) B909899
theorem B606649 : Blo 235815 606649 := bstep (se 2 (by rfl) ⟨227493, by rfl⟩ : syracuseStep 606649 = 454987) B454987
theorem B541129 : Blo 235815 541129 := bstep (se 2 (by rfl) ⟨202923, by rfl⟩ : syracuseStep 541129 = 405847) B405847
theorem B10961365 : Blo 235815 10961365 := bstep (se 7 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 10961365 = 256907) B256907
theorem B803357 : Blo 235815 803357 := bstep (se 3 (by rfl) ⟨150629, by rfl⟩ : syracuseStep 803357 = 301259) B301259
theorem B672457 : Blo 235815 672457 := bstep (se 2 (by rfl) ⟨252171, by rfl⟩ : syracuseStep 672457 = 504343) B504343
theorem B4735705 : Blo 235815 4735705 := bstep (se 2 (by rfl) ⟨1775889, by rfl⟩ : syracuseStep 4735705 = 3551779) B3551779
theorem B3261221 : Blo 235815 3261221 := bstep (se 4 (by rfl) ⟨305739, by rfl⟩ : syracuseStep 3261221 = 611479) B611479
theorem B2278307 : Blo 235815 2278307 := bstep (se 1 (by rfl) ⟨1708730, by rfl⟩ : syracuseStep 2278307 = 3417461) B3417461
theorem B1360907 : Blo 235815 1360907 := bstep (se 1 (by rfl) ⟨1020680, by rfl⟩ : syracuseStep 1360907 = 2041361) B2041361
theorem B574721 : Blo 235815 574721 := bstep (se 2 (by rfl) ⟨215520, by rfl⟩ : syracuseStep 574721 = 431041) B431041
theorem B378155 : Blo 235815 378155 := bstep (se 1 (by rfl) ⟨283616, by rfl⟩ : syracuseStep 378155 = 567233) B567233
theorem B1230265 : Blo 235815 1230265 := bstep (se 2 (by rfl) ⟨461349, by rfl⟩ : syracuseStep 1230265 = 922699) B922699
theorem B902609 : Blo 235815 902609 := bstep (se 2 (by rfl) ⟨338478, by rfl⟩ : syracuseStep 902609 = 676957) B676957
theorem B902927 : Blo 235815 902927 := bstep (se 1 (by rfl) ⟨677195, by rfl⟩ : syracuseStep 902927 = 1354391) B1354391
theorem B804761 : Blo 235815 804761 := bstep (se 2 (by rfl) ⟨301785, by rfl⟩ : syracuseStep 804761 = 603571) B603571
theorem B1820987 : Blo 235815 1820987 := bstep (se 1 (by rfl) ⟨1365740, by rfl⟩ : syracuseStep 1820987 = 2731481) B2731481
theorem B608647 : Blo 235815 608647 := bstep (se 1 (by rfl) ⟨456485, by rfl⟩ : syracuseStep 608647 = 912971) B912971
theorem B674315 : Blo 235815 674315 := bstep (se 1 (by rfl) ⟨505736, by rfl⟩ : syracuseStep 674315 = 1011473) B1011473
theorem B805463 : Blo 235815 805463 := bstep (se 1 (by rfl) ⟨604097, by rfl⟩ : syracuseStep 805463 = 1208195) B1208195
theorem B1100729 : Blo 235815 1100729 := bstep (se 2 (by rfl) ⟨412773, by rfl⟩ : syracuseStep 1100729 = 825547) B825547
theorem B805949 : Blo 235815 805949 := bstep (se 3 (by rfl) ⟨151115, by rfl⟩ : syracuseStep 805949 = 302231) B302231
theorem B674963 : Blo 235815 674963 := bstep (se 1 (by rfl) ⟨506222, by rfl⟩ : syracuseStep 674963 = 1012445) B1012445
theorem B609623 : Blo 235815 609623 := bstep (se 1 (by rfl) ⟨457217, by rfl⟩ : syracuseStep 609623 = 914435) B914435
theorem B675191 : Blo 235815 675191 := bstep (se 1 (by rfl) ⟨506393, by rfl⟩ : syracuseStep 675191 = 1012787) B1012787
theorem B3067267 : Blo 235815 3067267 := bstep (se 1 (by rfl) ⟨2300450, by rfl⟩ : syracuseStep 3067267 = 4600901) B4600901
theorem B642505 : Blo 235815 642505 := bstep (se 2 (by rfl) ⟨240939, by rfl⟩ : syracuseStep 642505 = 481879) B481879
theorem B2215795 : Blo 235815 2215795 := bstep (se 1 (by rfl) ⟨1661846, by rfl⟩ : syracuseStep 2215795 = 3323693) B3323693
theorem B643133 : Blo 235815 643133 := bstep (se 3 (by rfl) ⟨120587, by rfl⟩ : syracuseStep 643133 = 241175) B241175
theorem B1364141 : Blo 235815 1364141 := bstep (se 3 (by rfl) ⟨255776, by rfl⟩ : syracuseStep 1364141 = 511553) B511553
theorem B381199 : Blo 235815 381199 := bstep (se 1 (by rfl) ⟨285899, by rfl⟩ : syracuseStep 381199 = 571799) B571799
theorem B971023 : Blo 235815 971023 := bstep (se 1 (by rfl) ⟨728267, by rfl⟩ : syracuseStep 971023 = 1456535) B1456535
theorem B807353 : Blo 235815 807353 := bstep (se 2 (by rfl) ⟨302757, by rfl⟩ : syracuseStep 807353 = 605515) B605515
theorem B1135619 : Blo 235815 1135619 := bstep (se 1 (by rfl) ⟨851714, by rfl⟩ : syracuseStep 1135619 = 1703429) B1703429
theorem B807947 : Blo 235815 807947 := bstep (se 1 (by rfl) ⟨605960, by rfl⟩ : syracuseStep 807947 = 1211921) B1211921
theorem B2184215 : Blo 235815 2184215 := bstep (se 1 (by rfl) ⟨1638161, by rfl⟩ : syracuseStep 2184215 = 3276323) B3276323
theorem B1528919 : Blo 235815 1528919 := bstep (se 1 (by rfl) ⟨1146689, by rfl⟩ : syracuseStep 1528919 = 2293379) B2293379
theorem B808055 : Blo 235815 808055 := bstep (se 1 (by rfl) ⟨606041, by rfl⟩ : syracuseStep 808055 = 1212083) B1212083
theorem B382153 : Blo 235815 382153 := bstep (se 2 (by rfl) ⟨143307, by rfl⟩ : syracuseStep 382153 = 286615) B286615
theorem B906497 : Blo 235815 906497 := bstep (se 2 (by rfl) ⟨339936, by rfl⟩ : syracuseStep 906497 = 679873) B679873
theorem B906511 : Blo 235815 906511 := bstep (se 1 (by rfl) ⟨679883, by rfl⟩ : syracuseStep 906511 = 1359767) B1359767
theorem B1365281 : Blo 235815 1365281 := bstep (se 2 (by rfl) ⟨511980, by rfl⟩ : syracuseStep 1365281 = 1023961) B1023961
theorem B480647 : Blo 235815 480647 := bstep (se 1 (by rfl) ⟨360485, by rfl⟩ : syracuseStep 480647 = 720971) B720971
theorem B2184583 : Blo 235815 2184583 := bstep (se 1 (by rfl) ⟨1638437, by rfl⟩ : syracuseStep 2184583 = 3276875) B3276875
theorem B1201553 : Blo 235815 1201553 := bstep (se 2 (by rfl) ⟨450582, by rfl⟩ : syracuseStep 1201553 = 901165) B901165
theorem B644669 : Blo 235815 644669 := bstep (se 3 (by rfl) ⟨120875, by rfl⟩ : syracuseStep 644669 = 241751) B241751
theorem B382583 : Blo 235815 382583 := bstep (se 1 (by rfl) ⟨286937, by rfl⟩ : syracuseStep 382583 = 573875) B573875
theorem B808649 : Blo 235815 808649 := bstep (se 2 (by rfl) ⟨303243, by rfl⟩ : syracuseStep 808649 = 606487) B606487
theorem B448571 : Blo 235815 448571 := bstep (se 1 (by rfl) ⟨336428, by rfl⟩ : syracuseStep 448571 = 672857) B672857
theorem B809351 : Blo 235815 809351 := bstep (se 1 (by rfl) ⟨607013, by rfl⟩ : syracuseStep 809351 = 1214027) B1214027
theorem B612793 : Blo 235815 612793 := bstep (se 2 (by rfl) ⟨229797, by rfl⟩ : syracuseStep 612793 = 459595) B459595
theorem B907787 : Blo 235815 907787 := bstep (se 1 (by rfl) ⟨680840, by rfl⟩ : syracuseStep 907787 = 1361681) B1361681
theorem B678415 : Blo 235815 678415 := bstep (se 1 (by rfl) ⟨508811, by rfl⟩ : syracuseStep 678415 = 1017623) B1017623
theorem B449057 : Blo 235815 449057 := bstep (se 2 (by rfl) ⟨168396, by rfl⟩ : syracuseStep 449057 = 336793) B336793
theorem B678689 : Blo 235815 678689 := bstep (se 2 (by rfl) ⟨254508, by rfl⟩ : syracuseStep 678689 = 509017) B509017
theorem B908167 : Blo 235815 908167 := bstep (se 1 (by rfl) ⟨681125, by rfl⟩ : syracuseStep 908167 = 1362251) B1362251
theorem B2579363 : Blo 235815 2579363 := bstep (se 1 (by rfl) ⟨1934522, by rfl⟩ : syracuseStep 2579363 = 3869045) B3869045
theorem B1137617 : Blo 235815 1137617 := bstep (se 2 (by rfl) ⟨426606, by rfl⟩ : syracuseStep 1137617 = 853213) B853213
theorem B482593 : Blo 235815 482593 := bstep (se 2 (by rfl) ⟨180972, by rfl⟩ : syracuseStep 482593 = 361945) B361945
theorem B1793339 : Blo 235815 1793339 := bstep (se 1 (by rfl) ⟨1345004, by rfl⟩ : syracuseStep 1793339 = 2690009) B2690009
theorem B908729 : Blo 235815 908729 := bstep (se 2 (by rfl) ⟨340773, by rfl⟩ : syracuseStep 908729 = 681547) B681547
theorem B1203659 : Blo 235815 1203659 := bstep (se 1 (by rfl) ⟨902744, by rfl⟩ : syracuseStep 1203659 = 1805489) B1805489
theorem B679691 : Blo 235815 679691 := bstep (se 1 (by rfl) ⟨509768, by rfl⟩ : syracuseStep 679691 = 1019537) B1019537
theorem B1203983 : Blo 235815 1203983 := bstep (se 1 (by rfl) ⟨902987, by rfl⟩ : syracuseStep 1203983 = 1805975) B1805975
theorem B2023217 : Blo 235815 2023217 := bstep (se 2 (by rfl) ⟨758706, by rfl⟩ : syracuseStep 2023217 = 1517413) B1517413
theorem B12443543 : Blo 235815 12443543 := bstep (se 1 (by rfl) ⟨9332657, by rfl⟩ : syracuseStep 12443543 = 18665315) B18665315
theorem B680089 : Blo 235815 680089 := bstep (se 2 (by rfl) ⟨255033, by rfl⟩ : syracuseStep 680089 = 510067) B510067
theorem B450859 : Blo 235815 450859 := bstep (se 1 (by rfl) ⟨338144, by rfl⟩ : syracuseStep 450859 = 676289) B676289
theorem B680339 : Blo 235815 680339 := bstep (se 1 (by rfl) ⟨510254, by rfl⟩ : syracuseStep 680339 = 1020509) B1020509
theorem B2023865 : Blo 235815 2023865 := bstep (se 2 (by rfl) ⟨758949, by rfl⟩ : syracuseStep 2023865 = 1517899) B1517899
theorem B451001 : Blo 235815 451001 := bstep (se 2 (by rfl) ⟨169125, by rfl⟩ : syracuseStep 451001 = 338251) B338251
theorem B1008139 : Blo 235815 1008139 := bstep (se 1 (by rfl) ⟨756104, by rfl⟩ : syracuseStep 1008139 = 1512209) B1512209
theorem B1368695 : Blo 235815 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B254863 : Blo 235815 254863 := bstep (se 1 (by rfl) ⟨191147, by rfl⟩ : syracuseStep 254863 = 382295) B382295
theorem B287759 : Blo 235815 287759 := bstep (se 1 (by rfl) ⟨215819, by rfl⟩ : syracuseStep 287759 = 431639) B431639
theorem B1532951 : Blo 235815 1532951 := bstep (se 1 (by rfl) ⟨1149713, by rfl⟩ : syracuseStep 1532951 = 2299427) B2299427
theorem B1303595 : Blo 235815 1303595 := bstep (se 1 (by rfl) ⟨977696, by rfl⟩ : syracuseStep 1303595 = 1955393) B1955393
theorem B320647 : Blo 235815 320647 := bstep (se 1 (by rfl) ⟨240485, by rfl⟩ : syracuseStep 320647 = 480971) B480971
theorem B1205441 : Blo 235815 1205441 := bstep (se 2 (by rfl) ⟨452040, by rfl⟩ : syracuseStep 1205441 = 904081) B904081
theorem B681331 : Blo 235815 681331 := bstep (se 1 (by rfl) ⟨510998, by rfl⟩ : syracuseStep 681331 = 1021997) B1021997
theorem B1533329 : Blo 235815 1533329 := bstep (se 2 (by rfl) ⟨574998, by rfl⟩ : syracuseStep 1533329 = 1149997) B1149997
theorem B353723 : Blo 235815 353723 := bstep (se 1 (by rfl) ⟨265292, by rfl⟩ : syracuseStep 353723 = 530585) B530585
theorem B353783 : Blo 235815 353783 := bstep (se 1 (by rfl) ⟨265337, by rfl⟩ : syracuseStep 353783 = 530675) B530675
theorem B353807 : Blo 235815 353807 := bstep (se 1 (by rfl) ⟨265355, by rfl⟩ : syracuseStep 353807 = 530711) B530711
theorem B353849 : Blo 235815 353849 := bstep (se 2 (by rfl) ⟨132693, by rfl⟩ : syracuseStep 353849 = 265387) B265387
theorem B452155 : Blo 235815 452155 := bstep (se 1 (by rfl) ⟨339116, by rfl⟩ : syracuseStep 452155 = 678233) B678233
theorem B353927 : Blo 235815 353927 := bstep (se 1 (by rfl) ⟨265445, by rfl⟩ : syracuseStep 353927 = 530891) B530891
theorem B353963 : Blo 235815 353963 := bstep (se 1 (by rfl) ⟨265472, by rfl⟩ : syracuseStep 353963 = 530945) B530945
theorem B353993 : Blo 235815 353993 := bstep (se 2 (by rfl) ⟨132747, by rfl⟩ : syracuseStep 353993 = 265495) B265495
theorem B1828645 : Blo 235815 1828645 := bstep (se 4 (by rfl) ⟨171435, by rfl⟩ : syracuseStep 1828645 = 342871) B342871
theorem B354107 : Blo 235815 354107 := bstep (se 1 (by rfl) ⟨265580, by rfl⟩ : syracuseStep 354107 = 531161) B531161
theorem B354167 : Blo 235815 354167 := bstep (se 1 (by rfl) ⟨265625, by rfl⟩ : syracuseStep 354167 = 531251) B531251
theorem B354191 : Blo 235815 354191 := bstep (se 1 (by rfl) ⟨265643, by rfl⟩ : syracuseStep 354191 = 531287) B531287
theorem B354233 : Blo 235815 354233 := bstep (se 2 (by rfl) ⟨132837, by rfl⟩ : syracuseStep 354233 = 265675) B265675
theorem B354311 : Blo 235815 354311 := bstep (se 1 (by rfl) ⟨265733, by rfl⟩ : syracuseStep 354311 = 531467) B531467
theorem B452641 : Blo 235815 452641 := bstep (se 2 (by rfl) ⟨169740, by rfl⟩ : syracuseStep 452641 = 339481) B339481
theorem B354347 : Blo 235815 354347 := bstep (se 1 (by rfl) ⟨265760, by rfl⟩ : syracuseStep 354347 = 531521) B531521
theorem B354377 : Blo 235815 354377 := bstep (se 2 (by rfl) ⟨132891, by rfl⟩ : syracuseStep 354377 = 265783) B265783
theorem B354491 : Blo 235815 354491 := bstep (se 1 (by rfl) ⟨265868, by rfl⟩ : syracuseStep 354491 = 531737) B531737
theorem B354551 : Blo 235815 354551 := bstep (se 1 (by rfl) ⟨265913, by rfl⟩ : syracuseStep 354551 = 531827) B531827
theorem B354575 : Blo 235815 354575 := bstep (se 1 (by rfl) ⟨265931, by rfl⟩ : syracuseStep 354575 = 531863) B531863
theorem B354617 : Blo 235815 354617 := bstep (se 2 (by rfl) ⟨132981, by rfl⟩ : syracuseStep 354617 = 265963) B265963
theorem B354695 : Blo 235815 354695 := bstep (se 1 (by rfl) ⟨266021, by rfl⟩ : syracuseStep 354695 = 532043) B532043
theorem B354731 : Blo 235815 354731 := bstep (se 1 (by rfl) ⟨266048, by rfl⟩ : syracuseStep 354731 = 532097) B532097
theorem B354761 : Blo 235815 354761 := bstep (se 2 (by rfl) ⟨133035, by rfl⟩ : syracuseStep 354761 = 266071) B266071
theorem B1206737 : Blo 235815 1206737 := bstep (se 2 (by rfl) ⟨452526, by rfl⟩ : syracuseStep 1206737 = 905053) B905053
theorem B3434993 : Blo 235815 3434993 := bstep (se 2 (by rfl) ⟨1288122, by rfl⟩ : syracuseStep 3434993 = 2576245) B2576245
theorem B354875 : Blo 235815 354875 := bstep (se 1 (by rfl) ⟨266156, by rfl⟩ : syracuseStep 354875 = 532313) B532313
theorem B1075799 : Blo 235815 1075799 := bstep (se 1 (by rfl) ⟨806849, by rfl⟩ : syracuseStep 1075799 = 1613699) B1613699
theorem B354935 : Blo 235815 354935 := bstep (se 1 (by rfl) ⟨266201, by rfl⟩ : syracuseStep 354935 = 532403) B532403
theorem B354959 : Blo 235815 354959 := bstep (se 1 (by rfl) ⟨266219, by rfl⟩ : syracuseStep 354959 = 532439) B532439
theorem B355001 : Blo 235815 355001 := bstep (se 2 (by rfl) ⟨133125, by rfl⟩ : syracuseStep 355001 = 266251) B266251
theorem B355079 : Blo 235815 355079 := bstep (se 1 (by rfl) ⟨266309, by rfl⟩ : syracuseStep 355079 = 532619) B532619
theorem B2026255 : Blo 235815 2026255 := bstep (se 1 (by rfl) ⟨1519691, by rfl⟩ : syracuseStep 2026255 = 3039383) B3039383
theorem B355115 : Blo 235815 355115 := bstep (se 1 (by rfl) ⟨266336, by rfl⟩ : syracuseStep 355115 = 532673) B532673
theorem B1436467 : Blo 235815 1436467 := bstep (se 1 (by rfl) ⟨1077350, by rfl⟩ : syracuseStep 1436467 = 2154701) B2154701
theorem B355145 : Blo 235815 355145 := bstep (se 2 (by rfl) ⟨133179, by rfl⟩ : syracuseStep 355145 = 266359) B266359
theorem B355259 : Blo 235815 355259 := bstep (se 1 (by rfl) ⟨266444, by rfl⟩ : syracuseStep 355259 = 532889) B532889
theorem B355319 : Blo 235815 355319 := bstep (se 1 (by rfl) ⟨266489, by rfl⟩ : syracuseStep 355319 = 532979) B532979
theorem B355343 : Blo 235815 355343 := bstep (se 1 (by rfl) ⟨266507, by rfl⟩ : syracuseStep 355343 = 533015) B533015
theorem B355385 : Blo 235815 355385 := bstep (se 2 (by rfl) ⟨133269, by rfl⟩ : syracuseStep 355385 = 266539) B266539
theorem B1141847 : Blo 235815 1141847 := bstep (se 1 (by rfl) ⟨856385, by rfl⟩ : syracuseStep 1141847 = 1712771) B1712771
theorem B355463 : Blo 235815 355463 := bstep (se 1 (by rfl) ⟨266597, by rfl⟩ : syracuseStep 355463 = 533195) B533195
theorem B355499 : Blo 235815 355499 := bstep (se 1 (by rfl) ⟨266624, by rfl⟩ : syracuseStep 355499 = 533249) B533249
theorem B355529 : Blo 235815 355529 := bstep (se 2 (by rfl) ⟨133323, by rfl⟩ : syracuseStep 355529 = 266647) B266647
theorem B453833 : Blo 235815 453833 := bstep (se 2 (by rfl) ⟨170187, by rfl⟩ : syracuseStep 453833 = 340375) B340375
theorem B683275 : Blo 235815 683275 := bstep (se 1 (by rfl) ⟨512456, by rfl⟩ : syracuseStep 683275 = 1024913) B1024913
theorem B355643 : Blo 235815 355643 := bstep (se 1 (by rfl) ⟨266732, by rfl⟩ : syracuseStep 355643 = 533465) B533465
theorem B355703 : Blo 235815 355703 := bstep (se 1 (by rfl) ⟨266777, by rfl⟩ : syracuseStep 355703 = 533555) B533555
theorem B355727 : Blo 235815 355727 := bstep (se 1 (by rfl) ⟨266795, by rfl⟩ : syracuseStep 355727 = 533591) B533591
theorem B355769 : Blo 235815 355769 := bstep (se 2 (by rfl) ⟨133413, by rfl⟩ : syracuseStep 355769 = 266827) B266827
theorem B1535441 : Blo 235815 1535441 := bstep (se 2 (by rfl) ⟨575790, by rfl⟩ : syracuseStep 1535441 = 1151581) B1151581
theorem B355847 : Blo 235815 355847 := bstep (se 1 (by rfl) ⟨266885, by rfl⟩ : syracuseStep 355847 = 533771) B533771
theorem B355883 : Blo 235815 355883 := bstep (se 1 (by rfl) ⟨266912, by rfl⟩ : syracuseStep 355883 = 533825) B533825
theorem B355913 : Blo 235815 355913 := bstep (se 2 (by rfl) ⟨133467, by rfl⟩ : syracuseStep 355913 = 266935) B266935
theorem B58453589 : Blo 235815 58453589 := bstep (se 8 (by rfl) ⟨342501, by rfl⟩ : syracuseStep 58453589 = 685003) B685003
theorem B356027 : Blo 235815 356027 := bstep (se 1 (by rfl) ⟨267020, by rfl⟩ : syracuseStep 356027 = 534041) B534041
theorem B356087 : Blo 235815 356087 := bstep (se 1 (by rfl) ⟨267065, by rfl⟩ : syracuseStep 356087 = 534131) B534131
theorem B356111 : Blo 235815 356111 := bstep (se 1 (by rfl) ⟨267083, by rfl⟩ : syracuseStep 356111 = 534167) B534167
theorem B618283 : Blo 235815 618283 := bstep (se 1 (by rfl) ⟨463712, by rfl⟩ : syracuseStep 618283 = 927425) B927425
theorem B356153 : Blo 235815 356153 := bstep (se 2 (by rfl) ⟨133557, by rfl⟩ : syracuseStep 356153 = 267115) B267115
theorem B356231 : Blo 235815 356231 := bstep (se 1 (by rfl) ⟨267173, by rfl⟩ : syracuseStep 356231 = 534347) B534347
theorem B454547 : Blo 235815 454547 := bstep (se 1 (by rfl) ⟨340910, by rfl⟩ : syracuseStep 454547 = 681821) B681821
theorem B356267 : Blo 235815 356267 := bstep (se 1 (by rfl) ⟨267200, by rfl⟩ : syracuseStep 356267 = 534401) B534401
theorem B454585 : Blo 235815 454585 := bstep (se 2 (by rfl) ⟨170469, by rfl⟩ : syracuseStep 454585 = 340939) B340939
theorem B356297 : Blo 235815 356297 := bstep (se 2 (by rfl) ⟨133611, by rfl⟩ : syracuseStep 356297 = 267223) B267223
theorem B356411 : Blo 235815 356411 := bstep (se 1 (by rfl) ⟨267308, by rfl⟩ : syracuseStep 356411 = 534617) B534617
theorem B356471 : Blo 235815 356471 := bstep (se 1 (by rfl) ⟨267353, by rfl⟩ : syracuseStep 356471 = 534707) B534707
theorem B356495 : Blo 235815 356495 := bstep (se 1 (by rfl) ⟨267371, by rfl⟩ : syracuseStep 356495 = 534743) B534743
theorem B356537 : Blo 235815 356537 := bstep (se 2 (by rfl) ⟨133701, by rfl⟩ : syracuseStep 356537 = 267403) B267403
theorem B2355437 : Blo 235815 2355437 := bstep (se 3 (by rfl) ⟨441644, by rfl⟩ : syracuseStep 2355437 = 883289) B883289
theorem B356615 : Blo 235815 356615 := bstep (se 1 (by rfl) ⟨267461, by rfl⟩ : syracuseStep 356615 = 534923) B534923
theorem B913697 : Blo 235815 913697 := bstep (se 2 (by rfl) ⟨342636, by rfl⟩ : syracuseStep 913697 = 685273) B685273
theorem B356651 : Blo 235815 356651 := bstep (se 1 (by rfl) ⟨267488, by rfl⟩ : syracuseStep 356651 = 534977) B534977
theorem B356681 : Blo 235815 356681 := bstep (se 2 (by rfl) ⟨133755, by rfl⟩ : syracuseStep 356681 = 267511) B267511
theorem B1143193 : Blo 235815 1143193 := bstep (se 2 (by rfl) ⟨428697, by rfl⟩ : syracuseStep 1143193 = 857395) B857395
theorem B356795 : Blo 235815 356795 := bstep (se 1 (by rfl) ⟨267596, by rfl⟩ : syracuseStep 356795 = 535193) B535193
theorem B356855 : Blo 235815 356855 := bstep (se 1 (by rfl) ⟨267641, by rfl⟩ : syracuseStep 356855 = 535283) B535283
theorem B1208843 : Blo 235815 1208843 := bstep (se 1 (by rfl) ⟨906632, by rfl⟩ : syracuseStep 1208843 = 1813265) B1813265
theorem B356879 : Blo 235815 356879 := bstep (se 1 (by rfl) ⟨267659, by rfl⟩ : syracuseStep 356879 = 535319) B535319
theorem B1798685 : Blo 235815 1798685 := bstep (se 3 (by rfl) ⟨337253, by rfl⟩ : syracuseStep 1798685 = 674507) B674507
theorem B356921 : Blo 235815 356921 := bstep (se 2 (by rfl) ⟨133845, by rfl⟩ : syracuseStep 356921 = 267691) B267691
theorem B356999 : Blo 235815 356999 := bstep (se 1 (by rfl) ⟨267749, by rfl⟩ : syracuseStep 356999 = 535499) B535499
theorem B357035 : Blo 235815 357035 := bstep (se 1 (by rfl) ⟨267776, by rfl⟩ : syracuseStep 357035 = 535553) B535553
theorem B1209005 : Blo 235815 1209005 := bstep (se 3 (by rfl) ⟨226688, by rfl⟩ : syracuseStep 1209005 = 453377) B453377
theorem B357065 : Blo 235815 357065 := bstep (se 2 (by rfl) ⟨133899, by rfl⟩ : syracuseStep 357065 = 267799) B267799
theorem B1012513 : Blo 235815 1012513 := bstep (se 2 (by rfl) ⟨379692, by rfl⟩ : syracuseStep 1012513 = 759385) B759385
theorem B357179 : Blo 235815 357179 := bstep (se 1 (by rfl) ⟨267884, by rfl⟩ : syracuseStep 357179 = 535769) B535769
theorem B652151 : Blo 235815 652151 := bstep (se 1 (by rfl) ⟨489113, by rfl⟩ : syracuseStep 652151 = 978227) B978227
theorem B357239 : Blo 235815 357239 := bstep (se 1 (by rfl) ⟨267929, by rfl⟩ : syracuseStep 357239 = 535859) B535859
theorem B357263 : Blo 235815 357263 := bstep (se 1 (by rfl) ⟨267947, by rfl⟩ : syracuseStep 357263 = 535895) B535895
theorem B357305 : Blo 235815 357305 := bstep (se 2 (by rfl) ⟨133989, by rfl⟩ : syracuseStep 357305 = 267979) B267979
theorem B357383 : Blo 235815 357383 := bstep (se 1 (by rfl) ⟨268037, by rfl⟩ : syracuseStep 357383 = 536075) B536075
theorem B357419 : Blo 235815 357419 := bstep (se 1 (by rfl) ⟨268064, by rfl⟩ : syracuseStep 357419 = 536129) B536129
theorem B357449 : Blo 235815 357449 := bstep (se 2 (by rfl) ⟨134043, by rfl⟩ : syracuseStep 357449 = 268087) B268087
theorem B357563 : Blo 235815 357563 := bstep (se 1 (by rfl) ⟨268172, by rfl⟩ : syracuseStep 357563 = 536345) B536345
theorem B357623 : Blo 235815 357623 := bstep (se 1 (by rfl) ⟨268217, by rfl⟩ : syracuseStep 357623 = 536435) B536435
theorem B357647 : Blo 235815 357647 := bstep (se 1 (by rfl) ⟨268235, by rfl⟩ : syracuseStep 357647 = 536471) B536471
theorem B357689 : Blo 235815 357689 := bstep (se 2 (by rfl) ⟨134133, by rfl⟩ : syracuseStep 357689 = 268267) B268267
theorem B357767 : Blo 235815 357767 := bstep (se 1 (by rfl) ⟨268325, by rfl⟩ : syracuseStep 357767 = 536651) B536651
theorem B259471 : Blo 235815 259471 := bstep (se 1 (by rfl) ⟨194603, by rfl⟩ : syracuseStep 259471 = 389207) B389207
theorem B357803 : Blo 235815 357803 := bstep (se 1 (by rfl) ⟨268352, by rfl⟩ : syracuseStep 357803 = 536705) B536705
theorem B357833 : Blo 235815 357833 := bstep (se 2 (by rfl) ⟨134187, by rfl⟩ : syracuseStep 357833 = 268375) B268375
theorem B357947 : Blo 235815 357947 := bstep (se 1 (by rfl) ⟨268460, by rfl⟩ : syracuseStep 357947 = 536921) B536921
theorem B358007 : Blo 235815 358007 := bstep (se 1 (by rfl) ⟨268505, by rfl⟩ : syracuseStep 358007 = 537011) B537011
theorem B358031 : Blo 235815 358031 := bstep (se 1 (by rfl) ⟨268523, by rfl⟩ : syracuseStep 358031 = 537047) B537047
theorem B358073 : Blo 235815 358073 := bstep (se 2 (by rfl) ⟨134277, by rfl⟩ : syracuseStep 358073 = 268555) B268555
theorem B587521 : Blo 235815 587521 := bstep (se 2 (by rfl) ⟨220320, by rfl⟩ : syracuseStep 587521 = 440641) B440641
theorem B358151 : Blo 235815 358151 := bstep (se 1 (by rfl) ⟨268613, by rfl⟩ : syracuseStep 358151 = 537227) B537227
theorem B718625 : Blo 235815 718625 := bstep (se 2 (by rfl) ⟨269484, by rfl⟩ : syracuseStep 718625 = 538969) B538969
theorem B358187 : Blo 235815 358187 := bstep (se 1 (by rfl) ⟨268640, by rfl⟩ : syracuseStep 358187 = 537281) B537281
theorem B358217 : Blo 235815 358217 := bstep (se 2 (by rfl) ⟨134331, by rfl⟩ : syracuseStep 358217 = 268663) B268663
theorem B1439603 : Blo 235815 1439603 := bstep (se 1 (by rfl) ⟨1079702, by rfl⟩ : syracuseStep 1439603 = 2159405) B2159405
theorem B358331 : Blo 235815 358331 := bstep (se 1 (by rfl) ⟨268748, by rfl⟩ : syracuseStep 358331 = 537497) B537497
theorem B358391 : Blo 235815 358391 := bstep (se 1 (by rfl) ⟨268793, by rfl⟩ : syracuseStep 358391 = 537587) B537587
theorem B358415 : Blo 235815 358415 := bstep (se 1 (by rfl) ⟨268811, by rfl⟩ : syracuseStep 358415 = 537623) B537623
theorem B358457 : Blo 235815 358457 := bstep (se 2 (by rfl) ⟨134421, by rfl⟩ : syracuseStep 358457 = 268843) B268843
theorem B358535 : Blo 235815 358535 := bstep (se 1 (by rfl) ⟨268901, by rfl⟩ : syracuseStep 358535 = 537803) B537803
theorem B358571 : Blo 235815 358571 := bstep (se 1 (by rfl) ⟨268928, by rfl⟩ : syracuseStep 358571 = 537857) B537857
theorem B358601 : Blo 235815 358601 := bstep (se 2 (by rfl) ⟨134475, by rfl⟩ : syracuseStep 358601 = 268951) B268951
theorem B1210625 : Blo 235815 1210625 := bstep (se 2 (by rfl) ⟨453984, by rfl⟩ : syracuseStep 1210625 = 907969) B907969
theorem B358715 : Blo 235815 358715 := bstep (se 1 (by rfl) ⟨269036, by rfl⟩ : syracuseStep 358715 = 538073) B538073
theorem B1440089 : Blo 235815 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B719219 : Blo 235815 719219 := bstep (se 1 (by rfl) ⟨539414, by rfl⟩ : syracuseStep 719219 = 1078829) B1078829
theorem B358775 : Blo 235815 358775 := bstep (se 1 (by rfl) ⟨269081, by rfl⟩ : syracuseStep 358775 = 538163) B538163
theorem B358799 : Blo 235815 358799 := bstep (se 1 (by rfl) ⟨269099, by rfl⟩ : syracuseStep 358799 = 538199) B538199
theorem B1440185 : Blo 235815 1440185 := bstep (se 2 (by rfl) ⟨540069, by rfl⟩ : syracuseStep 1440185 = 1080139) B1080139
theorem B358841 : Blo 235815 358841 := bstep (se 2 (by rfl) ⟨134565, by rfl⟩ : syracuseStep 358841 = 269131) B269131
theorem B358919 : Blo 235815 358919 := bstep (se 1 (by rfl) ⟨269189, by rfl⟩ : syracuseStep 358919 = 538379) B538379
theorem B358955 : Blo 235815 358955 := bstep (se 1 (by rfl) ⟨269216, by rfl⟩ : syracuseStep 358955 = 538433) B538433
theorem B358985 : Blo 235815 358985 := bstep (se 2 (by rfl) ⟨134619, by rfl⟩ : syracuseStep 358985 = 269239) B269239
theorem B719513 : Blo 235815 719513 := bstep (se 2 (by rfl) ⟨269817, by rfl⟩ : syracuseStep 719513 = 539635) B539635
theorem B359099 : Blo 235815 359099 := bstep (se 1 (by rfl) ⟨269324, by rfl⟩ : syracuseStep 359099 = 538649) B538649
theorem B359159 : Blo 235815 359159 := bstep (se 1 (by rfl) ⟨269369, by rfl⟩ : syracuseStep 359159 = 538739) B538739
theorem B359183 : Blo 235815 359183 := bstep (se 1 (by rfl) ⟨269387, by rfl⟩ : syracuseStep 359183 = 538775) B538775
theorem B359225 : Blo 235815 359225 := bstep (se 2 (by rfl) ⟨134709, by rfl⟩ : syracuseStep 359225 = 269419) B269419
theorem B7863155 : Blo 235815 7863155 := bstep (se 1 (by rfl) ⟨5897366, by rfl⟩ : syracuseStep 7863155 = 11794733) B11794733
theorem B359303 : Blo 235815 359303 := bstep (se 1 (by rfl) ⟨269477, by rfl⟩ : syracuseStep 359303 = 538955) B538955
theorem B359339 : Blo 235815 359339 := bstep (se 1 (by rfl) ⟨269504, by rfl⟩ : syracuseStep 359339 = 539009) B539009
theorem B359369 : Blo 235815 359369 := bstep (se 2 (by rfl) ⟨134763, by rfl⟩ : syracuseStep 359369 = 269527) B269527
theorem B1211435 : Blo 235815 1211435 := bstep (se 1 (by rfl) ⟨908576, by rfl⟩ : syracuseStep 1211435 = 1817153) B1817153
theorem B359483 : Blo 235815 359483 := bstep (se 1 (by rfl) ⟨269612, by rfl⟩ : syracuseStep 359483 = 539225) B539225
theorem B359543 : Blo 235815 359543 := bstep (se 1 (by rfl) ⟨269657, by rfl⟩ : syracuseStep 359543 = 539315) B539315
theorem B359567 : Blo 235815 359567 := bstep (se 1 (by rfl) ⟨269675, by rfl⟩ : syracuseStep 359567 = 539351) B539351
theorem B359609 : Blo 235815 359609 := bstep (se 2 (by rfl) ⟨134853, by rfl⟩ : syracuseStep 359609 = 269707) B269707
theorem B359687 : Blo 235815 359687 := bstep (se 1 (by rfl) ⟨269765, by rfl⟩ : syracuseStep 359687 = 539531) B539531
theorem B359723 : Blo 235815 359723 := bstep (se 1 (by rfl) ⟨269792, by rfl⟩ : syracuseStep 359723 = 539585) B539585
theorem B360121 : Blo 235815 360121 := bstep (se 2 (by rfl) ⟨135045, by rfl⟩ : syracuseStep 360121 = 270091) B270091
theorem B917561 : Blo 235815 917561 := bstep (se 2 (by rfl) ⟨344085, by rfl⟩ : syracuseStep 917561 = 688171) B688171
theorem B23298293 : Blo 235815 23298293 := bstep (se 5 (by rfl) ⟨1092107, by rfl⟩ : syracuseStep 23298293 = 2184215) B2184215
theorem B6127973 : Blo 235815 6127973 := bstep (se 4 (by rfl) ⟨574497, by rfl⟩ : syracuseStep 6127973 = 1148995) B1148995
theorem B721505 : Blo 235815 721505 := bstep (se 2 (by rfl) ⟨270564, by rfl⟩ : syracuseStep 721505 = 541129) B541129
theorem B14615153 : Blo 235815 14615153 := bstep (se 2 (by rfl) ⟨5480682, by rfl⟩ : syracuseStep 14615153 = 10961365) B10961365
theorem B1344185 : Blo 235815 1344185 := bstep (se 2 (by rfl) ⟨504069, by rfl⟩ : syracuseStep 1344185 = 1008139) B1008139
theorem B721847 : Blo 235815 721847 := bstep (se 1 (by rfl) ⟨541385, by rfl⟩ : syracuseStep 721847 = 1082771) B1082771
theorem B427529 : Blo 235815 427529 := bstep (se 2 (by rfl) ⟨160323, by rfl⟩ : syracuseStep 427529 = 320647) B320647
theorem B1213991 : Blo 235815 1213991 := bstep (se 1 (by rfl) ⟨910493, by rfl⟩ : syracuseStep 1213991 = 1820987) B1820987
theorem B1640353 : Blo 235815 1640353 := bstep (se 2 (by rfl) ⟨615132, by rfl⟩ : syracuseStep 1640353 = 1230265) B1230265
theorem B1804517 : Blo 235815 1804517 := bstep (se 4 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 1804517 = 338347) B338347
theorem B428755 : Blo 235815 428755 := bstep (se 1 (by rfl) ⟨321566, by rfl⟩ : syracuseStep 428755 = 643133) B643133
theorem B757079 : Blo 235815 757079 := bstep (se 1 (by rfl) ⟨567809, by rfl⟩ : syracuseStep 757079 = 1135619) B1135619
theorem B265567 : Blo 235815 265567 := bstep (se 1 (by rfl) ⟨199175, by rfl⟩ : syracuseStep 265567 = 398351) B398351
theorem B1019279 : Blo 235815 1019279 := bstep (se 1 (by rfl) ⟨764459, by rfl⟩ : syracuseStep 1019279 = 1528919) B1528919
theorem B265927 : Blo 235815 265927 := bstep (se 1 (by rfl) ⟨199445, by rfl⟩ : syracuseStep 265927 = 398891) B398891
theorem B429779 : Blo 235815 429779 := bstep (se 1 (by rfl) ⟨322334, by rfl⟩ : syracuseStep 429779 = 644669) B644669
theorem B2101277 : Blo 235815 2101277 := bstep (se 3 (by rfl) ⟨393989, by rfl⟩ : syracuseStep 2101277 = 787979) B787979
theorem B299047 : Blo 235815 299047 := bstep (se 1 (by rfl) ⟨224285, by rfl⟩ : syracuseStep 299047 = 448571) B448571
theorem B3281075 : Blo 235815 3281075 := bstep (se 1 (by rfl) ⟨2460806, by rfl⟩ : syracuseStep 3281075 = 4921613) B4921613
theorem B1020221 : Blo 235815 1020221 := bstep (se 3 (by rfl) ⟨191291, by rfl⟩ : syracuseStep 1020221 = 382583) B382583
theorem B299371 : Blo 235815 299371 := bstep (se 1 (by rfl) ⟨224528, by rfl⟩ : syracuseStep 299371 = 449057) B449057
theorem B758297 : Blo 235815 758297 := bstep (se 2 (by rfl) ⟨284361, by rfl⟩ : syracuseStep 758297 = 568723) B568723
theorem B266791 : Blo 235815 266791 := bstep (se 1 (by rfl) ⟨200093, by rfl⟩ : syracuseStep 266791 = 400187) B400187
theorem B725543 : Blo 235815 725543 := bstep (se 1 (by rfl) ⟨544157, by rfl⟩ : syracuseStep 725543 = 1088315) B1088315
theorem B856673 : Blo 235815 856673 := bstep (se 2 (by rfl) ⟨321252, by rfl⟩ : syracuseStep 856673 = 642505) B642505
theorem B758411 : Blo 235815 758411 := bstep (se 1 (by rfl) ⟨568808, by rfl⟩ : syracuseStep 758411 = 1137617) B1137617
theorem B3248849 : Blo 235815 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B922487 : Blo 235815 922487 := bstep (se 1 (by rfl) ⟨691865, by rfl⟩ : syracuseStep 922487 = 1383731) B1383731
theorem B398263 : Blo 235815 398263 := bstep (se 1 (by rfl) ⟨298697, by rfl⟩ : syracuseStep 398263 = 597395) B597395
theorem B398459 : Blo 235815 398459 := bstep (se 1 (by rfl) ⟨298844, by rfl⟩ : syracuseStep 398459 = 597689) B597689
theorem B2954393 : Blo 235815 2954393 := bstep (se 2 (by rfl) ⟨1107897, by rfl⟩ : syracuseStep 2954393 = 2215795) B2215795
theorem B1348811 : Blo 235815 1348811 := bstep (se 1 (by rfl) ⟨1011608, by rfl⟩ : syracuseStep 1348811 = 2023217) B2023217
theorem B8295695 : Blo 235815 8295695 := bstep (se 1 (by rfl) ⟨6221771, by rfl⟩ : syracuseStep 8295695 = 12443543) B12443543
theorem B398857 : Blo 235815 398857 := bstep (se 2 (by rfl) ⟨149571, by rfl⟩ : syracuseStep 398857 = 299143) B299143
theorem B1349243 : Blo 235815 1349243 := bstep (se 1 (by rfl) ⟨1011932, by rfl⟩ : syracuseStep 1349243 = 2023865) B2023865
theorem B300667 : Blo 235815 300667 := bstep (se 1 (by rfl) ⟨225500, by rfl⟩ : syracuseStep 300667 = 451001) B451001
theorem B399019 : Blo 235815 399019 := bstep (se 1 (by rfl) ⟨299264, by rfl⟩ : syracuseStep 399019 = 598529) B598529
theorem B399323 : Blo 235815 399323 := bstep (se 1 (by rfl) ⟨299492, by rfl⟩ : syracuseStep 399323 = 598985) B598985
theorem B1021967 : Blo 235815 1021967 := bstep (se 1 (by rfl) ⟨766475, by rfl⟩ : syracuseStep 1021967 = 1532951) B1532951
theorem B268411 : Blo 235815 268411 := bstep (se 1 (by rfl) ⟨201308, by rfl⟩ : syracuseStep 268411 = 402617) B402617
theorem B530603 : Blo 235815 530603 := bstep (se 1 (by rfl) ⟨397952, by rfl⟩ : syracuseStep 530603 = 795905) B795905
theorem B399559 : Blo 235815 399559 := bstep (se 1 (by rfl) ⟨299669, by rfl⟩ : syracuseStep 399559 = 599339) B599339
theorem B1022219 : Blo 235815 1022219 := bstep (se 1 (by rfl) ⟨766664, by rfl⟩ : syracuseStep 1022219 = 1533329) B1533329
theorem B235815 : Blo 235815 235815 := bstep (se 1 (by rfl) ⟨176861, by rfl⟩ : syracuseStep 235815 = 353723) B353723
theorem B235855 : Blo 235815 235855 := bstep (se 1 (by rfl) ⟨176891, by rfl⟩ : syracuseStep 235855 = 353783) B353783
theorem B235871 : Blo 235815 235871 := bstep (se 1 (by rfl) ⟨176903, by rfl⟩ : syracuseStep 235871 = 353807) B353807
theorem B399721 : Blo 235815 399721 := bstep (se 2 (by rfl) ⟨149895, by rfl⟩ : syracuseStep 399721 = 299791) B299791
theorem B235899 : Blo 235815 235899 := bstep (se 1 (by rfl) ⟨176924, by rfl⟩ : syracuseStep 235899 = 353849) B353849
theorem B1350017 : Blo 235815 1350017 := bstep (se 2 (by rfl) ⟨506256, by rfl⟩ : syracuseStep 1350017 = 1012513) B1012513
theorem B235951 : Blo 235815 235951 := bstep (se 1 (by rfl) ⟨176963, by rfl⟩ : syracuseStep 235951 = 353927) B353927
theorem B235975 : Blo 235815 235975 := bstep (se 1 (by rfl) ⟨176981, by rfl⟩ : syracuseStep 235975 = 353963) B353963
theorem B235995 : Blo 235815 235995 := bstep (se 1 (by rfl) ⟨176996, by rfl⟩ : syracuseStep 235995 = 353993) B353993
theorem B3840493 : Blo 235815 3840493 := bstep (se 3 (by rfl) ⟨720092, by rfl⟩ : syracuseStep 3840493 = 1440185) B1440185
theorem B236071 : Blo 235815 236071 := bstep (se 1 (by rfl) ⟨177053, by rfl⟩ : syracuseStep 236071 = 354107) B354107
theorem B236111 : Blo 235815 236111 := bstep (se 1 (by rfl) ⟨177083, by rfl⟩ : syracuseStep 236111 = 354167) B354167
theorem B268879 : Blo 235815 268879 := bstep (se 1 (by rfl) ⟨201659, by rfl⟩ : syracuseStep 268879 = 403319) B403319
theorem B236127 : Blo 235815 236127 := bstep (se 1 (by rfl) ⟨177095, by rfl⟩ : syracuseStep 236127 = 354191) B354191
theorem B236155 : Blo 235815 236155 := bstep (se 1 (by rfl) ⟨177116, by rfl⟩ : syracuseStep 236155 = 354233) B354233
theorem B236207 : Blo 235815 236207 := bstep (se 1 (by rfl) ⟨177155, by rfl⟩ : syracuseStep 236207 = 354311) B354311
theorem B531143 : Blo 235815 531143 := bstep (se 1 (by rfl) ⟨398357, by rfl⟩ : syracuseStep 531143 = 796715) B796715
theorem B236231 : Blo 235815 236231 := bstep (se 1 (by rfl) ⟨177173, by rfl⟩ : syracuseStep 236231 = 354347) B354347
theorem B1284817 : Blo 235815 1284817 := bstep (se 2 (by rfl) ⟨481806, by rfl⟩ : syracuseStep 1284817 = 963613) B963613
theorem B236251 : Blo 235815 236251 := bstep (se 1 (by rfl) ⟨177188, by rfl⟩ : syracuseStep 236251 = 354377) B354377
theorem B236327 : Blo 235815 236327 := bstep (se 1 (by rfl) ⟨177245, by rfl⟩ : syracuseStep 236327 = 354491) B354491
theorem B236367 : Blo 235815 236367 := bstep (se 1 (by rfl) ⟨177275, by rfl⟩ : syracuseStep 236367 = 354551) B354551
theorem B236383 : Blo 235815 236383 := bstep (se 1 (by rfl) ⟨177287, by rfl⟩ : syracuseStep 236383 = 354575) B354575
theorem B236411 : Blo 235815 236411 := bstep (se 1 (by rfl) ⟨177308, by rfl⟩ : syracuseStep 236411 = 354617) B354617
theorem B236463 : Blo 235815 236463 := bstep (se 1 (by rfl) ⟨177347, by rfl⟩ : syracuseStep 236463 = 354695) B354695
theorem B400315 : Blo 235815 400315 := bstep (se 1 (by rfl) ⟨300236, by rfl⟩ : syracuseStep 400315 = 600473) B600473
theorem B236487 : Blo 235815 236487 := bstep (se 1 (by rfl) ⟨177365, by rfl⟩ : syracuseStep 236487 = 354731) B354731
theorem B236507 : Blo 235815 236507 := bstep (se 1 (by rfl) ⟨177380, by rfl⟩ : syracuseStep 236507 = 354761) B354761
theorem B269275 : Blo 235815 269275 := bstep (se 1 (by rfl) ⟨201956, by rfl⟩ : syracuseStep 269275 = 403913) B403913
theorem B236583 : Blo 235815 236583 := bstep (se 1 (by rfl) ⟨177437, by rfl⟩ : syracuseStep 236583 = 354875) B354875
theorem B400423 : Blo 235815 400423 := bstep (se 1 (by rfl) ⟨300317, by rfl⟩ : syracuseStep 400423 = 600635) B600635
theorem B597071 : Blo 235815 597071 := bstep (se 1 (by rfl) ⟨447803, by rfl⟩ : syracuseStep 597071 = 895607) B895607
theorem B236623 : Blo 235815 236623 := bstep (se 1 (by rfl) ⟨177467, by rfl⟩ : syracuseStep 236623 = 354935) B354935
theorem B236639 : Blo 235815 236639 := bstep (se 1 (by rfl) ⟨177479, by rfl⟩ : syracuseStep 236639 = 354959) B354959
theorem B236667 : Blo 235815 236667 := bstep (se 1 (by rfl) ⟨177500, by rfl⟩ : syracuseStep 236667 = 355001) B355001
theorem B236719 : Blo 235815 236719 := bstep (se 1 (by rfl) ⟨177539, by rfl⟩ : syracuseStep 236719 = 355079) B355079
theorem B236743 : Blo 235815 236743 := bstep (se 1 (by rfl) ⟨177557, by rfl⟩ : syracuseStep 236743 = 355115) B355115
theorem B236763 : Blo 235815 236763 := bstep (se 1 (by rfl) ⟨177572, by rfl⟩ : syracuseStep 236763 = 355145) B355145
theorem B236839 : Blo 235815 236839 := bstep (se 1 (by rfl) ⟨177629, by rfl⟩ : syracuseStep 236839 = 355259) B355259
theorem B236879 : Blo 235815 236879 := bstep (se 1 (by rfl) ⟨177659, by rfl⟩ : syracuseStep 236879 = 355319) B355319
theorem B236895 : Blo 235815 236895 := bstep (se 1 (by rfl) ⟨177671, by rfl⟩ : syracuseStep 236895 = 355343) B355343
theorem B400747 : Blo 235815 400747 := bstep (se 1 (by rfl) ⟨300560, by rfl⟩ : syracuseStep 400747 = 601121) B601121
theorem B236923 : Blo 235815 236923 := bstep (se 1 (by rfl) ⟨177692, by rfl⟩ : syracuseStep 236923 = 355385) B355385
theorem B761231 : Blo 235815 761231 := bstep (se 1 (by rfl) ⟨570923, by rfl⟩ : syracuseStep 761231 = 1141847) B1141847
theorem B236975 : Blo 235815 236975 := bstep (se 1 (by rfl) ⟨177731, by rfl⟩ : syracuseStep 236975 = 355463) B355463
theorem B269743 : Blo 235815 269743 := bstep (se 1 (by rfl) ⟨202307, by rfl⟩ : syracuseStep 269743 = 404615) B404615
theorem B236999 : Blo 235815 236999 := bstep (se 1 (by rfl) ⟨177749, by rfl⟩ : syracuseStep 236999 = 355499) B355499
theorem B237019 : Blo 235815 237019 := bstep (se 1 (by rfl) ⟨177764, by rfl⟩ : syracuseStep 237019 = 355529) B355529
theorem B302555 : Blo 235815 302555 := bstep (se 1 (by rfl) ⟨226916, by rfl⟩ : syracuseStep 302555 = 453833) B453833
theorem B532007 : Blo 235815 532007 := bstep (se 1 (by rfl) ⟨399005, by rfl⟩ : syracuseStep 532007 = 798011) B798011
theorem B237095 : Blo 235815 237095 := bstep (se 1 (by rfl) ⟨177821, by rfl⟩ : syracuseStep 237095 = 355643) B355643
theorem B237135 : Blo 235815 237135 := bstep (se 1 (by rfl) ⟨177851, by rfl⟩ : syracuseStep 237135 = 355703) B355703
theorem B237151 : Blo 235815 237151 := bstep (se 1 (by rfl) ⟨177863, by rfl⟩ : syracuseStep 237151 = 355727) B355727
theorem B237179 : Blo 235815 237179 := bstep (se 1 (by rfl) ⟨177884, by rfl⟩ : syracuseStep 237179 = 355769) B355769
theorem B237231 : Blo 235815 237231 := bstep (se 1 (by rfl) ⟨177923, by rfl⟩ : syracuseStep 237231 = 355847) B355847
theorem B237255 : Blo 235815 237255 := bstep (se 1 (by rfl) ⟨177941, by rfl⟩ : syracuseStep 237255 = 355883) B355883
theorem B597719 : Blo 235815 597719 := bstep (se 1 (by rfl) ⟨448289, by rfl⟩ : syracuseStep 597719 = 896579) B896579
theorem B237275 : Blo 235815 237275 := bstep (se 1 (by rfl) ⟨177956, by rfl⟩ : syracuseStep 237275 = 355913) B355913
theorem B38969059 : Blo 235815 38969059 := bstep (se 1 (by rfl) ⟨29226794, by rfl⟩ : syracuseStep 38969059 = 58453589) B58453589
theorem B237351 : Blo 235815 237351 := bstep (se 1 (by rfl) ⟨178013, by rfl⟩ : syracuseStep 237351 = 356027) B356027
theorem B1384235 : Blo 235815 1384235 := bstep (se 1 (by rfl) ⟨1038176, by rfl⟩ : syracuseStep 1384235 = 2076353) B2076353
theorem B237391 : Blo 235815 237391 := bstep (se 1 (by rfl) ⟨178043, by rfl⟩ : syracuseStep 237391 = 356087) B356087
theorem B237407 : Blo 235815 237407 := bstep (se 1 (by rfl) ⟨178055, by rfl⟩ : syracuseStep 237407 = 356111) B356111
theorem B532331 : Blo 235815 532331 := bstep (se 1 (by rfl) ⟨399248, by rfl⟩ : syracuseStep 532331 = 798497) B798497
theorem B237435 : Blo 235815 237435 := bstep (se 1 (by rfl) ⟨178076, by rfl⟩ : syracuseStep 237435 = 356153) B356153
theorem B532385 : Blo 235815 532385 := bstep (se 2 (by rfl) ⟨199644, by rfl⟩ : syracuseStep 532385 = 399289) B399289
theorem B237487 : Blo 235815 237487 := bstep (se 1 (by rfl) ⟨178115, by rfl⟩ : syracuseStep 237487 = 356231) B356231
theorem B303031 : Blo 235815 303031 := bstep (se 1 (by rfl) ⟨227273, by rfl⟩ : syracuseStep 303031 = 454547) B454547
theorem B237511 : Blo 235815 237511 := bstep (se 1 (by rfl) ⟨178133, by rfl⟩ : syracuseStep 237511 = 356267) B356267
theorem B237531 : Blo 235815 237531 := bstep (se 1 (by rfl) ⟨178148, by rfl⟩ : syracuseStep 237531 = 356297) B356297
theorem B237607 : Blo 235815 237607 := bstep (se 1 (by rfl) ⟨178205, by rfl⟩ : syracuseStep 237607 = 356411) B356411
theorem B237647 : Blo 235815 237647 := bstep (se 1 (by rfl) ⟨178235, by rfl⟩ : syracuseStep 237647 = 356471) B356471
theorem B237663 : Blo 235815 237663 := bstep (se 1 (by rfl) ⟨178247, by rfl⟩ : syracuseStep 237663 = 356495) B356495
theorem B237691 : Blo 235815 237691 := bstep (se 1 (by rfl) ⟨178268, by rfl⟩ : syracuseStep 237691 = 356537) B356537
theorem B237743 : Blo 235815 237743 := bstep (se 1 (by rfl) ⟨178307, by rfl⟩ : syracuseStep 237743 = 356615) B356615
theorem B237767 : Blo 235815 237767 := bstep (se 1 (by rfl) ⟨178325, by rfl⟩ : syracuseStep 237767 = 356651) B356651
theorem B237787 : Blo 235815 237787 := bstep (se 1 (by rfl) ⟨178340, by rfl⟩ : syracuseStep 237787 = 356681) B356681
theorem B532727 : Blo 235815 532727 := bstep (se 1 (by rfl) ⟨399545, by rfl⟩ : syracuseStep 532727 = 799091) B799091
theorem B237863 : Blo 235815 237863 := bstep (se 1 (by rfl) ⟨178397, by rfl⟩ : syracuseStep 237863 = 356795) B356795
theorem B237903 : Blo 235815 237903 := bstep (se 1 (by rfl) ⟨178427, by rfl⟩ : syracuseStep 237903 = 356855) B356855
theorem B237919 : Blo 235815 237919 := bstep (se 1 (by rfl) ⟨178439, by rfl⟩ : syracuseStep 237919 = 356879) B356879
theorem B237947 : Blo 235815 237947 := bstep (se 1 (by rfl) ⟨178460, by rfl⟩ : syracuseStep 237947 = 356921) B356921
theorem B401807 : Blo 235815 401807 := bstep (se 1 (by rfl) ⟨301355, by rfl⟩ : syracuseStep 401807 = 602711) B602711
theorem B237999 : Blo 235815 237999 := bstep (se 1 (by rfl) ⟨178499, by rfl⟩ : syracuseStep 237999 = 356999) B356999
theorem B238023 : Blo 235815 238023 := bstep (se 1 (by rfl) ⟨178517, by rfl⟩ : syracuseStep 238023 = 357035) B357035
theorem B238043 : Blo 235815 238043 := bstep (se 1 (by rfl) ⟨178532, by rfl⟩ : syracuseStep 238043 = 357065) B357065
theorem B238119 : Blo 235815 238119 := bstep (se 1 (by rfl) ⟨178589, by rfl⟩ : syracuseStep 238119 = 357179) B357179
theorem B434767 : Blo 235815 434767 := bstep (se 1 (by rfl) ⟨326075, by rfl⟩ : syracuseStep 434767 = 652151) B652151
theorem B238159 : Blo 235815 238159 := bstep (se 1 (by rfl) ⟨178619, by rfl⟩ : syracuseStep 238159 = 357239) B357239
theorem B238175 : Blo 235815 238175 := bstep (se 1 (by rfl) ⟨178631, by rfl⟩ : syracuseStep 238175 = 357263) B357263
theorem B238203 : Blo 235815 238203 := bstep (se 1 (by rfl) ⟨178652, by rfl⟩ : syracuseStep 238203 = 357305) B357305
theorem B402043 : Blo 235815 402043 := bstep (se 1 (by rfl) ⟨301532, by rfl⟩ : syracuseStep 402043 = 603065) B603065
theorem B238255 : Blo 235815 238255 := bstep (se 1 (by rfl) ⟨178691, by rfl⟩ : syracuseStep 238255 = 357383) B357383
theorem B238279 : Blo 235815 238279 := bstep (se 1 (by rfl) ⟨178709, by rfl⟩ : syracuseStep 238279 = 357419) B357419
theorem B238299 : Blo 235815 238299 := bstep (se 1 (by rfl) ⟨178724, by rfl⟩ : syracuseStep 238299 = 357449) B357449
theorem B4072193 : Blo 235815 4072193 := bstep (se 2 (by rfl) ⟨1527072, by rfl⟩ : syracuseStep 4072193 = 3054145) B3054145
theorem B1352477 : Blo 235815 1352477 := bstep (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) B507179
theorem B238375 : Blo 235815 238375 := bstep (se 1 (by rfl) ⟨178781, by rfl⟩ : syracuseStep 238375 = 357563) B357563
theorem B533321 : Blo 235815 533321 := bstep (se 2 (by rfl) ⟨199995, by rfl⟩ : syracuseStep 533321 = 399991) B399991
theorem B238415 : Blo 235815 238415 := bstep (se 1 (by rfl) ⟨178811, by rfl⟩ : syracuseStep 238415 = 357623) B357623
theorem B271199 : Blo 235815 271199 := bstep (se 1 (by rfl) ⟨203399, by rfl⟩ : syracuseStep 271199 = 406799) B406799
theorem B238431 : Blo 235815 238431 := bstep (se 1 (by rfl) ⟨178823, by rfl⟩ : syracuseStep 238431 = 357647) B357647
theorem B238459 : Blo 235815 238459 := bstep (se 1 (by rfl) ⟨178844, by rfl⟩ : syracuseStep 238459 = 357689) B357689
theorem B238511 : Blo 235815 238511 := bstep (se 1 (by rfl) ⟨178883, by rfl⟩ : syracuseStep 238511 = 357767) B357767
theorem B238535 : Blo 235815 238535 := bstep (se 1 (by rfl) ⟨178901, by rfl⟩ : syracuseStep 238535 = 357803) B357803
theorem B238555 : Blo 235815 238555 := bstep (se 1 (by rfl) ⟨178916, by rfl⟩ : syracuseStep 238555 = 357833) B357833
theorem B238631 : Blo 235815 238631 := bstep (se 1 (by rfl) ⟨178973, by rfl⟩ : syracuseStep 238631 = 357947) B357947
theorem B238671 : Blo 235815 238671 := bstep (se 1 (by rfl) ⟨179003, by rfl⟩ : syracuseStep 238671 = 358007) B358007
theorem B238687 : Blo 235815 238687 := bstep (se 1 (by rfl) ⟨179015, by rfl⟩ : syracuseStep 238687 = 358031) B358031
theorem B238715 : Blo 235815 238715 := bstep (se 1 (by rfl) ⟨179036, by rfl⟩ : syracuseStep 238715 = 358073) B358073
theorem B238767 : Blo 235815 238767 := bstep (se 1 (by rfl) ⟨179075, by rfl⟩ : syracuseStep 238767 = 358151) B358151
theorem B238791 : Blo 235815 238791 := bstep (se 1 (by rfl) ⟨179093, by rfl⟩ : syracuseStep 238791 = 358187) B358187
theorem B238811 : Blo 235815 238811 := bstep (se 1 (by rfl) ⟨179108, by rfl⟩ : syracuseStep 238811 = 358217) B358217
theorem B959735 : Blo 235815 959735 := bstep (se 1 (by rfl) ⟨719801, by rfl⟩ : syracuseStep 959735 = 1439603) B1439603
theorem B238887 : Blo 235815 238887 := bstep (se 1 (by rfl) ⟨179165, by rfl⟩ : syracuseStep 238887 = 358331) B358331
theorem B238927 : Blo 235815 238927 := bstep (se 1 (by rfl) ⟨179195, by rfl⟩ : syracuseStep 238927 = 358391) B358391
theorem B238943 : Blo 235815 238943 := bstep (se 1 (by rfl) ⟨179207, by rfl⟩ : syracuseStep 238943 = 358415) B358415
theorem B238971 : Blo 235815 238971 := bstep (se 1 (by rfl) ⟨179228, by rfl⟩ : syracuseStep 238971 = 358457) B358457
theorem B239023 : Blo 235815 239023 := bstep (se 1 (by rfl) ⟨179267, by rfl⟩ : syracuseStep 239023 = 358535) B358535
theorem B239047 : Blo 235815 239047 := bstep (se 1 (by rfl) ⟨179285, by rfl⟩ : syracuseStep 239047 = 358571) B358571
theorem B402907 : Blo 235815 402907 := bstep (se 1 (by rfl) ⟨302180, by rfl⟩ : syracuseStep 402907 = 604361) B604361
theorem B239067 : Blo 235815 239067 := bstep (se 1 (by rfl) ⟨179300, by rfl⟩ : syracuseStep 239067 = 358601) B358601
theorem B239143 : Blo 235815 239143 := bstep (se 1 (by rfl) ⟨179357, by rfl⟩ : syracuseStep 239143 = 358715) B358715
theorem B960059 : Blo 235815 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B239183 : Blo 235815 239183 := bstep (se 1 (by rfl) ⟨179387, by rfl⟩ : syracuseStep 239183 = 358775) B358775
theorem B239199 : Blo 235815 239199 := bstep (se 1 (by rfl) ⟨179399, by rfl⟩ : syracuseStep 239199 = 358799) B358799
theorem B534113 : Blo 235815 534113 := bstep (se 2 (by rfl) ⟨200292, by rfl⟩ : syracuseStep 534113 = 400585) B400585
theorem B796283 : Blo 235815 796283 := bstep (se 1 (by rfl) ⟨597212, by rfl⟩ : syracuseStep 796283 = 1194425) B1194425
theorem B239227 : Blo 235815 239227 := bstep (se 1 (by rfl) ⟨179420, by rfl⟩ : syracuseStep 239227 = 358841) B358841
theorem B239279 : Blo 235815 239279 := bstep (se 1 (by rfl) ⟨179459, by rfl⟩ : syracuseStep 239279 = 358919) B358919
theorem B239303 : Blo 235815 239303 := bstep (se 1 (by rfl) ⟨179477, by rfl⟩ : syracuseStep 239303 = 358955) B358955
theorem B239323 : Blo 235815 239323 := bstep (se 1 (by rfl) ⟨179492, by rfl⟩ : syracuseStep 239323 = 358985) B358985
theorem B796445 : Blo 235815 796445 := bstep (se 3 (by rfl) ⟨149333, by rfl⟩ : syracuseStep 796445 = 298667) B298667
theorem B239399 : Blo 235815 239399 := bstep (se 1 (by rfl) ⟨179549, by rfl⟩ : syracuseStep 239399 = 359099) B359099
theorem B239439 : Blo 235815 239439 := bstep (se 1 (by rfl) ⟨179579, by rfl⟩ : syracuseStep 239439 = 359159) B359159
theorem B239455 : Blo 235815 239455 := bstep (se 1 (by rfl) ⟨179591, by rfl⟩ : syracuseStep 239455 = 359183) B359183
theorem B239483 : Blo 235815 239483 := bstep (se 1 (by rfl) ⟨179612, by rfl⟩ : syracuseStep 239483 = 359225) B359225
theorem B239535 : Blo 235815 239535 := bstep (se 1 (by rfl) ⟨179651, by rfl⟩ : syracuseStep 239535 = 359303) B359303
theorem B534455 : Blo 235815 534455 := bstep (se 1 (by rfl) ⟨400841, by rfl⟩ : syracuseStep 534455 = 801683) B801683
theorem B239559 : Blo 235815 239559 := bstep (se 1 (by rfl) ⟨179669, by rfl⟩ : syracuseStep 239559 = 359339) B359339
theorem B239579 : Blo 235815 239579 := bstep (se 1 (by rfl) ⟨179684, by rfl⟩ : syracuseStep 239579 = 359369) B359369
theorem B239655 : Blo 235815 239655 := bstep (se 1 (by rfl) ⟨179741, by rfl⟩ : syracuseStep 239655 = 359483) B359483
theorem B403535 : Blo 235815 403535 := bstep (se 1 (by rfl) ⟨302651, by rfl⟩ : syracuseStep 403535 = 605303) B605303
theorem B239695 : Blo 235815 239695 := bstep (se 1 (by rfl) ⟨179771, by rfl⟩ : syracuseStep 239695 = 359543) B359543
theorem B239711 : Blo 235815 239711 := bstep (se 1 (by rfl) ⟨179783, by rfl⟩ : syracuseStep 239711 = 359567) B359567
theorem B239739 : Blo 235815 239739 := bstep (se 1 (by rfl) ⟨179804, by rfl⟩ : syracuseStep 239739 = 359609) B359609
theorem B239791 : Blo 235815 239791 := bstep (se 1 (by rfl) ⟨179843, by rfl⟩ : syracuseStep 239791 = 359687) B359687
theorem B239815 : Blo 235815 239815 := bstep (se 1 (by rfl) ⟨179861, by rfl⟩ : syracuseStep 239815 = 359723) B359723
theorem B600311 : Blo 235815 600311 := bstep (se 1 (by rfl) ⟨450233, by rfl⟩ : syracuseStep 600311 = 900467) B900467
theorem B1681817 : Blo 235815 1681817 := bstep (se 2 (by rfl) ⟨630681, by rfl⟩ : syracuseStep 1681817 = 1261363) B1261363
theorem B338359 : Blo 235815 338359 := bstep (se 1 (by rfl) ⟨253769, by rfl⟩ : syracuseStep 338359 = 507539) B507539
theorem B797147 : Blo 235815 797147 := bstep (se 1 (by rfl) ⟨597860, by rfl⟩ : syracuseStep 797147 = 1195721) B1195721
theorem B535049 : Blo 235815 535049 := bstep (se 2 (by rfl) ⟨200643, by rfl⟩ : syracuseStep 535049 = 401287) B401287
theorem B535391 : Blo 235815 535391 := bstep (se 1 (by rfl) ⟨401543, by rfl⟩ : syracuseStep 535391 = 803087) B803087
theorem B404399 : Blo 235815 404399 := bstep (se 1 (by rfl) ⟨303299, by rfl⟩ : syracuseStep 404399 = 606599) B606599
theorem B535571 : Blo 235815 535571 := bstep (se 1 (by rfl) ⟨401678, by rfl⟩ : syracuseStep 535571 = 803357) B803357
theorem B601145 : Blo 235815 601145 := bstep (se 2 (by rfl) ⟨225429, by rfl⟩ : syracuseStep 601145 = 450859) B450859
theorem B797849 : Blo 235815 797849 := bstep (se 2 (by rfl) ⟨299193, by rfl⟩ : syracuseStep 797849 = 598387) B598387
theorem B2174147 : Blo 235815 2174147 := bstep (se 1 (by rfl) ⟨1630610, by rfl⟩ : syracuseStep 2174147 = 3261221) B3261221
theorem B1813751 : Blo 235815 1813751 := bstep (se 1 (by rfl) ⟨1360313, by rfl⟩ : syracuseStep 1813751 = 2720627) B2720627
theorem B535913 : Blo 235815 535913 := bstep (se 2 (by rfl) ⟨200967, by rfl⟩ : syracuseStep 535913 = 401935) B401935
theorem B896609 : Blo 235815 896609 := bstep (se 2 (by rfl) ⟨336228, by rfl⟩ : syracuseStep 896609 = 672457) B672457
theorem B601739 : Blo 235815 601739 := bstep (se 1 (by rfl) ⟨451304, by rfl⟩ : syracuseStep 601739 = 902609) B902609
theorem B765587 : Blo 235815 765587 := bstep (se 1 (by rfl) ⟨574190, by rfl⟩ : syracuseStep 765587 = 1148381) B1148381
theorem B1814237 : Blo 235815 1814237 := bstep (se 3 (by rfl) ⟨340169, by rfl⟩ : syracuseStep 1814237 = 680339) B680339
theorem B601951 : Blo 235815 601951 := bstep (se 1 (by rfl) ⟨451463, by rfl⟩ : syracuseStep 601951 = 902927) B902927
theorem B339817 : Blo 235815 339817 := bstep (se 2 (by rfl) ⟨127431, by rfl⟩ : syracuseStep 339817 = 254863) B254863
theorem B536507 : Blo 235815 536507 := bstep (se 1 (by rfl) ⟨402380, by rfl⟩ : syracuseStep 536507 = 804761) B804761
theorem B536633 : Blo 235815 536633 := bstep (se 2 (by rfl) ⟨201237, by rfl⟩ : syracuseStep 536633 = 402475) B402475
theorem B3321917 : Blo 235815 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B799037 : Blo 235815 799037 := bstep (se 3 (by rfl) ⟨149819, by rfl⟩ : syracuseStep 799037 = 299639) B299639
theorem B3649853 : Blo 235815 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B536975 : Blo 235815 536975 := bstep (se 1 (by rfl) ⟨402731, by rfl⟩ : syracuseStep 536975 = 805463) B805463
theorem B569953 : Blo 235815 569953 := bstep (se 2 (by rfl) ⟨213732, by rfl⟩ : syracuseStep 569953 = 427465) B427465
theorem B733819 : Blo 235815 733819 := bstep (se 1 (by rfl) ⟨550364, by rfl⟩ : syracuseStep 733819 = 1100729) B1100729
theorem B537299 : Blo 235815 537299 := bstep (se 1 (by rfl) ⟨402974, by rfl⟩ : syracuseStep 537299 = 805949) B805949
theorem B602873 : Blo 235815 602873 := bstep (se 2 (by rfl) ⟨226077, by rfl⟩ : syracuseStep 602873 = 452155) B452155
theorem B570185 : Blo 235815 570185 := bstep (se 2 (by rfl) ⟨213819, by rfl⟩ : syracuseStep 570185 = 427639) B427639
theorem B406415 : Blo 235815 406415 := bstep (se 1 (by rfl) ⟨304811, by rfl⟩ : syracuseStep 406415 = 609623) B609623
theorem B898067 : Blo 235815 898067 := bstep (se 1 (by rfl) ⟨673550, by rfl⟩ : syracuseStep 898067 = 1347101) B1347101
theorem B1356851 : Blo 235815 1356851 := bstep (se 1 (by rfl) ⟨1017638, by rfl⟩ : syracuseStep 1356851 = 2035277) B2035277
theorem B6075485 : Blo 235815 6075485 := bstep (se 3 (by rfl) ⟨1139153, by rfl⟩ : syracuseStep 6075485 = 2278307) B2278307
theorem B799901 : Blo 235815 799901 := bstep (se 3 (by rfl) ⟨149981, by rfl⟩ : syracuseStep 799901 = 299963) B299963
theorem B767357 : Blo 235815 767357 := bstep (se 3 (by rfl) ⟨143879, by rfl⟩ : syracuseStep 767357 = 287759) B287759
theorem B603521 : Blo 235815 603521 := bstep (se 2 (by rfl) ⟨226320, by rfl⟩ : syracuseStep 603521 = 452641) B452641
theorem B898523 : Blo 235815 898523 := bstep (se 1 (by rfl) ⟨673892, by rfl⟩ : syracuseStep 898523 = 1347785) B1347785
theorem B538235 : Blo 235815 538235 := bstep (se 1 (by rfl) ⟨403676, by rfl⟩ : syracuseStep 538235 = 807353) B807353
theorem B767627 : Blo 235815 767627 := bstep (se 1 (by rfl) ⟨575720, by rfl⟩ : syracuseStep 767627 = 1151441) B1151441
theorem B800441 : Blo 235815 800441 := bstep (se 2 (by rfl) ⟨300165, by rfl⟩ : syracuseStep 800441 = 600331) B600331
theorem B538361 : Blo 235815 538361 := bstep (se 2 (by rfl) ⟨201885, by rfl⟩ : syracuseStep 538361 = 403771) B403771
theorem B538631 : Blo 235815 538631 := bstep (se 1 (by rfl) ⟨403973, by rfl⟩ : syracuseStep 538631 = 807947) B807947
theorem B538703 : Blo 235815 538703 := bstep (se 1 (by rfl) ⟨404027, by rfl⟩ : syracuseStep 538703 = 808055) B808055
theorem B604331 : Blo 235815 604331 := bstep (se 1 (by rfl) ⟨453248, by rfl⟩ : syracuseStep 604331 = 906497) B906497
theorem B801035 : Blo 235815 801035 := bstep (se 1 (by rfl) ⟨600776, by rfl⟩ : syracuseStep 801035 = 1201553) B1201553
theorem B2701673 : Blo 235815 2701673 := bstep (se 2 (by rfl) ⟨1013127, by rfl⟩ : syracuseStep 2701673 = 2026255) B2026255
theorem B1980805 : Blo 235815 1980805 := bstep (se 4 (by rfl) ⟨185700, by rfl⟩ : syracuseStep 1980805 = 371401) B371401
theorem B1915289 : Blo 235815 1915289 := bstep (se 2 (by rfl) ⟨718233, by rfl⟩ : syracuseStep 1915289 = 1436467) B1436467
theorem B539099 : Blo 235815 539099 := bstep (se 1 (by rfl) ⟨404324, by rfl⟩ : syracuseStep 539099 = 808649) B808649
theorem B801305 : Blo 235815 801305 := bstep (se 2 (by rfl) ⟨300489, by rfl⟩ : syracuseStep 801305 = 600979) B600979
theorem B899707 : Blo 235815 899707 := bstep (se 1 (by rfl) ⟨674780, by rfl⟩ : syracuseStep 899707 = 1349561) B1349561
theorem B539567 : Blo 235815 539567 := bstep (se 1 (by rfl) ⟨404675, by rfl⟩ : syracuseStep 539567 = 809351) B809351
theorem B605191 : Blo 235815 605191 := bstep (se 1 (by rfl) ⟨453893, by rfl⟩ : syracuseStep 605191 = 907787) B907787
theorem B1719575 : Blo 235815 1719575 := bstep (se 1 (by rfl) ⟨1289681, by rfl⟩ : syracuseStep 1719575 = 2579363) B2579363
theorem B1195559 : Blo 235815 1195559 := bstep (se 1 (by rfl) ⟨896669, by rfl⟩ : syracuseStep 1195559 = 1793339) B1793339
theorem B605819 : Blo 235815 605819 := bstep (se 1 (by rfl) ⟨454364, by rfl⟩ : syracuseStep 605819 = 908729) B908729
theorem B802439 : Blo 235815 802439 := bstep (se 1 (by rfl) ⟨601829, by rfl⟩ : syracuseStep 802439 = 1203659) B1203659
theorem B802493 : Blo 235815 802493 := bstep (se 3 (by rfl) ⟨150467, by rfl⟩ : syracuseStep 802493 = 300935) B300935
theorem B966467 : Blo 235815 966467 := bstep (se 1 (by rfl) ⟨724850, by rfl⟩ : syracuseStep 966467 = 1449701) B1449701
theorem B802655 : Blo 235815 802655 := bstep (se 1 (by rfl) ⟨601991, by rfl⟩ : syracuseStep 802655 = 1203983) B1203983
theorem B900983 : Blo 235815 900983 := bstep (se 1 (by rfl) ⟨675737, by rfl⟩ : syracuseStep 900983 = 1351475) B1351475
theorem B606113 : Blo 235815 606113 := bstep (se 2 (by rfl) ⟨227292, by rfl⟩ : syracuseStep 606113 = 454585) B454585
theorem B802817 : Blo 235815 802817 := bstep (se 2 (by rfl) ⟨301056, by rfl⟩ : syracuseStep 802817 = 602113) B602113
theorem B11583755 : Blo 235815 11583755 := bstep (se 1 (by rfl) ⟨8687816, by rfl⟩ : syracuseStep 11583755 = 17375633) B17375633
theorem B508265 : Blo 235815 508265 := bstep (se 2 (by rfl) ⟨190599, by rfl⟩ : syracuseStep 508265 = 381199) B381199
theorem B1294697 : Blo 235815 1294697 := bstep (se 2 (by rfl) ⟨485511, by rfl⟩ : syracuseStep 1294697 = 971023) B971023
theorem B1524257 : Blo 235815 1524257 := bstep (se 2 (by rfl) ⟨571596, by rfl⟩ : syracuseStep 1524257 = 1143193) B1143193
theorem B869063 : Blo 235815 869063 := bstep (se 1 (by rfl) ⟨651797, by rfl⟩ : syracuseStep 869063 = 1303595) B1303595
theorem B803627 : Blo 235815 803627 := bstep (se 1 (by rfl) ⟨602720, by rfl⟩ : syracuseStep 803627 = 1205441) B1205441
theorem B901955 : Blo 235815 901955 := bstep (se 1 (by rfl) ⟨676466, by rfl⟩ : syracuseStep 901955 = 1352933) B1352933
theorem B1917917 : Blo 235815 1917917 := bstep (se 3 (by rfl) ⟨359609, by rfl⟩ : syracuseStep 1917917 = 719219) B719219
theorem B803897 : Blo 235815 803897 := bstep (se 2 (by rfl) ⟨301461, by rfl⟩ : syracuseStep 803897 = 602923) B602923
theorem B902411 : Blo 235815 902411 := bstep (se 1 (by rfl) ⟨676808, by rfl⟩ : syracuseStep 902411 = 1353617) B1353617
theorem B804221 : Blo 235815 804221 := bstep (se 3 (by rfl) ⟨150791, by rfl⟩ : syracuseStep 804221 = 301583) B301583
theorem B1820069 : Blo 235815 1820069 := bstep (se 4 (by rfl) ⟨170631, by rfl⟩ : syracuseStep 1820069 = 341263) B341263
theorem B2868797 : Blo 235815 2868797 := bstep (se 3 (by rfl) ⟨537899, by rfl⟩ : syracuseStep 2868797 = 1075799) B1075799
theorem B1197665 : Blo 235815 1197665 := bstep (se 2 (by rfl) ⟨449124, by rfl⟩ : syracuseStep 1197665 = 898249) B898249
theorem B509537 : Blo 235815 509537 := bstep (se 2 (by rfl) ⟨191076, by rfl⟩ : syracuseStep 509537 = 382153) B382153
theorem B1295995 : Blo 235815 1295995 := bstep (se 1 (by rfl) ⟨971996, by rfl⟩ : syracuseStep 1295995 = 1943993) B1943993
theorem B804491 : Blo 235815 804491 := bstep (se 1 (by rfl) ⟨603368, by rfl⟩ : syracuseStep 804491 = 1206737) B1206737
theorem B345961 : Blo 235815 345961 := bstep (se 2 (by rfl) ⟨129735, by rfl⟩ : syracuseStep 345961 = 259471) B259471
theorem B903095 : Blo 235815 903095 := bstep (se 1 (by rfl) ⟨677321, by rfl⟩ : syracuseStep 903095 = 1354643) B1354643
theorem B968723 : Blo 235815 968723 := bstep (se 1 (by rfl) ⟨726542, by rfl⟩ : syracuseStep 968723 = 1453085) B1453085
theorem B3426461 : Blo 235815 3426461 := bstep (se 3 (by rfl) ⟨642461, by rfl⟩ : syracuseStep 3426461 = 1284923) B1284923
theorem B805409 : Blo 235815 805409 := bstep (se 2 (by rfl) ⟨302028, by rfl⟩ : syracuseStep 805409 = 604057) B604057
theorem B903869 : Blo 235815 903869 := bstep (se 3 (by rfl) ⟨169475, by rfl⟩ : syracuseStep 903869 = 338951) B338951
theorem B805625 : Blo 235815 805625 := bstep (se 2 (by rfl) ⟨302109, by rfl⟩ : syracuseStep 805625 = 604219) B604219
theorem B609131 : Blo 235815 609131 := bstep (se 1 (by rfl) ⟨456848, by rfl⟩ : syracuseStep 609131 = 913697) B913697
theorem B2214839 : Blo 235815 2214839 := bstep (se 1 (by rfl) ⟨1661129, by rfl⟩ : syracuseStep 2214839 = 3322259) B3322259
theorem B805895 : Blo 235815 805895 := bstep (se 1 (by rfl) ⟨604421, by rfl⟩ : syracuseStep 805895 = 1208843) B1208843
theorem B1199123 : Blo 235815 1199123 := bstep (se 1 (by rfl) ⟨899342, by rfl⟩ : syracuseStep 1199123 = 1798685) B1798685
theorem B806003 : Blo 235815 806003 := bstep (se 1 (by rfl) ⟨604502, by rfl⟩ : syracuseStep 806003 = 1209005) B1209005
theorem B1363139 : Blo 235815 1363139 := bstep (se 1 (by rfl) ⟨1022354, by rfl⟩ : syracuseStep 1363139 = 2044709) B2044709
theorem B904553 : Blo 235815 904553 := bstep (se 2 (by rfl) ⟨339207, by rfl⟩ : syracuseStep 904553 = 678415) B678415
theorem B806273 : Blo 235815 806273 := bstep (se 2 (by rfl) ⟨302352, by rfl⟩ : syracuseStep 806273 = 604705) B604705
theorem B511451 : Blo 235815 511451 := bstep (se 1 (by rfl) ⟨383588, by rfl⟩ : syracuseStep 511451 = 767177) B767177
theorem B479083 : Blo 235815 479083 := bstep (se 1 (by rfl) ⟨359312, by rfl⟩ : syracuseStep 479083 = 718625) B718625
theorem B2019491 : Blo 235815 2019491 := bstep (se 1 (by rfl) ⟨1514618, by rfl⟩ : syracuseStep 2019491 = 3029237) B3029237
theorem B807083 : Blo 235815 807083 := bstep (se 1 (by rfl) ⟨605312, by rfl⟩ : syracuseStep 807083 = 1210625) B1210625
theorem B9752773 : Blo 235815 9752773 := bstep (se 4 (by rfl) ⟨914322, by rfl⟩ : syracuseStep 9752773 = 1828645) B1828645
theorem B3297509 : Blo 235815 3297509 := bstep (se 4 (by rfl) ⟨309141, by rfl⟩ : syracuseStep 3297509 = 618283) B618283
theorem B643457 : Blo 235815 643457 := bstep (se 2 (by rfl) ⟨241296, by rfl⟩ : syracuseStep 643457 = 482593) B482593
theorem B479675 : Blo 235815 479675 := bstep (se 1 (by rfl) ⟨359756, by rfl⟩ : syracuseStep 479675 = 719513) B719513
theorem B807623 : Blo 235815 807623 := bstep (se 1 (by rfl) ⟨605717, by rfl⟩ : syracuseStep 807623 = 1211435) B1211435
theorem B480161 : Blo 235815 480161 := bstep (se 2 (by rfl) ⟨180060, by rfl⟩ : syracuseStep 480161 = 360121) B360121
theorem B381871 : Blo 235815 381871 := bstep (se 1 (by rfl) ⟨286403, by rfl⟩ : syracuseStep 381871 = 572807) B572807
theorem B1791395 : Blo 235815 1791395 := bstep (se 1 (by rfl) ⟨1343546, by rfl⟩ : syracuseStep 1791395 = 2687093) B2687093
theorem B906785 : Blo 235815 906785 := bstep (se 2 (by rfl) ⟨340044, by rfl⟩ : syracuseStep 906785 = 680089) B680089
theorem B808487 : Blo 235815 808487 := bstep (se 1 (by rfl) ⟨606365, by rfl⟩ : syracuseStep 808487 = 1212731) B1212731
theorem B808595 : Blo 235815 808595 := bstep (se 1 (by rfl) ⟨606446, by rfl⟩ : syracuseStep 808595 = 1212893) B1212893
theorem B1529533 : Blo 235815 1529533 := bstep (se 3 (by rfl) ⟨286787, by rfl⟩ : syracuseStep 1529533 = 573575) B573575
theorem B2447147 : Blo 235815 2447147 := bstep (se 1 (by rfl) ⟨1835360, by rfl⟩ : syracuseStep 2447147 = 3670721) B3670721
theorem B808811 : Blo 235815 808811 := bstep (se 1 (by rfl) ⟨606608, by rfl⟩ : syracuseStep 808811 = 1213217) B1213217
theorem B1202039 : Blo 235815 1202039 := bstep (se 1 (by rfl) ⟨901529, by rfl⟩ : syracuseStep 1202039 = 1803059) B1803059
theorem B808865 : Blo 235815 808865 := bstep (se 2 (by rfl) ⟨303324, by rfl⟩ : syracuseStep 808865 = 606649) B606649
theorem B284635 : Blo 235815 284635 := bstep (se 1 (by rfl) ⟨213476, by rfl⟩ : syracuseStep 284635 = 426953) B426953
theorem B907271 : Blo 235815 907271 := bstep (se 1 (by rfl) ⟨680453, by rfl⟩ : syracuseStep 907271 = 1360907) B1360907
theorem B383147 : Blo 235815 383147 := bstep (se 1 (by rfl) ⟨287360, by rfl⟩ : syracuseStep 383147 = 574721) B574721
theorem B6314273 : Blo 235815 6314273 := bstep (se 2 (by rfl) ⟨2367852, by rfl⟩ : syracuseStep 6314273 = 4735705) B4735705
theorem B907757 : Blo 235815 907757 := bstep (se 3 (by rfl) ⟨170204, by rfl⟩ : syracuseStep 907757 = 340409) B340409
theorem B449543 : Blo 235815 449543 := bstep (se 1 (by rfl) ⟨337157, by rfl⟩ : syracuseStep 449543 = 674315) B674315
theorem B908441 : Blo 235815 908441 := bstep (se 2 (by rfl) ⟨340665, by rfl⟩ : syracuseStep 908441 = 681331) B681331
theorem B449975 : Blo 235815 449975 := bstep (se 1 (by rfl) ⟨337481, by rfl⟩ : syracuseStep 449975 = 674963) B674963
theorem B1531379 : Blo 235815 1531379 := bstep (se 1 (by rfl) ⟨1148534, by rfl⟩ : syracuseStep 1531379 = 2297069) B2297069
theorem B450127 : Blo 235815 450127 := bstep (se 1 (by rfl) ⟨337595, by rfl⟩ : syracuseStep 450127 = 675191) B675191
theorem B810643 : Blo 235815 810643 := bstep (se 1 (by rfl) ⟨607982, by rfl⟩ : syracuseStep 810643 = 1215965) B1215965
theorem B1793825 : Blo 235815 1793825 := bstep (se 2 (by rfl) ⟨672684, by rfl⟩ : syracuseStep 1793825 = 1345369) B1345369
theorem B286759 : Blo 235815 286759 := bstep (se 1 (by rfl) ⟨215069, by rfl⟩ : syracuseStep 286759 = 430139) B430139
theorem B909427 : Blo 235815 909427 := bstep (se 1 (by rfl) ⟨682070, by rfl⟩ : syracuseStep 909427 = 1364141) B1364141
theorem B811529 : Blo 235815 811529 := bstep (se 2 (by rfl) ⟨304323, by rfl⟩ : syracuseStep 811529 = 608647) B608647
theorem B1008413 : Blo 235815 1008413 := bstep (se 3 (by rfl) ⟨189077, by rfl⟩ : syracuseStep 1008413 = 378155) B378155
theorem B451433 : Blo 235815 451433 := bstep (se 2 (by rfl) ⟨169287, by rfl⟩ : syracuseStep 451433 = 338575) B338575
theorem B910187 : Blo 235815 910187 := bstep (se 1 (by rfl) ⟨682640, by rfl⟩ : syracuseStep 910187 = 1365281) B1365281
theorem B320431 : Blo 235815 320431 := bstep (se 1 (by rfl) ⟨240323, by rfl⟩ : syracuseStep 320431 = 480647) B480647
theorem B1009097 : Blo 235815 1009097 := bstep (se 2 (by rfl) ⟨378411, by rfl⟩ : syracuseStep 1009097 = 756823) B756823
theorem B353801 : Blo 235815 353801 := bstep (se 2 (by rfl) ⟨132675, by rfl⟩ : syracuseStep 353801 = 265351) B265351
theorem B353831 : Blo 235815 353831 := bstep (se 1 (by rfl) ⟨265373, by rfl⟩ : syracuseStep 353831 = 530747) B530747
theorem B353915 : Blo 235815 353915 := bstep (se 1 (by rfl) ⟨265436, by rfl⟩ : syracuseStep 353915 = 530873) B530873
theorem B911033 : Blo 235815 911033 := bstep (se 2 (by rfl) ⟨341637, by rfl⟩ : syracuseStep 911033 = 683275) B683275
theorem B354041 : Blo 235815 354041 := bstep (se 2 (by rfl) ⟨132765, by rfl⟩ : syracuseStep 354041 = 265531) B265531
theorem B2713337 : Blo 235815 2713337 := bstep (se 2 (by rfl) ⟨1017501, by rfl⟩ : syracuseStep 2713337 = 2035003) B2035003
theorem B812843 : Blo 235815 812843 := bstep (se 1 (by rfl) ⟨609632, by rfl⟩ : syracuseStep 812843 = 1219265) B1219265
theorem B4089689 : Blo 235815 4089689 := bstep (se 2 (by rfl) ⟨1533633, by rfl⟩ : syracuseStep 4089689 = 3067267) B3067267
theorem B354143 : Blo 235815 354143 := bstep (se 1 (by rfl) ⟨265607, by rfl⟩ : syracuseStep 354143 = 531215) B531215
theorem B354155 : Blo 235815 354155 := bstep (se 1 (by rfl) ⟨265616, by rfl⟩ : syracuseStep 354155 = 531233) B531233
theorem B452459 : Blo 235815 452459 := bstep (se 1 (by rfl) ⟨339344, by rfl⟩ : syracuseStep 452459 = 678689) B678689
theorem B354383 : Blo 235815 354383 := bstep (se 1 (by rfl) ⟨265787, by rfl⟩ : syracuseStep 354383 = 531575) B531575
theorem B354503 : Blo 235815 354503 := bstep (se 1 (by rfl) ⟨265877, by rfl⟩ : syracuseStep 354503 = 531755) B531755
theorem B3107159 : Blo 235815 3107159 := bstep (se 1 (by rfl) ⟨2330369, by rfl⟩ : syracuseStep 3107159 = 4660739) B4660739
theorem B354665 : Blo 235815 354665 := bstep (se 2 (by rfl) ⟨132999, by rfl⟩ : syracuseStep 354665 = 265999) B265999
theorem B354743 : Blo 235815 354743 := bstep (se 1 (by rfl) ⟨266057, by rfl⟩ : syracuseStep 354743 = 532115) B532115
theorem B354779 : Blo 235815 354779 := bstep (se 1 (by rfl) ⟨266084, by rfl⟩ : syracuseStep 354779 = 532169) B532169
theorem B944621 : Blo 235815 944621 := bstep (se 3 (by rfl) ⟨177116, by rfl⟩ : syracuseStep 944621 = 354233) B354233
theorem B453127 : Blo 235815 453127 := bstep (se 1 (by rfl) ⟨339845, by rfl⟩ : syracuseStep 453127 = 679691) B679691
theorem B1141307 : Blo 235815 1141307 := bstep (se 1 (by rfl) ⟨855980, by rfl⟩ : syracuseStep 1141307 = 1711961) B1711961
theorem B486319 : Blo 235815 486319 := bstep (se 1 (by rfl) ⟨364739, by rfl⟩ : syracuseStep 486319 = 729479) B729479
theorem B355247 : Blo 235815 355247 := bstep (se 1 (by rfl) ⟨266435, by rfl⟩ : syracuseStep 355247 = 532871) B532871
theorem B1207223 : Blo 235815 1207223 := bstep (se 1 (by rfl) ⟨905417, by rfl⟩ : syracuseStep 1207223 = 1810835) B1810835
theorem B355337 : Blo 235815 355337 := bstep (se 2 (by rfl) ⟨133251, by rfl⟩ : syracuseStep 355337 = 266503) B266503
theorem B355367 : Blo 235815 355367 := bstep (se 1 (by rfl) ⟨266525, by rfl⟩ : syracuseStep 355367 = 533051) B533051
theorem B355451 : Blo 235815 355451 := bstep (se 1 (by rfl) ⟨266588, by rfl⟩ : syracuseStep 355451 = 533177) B533177
theorem B355577 : Blo 235815 355577 := bstep (se 2 (by rfl) ⟨133341, by rfl⟩ : syracuseStep 355577 = 266683) B266683
theorem B355679 : Blo 235815 355679 := bstep (se 1 (by rfl) ⟨266759, by rfl⟩ : syracuseStep 355679 = 533519) B533519
theorem B355691 : Blo 235815 355691 := bstep (se 1 (by rfl) ⟨266768, by rfl⟩ : syracuseStep 355691 = 533537) B533537
theorem B355919 : Blo 235815 355919 := bstep (se 1 (by rfl) ⟨266939, by rfl⟩ : syracuseStep 355919 = 533879) B533879
theorem B356039 : Blo 235815 356039 := bstep (se 1 (by rfl) ⟨267029, by rfl⟩ : syracuseStep 356039 = 534059) B534059
theorem B356201 : Blo 235815 356201 := bstep (se 2 (by rfl) ⟨133575, by rfl⟩ : syracuseStep 356201 = 267151) B267151
theorem B356279 : Blo 235815 356279 := bstep (se 1 (by rfl) ⟨267209, by rfl⟩ : syracuseStep 356279 = 534419) B534419
theorem B356315 : Blo 235815 356315 := bstep (se 1 (by rfl) ⟨267236, by rfl⟩ : syracuseStep 356315 = 534473) B534473
theorem B454753 : Blo 235815 454753 := bstep (se 2 (by rfl) ⟨170532, by rfl⟩ : syracuseStep 454753 = 341065) B341065
theorem B2289995 : Blo 235815 2289995 := bstep (se 1 (by rfl) ⟨1717496, by rfl⟩ : syracuseStep 2289995 = 3434993) B3434993
theorem B1208681 : Blo 235815 1208681 := bstep (se 2 (by rfl) ⟨453255, by rfl⟩ : syracuseStep 1208681 = 906511) B906511
theorem B356783 : Blo 235815 356783 := bstep (se 1 (by rfl) ⟨267587, by rfl⟩ : syracuseStep 356783 = 535175) B535175
theorem B356873 : Blo 235815 356873 := bstep (se 2 (by rfl) ⟨133827, by rfl⟩ : syracuseStep 356873 = 267655) B267655
theorem B2912777 : Blo 235815 2912777 := bstep (se 2 (by rfl) ⟨1092291, by rfl⟩ : syracuseStep 2912777 = 2184583) B2184583
theorem B356903 : Blo 235815 356903 := bstep (se 1 (by rfl) ⟨267677, by rfl⟩ : syracuseStep 356903 = 535355) B535355
theorem B356987 : Blo 235815 356987 := bstep (se 1 (by rfl) ⟨267740, by rfl⟩ : syracuseStep 356987 = 535481) B535481
theorem B357113 : Blo 235815 357113 := bstep (se 2 (by rfl) ⟨133917, by rfl⟩ : syracuseStep 357113 = 267835) B267835
theorem B357215 : Blo 235815 357215 := bstep (se 1 (by rfl) ⟨267911, by rfl⟩ : syracuseStep 357215 = 535823) B535823
theorem B357227 : Blo 235815 357227 := bstep (se 1 (by rfl) ⟨267920, by rfl⟩ : syracuseStep 357227 = 535841) B535841
theorem B783361 : Blo 235815 783361 := bstep (se 2 (by rfl) ⟨293760, by rfl⟩ : syracuseStep 783361 = 587521) B587521
theorem B1537103 : Blo 235815 1537103 := bstep (se 1 (by rfl) ⟨1152827, by rfl⟩ : syracuseStep 1537103 = 2305655) B2305655
theorem B357455 : Blo 235815 357455 := bstep (se 1 (by rfl) ⟨268091, by rfl⟩ : syracuseStep 357455 = 536183) B536183
theorem B357575 : Blo 235815 357575 := bstep (se 1 (by rfl) ⟨268181, by rfl⟩ : syracuseStep 357575 = 536363) B536363
theorem B357737 : Blo 235815 357737 := bstep (se 2 (by rfl) ⟨134151, by rfl⟩ : syracuseStep 357737 = 268303) B268303
theorem B357815 : Blo 235815 357815 := bstep (se 1 (by rfl) ⟨268361, by rfl⟩ : syracuseStep 357815 = 536723) B536723
theorem B357851 : Blo 235815 357851 := bstep (se 1 (by rfl) ⟨268388, by rfl⟩ : syracuseStep 357851 = 536777) B536777
theorem B1144307 : Blo 235815 1144307 := bstep (se 1 (by rfl) ⟨858230, by rfl⟩ : syracuseStep 1144307 = 1716461) B1716461
theorem B1570291 : Blo 235815 1570291 := bstep (se 1 (by rfl) ⟨1177718, by rfl⟩ : syracuseStep 1570291 = 2355437) B2355437
theorem B19363697 : Blo 235815 19363697 := bstep (se 2 (by rfl) ⟨7261386, by rfl⟩ : syracuseStep 19363697 = 14522773) B14522773
theorem B817057 : Blo 235815 817057 := bstep (se 2 (by rfl) ⟨306396, by rfl⟩ : syracuseStep 817057 = 612793) B612793
theorem B358319 : Blo 235815 358319 := bstep (se 1 (by rfl) ⟨268739, by rfl⟩ : syracuseStep 358319 = 537479) B537479
theorem B1275841 : Blo 235815 1275841 := bstep (se 2 (by rfl) ⟨478440, by rfl⟩ : syracuseStep 1275841 = 956881) B956881
theorem B358409 : Blo 235815 358409 := bstep (se 2 (by rfl) ⟨134403, by rfl⟩ : syracuseStep 358409 = 268807) B268807
theorem B358439 : Blo 235815 358439 := bstep (se 1 (by rfl) ⟨268829, by rfl⟩ : syracuseStep 358439 = 537659) B537659
theorem B358523 : Blo 235815 358523 := bstep (se 1 (by rfl) ⟨268892, by rfl⟩ : syracuseStep 358523 = 537785) B537785
theorem B489721 : Blo 235815 489721 := bstep (se 2 (by rfl) ⟨183645, by rfl⟩ : syracuseStep 489721 = 367291) B367291
theorem B358649 : Blo 235815 358649 := bstep (se 2 (by rfl) ⟨134493, by rfl⟩ : syracuseStep 358649 = 268987) B268987
theorem B358751 : Blo 235815 358751 := bstep (se 1 (by rfl) ⟨269063, by rfl⟩ : syracuseStep 358751 = 538127) B538127
theorem B358763 : Blo 235815 358763 := bstep (se 1 (by rfl) ⟨269072, by rfl⟩ : syracuseStep 358763 = 538145) B538145
theorem B1210889 : Blo 235815 1210889 := bstep (se 2 (by rfl) ⟨454083, by rfl⟩ : syracuseStep 1210889 = 908167) B908167
theorem B4094509 : Blo 235815 4094509 := bstep (se 3 (by rfl) ⟨767720, by rfl⟩ : syracuseStep 4094509 = 1535441) B1535441
theorem B358991 : Blo 235815 358991 := bstep (se 1 (by rfl) ⟨269243, by rfl⟩ : syracuseStep 358991 = 538487) B538487
theorem B359111 : Blo 235815 359111 := bstep (se 1 (by rfl) ⟨269333, by rfl⟩ : syracuseStep 359111 = 538667) B538667
theorem B817879 : Blo 235815 817879 := bstep (se 1 (by rfl) ⟨613409, by rfl⟩ : syracuseStep 817879 = 1226819) B1226819
theorem B359273 : Blo 235815 359273 := bstep (se 2 (by rfl) ⟨134727, by rfl⟩ : syracuseStep 359273 = 269455) B269455
theorem B359351 : Blo 235815 359351 := bstep (se 1 (by rfl) ⟨269513, by rfl⟩ : syracuseStep 359351 = 539027) B539027
theorem B359387 : Blo 235815 359387 := bstep (se 1 (by rfl) ⟨269540, by rfl⟩ : syracuseStep 359387 = 539081) B539081
theorem B425159 : Blo 235815 425159 := bstep (se 1 (by rfl) ⟨318869, by rfl⟩ : syracuseStep 425159 = 637739) B637739
theorem B5242103 : Blo 235815 5242103 := bstep (se 1 (by rfl) ⟨3931577, by rfl⟩ : syracuseStep 5242103 = 7863155) B7863155
theorem B3440015 : Blo 235815 3440015 := bstep (se 1 (by rfl) ⟨2580011, by rfl⟩ : syracuseStep 3440015 = 5160023) B5160023
theorem B622279 : Blo 235815 622279 := bstep (se 1 (by rfl) ⟨466709, by rfl⟩ : syracuseStep 622279 = 933419) B933419
theorem B425915 : Blo 235815 425915 := bstep (se 1 (by rfl) ⟨319436, by rfl⟩ : syracuseStep 425915 = 638873) B638873
theorem B1212569 : Blo 235815 1212569 := bstep (se 2 (by rfl) ⟨454713, by rfl⟩ : syracuseStep 1212569 = 909427) B909427
theorem B15532195 : Blo 235815 15532195 := bstep (se 1 (by rfl) ⟨11649146, by rfl⟩ : syracuseStep 15532195 = 23298293) B23298293
theorem B1016171 : Blo 235815 1016171 := bstep (se 1 (by rfl) ⟨762128, by rfl⟩ : syracuseStep 1016171 = 1524257) B1524257
theorem B2425349 : Blo 235815 2425349 := bstep (se 4 (by rfl) ⟨227376, by rfl⟩ : syracuseStep 2425349 = 454753) B454753
theorem B1278611 : Blo 235815 1278611 := bstep (se 1 (by rfl) ⟨958958, by rfl⟩ : syracuseStep 1278611 = 1917917) B1917917
theorem B1213379 : Blo 235815 1213379 := bstep (se 1 (by rfl) ⟨910034, by rfl⟩ : syracuseStep 1213379 = 1820069) B1820069
theorem B427241 : Blo 235815 427241 := bstep (se 2 (by rfl) ⟨160215, by rfl⟩ : syracuseStep 427241 = 320431) B320431
theorem B1476559 : Blo 235815 1476559 := bstep (se 1 (by rfl) ⟨1107419, by rfl⟩ : syracuseStep 1476559 = 2214839) B2214839
theorem B723197 : Blo 235815 723197 := bstep (se 3 (by rfl) ⟨135599, by rfl⟩ : syracuseStep 723197 = 271199) B271199
theorem B2459965 : Blo 235815 2459965 := bstep (se 3 (by rfl) ⟨461243, by rfl⟩ : syracuseStep 2459965 = 922487) B922487
theorem B1083773 : Blo 235815 1083773 := bstep (se 3 (by rfl) ⟨203207, by rfl⟩ : syracuseStep 1083773 = 406415) B406415
theorem B1346327 : Blo 235815 1346327 := bstep (se 1 (by rfl) ⟨1009745, by rfl⟩ : syracuseStep 1346327 = 2019491) B2019491
theorem B2198339 : Blo 235815 2198339 := bstep (se 1 (by rfl) ⟨1648754, by rfl⟩ : syracuseStep 2198339 = 3297509) B3297509
theorem B428971 : Blo 235815 428971 := bstep (se 1 (by rfl) ⟨321728, by rfl⟩ : syracuseStep 428971 = 643457) B643457
theorem B265639 : Blo 235815 265639 := bstep (se 1 (by rfl) ⟨199229, by rfl⟩ : syracuseStep 265639 = 398459) B398459
theorem B1969595 : Blo 235815 1969595 := bstep (se 1 (by rfl) ⟨1477196, by rfl⟩ : syracuseStep 1969595 = 2954393) B2954393
theorem B266215 : Blo 235815 266215 := bstep (se 1 (by rfl) ⟨199661, by rfl⟩ : syracuseStep 266215 = 399323) B399323
theorem B2560157 : Blo 235815 2560157 := bstep (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) B960059
theorem B299695 : Blo 235815 299695 := bstep (se 1 (by rfl) ⟨224771, by rfl⟩ : syracuseStep 299695 = 449543) B449543
theorem B398047 : Blo 235815 398047 := bstep (se 1 (by rfl) ⟨298535, by rfl⟩ : syracuseStep 398047 = 597071) B597071
theorem B1020919 : Blo 235815 1020919 := bstep (se 1 (by rfl) ⟨765689, by rfl⟩ : syracuseStep 1020919 = 1531379) B1531379
theorem B398479 : Blo 235815 398479 := bstep (se 1 (by rfl) ⟨298859, by rfl⟩ : syracuseStep 398479 = 597719) B597719
theorem B922823 : Blo 235815 922823 := bstep (se 1 (by rfl) ⟨692117, by rfl⟩ : syracuseStep 922823 = 1384235) B1384235
theorem B398729 : Blo 235815 398729 := bstep (se 2 (by rfl) ⟨149523, by rfl⟩ : syracuseStep 398729 = 299047) B299047
theorem B267871 : Blo 235815 267871 := bstep (se 1 (by rfl) ⟨200903, by rfl⟩ : syracuseStep 267871 = 401807) B401807
theorem B399161 : Blo 235815 399161 := bstep (se 2 (by rfl) ⟨149685, by rfl⟩ : syracuseStep 399161 = 299371) B299371
theorem B759937 : Blo 235815 759937 := bstep (se 2 (by rfl) ⟨284976, by rfl⟩ : syracuseStep 759937 = 569953) B569953
theorem B235867 : Blo 235815 235867 := bstep (se 1 (by rfl) ⟨176900, by rfl⟩ : syracuseStep 235867 = 353801) B353801
theorem B235887 : Blo 235815 235887 := bstep (se 1 (by rfl) ⟨176915, by rfl⟩ : syracuseStep 235887 = 353831) B353831
theorem B530855 : Blo 235815 530855 := bstep (se 1 (by rfl) ⟨398141, by rfl⟩ : syracuseStep 530855 = 796283) B796283
theorem B235943 : Blo 235815 235943 := bstep (se 1 (by rfl) ⟨176957, by rfl⟩ : syracuseStep 235943 = 353915) B353915
theorem B236027 : Blo 235815 236027 := bstep (se 1 (by rfl) ⟨177020, by rfl⟩ : syracuseStep 236027 = 354041) B354041
theorem B1808891 : Blo 235815 1808891 := bstep (se 1 (by rfl) ⟨1356668, by rfl⟩ : syracuseStep 1808891 = 2713337) B2713337
theorem B530963 : Blo 235815 530963 := bstep (se 1 (by rfl) ⟨398222, by rfl⟩ : syracuseStep 530963 = 796445) B796445
theorem B2726459 : Blo 235815 2726459 := bstep (se 1 (by rfl) ⟨2044844, by rfl⟩ : syracuseStep 2726459 = 4089689) B4089689
theorem B236095 : Blo 235815 236095 := bstep (se 1 (by rfl) ⟨177071, by rfl⟩ : syracuseStep 236095 = 354143) B354143
theorem B236103 : Blo 235815 236103 := bstep (se 1 (by rfl) ⟨177077, by rfl⟩ : syracuseStep 236103 = 354155) B354155
theorem B301639 : Blo 235815 301639 := bstep (se 1 (by rfl) ⟨226229, by rfl⟩ : syracuseStep 301639 = 452459) B452459
theorem B531017 : Blo 235815 531017 := bstep (se 2 (by rfl) ⟨199131, by rfl⟩ : syracuseStep 531017 = 398263) B398263
theorem B236255 : Blo 235815 236255 := bstep (se 1 (by rfl) ⟨177191, by rfl⟩ : syracuseStep 236255 = 354383) B354383
theorem B269023 : Blo 235815 269023 := bstep (se 1 (by rfl) ⟨201767, by rfl⟩ : syracuseStep 269023 = 403535) B403535
theorem B236335 : Blo 235815 236335 := bstep (se 1 (by rfl) ⟨177251, by rfl⟩ : syracuseStep 236335 = 354503) B354503
theorem B400207 : Blo 235815 400207 := bstep (se 1 (by rfl) ⟨300155, by rfl⟩ : syracuseStep 400207 = 600311) B600311
theorem B2071439 : Blo 235815 2071439 := bstep (se 1 (by rfl) ⟨1553579, by rfl⟩ : syracuseStep 2071439 = 3107159) B3107159
theorem B236443 : Blo 235815 236443 := bstep (se 1 (by rfl) ⟨177332, by rfl⟩ : syracuseStep 236443 = 354665) B354665
theorem B236495 : Blo 235815 236495 := bstep (se 1 (by rfl) ⟨177371, by rfl⟩ : syracuseStep 236495 = 354743) B354743
theorem B531431 : Blo 235815 531431 := bstep (se 1 (by rfl) ⟨398573, by rfl⟩ : syracuseStep 531431 = 797147) B797147
theorem B236519 : Blo 235815 236519 := bstep (se 1 (by rfl) ⟨177389, by rfl⟩ : syracuseStep 236519 = 354779) B354779
theorem B629747 : Blo 235815 629747 := bstep (se 1 (by rfl) ⟨472310, by rfl⟩ : syracuseStep 629747 = 944621) B944621
theorem B760871 : Blo 235815 760871 := bstep (se 1 (by rfl) ⟨570653, by rfl⟩ : syracuseStep 760871 = 1141307) B1141307
theorem B236831 : Blo 235815 236831 := bstep (se 1 (by rfl) ⟨177623, by rfl⟩ : syracuseStep 236831 = 355247) B355247
theorem B269599 : Blo 235815 269599 := bstep (se 1 (by rfl) ⟨202199, by rfl⟩ : syracuseStep 269599 = 404399) B404399
theorem B236891 : Blo 235815 236891 := bstep (se 1 (by rfl) ⟨177668, by rfl⟩ : syracuseStep 236891 = 355337) B355337
theorem B531809 : Blo 235815 531809 := bstep (se 2 (by rfl) ⟨199428, by rfl⟩ : syracuseStep 531809 = 398857) B398857
theorem B236911 : Blo 235815 236911 := bstep (se 1 (by rfl) ⟨177683, by rfl⟩ : syracuseStep 236911 = 355367) B355367
theorem B400763 : Blo 235815 400763 := bstep (se 1 (by rfl) ⟨300572, by rfl⟩ : syracuseStep 400763 = 601145) B601145
theorem B236967 : Blo 235815 236967 := bstep (se 1 (by rfl) ⟨177725, by rfl⟩ : syracuseStep 236967 = 355451) B355451
theorem B531899 : Blo 235815 531899 := bstep (se 1 (by rfl) ⟨398924, by rfl⟩ : syracuseStep 531899 = 797849) B797849
theorem B1449431 : Blo 235815 1449431 := bstep (se 1 (by rfl) ⟨1087073, by rfl⟩ : syracuseStep 1449431 = 2174147) B2174147
theorem B400889 : Blo 235815 400889 := bstep (se 2 (by rfl) ⟨150333, by rfl⟩ : syracuseStep 400889 = 300667) B300667
theorem B237051 : Blo 235815 237051 := bstep (se 1 (by rfl) ⟨177788, by rfl⟩ : syracuseStep 237051 = 355577) B355577
theorem B532025 : Blo 235815 532025 := bstep (se 2 (by rfl) ⟨199509, by rfl⟩ : syracuseStep 532025 = 399019) B399019
theorem B237119 : Blo 235815 237119 := bstep (se 1 (by rfl) ⟨177839, by rfl⟩ : syracuseStep 237119 = 355679) B355679
theorem B237127 : Blo 235815 237127 := bstep (se 1 (by rfl) ⟨177845, by rfl⟩ : syracuseStep 237127 = 355691) B355691
theorem B2039377 : Blo 235815 2039377 := bstep (se 2 (by rfl) ⟨764766, by rfl⟩ : syracuseStep 2039377 = 1529533) B1529533
theorem B237279 : Blo 235815 237279 := bstep (se 1 (by rfl) ⟨177959, by rfl⟩ : syracuseStep 237279 = 355919) B355919
theorem B597739 : Blo 235815 597739 := bstep (se 1 (by rfl) ⟨448304, by rfl⟩ : syracuseStep 597739 = 896609) B896609
theorem B401159 : Blo 235815 401159 := bstep (se 1 (by rfl) ⟨300869, by rfl⟩ : syracuseStep 401159 = 601739) B601739
theorem B237359 : Blo 235815 237359 := bstep (se 1 (by rfl) ⟨178019, by rfl⟩ : syracuseStep 237359 = 356039) B356039
theorem B1089409 : Blo 235815 1089409 := bstep (se 2 (by rfl) ⟨408528, by rfl⟩ : syracuseStep 1089409 = 817057) B817057
theorem B237467 : Blo 235815 237467 := bstep (se 1 (by rfl) ⟨178100, by rfl⟩ : syracuseStep 237467 = 356201) B356201
theorem B237519 : Blo 235815 237519 := bstep (se 1 (by rfl) ⟨178139, by rfl⟩ : syracuseStep 237519 = 356279) B356279
theorem B237543 : Blo 235815 237543 := bstep (se 1 (by rfl) ⟨178157, by rfl⟩ : syracuseStep 237543 = 356315) B356315
theorem B532691 : Blo 235815 532691 := bstep (se 1 (by rfl) ⟨399518, by rfl⟩ : syracuseStep 532691 = 799037) B799037
theorem B2433235 : Blo 235815 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B532745 : Blo 235815 532745 := bstep (se 2 (by rfl) ⟨199779, by rfl⟩ : syracuseStep 532745 = 399559) B399559
theorem B237855 : Blo 235815 237855 := bstep (se 1 (by rfl) ⟨178391, by rfl⟩ : syracuseStep 237855 = 356783) B356783
theorem B237915 : Blo 235815 237915 := bstep (se 1 (by rfl) ⟨178436, by rfl⟩ : syracuseStep 237915 = 356873) B356873
theorem B1941851 : Blo 235815 1941851 := bstep (se 1 (by rfl) ⟨1456388, by rfl⟩ : syracuseStep 1941851 = 2912777) B2912777
theorem B237935 : Blo 235815 237935 := bstep (se 1 (by rfl) ⟨178451, by rfl⟩ : syracuseStep 237935 = 356903) B356903
theorem B237991 : Blo 235815 237991 := bstep (se 1 (by rfl) ⟨178493, by rfl⟩ : syracuseStep 237991 = 356987) B356987
theorem B532961 : Blo 235815 532961 := bstep (se 2 (by rfl) ⟨199860, by rfl⟩ : syracuseStep 532961 = 399721) B399721
theorem B238075 : Blo 235815 238075 := bstep (se 1 (by rfl) ⟨178556, by rfl⟩ : syracuseStep 238075 = 357113) B357113
theorem B401915 : Blo 235815 401915 := bstep (se 1 (by rfl) ⟨301436, by rfl⟩ : syracuseStep 401915 = 602873) B602873
theorem B238143 : Blo 235815 238143 := bstep (se 1 (by rfl) ⟨178607, by rfl⟩ : syracuseStep 238143 = 357215) B357215
theorem B238151 : Blo 235815 238151 := bstep (se 1 (by rfl) ⟨178613, by rfl⟩ : syracuseStep 238151 = 357227) B357227
theorem B5120657 : Blo 235815 5120657 := bstep (se 2 (by rfl) ⟨1920246, by rfl⟩ : syracuseStep 5120657 = 3840493) B3840493
theorem B598711 : Blo 235815 598711 := bstep (se 1 (by rfl) ⟨449033, by rfl⟩ : syracuseStep 598711 = 898067) B898067
theorem B1024735 : Blo 235815 1024735 := bstep (se 1 (by rfl) ⟨768551, by rfl⟩ : syracuseStep 1024735 = 1537103) B1537103
theorem B238303 : Blo 235815 238303 := bstep (se 1 (by rfl) ⟨178727, by rfl⟩ : syracuseStep 238303 = 357455) B357455
theorem B533267 : Blo 235815 533267 := bstep (se 1 (by rfl) ⟨399950, by rfl⟩ : syracuseStep 533267 = 799901) B799901
theorem B238383 : Blo 235815 238383 := bstep (se 1 (by rfl) ⟨178787, by rfl⟩ : syracuseStep 238383 = 357575) B357575
theorem B238491 : Blo 235815 238491 := bstep (se 1 (by rfl) ⟨178868, by rfl⟩ : syracuseStep 238491 = 357737) B357737
theorem B402347 : Blo 235815 402347 := bstep (se 1 (by rfl) ⟨301760, by rfl⟩ : syracuseStep 402347 = 603521) B603521
theorem B1713089 : Blo 235815 1713089 := bstep (se 2 (by rfl) ⟨642408, by rfl⟩ : syracuseStep 1713089 = 1284817) B1284817
theorem B1090505 : Blo 235815 1090505 := bstep (se 2 (by rfl) ⟨408939, by rfl⟩ : syracuseStep 1090505 = 817879) B817879
theorem B238543 : Blo 235815 238543 := bstep (se 1 (by rfl) ⟨178907, by rfl⟩ : syracuseStep 238543 = 357815) B357815
theorem B599015 : Blo 235815 599015 := bstep (se 1 (by rfl) ⟨449261, by rfl⟩ : syracuseStep 599015 = 898523) B898523
theorem B238567 : Blo 235815 238567 := bstep (se 1 (by rfl) ⟨178925, by rfl⟩ : syracuseStep 238567 = 357851) B357851
theorem B762871 : Blo 235815 762871 := bstep (se 1 (by rfl) ⟨572153, by rfl⟩ : syracuseStep 762871 = 1144307) B1144307
theorem B533627 : Blo 235815 533627 := bstep (se 1 (by rfl) ⟨400220, by rfl⟩ : syracuseStep 533627 = 800441) B800441
theorem B533753 : Blo 235815 533753 := bstep (se 2 (by rfl) ⟨200157, by rfl⟩ : syracuseStep 533753 = 400315) B400315
theorem B238879 : Blo 235815 238879 := bstep (se 1 (by rfl) ⟨179159, by rfl⟩ : syracuseStep 238879 = 358319) B358319
theorem B238939 : Blo 235815 238939 := bstep (se 1 (by rfl) ⟨179204, by rfl⟩ : syracuseStep 238939 = 358409) B358409
theorem B238959 : Blo 235815 238959 := bstep (se 1 (by rfl) ⟨179219, by rfl⟩ : syracuseStep 238959 = 358439) B358439
theorem B533897 : Blo 235815 533897 := bstep (se 2 (by rfl) ⟨200211, by rfl⟩ : syracuseStep 533897 = 400423) B400423
theorem B239015 : Blo 235815 239015 := bstep (se 1 (by rfl) ⟨179261, by rfl⟩ : syracuseStep 239015 = 358523) B358523
theorem B402887 : Blo 235815 402887 := bstep (se 1 (by rfl) ⟨302165, by rfl⟩ : syracuseStep 402887 = 604331) B604331
theorem B239099 : Blo 235815 239099 := bstep (se 1 (by rfl) ⟨179324, by rfl⟩ : syracuseStep 239099 = 358649) B358649
theorem B534023 : Blo 235815 534023 := bstep (se 1 (by rfl) ⟨400517, by rfl⟩ : syracuseStep 534023 = 801035) B801035
theorem B239167 : Blo 235815 239167 := bstep (se 1 (by rfl) ⟨179375, by rfl⟩ : syracuseStep 239167 = 358751) B358751
theorem B239175 : Blo 235815 239175 := bstep (se 1 (by rfl) ⟨179381, by rfl⟩ : syracuseStep 239175 = 358763) B358763
theorem B534203 : Blo 235815 534203 := bstep (se 1 (by rfl) ⟨400652, by rfl⟩ : syracuseStep 534203 = 801305) B801305
theorem B239327 : Blo 235815 239327 := bstep (se 1 (by rfl) ⟨179495, by rfl⟩ : syracuseStep 239327 = 358991) B358991
theorem B239407 : Blo 235815 239407 := bstep (se 1 (by rfl) ⟨179555, by rfl⟩ : syracuseStep 239407 = 359111) B359111
theorem B534329 : Blo 235815 534329 := bstep (se 2 (by rfl) ⟨200373, by rfl⟩ : syracuseStep 534329 = 400747) B400747
theorem B1845125 : Blo 235815 1845125 := bstep (se 4 (by rfl) ⟨172980, by rfl⟩ : syracuseStep 1845125 = 345961) B345961
theorem B239515 : Blo 235815 239515 := bstep (se 1 (by rfl) ⟨179636, by rfl⟩ : syracuseStep 239515 = 359273) B359273
theorem B239567 : Blo 235815 239567 := bstep (se 1 (by rfl) ⟨179675, by rfl⟩ : syracuseStep 239567 = 359351) B359351
theorem B239591 : Blo 235815 239591 := bstep (se 1 (by rfl) ⟨179693, by rfl⟩ : syracuseStep 239591 = 359387) B359387
theorem B600169 : Blo 235815 600169 := bstep (se 2 (by rfl) ⟨225063, by rfl⟩ : syracuseStep 600169 = 450127) B450127
theorem B829705 : Blo 235815 829705 := bstep (se 2 (by rfl) ⟨311139, by rfl⟩ : syracuseStep 829705 = 622279) B622279
theorem B797039 : Blo 235815 797039 := bstep (se 1 (by rfl) ⟨597779, by rfl⟩ : syracuseStep 797039 = 1195559) B1195559
theorem B33499541 : Blo 235815 33499541 := bstep (se 6 (by rfl) ⟨785145, by rfl⟩ : syracuseStep 33499541 = 1570291) B1570291
theorem B403879 : Blo 235815 403879 := bstep (se 1 (by rfl) ⟨302909, by rfl⟩ : syracuseStep 403879 = 605819) B605819
theorem B534959 : Blo 235815 534959 := bstep (se 1 (by rfl) ⟨401219, by rfl⟩ : syracuseStep 534959 = 802439) B802439
theorem B534995 : Blo 235815 534995 := bstep (se 1 (by rfl) ⟨401246, by rfl⟩ : syracuseStep 534995 = 802493) B802493
theorem B535103 : Blo 235815 535103 := bstep (se 1 (by rfl) ⟨401327, by rfl⟩ : syracuseStep 535103 = 802655) B802655
theorem B404041 : Blo 235815 404041 := bstep (se 2 (by rfl) ⟨151515, by rfl⟩ : syracuseStep 404041 = 303031) B303031
theorem B600655 : Blo 235815 600655 := bstep (se 1 (by rfl) ⟨450491, by rfl⟩ : syracuseStep 600655 = 900983) B900983
theorem B404075 : Blo 235815 404075 := bstep (se 1 (by rfl) ⟨303056, by rfl⟩ : syracuseStep 404075 = 606113) B606113
theorem B535211 : Blo 235815 535211 := bstep (se 1 (by rfl) ⟨401408, by rfl⟩ : syracuseStep 535211 = 802817) B802817
theorem B338843 : Blo 235815 338843 := bstep (se 1 (by rfl) ⟨254132, by rfl⟩ : syracuseStep 338843 = 508265) B508265
theorem B863131 : Blo 235815 863131 := bstep (se 1 (by rfl) ⟨647348, by rfl⟩ : syracuseStep 863131 = 1294697) B1294697
theorem B9743435 : Blo 235815 9743435 := bstep (se 1 (by rfl) ⟨7307576, by rfl⟩ : syracuseStep 9743435 = 14615153) B14615153
theorem B896123 : Blo 235815 896123 := bstep (se 1 (by rfl) ⟨672092, by rfl⟩ : syracuseStep 896123 = 1344185) B1344185
theorem B535751 : Blo 235815 535751 := bstep (se 1 (by rfl) ⟨401813, by rfl⟩ : syracuseStep 535751 = 803627) B803627
theorem B601303 : Blo 235815 601303 := bstep (se 1 (by rfl) ⟨450977, by rfl⟩ : syracuseStep 601303 = 901955) B901955
theorem B535931 : Blo 235815 535931 := bstep (se 1 (by rfl) ⟨401948, by rfl⟩ : syracuseStep 535931 = 803897) B803897
theorem B536057 : Blo 235815 536057 := bstep (se 2 (by rfl) ⟨201021, by rfl⟩ : syracuseStep 536057 = 402043) B402043
theorem B601607 : Blo 235815 601607 := bstep (se 1 (by rfl) ⟨451205, by rfl⟩ : syracuseStep 601607 = 902411) B902411
theorem B536147 : Blo 235815 536147 := bstep (se 1 (by rfl) ⟨402110, by rfl⟩ : syracuseStep 536147 = 804221) B804221
theorem B798443 : Blo 235815 798443 := bstep (se 1 (by rfl) ⟨598832, by rfl⟩ : syracuseStep 798443 = 1197665) B1197665
theorem B536327 : Blo 235815 536327 := bstep (se 1 (by rfl) ⟨402245, by rfl⟩ : syracuseStep 536327 = 804491) B804491
theorem B602063 : Blo 235815 602063 := bstep (se 1 (by rfl) ⟨451547, by rfl⟩ : syracuseStep 602063 = 903095) B903095
theorem B536939 : Blo 235815 536939 := bstep (se 1 (by rfl) ⟨402704, by rfl⟩ : syracuseStep 536939 = 805409) B805409
theorem B602579 : Blo 235815 602579 := bstep (se 1 (by rfl) ⟨451934, by rfl⟩ : syracuseStep 602579 = 903869) B903869
theorem B537083 : Blo 235815 537083 := bstep (se 1 (by rfl) ⟨402812, by rfl⟩ : syracuseStep 537083 = 805625) B805625
theorem B8663597 : Blo 235815 8663597 := bstep (se 3 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 8663597 = 3248849) B3248849
theorem B537209 : Blo 235815 537209 := bstep (se 2 (by rfl) ⟨201453, by rfl⟩ : syracuseStep 537209 = 402907) B402907
theorem B537263 : Blo 235815 537263 := bstep (se 1 (by rfl) ⟨402947, by rfl⟩ : syracuseStep 537263 = 805895) B805895
theorem B799415 : Blo 235815 799415 := bstep (se 1 (by rfl) ⟨599561, by rfl⟩ : syracuseStep 799415 = 1199123) B1199123
theorem B537335 : Blo 235815 537335 := bstep (se 1 (by rfl) ⟨403001, by rfl⟩ : syracuseStep 537335 = 806003) B806003
theorem B504719 : Blo 235815 504719 := bstep (se 1 (by rfl) ⟨378539, by rfl⟩ : syracuseStep 504719 = 757079) B757079
theorem B603035 : Blo 235815 603035 := bstep (se 1 (by rfl) ⟨452276, by rfl⟩ : syracuseStep 603035 = 904553) B904553
theorem B537515 : Blo 235815 537515 := bstep (se 1 (by rfl) ⟨403136, by rfl⟩ : syracuseStep 537515 = 806273) B806273
theorem B340967 : Blo 235815 340967 := bstep (se 1 (by rfl) ⟨255725, by rfl⟩ : syracuseStep 340967 = 511451) B511451
theorem B538055 : Blo 235815 538055 := bstep (se 1 (by rfl) ⟨403541, by rfl⟩ : syracuseStep 538055 = 807083) B807083
theorem B505531 : Blo 235815 505531 := bstep (se 1 (by rfl) ⟨379148, by rfl⟩ : syracuseStep 505531 = 758297) B758297
theorem B571115 : Blo 235815 571115 := bstep (se 1 (by rfl) ⟨428336, by rfl⟩ : syracuseStep 571115 = 856673) B856673
theorem B505607 : Blo 235815 505607 := bstep (se 1 (by rfl) ⟨379205, by rfl⟩ : syracuseStep 505607 = 758411) B758411
theorem B538415 : Blo 235815 538415 := bstep (se 1 (by rfl) ⟨403811, by rfl⟩ : syracuseStep 538415 = 807623) B807623
theorem B604169 : Blo 235815 604169 := bstep (se 2 (by rfl) ⟨226563, by rfl⟩ : syracuseStep 604169 = 453127) B453127
theorem B899207 : Blo 235815 899207 := bstep (se 1 (by rfl) ⟨674405, by rfl⟩ : syracuseStep 899207 = 1348811) B1348811
theorem B1194263 : Blo 235815 1194263 := bstep (se 1 (by rfl) ⟨895697, by rfl⟩ : syracuseStep 1194263 = 1791395) B1791395
theorem B571673 : Blo 235815 571673 := bstep (se 2 (by rfl) ⟨214377, by rfl⟩ : syracuseStep 571673 = 428755) B428755
theorem B604523 : Blo 235815 604523 := bstep (se 1 (by rfl) ⟨453392, by rfl⟩ : syracuseStep 604523 = 906785) B906785
theorem B538991 : Blo 235815 538991 := bstep (se 1 (by rfl) ⟨404243, by rfl⟩ : syracuseStep 538991 = 808487) B808487
theorem B899495 : Blo 235815 899495 := bstep (se 1 (by rfl) ⟨674621, by rfl⟩ : syracuseStep 899495 = 1349243) B1349243
theorem B539063 : Blo 235815 539063 := bstep (se 1 (by rfl) ⟨404297, by rfl⟩ : syracuseStep 539063 = 808595) B808595
theorem B539207 : Blo 235815 539207 := bstep (se 1 (by rfl) ⟨404405, by rfl⟩ : syracuseStep 539207 = 808811) B808811
theorem B801359 : Blo 235815 801359 := bstep (se 1 (by rfl) ⟨601019, by rfl⟩ : syracuseStep 801359 = 1202039) B1202039
theorem B539243 : Blo 235815 539243 := bstep (se 1 (by rfl) ⟨404432, by rfl⟩ : syracuseStep 539243 = 808865) B808865
theorem B604847 : Blo 235815 604847 := bstep (se 1 (by rfl) ⟨453635, by rfl⟩ : syracuseStep 604847 = 907271) B907271
theorem B7650125 : Blo 235815 7650125 := bstep (se 3 (by rfl) ⟨1434398, by rfl⟩ : syracuseStep 7650125 = 2868797) B2868797
theorem B4209515 : Blo 235815 4209515 := bstep (se 1 (by rfl) ⟨3157136, by rfl⟩ : syracuseStep 4209515 = 6314273) B6314273
theorem B900011 : Blo 235815 900011 := bstep (se 1 (by rfl) ⟨675008, by rfl⟩ : syracuseStep 900011 = 1350017) B1350017
theorem B1358765 : Blo 235815 1358765 := bstep (se 3 (by rfl) ⟨254768, by rfl⟩ : syracuseStep 1358765 = 509537) B509537
theorem B605171 : Blo 235815 605171 := bstep (se 1 (by rfl) ⟨453878, by rfl⟩ : syracuseStep 605171 = 907757) B907757
theorem B605627 : Blo 235815 605627 := bstep (se 1 (by rfl) ⟨454220, by rfl⟩ : syracuseStep 605627 = 908441) B908441
theorem B507487 : Blo 235815 507487 := bstep (se 1 (by rfl) ⟨380615, by rfl⟩ : syracuseStep 507487 = 761231) B761231
theorem B802601 : Blo 235815 802601 := bstep (se 2 (by rfl) ⟨300975, by rfl⟩ : syracuseStep 802601 = 601951) B601951
theorem B638777 : Blo 235815 638777 := bstep (se 2 (by rfl) ⟨239541, by rfl⟩ : syracuseStep 638777 = 479083) B479083
theorem B1195883 : Blo 235815 1195883 := bstep (se 1 (by rfl) ⟨896912, by rfl⟩ : syracuseStep 1195883 = 1793825) B1793825
theorem B541019 : Blo 235815 541019 := bstep (se 1 (by rfl) ⟨405764, by rfl⟩ : syracuseStep 541019 = 811529) B811529
theorem B672275 : Blo 235815 672275 := bstep (se 1 (by rfl) ⟨504206, by rfl⟩ : syracuseStep 672275 = 1008413) B1008413
theorem B901651 : Blo 235815 901651 := bstep (se 1 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 901651 = 1352477) B1352477
theorem B606791 : Blo 235815 606791 := bstep (se 1 (by rfl) ⟨455093, by rfl⟩ : syracuseStep 606791 = 910187) B910187
theorem B639823 : Blo 235815 639823 := bstep (se 1 (by rfl) ⟨479867, by rfl⟩ : syracuseStep 639823 = 959735) B959735
theorem B672731 : Blo 235815 672731 := bstep (se 1 (by rfl) ⟨504548, by rfl⟩ : syracuseStep 672731 = 1009097) B1009097
theorem B607355 : Blo 235815 607355 := bstep (se 1 (by rfl) ⟨455516, by rfl⟩ : syracuseStep 607355 = 911033) B911033
theorem B541895 : Blo 235815 541895 := bstep (se 1 (by rfl) ⟨406421, by rfl⟩ : syracuseStep 541895 = 812843) B812843
theorem B509161 : Blo 235815 509161 := bstep (se 2 (by rfl) ⟨190935, by rfl⟩ : syracuseStep 509161 = 381871) B381871
theorem B804815 : Blo 235815 804815 := bstep (se 1 (by rfl) ⟨603611, by rfl⟩ : syracuseStep 804815 = 1207223) B1207223
theorem B1624349 : Blo 235815 1624349 := bstep (se 3 (by rfl) ⟨304565, by rfl⟩ : syracuseStep 1624349 = 609131) B609131
theorem B510391 : Blo 235815 510391 := bstep (se 1 (by rfl) ⟨382793, by rfl⟩ : syracuseStep 510391 = 765587) B765587
theorem B379513 : Blo 235815 379513 := bstep (se 2 (by rfl) ⟨142317, by rfl⟩ : syracuseStep 379513 = 284635) B284635
theorem B2214611 : Blo 235815 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B42257173 : Blo 235815 42257173 := bstep (se 6 (by rfl) ⟨990402, by rfl⟩ : syracuseStep 42257173 = 1980805) B1980805
theorem B1526663 : Blo 235815 1526663 := bstep (se 1 (by rfl) ⟨1144997, by rfl⟩ : syracuseStep 1526663 = 2289995) B2289995
theorem B805787 : Blo 235815 805787 := bstep (se 1 (by rfl) ⟨604340, by rfl⟩ : syracuseStep 805787 = 1208681) B1208681
theorem B380123 : Blo 235815 380123 := bstep (se 1 (by rfl) ⟨285092, by rfl⟩ : syracuseStep 380123 = 570185) B570185
theorem B904567 : Blo 235815 904567 := bstep (se 1 (by rfl) ⟨678425, by rfl⟩ : syracuseStep 904567 = 1356851) B1356851
theorem B5459345 : Blo 235815 5459345 := bstep (se 2 (by rfl) ⟨2047254, by rfl⟩ : syracuseStep 5459345 = 4094509) B4094509
theorem B4050323 : Blo 235815 4050323 := bstep (se 1 (by rfl) ⟨3037742, by rfl⟩ : syracuseStep 4050323 = 6075485) B6075485
theorem B1199609 : Blo 235815 1199609 := bstep (se 2 (by rfl) ⟨449853, by rfl⟩ : syracuseStep 1199609 = 899707) B899707
theorem B511571 : Blo 235815 511571 := bstep (se 1 (by rfl) ⟨383678, by rfl⟩ : syracuseStep 511571 = 767357) B767357
theorem B511751 : Blo 235815 511751 := bstep (se 1 (by rfl) ⟨383813, by rfl⟩ : syracuseStep 511751 = 767627) B767627
theorem B1199933 : Blo 235815 1199933 := bstep (se 3 (by rfl) ⟨224987, by rfl⟩ : syracuseStep 1199933 = 449975) B449975
theorem B806813 : Blo 235815 806813 := bstep (se 3 (by rfl) ⟨151277, by rfl⟩ : syracuseStep 806813 = 302555) B302555
theorem B806921 : Blo 235815 806921 := bstep (se 2 (by rfl) ⟨302595, by rfl⟩ : syracuseStep 806921 = 605191) B605191
theorem B807259 : Blo 235815 807259 := bstep (se 1 (by rfl) ⟨605444, by rfl⟩ : syracuseStep 807259 = 1210889) B1210889
theorem B283439 : Blo 235815 283439 := bstep (se 1 (by rfl) ⟨212579, by rfl⟩ : syracuseStep 283439 = 425159) B425159
theorem B3494735 : Blo 235815 3494735 := bstep (se 1 (by rfl) ⟨2621051, by rfl⟩ : syracuseStep 3494735 = 5242103) B5242103
theorem B51958745 : Blo 235815 51958745 := bstep (se 2 (by rfl) ⟨19484529, by rfl⟩ : syracuseStep 51958745 = 38969059) B38969059
theorem B644311 : Blo 235815 644311 := bstep (se 1 (by rfl) ⟨483233, by rfl⟩ : syracuseStep 644311 = 966467) B966467
theorem B283943 : Blo 235815 283943 := bstep (se 1 (by rfl) ⟨212957, by rfl⟩ : syracuseStep 283943 = 425915) B425915
theorem B611707 : Blo 235815 611707 := bstep (se 1 (by rfl) ⟨458780, by rfl⟩ : syracuseStep 611707 = 917561) B917561
theorem B7722503 : Blo 235815 7722503 := bstep (se 1 (by rfl) ⟨5791877, by rfl⟩ : syracuseStep 7722503 = 11583755) B11583755
theorem B1529381 : Blo 235815 1529381 := bstep (se 4 (by rfl) ⟨143379, by rfl⟩ : syracuseStep 1529381 = 286759) B286759
theorem B4085315 : Blo 235815 4085315 := bstep (se 1 (by rfl) ⟨3063986, by rfl⟩ : syracuseStep 4085315 = 6127973) B6127973
theorem B481231 : Blo 235815 481231 := bstep (se 1 (by rfl) ⟨360923, by rfl⟩ : syracuseStep 481231 = 721847) B721847
theorem B579689 : Blo 235815 579689 := bstep (se 2 (by rfl) ⟨217383, by rfl⟩ : syracuseStep 579689 = 434767) B434767
theorem B809327 : Blo 235815 809327 := bstep (se 1 (by rfl) ⟨606995, by rfl⟩ : syracuseStep 809327 = 1213991) B1213991
theorem B645815 : Blo 235815 645815 := bstep (se 1 (by rfl) ⟨484361, by rfl⟩ : syracuseStep 645815 = 968723) B968723
theorem B2284307 : Blo 235815 2284307 := bstep (se 1 (by rfl) ⟨1713230, by rfl⟩ : syracuseStep 2284307 = 3426461) B3426461
theorem B1203011 : Blo 235815 1203011 := bstep (se 1 (by rfl) ⟨902258, by rfl⟩ : syracuseStep 1203011 = 1804517) B1804517
theorem B1924013 : Blo 235815 1924013 := bstep (se 3 (by rfl) ⟨360752, by rfl⟩ : syracuseStep 1924013 = 721505) B721505
theorem B2317501 : Blo 235815 2317501 := bstep (se 3 (by rfl) ⟨434531, by rfl⟩ : syracuseStep 2317501 = 869063) B869063
theorem B908759 : Blo 235815 908759 := bstep (se 1 (by rfl) ⟨681569, by rfl⟩ : syracuseStep 908759 = 1363139) B1363139
theorem B1727993 : Blo 235815 1727993 := bstep (se 2 (by rfl) ⟨647997, by rfl⟩ : syracuseStep 1727993 = 1295995) B1295995
theorem B679519 : Blo 235815 679519 := bstep (se 1 (by rfl) ⟨509639, by rfl⟩ : syracuseStep 679519 = 1019279) B1019279
theorem B1203821 : Blo 235815 1203821 := bstep (se 3 (by rfl) ⟨225716, by rfl⟩ : syracuseStep 1203821 = 451433) B451433
theorem B286519 : Blo 235815 286519 := bstep (se 1 (by rfl) ⟨214889, by rfl⟩ : syracuseStep 286519 = 429779) B429779
theorem B2187137 : Blo 235815 2187137 := bstep (se 2 (by rfl) ⟨820176, by rfl⟩ : syracuseStep 2187137 = 1640353) B1640353
theorem B1400851 : Blo 235815 1400851 := bstep (se 1 (by rfl) ⟨1050638, by rfl⟩ : syracuseStep 1400851 = 2101277) B2101277
theorem B2187383 : Blo 235815 2187383 := bstep (se 1 (by rfl) ⟨1640537, by rfl⟩ : syracuseStep 2187383 = 3281075) B3281075
theorem B680147 : Blo 235815 680147 := bstep (se 1 (by rfl) ⟨510110, by rfl⟩ : syracuseStep 680147 = 1020221) B1020221
theorem B319783 : Blo 235815 319783 := bstep (se 1 (by rfl) ⟨239837, by rfl⟩ : syracuseStep 319783 = 479675) B479675
theorem B483695 : Blo 235815 483695 := bstep (se 1 (by rfl) ⟨362771, by rfl⟩ : syracuseStep 483695 = 725543) B725543
theorem B451145 : Blo 235815 451145 := bstep (se 2 (by rfl) ⟨169179, by rfl⟩ : syracuseStep 451145 = 338359) B338359
theorem B320107 : Blo 235815 320107 := bstep (se 1 (by rfl) ⟨240080, by rfl⟩ : syracuseStep 320107 = 480161) B480161
theorem B5530463 : Blo 235815 5530463 := bstep (se 1 (by rfl) ⟨4147847, by rfl⟩ : syracuseStep 5530463 = 8295695) B8295695
theorem B1631431 : Blo 235815 1631431 := bstep (se 1 (by rfl) ⟨1223573, by rfl⟩ : syracuseStep 1631431 = 2447147) B2447147
theorem B648425 : Blo 235815 648425 := bstep (se 2 (by rfl) ⟨243159, by rfl⟩ : syracuseStep 648425 = 486319) B486319
theorem B681311 : Blo 235815 681311 := bstep (se 1 (by rfl) ⟨510983, by rfl⟩ : syracuseStep 681311 = 1021967) B1021967
theorem B1140077 : Blo 235815 1140077 := bstep (se 3 (by rfl) ⟨213764, by rfl⟩ : syracuseStep 1140077 = 427529) B427529
theorem B353735 : Blo 235815 353735 := bstep (se 1 (by rfl) ⟨265301, by rfl⟩ : syracuseStep 353735 = 530603) B530603
theorem B255431 : Blo 235815 255431 := bstep (se 1 (by rfl) ⟨191573, by rfl⟩ : syracuseStep 255431 = 383147) B383147
theorem B681479 : Blo 235815 681479 := bstep (se 1 (by rfl) ⟨511109, by rfl⟩ : syracuseStep 681479 = 1022219) B1022219
theorem B354089 : Blo 235815 354089 := bstep (se 2 (by rfl) ⟨132783, by rfl⟩ : syracuseStep 354089 = 265567) B265567
theorem B354095 : Blo 235815 354095 := bstep (se 1 (by rfl) ⟨265571, by rfl⟩ : syracuseStep 354095 = 531143) B531143
theorem B354569 : Blo 235815 354569 := bstep (se 2 (by rfl) ⟨132963, by rfl⟩ : syracuseStep 354569 = 265927) B265927
theorem B354671 : Blo 235815 354671 := bstep (se 1 (by rfl) ⟨266003, by rfl⟩ : syracuseStep 354671 = 532007) B532007
theorem B453089 : Blo 235815 453089 := bstep (se 2 (by rfl) ⟨169908, by rfl⟩ : syracuseStep 453089 = 339817) B339817
theorem B354887 : Blo 235815 354887 := bstep (se 1 (by rfl) ⟨266165, by rfl⟩ : syracuseStep 354887 = 532331) B532331
theorem B354923 : Blo 235815 354923 := bstep (se 1 (by rfl) ⟨266192, by rfl⟩ : syracuseStep 354923 = 532385) B532385
theorem B355151 : Blo 235815 355151 := bstep (se 1 (by rfl) ⟨266363, by rfl⟩ : syracuseStep 355151 = 532727) B532727
theorem B13003697 : Blo 235815 13003697 := bstep (se 2 (by rfl) ⟨4876386, by rfl⟩ : syracuseStep 13003697 = 9752773) B9752773
theorem B2714795 : Blo 235815 2714795 := bstep (se 1 (by rfl) ⟨2036096, by rfl⟩ : syracuseStep 2714795 = 4072193) B4072193
theorem B355547 : Blo 235815 355547 := bstep (se 1 (by rfl) ⟨266660, by rfl⟩ : syracuseStep 355547 = 533321) B533321
theorem B355721 : Blo 235815 355721 := bstep (se 2 (by rfl) ⟨133395, by rfl⟩ : syracuseStep 355721 = 266791) B266791
theorem B978425 : Blo 235815 978425 := bstep (se 2 (by rfl) ⟨366909, by rfl⟩ : syracuseStep 978425 = 733819) B733819
theorem B356075 : Blo 235815 356075 := bstep (se 1 (by rfl) ⟨267056, by rfl⟩ : syracuseStep 356075 = 534113) B534113
theorem B4484845 : Blo 235815 4484845 := bstep (se 3 (by rfl) ⟨840908, by rfl⟩ : syracuseStep 4484845 = 1681817) B1681817
theorem B356303 : Blo 235815 356303 := bstep (se 1 (by rfl) ⟨267227, by rfl⟩ : syracuseStep 356303 = 534455) B534455
theorem B1044481 : Blo 235815 1044481 := bstep (se 2 (by rfl) ⟨391680, by rfl⟩ : syracuseStep 1044481 = 783361) B783361
theorem B356699 : Blo 235815 356699 := bstep (se 1 (by rfl) ⟨267524, by rfl⟩ : syracuseStep 356699 = 535049) B535049
theorem B356927 : Blo 235815 356927 := bstep (se 1 (by rfl) ⟨267695, by rfl⟩ : syracuseStep 356927 = 535391) B535391
theorem B357047 : Blo 235815 357047 := bstep (se 1 (by rfl) ⟨267785, by rfl⟩ : syracuseStep 357047 = 535571) B535571
theorem B1209167 : Blo 235815 1209167 := bstep (se 1 (by rfl) ⟨906875, by rfl⟩ : syracuseStep 1209167 = 1813751) B1813751
theorem B357275 : Blo 235815 357275 := bstep (se 1 (by rfl) ⟨267956, by rfl⟩ : syracuseStep 357275 = 535913) B535913
theorem B1209491 : Blo 235815 1209491 := bstep (se 1 (by rfl) ⟨907118, by rfl⟩ : syracuseStep 1209491 = 1814237) B1814237
theorem B1701121 : Blo 235815 1701121 := bstep (se 2 (by rfl) ⟨637920, by rfl⟩ : syracuseStep 1701121 = 1275841) B1275841
theorem B357671 : Blo 235815 357671 := bstep (se 1 (by rfl) ⟨268253, by rfl⟩ : syracuseStep 357671 = 536507) B536507
theorem B357755 : Blo 235815 357755 := bstep (se 1 (by rfl) ⟨268316, by rfl⟩ : syracuseStep 357755 = 536633) B536633
theorem B357881 : Blo 235815 357881 := bstep (se 2 (by rfl) ⟨134205, by rfl⟩ : syracuseStep 357881 = 268411) B268411
theorem B357983 : Blo 235815 357983 := bstep (se 1 (by rfl) ⟨268487, by rfl⟩ : syracuseStep 357983 = 536975) B536975
theorem B652961 : Blo 235815 652961 := bstep (se 2 (by rfl) ⟨244860, by rfl⟩ : syracuseStep 652961 = 489721) B489721
theorem B358199 : Blo 235815 358199 := bstep (se 1 (by rfl) ⟨268649, by rfl⟩ : syracuseStep 358199 = 537299) B537299
theorem B358505 : Blo 235815 358505 := bstep (se 2 (by rfl) ⟨134439, by rfl⟩ : syracuseStep 358505 = 268879) B268879
theorem B358823 : Blo 235815 358823 := bstep (se 1 (by rfl) ⟨269117, by rfl⟩ : syracuseStep 358823 = 538235) B538235
theorem B358907 : Blo 235815 358907 := bstep (se 1 (by rfl) ⟨269180, by rfl⟩ : syracuseStep 358907 = 538361) B538361
theorem B12909131 : Blo 235815 12909131 := bstep (se 1 (by rfl) ⟨9681848, by rfl⟩ : syracuseStep 12909131 = 19363697) B19363697
theorem B359033 : Blo 235815 359033 := bstep (se 2 (by rfl) ⟨134637, by rfl⟩ : syracuseStep 359033 = 269275) B269275
theorem B359087 : Blo 235815 359087 := bstep (se 1 (by rfl) ⟨269315, by rfl⟩ : syracuseStep 359087 = 538631) B538631
theorem B359135 : Blo 235815 359135 := bstep (se 1 (by rfl) ⟨269351, by rfl⟩ : syracuseStep 359135 = 538703) B538703
theorem B1801115 : Blo 235815 1801115 := bstep (se 1 (by rfl) ⟨1350836, by rfl⟩ : syracuseStep 1801115 = 2701673) B2701673
theorem B1276859 : Blo 235815 1276859 := bstep (se 1 (by rfl) ⟨957644, by rfl⟩ : syracuseStep 1276859 = 1915289) B1915289
theorem B359399 : Blo 235815 359399 := bstep (se 1 (by rfl) ⟨269549, by rfl⟩ : syracuseStep 359399 = 539099) B539099
theorem B359657 : Blo 235815 359657 := bstep (se 2 (by rfl) ⟨134871, by rfl⟩ : syracuseStep 359657 = 269743) B269743
theorem B359711 : Blo 235815 359711 := bstep (se 1 (by rfl) ⟨269783, by rfl⟩ : syracuseStep 359711 = 539567) B539567
theorem B1146383 : Blo 235815 1146383 := bstep (se 1 (by rfl) ⟨859787, by rfl⟩ : syracuseStep 1146383 = 1719575) B1719575
theorem B1080857 : Blo 235815 1080857 := bstep (se 2 (by rfl) ⟨405321, by rfl⟩ : syracuseStep 1080857 = 810643) B810643
theorem B2293343 : Blo 235815 2293343 := bstep (se 1 (by rfl) ⟨1720007, by rfl⟩ : syracuseStep 2293343 = 3440015) B3440015
theorem B1867801 : Blo 235815 1867801 := bstep (se 2 (by rfl) ⟨700425, by rfl⟩ : syracuseStep 1867801 = 1400851) B1400851
theorem B20709593 : Blo 235815 20709593 := bstep (se 2 (by rfl) ⟨7766097, by rfl⟩ : syracuseStep 20709593 = 15532195) B15532195
theorem B3244313 : Blo 235815 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B5833021 : Blo 235815 5833021 := bstep (se 3 (by rfl) ⟨1093691, by rfl⟩ : syracuseStep 5833021 = 2187383) B2187383
theorem B426377 : Blo 235815 426377 := bstep (se 2 (by rfl) ⟨159891, by rfl⟩ : syracuseStep 426377 = 319783) B319783
theorem B852407 : Blo 235815 852407 := bstep (se 1 (by rfl) ⟨639305, by rfl⟩ : syracuseStep 852407 = 1278611) B1278611
theorem B426809 : Blo 235815 426809 := bstep (se 2 (by rfl) ⟨160053, by rfl⟩ : syracuseStep 426809 = 320107) B320107
theorem B1442717 : Blo 235815 1442717 := bstep (se 3 (by rfl) ⟨270509, by rfl⟩ : syracuseStep 1442717 = 541019) B541019
theorem B5178269 : Blo 235815 5178269 := bstep (se 3 (by rfl) ⟨970925, by rfl⟩ : syracuseStep 5178269 = 1941851) B1941851
theorem B853097 : Blo 235815 853097 := bstep (se 2 (by rfl) ⟨319911, by rfl⟩ : syracuseStep 853097 = 639823) B639823
theorem B1017161 : Blo 235815 1017161 := bstep (se 2 (by rfl) ⟨381435, by rfl⟩ : syracuseStep 1017161 = 762871) B762871
theorem B1082899 : Blo 235815 1082899 := bstep (se 1 (by rfl) ⟨812174, by rfl⟩ : syracuseStep 1082899 = 1624349) B1624349
theorem B722515 : Blo 235815 722515 := bstep (se 1 (by rfl) ⟨541886, by rfl⟩ : syracuseStep 722515 = 1083773) B1083773
theorem B1476407 : Blo 235815 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B1017775 : Blo 235815 1017775 := bstep (se 1 (by rfl) ⟨763331, by rfl⟩ : syracuseStep 1017775 = 1526663) B1526663
theorem B755837 : Blo 235815 755837 := bstep (se 3 (by rfl) ⟨141719, by rfl⟩ : syracuseStep 755837 = 283439) B283439
theorem B3639563 : Blo 235815 3639563 := bstep (se 1 (by rfl) ⟨2729672, by rfl⟩ : syracuseStep 3639563 = 5459345) B5459345
theorem B2722085 : Blo 235815 2722085 := bstep (se 4 (by rfl) ⟨255195, by rfl⟩ : syracuseStep 2722085 = 510391) B510391
theorem B1313063 : Blo 235815 1313063 := bstep (se 1 (by rfl) ⟨984797, by rfl⟩ : syracuseStep 1313063 = 1969595) B1969595
theorem B1968745 : Blo 235815 1968745 := bstep (se 2 (by rfl) ⟨738279, by rfl⟩ : syracuseStep 1968745 = 1476559) B1476559
theorem B1706771 : Blo 235815 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B3279953 : Blo 235815 3279953 := bstep (se 2 (by rfl) ⟨1229982, by rfl⟩ : syracuseStep 3279953 = 2459965) B2459965
theorem B1445053 : Blo 235815 1445053 := bstep (se 3 (by rfl) ⟨270947, by rfl⟩ : syracuseStep 1445053 = 541895) B541895
theorem B2329823 : Blo 235815 2329823 := bstep (se 1 (by rfl) ⟨1747367, by rfl⟩ : syracuseStep 2329823 = 3494735) B3494735
theorem B34639163 : Blo 235815 34639163 := bstep (se 1 (by rfl) ⟨25979372, by rfl⟩ : syracuseStep 34639163 = 51958745) B51958745
theorem B757181 : Blo 235815 757181 := bstep (se 3 (by rfl) ⟨141971, by rfl⟩ : syracuseStep 757181 = 283943) B283943
theorem B265819 : Blo 235815 265819 := bstep (se 1 (by rfl) ⟨199364, by rfl⟩ : syracuseStep 265819 = 398729) B398729
theorem B5148335 : Blo 235815 5148335 := bstep (se 1 (by rfl) ⟨3861251, by rfl⟩ : syracuseStep 5148335 = 7722503) B7722503
theorem B1019587 : Blo 235815 1019587 := bstep (se 1 (by rfl) ⟨764690, by rfl⟩ : syracuseStep 1019587 = 1529381) B1529381
theorem B2723543 : Blo 235815 2723543 := bstep (se 1 (by rfl) ⟨2042657, by rfl⟩ : syracuseStep 2723543 = 4085315) B4085315
theorem B1150841 : Blo 235815 1150841 := bstep (se 2 (by rfl) ⟨431565, by rfl⟩ : syracuseStep 1150841 = 863131) B863131
theorem B266107 : Blo 235815 266107 := bstep (se 1 (by rfl) ⟨199580, by rfl⟩ : syracuseStep 266107 = 399161) B399161
theorem B430543 : Blo 235815 430543 := bstep (se 1 (by rfl) ⟨322907, by rfl⟩ : syracuseStep 430543 = 645815) B645815
theorem B1380959 : Blo 235815 1380959 := bstep (se 1 (by rfl) ⟨1035719, by rfl⟩ : syracuseStep 1380959 = 2071439) B2071439
theorem B1348285 : Blo 235815 1348285 := bstep (se 3 (by rfl) ⟨252803, by rfl⟩ : syracuseStep 1348285 = 505607) B505607
theorem B267259 : Blo 235815 267259 := bstep (se 1 (by rfl) ⟨200444, by rfl⟩ : syracuseStep 267259 = 400889) B400889
theorem B1151995 : Blo 235815 1151995 := bstep (se 1 (by rfl) ⟨863996, by rfl⟩ : syracuseStep 1151995 = 1727993) B1727993
theorem B267439 : Blo 235815 267439 := bstep (se 1 (by rfl) ⟨200579, by rfl⟩ : syracuseStep 267439 = 401159) B401159
theorem B267943 : Blo 235815 267943 := bstep (se 1 (by rfl) ⟨200957, by rfl⟩ : syracuseStep 267943 = 401915) B401915
theorem B300763 : Blo 235815 300763 := bstep (se 1 (by rfl) ⟨225572, by rfl⟩ : syracuseStep 300763 = 451145) B451145
theorem B3413771 : Blo 235815 3413771 := bstep (se 1 (by rfl) ⟨2560328, by rfl⟩ : syracuseStep 3413771 = 5120657) B5120657
theorem B268231 : Blo 235815 268231 := bstep (se 1 (by rfl) ⟨201173, by rfl⟩ : syracuseStep 268231 = 402347) B402347
theorem B727003 : Blo 235815 727003 := bstep (se 1 (by rfl) ⟨545252, by rfl⟩ : syracuseStep 727003 = 1090505) B1090505
theorem B399343 : Blo 235815 399343 := bstep (se 1 (by rfl) ⟨299507, by rfl⟩ : syracuseStep 399343 = 599015) B599015
theorem B399593 : Blo 235815 399593 := bstep (se 2 (by rfl) ⟨149847, by rfl⟩ : syracuseStep 399593 = 299695) B299695
theorem B760051 : Blo 235815 760051 := bstep (se 1 (by rfl) ⟨570038, by rfl⟩ : syracuseStep 760051 = 1140077) B1140077
theorem B530729 : Blo 235815 530729 := bstep (se 2 (by rfl) ⟨199023, by rfl⟩ : syracuseStep 530729 = 398047) B398047
theorem B235823 : Blo 235815 235823 := bstep (se 1 (by rfl) ⟨176867, by rfl⟩ : syracuseStep 235823 = 353735) B353735
theorem B268591 : Blo 235815 268591 := bstep (se 1 (by rfl) ⟨201443, by rfl⟩ : syracuseStep 268591 = 402887) B402887
theorem B89332109 : Blo 235815 89332109 := bstep (se 3 (by rfl) ⟨16749770, by rfl⟩ : syracuseStep 89332109 = 33499541) B33499541
theorem B236059 : Blo 235815 236059 := bstep (se 1 (by rfl) ⟨177044, by rfl⟩ : syracuseStep 236059 = 354089) B354089
theorem B236063 : Blo 235815 236063 := bstep (se 1 (by rfl) ⟨177047, by rfl⟩ : syracuseStep 236063 = 354095) B354095
theorem B236379 : Blo 235815 236379 := bstep (se 1 (by rfl) ⟨177284, by rfl⟩ : syracuseStep 236379 = 354569) B354569
theorem B531305 : Blo 235815 531305 := bstep (se 2 (by rfl) ⟨199239, by rfl⟩ : syracuseStep 531305 = 398479) B398479
theorem B531359 : Blo 235815 531359 := bstep (se 1 (by rfl) ⟨398519, by rfl⟩ : syracuseStep 531359 = 797039) B797039
theorem B236447 : Blo 235815 236447 := bstep (se 1 (by rfl) ⟨177335, by rfl⟩ : syracuseStep 236447 = 354671) B354671
theorem B859081 : Blo 235815 859081 := bstep (se 2 (by rfl) ⟨322155, by rfl⟩ : syracuseStep 859081 = 644311) B644311
theorem B302059 : Blo 235815 302059 := bstep (se 1 (by rfl) ⟨226544, by rfl⟩ : syracuseStep 302059 = 453089) B453089
theorem B2268161 : Blo 235815 2268161 := bstep (se 2 (by rfl) ⟨850560, by rfl⟩ : syracuseStep 2268161 = 1701121) B1701121
theorem B236591 : Blo 235815 236591 := bstep (se 1 (by rfl) ⟨177443, by rfl⟩ : syracuseStep 236591 = 354887) B354887
theorem B236615 : Blo 235815 236615 := bstep (se 1 (by rfl) ⟨177461, by rfl⟩ : syracuseStep 236615 = 354923) B354923
theorem B269383 : Blo 235815 269383 := bstep (se 1 (by rfl) ⟨202037, by rfl⟩ : syracuseStep 269383 = 404075) B404075
theorem B236767 : Blo 235815 236767 := bstep (se 1 (by rfl) ⟨177575, by rfl⟩ : syracuseStep 236767 = 355151) B355151
theorem B6495623 : Blo 235815 6495623 := bstep (se 1 (by rfl) ⟨4871717, by rfl⟩ : syracuseStep 6495623 = 9743435) B9743435
theorem B597415 : Blo 235815 597415 := bstep (se 1 (by rfl) ⟨448061, by rfl⟩ : syracuseStep 597415 = 896123) B896123
theorem B1809863 : Blo 235815 1809863 := bstep (se 1 (by rfl) ⟨1357397, by rfl⟩ : syracuseStep 1809863 = 2714795) B2714795
theorem B237031 : Blo 235815 237031 := bstep (se 1 (by rfl) ⟨177773, by rfl⟩ : syracuseStep 237031 = 355547) B355547
theorem B237147 : Blo 235815 237147 := bstep (se 1 (by rfl) ⟨177860, by rfl⟩ : syracuseStep 237147 = 355721) B355721
theorem B401071 : Blo 235815 401071 := bstep (se 1 (by rfl) ⟨300803, by rfl⟩ : syracuseStep 401071 = 601607) B601607
theorem B34676525 : Blo 235815 34676525 := bstep (se 3 (by rfl) ⟨6501848, by rfl⟩ : syracuseStep 34676525 = 13003697) B13003697
theorem B532295 : Blo 235815 532295 := bstep (se 1 (by rfl) ⟨399221, by rfl⟩ : syracuseStep 532295 = 798443) B798443
theorem B237383 : Blo 235815 237383 := bstep (se 1 (by rfl) ⟨178037, by rfl⟩ : syracuseStep 237383 = 356075) B356075
theorem B237535 : Blo 235815 237535 := bstep (se 1 (by rfl) ⟨178151, by rfl⟩ : syracuseStep 237535 = 356303) B356303
theorem B401375 : Blo 235815 401375 := bstep (se 1 (by rfl) ⟨301031, by rfl⟩ : syracuseStep 401375 = 602063) B602063
theorem B237799 : Blo 235815 237799 := bstep (se 1 (by rfl) ⟨178349, by rfl⟩ : syracuseStep 237799 = 356699) B356699
theorem B401719 : Blo 235815 401719 := bstep (se 1 (by rfl) ⟨301289, by rfl⟩ : syracuseStep 401719 = 602579) B602579
theorem B5775731 : Blo 235815 5775731 := bstep (se 1 (by rfl) ⟨4331798, by rfl⟩ : syracuseStep 5775731 = 8663597) B8663597
theorem B237951 : Blo 235815 237951 := bstep (se 1 (by rfl) ⟨178463, by rfl⟩ : syracuseStep 237951 = 356927) B356927
theorem B532943 : Blo 235815 532943 := bstep (se 1 (by rfl) ⟨399707, by rfl⟩ : syracuseStep 532943 = 799415) B799415
theorem B238031 : Blo 235815 238031 := bstep (se 1 (by rfl) ⟨178523, by rfl⟩ : syracuseStep 238031 = 357047) B357047
theorem B336479 : Blo 235815 336479 := bstep (se 1 (by rfl) ⟨252359, by rfl⟩ : syracuseStep 336479 = 504719) B504719
theorem B238183 : Blo 235815 238183 := bstep (se 1 (by rfl) ⟨178637, by rfl⟩ : syracuseStep 238183 = 357275) B357275
theorem B402023 : Blo 235815 402023 := bstep (se 1 (by rfl) ⟨301517, by rfl⟩ : syracuseStep 402023 = 603035) B603035
theorem B402185 : Blo 235815 402185 := bstep (se 2 (by rfl) ⟨150819, by rfl⟩ : syracuseStep 402185 = 301639) B301639
theorem B238447 : Blo 235815 238447 := bstep (se 1 (by rfl) ⟨178835, by rfl⟩ : syracuseStep 238447 = 357671) B357671
theorem B238503 : Blo 235815 238503 := bstep (se 1 (by rfl) ⟨178877, by rfl⟩ : syracuseStep 238503 = 357755) B357755
theorem B238587 : Blo 235815 238587 := bstep (se 1 (by rfl) ⟨178940, by rfl⟩ : syracuseStep 238587 = 357881) B357881
theorem B238655 : Blo 235815 238655 := bstep (se 1 (by rfl) ⟨178991, by rfl⟩ : syracuseStep 238655 = 357983) B357983
theorem B533609 : Blo 235815 533609 := bstep (se 2 (by rfl) ⟨200103, by rfl⟩ : syracuseStep 533609 = 400207) B400207
theorem B435307 : Blo 235815 435307 := bstep (se 1 (by rfl) ⟨326480, by rfl⟩ : syracuseStep 435307 = 652961) B652961
theorem B238799 : Blo 235815 238799 := bstep (se 1 (by rfl) ⟨179099, by rfl⟩ : syracuseStep 238799 = 358199) B358199
theorem B402779 : Blo 235815 402779 := bstep (se 1 (by rfl) ⟨302084, by rfl⟩ : syracuseStep 402779 = 604169) B604169
theorem B239003 : Blo 235815 239003 := bstep (se 1 (by rfl) ⟨179252, by rfl⟩ : syracuseStep 239003 = 358505) B358505
theorem B599471 : Blo 235815 599471 := bstep (se 1 (by rfl) ⟨449603, by rfl⟩ : syracuseStep 599471 = 899207) B899207
theorem B796175 : Blo 235815 796175 := bstep (se 1 (by rfl) ⟨597131, by rfl⟩ : syracuseStep 796175 = 1194263) B1194263
theorem B403015 : Blo 235815 403015 := bstep (se 1 (by rfl) ⟨302261, by rfl⟩ : syracuseStep 403015 = 604523) B604523
theorem B3090001 : Blo 235815 3090001 := bstep (se 2 (by rfl) ⟨1158750, by rfl⟩ : syracuseStep 3090001 = 2317501) B2317501
theorem B599663 : Blo 235815 599663 := bstep (se 1 (by rfl) ⟨449747, by rfl⟩ : syracuseStep 599663 = 899495) B899495
theorem B239215 : Blo 235815 239215 := bstep (se 1 (by rfl) ⟨179411, by rfl⟩ : syracuseStep 239215 = 358823) B358823
theorem B239271 : Blo 235815 239271 := bstep (se 1 (by rfl) ⟨179453, by rfl⟩ : syracuseStep 239271 = 358907) B358907
theorem B534239 : Blo 235815 534239 := bstep (se 1 (by rfl) ⟨400679, by rfl⟩ : syracuseStep 534239 = 801359) B801359
theorem B239355 : Blo 235815 239355 := bstep (se 1 (by rfl) ⟨179516, by rfl⟩ : syracuseStep 239355 = 359033) B359033
theorem B403231 : Blo 235815 403231 := bstep (se 1 (by rfl) ⟨302423, by rfl⟩ : syracuseStep 403231 = 604847) B604847
theorem B239391 : Blo 235815 239391 := bstep (se 1 (by rfl) ⟨179543, by rfl⟩ : syracuseStep 239391 = 359087) B359087
theorem B239423 : Blo 235815 239423 := bstep (se 1 (by rfl) ⟨179567, by rfl⟩ : syracuseStep 239423 = 359135) B359135
theorem B600007 : Blo 235815 600007 := bstep (se 1 (by rfl) ⟨450005, by rfl⟩ : syracuseStep 600007 = 900011) B900011
theorem B239599 : Blo 235815 239599 := bstep (se 1 (by rfl) ⟨179699, by rfl⟩ : syracuseStep 239599 = 359399) B359399
theorem B403447 : Blo 235815 403447 := bstep (se 1 (by rfl) ⟨302585, by rfl⟩ : syracuseStep 403447 = 605171) B605171
theorem B239771 : Blo 235815 239771 := bstep (se 1 (by rfl) ⟨179828, by rfl⟩ : syracuseStep 239771 = 359657) B359657
theorem B239807 : Blo 235815 239807 := bstep (se 1 (by rfl) ⟨179855, by rfl⟩ : syracuseStep 239807 = 359711) B359711
theorem B403751 : Blo 235815 403751 := bstep (se 1 (by rfl) ⟨302813, by rfl⟩ : syracuseStep 403751 = 605627) B605627
theorem B796985 : Blo 235815 796985 := bstep (se 2 (by rfl) ⟨298869, by rfl⟩ : syracuseStep 796985 = 597739) B597739
theorem B764255 : Blo 235815 764255 := bstep (se 1 (by rfl) ⟨573191, by rfl⟩ : syracuseStep 764255 = 1146383) B1146383
theorem B1452545 : Blo 235815 1452545 := bstep (se 2 (by rfl) ⟨544704, by rfl⟩ : syracuseStep 1452545 = 1089409) B1089409
theorem B535067 : Blo 235815 535067 := bstep (se 1 (by rfl) ⟨401300, by rfl⟩ : syracuseStep 535067 = 802601) B802601
theorem B797255 : Blo 235815 797255 := bstep (se 1 (by rfl) ⟨597941, by rfl⟩ : syracuseStep 797255 = 1195883) B1195883
theorem B404527 : Blo 235815 404527 := bstep (se 1 (by rfl) ⟨303395, by rfl⟩ : syracuseStep 404527 = 606791) B606791
theorem B404903 : Blo 235815 404903 := bstep (se 1 (by rfl) ⟨303677, by rfl⟩ : syracuseStep 404903 = 607355) B607355
theorem B798281 : Blo 235815 798281 := bstep (se 2 (by rfl) ⟨299355, by rfl⟩ : syracuseStep 798281 = 598711) B598711
theorem B536543 : Blo 235815 536543 := bstep (se 1 (by rfl) ⟨402407, by rfl⟩ : syracuseStep 536543 = 804815) B804815
theorem B6467597 : Blo 235815 6467597 := bstep (se 3 (by rfl) ⟨1212674, by rfl⟩ : syracuseStep 6467597 = 2425349) B2425349
theorem B897551 : Blo 235815 897551 := bstep (se 1 (by rfl) ⟨673163, by rfl⟩ : syracuseStep 897551 = 1346327) B1346327
theorem B537191 : Blo 235815 537191 := bstep (se 1 (by rfl) ⟨402893, by rfl⟩ : syracuseStep 537191 = 805787) B805787
theorem B2700215 : Blo 235815 2700215 := bstep (se 1 (by rfl) ⟨2025161, by rfl⟩ : syracuseStep 2700215 = 4050323) B4050323
theorem B799739 : Blo 235815 799739 := bstep (se 1 (by rfl) ⟨599804, by rfl⟩ : syracuseStep 799739 = 1199609) B1199609
theorem B341047 : Blo 235815 341047 := bstep (se 1 (by rfl) ⟨255785, by rfl⟩ : syracuseStep 341047 = 511571) B511571
theorem B341167 : Blo 235815 341167 := bstep (se 1 (by rfl) ⟨255875, by rfl⟩ : syracuseStep 341167 = 511751) B511751
theorem B799955 : Blo 235815 799955 := bstep (se 1 (by rfl) ⟨599966, by rfl⟩ : syracuseStep 799955 = 1199933) B1199933
theorem B537875 : Blo 235815 537875 := bstep (se 1 (by rfl) ⟨403406, by rfl⟩ : syracuseStep 537875 = 806813) B806813
theorem B537947 : Blo 235815 537947 := bstep (se 1 (by rfl) ⟨403460, by rfl⟩ : syracuseStep 537947 = 806921) B806921
theorem B800225 : Blo 235815 800225 := bstep (se 2 (by rfl) ⟨300084, by rfl⟩ : syracuseStep 800225 = 600169) B600169
theorem B538505 : Blo 235815 538505 := bstep (se 2 (by rfl) ⟨201939, by rfl⟩ : syracuseStep 538505 = 403879) B403879
theorem B538721 : Blo 235815 538721 := bstep (se 2 (by rfl) ⟨202020, by rfl⟩ : syracuseStep 538721 = 404041) B404041
theorem B800873 : Blo 235815 800873 := bstep (se 2 (by rfl) ⟨300327, by rfl⟩ : syracuseStep 800873 = 600655) B600655
theorem B506017 : Blo 235815 506017 := bstep (se 2 (by rfl) ⟨189756, by rfl⟩ : syracuseStep 506017 = 379513) B379513
theorem B1816829 : Blo 235815 1816829 := bstep (se 3 (by rfl) ⟨340655, by rfl⟩ : syracuseStep 1816829 = 681311) B681311
theorem B56342897 : Blo 235815 56342897 := bstep (se 2 (by rfl) ⟨21128586, by rfl⟩ : syracuseStep 56342897 = 42257173) B42257173
theorem B571961 : Blo 235815 571961 := bstep (se 2 (by rfl) ⟨214485, by rfl⟩ : syracuseStep 571961 = 428971) B428971
theorem B539551 : Blo 235815 539551 := bstep (se 1 (by rfl) ⟨404663, by rfl⟩ : syracuseStep 539551 = 809327) B809327
theorem B801737 : Blo 235815 801737 := bstep (se 2 (by rfl) ⟨300651, by rfl⟩ : syracuseStep 801737 = 601303) B601303
theorem B1817639 : Blo 235815 1817639 := bstep (se 1 (by rfl) ⟨1363229, by rfl⟩ : syracuseStep 1817639 = 2726459) B2726459
theorem B1522871 : Blo 235815 1522871 := bstep (se 1 (by rfl) ⟨1142153, by rfl⟩ : syracuseStep 1522871 = 2284307) B2284307
theorem B802007 : Blo 235815 802007 := bstep (se 1 (by rfl) ⟨601505, by rfl⟩ : syracuseStep 802007 = 1203011) B1203011
theorem B966287 : Blo 235815 966287 := bstep (se 1 (by rfl) ⟨724715, by rfl⟩ : syracuseStep 966287 = 1449431) B1449431
theorem B605839 : Blo 235815 605839 := bstep (se 1 (by rfl) ⟨454379, by rfl⟩ : syracuseStep 605839 = 908759) B908759
theorem B5979793 : Blo 235815 5979793 := bstep (se 2 (by rfl) ⟨2242422, by rfl⟩ : syracuseStep 5979793 = 4484845) B4484845
theorem B802547 : Blo 235815 802547 := bstep (se 1 (by rfl) ⟨601910, by rfl⟩ : syracuseStep 802547 = 1203821) B1203821
theorem B1458091 : Blo 235815 1458091 := bstep (se 1 (by rfl) ⟨1093568, by rfl⟩ : syracuseStep 1458091 = 2187137) B2187137
theorem B1392641 : Blo 235815 1392641 := bstep (se 2 (by rfl) ⟨522240, by rfl⟩ : syracuseStep 1392641 = 1044481) B1044481
theorem B3686975 : Blo 235815 3686975 := bstep (se 1 (by rfl) ⟨2765231, by rfl⟩ : syracuseStep 3686975 = 5530463) B5530463
theorem B8700965 : Blo 235815 8700965 := bstep (se 4 (by rfl) ⟨815715, by rfl⟩ : syracuseStep 8700965 = 1631431) B1631431
theorem B1230083 : Blo 235815 1230083 := bstep (se 1 (by rfl) ⟨922562, by rfl⟩ : syracuseStep 1230083 = 1845125) B1845125
theorem B1361225 : Blo 235815 1361225 := bstep (se 2 (by rfl) ⟨510459, by rfl⟩ : syracuseStep 1361225 = 1020919) B1020919
theorem B674041 : Blo 235815 674041 := bstep (se 2 (by rfl) ⟨252765, by rfl⟩ : syracuseStep 674041 = 505531) B505531
theorem B903581 : Blo 235815 903581 := bstep (se 3 (by rfl) ⟨169421, by rfl⟩ : syracuseStep 903581 = 338843) B338843
theorem B5130701 : Blo 235815 5130701 := bstep (se 3 (by rfl) ⟨962006, by rfl⟩ : syracuseStep 5130701 = 1924013) B1924013
theorem B641641 : Blo 235815 641641 := bstep (se 2 (by rfl) ⟨240615, by rfl⟩ : syracuseStep 641641 = 481231) B481231
theorem B806111 : Blo 235815 806111 := bstep (se 1 (by rfl) ⟨604583, by rfl⟩ : syracuseStep 806111 = 1209167) B1209167
theorem B806327 : Blo 235815 806327 := bstep (se 1 (by rfl) ⟨604745, by rfl⟩ : syracuseStep 806327 = 1209491) B1209491
theorem B1068701 : Blo 235815 1068701 := bstep (se 3 (by rfl) ⟨200381, by rfl⟩ : syracuseStep 1068701 = 400763) B400763
theorem B380743 : Blo 235815 380743 := bstep (se 1 (by rfl) ⟨285557, by rfl⟩ : syracuseStep 380743 = 571115) B571115
theorem B381115 : Blo 235815 381115 := bstep (se 1 (by rfl) ⟨285836, by rfl⟩ : syracuseStep 381115 = 571673) B571673
theorem B8606087 : Blo 235815 8606087 := bstep (se 1 (by rfl) ⟨6454565, by rfl⟩ : syracuseStep 8606087 = 12909131) B12909131
theorem B5100083 : Blo 235815 5100083 := bstep (se 1 (by rfl) ⟨3825062, by rfl⟩ : syracuseStep 5100083 = 7650125) B7650125
theorem B2806343 : Blo 235815 2806343 := bstep (se 1 (by rfl) ⟨2104757, by rfl⟩ : syracuseStep 2806343 = 4209515) B4209515
theorem B1200743 : Blo 235815 1200743 := bstep (se 1 (by rfl) ⟨900557, by rfl⟩ : syracuseStep 1200743 = 1801115) B1801115
theorem B905843 : Blo 235815 905843 := bstep (se 1 (by rfl) ⟨679382, by rfl⟩ : syracuseStep 905843 = 1358765) B1358765
theorem B676649 : Blo 235815 676649 := bstep (se 2 (by rfl) ⟨253743, by rfl⟩ : syracuseStep 676649 = 507487) B507487
theorem B906025 : Blo 235815 906025 := bstep (se 2 (by rfl) ⟨339759, by rfl⟩ : syracuseStep 906025 = 679519) B679519
theorem B1528895 : Blo 235815 1528895 := bstep (se 1 (by rfl) ⟨1146671, by rfl⟩ : syracuseStep 1528895 = 2293343) B2293343
theorem B382025 : Blo 235815 382025 := bstep (se 2 (by rfl) ⟨143259, by rfl⟩ : syracuseStep 382025 = 286519) B286519
theorem B808379 : Blo 235815 808379 := bstep (se 1 (by rfl) ⟨606284, by rfl⟩ : syracuseStep 808379 = 1212569) B1212569
theorem B677447 : Blo 235815 677447 := bstep (se 1 (by rfl) ⟨508085, by rfl⟩ : syracuseStep 677447 = 1016171) B1016171
theorem B448183 : Blo 235815 448183 := bstep (se 1 (by rfl) ⟨336137, by rfl⟩ : syracuseStep 448183 = 672275) B672275
theorem B808919 : Blo 235815 808919 := bstep (se 1 (by rfl) ⟨606689, by rfl⟩ : syracuseStep 808919 = 1213379) B1213379
theorem B448487 : Blo 235815 448487 := bstep (se 1 (by rfl) ⟨336365, by rfl⟩ : syracuseStep 448487 = 672731) B672731
theorem B1202201 : Blo 235815 1202201 := bstep (se 2 (by rfl) ⟨450825, by rfl⟩ : syracuseStep 1202201 = 901651) B901651
theorem B1366313 : Blo 235815 1366313 := bstep (se 2 (by rfl) ⟨512367, by rfl⟩ : syracuseStep 1366313 = 1024735) B1024735
theorem B482131 : Blo 235815 482131 := bstep (se 1 (by rfl) ⟨361598, by rfl⟩ : syracuseStep 482131 = 723197) B723197
theorem B678881 : Blo 235815 678881 := bstep (se 2 (by rfl) ⟨254580, by rfl⟩ : syracuseStep 678881 = 509161) B509161
theorem B1465559 : Blo 235815 1465559 := bstep (se 1 (by rfl) ⟨1099169, by rfl⟩ : syracuseStep 1465559 = 2198339) B2198339
theorem B253415 : Blo 235815 253415 := bstep (se 1 (by rfl) ⟨190061, by rfl⟩ : syracuseStep 253415 = 380123) B380123
theorem B909245 : Blo 235815 909245 := bstep (se 3 (by rfl) ⟨170483, by rfl⟩ : syracuseStep 909245 = 340967) B340967
theorem B1106273 : Blo 235815 1106273 := bstep (se 2 (by rfl) ⟨414852, by rfl⟩ : syracuseStep 1106273 = 829705) B829705
theorem B1729133 : Blo 235815 1729133 := bstep (se 3 (by rfl) ⟨324212, by rfl⟩ : syracuseStep 1729133 = 648425) B648425
theorem B1139309 : Blo 235815 1139309 := bstep (se 3 (by rfl) ⟨213620, by rfl⟩ : syracuseStep 1139309 = 427241) B427241
theorem B615215 : Blo 235815 615215 := bstep (se 1 (by rfl) ⟨461411, by rfl⟩ : syracuseStep 615215 = 922823) B922823
theorem B681149 : Blo 235815 681149 := bstep (se 3 (by rfl) ⟨127715, by rfl⟩ : syracuseStep 681149 = 255431) B255431
theorem B386459 : Blo 235815 386459 := bstep (se 1 (by rfl) ⟨289844, by rfl⟩ : syracuseStep 386459 = 579689) B579689
theorem B353903 : Blo 235815 353903 := bstep (se 1 (by rfl) ⟨265427, by rfl⟩ : syracuseStep 353903 = 530855) B530855
theorem B1205927 : Blo 235815 1205927 := bstep (se 1 (by rfl) ⟨904445, by rfl⟩ : syracuseStep 1205927 = 1808891) B1808891
theorem B353975 : Blo 235815 353975 := bstep (se 1 (by rfl) ⟨265481, by rfl⟩ : syracuseStep 353975 = 530963) B530963
theorem B354011 : Blo 235815 354011 := bstep (se 1 (by rfl) ⟨265508, by rfl⟩ : syracuseStep 354011 = 531017) B531017
theorem B1206089 : Blo 235815 1206089 := bstep (se 2 (by rfl) ⟨452283, by rfl⟩ : syracuseStep 1206089 = 904567) B904567
theorem B354185 : Blo 235815 354185 := bstep (se 2 (by rfl) ⟨132819, by rfl⟩ : syracuseStep 354185 = 265639) B265639
theorem B354287 : Blo 235815 354287 := bstep (se 1 (by rfl) ⟨265715, by rfl⟩ : syracuseStep 354287 = 531431) B531431
theorem B419831 : Blo 235815 419831 := bstep (se 1 (by rfl) ⟨314873, by rfl⟩ : syracuseStep 419831 = 629747) B629747
theorem B354539 : Blo 235815 354539 := bstep (se 1 (by rfl) ⟨265904, by rfl⟩ : syracuseStep 354539 = 531809) B531809
theorem B354599 : Blo 235815 354599 := bstep (se 1 (by rfl) ⟨265949, by rfl⟩ : syracuseStep 354599 = 531899) B531899
theorem B354683 : Blo 235815 354683 := bstep (se 1 (by rfl) ⟨266012, by rfl⟩ : syracuseStep 354683 = 532025) B532025
theorem B354953 : Blo 235815 354953 := bstep (se 2 (by rfl) ⟨133107, by rfl⟩ : syracuseStep 354953 = 266215) B266215
theorem B355127 : Blo 235815 355127 := bstep (se 1 (by rfl) ⟨266345, by rfl⟩ : syracuseStep 355127 = 532691) B532691
theorem B453431 : Blo 235815 453431 := bstep (se 1 (by rfl) ⟨340073, by rfl⟩ : syracuseStep 453431 = 680147) B680147
theorem B355163 : Blo 235815 355163 := bstep (se 1 (by rfl) ⟨266372, by rfl⟩ : syracuseStep 355163 = 532745) B532745
theorem B322463 : Blo 235815 322463 := bstep (se 1 (by rfl) ⟨241847, by rfl⟩ : syracuseStep 322463 = 483695) B483695
theorem B355307 : Blo 235815 355307 := bstep (se 1 (by rfl) ⟨266480, by rfl⟩ : syracuseStep 355307 = 532961) B532961
theorem B1076345 : Blo 235815 1076345 := bstep (se 2 (by rfl) ⟨403629, by rfl⟩ : syracuseStep 1076345 = 807259) B807259
theorem B355511 : Blo 235815 355511 := bstep (se 1 (by rfl) ⟨266633, by rfl⟩ : syracuseStep 355511 = 533267) B533267
theorem B1142059 : Blo 235815 1142059 := bstep (se 1 (by rfl) ⟨856544, by rfl⟩ : syracuseStep 1142059 = 1713089) B1713089
theorem B355751 : Blo 235815 355751 := bstep (se 1 (by rfl) ⟨266813, by rfl⟩ : syracuseStep 355751 = 533627) B533627
theorem B355835 : Blo 235815 355835 := bstep (se 1 (by rfl) ⟨266876, by rfl⟩ : syracuseStep 355835 = 533753) B533753
theorem B355931 : Blo 235815 355931 := bstep (se 1 (by rfl) ⟨266948, by rfl⟩ : syracuseStep 355931 = 533897) B533897
theorem B356015 : Blo 235815 356015 := bstep (se 1 (by rfl) ⟨267011, by rfl⟩ : syracuseStep 356015 = 534023) B534023
theorem B454319 : Blo 235815 454319 := bstep (se 1 (by rfl) ⟨340739, by rfl⟩ : syracuseStep 454319 = 681479) B681479
theorem B356135 : Blo 235815 356135 := bstep (se 1 (by rfl) ⟨267101, by rfl⟩ : syracuseStep 356135 = 534203) B534203
theorem B356219 : Blo 235815 356219 := bstep (se 1 (by rfl) ⟨267164, by rfl⟩ : syracuseStep 356219 = 534329) B534329
theorem B356639 : Blo 235815 356639 := bstep (se 1 (by rfl) ⟨267479, by rfl⟩ : syracuseStep 356639 = 534959) B534959
theorem B356663 : Blo 235815 356663 := bstep (se 1 (by rfl) ⟨267497, by rfl⟩ : syracuseStep 356663 = 534995) B534995
theorem B356735 : Blo 235815 356735 := bstep (se 1 (by rfl) ⟨267551, by rfl⟩ : syracuseStep 356735 = 535103) B535103
theorem B356807 : Blo 235815 356807 := bstep (se 1 (by rfl) ⟨267605, by rfl⟩ : syracuseStep 356807 = 535211) B535211
theorem B815609 : Blo 235815 815609 := bstep (se 2 (by rfl) ⟨305853, by rfl⟩ : syracuseStep 815609 = 611707) B611707
theorem B357161 : Blo 235815 357161 := bstep (se 2 (by rfl) ⟨133935, by rfl⟩ : syracuseStep 357161 = 267871) B267871
theorem B357167 : Blo 235815 357167 := bstep (se 1 (by rfl) ⟨267875, by rfl⟩ : syracuseStep 357167 = 535751) B535751
theorem B357287 : Blo 235815 357287 := bstep (se 1 (by rfl) ⟨267965, by rfl⟩ : syracuseStep 357287 = 535931) B535931
theorem B652283 : Blo 235815 652283 := bstep (se 1 (by rfl) ⟨489212, by rfl⟩ : syracuseStep 652283 = 978425) B978425
theorem B357371 : Blo 235815 357371 := bstep (se 1 (by rfl) ⟨268028, by rfl⟩ : syracuseStep 357371 = 536057) B536057
theorem B357431 : Blo 235815 357431 := bstep (se 1 (by rfl) ⟨268073, by rfl⟩ : syracuseStep 357431 = 536147) B536147
theorem B357551 : Blo 235815 357551 := bstep (se 1 (by rfl) ⟨268163, by rfl⟩ : syracuseStep 357551 = 536327) B536327
theorem B2028989 : Blo 235815 2028989 := bstep (se 3 (by rfl) ⟨380435, by rfl⟩ : syracuseStep 2028989 = 760871) B760871
theorem B1013249 : Blo 235815 1013249 := bstep (se 2 (by rfl) ⟨379968, by rfl⟩ : syracuseStep 1013249 = 759937) B759937
theorem B357959 : Blo 235815 357959 := bstep (se 1 (by rfl) ⟨268469, by rfl⟩ : syracuseStep 357959 = 536939) B536939
theorem B358055 : Blo 235815 358055 := bstep (se 1 (by rfl) ⟨268541, by rfl⟩ : syracuseStep 358055 = 537083) B537083
theorem B358139 : Blo 235815 358139 := bstep (se 1 (by rfl) ⟨268604, by rfl⟩ : syracuseStep 358139 = 537209) B537209
theorem B358175 : Blo 235815 358175 := bstep (se 1 (by rfl) ⟨268631, by rfl⟩ : syracuseStep 358175 = 537263) B537263
theorem B358223 : Blo 235815 358223 := bstep (se 1 (by rfl) ⟨268667, by rfl⟩ : syracuseStep 358223 = 537335) B537335
theorem B358343 : Blo 235815 358343 := bstep (se 1 (by rfl) ⟨268757, by rfl⟩ : syracuseStep 358343 = 537515) B537515
theorem B358697 : Blo 235815 358697 := bstep (se 2 (by rfl) ⟨134511, by rfl⟩ : syracuseStep 358697 = 269023) B269023
theorem B358703 : Blo 235815 358703 := bstep (se 1 (by rfl) ⟨269027, by rfl⟩ : syracuseStep 358703 = 538055) B538055
theorem B358943 : Blo 235815 358943 := bstep (se 1 (by rfl) ⟨269207, by rfl⟩ : syracuseStep 358943 = 538415) B538415
theorem B359327 : Blo 235815 359327 := bstep (se 1 (by rfl) ⟨269495, by rfl⟩ : syracuseStep 359327 = 538991) B538991
theorem B359375 : Blo 235815 359375 := bstep (se 1 (by rfl) ⟨269531, by rfl⟩ : syracuseStep 359375 = 539063) B539063
theorem B359465 : Blo 235815 359465 := bstep (se 2 (by rfl) ⟨134799, by rfl⟩ : syracuseStep 359465 = 269599) B269599
theorem B359471 : Blo 235815 359471 := bstep (se 1 (by rfl) ⟨269603, by rfl⟩ : syracuseStep 359471 = 539207) B539207
theorem B359495 : Blo 235815 359495 := bstep (se 1 (by rfl) ⟨269621, by rfl⟩ : syracuseStep 359495 = 539243) B539243
theorem B851239 : Blo 235815 851239 := bstep (se 1 (by rfl) ⟨638429, by rfl⟩ : syracuseStep 851239 = 1276859) B1276859
theorem B2719169 : Blo 235815 2719169 := bstep (se 2 (by rfl) ⟨1019688, by rfl⟩ : syracuseStep 2719169 = 2039377) B2039377
theorem B1703405 : Blo 235815 1703405 := bstep (se 3 (by rfl) ⟨319388, by rfl⟩ : syracuseStep 1703405 = 638777) B638777
theorem B720571 : Blo 235815 720571 := bstep (se 1 (by rfl) ⟨540428, by rfl⟩ : syracuseStep 720571 = 1080857) B1080857
theorem B2490401 : Blo 235815 2490401 := bstep (se 2 (by rfl) ⟨933900, by rfl⟩ : syracuseStep 2490401 = 1867801) B1867801
theorem B2162875 : Blo 235815 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B2457983 : Blo 235815 2457983 := bstep (se 1 (by rfl) ⟨1843487, by rfl⟩ : syracuseStep 2457983 = 3686975) B3686975
theorem B5800643 : Blo 235815 5800643 := bstep (se 1 (by rfl) ⟨4350482, by rfl⟩ : syracuseStep 5800643 = 8700965) B8700965
theorem B820055 : Blo 235815 820055 := bstep (se 1 (by rfl) ⟨615041, by rfl⟩ : syracuseStep 820055 = 1230083) B1230083
theorem B2032613 : Blo 235815 2032613 := bstep (se 4 (by rfl) ⟨190557, by rfl⟩ : syracuseStep 2032613 = 381115) B381115
theorem B2426375 : Blo 235815 2426375 := bstep (se 1 (by rfl) ⟨1819781, by rfl⟩ : syracuseStep 2426375 = 3639563) B3639563
theorem B1443865 : Blo 235815 1443865 := bstep (se 2 (by rfl) ⟨541449, by rfl⟩ : syracuseStep 1443865 = 1082899) B1082899
theorem B1640573 : Blo 235815 1640573 := bstep (se 3 (by rfl) ⟨307607, by rfl⟩ : syracuseStep 1640573 = 615215) B615215
theorem B5737391 : Blo 235815 5737391 := bstep (se 1 (by rfl) ⟨4303043, by rfl⟩ : syracuseStep 5737391 = 8606087) B8606087
theorem B1870895 : Blo 235815 1870895 := bstep (se 1 (by rfl) ⟨1403171, by rfl⟩ : syracuseStep 1870895 = 2806343) B2806343
theorem B920639 : Blo 235815 920639 := bstep (se 1 (by rfl) ⟨690479, by rfl⟩ : syracuseStep 920639 = 1380959) B1380959
theorem B1019263 : Blo 235815 1019263 := bstep (se 1 (by rfl) ⟨764447, by rfl⟩ : syracuseStep 1019263 = 1528895) B1528895
theorem B2624993 : Blo 235815 2624993 := bstep (se 2 (by rfl) ⟨984372, by rfl⟩ : syracuseStep 2624993 = 1968745) B1968745
theorem B855521 : Blo 235815 855521 := bstep (se 2 (by rfl) ⟨320820, by rfl⟩ : syracuseStep 855521 = 641641) B641641
theorem B298991 : Blo 235815 298991 := bstep (se 1 (by rfl) ⟨224243, by rfl⟩ : syracuseStep 298991 = 448487) B448487
theorem B266395 : Blo 235815 266395 := bstep (se 1 (by rfl) ⟨199796, by rfl⟩ : syracuseStep 266395 = 399593) B399593
theorem B1512107 : Blo 235815 1512107 := bstep (se 1 (by rfl) ⟨1134080, by rfl⟩ : syracuseStep 1512107 = 2268161) B2268161
theorem B3937085 : Blo 235815 3937085 := bstep (se 3 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 3937085 = 1476407) B1476407
theorem B4330415 : Blo 235815 4330415 := bstep (se 1 (by rfl) ⟨3247811, by rfl⟩ : syracuseStep 4330415 = 6495623) B6495623
theorem B267583 : Blo 235815 267583 := bstep (se 1 (by rfl) ⟨200687, by rfl⟩ : syracuseStep 267583 = 401375) B401375
theorem B268015 : Blo 235815 268015 := bstep (se 1 (by rfl) ⟨201011, by rfl⟩ : syracuseStep 268015 = 402023) B402023
theorem B1152755 : Blo 235815 1152755 := bstep (se 1 (by rfl) ⟨864566, by rfl⟩ : syracuseStep 1152755 = 1729133) B1729133
theorem B759539 : Blo 235815 759539 := bstep (se 1 (by rfl) ⟨569654, by rfl⟩ : syracuseStep 759539 = 1139309) B1139309
theorem B268123 : Blo 235815 268123 := bstep (se 1 (by rfl) ⟨201092, by rfl⟩ : syracuseStep 268123 = 402185) B402185
theorem B3643501 : Blo 235815 3643501 := bstep (se 3 (by rfl) ⟨683156, by rfl⟩ : syracuseStep 3643501 = 1366313) B1366313
theorem B268519 : Blo 235815 268519 := bstep (se 1 (by rfl) ⟨201389, by rfl⟩ : syracuseStep 268519 = 402779) B402779
theorem B399647 : Blo 235815 399647 := bstep (se 1 (by rfl) ⟨299735, by rfl⟩ : syracuseStep 399647 = 599471) B599471
theorem B530783 : Blo 235815 530783 := bstep (se 1 (by rfl) ⟨398087, by rfl⟩ : syracuseStep 530783 = 796175) B796175
theorem B235935 : Blo 235815 235935 := bstep (se 1 (by rfl) ⟨176951, by rfl⟩ : syracuseStep 235935 = 353903) B353903
theorem B399775 : Blo 235815 399775 := bstep (se 1 (by rfl) ⟨299831, by rfl⟩ : syracuseStep 399775 = 599663) B599663
theorem B235983 : Blo 235815 235983 := bstep (se 1 (by rfl) ⟨176987, by rfl⟩ : syracuseStep 235983 = 353975) B353975
theorem B236007 : Blo 235815 236007 := bstep (se 1 (by rfl) ⟨177005, by rfl⟩ : syracuseStep 236007 = 354011) B354011
theorem B236123 : Blo 235815 236123 := bstep (se 1 (by rfl) ⟨177092, by rfl⟩ : syracuseStep 236123 = 354185) B354185
theorem B236191 : Blo 235815 236191 := bstep (se 1 (by rfl) ⟨177143, by rfl⟩ : syracuseStep 236191 = 354287) B354287
theorem B236359 : Blo 235815 236359 := bstep (se 1 (by rfl) ⟨177269, by rfl⟩ : syracuseStep 236359 = 354539) B354539
theorem B236399 : Blo 235815 236399 := bstep (se 1 (by rfl) ⟨177299, by rfl⟩ : syracuseStep 236399 = 354599) B354599
theorem B269167 : Blo 235815 269167 := bstep (se 1 (by rfl) ⟨201875, by rfl⟩ : syracuseStep 269167 = 403751) B403751
theorem B531323 : Blo 235815 531323 := bstep (se 1 (by rfl) ⟨398492, by rfl⟩ : syracuseStep 531323 = 796985) B796985
theorem B236455 : Blo 235815 236455 := bstep (se 1 (by rfl) ⟨177341, by rfl⟩ : syracuseStep 236455 = 354683) B354683
theorem B531503 : Blo 235815 531503 := bstep (se 1 (by rfl) ⟨398627, by rfl⟩ : syracuseStep 531503 = 797255) B797255
theorem B236635 : Blo 235815 236635 := bstep (se 1 (by rfl) ⟨177476, by rfl⟩ : syracuseStep 236635 = 354953) B354953
theorem B236751 : Blo 235815 236751 := bstep (se 1 (by rfl) ⟨177563, by rfl⟩ : syracuseStep 236751 = 355127) B355127
theorem B302287 : Blo 235815 302287 := bstep (se 1 (by rfl) ⟨226715, by rfl⟩ : syracuseStep 302287 = 453431) B453431
theorem B236775 : Blo 235815 236775 := bstep (se 1 (by rfl) ⟨177581, by rfl⟩ : syracuseStep 236775 = 355163) B355163
theorem B236871 : Blo 235815 236871 := bstep (se 1 (by rfl) ⟨177653, by rfl⟩ : syracuseStep 236871 = 355307) B355307
theorem B237007 : Blo 235815 237007 := bstep (se 1 (by rfl) ⟨177755, by rfl⟩ : syracuseStep 237007 = 355511) B355511
theorem B597577 : Blo 235815 597577 := bstep (se 2 (by rfl) ⟨224091, by rfl⟩ : syracuseStep 597577 = 448183) B448183
theorem B269935 : Blo 235815 269935 := bstep (se 1 (by rfl) ⟨202451, by rfl⟩ : syracuseStep 269935 = 404903) B404903
theorem B237167 : Blo 235815 237167 := bstep (se 1 (by rfl) ⟨177875, by rfl⟩ : syracuseStep 237167 = 355751) B355751
theorem B401017 : Blo 235815 401017 := bstep (se 2 (by rfl) ⟨150381, by rfl⟩ : syracuseStep 401017 = 300763) B300763
theorem B237223 : Blo 235815 237223 := bstep (se 1 (by rfl) ⟨177917, by rfl⟩ : syracuseStep 237223 = 355835) B355835
theorem B532187 : Blo 235815 532187 := bstep (se 1 (by rfl) ⟨399140, by rfl⟩ : syracuseStep 532187 = 798281) B798281
theorem B237287 : Blo 235815 237287 := bstep (se 1 (by rfl) ⟨177965, by rfl⟩ : syracuseStep 237287 = 355931) B355931
theorem B859901 : Blo 235815 859901 := bstep (se 3 (by rfl) ⟨161231, by rfl⟩ : syracuseStep 859901 = 322463) B322463
theorem B237343 : Blo 235815 237343 := bstep (se 1 (by rfl) ⟨178007, by rfl⟩ : syracuseStep 237343 = 356015) B356015
theorem B302879 : Blo 235815 302879 := bstep (se 1 (by rfl) ⟨227159, by rfl⟩ : syracuseStep 302879 = 454319) B454319
theorem B237423 : Blo 235815 237423 := bstep (se 1 (by rfl) ⟨178067, by rfl⟩ : syracuseStep 237423 = 356135) B356135
theorem B237479 : Blo 235815 237479 := bstep (se 1 (by rfl) ⟨178109, by rfl⟩ : syracuseStep 237479 = 356219) B356219
theorem B1810349 : Blo 235815 1810349 := bstep (se 3 (by rfl) ⟨339440, by rfl⟩ : syracuseStep 1810349 = 678881) B678881
theorem B532457 : Blo 235815 532457 := bstep (se 2 (by rfl) ⟨199671, by rfl⟩ : syracuseStep 532457 = 399343) B399343
theorem B237759 : Blo 235815 237759 := bstep (se 1 (by rfl) ⟨178319, by rfl⟩ : syracuseStep 237759 = 356639) B356639
theorem B237775 : Blo 235815 237775 := bstep (se 1 (by rfl) ⟨178331, by rfl⟩ : syracuseStep 237775 = 356663) B356663
theorem B237823 : Blo 235815 237823 := bstep (se 1 (by rfl) ⟨178367, by rfl⟩ : syracuseStep 237823 = 356735) B356735
theorem B237871 : Blo 235815 237871 := bstep (se 1 (by rfl) ⟨178403, by rfl⟩ : syracuseStep 237871 = 356807) B356807
theorem B598367 : Blo 235815 598367 := bstep (se 1 (by rfl) ⟨448775, by rfl⟩ : syracuseStep 598367 = 897551) B897551
theorem B238107 : Blo 235815 238107 := bstep (se 1 (by rfl) ⟨178580, by rfl⟩ : syracuseStep 238107 = 357161) B357161
theorem B238111 : Blo 235815 238111 := bstep (se 1 (by rfl) ⟨178583, by rfl⟩ : syracuseStep 238111 = 357167) B357167
theorem B238191 : Blo 235815 238191 := bstep (se 1 (by rfl) ⟨178643, by rfl⟩ : syracuseStep 238191 = 357287) B357287
theorem B533159 : Blo 235815 533159 := bstep (se 1 (by rfl) ⟨399869, by rfl⟩ : syracuseStep 533159 = 799739) B799739
theorem B434855 : Blo 235815 434855 := bstep (se 1 (by rfl) ⟨326141, by rfl⟩ : syracuseStep 434855 = 652283) B652283
theorem B238247 : Blo 235815 238247 := bstep (se 1 (by rfl) ⟨178685, by rfl⟩ : syracuseStep 238247 = 357371) B357371
theorem B238287 : Blo 235815 238287 := bstep (se 1 (by rfl) ⟨178715, by rfl⟩ : syracuseStep 238287 = 357431) B357431
theorem B238367 : Blo 235815 238367 := bstep (se 1 (by rfl) ⟨178775, by rfl⟩ : syracuseStep 238367 = 357551) B357551
theorem B533303 : Blo 235815 533303 := bstep (se 1 (by rfl) ⟨399977, by rfl⟩ : syracuseStep 533303 = 799955) B799955
theorem B1352659 : Blo 235815 1352659 := bstep (se 1 (by rfl) ⟨1014494, by rfl⟩ : syracuseStep 1352659 = 2028989) B2028989
theorem B533483 : Blo 235815 533483 := bstep (se 1 (by rfl) ⟨400112, by rfl⟩ : syracuseStep 533483 = 800225) B800225
theorem B238639 : Blo 235815 238639 := bstep (se 1 (by rfl) ⟨178979, by rfl⟩ : syracuseStep 238639 = 357959) B357959
theorem B238703 : Blo 235815 238703 := bstep (se 1 (by rfl) ⟨179027, by rfl⟩ : syracuseStep 238703 = 358055) B358055
theorem B238759 : Blo 235815 238759 := bstep (se 1 (by rfl) ⟨179069, by rfl⟩ : syracuseStep 238759 = 358139) B358139
theorem B238783 : Blo 235815 238783 := bstep (se 1 (by rfl) ⟨179087, by rfl⟩ : syracuseStep 238783 = 358175) B358175
theorem B238815 : Blo 235815 238815 := bstep (se 1 (by rfl) ⟨179111, by rfl⟩ : syracuseStep 238815 = 358223) B358223
theorem B238895 : Blo 235815 238895 := bstep (se 1 (by rfl) ⟨179171, by rfl⟩ : syracuseStep 238895 = 358343) B358343
theorem B402745 : Blo 235815 402745 := bstep (se 2 (by rfl) ⟨151029, by rfl⟩ : syracuseStep 402745 = 302059) B302059
theorem B533915 : Blo 235815 533915 := bstep (se 1 (by rfl) ⟨400436, by rfl⟩ : syracuseStep 533915 = 800873) B800873
theorem B239131 : Blo 235815 239131 := bstep (se 1 (by rfl) ⟨179348, by rfl⟩ : syracuseStep 239131 = 358697) B358697
theorem B239135 : Blo 235815 239135 := bstep (se 1 (by rfl) ⟨179351, by rfl⟩ : syracuseStep 239135 = 358703) B358703
theorem B37561931 : Blo 235815 37561931 := bstep (se 1 (by rfl) ⟨28171448, by rfl⟩ : syracuseStep 37561931 = 56342897) B56342897
theorem B239295 : Blo 235815 239295 := bstep (se 1 (by rfl) ⟨179471, by rfl⟩ : syracuseStep 239295 = 358943) B358943
theorem B796553 : Blo 235815 796553 := bstep (se 2 (by rfl) ⟨298707, by rfl⟩ : syracuseStep 796553 = 597415) B597415
theorem B239551 : Blo 235815 239551 := bstep (se 1 (by rfl) ⟨179663, by rfl⟩ : syracuseStep 239551 = 359327) B359327
theorem B534491 : Blo 235815 534491 := bstep (se 1 (by rfl) ⟨400868, by rfl⟩ : syracuseStep 534491 = 801737) B801737
theorem B239583 : Blo 235815 239583 := bstep (se 1 (by rfl) ⟨179687, by rfl⟩ : syracuseStep 239583 = 359375) B359375
theorem B239643 : Blo 235815 239643 := bstep (se 1 (by rfl) ⟨179732, by rfl⟩ : syracuseStep 239643 = 359465) B359465
theorem B239647 : Blo 235815 239647 := bstep (se 1 (by rfl) ⟨179735, by rfl⟩ : syracuseStep 239647 = 359471) B359471
theorem B239663 : Blo 235815 239663 := bstep (se 1 (by rfl) ⟨179747, by rfl⟩ : syracuseStep 239663 = 359495) B359495
theorem B534671 : Blo 235815 534671 := bstep (se 1 (by rfl) ⟨401003, by rfl⟩ : syracuseStep 534671 = 802007) B802007
theorem B7973057 : Blo 235815 7973057 := bstep (se 2 (by rfl) ⟨2989896, by rfl⟩ : syracuseStep 7973057 = 5979793) B5979793
theorem B534761 : Blo 235815 534761 := bstep (se 2 (by rfl) ⟨200535, by rfl⟩ : syracuseStep 534761 = 401071) B401071
theorem B960761 : Blo 235815 960761 := bstep (se 2 (by rfl) ⟨360285, by rfl⟩ : syracuseStep 960761 = 720571) B720571
theorem B1812779 : Blo 235815 1812779 := bstep (se 1 (by rfl) ⟨1359584, by rfl⟩ : syracuseStep 1812779 = 2719169) B2719169
theorem B535031 : Blo 235815 535031 := bstep (se 1 (by rfl) ⟨401273, by rfl⟩ : syracuseStep 535031 = 802547) B802547
theorem B1944121 : Blo 235815 1944121 := bstep (se 2 (by rfl) ⟨729045, by rfl⟩ : syracuseStep 1944121 = 1458091) B1458091
theorem B928427 : Blo 235815 928427 := bstep (se 1 (by rfl) ⟨696320, by rfl⟩ : syracuseStep 928427 = 1392641) B1392641
theorem B13806395 : Blo 235815 13806395 := bstep (se 1 (by rfl) ⟨10354796, by rfl⟩ : syracuseStep 13806395 = 20709593) B20709593
theorem B568271 : Blo 235815 568271 := bstep (se 1 (by rfl) ⟨426203, by rfl⟩ : syracuseStep 568271 = 852407) B852407
theorem B535625 : Blo 235815 535625 := bstep (se 2 (by rfl) ⟨200859, by rfl⟩ : syracuseStep 535625 = 401719) B401719
theorem B7777361 : Blo 235815 7777361 := bstep (se 2 (by rfl) ⟨2916510, by rfl⟩ : syracuseStep 7777361 = 5833021) B5833021
theorem B961811 : Blo 235815 961811 := bstep (se 1 (by rfl) ⟨721358, by rfl⟩ : syracuseStep 961811 = 1442717) B1442717
theorem B3452179 : Blo 235815 3452179 := bstep (se 1 (by rfl) ⟨2589134, by rfl⟩ : syracuseStep 3452179 = 5178269) B5178269
theorem B2698757 : Blo 235815 2698757 := bstep (se 4 (by rfl) ⟨253008, by rfl⟩ : syracuseStep 2698757 = 506017) B506017
theorem B2174957 : Blo 235815 2174957 := bstep (se 3 (by rfl) ⟨407804, by rfl⟩ : syracuseStep 2174957 = 815609) B815609
theorem B503891 : Blo 235815 503891 := bstep (se 1 (by rfl) ⟨377918, by rfl⟩ : syracuseStep 503891 = 755837) B755837
theorem B1814723 : Blo 235815 1814723 := bstep (se 1 (by rfl) ⟨1361042, by rfl⟩ : syracuseStep 1814723 = 2722085) B2722085
theorem B897277 : Blo 235815 897277 := bstep (se 3 (by rfl) ⟨168239, by rfl⟩ : syracuseStep 897277 = 336479) B336479
theorem B602387 : Blo 235815 602387 := bstep (se 1 (by rfl) ⟨451790, by rfl⟩ : syracuseStep 602387 = 903581) B903581
theorem B3420467 : Blo 235815 3420467 := bstep (se 1 (by rfl) ⟨2565350, by rfl⟩ : syracuseStep 3420467 = 5130701) B5130701
theorem B537353 : Blo 235815 537353 := bstep (se 2 (by rfl) ⟨201507, by rfl⟩ : syracuseStep 537353 = 403015) B403015
theorem B963353 : Blo 235815 963353 := bstep (se 2 (by rfl) ⟨361257, by rfl⟩ : syracuseStep 963353 = 722515) B722515
theorem B537407 : Blo 235815 537407 := bstep (se 1 (by rfl) ⟨403055, by rfl⟩ : syracuseStep 537407 = 806111) B806111
theorem B1553215 : Blo 235815 1553215 := bstep (se 1 (by rfl) ⟨1164911, by rfl⟩ : syracuseStep 1553215 = 2329823) B2329823
theorem B537551 : Blo 235815 537551 := bstep (se 1 (by rfl) ⟨403163, by rfl⟩ : syracuseStep 537551 = 806327) B806327
theorem B504787 : Blo 235815 504787 := bstep (se 1 (by rfl) ⟨378590, by rfl⟩ : syracuseStep 504787 = 757181) B757181
theorem B537641 : Blo 235815 537641 := bstep (se 2 (by rfl) ⟨201615, by rfl⟩ : syracuseStep 537641 = 403231) B403231
theorem B1815695 : Blo 235815 1815695 := bstep (se 1 (by rfl) ⟨1361771, by rfl⟩ : syracuseStep 1815695 = 2723543) B2723543
theorem B1357033 : Blo 235815 1357033 := bstep (se 2 (by rfl) ⟨508887, by rfl⟩ : syracuseStep 1357033 = 1017775) B1017775
theorem B767227 : Blo 235815 767227 := bstep (se 1 (by rfl) ⟨575420, by rfl⟩ : syracuseStep 767227 = 1150841) B1150841
theorem B800009 : Blo 235815 800009 := bstep (se 2 (by rfl) ⟨300003, by rfl⟩ : syracuseStep 800009 = 600007) B600007
theorem B537929 : Blo 235815 537929 := bstep (se 2 (by rfl) ⟨201723, by rfl⟩ : syracuseStep 537929 = 403447) B403447
theorem B2274925 : Blo 235815 2274925 := bstep (se 3 (by rfl) ⟨426548, by rfl⟩ : syracuseStep 2274925 = 853097) B853097
theorem B898721 : Blo 235815 898721 := bstep (se 2 (by rfl) ⟨337020, by rfl⟩ : syracuseStep 898721 = 674041) B674041
theorem B800495 : Blo 235815 800495 := bstep (se 1 (by rfl) ⟨600371, by rfl⟩ : syracuseStep 800495 = 1200743) B1200743
theorem B603895 : Blo 235815 603895 := bstep (se 1 (by rfl) ⟨452921, by rfl⟩ : syracuseStep 603895 = 905843) B905843
theorem B538919 : Blo 235815 538919 := bstep (se 1 (by rfl) ⟨404189, by rfl⟩ : syracuseStep 538919 = 808379) B808379
theorem B2275847 : Blo 235815 2275847 := bstep (se 1 (by rfl) ⟨1706885, by rfl⟩ : syracuseStep 2275847 = 3413771) B3413771
theorem B539279 : Blo 235815 539279 := bstep (se 1 (by rfl) ⟨404459, by rfl⟩ : syracuseStep 539279 = 808919) B808919
theorem B801467 : Blo 235815 801467 := bstep (se 1 (by rfl) ⟨601100, by rfl⟩ : syracuseStep 801467 = 1202201) B1202201
theorem B539369 : Blo 235815 539369 := bstep (se 2 (by rfl) ⟨202263, by rfl⟩ : syracuseStep 539369 = 404527) B404527
theorem B59554739 : Blo 235815 59554739 := bstep (se 1 (by rfl) ⟨44666054, by rfl⟩ : syracuseStep 59554739 = 89332109) B89332109
theorem B1522745 : Blo 235815 1522745 := bstep (se 2 (by rfl) ⟨571029, by rfl⟩ : syracuseStep 1522745 = 1142059) B1142059
theorem B2571365 : Blo 235815 2571365 := bstep (se 4 (by rfl) ⟨241065, by rfl⟩ : syracuseStep 2571365 = 482131) B482131
theorem B1359449 : Blo 235815 1359449 := bstep (se 2 (by rfl) ⟨509793, by rfl⟩ : syracuseStep 1359449 = 1019587) B1019587
theorem B23117683 : Blo 235815 23117683 := bstep (se 1 (by rfl) ⟨17338262, by rfl⟩ : syracuseStep 23117683 = 34676525) B34676525
theorem B606163 : Blo 235815 606163 := bstep (se 1 (by rfl) ⟨454622, by rfl⟩ : syracuseStep 606163 = 909245) B909245
theorem B737515 : Blo 235815 737515 := bstep (se 1 (by rfl) ⟨553136, by rfl⟩ : syracuseStep 737515 = 1106273) B1106273
theorem B3850487 : Blo 235815 3850487 := bstep (se 1 (by rfl) ⟨2887865, by rfl⟩ : syracuseStep 3850487 = 5775731) B5775731
theorem B574057 : Blo 235815 574057 := bstep (se 2 (by rfl) ⟨215271, by rfl⟩ : syracuseStep 574057 = 430543) B430543
theorem B803951 : Blo 235815 803951 := bstep (se 1 (by rfl) ⟨602963, by rfl⟩ : syracuseStep 803951 = 1205927) B1205927
theorem B804059 : Blo 235815 804059 := bstep (se 1 (by rfl) ⟨603044, by rfl⟩ : syracuseStep 804059 = 1206089) B1206089
theorem B279887 : Blo 235815 279887 := bstep (se 1 (by rfl) ⟨209915, by rfl⟩ : syracuseStep 279887 = 419831) B419831
theorem B1525229 : Blo 235815 1525229 := bstep (se 3 (by rfl) ⟨285980, by rfl⟩ : syracuseStep 1525229 = 571961) B571961
theorem B509503 : Blo 235815 509503 := bstep (se 1 (by rfl) ⟨382127, by rfl⟩ : syracuseStep 509503 = 764255) B764255
theorem B968363 : Blo 235815 968363 := bstep (se 1 (by rfl) ⟨726272, by rfl⟩ : syracuseStep 968363 = 1452545) B1452545
theorem B969337 : Blo 235815 969337 := bstep (se 2 (by rfl) ⟨363501, by rfl⟩ : syracuseStep 969337 = 727003) B727003
theorem B4311731 : Blo 235815 4311731 := bstep (se 1 (by rfl) ⟨3233798, by rfl⟩ : syracuseStep 4311731 = 6467597) B6467597
theorem B675499 : Blo 235815 675499 := bstep (se 1 (by rfl) ⟨506624, by rfl⟩ : syracuseStep 675499 = 1013249) B1013249
theorem B675773 : Blo 235815 675773 := bstep (se 3 (by rfl) ⟨126707, by rfl⟩ : syracuseStep 675773 = 253415) B253415
theorem B2576765 : Blo 235815 2576765 := bstep (se 3 (by rfl) ⟨483143, by rfl⟩ : syracuseStep 2576765 = 966287) B966287
theorem B1134985 : Blo 235815 1134985 := bstep (se 2 (by rfl) ⟨425619, by rfl⟩ : syracuseStep 1134985 = 851239) B851239
theorem B807785 : Blo 235815 807785 := bstep (se 2 (by rfl) ⟨302919, by rfl⟩ : syracuseStep 807785 = 605839) B605839
theorem B1135603 : Blo 235815 1135603 := bstep (se 1 (by rfl) ⟨851702, by rfl⟩ : syracuseStep 1135603 = 1703405) B1703405
theorem B284251 : Blo 235815 284251 := bstep (se 1 (by rfl) ⟨213188, by rfl⟩ : syracuseStep 284251 = 426377) B426377
theorem B678107 : Blo 235815 678107 := bstep (se 1 (by rfl) ⟨508580, by rfl⟩ : syracuseStep 678107 = 1017161) B1017161
theorem B907483 : Blo 235815 907483 := bstep (se 1 (by rfl) ⟨680612, by rfl⟩ : syracuseStep 907483 = 1361225) B1361225
theorem B580409 : Blo 235815 580409 := bstep (se 2 (by rfl) ⟨217653, by rfl⟩ : syracuseStep 580409 = 435307) B435307
theorem B875375 : Blo 235815 875375 := bstep (se 1 (by rfl) ⟨656531, by rfl⟩ : syracuseStep 875375 = 1313063) B1313063
theorem B2186635 : Blo 235815 2186635 := bstep (se 1 (by rfl) ⟨1639976, by rfl⟩ : syracuseStep 2186635 = 3279953) B3279953
theorem B4120001 : Blo 235815 4120001 := bstep (se 2 (by rfl) ⟨1545000, by rfl⟩ : syracuseStep 4120001 = 3090001) B3090001
theorem B1138157 : Blo 235815 1138157 := bstep (se 3 (by rfl) ⟨213404, by rfl⟩ : syracuseStep 1138157 = 426809) B426809
theorem B23092775 : Blo 235815 23092775 := bstep (se 1 (by rfl) ⟨17319581, by rfl⟩ : syracuseStep 23092775 = 34639163) B34639163
theorem B3432223 : Blo 235815 3432223 := bstep (se 1 (by rfl) ⟨2574167, by rfl⟩ : syracuseStep 3432223 = 5148335) B5148335
theorem B3400055 : Blo 235815 3400055 := bstep (se 1 (by rfl) ⟨2550041, by rfl⟩ : syracuseStep 3400055 = 5100083) B5100083
theorem B451099 : Blo 235815 451099 := bstep (se 1 (by rfl) ⟨338324, by rfl⟩ : syracuseStep 451099 = 676649) B676649
theorem B254683 : Blo 235815 254683 := bstep (se 1 (by rfl) ⟨191012, by rfl⟩ : syracuseStep 254683 = 382025) B382025
theorem B451631 : Blo 235815 451631 := bstep (se 1 (by rfl) ⟨338723, by rfl⟩ : syracuseStep 451631 = 677447) B677447
theorem B353819 : Blo 235815 353819 := bstep (se 1 (by rfl) ⟨265364, by rfl⟩ : syracuseStep 353819 = 530729) B530729
theorem B1926737 : Blo 235815 1926737 := bstep (se 2 (by rfl) ⟨722526, by rfl⟩ : syracuseStep 1926737 = 1445053) B1445053
theorem B354203 : Blo 235815 354203 := bstep (se 1 (by rfl) ⟨265652, by rfl⟩ : syracuseStep 354203 = 531305) B531305
theorem B354239 : Blo 235815 354239 := bstep (se 1 (by rfl) ⟨265679, by rfl⟩ : syracuseStep 354239 = 531359) B531359
theorem B354425 : Blo 235815 354425 := bstep (se 2 (by rfl) ⟨132909, by rfl⟩ : syracuseStep 354425 = 265819) B265819
theorem B977039 : Blo 235815 977039 := bstep (se 1 (by rfl) ⟨732779, by rfl⟩ : syracuseStep 977039 = 1465559) B1465559
theorem B2877605 : Blo 235815 2877605 := bstep (se 4 (by rfl) ⟨269775, by rfl⟩ : syracuseStep 2877605 = 539551) B539551
theorem B1206575 : Blo 235815 1206575 := bstep (se 1 (by rfl) ⟨904931, by rfl⟩ : syracuseStep 1206575 = 1809863) B1809863
theorem B354809 : Blo 235815 354809 := bstep (se 2 (by rfl) ⟨133053, by rfl⟩ : syracuseStep 354809 = 266107) B266107
theorem B354863 : Blo 235815 354863 := bstep (se 1 (by rfl) ⟨266147, by rfl⟩ : syracuseStep 354863 = 532295) B532295
theorem B355295 : Blo 235815 355295 := bstep (se 1 (by rfl) ⟨266471, by rfl⟩ : syracuseStep 355295 = 532943) B532943
theorem B355739 : Blo 235815 355739 := bstep (se 1 (by rfl) ⟨266804, by rfl⟩ : syracuseStep 355739 = 533609) B533609
theorem B454099 : Blo 235815 454099 := bstep (se 1 (by rfl) ⟨340574, by rfl⟩ : syracuseStep 454099 = 681149) B681149
theorem B1797713 : Blo 235815 1797713 := bstep (se 2 (by rfl) ⟨674142, by rfl⟩ : syracuseStep 1797713 = 1348285) B1348285
theorem B257639 : Blo 235815 257639 := bstep (se 1 (by rfl) ⟨193229, by rfl⟩ : syracuseStep 257639 = 386459) B386459
theorem B1208033 : Blo 235815 1208033 := bstep (se 2 (by rfl) ⟨453012, by rfl⟩ : syracuseStep 1208033 = 906025) B906025
theorem B356159 : Blo 235815 356159 := bstep (se 1 (by rfl) ⟨267119, by rfl⟩ : syracuseStep 356159 = 534239) B534239
theorem B356345 : Blo 235815 356345 := bstep (se 2 (by rfl) ⟨133629, by rfl⟩ : syracuseStep 356345 = 267259) B267259
theorem B1535993 : Blo 235815 1535993 := bstep (se 2 (by rfl) ⟨575997, by rfl⟩ : syracuseStep 1535993 = 1151995) B1151995
theorem B454729 : Blo 235815 454729 := bstep (se 2 (by rfl) ⟨170523, by rfl⟩ : syracuseStep 454729 = 341047) B341047
theorem B356585 : Blo 235815 356585 := bstep (se 2 (by rfl) ⟨133719, by rfl⟩ : syracuseStep 356585 = 267439) B267439
theorem B454889 : Blo 235815 454889 := bstep (se 2 (by rfl) ⟨170583, by rfl⟩ : syracuseStep 454889 = 341167) B341167
theorem B356711 : Blo 235815 356711 := bstep (se 1 (by rfl) ⟨267533, by rfl⟩ : syracuseStep 356711 = 535067) B535067
theorem B4551389 : Blo 235815 4551389 := bstep (se 3 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 4551389 = 1706771) B1706771
theorem B717563 : Blo 235815 717563 := bstep (se 1 (by rfl) ⟨538172, by rfl⟩ : syracuseStep 717563 = 1076345) B1076345
theorem B357257 : Blo 235815 357257 := bstep (se 2 (by rfl) ⟨133971, by rfl⟩ : syracuseStep 357257 = 267943) B267943
theorem B357641 : Blo 235815 357641 := bstep (se 2 (by rfl) ⟨134115, by rfl⟩ : syracuseStep 357641 = 268231) B268231
theorem B357695 : Blo 235815 357695 := bstep (se 1 (by rfl) ⟨268271, by rfl⟩ : syracuseStep 357695 = 536543) B536543
theorem B1013401 : Blo 235815 1013401 := bstep (se 2 (by rfl) ⟨380025, by rfl⟩ : syracuseStep 1013401 = 760051) B760051
theorem B358121 : Blo 235815 358121 := bstep (se 2 (by rfl) ⟨134295, by rfl⟩ : syracuseStep 358121 = 268591) B268591
theorem B358127 : Blo 235815 358127 := bstep (se 1 (by rfl) ⟨268595, by rfl⟩ : syracuseStep 358127 = 537191) B537191
theorem B1800143 : Blo 235815 1800143 := bstep (se 1 (by rfl) ⟨1350107, by rfl⟩ : syracuseStep 1800143 = 2700215) B2700215
theorem B358583 : Blo 235815 358583 := bstep (se 1 (by rfl) ⟨268937, by rfl⟩ : syracuseStep 358583 = 537875) B537875
theorem B358631 : Blo 235815 358631 := bstep (se 1 (by rfl) ⟨268973, by rfl⟩ : syracuseStep 358631 = 537947) B537947
theorem B359003 : Blo 235815 359003 := bstep (se 1 (by rfl) ⟨269252, by rfl⟩ : syracuseStep 359003 = 538505) B538505
theorem B1145441 : Blo 235815 1145441 := bstep (se 2 (by rfl) ⟨429540, by rfl⟩ : syracuseStep 1145441 = 859081) B859081
theorem B359147 : Blo 235815 359147 := bstep (se 1 (by rfl) ⟨269360, by rfl⟩ : syracuseStep 359147 = 538721) B538721
theorem B359177 : Blo 235815 359177 := bstep (se 2 (by rfl) ⟨134691, by rfl⟩ : syracuseStep 359177 = 269383) B269383
theorem B1211219 : Blo 235815 1211219 := bstep (se 1 (by rfl) ⟨908414, by rfl⟩ : syracuseStep 1211219 = 1816829) B1816829
theorem B2030629 : Blo 235815 2030629 := bstep (se 4 (by rfl) ⟨190371, by rfl⟩ : syracuseStep 2030629 = 380743) B380743
theorem B2849869 : Blo 235815 2849869 := bstep (se 3 (by rfl) ⟨534350, by rfl⟩ : syracuseStep 2849869 = 1068701) B1068701
theorem B1211759 : Blo 235815 1211759 := bstep (se 1 (by rfl) ⟨908819, by rfl⟩ : syracuseStep 1211759 = 1817639) B1817639
theorem B1015247 : Blo 235815 1015247 := bstep (se 1 (by rfl) ⟨761435, by rfl⟩ : syracuseStep 1015247 = 1522871) B1522871
theorem B2883833 : Blo 235815 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B983353 : Blo 235815 983353 := bstep (se 2 (by rfl) ⟨368757, by rfl⟩ : syracuseStep 983353 = 737515) B737515
theorem B3867095 : Blo 235815 3867095 := bstep (se 1 (by rfl) ⟨2900321, by rfl⟩ : syracuseStep 3867095 = 5800643) B5800643
theorem B1016819 : Blo 235815 1016819 := bstep (se 1 (by rfl) ⟨762614, by rfl⟩ : syracuseStep 1016819 = 1525229) B1525229
theorem B6554621 : Blo 235815 6554621 := bstep (se 3 (by rfl) ⟨1228991, by rfl⟩ : syracuseStep 6554621 = 2457983) B2457983
theorem B1803545 : Blo 235815 1803545 := bstep (se 2 (by rfl) ⟨676329, by rfl⟩ : syracuseStep 1803545 = 1352659) B1352659
theorem B2624723 : Blo 235815 2624723 := bstep (se 1 (by rfl) ⟨1968542, by rfl⟩ : syracuseStep 2624723 = 3937085) B3937085
theorem B2886943 : Blo 235815 2886943 := bstep (se 1 (by rfl) ⟨2165207, by rfl⟩ : syracuseStep 2886943 = 4330415) B4330415
theorem B2592161 : Blo 235815 2592161 := bstep (se 2 (by rfl) ⟨972060, by rfl⟩ : syracuseStep 2592161 = 1944121) B1944121
theorem B2985461 : Blo 235815 2985461 := bstep (se 5 (by rfl) ⟨139943, by rfl⟩ : syracuseStep 2985461 = 279887) B279887
theorem B266431 : Blo 235815 266431 := bstep (se 1 (by rfl) ⟨199823, by rfl⟩ : syracuseStep 266431 = 399647) B399647
theorem B758771 : Blo 235815 758771 := bstep (se 1 (by rfl) ⟨569078, by rfl⟩ : syracuseStep 758771 = 1138157) B1138157
theorem B398911 : Blo 235815 398911 := bstep (se 1 (by rfl) ⟨299183, by rfl⟩ : syracuseStep 398911 = 598367) B598367
theorem B2266703 : Blo 235815 2266703 := bstep (se 1 (by rfl) ⟨1700027, by rfl⟩ : syracuseStep 2266703 = 3400055) B3400055
theorem B1513313 : Blo 235815 1513313 := bstep (se 2 (by rfl) ⟨567492, by rfl⟩ : syracuseStep 1513313 = 1134985) B1134985
theorem B301087 : Blo 235815 301087 := bstep (se 1 (by rfl) ⟨225815, by rfl⟩ : syracuseStep 301087 = 451631) B451631
theorem B235879 : Blo 235815 235879 := bstep (se 1 (by rfl) ⟨176909, by rfl⟩ : syracuseStep 235879 = 353819) B353819
theorem B25041287 : Blo 235815 25041287 := bstep (se 1 (by rfl) ⟨18780965, by rfl⟩ : syracuseStep 25041287 = 37561931) B37561931
theorem B1284491 : Blo 235815 1284491 := bstep (se 1 (by rfl) ⟨963368, by rfl⟩ : syracuseStep 1284491 = 1926737) B1926737
theorem B2070953 : Blo 235815 2070953 := bstep (se 2 (by rfl) ⟨776607, by rfl⟩ : syracuseStep 2070953 = 1553215) B1553215
theorem B531035 : Blo 235815 531035 := bstep (se 1 (by rfl) ⟨398276, by rfl⟩ : syracuseStep 531035 = 796553) B796553
theorem B236135 : Blo 235815 236135 := bstep (se 1 (by rfl) ⟨177101, by rfl⟩ : syracuseStep 236135 = 354203) B354203
theorem B236159 : Blo 235815 236159 := bstep (se 1 (by rfl) ⟨177119, by rfl⟩ : syracuseStep 236159 = 354239) B354239
theorem B1514137 : Blo 235815 1514137 := bstep (se 2 (by rfl) ⟨567801, by rfl⟩ : syracuseStep 1514137 = 1135603) B1135603
theorem B236283 : Blo 235815 236283 := bstep (se 1 (by rfl) ⟨177212, by rfl⟩ : syracuseStep 236283 = 354425) B354425
theorem B5315371 : Blo 235815 5315371 := bstep (se 1 (by rfl) ⟨3986528, by rfl⟩ : syracuseStep 5315371 = 7973057) B7973057
theorem B3054509 : Blo 235815 3054509 := bstep (se 3 (by rfl) ⟨572720, by rfl⟩ : syracuseStep 3054509 = 1145441) B1145441
theorem B1809377 : Blo 235815 1809377 := bstep (se 2 (by rfl) ⟨678516, by rfl⟩ : syracuseStep 1809377 = 1357033) B1357033
theorem B1022969 : Blo 235815 1022969 := bstep (se 2 (by rfl) ⟨383613, by rfl⟩ : syracuseStep 1022969 = 767227) B767227
theorem B236539 : Blo 235815 236539 := bstep (se 1 (by rfl) ⟨177404, by rfl⟩ : syracuseStep 236539 = 354809) B354809
theorem B236575 : Blo 235815 236575 := bstep (se 1 (by rfl) ⟨177431, by rfl⟩ : syracuseStep 236575 = 354863) B354863
theorem B236863 : Blo 235815 236863 := bstep (se 1 (by rfl) ⟨177647, by rfl⟩ : syracuseStep 236863 = 355295) B355295
theorem B1351201 : Blo 235815 1351201 := bstep (se 2 (by rfl) ⟨506700, by rfl⟩ : syracuseStep 1351201 = 1013401) B1013401
theorem B237159 : Blo 235815 237159 := bstep (se 1 (by rfl) ⟨177869, by rfl⟩ : syracuseStep 237159 = 355739) B355739
theorem B237439 : Blo 235815 237439 := bstep (se 1 (by rfl) ⟨178079, by rfl⟩ : syracuseStep 237439 = 356159) B356159
theorem B1449971 : Blo 235815 1449971 := bstep (se 1 (by rfl) ⟨1087478, by rfl⟩ : syracuseStep 1449971 = 2174957) B2174957
theorem B237563 : Blo 235815 237563 := bstep (se 1 (by rfl) ⟨178172, by rfl⟩ : syracuseStep 237563 = 356345) B356345
theorem B1023995 : Blo 235815 1023995 := bstep (se 1 (by rfl) ⟨767996, by rfl⟩ : syracuseStep 1023995 = 1535993) B1535993
theorem B335927 : Blo 235815 335927 := bstep (se 1 (by rfl) ⟨251945, by rfl⟩ : syracuseStep 335927 = 503891) B503891
theorem B4989053 : Blo 235815 4989053 := bstep (se 3 (by rfl) ⟨935447, by rfl⟩ : syracuseStep 4989053 = 1870895) B1870895
theorem B4858001 : Blo 235815 4858001 := bstep (se 2 (by rfl) ⟨1821750, by rfl⟩ : syracuseStep 4858001 = 3643501) B3643501
theorem B237723 : Blo 235815 237723 := bstep (se 1 (by rfl) ⟨178292, by rfl⟩ : syracuseStep 237723 = 356585) B356585
theorem B303259 : Blo 235815 303259 := bstep (se 1 (by rfl) ⟨227444, by rfl⟩ : syracuseStep 303259 = 454889) B454889
theorem B401591 : Blo 235815 401591 := bstep (se 1 (by rfl) ⟨301193, by rfl⟩ : syracuseStep 401591 = 602387) B602387
theorem B237807 : Blo 235815 237807 := bstep (se 1 (by rfl) ⟨178355, by rfl⟩ : syracuseStep 237807 = 356711) B356711
theorem B533033 : Blo 235815 533033 := bstep (se 2 (by rfl) ⟨199887, by rfl⟩ : syracuseStep 533033 = 399775) B399775
theorem B238171 : Blo 235815 238171 := bstep (se 1 (by rfl) ⟨178628, by rfl⟩ : syracuseStep 238171 = 357257) B357257
theorem B533339 : Blo 235815 533339 := bstep (se 1 (by rfl) ⟨400004, by rfl⟩ : syracuseStep 533339 = 800009) B800009
theorem B238427 : Blo 235815 238427 := bstep (se 1 (by rfl) ⟨178820, by rfl⟩ : syracuseStep 238427 = 357641) B357641
theorem B238463 : Blo 235815 238463 := bstep (se 1 (by rfl) ⟨178847, by rfl⟩ : syracuseStep 238463 = 357695) B357695
theorem B599147 : Blo 235815 599147 := bstep (se 1 (by rfl) ⟨449360, by rfl⟩ : syracuseStep 599147 = 898721) B898721
theorem B238747 : Blo 235815 238747 := bstep (se 1 (by rfl) ⟨179060, by rfl⟩ : syracuseStep 238747 = 358121) B358121
theorem B533663 : Blo 235815 533663 := bstep (se 1 (by rfl) ⟨400247, by rfl⟩ : syracuseStep 533663 = 800495) B800495
theorem B238751 : Blo 235815 238751 := bstep (se 1 (by rfl) ⟨179063, by rfl⟩ : syracuseStep 238751 = 358127) B358127
theorem B239055 : Blo 235815 239055 := bstep (se 1 (by rfl) ⟨179291, by rfl⟩ : syracuseStep 239055 = 358583) B358583
theorem B239087 : Blo 235815 239087 := bstep (se 1 (by rfl) ⟨179315, by rfl⟩ : syracuseStep 239087 = 358631) B358631
theorem B403049 : Blo 235815 403049 := bstep (se 2 (by rfl) ⟨151143, by rfl⟩ : syracuseStep 403049 = 302287) B302287
theorem B1517231 : Blo 235815 1517231 := bstep (se 1 (by rfl) ⟨1137923, by rfl⟩ : syracuseStep 1517231 = 2275847) B2275847
theorem B239335 : Blo 235815 239335 := bstep (se 1 (by rfl) ⟨179501, by rfl⟩ : syracuseStep 239335 = 359003) B359003
theorem B534311 : Blo 235815 534311 := bstep (se 1 (by rfl) ⟨400733, by rfl⟩ : syracuseStep 534311 = 801467) B801467
theorem B239431 : Blo 235815 239431 := bstep (se 1 (by rfl) ⟨179573, by rfl⟩ : syracuseStep 239431 = 359147) B359147
theorem B239451 : Blo 235815 239451 := bstep (se 1 (by rfl) ⟨179588, by rfl⟩ : syracuseStep 239451 = 359177) B359177
theorem B1714243 : Blo 235815 1714243 := bstep (se 1 (by rfl) ⟨1285682, by rfl⟩ : syracuseStep 1714243 = 2571365) B2571365
theorem B796769 : Blo 235815 796769 := bstep (se 2 (by rfl) ⟨298788, by rfl⟩ : syracuseStep 796769 = 597577) B597577
theorem B534689 : Blo 235815 534689 := bstep (se 2 (by rfl) ⟨200508, by rfl⟩ : syracuseStep 534689 = 401017) B401017
theorem B797309 : Blo 235815 797309 := bstep (se 3 (by rfl) ⟨149495, by rfl⟩ : syracuseStep 797309 = 298991) B298991
theorem B2566991 : Blo 235815 2566991 := bstep (se 1 (by rfl) ⟨1925243, by rfl⟩ : syracuseStep 2566991 = 3850487) B3850487
theorem B1355075 : Blo 235815 1355075 := bstep (se 1 (by rfl) ⟨1016306, by rfl⟩ : syracuseStep 1355075 = 2032613) B2032613
theorem B601465 : Blo 235815 601465 := bstep (se 2 (by rfl) ⟨225549, by rfl⟩ : syracuseStep 601465 = 451099) B451099
theorem B535967 : Blo 235815 535967 := bstep (se 1 (by rfl) ⟨401975, by rfl⟩ : syracuseStep 535967 = 803951) B803951
theorem B765409 : Blo 235815 765409 := bstep (se 2 (by rfl) ⟨287028, by rfl⟩ : syracuseStep 765409 = 574057) B574057
theorem B536039 : Blo 235815 536039 := bstep (se 1 (by rfl) ⟨402029, by rfl⟩ : syracuseStep 536039 = 804059) B804059
theorem B1617583 : Blo 235815 1617583 := bstep (se 1 (by rfl) ⟨1213187, by rfl⟩ : syracuseStep 1617583 = 2426375) B2426375
theorem B1093715 : Blo 235815 1093715 := bstep (se 1 (by rfl) ⟨820286, by rfl⟩ : syracuseStep 1093715 = 1640573) B1640573
theorem B536993 : Blo 235815 536993 := bstep (se 2 (by rfl) ⟨201372, by rfl⟩ : syracuseStep 536993 = 402745) B402745
theorem B2568941 : Blo 235815 2568941 := bstep (se 3 (by rfl) ⟨481676, by rfl⟩ : syracuseStep 2568941 = 963353) B963353
theorem B1749995 : Blo 235815 1749995 := bstep (se 1 (by rfl) ⟨1312496, by rfl⟩ : syracuseStep 1749995 = 2624993) B2624993
theorem B570347 : Blo 235815 570347 := bstep (se 1 (by rfl) ⟨427760, by rfl⟩ : syracuseStep 570347 = 855521) B855521
theorem B1717843 : Blo 235815 1717843 := bstep (se 1 (by rfl) ⟨1288382, by rfl⟩ : syracuseStep 1717843 = 2576765) B2576765
theorem B538523 : Blo 235815 538523 := bstep (se 1 (by rfl) ⟨403892, by rfl⟩ : syracuseStep 538523 = 807785) B807785
theorem B1292449 : Blo 235815 1292449 := bstep (se 2 (by rfl) ⟨484668, by rfl⟩ : syracuseStep 1292449 = 969337) B969337
theorem B1358309 : Blo 235815 1358309 := bstep (se 4 (by rfl) ⟨127341, by rfl⟩ : syracuseStep 1358309 = 254683) B254683
theorem B768503 : Blo 235815 768503 := bstep (se 1 (by rfl) ⟨576377, by rfl⟩ : syracuseStep 768503 = 1152755) B1152755
theorem B506359 : Blo 235815 506359 := bstep (se 1 (by rfl) ⟨379769, by rfl⟩ : syracuseStep 506359 = 759539) B759539
theorem B4602905 : Blo 235815 4602905 := bstep (se 2 (by rfl) ⟨1726089, by rfl⟩ : syracuseStep 4602905 = 3452179) B3452179
theorem B1359017 : Blo 235815 1359017 := bstep (se 2 (by rfl) ⟨509631, by rfl⟩ : syracuseStep 1359017 = 1019263) B1019263
theorem B605465 : Blo 235815 605465 := bstep (se 2 (by rfl) ⟨227049, by rfl⟩ : syracuseStep 605465 = 454099) B454099
theorem B900665 : Blo 235815 900665 := bstep (se 2 (by rfl) ⟨337749, by rfl⟩ : syracuseStep 900665 = 675499) B675499
theorem B606305 : Blo 235815 606305 := bstep (se 2 (by rfl) ⟨227364, by rfl⟩ : syracuseStep 606305 = 454729) B454729
theorem B1196369 : Blo 235815 1196369 := bstep (se 2 (by rfl) ⟨448638, by rfl⟩ : syracuseStep 1196369 = 897277) B897277
theorem B673049 : Blo 235815 673049 := bstep (se 2 (by rfl) ⟨252393, by rfl⟩ : syracuseStep 673049 = 504787) B504787
theorem B1918403 : Blo 235815 1918403 := bstep (se 1 (by rfl) ⟨1438802, by rfl⟩ : syracuseStep 1918403 = 2877605) B2877605
theorem B640507 : Blo 235815 640507 := bstep (se 1 (by rfl) ⟨480380, by rfl⟩ : syracuseStep 640507 = 960761) B960761
theorem B804383 : Blo 235815 804383 := bstep (se 1 (by rfl) ⟨603287, by rfl⟩ : syracuseStep 804383 = 1206575) B1206575
theorem B2475805 : Blo 235815 2475805 := bstep (se 3 (by rfl) ⟨464213, by rfl⟩ : syracuseStep 2475805 = 928427) B928427
theorem B378847 : Blo 235815 378847 := bstep (se 1 (by rfl) ⟨284135, by rfl⟩ : syracuseStep 378847 = 568271) B568271
theorem B379001 : Blo 235815 379001 := bstep (se 2 (by rfl) ⟨142125, by rfl⟩ : syracuseStep 379001 = 284251) B284251
theorem B3033233 : Blo 235815 3033233 := bstep (se 2 (by rfl) ⟨1137462, by rfl⟩ : syracuseStep 3033233 = 2274925) B2274925
theorem B641207 : Blo 235815 641207 := bstep (se 1 (by rfl) ⟨480905, by rfl⟩ : syracuseStep 641207 = 961811) B961811
theorem B805193 : Blo 235815 805193 := bstep (se 2 (by rfl) ⟨301947, by rfl⟩ : syracuseStep 805193 = 603895) B603895
theorem B1198475 : Blo 235815 1198475 := bstep (se 1 (by rfl) ⟨898856, by rfl⟩ : syracuseStep 1198475 = 1797713) B1797713
theorem B805355 : Blo 235815 805355 := bstep (se 1 (by rfl) ⟨604016, by rfl⟩ : syracuseStep 805355 = 1208033) B1208033
theorem B2280311 : Blo 235815 2280311 := bstep (se 1 (by rfl) ⟨1710233, by rfl⟩ : syracuseStep 2280311 = 3420467) B3420467
theorem B3034259 : Blo 235815 3034259 := bstep (se 1 (by rfl) ⟨2275694, by rfl⟩ : syracuseStep 3034259 = 4551389) B4551389
theorem B478375 : Blo 235815 478375 := bstep (se 1 (by rfl) ⟨358781, by rfl⟩ : syracuseStep 478375 = 717563) B717563
theorem B1200095 : Blo 235815 1200095 := bstep (se 1 (by rfl) ⟨900071, by rfl⟩ : syracuseStep 1200095 = 1800143) B1800143
theorem B2707505 : Blo 235815 2707505 := bstep (se 2 (by rfl) ⟨1015314, by rfl⟩ : syracuseStep 2707505 = 2030629) B2030629
theorem B807479 : Blo 235815 807479 := bstep (se 1 (by rfl) ⟨605609, by rfl⟩ : syracuseStep 807479 = 1211219) B1211219
theorem B39703159 : Blo 235815 39703159 := bstep (se 1 (by rfl) ⟨29777369, by rfl⟩ : syracuseStep 39703159 = 59554739) B59554739
theorem B807677 : Blo 235815 807677 := bstep (se 3 (by rfl) ⟨151439, by rfl⟩ : syracuseStep 807677 = 302879) B302879
theorem B807839 : Blo 235815 807839 := bstep (se 1 (by rfl) ⟨605879, by rfl⟩ : syracuseStep 807839 = 1211759) B1211759
theorem B676831 : Blo 235815 676831 := bstep (se 1 (by rfl) ⟨507623, by rfl⟩ : syracuseStep 676831 = 1015247) B1015247
theorem B4576297 : Blo 235815 4576297 := bstep (se 2 (by rfl) ⟨1716111, by rfl⟩ : syracuseStep 4576297 = 3432223) B3432223
theorem B906299 : Blo 235815 906299 := bstep (se 1 (by rfl) ⟨679724, by rfl⟩ : syracuseStep 906299 = 1359449) B1359449
theorem B30823577 : Blo 235815 30823577 := bstep (se 2 (by rfl) ⟨11558841, by rfl⟩ : syracuseStep 30823577 = 23117683) B23117683
theorem B808217 : Blo 235815 808217 := bstep (se 2 (by rfl) ⟨303081, by rfl⟩ : syracuseStep 808217 = 606163) B606163
theorem B1660267 : Blo 235815 1660267 := bstep (se 1 (by rfl) ⟨1245200, by rfl⟩ : syracuseStep 1660267 = 2490401) B2490401
theorem B645575 : Blo 235815 645575 := bstep (se 1 (by rfl) ⟨484181, by rfl⟩ : syracuseStep 645575 = 968363) B968363
theorem B3824927 : Blo 235815 3824927 := bstep (se 1 (by rfl) ⟨2868695, by rfl⟩ : syracuseStep 3824927 = 5737391) B5737391
theorem B613759 : Blo 235815 613759 := bstep (se 1 (by rfl) ⟨460319, by rfl⟩ : syracuseStep 613759 = 920639) B920639
theorem B679337 : Blo 235815 679337 := bstep (se 2 (by rfl) ⟨254751, by rfl⟩ : syracuseStep 679337 = 509503) B509503
theorem B2186813 : Blo 235815 2186813 := bstep (se 3 (by rfl) ⟨410027, by rfl⟩ : syracuseStep 2186813 = 820055) B820055
theorem B5758613 : Blo 235815 5758613 := bstep (se 6 (by rfl) ⟨134967, by rfl⟩ : syracuseStep 5758613 = 269935) B269935
theorem B450515 : Blo 235815 450515 := bstep (se 1 (by rfl) ⟨337886, by rfl⟩ : syracuseStep 450515 = 675773) B675773
theorem B1925153 : Blo 235815 1925153 := bstep (se 2 (by rfl) ⟨721932, by rfl⟩ : syracuseStep 1925153 = 1443865) B1443865
theorem B1008071 : Blo 235815 1008071 := bstep (se 1 (by rfl) ⟨756053, by rfl⟩ : syracuseStep 1008071 = 1512107) B1512107
theorem B452071 : Blo 235815 452071 := bstep (se 1 (by rfl) ⟨339053, by rfl⟩ : syracuseStep 452071 = 678107) B678107
theorem B353855 : Blo 235815 353855 := bstep (se 1 (by rfl) ⟨265391, by rfl⟩ : syracuseStep 353855 = 530783) B530783
theorem B386939 : Blo 235815 386939 := bstep (se 1 (by rfl) ⟨290204, by rfl⟩ : syracuseStep 386939 = 580409) B580409
theorem B583583 : Blo 235815 583583 := bstep (se 1 (by rfl) ⟨437687, by rfl⟩ : syracuseStep 583583 = 875375) B875375
theorem B354215 : Blo 235815 354215 := bstep (se 1 (by rfl) ⟨265661, by rfl⟩ : syracuseStep 354215 = 531323) B531323
theorem B354335 : Blo 235815 354335 := bstep (se 1 (by rfl) ⟨265751, by rfl⟩ : syracuseStep 354335 = 531503) B531503
theorem B2746667 : Blo 235815 2746667 := bstep (se 1 (by rfl) ⟨2060000, by rfl⟩ : syracuseStep 2746667 = 4120001) B4120001
theorem B15395183 : Blo 235815 15395183 := bstep (se 1 (by rfl) ⟨11546387, by rfl⟩ : syracuseStep 15395183 = 23092775) B23092775
theorem B354791 : Blo 235815 354791 := bstep (se 1 (by rfl) ⟨266093, by rfl⟩ : syracuseStep 354791 = 532187) B532187
theorem B1206899 : Blo 235815 1206899 := bstep (se 1 (by rfl) ⟨905174, by rfl⟩ : syracuseStep 1206899 = 1810349) B1810349
theorem B354971 : Blo 235815 354971 := bstep (se 1 (by rfl) ⟨266228, by rfl⟩ : syracuseStep 354971 = 532457) B532457
theorem B355193 : Blo 235815 355193 := bstep (se 2 (by rfl) ⟨133197, by rfl⟩ : syracuseStep 355193 = 266395) B266395
theorem B15199301 : Blo 235815 15199301 := bstep (se 4 (by rfl) ⟨1424934, by rfl⟩ : syracuseStep 15199301 = 2849869) B2849869
theorem B355439 : Blo 235815 355439 := bstep (se 1 (by rfl) ⟨266579, by rfl⟩ : syracuseStep 355439 = 533159) B533159
theorem B289903 : Blo 235815 289903 := bstep (se 1 (by rfl) ⟨217427, by rfl⟩ : syracuseStep 289903 = 434855) B434855
theorem B355535 : Blo 235815 355535 := bstep (se 1 (by rfl) ⟨266651, by rfl⟩ : syracuseStep 355535 = 533303) B533303
theorem B355655 : Blo 235815 355655 := bstep (se 1 (by rfl) ⟨266741, by rfl⟩ : syracuseStep 355655 = 533483) B533483
theorem B355943 : Blo 235815 355943 := bstep (se 1 (by rfl) ⟨266957, by rfl⟩ : syracuseStep 355943 = 533915) B533915
theorem B356327 : Blo 235815 356327 := bstep (se 1 (by rfl) ⟨267245, by rfl⟩ : syracuseStep 356327 = 534491) B534491
theorem B356447 : Blo 235815 356447 := bstep (se 1 (by rfl) ⟨267335, by rfl⟩ : syracuseStep 356447 = 534671) B534671
theorem B651359 : Blo 235815 651359 := bstep (se 1 (by rfl) ⟨488519, by rfl⟩ : syracuseStep 651359 = 977039) B977039
theorem B356507 : Blo 235815 356507 := bstep (se 1 (by rfl) ⟨267380, by rfl⟩ : syracuseStep 356507 = 534761) B534761
theorem B1208519 : Blo 235815 1208519 := bstep (se 1 (by rfl) ⟨906389, by rfl⟩ : syracuseStep 1208519 = 1812779) B1812779
theorem B356687 : Blo 235815 356687 := bstep (se 1 (by rfl) ⟨267515, by rfl⟩ : syracuseStep 356687 = 535031) B535031
theorem B356777 : Blo 235815 356777 := bstep (se 2 (by rfl) ⟨133791, by rfl⟩ : syracuseStep 356777 = 267583) B267583
theorem B11497949 : Blo 235815 11497949 := bstep (se 3 (by rfl) ⟨2155865, by rfl⟩ : syracuseStep 11497949 = 4311731) B4311731
theorem B9204263 : Blo 235815 9204263 := bstep (se 1 (by rfl) ⟨6903197, by rfl⟩ : syracuseStep 9204263 = 13806395) B13806395
theorem B357083 : Blo 235815 357083 := bstep (se 1 (by rfl) ⟨267812, by rfl⟩ : syracuseStep 357083 = 535625) B535625
theorem B357353 : Blo 235815 357353 := bstep (se 2 (by rfl) ⟨134007, by rfl⟩ : syracuseStep 357353 = 268015) B268015
theorem B1799171 : Blo 235815 1799171 := bstep (se 1 (by rfl) ⟨1349378, by rfl⟩ : syracuseStep 1799171 = 2698757) B2698757
theorem B357497 : Blo 235815 357497 := bstep (se 2 (by rfl) ⟨134061, by rfl⟩ : syracuseStep 357497 = 268123) B268123
theorem B9172277 : Blo 235815 9172277 := bstep (se 5 (by rfl) ⟨429950, by rfl⟩ : syracuseStep 9172277 = 859901) B859901
theorem B1209815 : Blo 235815 1209815 := bstep (se 1 (by rfl) ⟨907361, by rfl⟩ : syracuseStep 1209815 = 1814723) B1814723
theorem B20739629 : Blo 235815 20739629 := bstep (se 3 (by rfl) ⟨3888680, by rfl⟩ : syracuseStep 20739629 = 7777361) B7777361
theorem B1209977 : Blo 235815 1209977 := bstep (se 2 (by rfl) ⟨453741, by rfl⟩ : syracuseStep 1209977 = 907483) B907483
theorem B358025 : Blo 235815 358025 := bstep (se 2 (by rfl) ⟨134259, by rfl⟩ : syracuseStep 358025 = 268519) B268519
theorem B358235 : Blo 235815 358235 := bstep (se 1 (by rfl) ⟨268676, by rfl⟩ : syracuseStep 358235 = 537353) B537353
theorem B358271 : Blo 235815 358271 := bstep (se 1 (by rfl) ⟨268703, by rfl⟩ : syracuseStep 358271 = 537407) B537407
theorem B358367 : Blo 235815 358367 := bstep (se 1 (by rfl) ⟨268775, by rfl⟩ : syracuseStep 358367 = 537551) B537551
theorem B358427 : Blo 235815 358427 := bstep (se 1 (by rfl) ⟨268820, by rfl⟩ : syracuseStep 358427 = 537641) B537641
theorem B1210463 : Blo 235815 1210463 := bstep (se 1 (by rfl) ⟨907847, by rfl⟩ : syracuseStep 1210463 = 1815695) B1815695
theorem B358619 : Blo 235815 358619 := bstep (se 1 (by rfl) ⟨268964, by rfl⟩ : syracuseStep 358619 = 537929) B537929
theorem B358889 : Blo 235815 358889 := bstep (se 2 (by rfl) ⟨134583, by rfl⟩ : syracuseStep 358889 = 269167) B269167
theorem B359279 : Blo 235815 359279 := bstep (se 1 (by rfl) ⟨269459, by rfl⟩ : syracuseStep 359279 = 538919) B538919
theorem B687037 : Blo 235815 687037 := bstep (se 3 (by rfl) ⟨128819, by rfl⟩ : syracuseStep 687037 = 257639) B257639
theorem B359519 : Blo 235815 359519 := bstep (se 1 (by rfl) ⟨269639, by rfl⟩ : syracuseStep 359519 = 539279) B539279
theorem B359579 : Blo 235815 359579 := bstep (se 1 (by rfl) ⟨269684, by rfl⟩ : syracuseStep 359579 = 539369) B539369
theorem B2915513 : Blo 235815 2915513 := bstep (se 2 (by rfl) ⟨1093317, by rfl⟩ : syracuseStep 2915513 = 2186635) B2186635
theorem B1015163 : Blo 235815 1015163 := bstep (se 1 (by rfl) ⟨761372, by rfl⟩ : syracuseStep 1015163 = 1522745) B1522745
theorem B1736957 : Blo 235815 1736957 := bstep (se 3 (by rfl) ⟨325679, by rfl⟩ : syracuseStep 1736957 = 651359) B651359
theorem B1311137 : Blo 235815 1311137 := bstep (se 2 (by rfl) ⟨491676, by rfl⟩ : syracuseStep 1311137 = 983353) B983353
theorem B1278935 : Blo 235815 1278935 := bstep (se 1 (by rfl) ⟨959201, by rfl⟩ : syracuseStep 1278935 = 1918403) B1918403
theorem B854009 : Blo 235815 854009 := bstep (se 2 (by rfl) ⟨320253, by rfl⟩ : syracuseStep 854009 = 640507) B640507
theorem B1805003 : Blo 235815 1805003 := bstep (se 1 (by rfl) ⟨1353752, by rfl⟩ : syracuseStep 1805003 = 2707505) B2707505
theorem B20549051 : Blo 235815 20549051 := bstep (se 1 (by rfl) ⟨15411788, by rfl⟩ : syracuseStep 20549051 = 30823577) B30823577
theorem B1511135 : Blo 235815 1511135 := bstep (se 1 (by rfl) ⟨1133351, by rfl⟩ : syracuseStep 1511135 = 2266703) B2266703
theorem B28348645 : Blo 235815 28348645 := bstep (se 4 (by rfl) ⟨2657685, by rfl⟩ : syracuseStep 28348645 = 5315371) B5315371
theorem B856327 : Blo 235815 856327 := bstep (se 1 (by rfl) ⟨642245, by rfl⟩ : syracuseStep 856327 = 1284491) B1284491
theorem B1380635 : Blo 235815 1380635 := bstep (se 1 (by rfl) ⟨1035476, by rfl⟩ : syracuseStep 1380635 = 2070953) B2070953
theorem B2036339 : Blo 235815 2036339 := bstep (se 1 (by rfl) ⟨1527254, by rfl⟩ : syracuseStep 2036339 = 3054509) B3054509
theorem B1020545 : Blo 235815 1020545 := bstep (se 2 (by rfl) ⟨382704, by rfl⟩ : syracuseStep 1020545 = 765409) B765409
theorem B6886133 : Blo 235815 6886133 := bstep (se 5 (by rfl) ⟨322787, by rfl⟩ : syracuseStep 6886133 = 645575) B645575
theorem B3839075 : Blo 235815 3839075 := bstep (se 1 (by rfl) ⟨2879306, by rfl⟩ : syracuseStep 3839075 = 5758613) B5758613
theorem B300343 : Blo 235815 300343 := bstep (se 1 (by rfl) ⟨225257, by rfl⟩ : syracuseStep 300343 = 450515) B450515
theorem B1283435 : Blo 235815 1283435 := bstep (se 1 (by rfl) ⟨962576, by rfl⟩ : syracuseStep 1283435 = 1925153) B1925153
theorem B267727 : Blo 235815 267727 := bstep (se 1 (by rfl) ⟨200795, by rfl⟩ : syracuseStep 267727 = 401591) B401591
theorem B1709885 : Blo 235815 1709885 := bstep (se 3 (by rfl) ⟨320603, by rfl⟩ : syracuseStep 1709885 = 641207) B641207
theorem B399431 : Blo 235815 399431 := bstep (se 1 (by rfl) ⟨299573, by rfl⟩ : syracuseStep 399431 = 599147) B599147
theorem B235903 : Blo 235815 235903 := bstep (se 1 (by rfl) ⟨176927, by rfl⟩ : syracuseStep 235903 = 353855) B353855
theorem B268699 : Blo 235815 268699 := bstep (se 1 (by rfl) ⟨201524, by rfl⟩ : syracuseStep 268699 = 403049) B403049
theorem B236143 : Blo 235815 236143 := bstep (se 1 (by rfl) ⟨177107, by rfl⟩ : syracuseStep 236143 = 354215) B354215
theorem B236223 : Blo 235815 236223 := bstep (se 1 (by rfl) ⟨177167, by rfl⟩ : syracuseStep 236223 = 354335) B354335
theorem B6101729 : Blo 235815 6101729 := bstep (se 2 (by rfl) ⟨2288148, by rfl⟩ : syracuseStep 6101729 = 4576297) B4576297
theorem B531179 : Blo 235815 531179 := bstep (se 1 (by rfl) ⟨398384, by rfl⟩ : syracuseStep 531179 = 796769) B796769
theorem B10263455 : Blo 235815 10263455 := bstep (se 1 (by rfl) ⟨7697591, by rfl⟩ : syracuseStep 10263455 = 15395183) B15395183
theorem B236527 : Blo 235815 236527 := bstep (se 1 (by rfl) ⟨177395, by rfl⟩ : syracuseStep 236527 = 354791) B354791
theorem B531539 : Blo 235815 531539 := bstep (se 1 (by rfl) ⟨398654, by rfl⟩ : syracuseStep 531539 = 797309) B797309
theorem B236647 : Blo 235815 236647 := bstep (se 1 (by rfl) ⟨177485, by rfl⟩ : syracuseStep 236647 = 354971) B354971
theorem B236795 : Blo 235815 236795 := bstep (se 1 (by rfl) ⟨177596, by rfl⟩ : syracuseStep 236795 = 355193) B355193
theorem B10132867 : Blo 235815 10132867 := bstep (se 1 (by rfl) ⟨7599650, by rfl⟩ : syracuseStep 10132867 = 15199301) B15199301
theorem B236959 : Blo 235815 236959 := bstep (se 1 (by rfl) ⟨177719, by rfl⟩ : syracuseStep 236959 = 355439) B355439
theorem B531881 : Blo 235815 531881 := bstep (se 2 (by rfl) ⟨199455, by rfl⟩ : syracuseStep 531881 = 398911) B398911
theorem B237023 : Blo 235815 237023 := bstep (se 1 (by rfl) ⟨177767, by rfl⟩ : syracuseStep 237023 = 355535) B355535
theorem B237103 : Blo 235815 237103 := bstep (se 1 (by rfl) ⟨177827, by rfl⟩ : syracuseStep 237103 = 355655) B355655
theorem B237295 : Blo 235815 237295 := bstep (se 1 (by rfl) ⟨177971, by rfl⟩ : syracuseStep 237295 = 355943) B355943
theorem B2727917 : Blo 235815 2727917 := bstep (se 3 (by rfl) ⟨511484, by rfl⟩ : syracuseStep 2727917 = 1022969) B1022969
theorem B237551 : Blo 235815 237551 := bstep (se 1 (by rfl) ⟨178163, by rfl⟩ : syracuseStep 237551 = 356327) B356327
theorem B401449 : Blo 235815 401449 := bstep (se 2 (by rfl) ⟨150543, by rfl⟩ : syracuseStep 401449 = 301087) B301087
theorem B729143 : Blo 235815 729143 := bstep (se 1 (by rfl) ⟨546857, by rfl⟩ : syracuseStep 729143 = 1093715) B1093715
theorem B237631 : Blo 235815 237631 := bstep (se 1 (by rfl) ⟨178223, by rfl⟩ : syracuseStep 237631 = 356447) B356447
theorem B237671 : Blo 235815 237671 := bstep (se 1 (by rfl) ⟨178253, by rfl⟩ : syracuseStep 237671 = 356507) B356507
theorem B237791 : Blo 235815 237791 := bstep (se 1 (by rfl) ⟨178343, by rfl⟩ : syracuseStep 237791 = 356687) B356687
theorem B237851 : Blo 235815 237851 := bstep (se 1 (by rfl) ⟨178388, by rfl⟩ : syracuseStep 237851 = 356777) B356777
theorem B6136175 : Blo 235815 6136175 := bstep (se 1 (by rfl) ⟨4602131, by rfl⟩ : syracuseStep 6136175 = 9204263) B9204263
theorem B238055 : Blo 235815 238055 := bstep (se 1 (by rfl) ⟨178541, by rfl⟩ : syracuseStep 238055 = 357083) B357083
theorem B1712627 : Blo 235815 1712627 := bstep (se 1 (by rfl) ⟨1284470, by rfl⟩ : syracuseStep 1712627 = 2568941) B2568941
theorem B238235 : Blo 235815 238235 := bstep (se 1 (by rfl) ⟨178676, by rfl⟩ : syracuseStep 238235 = 357353) B357353
theorem B238331 : Blo 235815 238331 := bstep (se 1 (by rfl) ⟨178748, by rfl⟩ : syracuseStep 238331 = 357497) B357497
theorem B238683 : Blo 235815 238683 := bstep (se 1 (by rfl) ⟨179012, by rfl⟩ : syracuseStep 238683 = 358025) B358025
theorem B238823 : Blo 235815 238823 := bstep (se 1 (by rfl) ⟨179117, by rfl⟩ : syracuseStep 238823 = 358235) B358235
theorem B238847 : Blo 235815 238847 := bstep (se 1 (by rfl) ⟨179135, by rfl⟩ : syracuseStep 238847 = 358271) B358271
theorem B238911 : Blo 235815 238911 := bstep (se 1 (by rfl) ⟨179183, by rfl⟩ : syracuseStep 238911 = 358367) B358367
theorem B238951 : Blo 235815 238951 := bstep (se 1 (by rfl) ⟨179213, by rfl⟩ : syracuseStep 238951 = 358427) B358427
theorem B239079 : Blo 235815 239079 := bstep (se 1 (by rfl) ⟨179309, by rfl⟩ : syracuseStep 239079 = 358619) B358619
theorem B239259 : Blo 235815 239259 := bstep (se 1 (by rfl) ⟨179444, by rfl⟩ : syracuseStep 239259 = 358889) B358889
theorem B239519 : Blo 235815 239519 := bstep (se 1 (by rfl) ⟨179639, by rfl⟩ : syracuseStep 239519 = 359279) B359279
theorem B239679 : Blo 235815 239679 := bstep (se 1 (by rfl) ⟨179759, by rfl⟩ : syracuseStep 239679 = 359519) B359519
theorem B239719 : Blo 235815 239719 := bstep (se 1 (by rfl) ⟨179789, by rfl⟩ : syracuseStep 239719 = 359579) B359579
theorem B1943675 : Blo 235815 1943675 := bstep (se 1 (by rfl) ⟨1457756, by rfl⟩ : syracuseStep 1943675 = 2915513) B2915513
theorem B403643 : Blo 235815 403643 := bstep (se 1 (by rfl) ⟨302732, by rfl⟩ : syracuseStep 403643 = 605465) B605465
theorem B600443 : Blo 235815 600443 := bstep (se 1 (by rfl) ⟨450332, by rfl⟩ : syracuseStep 600443 = 900665) B900665
theorem B404203 : Blo 235815 404203 := bstep (se 1 (by rfl) ⟨303152, by rfl⟩ : syracuseStep 404203 = 606305) B606305
theorem B895805 : Blo 235815 895805 := bstep (se 3 (by rfl) ⟨167963, by rfl⟩ : syracuseStep 895805 = 335927) B335927
theorem B404345 : Blo 235815 404345 := bstep (se 2 (by rfl) ⟨151629, by rfl⟩ : syracuseStep 404345 = 303259) B303259
theorem B797579 : Blo 235815 797579 := bstep (se 1 (by rfl) ⟨598184, by rfl⟩ : syracuseStep 797579 = 1196369) B1196369
theorem B4369747 : Blo 235815 4369747 := bstep (se 1 (by rfl) ⟨3277310, by rfl⟩ : syracuseStep 4369747 = 6554621) B6554621
theorem B536255 : Blo 235815 536255 := bstep (se 1 (by rfl) ⟨402191, by rfl⟩ : syracuseStep 536255 = 804383) B804383
theorem B536795 : Blo 235815 536795 := bstep (se 1 (by rfl) ⟨402596, by rfl⟩ : syracuseStep 536795 = 805193) B805193
theorem B798983 : Blo 235815 798983 := bstep (se 1 (by rfl) ⟨599237, by rfl⟩ : syracuseStep 798983 = 1198475) B1198475
theorem B536903 : Blo 235815 536903 := bstep (se 1 (by rfl) ⟨402677, by rfl⟩ : syracuseStep 536903 = 805355) B805355
theorem B1520207 : Blo 235815 1520207 := bstep (se 1 (by rfl) ⟨1140155, by rfl⟩ : syracuseStep 1520207 = 2280311) B2280311
theorem B602761 : Blo 235815 602761 := bstep (se 2 (by rfl) ⟨226035, by rfl⟩ : syracuseStep 602761 = 452071) B452071
theorem B1749815 : Blo 235815 1749815 := bstep (se 1 (by rfl) ⟨1312361, by rfl⟩ : syracuseStep 1749815 = 2624723) B2624723
theorem B505129 : Blo 235815 505129 := bstep (se 2 (by rfl) ⟨189423, by rfl⟩ : syracuseStep 505129 = 378847) B378847
theorem B800063 : Blo 235815 800063 := bstep (se 1 (by rfl) ⟨600047, by rfl⟩ : syracuseStep 800063 = 1200095) B1200095
theorem B538319 : Blo 235815 538319 := bstep (se 1 (by rfl) ⟨403739, by rfl⟩ : syracuseStep 538319 = 807479) B807479
theorem B538451 : Blo 235815 538451 := bstep (se 1 (by rfl) ⟨403838, by rfl⟩ : syracuseStep 538451 = 807677) B807677
theorem B538559 : Blo 235815 538559 := bstep (se 1 (by rfl) ⟨403919, by rfl⟩ : syracuseStep 538559 = 807839) B807839
theorem B505847 : Blo 235815 505847 := bstep (se 1 (by rfl) ⟨379385, by rfl⟩ : syracuseStep 505847 = 758771) B758771
theorem B604199 : Blo 235815 604199 := bstep (se 1 (by rfl) ⟨453149, by rfl⟩ : syracuseStep 604199 = 906299) B906299
theorem B538811 : Blo 235815 538811 := bstep (se 1 (by rfl) ⟨404108, by rfl⟩ : syracuseStep 538811 = 808217) B808217
theorem B16694191 : Blo 235815 16694191 := bstep (se 1 (by rfl) ⟨12520643, by rfl⟩ : syracuseStep 16694191 = 25041287) B25041287
theorem B3849257 : Blo 235815 3849257 := bstep (se 2 (by rfl) ⟨1443471, by rfl⟩ : syracuseStep 3849257 = 2886943) B2886943
theorem B4045949 : Blo 235815 4045949 := bstep (se 3 (by rfl) ⟨758615, by rfl⟩ : syracuseStep 4045949 = 1517231) B1517231
theorem B801953 : Blo 235815 801953 := bstep (se 2 (by rfl) ⟨300732, by rfl⟩ : syracuseStep 801953 = 601465) B601465
theorem B1031837 : Blo 235815 1031837 := bstep (se 3 (by rfl) ⟨193469, by rfl⟩ : syracuseStep 1031837 = 386939) B386939
theorem B1457875 : Blo 235815 1457875 := bstep (se 1 (by rfl) ⟨1093406, by rfl⟩ : syracuseStep 1457875 = 2186813) B2186813
theorem B1556221 : Blo 235815 1556221 := bstep (se 3 (by rfl) ⟨291791, by rfl⟩ : syracuseStep 1556221 = 583583) B583583
theorem B966647 : Blo 235815 966647 := bstep (se 1 (by rfl) ⟨724985, by rfl⟩ : syracuseStep 966647 = 1449971) B1449971
theorem B3326035 : Blo 235815 3326035 := bstep (se 1 (by rfl) ⟨2494526, by rfl⟩ : syracuseStep 3326035 = 4989053) B4989053
theorem B672047 : Blo 235815 672047 := bstep (se 1 (by rfl) ⟨504035, by rfl⟩ : syracuseStep 672047 = 1008071) B1008071
theorem B7324445 : Blo 235815 7324445 := bstep (se 3 (by rfl) ⟨1373333, by rfl⟩ : syracuseStep 7324445 = 2746667) B2746667
theorem B52937545 : Blo 235815 52937545 := bstep (se 2 (by rfl) ⟨19851579, by rfl⟩ : syracuseStep 52937545 = 39703159) B39703159
theorem B902441 : Blo 235815 902441 := bstep (se 2 (by rfl) ⟨338415, by rfl⟩ : syracuseStep 902441 = 676831) B676831
theorem B804599 : Blo 235815 804599 := bstep (se 1 (by rfl) ⟨603449, by rfl⟩ : syracuseStep 804599 = 1206899) B1206899
theorem B2213689 : Blo 235815 2213689 := bstep (se 2 (by rfl) ⟨830133, by rfl⟩ : syracuseStep 2213689 = 1660267) B1660267
theorem B903383 : Blo 235815 903383 := bstep (se 1 (by rfl) ⟨677537, by rfl⟩ : syracuseStep 903383 = 1355075) B1355075
theorem B805679 : Blo 235815 805679 := bstep (se 1 (by rfl) ⟨604259, by rfl⟩ : syracuseStep 805679 = 1208519) B1208519
theorem B1723265 : Blo 235815 1723265 := bstep (se 2 (by rfl) ⟨646224, by rfl⟩ : syracuseStep 1723265 = 1292449) B1292449
theorem B1166663 : Blo 235815 1166663 := bstep (se 1 (by rfl) ⟨874997, by rfl⟩ : syracuseStep 1166663 = 1749995) B1749995
theorem B380231 : Blo 235815 380231 := bstep (se 1 (by rfl) ⟨285173, by rfl⟩ : syracuseStep 380231 = 570347) B570347
theorem B675145 : Blo 235815 675145 := bstep (se 2 (by rfl) ⟨253179, by rfl⟩ : syracuseStep 675145 = 506359) B506359
theorem B1199447 : Blo 235815 1199447 := bstep (se 1 (by rfl) ⟨899585, by rfl⟩ : syracuseStep 1199447 = 1799171) B1799171
theorem B2018849 : Blo 235815 2018849 := bstep (se 2 (by rfl) ⟨757068, by rfl⟩ : syracuseStep 2018849 = 1514137) B1514137
theorem B6114851 : Blo 235815 6114851 := bstep (se 1 (by rfl) ⟨4586138, by rfl⟩ : syracuseStep 6114851 = 9172277) B9172277
theorem B806543 : Blo 235815 806543 := bstep (se 1 (by rfl) ⟨604907, by rfl⟩ : syracuseStep 806543 = 1209815) B1209815
theorem B806651 : Blo 235815 806651 := bstep (se 1 (by rfl) ⟨604988, by rfl⟩ : syracuseStep 806651 = 1209977) B1209977
theorem B806975 : Blo 235815 806975 := bstep (se 1 (by rfl) ⟨605231, by rfl⟩ : syracuseStep 806975 = 1210463) B1210463
theorem B905539 : Blo 235815 905539 := bstep (se 1 (by rfl) ⟨679154, by rfl⟩ : syracuseStep 905539 = 1358309) B1358309
theorem B512335 : Blo 235815 512335 := bstep (se 1 (by rfl) ⟨384251, by rfl⟩ : syracuseStep 512335 = 768503) B768503
theorem B3068603 : Blo 235815 3068603 := bstep (se 1 (by rfl) ⟨2301452, by rfl⟩ : syracuseStep 3068603 = 4602905) B4602905
theorem B906011 : Blo 235815 906011 := bstep (se 1 (by rfl) ⟨679508, by rfl⟩ : syracuseStep 906011 = 1359017) B1359017
theorem B676775 : Blo 235815 676775 := bstep (se 1 (by rfl) ⟨507581, by rfl⟩ : syracuseStep 676775 = 1015163) B1015163
theorem B1922555 : Blo 235815 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B2578063 : Blo 235815 2578063 := bstep (se 1 (by rfl) ⟨1933547, by rfl⟩ : syracuseStep 2578063 = 3867095) B3867095
theorem B677879 : Blo 235815 677879 := bstep (se 1 (by rfl) ⟨508409, by rfl⟩ : syracuseStep 677879 = 1016819) B1016819
theorem B1202363 : Blo 235815 1202363 := bstep (se 1 (by rfl) ⟨901772, by rfl⟩ : syracuseStep 1202363 = 1803545) B1803545
theorem B252667 : Blo 235815 252667 := bstep (se 1 (by rfl) ⟨189500, by rfl⟩ : syracuseStep 252667 = 379001) B379001
theorem B2022155 : Blo 235815 2022155 := bstep (se 1 (by rfl) ⟨1516616, by rfl⟩ : syracuseStep 2022155 = 3033233) B3033233
theorem B2022839 : Blo 235815 2022839 := bstep (se 1 (by rfl) ⟨1517129, by rfl⟩ : syracuseStep 2022839 = 3034259) B3034259
theorem B1728107 : Blo 235815 1728107 := bstep (se 1 (by rfl) ⟨1296080, by rfl⟩ : syracuseStep 1728107 = 2592161) B2592161
theorem B1990307 : Blo 235815 1990307 := bstep (se 1 (by rfl) ⟨1492730, by rfl⟩ : syracuseStep 1990307 = 2985461) B2985461
theorem B3301073 : Blo 235815 3301073 := bstep (se 2 (by rfl) ⟨1237902, by rfl⟩ : syracuseStep 3301073 = 2475805) B2475805
theorem B2285657 : Blo 235815 2285657 := bstep (se 2 (by rfl) ⟨857121, by rfl⟩ : syracuseStep 2285657 = 1714243) B1714243
theorem B1794797 : Blo 235815 1794797 := bstep (se 3 (by rfl) ⟨336524, by rfl⟩ : syracuseStep 1794797 = 673049) B673049
theorem B1008875 : Blo 235815 1008875 := bstep (se 1 (by rfl) ⟨756656, by rfl⟩ : syracuseStep 1008875 = 1513313) B1513313
theorem B386537 : Blo 235815 386537 := bstep (se 2 (by rfl) ⟨144951, by rfl⟩ : syracuseStep 386537 = 289903) B289903
theorem B354023 : Blo 235815 354023 := bstep (se 1 (by rfl) ⟨265517, by rfl⟩ : syracuseStep 354023 = 531035) B531035
theorem B1206251 : Blo 235815 1206251 := bstep (se 1 (by rfl) ⟨904688, by rfl⟩ : syracuseStep 1206251 = 1809377) B1809377
theorem B2549951 : Blo 235815 2549951 := bstep (se 1 (by rfl) ⟨1912463, by rfl⟩ : syracuseStep 2549951 = 3824927) B3824927
theorem B2156777 : Blo 235815 2156777 := bstep (se 2 (by rfl) ⟨808791, by rfl⟩ : syracuseStep 2156777 = 1617583) B1617583
theorem B452891 : Blo 235815 452891 := bstep (se 1 (by rfl) ⟨339668, by rfl⟩ : syracuseStep 452891 = 679337) B679337
theorem B682663 : Blo 235815 682663 := bstep (se 1 (by rfl) ⟨511997, by rfl⟩ : syracuseStep 682663 = 1023995) B1023995
theorem B3238667 : Blo 235815 3238667 := bstep (se 1 (by rfl) ⟨2429000, by rfl⟩ : syracuseStep 3238667 = 4858001) B4858001
theorem B355241 : Blo 235815 355241 := bstep (se 2 (by rfl) ⟨133215, by rfl⟩ : syracuseStep 355241 = 266431) B266431
theorem B355355 : Blo 235815 355355 := bstep (se 1 (by rfl) ⟨266516, by rfl⟩ : syracuseStep 355355 = 533033) B533033
theorem B355559 : Blo 235815 355559 := bstep (se 1 (by rfl) ⟨266669, by rfl⟩ : syracuseStep 355559 = 533339) B533339
theorem B355775 : Blo 235815 355775 := bstep (se 1 (by rfl) ⟨266831, by rfl⟩ : syracuseStep 355775 = 533663) B533663
theorem B2551333 : Blo 235815 2551333 := bstep (se 4 (by rfl) ⟨239187, by rfl⟩ : syracuseStep 2551333 = 478375) B478375
theorem B356207 : Blo 235815 356207 := bstep (se 1 (by rfl) ⟨267155, by rfl⟩ : syracuseStep 356207 = 534311) B534311
theorem B356459 : Blo 235815 356459 := bstep (se 1 (by rfl) ⟨267344, by rfl⟩ : syracuseStep 356459 = 534689) B534689
theorem B2290457 : Blo 235815 2290457 := bstep (se 2 (by rfl) ⟨858921, by rfl⟩ : syracuseStep 2290457 = 1717843) B1717843
theorem B6845309 : Blo 235815 6845309 := bstep (se 3 (by rfl) ⟨1283495, by rfl⟩ : syracuseStep 6845309 = 2566991) B2566991
theorem B357311 : Blo 235815 357311 := bstep (se 1 (by rfl) ⟨267983, by rfl⟩ : syracuseStep 357311 = 535967) B535967
theorem B357359 : Blo 235815 357359 := bstep (se 1 (by rfl) ⟨268019, by rfl⟩ : syracuseStep 357359 = 536039) B536039
theorem B357995 : Blo 235815 357995 := bstep (se 1 (by rfl) ⟨268496, by rfl⟩ : syracuseStep 357995 = 536993) B536993
theorem B7665299 : Blo 235815 7665299 := bstep (se 1 (by rfl) ⟨5748974, by rfl⟩ : syracuseStep 7665299 = 11497949) B11497949
theorem B13826419 : Blo 235815 13826419 := bstep (se 1 (by rfl) ⟨10369814, by rfl⟩ : syracuseStep 13826419 = 20739629) B20739629
theorem B916049 : Blo 235815 916049 := bstep (se 2 (by rfl) ⟨343518, by rfl⟩ : syracuseStep 916049 = 687037) B687037
theorem B359015 : Blo 235815 359015 := bstep (se 1 (by rfl) ⟨269261, by rfl⟩ : syracuseStep 359015 = 538523) B538523
theorem B818345 : Blo 235815 818345 := bstep (se 2 (by rfl) ⟨306879, by rfl⟩ : syracuseStep 818345 = 613759) B613759
theorem B1801601 : Blo 235815 1801601 := bstep (se 2 (by rfl) ⟨675600, by rfl⟩ : syracuseStep 1801601 = 1351201) B1351201
theorem B4882963 : Blo 235815 4882963 := bstep (se 1 (by rfl) ⟨3662222, by rfl⟩ : syracuseStep 4882963 = 7324445) B7324445
theorem B852623 : Blo 235815 852623 := bstep (se 1 (by rfl) ⟨639467, by rfl⟩ : syracuseStep 852623 = 1278935) B1278935
theorem B70583393 : Blo 235815 70583393 := bstep (se 2 (by rfl) ⟨26468772, by rfl⟩ : syracuseStep 70583393 = 52937545) B52937545
theorem B1148843 : Blo 235815 1148843 := bstep (se 1 (by rfl) ⟨861632, by rfl⟩ : syracuseStep 1148843 = 1723265) B1723265
theorem B13699367 : Blo 235815 13699367 := bstep (se 1 (by rfl) ⟨10274525, by rfl⟩ : syracuseStep 13699367 = 20549051) B20549051
theorem B2951585 : Blo 235815 2951585 := bstep (se 2 (by rfl) ⟨1106844, by rfl⟩ : syracuseStep 2951585 = 2213689) B2213689
theorem B920423 : Blo 235815 920423 := bstep (se 1 (by rfl) ⟨690317, by rfl⟩ : syracuseStep 920423 = 1380635) B1380635
theorem B4590755 : Blo 235815 4590755 := bstep (se 1 (by rfl) ⟨3443066, by rfl⟩ : syracuseStep 4590755 = 6886133) B6886133
theorem B2559383 : Blo 235815 2559383 := bstep (se 1 (by rfl) ⟨1919537, by rfl⟩ : syracuseStep 2559383 = 3839075) B3839075
theorem B855623 : Blo 235815 855623 := bstep (se 1 (by rfl) ⟨641717, by rfl⟩ : syracuseStep 855623 = 1283435) B1283435
theorem B1281703 : Blo 235815 1281703 := bstep (se 1 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 1281703 = 1922555) B1922555
theorem B266287 : Blo 235815 266287 := bstep (se 1 (by rfl) ⟨199715, by rfl⟩ : syracuseStep 266287 = 399431) B399431
theorem B4067819 : Blo 235815 4067819 := bstep (se 1 (by rfl) ⟨3050864, by rfl⟩ : syracuseStep 4067819 = 6101729) B6101729
theorem B1348103 : Blo 235815 1348103 := bstep (se 1 (by rfl) ⟨1011077, by rfl⟩ : syracuseStep 1348103 = 2022155) B2022155
theorem B604771093 : Blo 235815 604771093 := bstep (se 6 (by rfl) ⟨14174322, by rfl⟩ : syracuseStep 604771093 = 28348645) B28348645
theorem B1348559 : Blo 235815 1348559 := bstep (se 1 (by rfl) ⟨1011419, by rfl⟩ : syracuseStep 1348559 = 2022839) B2022839
theorem B1152071 : Blo 235815 1152071 := bstep (se 1 (by rfl) ⟨864053, by rfl⟩ : syracuseStep 1152071 = 1728107) B1728107
theorem B2200715 : Blo 235815 2200715 := bstep (se 1 (by rfl) ⟨1650536, by rfl⟩ : syracuseStep 2200715 = 3301073) B3301073
theorem B236015 : Blo 235815 236015 := bstep (se 1 (by rfl) ⟨177011, by rfl⟩ : syracuseStep 236015 = 354023) B354023
theorem B269095 : Blo 235815 269095 := bstep (se 1 (by rfl) ⟨201821, by rfl⟩ : syracuseStep 269095 = 403643) B403643
theorem B400295 : Blo 235815 400295 := bstep (se 1 (by rfl) ⟨300221, by rfl⟩ : syracuseStep 400295 = 600443) B600443
theorem B400457 : Blo 235815 400457 := bstep (se 2 (by rfl) ⟨150171, by rfl⟩ : syracuseStep 400457 = 300343) B300343
theorem B597203 : Blo 235815 597203 := bstep (se 1 (by rfl) ⟨447902, by rfl⟩ : syracuseStep 597203 = 895805) B895805
theorem B269563 : Blo 235815 269563 := bstep (se 1 (by rfl) ⟨202172, by rfl⟩ : syracuseStep 269563 = 404345) B404345
theorem B531719 : Blo 235815 531719 := bstep (se 1 (by rfl) ⟨398789, by rfl⟩ : syracuseStep 531719 = 797579) B797579
theorem B236827 : Blo 235815 236827 := bstep (se 1 (by rfl) ⟨177620, by rfl⟩ : syracuseStep 236827 = 355241) B355241
theorem B236903 : Blo 235815 236903 := bstep (se 1 (by rfl) ⟨177677, by rfl⟩ : syracuseStep 236903 = 355355) B355355
theorem B237039 : Blo 235815 237039 := bstep (se 1 (by rfl) ⟨177779, by rfl⟩ : syracuseStep 237039 = 355559) B355559
theorem B237183 : Blo 235815 237183 := bstep (se 1 (by rfl) ⟨177887, by rfl⟩ : syracuseStep 237183 = 355775) B355775
theorem B237471 : Blo 235815 237471 := bstep (se 1 (by rfl) ⟨178103, by rfl⟩ : syracuseStep 237471 = 356207) B356207
theorem B237639 : Blo 235815 237639 := bstep (se 1 (by rfl) ⟨178229, by rfl⟩ : syracuseStep 237639 = 356459) B356459
theorem B532655 : Blo 235815 532655 := bstep (se 1 (by rfl) ⟨399491, by rfl⟩ : syracuseStep 532655 = 798983) B798983
theorem B4563539 : Blo 235815 4563539 := bstep (se 1 (by rfl) ⟨3422654, by rfl⟩ : syracuseStep 4563539 = 6845309) B6845309
theorem B238207 : Blo 235815 238207 := bstep (se 1 (by rfl) ⟨178655, by rfl⟩ : syracuseStep 238207 = 357311) B357311
theorem B238239 : Blo 235815 238239 := bstep (se 1 (by rfl) ⟨178679, by rfl⟩ : syracuseStep 238239 = 357359) B357359
theorem B533375 : Blo 235815 533375 := bstep (se 1 (by rfl) ⟨400031, by rfl⟩ : syracuseStep 533375 = 800063) B800063
theorem B336889 : Blo 235815 336889 := bstep (se 2 (by rfl) ⟨126333, by rfl⟩ : syracuseStep 336889 = 252667) B252667
theorem B238663 : Blo 235815 238663 := bstep (se 1 (by rfl) ⟨178997, by rfl⟩ : syracuseStep 238663 = 357995) B357995
theorem B22258921 : Blo 235815 22258921 := bstep (se 2 (by rfl) ⟨8347095, by rfl⟩ : syracuseStep 22258921 = 16694191) B16694191
theorem B337231 : Blo 235815 337231 := bstep (se 1 (by rfl) ⟨252923, by rfl⟩ : syracuseStep 337231 = 505847) B505847
theorem B402799 : Blo 235815 402799 := bstep (se 1 (by rfl) ⟨302099, by rfl⟩ : syracuseStep 402799 = 604199) B604199
theorem B5383597 : Blo 235815 5383597 := bstep (se 3 (by rfl) ⟨1009424, by rfl⟩ : syracuseStep 5383597 = 2018849) B2018849
theorem B239343 : Blo 235815 239343 := bstep (se 1 (by rfl) ⟨179507, by rfl⟩ : syracuseStep 239343 = 359015) B359015
theorem B13510489 : Blo 235815 13510489 := bstep (se 2 (by rfl) ⟨5066433, by rfl⟩ : syracuseStep 13510489 = 10132867) B10132867
theorem B2566171 : Blo 235815 2566171 := bstep (se 1 (by rfl) ⟨1924628, by rfl⟩ : syracuseStep 2566171 = 3849257) B3849257
theorem B2697299 : Blo 235815 2697299 := bstep (se 1 (by rfl) ⟨2022974, by rfl⟩ : syracuseStep 2697299 = 4045949) B4045949
theorem B534635 : Blo 235815 534635 := bstep (se 1 (by rfl) ⟨400976, by rfl⟩ : syracuseStep 534635 = 801953) B801953
theorem B1943833 : Blo 235815 1943833 := bstep (se 2 (by rfl) ⟨728937, by rfl⟩ : syracuseStep 1943833 = 1457875) B1457875
theorem B2074961 : Blo 235815 2074961 := bstep (se 2 (by rfl) ⟨778110, by rfl⟩ : syracuseStep 2074961 = 1556221) B1556221
theorem B535265 : Blo 235815 535265 := bstep (se 2 (by rfl) ⟨200724, by rfl⟩ : syracuseStep 535265 = 401449) B401449
theorem B4434713 : Blo 235815 4434713 := bstep (se 2 (by rfl) ⟨1663017, by rfl⟩ : syracuseStep 4434713 = 3326035) B3326035
theorem B1157971 : Blo 235815 1157971 := bstep (se 1 (by rfl) ⟨868478, by rfl⟩ : syracuseStep 1157971 = 1736957) B1736957
theorem B601627 : Blo 235815 601627 := bstep (se 1 (by rfl) ⟨451220, by rfl⟩ : syracuseStep 601627 = 902441) B902441
theorem B536399 : Blo 235815 536399 := bstep (se 1 (by rfl) ⟨402299, by rfl⟩ : syracuseStep 536399 = 804599) B804599
theorem B569339 : Blo 235815 569339 := bstep (se 1 (by rfl) ⟨427004, by rfl⟩ : syracuseStep 569339 = 854009) B854009
theorem B602255 : Blo 235815 602255 := bstep (se 1 (by rfl) ⟨451691, by rfl⟩ : syracuseStep 602255 = 903383) B903383
theorem B2732453 : Blo 235815 2732453 := bstep (se 4 (by rfl) ⟨256167, by rfl⟩ : syracuseStep 2732453 = 512335) B512335
theorem B537119 : Blo 235815 537119 := bstep (se 1 (by rfl) ⟨402839, by rfl⟩ : syracuseStep 537119 = 805679) B805679
theorem B73740901 : Blo 235815 73740901 := bstep (se 4 (by rfl) ⟨6913209, by rfl⟩ : syracuseStep 73740901 = 13826419) B13826419
theorem B799631 : Blo 235815 799631 := bstep (se 1 (by rfl) ⟨599723, by rfl⟩ : syracuseStep 799631 = 1199447) B1199447
theorem B4076567 : Blo 235815 4076567 := bstep (se 1 (by rfl) ⟨3057425, by rfl⟩ : syracuseStep 4076567 = 6114851) B6114851
theorem B537695 : Blo 235815 537695 := bstep (se 1 (by rfl) ⟨403271, by rfl⟩ : syracuseStep 537695 = 806543) B806543
theorem B537767 : Blo 235815 537767 := bstep (se 1 (by rfl) ⟨403325, by rfl⟩ : syracuseStep 537767 = 806651) B806651
theorem B537983 : Blo 235815 537983 := bstep (se 1 (by rfl) ⟨403487, by rfl⟩ : syracuseStep 537983 = 806975) B806975
theorem B1357559 : Blo 235815 1357559 := bstep (se 1 (by rfl) ⟨1018169, by rfl⟩ : syracuseStep 1357559 = 2036339) B2036339
theorem B2045735 : Blo 235815 2045735 := bstep (se 1 (by rfl) ⟨1534301, by rfl⟩ : syracuseStep 2045735 = 3068603) B3068603
theorem B604007 : Blo 235815 604007 := bstep (se 1 (by rfl) ⟨453005, by rfl⟩ : syracuseStep 604007 = 906011) B906011
theorem B538937 : Blo 235815 538937 := bstep (se 2 (by rfl) ⟨202101, by rfl⟩ : syracuseStep 538937 = 404203) B404203
theorem B1030765 : Blo 235815 1030765 := bstep (se 3 (by rfl) ⟨193268, by rfl⟩ : syracuseStep 1030765 = 386537) B386537
theorem B801575 : Blo 235815 801575 := bstep (se 1 (by rfl) ⟨601181, by rfl⟩ : syracuseStep 801575 = 1202363) B1202363
theorem B900193 : Blo 235815 900193 := bstep (se 2 (by rfl) ⟨337572, by rfl⟩ : syracuseStep 900193 = 675145) B675145
theorem B1326871 : Blo 235815 1326871 := bstep (se 1 (by rfl) ⟨995153, by rfl⟩ : syracuseStep 1326871 = 1990307) B1990307
theorem B1818611 : Blo 235815 1818611 := bstep (se 1 (by rfl) ⟨1363958, by rfl⟩ : syracuseStep 1818611 = 2727917) B2727917
theorem B1523771 : Blo 235815 1523771 := bstep (se 1 (by rfl) ⟨1142828, by rfl⟩ : syracuseStep 1523771 = 2285657) B2285657
theorem B1196531 : Blo 235815 1196531 := bstep (se 1 (by rfl) ⟨897398, by rfl⟩ : syracuseStep 1196531 = 1794797) B1794797
theorem B672583 : Blo 235815 672583 := bstep (se 1 (by rfl) ⟨504437, by rfl⟩ : syracuseStep 672583 = 1008875) B1008875
theorem B803681 : Blo 235815 803681 := bstep (se 2 (by rfl) ⟨301380, by rfl⟩ : syracuseStep 803681 = 602761) B602761
theorem B804167 : Blo 235815 804167 := bstep (se 1 (by rfl) ⟨603125, by rfl⟩ : syracuseStep 804167 = 1206251) B1206251
theorem B1295783 : Blo 235815 1295783 := bstep (se 1 (by rfl) ⟨971837, by rfl⟩ : syracuseStep 1295783 = 1943675) B1943675
theorem B2442797 : Blo 235815 2442797 := bstep (se 3 (by rfl) ⟨458024, by rfl⟩ : syracuseStep 2442797 = 916049) B916049
theorem B673505 : Blo 235815 673505 := bstep (se 2 (by rfl) ⟨252564, by rfl⟩ : syracuseStep 673505 = 505129) B505129
theorem B1526971 : Blo 235815 1526971 := bstep (se 1 (by rfl) ⟨1145228, by rfl⟩ : syracuseStep 1526971 = 2290457) B2290457
theorem B1166543 : Blo 235815 1166543 := bstep (se 1 (by rfl) ⟨874907, by rfl⟩ : syracuseStep 1166543 = 1749815) B1749815
theorem B545563 : Blo 235815 545563 := bstep (se 1 (by rfl) ⟨409172, by rfl⟩ : syracuseStep 545563 = 818345) B818345
theorem B1201067 : Blo 235815 1201067 := bstep (se 1 (by rfl) ⟨900800, by rfl⟩ : syracuseStep 1201067 = 1801601) B1801601
theorem B644431 : Blo 235815 644431 := bstep (se 1 (by rfl) ⟨483323, by rfl⟩ : syracuseStep 644431 = 966647) B966647
theorem B448031 : Blo 235815 448031 := bstep (se 1 (by rfl) ⟨336023, by rfl⟩ : syracuseStep 448031 = 672047) B672047
theorem B874091 : Blo 235815 874091 := bstep (se 1 (by rfl) ⟨655568, by rfl⟩ : syracuseStep 874091 = 1311137) B1311137
theorem B1203335 : Blo 235815 1203335 := bstep (se 1 (by rfl) ⟨902501, by rfl⟩ : syracuseStep 1203335 = 1805003) B1805003
theorem B777775 : Blo 235815 777775 := bstep (se 1 (by rfl) ⟨583331, by rfl⟩ : syracuseStep 777775 = 1166663) B1166663
theorem B253487 : Blo 235815 253487 := bstep (se 1 (by rfl) ⟨190115, by rfl⟩ : syracuseStep 253487 = 380231) B380231
theorem B1007423 : Blo 235815 1007423 := bstep (se 1 (by rfl) ⟨755567, by rfl⟩ : syracuseStep 1007423 = 1511135) B1511135
theorem B680363 : Blo 235815 680363 := bstep (se 1 (by rfl) ⟨510272, by rfl⟩ : syracuseStep 680363 = 1020545) B1020545
theorem B451183 : Blo 235815 451183 := bstep (se 1 (by rfl) ⟨338387, by rfl⟩ : syracuseStep 451183 = 676775) B676775
theorem B910217 : Blo 235815 910217 := bstep (se 2 (by rfl) ⟨341331, by rfl⟩ : syracuseStep 910217 = 682663) B682663
theorem B1139923 : Blo 235815 1139923 := bstep (se 1 (by rfl) ⟨854942, by rfl⟩ : syracuseStep 1139923 = 1709885) B1709885
theorem B451919 : Blo 235815 451919 := bstep (se 1 (by rfl) ⟨338939, by rfl⟩ : syracuseStep 451919 = 677879) B677879
theorem B5826329 : Blo 235815 5826329 := bstep (se 2 (by rfl) ⟨2184873, by rfl⟩ : syracuseStep 5826329 = 4369747) B4369747
theorem B354119 : Blo 235815 354119 := bstep (se 1 (by rfl) ⟨265589, by rfl⟩ : syracuseStep 354119 = 531179) B531179
theorem B6842303 : Blo 235815 6842303 := bstep (se 1 (by rfl) ⟨5131727, by rfl⟩ : syracuseStep 6842303 = 10263455) B10263455
theorem B3401777 : Blo 235815 3401777 := bstep (se 2 (by rfl) ⟨1275666, by rfl⟩ : syracuseStep 3401777 = 2551333) B2551333
theorem B354359 : Blo 235815 354359 := bstep (se 1 (by rfl) ⟨265769, by rfl⟩ : syracuseStep 354359 = 531539) B531539
theorem B354587 : Blo 235815 354587 := bstep (se 1 (by rfl) ⟨265940, by rfl⟩ : syracuseStep 354587 = 531881) B531881
theorem B486095 : Blo 235815 486095 := bstep (se 1 (by rfl) ⟨364571, by rfl⟩ : syracuseStep 486095 = 729143) B729143
theorem B4090783 : Blo 235815 4090783 := bstep (se 1 (by rfl) ⟨3068087, by rfl⟩ : syracuseStep 4090783 = 6136175) B6136175
theorem B1141751 : Blo 235815 1141751 := bstep (se 1 (by rfl) ⟨856313, by rfl⟩ : syracuseStep 1141751 = 1712627) B1712627
theorem B1141769 : Blo 235815 1141769 := bstep (se 2 (by rfl) ⟨428163, by rfl⟩ : syracuseStep 1141769 = 856327) B856327
theorem B1207385 : Blo 235815 1207385 := bstep (se 2 (by rfl) ⟨452769, by rfl⟩ : syracuseStep 1207385 = 905539) B905539
theorem B1207709 : Blo 235815 1207709 := bstep (se 3 (by rfl) ⟨226445, by rfl⟩ : syracuseStep 1207709 = 452891) B452891
theorem B1699967 : Blo 235815 1699967 := bstep (se 1 (by rfl) ⟨1274975, by rfl⟩ : syracuseStep 1699967 = 2549951) B2549951
theorem B1437851 : Blo 235815 1437851 := bstep (se 1 (by rfl) ⟨1078388, by rfl⟩ : syracuseStep 1437851 = 2156777) B2156777
theorem B2159111 : Blo 235815 2159111 := bstep (se 1 (by rfl) ⟨1619333, by rfl⟩ : syracuseStep 2159111 = 3238667) B3238667
theorem B356969 : Blo 235815 356969 := bstep (se 2 (by rfl) ⟨133863, by rfl⟩ : syracuseStep 356969 = 267727) B267727
theorem B3437417 : Blo 235815 3437417 := bstep (se 2 (by rfl) ⟨1289031, by rfl⟩ : syracuseStep 3437417 = 2578063) B2578063
theorem B357503 : Blo 235815 357503 := bstep (se 1 (by rfl) ⟨268127, by rfl⟩ : syracuseStep 357503 = 536255) B536255
theorem B357863 : Blo 235815 357863 := bstep (se 1 (by rfl) ⟨268397, by rfl⟩ : syracuseStep 357863 = 536795) B536795
theorem B357935 : Blo 235815 357935 := bstep (se 1 (by rfl) ⟨268451, by rfl⟩ : syracuseStep 357935 = 536903) B536903
theorem B1013471 : Blo 235815 1013471 := bstep (se 1 (by rfl) ⟨760103, by rfl⟩ : syracuseStep 1013471 = 1520207) B1520207
theorem B358265 : Blo 235815 358265 := bstep (se 2 (by rfl) ⟨134349, by rfl⟩ : syracuseStep 358265 = 268699) B268699
theorem B5110199 : Blo 235815 5110199 := bstep (se 1 (by rfl) ⟨3832649, by rfl⟩ : syracuseStep 5110199 = 7665299) B7665299
theorem B358879 : Blo 235815 358879 := bstep (se 1 (by rfl) ⟨269159, by rfl⟩ : syracuseStep 358879 = 538319) B538319
theorem B358967 : Blo 235815 358967 := bstep (se 1 (by rfl) ⟨269225, by rfl⟩ : syracuseStep 358967 = 538451) B538451
theorem B359039 : Blo 235815 359039 := bstep (se 1 (by rfl) ⟨269279, by rfl⟩ : syracuseStep 359039 = 538559) B538559
theorem B359207 : Blo 235815 359207 := bstep (se 1 (by rfl) ⟨269405, by rfl⟩ : syracuseStep 359207 = 538811) B538811
theorem B2751565 : Blo 235815 2751565 := bstep (se 3 (by rfl) ⟨515918, by rfl⟩ : syracuseStep 2751565 = 1031837) B1031837
theorem B1015847 : Blo 235815 1015847 := bstep (se 1 (by rfl) ⟨761885, by rfl⟩ : syracuseStep 1015847 = 1523771) B1523771
theorem B47055595 : Blo 235815 47055595 := bstep (se 1 (by rfl) ⟨35291696, by rfl⟩ : syracuseStep 47055595 = 70583393) B70583393
theorem B1967723 : Blo 235815 1967723 := bstep (se 1 (by rfl) ⟨1475792, by rfl⟩ : syracuseStep 1967723 = 2951585) B2951585
theorem B7178129 : Blo 235815 7178129 := bstep (se 2 (by rfl) ⟨2691798, by rfl⟩ : syracuseStep 7178129 = 5383597) B5383597
theorem B1706255 : Blo 235815 1706255 := bstep (se 1 (by rfl) ⟨1279691, by rfl⟩ : syracuseStep 1706255 = 2559383) B2559383
theorem B2591777 : Blo 235815 2591777 := bstep (se 2 (by rfl) ⟨971916, by rfl⟩ : syracuseStep 2591777 = 1943833) B1943833
theorem B1543961 : Blo 235815 1543961 := bstep (se 2 (by rfl) ⟨578985, by rfl⟩ : syracuseStep 1543961 = 1157971) B1157971
theorem B2035961 : Blo 235815 2035961 := bstep (se 2 (by rfl) ⟨763485, by rfl⟩ : syracuseStep 2035961 = 1526971) B1526971
theorem B266863 : Blo 235815 266863 := bstep (se 1 (by rfl) ⟨200147, by rfl⟩ : syracuseStep 266863 = 400295) B400295
theorem B266971 : Blo 235815 266971 := bstep (se 1 (by rfl) ⟨200228, by rfl⟩ : syracuseStep 266971 = 400457) B400457
theorem B398135 : Blo 235815 398135 := bstep (se 1 (by rfl) ⟨298601, by rfl⟩ : syracuseStep 398135 = 597203) B597203
theorem B1708937 : Blo 235815 1708937 := bstep (se 2 (by rfl) ⟨640851, by rfl⟩ : syracuseStep 1708937 = 1281703) B1281703
theorem B727417 : Blo 235815 727417 := bstep (se 2 (by rfl) ⟨272781, by rfl⟩ : syracuseStep 727417 = 545563) B545563
theorem B236079 : Blo 235815 236079 := bstep (se 1 (by rfl) ⟨177059, by rfl⟩ : syracuseStep 236079 = 354119) B354119
theorem B4561535 : Blo 235815 4561535 := bstep (se 1 (by rfl) ⟨3421151, by rfl⟩ : syracuseStep 4561535 = 6842303) B6842303
theorem B2267851 : Blo 235815 2267851 := bstep (se 1 (by rfl) ⟨1700888, by rfl⟩ : syracuseStep 2267851 = 3401777) B3401777
theorem B236239 : Blo 235815 236239 := bstep (se 1 (by rfl) ⟨177179, by rfl⟩ : syracuseStep 236239 = 354359) B354359
theorem B236391 : Blo 235815 236391 := bstep (se 1 (by rfl) ⟨177293, by rfl⟩ : syracuseStep 236391 = 354587) B354587
theorem B1383307 : Blo 235815 1383307 := bstep (se 1 (by rfl) ⟨1037480, by rfl⟩ : syracuseStep 1383307 = 2074961) B2074961
theorem B859241 : Blo 235815 859241 := bstep (se 2 (by rfl) ⟨322215, by rfl⟩ : syracuseStep 859241 = 644431) B644431
theorem B2956475 : Blo 235815 2956475 := bstep (se 1 (by rfl) ⟨2217356, by rfl⟩ : syracuseStep 2956475 = 4434713) B4434713
theorem B761167 : Blo 235815 761167 := bstep (se 1 (by rfl) ⟨570875, by rfl⟩ : syracuseStep 761167 = 1141751) B1141751
theorem B761179 : Blo 235815 761179 := bstep (se 1 (by rfl) ⟨570884, by rfl⟩ : syracuseStep 761179 = 1141769) B1141769
theorem B401503 : Blo 235815 401503 := bstep (se 1 (by rfl) ⟨301127, by rfl⟩ : syracuseStep 401503 = 602255) B602255
theorem B958567 : Blo 235815 958567 := bstep (se 1 (by rfl) ⟨718925, by rfl⟩ : syracuseStep 958567 = 1437851) B1437851
theorem B237979 : Blo 235815 237979 := bstep (se 1 (by rfl) ⟨178484, by rfl⟩ : syracuseStep 237979 = 356969) B356969
theorem B533087 : Blo 235815 533087 := bstep (se 1 (by rfl) ⟨399815, by rfl⟩ : syracuseStep 533087 = 799631) B799631
theorem B238335 : Blo 235815 238335 := bstep (se 1 (by rfl) ⟨178751, by rfl⟩ : syracuseStep 238335 = 357503) B357503
theorem B238575 : Blo 235815 238575 := bstep (se 1 (by rfl) ⟨178931, by rfl⟩ : syracuseStep 238575 = 357863) B357863
theorem B238623 : Blo 235815 238623 := bstep (se 1 (by rfl) ⟨178967, by rfl⟩ : syracuseStep 238623 = 357935) B357935
theorem B402671 : Blo 235815 402671 := bstep (se 1 (by rfl) ⟨302003, by rfl⟩ : syracuseStep 402671 = 604007) B604007
theorem B238843 : Blo 235815 238843 := bstep (se 1 (by rfl) ⟨179132, by rfl⟩ : syracuseStep 238843 = 358265) B358265
theorem B239311 : Blo 235815 239311 := bstep (se 1 (by rfl) ⟨179483, by rfl⟩ : syracuseStep 239311 = 358967) B358967
theorem B239359 : Blo 235815 239359 := bstep (se 1 (by rfl) ⟨179519, by rfl⟩ : syracuseStep 239359 = 359039) B359039
theorem B534383 : Blo 235815 534383 := bstep (se 1 (by rfl) ⟨400787, by rfl⟩ : syracuseStep 534383 = 801575) B801575
theorem B239471 : Blo 235815 239471 := bstep (se 1 (by rfl) ⟨179603, by rfl⟩ : syracuseStep 239471 = 359207) B359207
theorem B797687 : Blo 235815 797687 := bstep (se 1 (by rfl) ⟨598265, by rfl⟩ : syracuseStep 797687 = 1196531) B1196531
theorem B568415 : Blo 235815 568415 := bstep (se 1 (by rfl) ⟨426311, by rfl⟩ : syracuseStep 568415 = 852623) B852623
theorem B535787 : Blo 235815 535787 := bstep (se 1 (by rfl) ⟨401840, by rfl⟩ : syracuseStep 535787 = 803681) B803681
theorem B601577 : Blo 235815 601577 := bstep (se 2 (by rfl) ⟨225591, by rfl⟩ : syracuseStep 601577 = 451183) B451183
theorem B536111 : Blo 235815 536111 := bstep (se 1 (by rfl) ⟨402083, by rfl⟩ : syracuseStep 536111 = 804167) B804167
theorem B863855 : Blo 235815 863855 := bstep (se 1 (by rfl) ⟨647891, by rfl⟩ : syracuseStep 863855 = 1295783) B1295783
theorem B896777 : Blo 235815 896777 := bstep (se 2 (by rfl) ⟨336291, by rfl⟩ : syracuseStep 896777 = 672583) B672583
theorem B765895 : Blo 235815 765895 := bstep (se 1 (by rfl) ⟨574421, by rfl⟩ : syracuseStep 765895 = 1148843) B1148843
theorem B1519897 : Blo 235815 1519897 := bstep (se 2 (by rfl) ⟨569961, by rfl⟩ : syracuseStep 1519897 = 1139923) B1139923
theorem B537065 : Blo 235815 537065 := bstep (se 2 (by rfl) ⟨201399, by rfl⟩ : syracuseStep 537065 = 402799) B402799
theorem B3060503 : Blo 235815 3060503 := bstep (se 1 (by rfl) ⟨2295377, by rfl⟩ : syracuseStep 3060503 = 4590755) B4590755
theorem B570415 : Blo 235815 570415 := bstep (se 1 (by rfl) ⟨427811, by rfl⟩ : syracuseStep 570415 = 855623) B855623
theorem B3421561 : Blo 235815 3421561 := bstep (se 2 (by rfl) ⟨1283085, by rfl⟩ : syracuseStep 3421561 = 2566171) B2566171
theorem B898735 : Blo 235815 898735 := bstep (se 1 (by rfl) ⟨674051, by rfl⟩ : syracuseStep 898735 = 1348103) B1348103
theorem B800711 : Blo 235815 800711 := bstep (se 1 (by rfl) ⟨600533, by rfl⟩ : syracuseStep 800711 = 1201067) B1201067
theorem B899039 : Blo 235815 899039 := bstep (se 1 (by rfl) ⟨674279, by rfl⟩ : syracuseStep 899039 = 1348559) B1348559
theorem B768047 : Blo 235815 768047 := bstep (se 1 (by rfl) ⟨576035, by rfl⟩ : syracuseStep 768047 = 1152071) B1152071
theorem B5454377 : Blo 235815 5454377 := bstep (se 2 (by rfl) ⟨2045391, by rfl⟩ : syracuseStep 5454377 = 4090783) B4090783
theorem B1194749 : Blo 235815 1194749 := bstep (se 3 (by rfl) ⟨224015, by rfl⟩ : syracuseStep 1194749 = 448031) B448031
theorem B802169 : Blo 235815 802169 := bstep (se 2 (by rfl) ⟨300813, by rfl⟩ : syracuseStep 802169 = 601627) B601627
theorem B802223 : Blo 235815 802223 := bstep (se 1 (by rfl) ⟨601667, by rfl⟩ : syracuseStep 802223 = 1203335) B1203335
theorem B671615 : Blo 235815 671615 := bstep (se 1 (by rfl) ⟨503711, by rfl⟩ : syracuseStep 671615 = 1007423) B1007423
theorem B606811 : Blo 235815 606811 := bstep (se 1 (by rfl) ⟨455108, by rfl⟩ : syracuseStep 606811 = 910217) B910217
theorem B98321201 : Blo 235815 98321201 := bstep (se 2 (by rfl) ⟨36870450, by rfl⟩ : syracuseStep 98321201 = 73740901) B73740901
theorem B3884219 : Blo 235815 3884219 := bstep (se 1 (by rfl) ⟨2913164, by rfl⟩ : syracuseStep 3884219 = 5826329) B5826329
theorem B1296253 : Blo 235815 1296253 := bstep (se 3 (by rfl) ⟨243047, by rfl⟩ : syracuseStep 1296253 = 486095) B486095
theorem B804923 : Blo 235815 804923 := bstep (se 1 (by rfl) ⟨603692, by rfl⟩ : syracuseStep 804923 = 1207385) B1207385
theorem B805139 : Blo 235815 805139 := bstep (se 1 (by rfl) ⟨603854, by rfl⟩ : syracuseStep 805139 = 1207709) B1207709
theorem B379559 : Blo 235815 379559 := bstep (se 1 (by rfl) ⟨284669, by rfl⟩ : syracuseStep 379559 = 569339) B569339
theorem B1133311 : Blo 235815 1133311 := bstep (se 1 (by rfl) ⟨849983, by rfl⟩ : syracuseStep 1133311 = 1699967) B1699967
theorem B1821635 : Blo 235815 1821635 := bstep (se 1 (by rfl) ⟨1366226, by rfl⟩ : syracuseStep 1821635 = 2732453) B2732453
theorem B478505 : Blo 235815 478505 := bstep (se 2 (by rfl) ⟨179439, by rfl⟩ : syracuseStep 478505 = 358879) B358879
theorem B675647 : Blo 235815 675647 := bstep (se 1 (by rfl) ⟨506735, by rfl⟩ : syracuseStep 675647 = 1013471) B1013471
theorem B905039 : Blo 235815 905039 := bstep (se 1 (by rfl) ⟨678779, by rfl⟩ : syracuseStep 905039 = 1357559) B1357559
theorem B1363823 : Blo 235815 1363823 := bstep (se 1 (by rfl) ⟨1022867, by rfl⟩ : syracuseStep 1363823 = 2045735) B2045735
theorem B675965 : Blo 235815 675965 := bstep (se 3 (by rfl) ⟨126743, by rfl⟩ : syracuseStep 675965 = 253487) B253487
theorem B1200257 : Blo 235815 1200257 := bstep (se 2 (by rfl) ⟨450096, by rfl⟩ : syracuseStep 1200257 = 900193) B900193
theorem B1037033 : Blo 235815 1037033 := bstep (se 2 (by rfl) ⟨388887, by rfl⟩ : syracuseStep 1037033 = 777775) B777775
theorem B6510617 : Blo 235815 6510617 := bstep (se 2 (by rfl) ⟨2441481, by rfl⟩ : syracuseStep 6510617 = 4882963) B4882963
theorem B1628531 : Blo 235815 1628531 := bstep (se 1 (by rfl) ⟨1221398, by rfl⟩ : syracuseStep 1628531 = 2442797) B2442797
theorem B449003 : Blo 235815 449003 := bstep (se 1 (by rfl) ⟨336752, by rfl⟩ : syracuseStep 449003 = 673505) B673505
theorem B9132911 : Blo 235815 9132911 := bstep (se 1 (by rfl) ⟨6849683, by rfl⟩ : syracuseStep 9132911 = 13699367) B13699367
theorem B29678561 : Blo 235815 29678561 := bstep (se 2 (by rfl) ⟨11129460, by rfl⟩ : syracuseStep 29678561 = 22258921) B22258921
theorem B449641 : Blo 235815 449641 := bstep (se 2 (by rfl) ⟨168615, by rfl⟩ : syracuseStep 449641 = 337231) B337231
theorem B613615 : Blo 235815 613615 := bstep (se 1 (by rfl) ⟨460211, by rfl⟩ : syracuseStep 613615 = 920423) B920423
theorem B777695 : Blo 235815 777695 := bstep (se 1 (by rfl) ⟨583271, by rfl⟩ : syracuseStep 777695 = 1166543) B1166543
theorem B18013985 : Blo 235815 18013985 := bstep (se 2 (by rfl) ⟨6755244, by rfl⟩ : syracuseStep 18013985 = 13510489) B13510489
theorem B2711879 : Blo 235815 2711879 := bstep (se 1 (by rfl) ⟨2033909, by rfl⟩ : syracuseStep 2711879 = 4067819) B4067819
theorem B1467143 : Blo 235815 1467143 := bstep (se 1 (by rfl) ⟨1100357, by rfl⟩ : syracuseStep 1467143 = 2200715) B2200715
theorem B1205117 : Blo 235815 1205117 := bstep (se 3 (by rfl) ⟨225959, by rfl⟩ : syracuseStep 1205117 = 451919) B451919
theorem B582727 : Blo 235815 582727 := bstep (se 1 (by rfl) ⟨437045, by rfl⟩ : syracuseStep 582727 = 874091) B874091
theorem B3225445829 : Blo 235815 3225445829 := bstep (se 4 (by rfl) ⟨302385546, by rfl⟩ : syracuseStep 3225445829 = 604771093) B604771093
theorem B354479 : Blo 235815 354479 := bstep (se 1 (by rfl) ⟨265859, by rfl⟩ : syracuseStep 354479 = 531719) B531719
theorem B1796741 : Blo 235815 1796741 := bstep (se 4 (by rfl) ⟨168444, by rfl⟩ : syracuseStep 1796741 = 336889) B336889
theorem B355049 : Blo 235815 355049 := bstep (se 2 (by rfl) ⟨133143, by rfl⟩ : syracuseStep 355049 = 266287) B266287
theorem B355103 : Blo 235815 355103 := bstep (se 1 (by rfl) ⟨266327, by rfl⟩ : syracuseStep 355103 = 532655) B532655
theorem B453575 : Blo 235815 453575 := bstep (se 1 (by rfl) ⟨340181, by rfl⟩ : syracuseStep 453575 = 680363) B680363
theorem B3042359 : Blo 235815 3042359 := bstep (se 1 (by rfl) ⟨2281769, by rfl⟩ : syracuseStep 3042359 = 4563539) B4563539
theorem B355583 : Blo 235815 355583 := bstep (se 1 (by rfl) ⟨266687, by rfl⟩ : syracuseStep 355583 = 533375) B533375
theorem B1798199 : Blo 235815 1798199 := bstep (se 1 (by rfl) ⟨1348649, by rfl⟩ : syracuseStep 1798199 = 2697299) B2697299
theorem B356423 : Blo 235815 356423 := bstep (se 1 (by rfl) ⟨267317, by rfl⟩ : syracuseStep 356423 = 534635) B534635
theorem B356843 : Blo 235815 356843 := bstep (se 1 (by rfl) ⟨267632, by rfl⟩ : syracuseStep 356843 = 535265) B535265
theorem B357599 : Blo 235815 357599 := bstep (se 1 (by rfl) ⟨268199, by rfl⟩ : syracuseStep 357599 = 536399) B536399
theorem B1439407 : Blo 235815 1439407 := bstep (se 1 (by rfl) ⟨1079555, by rfl⟩ : syracuseStep 1439407 = 2159111) B2159111
theorem B358079 : Blo 235815 358079 := bstep (se 1 (by rfl) ⟨268559, by rfl⟩ : syracuseStep 358079 = 537119) B537119
theorem B2291611 : Blo 235815 2291611 := bstep (se 1 (by rfl) ⟨1718708, by rfl⟩ : syracuseStep 2291611 = 3437417) B3437417
theorem B2717711 : Blo 235815 2717711 := bstep (se 1 (by rfl) ⟨2038283, by rfl⟩ : syracuseStep 2717711 = 4076567) B4076567
theorem B358463 : Blo 235815 358463 := bstep (se 1 (by rfl) ⟨268847, by rfl⟩ : syracuseStep 358463 = 537695) B537695
theorem B358511 : Blo 235815 358511 := bstep (se 1 (by rfl) ⟨268883, by rfl⟩ : syracuseStep 358511 = 537767) B537767
theorem B1374353 : Blo 235815 1374353 := bstep (se 2 (by rfl) ⟨515382, by rfl⟩ : syracuseStep 1374353 = 1030765) B1030765
theorem B358655 : Blo 235815 358655 := bstep (se 1 (by rfl) ⟨268991, by rfl⟩ : syracuseStep 358655 = 537983) B537983
theorem B358793 : Blo 235815 358793 := bstep (se 2 (by rfl) ⟨134547, by rfl⟩ : syracuseStep 358793 = 269095) B269095
theorem B3668753 : Blo 235815 3668753 := bstep (se 2 (by rfl) ⟨1375782, by rfl⟩ : syracuseStep 3668753 = 2751565) B2751565
theorem B359291 : Blo 235815 359291 := bstep (se 1 (by rfl) ⟨269468, by rfl⟩ : syracuseStep 359291 = 538937) B538937
theorem B3406799 : Blo 235815 3406799 := bstep (se 1 (by rfl) ⟨2555099, by rfl⟩ : syracuseStep 3406799 = 5110199) B5110199
theorem B359417 : Blo 235815 359417 := bstep (se 2 (by rfl) ⟨134781, by rfl⟩ : syracuseStep 359417 = 269563) B269563
theorem B1769161 : Blo 235815 1769161 := bstep (se 2 (by rfl) ⟨663435, by rfl⟩ : syracuseStep 1769161 = 1326871) B1326871
theorem B1212407 : Blo 235815 1212407 := bstep (se 1 (by rfl) ⟨909305, by rfl⟩ : syracuseStep 1212407 = 1818611) B1818611
theorem B1278089 : Blo 235815 1278089 := bstep (se 2 (by rfl) ⟨479283, by rfl⟩ : syracuseStep 1278089 = 958567) B958567
theorem B1802573 : Blo 235815 1802573 := bstep (se 3 (by rfl) ⟨337982, by rfl⟩ : syracuseStep 1802573 = 675965) B675965
theorem B2589479 : Blo 235815 2589479 := bstep (se 1 (by rfl) ⟨1942109, by rfl⟩ : syracuseStep 2589479 = 3884219) B3884219
theorem B1311815 : Blo 235815 1311815 := bstep (se 1 (by rfl) ⟨983861, by rfl⟩ : syracuseStep 1311815 = 1967723) B1967723
theorem B4785419 : Blo 235815 4785419 := bstep (se 1 (by rfl) ⟨3589064, by rfl⟩ : syracuseStep 4785419 = 7178129) B7178129
theorem B1214423 : Blo 235815 1214423 := bstep (se 1 (by rfl) ⟨910817, by rfl⟩ : syracuseStep 1214423 = 1821635) B1821635
theorem B691355 : Blo 235815 691355 := bstep (se 1 (by rfl) ⟨518516, by rfl⟩ : syracuseStep 691355 = 1037033) B1037033
theorem B265423 : Blo 235815 265423 := bstep (se 1 (by rfl) ⟨199067, by rfl⟩ : syracuseStep 265423 = 398135) B398135
theorem B1511081 : Blo 235815 1511081 := bstep (se 2 (by rfl) ⟨566655, by rfl⟩ : syracuseStep 1511081 = 1133311) B1133311
theorem B1085687 : Blo 235815 1085687 := bstep (se 1 (by rfl) ⟨814265, by rfl⟩ : syracuseStep 1085687 = 1628531) B1628531
theorem B7377637 : Blo 235815 7377637 := bstep (se 4 (by rfl) ⟨691653, by rfl⟩ : syracuseStep 7377637 = 1383307) B1383307
theorem B1970983 : Blo 235815 1970983 := bstep (se 1 (by rfl) ⟨1478237, by rfl⟩ : syracuseStep 1970983 = 2956475) B2956475
theorem B1021193 : Blo 235815 1021193 := bstep (se 2 (by rfl) ⟨382947, by rfl⟩ : syracuseStep 1021193 = 765895) B765895
theorem B1807919 : Blo 235815 1807919 := bstep (se 1 (by rfl) ⟨1355939, by rfl⟩ : syracuseStep 1807919 = 2711879) B2711879
theorem B268447 : Blo 235815 268447 := bstep (se 1 (by rfl) ⟨201335, by rfl⟩ : syracuseStep 268447 = 402671) B402671
theorem B760553 : Blo 235815 760553 := bstep (se 2 (by rfl) ⟨285207, by rfl⟩ : syracuseStep 760553 = 570415) B570415
theorem B236319 : Blo 235815 236319 := bstep (se 1 (by rfl) ⟨177239, by rfl⟩ : syracuseStep 236319 = 354479) B354479
theorem B236699 : Blo 235815 236699 := bstep (se 1 (by rfl) ⟨177524, by rfl⟩ : syracuseStep 236699 = 355049) B355049
theorem B4562081 : Blo 235815 4562081 := bstep (se 2 (by rfl) ⟨1710780, by rfl⟩ : syracuseStep 4562081 = 3421561) B3421561
theorem B236735 : Blo 235815 236735 := bstep (se 1 (by rfl) ⟨177551, by rfl⟩ : syracuseStep 236735 = 355103) B355103
theorem B302383 : Blo 235815 302383 := bstep (se 1 (by rfl) ⟨226787, by rfl⟩ : syracuseStep 302383 = 453575) B453575
theorem B531791 : Blo 235815 531791 := bstep (se 1 (by rfl) ⟨398843, by rfl⟩ : syracuseStep 531791 = 797687) B797687
theorem B237055 : Blo 235815 237055 := bstep (se 1 (by rfl) ⟨177791, by rfl⟩ : syracuseStep 237055 = 355583) B355583
theorem B401051 : Blo 235815 401051 := bstep (se 1 (by rfl) ⟨300788, by rfl⟩ : syracuseStep 401051 = 601577) B601577
theorem B597851 : Blo 235815 597851 := bstep (se 1 (by rfl) ⟨448388, by rfl⟩ : syracuseStep 597851 = 896777) B896777
theorem B3055481 : Blo 235815 3055481 := bstep (se 2 (by rfl) ⟨1145805, by rfl⟩ : syracuseStep 3055481 = 2291611) B2291611
theorem B237615 : Blo 235815 237615 := bstep (se 1 (by rfl) ⟨178211, by rfl⟩ : syracuseStep 237615 = 356423) B356423
theorem B1515773 : Blo 235815 1515773 := bstep (se 3 (by rfl) ⟨284207, by rfl⟩ : syracuseStep 1515773 = 568415) B568415
theorem B237895 : Blo 235815 237895 := bstep (se 1 (by rfl) ⟨178421, by rfl⟩ : syracuseStep 237895 = 356843) B356843
theorem B2040335 : Blo 235815 2040335 := bstep (se 1 (by rfl) ⟨1530251, by rfl⟩ : syracuseStep 2040335 = 3060503) B3060503
theorem B238399 : Blo 235815 238399 := bstep (se 1 (by rfl) ⟨178799, by rfl⟩ : syracuseStep 238399 = 357599) B357599
theorem B3023801 : Blo 235815 3023801 := bstep (se 2 (by rfl) ⟨1133925, by rfl⟩ : syracuseStep 3023801 = 2267851) B2267851
theorem B238719 : Blo 235815 238719 := bstep (se 1 (by rfl) ⟨179039, by rfl⟩ : syracuseStep 238719 = 358079) B358079
theorem B2073853 : Blo 235815 2073853 := bstep (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) B777695
theorem B533807 : Blo 235815 533807 := bstep (se 1 (by rfl) ⟨400355, by rfl⟩ : syracuseStep 533807 = 800711) B800711
theorem B599359 : Blo 235815 599359 := bstep (se 1 (by rfl) ⟨449519, by rfl⟩ : syracuseStep 599359 = 899039) B899039
theorem B1811807 : Blo 235815 1811807 := bstep (se 1 (by rfl) ⟨1358855, by rfl⟩ : syracuseStep 1811807 = 2717711) B2717711
theorem B238975 : Blo 235815 238975 := bstep (se 1 (by rfl) ⟨179231, by rfl⟩ : syracuseStep 238975 = 358463) B358463
theorem B239007 : Blo 235815 239007 := bstep (se 1 (by rfl) ⟨179255, by rfl⟩ : syracuseStep 239007 = 358511) B358511
theorem B599521 : Blo 235815 599521 := bstep (se 2 (by rfl) ⟨224820, by rfl⟩ : syracuseStep 599521 = 449641) B449641
theorem B239103 : Blo 235815 239103 := bstep (se 1 (by rfl) ⟨179327, by rfl⟩ : syracuseStep 239103 = 358655) B358655
theorem B239195 : Blo 235815 239195 := bstep (se 1 (by rfl) ⟨179396, by rfl⟩ : syracuseStep 239195 = 358793) B358793
theorem B796499 : Blo 235815 796499 := bstep (se 1 (by rfl) ⟨597374, by rfl⟩ : syracuseStep 796499 = 1194749) B1194749
theorem B239527 : Blo 235815 239527 := bstep (se 1 (by rfl) ⟨179645, by rfl⟩ : syracuseStep 239527 = 359291) B359291
theorem B2271199 : Blo 235815 2271199 := bstep (se 1 (by rfl) ⟨1703399, by rfl⟩ : syracuseStep 2271199 = 3406799) B3406799
theorem B239611 : Blo 235815 239611 := bstep (se 1 (by rfl) ⟨179708, by rfl⟩ : syracuseStep 239611 = 359417) B359417
theorem B534779 : Blo 235815 534779 := bstep (se 1 (by rfl) ⟨401084, by rfl⟩ : syracuseStep 534779 = 802169) B802169
theorem B534815 : Blo 235815 534815 := bstep (se 1 (by rfl) ⟨401111, by rfl⟩ : syracuseStep 534815 = 802223) B802223
theorem B535337 : Blo 235815 535337 := bstep (se 2 (by rfl) ⟨200751, by rfl⟩ : syracuseStep 535337 = 401503) B401503
theorem B65547467 : Blo 235815 65547467 := bstep (se 1 (by rfl) ⟨49160600, by rfl⟩ : syracuseStep 65547467 = 98321201) B98321201
theorem B536615 : Blo 235815 536615 := bstep (se 1 (by rfl) ⟨402461, by rfl⟩ : syracuseStep 536615 = 804923) B804923
theorem B536759 : Blo 235815 536759 := bstep (se 1 (by rfl) ⟨402569, by rfl⟩ : syracuseStep 536759 = 805139) B805139
theorem B603359 : Blo 235815 603359 := bstep (se 1 (by rfl) ⟨452519, by rfl⟩ : syracuseStep 603359 = 905039) B905039
theorem B800171 : Blo 235815 800171 := bstep (se 1 (by rfl) ⟨600128, by rfl⟩ : syracuseStep 800171 = 1200257) B1200257
theorem B1357307 : Blo 235815 1357307 := bstep (se 1 (by rfl) ⟨1017980, by rfl⟩ : syracuseStep 1357307 = 2035961) B2035961
theorem B4340411 : Blo 235815 4340411 := bstep (se 1 (by rfl) ⟨3255308, by rfl⟩ : syracuseStep 4340411 = 6510617) B6510617
theorem B572827 : Blo 235815 572827 := bstep (se 1 (by rfl) ⟨429620, by rfl⟩ : syracuseStep 572827 = 859241) B859241
theorem B12009323 : Blo 235815 12009323 := bstep (se 1 (by rfl) ⟨9006992, by rfl⟩ : syracuseStep 12009323 = 18013985) B18013985
theorem B2048125 : Blo 235815 2048125 := bstep (se 3 (by rfl) ⟨384023, by rfl⟩ : syracuseStep 2048125 = 768047) B768047
theorem B803411 : Blo 235815 803411 := bstep (se 1 (by rfl) ⟨602558, by rfl⟩ : syracuseStep 803411 = 1205117) B1205117
theorem B1197341 : Blo 235815 1197341 := bstep (se 3 (by rfl) ⟨224501, by rfl⟩ : syracuseStep 1197341 = 449003) B449003
theorem B1197827 : Blo 235815 1197827 := bstep (se 1 (by rfl) ⟨898370, by rfl⟩ : syracuseStep 1197827 = 1796741) B1796741
theorem B9783341 : Blo 235815 9783341 := bstep (se 3 (by rfl) ⟨1834376, by rfl⟩ : syracuseStep 9783341 = 3668753) B3668753
theorem B1919209 : Blo 235815 1919209 := bstep (se 2 (by rfl) ⟨719703, by rfl⟩ : syracuseStep 1919209 = 1439407) B1439407
theorem B1198313 : Blo 235815 1198313 := bstep (se 2 (by rfl) ⟨449367, by rfl⟩ : syracuseStep 1198313 = 898735) B898735
theorem B575903 : Blo 235815 575903 := bstep (se 1 (by rfl) ⟨431927, by rfl⟩ : syracuseStep 575903 = 863855) B863855
theorem B1198799 : Blo 235815 1198799 := bstep (se 1 (by rfl) ⟨899099, by rfl⟩ : syracuseStep 1198799 = 1798199) B1798199
theorem B969889 : Blo 235815 969889 := bstep (se 2 (by rfl) ⟨363708, by rfl⟩ : syracuseStep 969889 = 727417) B727417
theorem B4117229 : Blo 235815 4117229 := bstep (se 3 (by rfl) ⟨771980, by rfl⟩ : syracuseStep 4117229 = 1543961) B1543961
theorem B447743 : Blo 235815 447743 := bstep (se 1 (by rfl) ⟨335807, by rfl⟩ : syracuseStep 447743 = 671615) B671615
theorem B808271 : Blo 235815 808271 := bstep (se 1 (by rfl) ⟨606203, by rfl⟩ : syracuseStep 808271 = 1212407) B1212407
theorem B677231 : Blo 235815 677231 := bstep (se 1 (by rfl) ⟨507923, by rfl⟩ : syracuseStep 677231 = 1015847) B1015847
theorem B809081 : Blo 235815 809081 := bstep (se 2 (by rfl) ⟨303405, by rfl⟩ : syracuseStep 809081 = 606811) B606811
theorem B62740793 : Blo 235815 62740793 := bstep (se 2 (by rfl) ⟨23527797, by rfl⟩ : syracuseStep 62740793 = 47055595) B47055595
theorem B776969 : Blo 235815 776969 := bstep (se 2 (by rfl) ⟨291363, by rfl⟩ : syracuseStep 776969 = 582727) B582727
theorem B1137503 : Blo 235815 1137503 := bstep (se 1 (by rfl) ⟨853127, by rfl⟩ : syracuseStep 1137503 = 1706255) B1706255
theorem B253039 : Blo 235815 253039 := bstep (se 1 (by rfl) ⟨189779, by rfl⟩ : syracuseStep 253039 = 379559) B379559
theorem B1727851 : Blo 235815 1727851 := bstep (se 1 (by rfl) ⟨1295888, by rfl⟩ : syracuseStep 1727851 = 2591777) B2591777
theorem B319003 : Blo 235815 319003 := bstep (se 1 (by rfl) ⟨239252, by rfl⟩ : syracuseStep 319003 = 478505) B478505
theorem B450431 : Blo 235815 450431 := bstep (se 1 (by rfl) ⟨337823, by rfl⟩ : syracuseStep 450431 = 675647) B675647
theorem B909215 : Blo 235815 909215 := bstep (se 1 (by rfl) ⟨681911, by rfl⟩ : syracuseStep 909215 = 1363823) B1363823
theorem B1139291 : Blo 235815 1139291 := bstep (se 1 (by rfl) ⟨854468, by rfl⟩ : syracuseStep 1139291 = 1708937) B1708937
theorem B3041023 : Blo 235815 3041023 := bstep (se 1 (by rfl) ⟨2280767, by rfl⟩ : syracuseStep 3041023 = 4561535) B4561535
theorem B6088607 : Blo 235815 6088607 := bstep (se 1 (by rfl) ⟨4566455, by rfl⟩ : syracuseStep 6088607 = 9132911) B9132911
theorem B19785707 : Blo 235815 19785707 := bstep (se 1 (by rfl) ⟨14839280, by rfl⟩ : syracuseStep 19785707 = 29678561) B29678561
theorem B2026529 : Blo 235815 2026529 := bstep (se 2 (by rfl) ⟨759948, by rfl⟩ : syracuseStep 2026529 = 1519897) B1519897
theorem B355391 : Blo 235815 355391 := bstep (se 1 (by rfl) ⟨266543, by rfl⟩ : syracuseStep 355391 = 533087) B533087
theorem B978095 : Blo 235815 978095 := bstep (se 1 (by rfl) ⟨733571, by rfl⟩ : syracuseStep 978095 = 1467143) B1467143
theorem B355817 : Blo 235815 355817 := bstep (se 2 (by rfl) ⟨133431, by rfl⟩ : syracuseStep 355817 = 266863) B266863
theorem B355961 : Blo 235815 355961 := bstep (se 2 (by rfl) ⟨133485, by rfl⟩ : syracuseStep 355961 = 266971) B266971
theorem B2150297219 : Blo 235815 2150297219 := bstep (se 1 (by rfl) ⟨1612722914, by rfl⟩ : syracuseStep 2150297219 = 3225445829) B3225445829
theorem B356255 : Blo 235815 356255 := bstep (se 1 (by rfl) ⟨267191, by rfl⟩ : syracuseStep 356255 = 534383) B534383
theorem B2028239 : Blo 235815 2028239 := bstep (se 1 (by rfl) ⟨1521179, by rfl⟩ : syracuseStep 2028239 = 3042359) B3042359
theorem B357191 : Blo 235815 357191 := bstep (se 1 (by rfl) ⟨267893, by rfl⟩ : syracuseStep 357191 = 535787) B535787
theorem B357407 : Blo 235815 357407 := bstep (se 1 (by rfl) ⟨268055, by rfl⟩ : syracuseStep 357407 = 536111) B536111
theorem B358043 : Blo 235815 358043 := bstep (se 1 (by rfl) ⟨268532, by rfl⟩ : syracuseStep 358043 = 537065) B537065
theorem B916235 : Blo 235815 916235 := bstep (se 1 (by rfl) ⟨687176, by rfl⟩ : syracuseStep 916235 = 1374353) B1374353
theorem B818153 : Blo 235815 818153 := bstep (se 2 (by rfl) ⟨306807, by rfl⟩ : syracuseStep 818153 = 613615) B613615
theorem B3636251 : Blo 235815 3636251 := bstep (se 1 (by rfl) ⟨2727188, by rfl⟩ : syracuseStep 3636251 = 5454377) B5454377
theorem B1014889 : Blo 235815 1014889 := bstep (se 2 (by rfl) ⟨380583, by rfl⟩ : syracuseStep 1014889 = 761167) B761167
theorem B1014905 : Blo 235815 1014905 := bstep (se 2 (by rfl) ⟨380589, by rfl⟩ : syracuseStep 1014905 = 761179) B761179
theorem B6913349 : Blo 235815 6913349 := bstep (se 4 (by rfl) ⟨648126, by rfl⟩ : syracuseStep 6913349 = 1296253) B1296253
theorem B2358881 : Blo 235815 2358881 := bstep (se 2 (by rfl) ⟨884580, by rfl⟩ : syracuseStep 2358881 = 1769161) B1769161
theorem B852059 : Blo 235815 852059 := bstep (se 1 (by rfl) ⟨639044, by rfl⟩ : syracuseStep 852059 = 1278089) B1278089
theorem B6522227 : Blo 235815 6522227 := bstep (se 1 (by rfl) ⟨4891670, by rfl⟩ : syracuseStep 6522227 = 9783341) B9783341
theorem B460903 : Blo 235815 460903 := bstep (se 1 (by rfl) ⟨345677, by rfl⟩ : syracuseStep 460903 = 691355) B691355
theorem B723791 : Blo 235815 723791 := bstep (se 1 (by rfl) ⟨542843, by rfl⟩ : syracuseStep 723791 = 1085687) B1085687
theorem B2558945 : Blo 235815 2558945 := bstep (se 2 (by rfl) ⟨959604, by rfl⟩ : syracuseStep 2558945 = 1919209) B1919209
theorem B298495 : Blo 235815 298495 := bstep (se 1 (by rfl) ⟨223871, by rfl⟩ : syracuseStep 298495 = 447743) B447743
theorem B758335 : Blo 235815 758335 := bstep (se 1 (by rfl) ⟨568751, by rfl⟩ : syracuseStep 758335 = 1137503) B1137503
theorem B267367 : Blo 235815 267367 := bstep (se 1 (by rfl) ⟨200525, by rfl⟩ : syracuseStep 267367 = 401051) B401051
theorem B398567 : Blo 235815 398567 := bstep (se 1 (by rfl) ⟨298925, by rfl⟩ : syracuseStep 398567 = 597851) B597851
theorem B2036987 : Blo 235815 2036987 := bstep (se 1 (by rfl) ⟨1527740, by rfl⟩ : syracuseStep 2036987 = 3055481) B3055481
theorem B300287 : Blo 235815 300287 := bstep (se 1 (by rfl) ⟨225215, by rfl⟩ : syracuseStep 300287 = 450431) B450431
theorem B759527 : Blo 235815 759527 := bstep (se 1 (by rfl) ⟨569645, by rfl⟩ : syracuseStep 759527 = 1139291) B1139291
theorem B9836849 : Blo 235815 9836849 := bstep (se 2 (by rfl) ⟨3688818, by rfl⟩ : syracuseStep 9836849 = 7377637) B7377637
theorem B2627977 : Blo 235815 2627977 := bstep (se 2 (by rfl) ⟨985491, by rfl⟩ : syracuseStep 2627977 = 1970983) B1970983
theorem B530999 : Blo 235815 530999 := bstep (se 1 (by rfl) ⟨398249, by rfl⟩ : syracuseStep 530999 = 796499) B796499
theorem B1351019 : Blo 235815 1351019 := bstep (se 1 (by rfl) ⟨1013264, by rfl⟩ : syracuseStep 1351019 = 2026529) B2026529
theorem B236927 : Blo 235815 236927 := bstep (se 1 (by rfl) ⟨177695, by rfl⟩ : syracuseStep 236927 = 355391) B355391
theorem B237211 : Blo 235815 237211 := bstep (se 1 (by rfl) ⟨177908, by rfl⟩ : syracuseStep 237211 = 355817) B355817
theorem B237307 : Blo 235815 237307 := bstep (se 1 (by rfl) ⟨177980, by rfl⟩ : syracuseStep 237307 = 355961) B355961
theorem B237503 : Blo 235815 237503 := bstep (se 1 (by rfl) ⟨178127, by rfl⟩ : syracuseStep 237503 = 356255) B356255
theorem B1352159 : Blo 235815 1352159 := bstep (se 1 (by rfl) ⟨1014119, by rfl⟩ : syracuseStep 1352159 = 2028239) B2028239
theorem B238127 : Blo 235815 238127 := bstep (se 1 (by rfl) ⟨178595, by rfl⟩ : syracuseStep 238127 = 357191) B357191
theorem B238271 : Blo 235815 238271 := bstep (se 1 (by rfl) ⟨178703, by rfl⟩ : syracuseStep 238271 = 357407) B357407
theorem B402239 : Blo 235815 402239 := bstep (se 1 (by rfl) ⟨301679, by rfl⟩ : syracuseStep 402239 = 603359) B603359
theorem B533447 : Blo 235815 533447 := bstep (se 1 (by rfl) ⟨400085, by rfl⟩ : syracuseStep 533447 = 800171) B800171
theorem B238695 : Blo 235815 238695 := bstep (se 1 (by rfl) ⟨179021, by rfl⟩ : syracuseStep 238695 = 358043) B358043
theorem B1353185 : Blo 235815 1353185 := bstep (se 2 (by rfl) ⟨507444, by rfl⟩ : syracuseStep 1353185 = 1014889) B1014889
theorem B337385 : Blo 235815 337385 := bstep (se 2 (by rfl) ⟨126519, by rfl⟩ : syracuseStep 337385 = 253039) B253039
theorem B403177 : Blo 235815 403177 := bstep (se 2 (by rfl) ⟨151191, by rfl⟩ : syracuseStep 403177 = 302383) B302383
theorem B2893607 : Blo 235815 2893607 := bstep (se 1 (by rfl) ⟨2170205, by rfl⟩ : syracuseStep 2893607 = 4340411) B4340411
theorem B2303801 : Blo 235815 2303801 := bstep (se 2 (by rfl) ⟨863925, by rfl⟩ : syracuseStep 2303801 = 1727851) B1727851
theorem B763769 : Blo 235815 763769 := bstep (se 2 (by rfl) ⟨286413, by rfl⟩ : syracuseStep 763769 = 572827) B572827
theorem B8006215 : Blo 235815 8006215 := bstep (se 1 (by rfl) ⟨6004661, by rfl⟩ : syracuseStep 8006215 = 12009323) B12009323
theorem B2730833 : Blo 235815 2730833 := bstep (se 2 (by rfl) ⟨1024062, by rfl⟩ : syracuseStep 2730833 = 2048125) B2048125
theorem B535607 : Blo 235815 535607 := bstep (se 1 (by rfl) ⟨401705, by rfl⟩ : syracuseStep 535607 = 803411) B803411
theorem B3190279 : Blo 235815 3190279 := bstep (se 1 (by rfl) ⟨2392709, by rfl⟩ : syracuseStep 3190279 = 4785419) B4785419
theorem B798227 : Blo 235815 798227 := bstep (se 1 (by rfl) ⟨598670, by rfl⟩ : syracuseStep 798227 = 1197341) B1197341
theorem B798551 : Blo 235815 798551 := bstep (se 1 (by rfl) ⟨598913, by rfl⟩ : syracuseStep 798551 = 1197827) B1197827
theorem B798875 : Blo 235815 798875 := bstep (se 1 (by rfl) ⟨599156, by rfl⟩ : syracuseStep 798875 = 1198313) B1198313
theorem B2765137 : Blo 235815 2765137 := bstep (se 2 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 2765137 = 2073853) B2073853
theorem B799145 : Blo 235815 799145 := bstep (se 2 (by rfl) ⟨299679, by rfl⟩ : syracuseStep 799145 = 599359) B599359
theorem B799199 : Blo 235815 799199 := bstep (se 1 (by rfl) ⟨599399, by rfl⟩ : syracuseStep 799199 = 1198799) B1198799
theorem B799361 : Blo 235815 799361 := bstep (se 2 (by rfl) ⟨299760, by rfl⟩ : syracuseStep 799361 = 599521) B599521
theorem B3028265 : Blo 235815 3028265 := bstep (se 2 (by rfl) ⟨1135599, by rfl⟩ : syracuseStep 3028265 = 2271199) B2271199
theorem B538847 : Blo 235815 538847 := bstep (se 1 (by rfl) ⟨404135, by rfl⟩ : syracuseStep 538847 = 808271) B808271
theorem B539387 : Blo 235815 539387 := bstep (se 1 (by rfl) ⟨404540, by rfl⟩ : syracuseStep 539387 = 809081) B809081
theorem B41827195 : Blo 235815 41827195 := bstep (se 1 (by rfl) ⟨31370396, by rfl⟩ : syracuseStep 41827195 = 62740793) B62740793
theorem B1293185 : Blo 235815 1293185 := bstep (se 2 (by rfl) ⟨484944, by rfl⟩ : syracuseStep 1293185 = 969889) B969889
theorem B507035 : Blo 235815 507035 := bstep (se 1 (by rfl) ⟨380276, by rfl⟩ : syracuseStep 507035 = 760553) B760553
theorem B606143 : Blo 235815 606143 := bstep (se 1 (by rfl) ⟨454607, by rfl⟩ : syracuseStep 606143 = 909215) B909215
theorem B1360223 : Blo 235815 1360223 := bstep (se 1 (by rfl) ⟨1020167, by rfl⟩ : syracuseStep 1360223 = 2040335) B2040335
theorem B2015867 : Blo 235815 2015867 := bstep (se 1 (by rfl) ⟨1511900, by rfl⟩ : syracuseStep 2015867 = 3023801) B3023801
theorem B13190471 : Blo 235815 13190471 := bstep (se 1 (by rfl) ⟨9892853, by rfl⟩ : syracuseStep 13190471 = 19785707) B19785707
theorem B43698311 : Blo 235815 43698311 := bstep (se 1 (by rfl) ⟨32773733, by rfl⟩ : syracuseStep 43698311 = 65547467) B65547467
theorem B904871 : Blo 235815 904871 := bstep (se 1 (by rfl) ⟨678653, by rfl⟩ : syracuseStep 904871 = 1357307) B1357307
theorem B5734125917 : Blo 235815 5734125917 := bstep (se 3 (by rfl) ⟨1075148609, by rfl⟩ : syracuseStep 5734125917 = 2150297219) B2150297219
theorem B610823 : Blo 235815 610823 := bstep (se 1 (by rfl) ⟨458117, by rfl⟩ : syracuseStep 610823 = 916235) B916235
theorem B545435 : Blo 235815 545435 := bstep (se 1 (by rfl) ⟨409076, by rfl⟩ : syracuseStep 545435 = 818153) B818153
theorem B676603 : Blo 235815 676603 := bstep (se 1 (by rfl) ⟨507452, by rfl⟩ : syracuseStep 676603 = 1014905) B1014905
theorem B4608899 : Blo 235815 4608899 := bstep (se 1 (by rfl) ⟨3456674, by rfl⟩ : syracuseStep 4608899 = 6913349) B6913349
theorem B1201715 : Blo 235815 1201715 := bstep (se 1 (by rfl) ⟨901286, by rfl⟩ : syracuseStep 1201715 = 1802573) B1802573
theorem B1726319 : Blo 235815 1726319 := bstep (se 1 (by rfl) ⟨1294739, by rfl⟩ : syracuseStep 1726319 = 2589479) B2589479
theorem B6805397 : Blo 235815 6805397 := bstep (se 6 (by rfl) ⟨159501, by rfl⟩ : syracuseStep 6805397 = 319003) B319003
theorem B809615 : Blo 235815 809615 := bstep (se 1 (by rfl) ⟨607211, by rfl⟩ : syracuseStep 809615 = 1214423) B1214423
theorem B383935 : Blo 235815 383935 := bstep (se 1 (by rfl) ⟨287951, by rfl⟩ : syracuseStep 383935 = 575903) B575903
theorem B4054697 : Blo 235815 4054697 := bstep (se 2 (by rfl) ⟨1520511, by rfl⟩ : syracuseStep 4054697 = 3041023) B3041023
theorem B1007387 : Blo 235815 1007387 := bstep (se 1 (by rfl) ⟨755540, by rfl⟩ : syracuseStep 1007387 = 1511081) B1511081
theorem B3498173 : Blo 235815 3498173 := bstep (se 3 (by rfl) ⟨655907, by rfl⟩ : syracuseStep 3498173 = 1311815) B1311815
theorem B2744819 : Blo 235815 2744819 := bstep (se 1 (by rfl) ⟨2058614, by rfl⟩ : syracuseStep 2744819 = 4117229) B4117229
theorem B680795 : Blo 235815 680795 := bstep (se 1 (by rfl) ⟨510596, by rfl⟩ : syracuseStep 680795 = 1021193) B1021193
theorem B451487 : Blo 235815 451487 := bstep (se 1 (by rfl) ⟨338615, by rfl⟩ : syracuseStep 451487 = 677231) B677231
theorem B1205279 : Blo 235815 1205279 := bstep (se 1 (by rfl) ⟨903959, by rfl⟩ : syracuseStep 1205279 = 1807919) B1807919
theorem B353897 : Blo 235815 353897 := bstep (se 2 (by rfl) ⟨132711, by rfl⟩ : syracuseStep 353897 = 265423) B265423
theorem B517979 : Blo 235815 517979 := bstep (se 1 (by rfl) ⟨388484, by rfl⟩ : syracuseStep 517979 = 776969) B776969
theorem B3041387 : Blo 235815 3041387 := bstep (se 1 (by rfl) ⟨2281040, by rfl⟩ : syracuseStep 3041387 = 4562081) B4562081
theorem B354527 : Blo 235815 354527 := bstep (se 1 (by rfl) ⟨265895, by rfl⟩ : syracuseStep 354527 = 531791) B531791
theorem B1010515 : Blo 235815 1010515 := bstep (se 1 (by rfl) ⟨757886, by rfl⟩ : syracuseStep 1010515 = 1515773) B1515773
theorem B355871 : Blo 235815 355871 := bstep (se 1 (by rfl) ⟨266903, by rfl⟩ : syracuseStep 355871 = 533807) B533807
theorem B1207871 : Blo 235815 1207871 := bstep (se 1 (by rfl) ⟨905903, by rfl⟩ : syracuseStep 1207871 = 1811807) B1811807
theorem B4059071 : Blo 235815 4059071 := bstep (se 1 (by rfl) ⟨3044303, by rfl⟩ : syracuseStep 4059071 = 6088607) B6088607
theorem B356519 : Blo 235815 356519 := bstep (se 1 (by rfl) ⟨267389, by rfl⟩ : syracuseStep 356519 = 534779) B534779
theorem B356543 : Blo 235815 356543 := bstep (se 1 (by rfl) ⟨267407, by rfl⟩ : syracuseStep 356543 = 534815) B534815
theorem B356891 : Blo 235815 356891 := bstep (se 1 (by rfl) ⟨267668, by rfl⟩ : syracuseStep 356891 = 535337) B535337
theorem B652063 : Blo 235815 652063 := bstep (se 1 (by rfl) ⟨489047, by rfl⟩ : syracuseStep 652063 = 978095) B978095
theorem B357743 : Blo 235815 357743 := bstep (se 1 (by rfl) ⟨268307, by rfl⟩ : syracuseStep 357743 = 536615) B536615
theorem B357839 : Blo 235815 357839 := bstep (se 1 (by rfl) ⟨268379, by rfl⟩ : syracuseStep 357839 = 536759) B536759
theorem B357929 : Blo 235815 357929 := bstep (se 2 (by rfl) ⟨134223, by rfl⟩ : syracuseStep 357929 = 268447) B268447
theorem B2424167 : Blo 235815 2424167 := bstep (se 1 (by rfl) ⟨1818125, by rfl⟩ : syracuseStep 2424167 = 3636251) B3636251
theorem B1572587 : Blo 235815 1572587 := bstep (se 1 (by rfl) ⟨1179440, by rfl⟩ : syracuseStep 1572587 = 2358881) B2358881
theorem B1343911 : Blo 235815 1343911 := bstep (se 1 (by rfl) ⟨1007933, by rfl⟩ : syracuseStep 1343911 = 2015867) B2015867
theorem B29132207 : Blo 235815 29132207 := bstep (se 1 (by rfl) ⟨21849155, by rfl⟩ : syracuseStep 29132207 = 43698311) B43698311
theorem B1705963 : Blo 235815 1705963 := bstep (se 1 (by rfl) ⟨1279472, by rfl⟩ : syracuseStep 1705963 = 2558945) B2558945
theorem B3822750611 : Blo 235815 3822750611 := bstep (se 1 (by rfl) ⟨2867062958, by rfl⟩ : syracuseStep 3822750611 = 5734125917) B5734125917
theorem B363623 : Blo 235815 363623 := bstep (se 1 (by rfl) ⟨272717, by rfl⟩ : syracuseStep 363623 = 545435) B545435
theorem B265711 : Blo 235815 265711 := bstep (se 1 (by rfl) ⟨199283, by rfl⟩ : syracuseStep 265711 = 398567) B398567
theorem B1347353 : Blo 235815 1347353 := bstep (se 2 (by rfl) ⟨505257, by rfl⟩ : syracuseStep 1347353 = 1010515) B1010515
theorem B397993 : Blo 235815 397993 := bstep (se 2 (by rfl) ⟨149247, by rfl⟩ : syracuseStep 397993 = 298495) B298495
theorem B1381277 : Blo 235815 1381277 := bstep (se 3 (by rfl) ⟨258989, by rfl⟩ : syracuseStep 1381277 = 517979) B517979
theorem B2332115 : Blo 235815 2332115 := bstep (se 1 (by rfl) ⟨1749086, by rfl⟩ : syracuseStep 2332115 = 3498173) B3498173
theorem B268159 : Blo 235815 268159 := bstep (se 1 (by rfl) ⟨201119, by rfl⟩ : syracuseStep 268159 = 402239) B402239
theorem B300991 : Blo 235815 300991 := bstep (se 1 (by rfl) ⟨225743, by rfl⟩ : syracuseStep 300991 = 451487) B451487
theorem B235931 : Blo 235815 235931 := bstep (se 1 (by rfl) ⟨176948, by rfl⟩ : syracuseStep 235931 = 353897) B353897
theorem B236351 : Blo 235815 236351 := bstep (se 1 (by rfl) ⟨177263, by rfl⟩ : syracuseStep 236351 = 354527) B354527
theorem B532151 : Blo 235815 532151 := bstep (se 1 (by rfl) ⟨399113, by rfl⟩ : syracuseStep 532151 = 798227) B798227
theorem B237247 : Blo 235815 237247 := bstep (se 1 (by rfl) ⟨177935, by rfl⟩ : syracuseStep 237247 = 355871) B355871
theorem B532367 : Blo 235815 532367 := bstep (se 1 (by rfl) ⟨399275, by rfl⟩ : syracuseStep 532367 = 798551) B798551
theorem B532583 : Blo 235815 532583 := bstep (se 1 (by rfl) ⟨399437, by rfl⟩ : syracuseStep 532583 = 798875) B798875
theorem B237679 : Blo 235815 237679 := bstep (se 1 (by rfl) ⟨178259, by rfl⟩ : syracuseStep 237679 = 356519) B356519
theorem B237695 : Blo 235815 237695 := bstep (se 1 (by rfl) ⟨178271, by rfl⟩ : syracuseStep 237695 = 356543) B356543
theorem B532763 : Blo 235815 532763 := bstep (se 1 (by rfl) ⟨399572, by rfl⟩ : syracuseStep 532763 = 799145) B799145
theorem B532799 : Blo 235815 532799 := bstep (se 1 (by rfl) ⟨399599, by rfl⟩ : syracuseStep 532799 = 799199) B799199
theorem B237927 : Blo 235815 237927 := bstep (se 1 (by rfl) ⟨178445, by rfl⟩ : syracuseStep 237927 = 356891) B356891
theorem B532907 : Blo 235815 532907 := bstep (se 1 (by rfl) ⟨399680, by rfl⟩ : syracuseStep 532907 = 799361) B799361
theorem B238495 : Blo 235815 238495 := bstep (se 1 (by rfl) ⟨178871, by rfl⟩ : syracuseStep 238495 = 357743) B357743
theorem B238559 : Blo 235815 238559 := bstep (se 1 (by rfl) ⟨178919, by rfl⟩ : syracuseStep 238559 = 357839) B357839
theorem B238619 : Blo 235815 238619 := bstep (se 1 (by rfl) ⟨178964, by rfl⟩ : syracuseStep 238619 = 357929) B357929
theorem B862123 : Blo 235815 862123 := bstep (se 1 (by rfl) ⟨646592, by rfl⟩ : syracuseStep 862123 = 1293185) B1293185
theorem B338023 : Blo 235815 338023 := bstep (se 1 (by rfl) ⟨253517, by rfl⟩ : syracuseStep 338023 = 507035) B507035
theorem B1616111 : Blo 235815 1616111 := bstep (se 1 (by rfl) ⟨1212083, by rfl⟩ : syracuseStep 1616111 = 2424167) B2424167
theorem B404095 : Blo 235815 404095 := bstep (se 1 (by rfl) ⟨303071, by rfl⟩ : syracuseStep 404095 = 606143) B606143
theorem B2272157 : Blo 235815 2272157 := bstep (se 3 (by rfl) ⟨426029, by rfl⟩ : syracuseStep 2272157 = 852059) B852059
theorem B8793647 : Blo 235815 8793647 := bstep (se 1 (by rfl) ⟨6595235, by rfl⟩ : syracuseStep 8793647 = 13190471) B13190471
theorem B537569 : Blo 235815 537569 := bstep (se 2 (by rfl) ⟨201588, by rfl⟩ : syracuseStep 537569 = 403177) B403177
theorem B603247 : Blo 235815 603247 := bstep (se 1 (by rfl) ⟨452435, by rfl⟩ : syracuseStep 603247 = 904871) B904871
theorem B407215 : Blo 235815 407215 := bstep (se 1 (by rfl) ⟨305411, by rfl⟩ : syracuseStep 407215 = 610823) B610823
theorem B800765 : Blo 235815 800765 := bstep (se 3 (by rfl) ⟨150143, by rfl⟩ : syracuseStep 800765 = 300287) B300287
theorem B1357991 : Blo 235815 1357991 := bstep (se 1 (by rfl) ⟨1018493, by rfl⟩ : syracuseStep 1357991 = 2036987) B2036987
theorem B801143 : Blo 235815 801143 := bstep (se 1 (by rfl) ⟨600857, by rfl⟩ : syracuseStep 801143 = 1201715) B1201715
theorem B506351 : Blo 235815 506351 := bstep (se 1 (by rfl) ⟨379763, by rfl⟩ : syracuseStep 506351 = 759527) B759527
theorem B4536931 : Blo 235815 4536931 := bstep (se 1 (by rfl) ⟨3402698, by rfl⟩ : syracuseStep 4536931 = 6805397) B6805397
theorem B899693 : Blo 235815 899693 := bstep (se 3 (by rfl) ⟨168692, by rfl⟩ : syracuseStep 899693 = 337385) B337385
theorem B539743 : Blo 235815 539743 := bstep (se 1 (by rfl) ⟨404807, by rfl⟩ : syracuseStep 539743 = 809615) B809615
theorem B900679 : Blo 235815 900679 := bstep (se 1 (by rfl) ⟨675509, by rfl⟩ : syracuseStep 900679 = 1351019) B1351019
theorem B4603517 : Blo 235815 4603517 := bstep (se 3 (by rfl) ⟨863159, by rfl⟩ : syracuseStep 4603517 = 1726319) B1726319
theorem B2703131 : Blo 235815 2703131 := bstep (se 1 (by rfl) ⟨2027348, by rfl⟩ : syracuseStep 2703131 = 4054697) B4054697
theorem B671591 : Blo 235815 671591 := bstep (se 1 (by rfl) ⟨503693, by rfl⟩ : syracuseStep 671591 = 1007387) B1007387
theorem B901439 : Blo 235815 901439 := bstep (se 1 (by rfl) ⟨676079, by rfl⟩ : syracuseStep 901439 = 1352159) B1352159
theorem B3686849 : Blo 235815 3686849 := bstep (se 2 (by rfl) ⟨1382568, by rfl⟩ : syracuseStep 3686849 = 2765137) B2765137
theorem B803519 : Blo 235815 803519 := bstep (se 1 (by rfl) ⟨602639, by rfl⟩ : syracuseStep 803519 = 1205279) B1205279
theorem B26231597 : Blo 235815 26231597 := bstep (se 3 (by rfl) ⟨4918424, by rfl⟩ : syracuseStep 26231597 = 9836849) B9836849
theorem B902123 : Blo 235815 902123 := bstep (se 1 (by rfl) ⟨676592, by rfl⟩ : syracuseStep 902123 = 1353185) B1353185
theorem B902137 : Blo 235815 902137 := bstep (se 2 (by rfl) ⟨338301, by rfl⟩ : syracuseStep 902137 = 676603) B676603
theorem B869417 : Blo 235815 869417 := bstep (se 2 (by rfl) ⟨326031, by rfl⟩ : syracuseStep 869417 = 652063) B652063
theorem B509179 : Blo 235815 509179 := bstep (se 1 (by rfl) ⟨381884, by rfl⟩ : syracuseStep 509179 = 763769) B763769
theorem B1820555 : Blo 235815 1820555 := bstep (se 1 (by rfl) ⟨1365416, by rfl⟩ : syracuseStep 1820555 = 2730833) B2730833
theorem B805247 : Blo 235815 805247 := bstep (se 1 (by rfl) ⟨603935, by rfl⟩ : syracuseStep 805247 = 1207871) B1207871
theorem B2706047 : Blo 235815 2706047 := bstep (se 1 (by rfl) ⟨2029535, by rfl⟩ : syracuseStep 2706047 = 4059071) B4059071
theorem B2018843 : Blo 235815 2018843 := bstep (se 1 (by rfl) ⟨1514132, by rfl⟩ : syracuseStep 2018843 = 3028265) B3028265
theorem B511913 : Blo 235815 511913 := bstep (se 2 (by rfl) ⟨191967, by rfl⟩ : syracuseStep 511913 = 383935) B383935
theorem B906815 : Blo 235815 906815 := bstep (se 1 (by rfl) ⟨680111, by rfl⟩ : syracuseStep 906815 = 1360223) B1360223
theorem B4348151 : Blo 235815 4348151 := bstep (se 1 (by rfl) ⟨3261113, by rfl⟩ : syracuseStep 4348151 = 6522227) B6522227
theorem B482527 : Blo 235815 482527 := bstep (se 1 (by rfl) ⟨361895, by rfl⟩ : syracuseStep 482527 = 723791) B723791
theorem B614537 : Blo 235815 614537 := bstep (se 2 (by rfl) ⟨230451, by rfl⟩ : syracuseStep 614537 = 460903) B460903
theorem B3072599 : Blo 235815 3072599 := bstep (se 1 (by rfl) ⟨2304449, by rfl⟩ : syracuseStep 3072599 = 4608899) B4608899
theorem B10674953 : Blo 235815 10674953 := bstep (se 2 (by rfl) ⟨4003107, by rfl⟩ : syracuseStep 10674953 = 8006215) B8006215
theorem B353999 : Blo 235815 353999 := bstep (se 1 (by rfl) ⟨265499, by rfl⟩ : syracuseStep 353999 = 530999) B530999
theorem B4253705 : Blo 235815 4253705 := bstep (se 2 (by rfl) ⟨1595139, by rfl⟩ : syracuseStep 4253705 = 3190279) B3190279
theorem B1829879 : Blo 235815 1829879 := bstep (se 1 (by rfl) ⟨1372409, by rfl⟩ : syracuseStep 1829879 = 2744819) B2744819
theorem B453863 : Blo 235815 453863 := bstep (se 1 (by rfl) ⟨340397, by rfl⟩ : syracuseStep 453863 = 680795) B680795
theorem B355631 : Blo 235815 355631 := bstep (se 1 (by rfl) ⟨266723, by rfl⟩ : syracuseStep 355631 = 533447) B533447
theorem B1011113 : Blo 235815 1011113 := bstep (se 2 (by rfl) ⟨379167, by rfl⟩ : syracuseStep 1011113 = 758335) B758335
theorem B1929071 : Blo 235815 1929071 := bstep (se 1 (by rfl) ⟨1446803, by rfl⟩ : syracuseStep 1929071 = 2893607) B2893607
theorem B1535867 : Blo 235815 1535867 := bstep (se 1 (by rfl) ⟨1151900, by rfl⟩ : syracuseStep 1535867 = 2303801) B2303801
theorem B2027591 : Blo 235815 2027591 := bstep (se 1 (by rfl) ⟨1520693, by rfl⟩ : syracuseStep 2027591 = 3041387) B3041387
theorem B356489 : Blo 235815 356489 := bstep (se 2 (by rfl) ⟨133683, by rfl⟩ : syracuseStep 356489 = 267367) B267367
theorem B357071 : Blo 235815 357071 := bstep (se 1 (by rfl) ⟨267803, by rfl⟩ : syracuseStep 357071 = 535607) B535607
theorem B3503969 : Blo 235815 3503969 := bstep (se 2 (by rfl) ⟨1313988, by rfl⟩ : syracuseStep 3503969 = 2627977) B2627977
theorem B55769593 : Blo 235815 55769593 := bstep (se 2 (by rfl) ⟨20913597, by rfl⟩ : syracuseStep 55769593 = 41827195) B41827195
theorem B359231 : Blo 235815 359231 := bstep (se 1 (by rfl) ⟨269423, by rfl⟩ : syracuseStep 359231 = 538847) B538847
theorem B359591 : Blo 235815 359591 := bstep (se 1 (by rfl) ⟨269693, by rfl⟩ : syracuseStep 359591 = 539387) B539387
theorem B1048391 : Blo 235815 1048391 := bstep (se 1 (by rfl) ⟨786293, by rfl⟩ : syracuseStep 1048391 = 1572587) B1572587
theorem B2457899 : Blo 235815 2457899 := bstep (se 1 (by rfl) ⟨1843424, by rfl⟩ : syracuseStep 2457899 = 3686849) B3686849
theorem B1213703 : Blo 235815 1213703 := bstep (se 1 (by rfl) ⟨910277, by rfl⟩ : syracuseStep 1213703 = 1820555) B1820555
theorem B1804031 : Blo 235815 1804031 := bstep (se 1 (by rfl) ⟨1353023, by rfl⟩ : syracuseStep 1804031 = 2706047) B2706047
theorem B2548500407 : Blo 235815 2548500407 := bstep (se 1 (by rfl) ⟨1911375305, by rfl⟩ : syracuseStep 2548500407 = 3822750611) B3822750611
theorem B1345895 : Blo 235815 1345895 := bstep (se 1 (by rfl) ⟨1009421, by rfl⟩ : syracuseStep 1345895 = 2018843) B2018843
theorem B1149497 : Blo 235815 1149497 := bstep (se 2 (by rfl) ⟨431061, by rfl⟩ : syracuseStep 1149497 = 862123) B862123
theorem B920851 : Blo 235815 920851 := bstep (se 1 (by rfl) ⟨690638, by rfl⟩ : syracuseStep 920851 = 1381277) B1381277
theorem B7116635 : Blo 235815 7116635 := bstep (se 1 (by rfl) ⟨5337476, by rfl⟩ : syracuseStep 7116635 = 10674953) B10674953
theorem B530657 : Blo 235815 530657 := bstep (se 2 (by rfl) ⟨198996, by rfl⟩ : syracuseStep 530657 = 397993) B397993
theorem B235999 : Blo 235815 235999 := bstep (se 1 (by rfl) ⟨176999, by rfl⟩ : syracuseStep 235999 = 353999) B353999
theorem B1350269 : Blo 235815 1350269 := bstep (se 3 (by rfl) ⟨253175, by rfl⟩ : syracuseStep 1350269 = 506351) B506351
theorem B1514771 : Blo 235815 1514771 := bstep (se 1 (by rfl) ⟨1136078, by rfl⟩ : syracuseStep 1514771 = 2272157) B2272157
theorem B1219919 : Blo 235815 1219919 := bstep (se 1 (by rfl) ⟨914939, by rfl⟩ : syracuseStep 1219919 = 1829879) B1829879
theorem B237087 : Blo 235815 237087 := bstep (se 1 (by rfl) ⟨177815, by rfl⟩ : syracuseStep 237087 = 355631) B355631
theorem B1286047 : Blo 235815 1286047 := bstep (se 1 (by rfl) ⟨964535, by rfl⟩ : syracuseStep 1286047 = 1929071) B1929071
theorem B1023911 : Blo 235815 1023911 := bstep (se 1 (by rfl) ⟨767933, by rfl⟩ : syracuseStep 1023911 = 1535867) B1535867
theorem B401321 : Blo 235815 401321 := bstep (se 2 (by rfl) ⟨150495, by rfl⟩ : syracuseStep 401321 = 300991) B300991
theorem B1351727 : Blo 235815 1351727 := bstep (se 1 (by rfl) ⟨1013795, by rfl⟩ : syracuseStep 1351727 = 2027591) B2027591
theorem B237659 : Blo 235815 237659 := bstep (se 1 (by rfl) ⟨178244, by rfl⟩ : syracuseStep 237659 = 356489) B356489
theorem B238047 : Blo 235815 238047 := bstep (se 1 (by rfl) ⟨178535, by rfl⟩ : syracuseStep 238047 = 357071) B357071
theorem B74359457 : Blo 235815 74359457 := bstep (se 2 (by rfl) ⟨27884796, by rfl⟩ : syracuseStep 74359457 = 55769593) B55769593
theorem B2335979 : Blo 235815 2335979 := bstep (se 1 (by rfl) ⟨1751984, by rfl⟩ : syracuseStep 2335979 = 3503969) B3503969
theorem B533843 : Blo 235815 533843 := bstep (se 1 (by rfl) ⟨400382, by rfl⟩ : syracuseStep 533843 = 800765) B800765
theorem B534095 : Blo 235815 534095 := bstep (se 1 (by rfl) ⟨400571, by rfl⟩ : syracuseStep 534095 = 801143) B801143
theorem B599795 : Blo 235815 599795 := bstep (se 1 (by rfl) ⟨449846, by rfl⟩ : syracuseStep 599795 = 899693) B899693
theorem B239487 : Blo 235815 239487 := bstep (se 1 (by rfl) ⟨179615, by rfl⟩ : syracuseStep 239487 = 359231) B359231
theorem B239727 : Blo 235815 239727 := bstep (se 1 (by rfl) ⟨179795, by rfl⟩ : syracuseStep 239727 = 359591) B359591
theorem B698927 : Blo 235815 698927 := bstep (se 1 (by rfl) ⟨524195, by rfl⟩ : syracuseStep 698927 = 1048391) B1048391
theorem B600959 : Blo 235815 600959 := bstep (se 1 (by rfl) ⟨450719, by rfl⟩ : syracuseStep 600959 = 901439) B901439
theorem B535679 : Blo 235815 535679 := bstep (se 1 (by rfl) ⟨401759, by rfl⟩ : syracuseStep 535679 = 803519) B803519
theorem B601415 : Blo 235815 601415 := bstep (se 1 (by rfl) ⟨451061, by rfl⟩ : syracuseStep 601415 = 902123) B902123
theorem B536831 : Blo 235815 536831 := bstep (se 1 (by rfl) ⟨402623, by rfl⟩ : syracuseStep 536831 = 805247) B805247
theorem B898235 : Blo 235815 898235 := bstep (se 1 (by rfl) ⟨673676, by rfl⟩ : syracuseStep 898235 = 1347353) B1347353
theorem B341275 : Blo 235815 341275 := bstep (se 1 (by rfl) ⟨255956, by rfl⟩ : syracuseStep 341275 = 511913) B511913
theorem B2274617 : Blo 235815 2274617 := bstep (se 2 (by rfl) ⟨852981, by rfl⟩ : syracuseStep 2274617 = 1705963) B1705963
theorem B538793 : Blo 235815 538793 := bstep (se 2 (by rfl) ⟨202047, by rfl⟩ : syracuseStep 538793 = 404095) B404095
theorem B1554743 : Blo 235815 1554743 := bstep (se 1 (by rfl) ⟨1166057, by rfl⟩ : syracuseStep 1554743 = 2332115) B2332115
theorem B604543 : Blo 235815 604543 := bstep (se 1 (by rfl) ⟨453407, by rfl⟩ : syracuseStep 604543 = 906815) B906815
theorem B2898767 : Blo 235815 2898767 := bstep (se 1 (by rfl) ⟨2174075, by rfl⟩ : syracuseStep 2898767 = 4348151) B4348151
theorem B409691 : Blo 235815 409691 := bstep (se 1 (by rfl) ⟨307268, by rfl⟩ : syracuseStep 409691 = 614537) B614537
theorem B2048399 : Blo 235815 2048399 := bstep (se 1 (by rfl) ⟨1536299, by rfl⟩ : syracuseStep 2048399 = 3072599) B3072599
theorem B2573477 : Blo 235815 2573477 := bstep (se 4 (by rfl) ⟨241263, by rfl⟩ : syracuseStep 2573477 = 482527) B482527
theorem B2835803 : Blo 235815 2835803 := bstep (se 1 (by rfl) ⟨2126852, by rfl⟩ : syracuseStep 2835803 = 4253705) B4253705
theorem B804329 : Blo 235815 804329 := bstep (se 2 (by rfl) ⟨301623, by rfl⟩ : syracuseStep 804329 = 603247) B603247
theorem B542953 : Blo 235815 542953 := bstep (se 2 (by rfl) ⟨203607, by rfl⟩ : syracuseStep 542953 = 407215) B407215
theorem B674075 : Blo 235815 674075 := bstep (se 1 (by rfl) ⟨505556, by rfl⟩ : syracuseStep 674075 = 1011113) B1011113
theorem B969661 : Blo 235815 969661 := bstep (se 3 (by rfl) ⟨181811, by rfl⟩ : syracuseStep 969661 = 363623) B363623
theorem B6049241 : Blo 235815 6049241 := bstep (se 2 (by rfl) ⟨2268465, by rfl⟩ : syracuseStep 6049241 = 4536931) B4536931
theorem B905327 : Blo 235815 905327 := bstep (se 1 (by rfl) ⟨678995, by rfl⟩ : syracuseStep 905327 = 1357991) B1357991
theorem B1200905 : Blo 235815 1200905 := bstep (se 2 (by rfl) ⟨450339, by rfl⟩ : syracuseStep 1200905 = 900679) B900679
theorem B1790909 : Blo 235815 1790909 := bstep (se 3 (by rfl) ⟨335795, by rfl⟩ : syracuseStep 1790909 = 671591) B671591
theorem B3069011 : Blo 235815 3069011 := bstep (se 1 (by rfl) ⟨2301758, by rfl⟩ : syracuseStep 3069011 = 4603517) B4603517
theorem B17487731 : Blo 235815 17487731 := bstep (se 1 (by rfl) ⟨13115798, by rfl⟩ : syracuseStep 17487731 = 26231597) B26231597
theorem B1791881 : Blo 235815 1791881 := bstep (se 2 (by rfl) ⟨671955, by rfl⟩ : syracuseStep 1791881 = 1343911) B1343911
theorem B579611 : Blo 235815 579611 := bstep (se 1 (by rfl) ⟨434708, by rfl⟩ : syracuseStep 579611 = 869417) B869417
theorem B19421471 : Blo 235815 19421471 := bstep (se 1 (by rfl) ⟨14566103, by rfl⟩ : syracuseStep 19421471 = 29132207) B29132207
theorem B1202849 : Blo 235815 1202849 := bstep (se 2 (by rfl) ⟨451068, by rfl⟩ : syracuseStep 1202849 = 902137) B902137
theorem B678905 : Blo 235815 678905 := bstep (se 2 (by rfl) ⟨254589, by rfl⟩ : syracuseStep 678905 = 509179) B509179
theorem B450697 : Blo 235815 450697 := bstep (se 2 (by rfl) ⟨169011, by rfl⟩ : syracuseStep 450697 = 338023) B338023
theorem B354281 : Blo 235815 354281 := bstep (se 2 (by rfl) ⟨132855, by rfl⟩ : syracuseStep 354281 = 265711) B265711
theorem B354767 : Blo 235815 354767 := bstep (se 1 (by rfl) ⟨266075, by rfl⟩ : syracuseStep 354767 = 532151) B532151
theorem B354911 : Blo 235815 354911 := bstep (se 1 (by rfl) ⟨266183, by rfl⟩ : syracuseStep 354911 = 532367) B532367
theorem B355055 : Blo 235815 355055 := bstep (se 1 (by rfl) ⟨266291, by rfl⟩ : syracuseStep 355055 = 532583) B532583
theorem B355175 : Blo 235815 355175 := bstep (se 1 (by rfl) ⟨266381, by rfl⟩ : syracuseStep 355175 = 532763) B532763
theorem B355199 : Blo 235815 355199 := bstep (se 1 (by rfl) ⟨266399, by rfl⟩ : syracuseStep 355199 = 532799) B532799
theorem B355271 : Blo 235815 355271 := bstep (se 1 (by rfl) ⟨266453, by rfl⟩ : syracuseStep 355271 = 532907) B532907
theorem B1077407 : Blo 235815 1077407 := bstep (se 1 (by rfl) ⟨808055, by rfl⟩ : syracuseStep 1077407 = 1616111) B1616111
theorem B5862431 : Blo 235815 5862431 := bstep (se 1 (by rfl) ⟨4396823, by rfl⟩ : syracuseStep 5862431 = 8793647) B8793647
theorem B357545 : Blo 235815 357545 := bstep (se 2 (by rfl) ⟨134079, by rfl⟩ : syracuseStep 357545 = 268159) B268159
theorem B1210301 : Blo 235815 1210301 := bstep (se 3 (by rfl) ⟨226931, by rfl⟩ : syracuseStep 1210301 = 453863) B453863
theorem B358379 : Blo 235815 358379 := bstep (se 1 (by rfl) ⟨268784, by rfl⟩ : syracuseStep 358379 = 537569) B537569
theorem B719657 : Blo 235815 719657 := bstep (se 2 (by rfl) ⟨269871, by rfl⟩ : syracuseStep 719657 = 539743) B539743
theorem B1802087 : Blo 235815 1802087 := bstep (se 1 (by rfl) ⟨1351565, by rfl⟩ : syracuseStep 1802087 = 2703131) B2703131
theorem B1638599 : Blo 235815 1638599 := bstep (se 1 (by rfl) ⟨1228949, by rfl⟩ : syracuseStep 1638599 = 2457899) B2457899
theorem B4032827 : Blo 235815 4032827 := bstep (se 1 (by rfl) ⟨3024620, by rfl⟩ : syracuseStep 4032827 = 6049241) B6049241
theorem B267547 : Blo 235815 267547 := bstep (se 1 (by rfl) ⟨200660, by rfl⟩ : syracuseStep 267547 = 401321) B401321
theorem B399863 : Blo 235815 399863 := bstep (se 1 (by rfl) ⟨299897, by rfl⟩ : syracuseStep 399863 = 599795) B599795
theorem B236187 : Blo 235815 236187 := bstep (se 1 (by rfl) ⟨177140, by rfl⟩ : syracuseStep 236187 = 354281) B354281
theorem B236511 : Blo 235815 236511 := bstep (se 1 (by rfl) ⟨177383, by rfl⟩ : syracuseStep 236511 = 354767) B354767
theorem B236607 : Blo 235815 236607 := bstep (se 1 (by rfl) ⟨177455, by rfl⟩ : syracuseStep 236607 = 354911) B354911
theorem B236703 : Blo 235815 236703 := bstep (se 1 (by rfl) ⟨177527, by rfl⟩ : syracuseStep 236703 = 355055) B355055
theorem B236783 : Blo 235815 236783 := bstep (se 1 (by rfl) ⟨177587, by rfl⟩ : syracuseStep 236783 = 355175) B355175
theorem B236799 : Blo 235815 236799 := bstep (se 1 (by rfl) ⟨177599, by rfl⟩ : syracuseStep 236799 = 355199) B355199
theorem B400639 : Blo 235815 400639 := bstep (se 1 (by rfl) ⟨300479, by rfl⟩ : syracuseStep 400639 = 600959) B600959
theorem B236847 : Blo 235815 236847 := bstep (se 1 (by rfl) ⟨177635, by rfl⟩ : syracuseStep 236847 = 355271) B355271
theorem B400943 : Blo 235815 400943 := bstep (se 1 (by rfl) ⟨300707, by rfl⟩ : syracuseStep 400943 = 601415) B601415
theorem B3908287 : Blo 235815 3908287 := bstep (se 1 (by rfl) ⟨2931215, by rfl⟩ : syracuseStep 3908287 = 5862431) B5862431
theorem B238363 : Blo 235815 238363 := bstep (se 1 (by rfl) ⟨178772, by rfl⟩ : syracuseStep 238363 = 357545) B357545
theorem B598823 : Blo 235815 598823 := bstep (se 1 (by rfl) ⟨449117, by rfl⟩ : syracuseStep 598823 = 898235) B898235
theorem B1516411 : Blo 235815 1516411 := bstep (se 1 (by rfl) ⟨1137308, by rfl⟩ : syracuseStep 1516411 = 2274617) B2274617
theorem B3253117 : Blo 235815 3253117 := bstep (se 3 (by rfl) ⟨609959, by rfl⟩ : syracuseStep 3253117 = 1219919) B1219919
theorem B238919 : Blo 235815 238919 := bstep (se 1 (by rfl) ⟨179189, by rfl⟩ : syracuseStep 238919 = 358379) B358379
theorem B1714729 : Blo 235815 1714729 := bstep (se 2 (by rfl) ⟨643023, by rfl⟩ : syracuseStep 1714729 = 1286047) B1286047
theorem B600929 : Blo 235815 600929 := bstep (se 2 (by rfl) ⟨225348, by rfl⟩ : syracuseStep 600929 = 450697) B450697
theorem B1092509 : Blo 235815 1092509 := bstep (se 3 (by rfl) ⟨204845, by rfl⟩ : syracuseStep 1092509 = 409691) B409691
theorem B1715651 : Blo 235815 1715651 := bstep (se 1 (by rfl) ⟨1286738, by rfl⟩ : syracuseStep 1715651 = 2573477) B2573477
theorem B536219 : Blo 235815 536219 := bstep (se 1 (by rfl) ⟨402164, by rfl⟩ : syracuseStep 536219 = 804329) B804329
theorem B2895749 : Blo 235815 2895749 := bstep (se 4 (by rfl) ⟨271476, by rfl⟩ : syracuseStep 2895749 = 542953) B542953
theorem B1699000271 : Blo 235815 1699000271 := bstep (se 1 (by rfl) ⟨1274250203, by rfl⟩ : syracuseStep 1699000271 = 2548500407) B2548500407
theorem B897263 : Blo 235815 897263 := bstep (se 1 (by rfl) ⟨672947, by rfl⟩ : syracuseStep 897263 = 1345895) B1345895
theorem B766331 : Blo 235815 766331 := bstep (se 1 (by rfl) ⟨574748, by rfl⟩ : syracuseStep 766331 = 1149497) B1149497
theorem B603551 : Blo 235815 603551 := bstep (se 1 (by rfl) ⟨452663, by rfl⟩ : syracuseStep 603551 = 905327) B905327
theorem B800603 : Blo 235815 800603 := bstep (se 1 (by rfl) ⟨600452, by rfl⟩ : syracuseStep 800603 = 1200905) B1200905
theorem B1193939 : Blo 235815 1193939 := bstep (se 1 (by rfl) ⟨895454, by rfl⟩ : syracuseStep 1193939 = 1790909) B1790909
theorem B2046007 : Blo 235815 2046007 := bstep (se 1 (by rfl) ⟨1534505, by rfl⟩ : syracuseStep 2046007 = 3069011) B3069011
theorem B1194587 : Blo 235815 1194587 := bstep (se 1 (by rfl) ⟨895940, by rfl⟩ : syracuseStep 1194587 = 1791881) B1791881
theorem B900179 : Blo 235815 900179 := bstep (se 1 (by rfl) ⟨675134, by rfl⟩ : syracuseStep 900179 = 1350269) B1350269
theorem B801899 : Blo 235815 801899 := bstep (se 1 (by rfl) ⟨601424, by rfl⟩ : syracuseStep 801899 = 1202849) B1202849
theorem B901151 : Blo 235815 901151 := bstep (se 1 (by rfl) ⟨675863, by rfl⟩ : syracuseStep 901151 = 1351727) B1351727
theorem B51790589 : Blo 235815 51790589 := bstep (se 3 (by rfl) ⟨9710735, by rfl⟩ : syracuseStep 51790589 = 19421471) B19421471
theorem B1557319 : Blo 235815 1557319 := bstep (se 1 (by rfl) ⟨1167989, by rfl⟩ : syracuseStep 1557319 = 2335979) B2335979
theorem B806057 : Blo 235815 806057 := bstep (se 2 (by rfl) ⟨302271, by rfl⟩ : syracuseStep 806057 = 604543) B604543
theorem B806867 : Blo 235815 806867 := bstep (se 1 (by rfl) ⟨605150, by rfl⟩ : syracuseStep 806867 = 1210301) B1210301
theorem B1036495 : Blo 235815 1036495 := bstep (se 1 (by rfl) ⟨777371, by rfl⟩ : syracuseStep 1036495 = 1554743) B1554743
theorem B479771 : Blo 235815 479771 := bstep (se 1 (by rfl) ⟨359828, by rfl⟩ : syracuseStep 479771 = 719657) B719657
theorem B1201391 : Blo 235815 1201391 := bstep (se 1 (by rfl) ⟨901043, by rfl⟩ : syracuseStep 1201391 = 1802087) B1802087
theorem B1365599 : Blo 235815 1365599 := bstep (se 1 (by rfl) ⟨1024199, by rfl⟩ : syracuseStep 1365599 = 2048399) B2048399
theorem B809135 : Blo 235815 809135 := bstep (se 1 (by rfl) ⟨606851, by rfl⟩ : syracuseStep 809135 = 1213703) B1213703
theorem B1890535 : Blo 235815 1890535 := bstep (se 1 (by rfl) ⟨1417901, by rfl⟩ : syracuseStep 1890535 = 2835803) B2835803
theorem B1202687 : Blo 235815 1202687 := bstep (se 1 (by rfl) ⟨902015, by rfl⟩ : syracuseStep 1202687 = 1804031) B1804031
theorem B449383 : Blo 235815 449383 := bstep (se 1 (by rfl) ⟨337037, by rfl⟩ : syracuseStep 449383 = 674075) B674075
theorem B4744423 : Blo 235815 4744423 := bstep (se 1 (by rfl) ⟨3558317, by rfl⟩ : syracuseStep 4744423 = 7116635) B7116635
theorem B11658487 : Blo 235815 11658487 := bstep (se 1 (by rfl) ⟨8743865, by rfl⟩ : syracuseStep 11658487 = 17487731) B17487731
theorem B386407 : Blo 235815 386407 := bstep (se 1 (by rfl) ⟨289805, by rfl⟩ : syracuseStep 386407 = 579611) B579611
theorem B353771 : Blo 235815 353771 := bstep (se 1 (by rfl) ⟨265328, by rfl⟩ : syracuseStep 353771 = 530657) B530657
theorem B452603 : Blo 235815 452603 := bstep (se 1 (by rfl) ⟨339452, by rfl⟩ : syracuseStep 452603 = 678905) B678905
theorem B1009847 : Blo 235815 1009847 := bstep (se 1 (by rfl) ⟨757385, by rfl⟩ : syracuseStep 1009847 = 1514771) B1514771
theorem B5171525 : Blo 235815 5171525 := bstep (se 4 (by rfl) ⟨484830, by rfl⟩ : syracuseStep 5171525 = 969661) B969661
theorem B682607 : Blo 235815 682607 := bstep (se 1 (by rfl) ⟨511955, by rfl⟩ : syracuseStep 682607 = 1023911) B1023911
theorem B49572971 : Blo 235815 49572971 := bstep (se 1 (by rfl) ⟨37179728, by rfl⟩ : syracuseStep 49572971 = 74359457) B74359457
theorem B355895 : Blo 235815 355895 := bstep (se 1 (by rfl) ⟨266921, by rfl⟩ : syracuseStep 355895 = 533843) B533843
theorem B356063 : Blo 235815 356063 := bstep (se 1 (by rfl) ⟨267047, by rfl⟩ : syracuseStep 356063 = 534095) B534095
theorem B4911205 : Blo 235815 4911205 := bstep (se 4 (by rfl) ⟨460425, by rfl⟩ : syracuseStep 4911205 = 920851) B920851
theorem B1863805 : Blo 235815 1863805 := bstep (se 3 (by rfl) ⟨349463, by rfl⟩ : syracuseStep 1863805 = 698927) B698927
theorem B455033 : Blo 235815 455033 := bstep (se 2 (by rfl) ⟨170637, by rfl⟩ : syracuseStep 455033 = 341275) B341275
theorem B357119 : Blo 235815 357119 := bstep (se 1 (by rfl) ⟨267839, by rfl⟩ : syracuseStep 357119 = 535679) B535679
theorem B718271 : Blo 235815 718271 := bstep (se 1 (by rfl) ⟨538703, by rfl⟩ : syracuseStep 718271 = 1077407) B1077407
theorem B357887 : Blo 235815 357887 := bstep (se 1 (by rfl) ⟨268415, by rfl⟩ : syracuseStep 357887 = 536831) B536831
theorem B359195 : Blo 235815 359195 := bstep (se 1 (by rfl) ⟨269396, by rfl⟩ : syracuseStep 359195 = 538793) B538793
theorem B1932511 : Blo 235815 1932511 := bstep (se 1 (by rfl) ⟨1449383, by rfl⟩ : syracuseStep 1932511 = 2898767) B2898767
theorem B5211049 : Blo 235815 5211049 := bstep (se 2 (by rfl) ⟨1954143, by rfl⟩ : syracuseStep 5211049 = 3908287) B3908287
theorem B2688551 : Blo 235815 2688551 := bstep (se 1 (by rfl) ⟨2016413, by rfl⟩ : syracuseStep 2688551 = 4032827) B4032827
theorem B6325897 : Blo 235815 6325897 := bstep (se 2 (by rfl) ⟨2372211, by rfl⟩ : syracuseStep 6325897 = 4744423) B4744423
theorem B266575 : Blo 235815 266575 := bstep (se 1 (by rfl) ⟨199931, by rfl⟩ : syracuseStep 266575 = 399863) B399863
theorem B267295 : Blo 235815 267295 := bstep (se 1 (by rfl) ⟨200471, by rfl⟩ : syracuseStep 267295 = 400943) B400943
theorem B2692925 : Blo 235815 2692925 := bstep (se 3 (by rfl) ⟨504923, by rfl⟩ : syracuseStep 2692925 = 1009847) B1009847
theorem B399215 : Blo 235815 399215 := bstep (se 1 (by rfl) ⟨299411, by rfl⟩ : syracuseStep 399215 = 598823) B598823
theorem B235847 : Blo 235815 235847 := bstep (se 1 (by rfl) ⟨176885, by rfl⟩ : syracuseStep 235847 = 353771) B353771
theorem B301735 : Blo 235815 301735 := bstep (se 1 (by rfl) ⟨226301, by rfl⟩ : syracuseStep 301735 = 452603) B452603
theorem B3447683 : Blo 235815 3447683 := bstep (se 1 (by rfl) ⟨2585762, by rfl⟩ : syracuseStep 3447683 = 5171525) B5171525
theorem B400619 : Blo 235815 400619 := bstep (se 1 (by rfl) ⟨300464, by rfl⟩ : syracuseStep 400619 = 600929) B600929
theorem B237263 : Blo 235815 237263 := bstep (se 1 (by rfl) ⟨177947, by rfl⟩ : syracuseStep 237263 = 355895) B355895
theorem B237375 : Blo 235815 237375 := bstep (se 1 (by rfl) ⟨178031, by rfl⟩ : syracuseStep 237375 = 356063) B356063
theorem B1132666847 : Blo 235815 1132666847 := bstep (se 1 (by rfl) ⟨849500135, by rfl⟩ : syracuseStep 1132666847 = 1699000271) B1699000271
theorem B2728009 : Blo 235815 2728009 := bstep (se 2 (by rfl) ⟨1023003, by rfl⟩ : syracuseStep 2728009 = 2046007) B2046007
theorem B598175 : Blo 235815 598175 := bstep (se 1 (by rfl) ⟨448631, by rfl⟩ : syracuseStep 598175 = 897263) B897263
theorem B303355 : Blo 235815 303355 := bstep (se 1 (by rfl) ⟨227516, by rfl⟩ : syracuseStep 303355 = 455033) B455033
theorem B238079 : Blo 235815 238079 := bstep (se 1 (by rfl) ⟨178559, by rfl⟩ : syracuseStep 238079 = 357119) B357119
theorem B402367 : Blo 235815 402367 := bstep (se 1 (by rfl) ⟨301775, by rfl⟩ : syracuseStep 402367 = 603551) B603551
theorem B238591 : Blo 235815 238591 := bstep (se 1 (by rfl) ⟨178943, by rfl⟩ : syracuseStep 238591 = 357887) B357887
theorem B599177 : Blo 235815 599177 := bstep (se 2 (by rfl) ⟨224691, by rfl⟩ : syracuseStep 599177 = 449383) B449383
theorem B533735 : Blo 235815 533735 := bstep (se 1 (by rfl) ⟨400301, by rfl⟩ : syracuseStep 533735 = 800603) B800603
theorem B795959 : Blo 235815 795959 := bstep (se 1 (by rfl) ⟨596969, by rfl⟩ : syracuseStep 795959 = 1193939) B1193939
theorem B534185 : Blo 235815 534185 := bstep (se 2 (by rfl) ⟨200319, by rfl⟩ : syracuseStep 534185 = 400639) B400639
theorem B796391 : Blo 235815 796391 := bstep (se 1 (by rfl) ⟨597293, by rfl⟩ : syracuseStep 796391 = 1194587) B1194587
theorem B239463 : Blo 235815 239463 := bstep (se 1 (by rfl) ⟨179597, by rfl⟩ : syracuseStep 239463 = 359195) B359195
theorem B600119 : Blo 235815 600119 := bstep (se 1 (by rfl) ⟨450089, by rfl⟩ : syracuseStep 600119 = 900179) B900179
theorem B534599 : Blo 235815 534599 := bstep (se 1 (by rfl) ⟨400949, by rfl⟩ : syracuseStep 534599 = 801899) B801899
theorem B600767 : Blo 235815 600767 := bstep (se 1 (by rfl) ⟨450575, by rfl⟩ : syracuseStep 600767 = 901151) B901151
theorem B2076425 : Blo 235815 2076425 := bstep (se 2 (by rfl) ⟨778659, by rfl⟩ : syracuseStep 2076425 = 1557319) B1557319
theorem B4337489 : Blo 235815 4337489 := bstep (se 2 (by rfl) ⟨1626558, by rfl⟩ : syracuseStep 4337489 = 3253117) B3253117
theorem B15544649 : Blo 235815 15544649 := bstep (se 2 (by rfl) ⟨5829243, by rfl⟩ : syracuseStep 15544649 = 11658487) B11658487
theorem B17478389 : Blo 235815 17478389 := bstep (se 5 (by rfl) ⟨819299, by rfl⟩ : syracuseStep 17478389 = 1638599) B1638599
theorem B537371 : Blo 235815 537371 := bstep (se 1 (by rfl) ⟨403028, by rfl⟩ : syracuseStep 537371 = 806057) B806057
theorem B537911 : Blo 235815 537911 := bstep (se 1 (by rfl) ⟨403433, by rfl⟩ : syracuseStep 537911 = 806867) B806867
theorem B800927 : Blo 235815 800927 := bstep (se 1 (by rfl) ⟨600695, by rfl⟩ : syracuseStep 800927 = 1201391) B1201391
theorem B539423 : Blo 235815 539423 := bstep (se 1 (by rfl) ⟨404567, by rfl⟩ : syracuseStep 539423 = 809135) B809135
theorem B801791 : Blo 235815 801791 := bstep (se 1 (by rfl) ⟨601343, by rfl⟩ : syracuseStep 801791 = 1202687) B1202687
theorem B46613717 : Blo 235815 46613717 := bstep (se 7 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 46613717 = 1092509) B1092509
theorem B33048647 : Blo 235815 33048647 := bstep (se 1 (by rfl) ⟨24786485, by rfl⟩ : syracuseStep 33048647 = 49572971) B49572971
theorem B510887 : Blo 235815 510887 := bstep (se 1 (by rfl) ⟨383165, by rfl⟩ : syracuseStep 510887 = 766331) B766331
theorem B478847 : Blo 235815 478847 := bstep (se 1 (by rfl) ⟨359135, by rfl⟩ : syracuseStep 478847 = 718271) B718271
theorem B2576681 : Blo 235815 2576681 := bstep (se 2 (by rfl) ⟨966255, by rfl⟩ : syracuseStep 2576681 = 1932511) B1932511
theorem B34527059 : Blo 235815 34527059 := bstep (se 1 (by rfl) ⟨25895294, by rfl⟩ : syracuseStep 34527059 = 51790589) B51790589
theorem B5527973 : Blo 235815 5527973 := bstep (se 4 (by rfl) ⟨518247, by rfl⟩ : syracuseStep 5527973 = 1036495) B1036495
theorem B2021881 : Blo 235815 2021881 := bstep (se 2 (by rfl) ⟨758205, by rfl⟩ : syracuseStep 2021881 = 1516411) B1516411
theorem B515209 : Blo 235815 515209 := bstep (se 2 (by rfl) ⟨193203, by rfl⟩ : syracuseStep 515209 = 386407) B386407
theorem B319847 : Blo 235815 319847 := bstep (se 1 (by rfl) ⟨239885, by rfl⟩ : syracuseStep 319847 = 479771) B479771
theorem B2286305 : Blo 235815 2286305 := bstep (se 2 (by rfl) ⟨857364, by rfl⟩ : syracuseStep 2286305 = 1714729) B1714729
theorem B910399 : Blo 235815 910399 := bstep (se 1 (by rfl) ⟨682799, by rfl⟩ : syracuseStep 910399 = 1365599) B1365599
theorem B6548273 : Blo 235815 6548273 := bstep (se 2 (by rfl) ⟨2455602, by rfl⟩ : syracuseStep 6548273 = 4911205) B4911205
theorem B2485073 : Blo 235815 2485073 := bstep (se 2 (by rfl) ⟨931902, by rfl⟩ : syracuseStep 2485073 = 1863805) B1863805
theorem B356729 : Blo 235815 356729 := bstep (se 2 (by rfl) ⟨133773, by rfl⟩ : syracuseStep 356729 = 267547) B267547
theorem B455071 : Blo 235815 455071 := bstep (se 1 (by rfl) ⟨341303, by rfl⟩ : syracuseStep 455071 = 682607) B682607
theorem B1143767 : Blo 235815 1143767 := bstep (se 1 (by rfl) ⟨857825, by rfl⟩ : syracuseStep 1143767 = 1715651) B1715651
theorem B357479 : Blo 235815 357479 := bstep (se 1 (by rfl) ⟨268109, by rfl⟩ : syracuseStep 357479 = 536219) B536219
theorem B1930499 : Blo 235815 1930499 := bstep (se 1 (by rfl) ⟨1447874, by rfl⟩ : syracuseStep 1930499 = 2895749) B2895749
theorem B2520713 : Blo 235815 2520713 := bstep (se 2 (by rfl) ⟨945267, by rfl⟩ : syracuseStep 2520713 = 1890535) B1890535
theorem B14549381 : Blo 235815 14549381 := bstep (se 4 (by rfl) ⟨1364004, by rfl⟩ : syracuseStep 14549381 = 2728009) B2728009
theorem B852925 : Blo 235815 852925 := bstep (se 3 (by rfl) ⟨159923, by rfl⟩ : syracuseStep 852925 = 319847) B319847
theorem B6948065 : Blo 235815 6948065 := bstep (se 2 (by rfl) ⟨2605524, by rfl⟩ : syracuseStep 6948065 = 5211049) B5211049
theorem B1213865 : Blo 235815 1213865 := bstep (se 2 (by rfl) ⟨455199, by rfl⟩ : syracuseStep 1213865 = 910399) B910399
theorem B3050045 : Blo 235815 3050045 := bstep (se 3 (by rfl) ⟨571883, by rfl⟩ : syracuseStep 3050045 = 1143767) B1143767
theorem B266143 : Blo 235815 266143 := bstep (se 1 (by rfl) ⟨199607, by rfl⟩ : syracuseStep 266143 = 399215) B399215
theorem B2298455 : Blo 235815 2298455 := bstep (se 1 (by rfl) ⟨1723841, by rfl⟩ : syracuseStep 2298455 = 3447683) B3447683
theorem B267079 : Blo 235815 267079 := bstep (se 1 (by rfl) ⟨200309, by rfl⟩ : syracuseStep 267079 = 400619) B400619
theorem B755111231 : Blo 235815 755111231 := bstep (se 1 (by rfl) ⟨566333423, by rfl⟩ : syracuseStep 755111231 = 1132666847) B1132666847
theorem B398783 : Blo 235815 398783 := bstep (se 1 (by rfl) ⟨299087, by rfl⟩ : syracuseStep 398783 = 598175) B598175
theorem B399451 : Blo 235815 399451 := bstep (se 1 (by rfl) ⟨299588, by rfl⟩ : syracuseStep 399451 = 599177) B599177
theorem B530639 : Blo 235815 530639 := bstep (se 1 (by rfl) ⟨397979, by rfl⟩ : syracuseStep 530639 = 795959) B795959
theorem B530927 : Blo 235815 530927 := bstep (se 1 (by rfl) ⟨398195, by rfl⟩ : syracuseStep 530927 = 796391) B796391
theorem B400079 : Blo 235815 400079 := bstep (se 1 (by rfl) ⟨300059, by rfl⟩ : syracuseStep 400079 = 600119) B600119
theorem B400511 : Blo 235815 400511 := bstep (se 1 (by rfl) ⟨300383, by rfl⟩ : syracuseStep 400511 = 600767) B600767
theorem B4365515 : Blo 235815 4365515 := bstep (se 1 (by rfl) ⟨3274136, by rfl⟩ : syracuseStep 4365515 = 6548273) B6548273
theorem B6626861 : Blo 235815 6626861 := bstep (se 3 (by rfl) ⟨1242536, by rfl⟩ : syracuseStep 6626861 = 2485073) B2485073
theorem B1384283 : Blo 235815 1384283 := bstep (se 1 (by rfl) ⟨1038212, by rfl⟩ : syracuseStep 1384283 = 2076425) B2076425
theorem B2891659 : Blo 235815 2891659 := bstep (se 1 (by rfl) ⟨2168744, by rfl⟩ : syracuseStep 2891659 = 4337489) B4337489
theorem B10363099 : Blo 235815 10363099 := bstep (se 1 (by rfl) ⟨7772324, by rfl⟩ : syracuseStep 10363099 = 15544649) B15544649
theorem B237819 : Blo 235815 237819 := bstep (se 1 (by rfl) ⟨178364, by rfl⟩ : syracuseStep 237819 = 356729) B356729
theorem B2695841 : Blo 235815 2695841 := bstep (se 2 (by rfl) ⟨1010940, by rfl⟩ : syracuseStep 2695841 = 2021881) B2021881
theorem B238319 : Blo 235815 238319 := bstep (se 1 (by rfl) ⟨178739, by rfl⟩ : syracuseStep 238319 = 357479) B357479
theorem B1286999 : Blo 235815 1286999 := bstep (se 1 (by rfl) ⟨965249, by rfl⟩ : syracuseStep 1286999 = 1930499) B1930499
theorem B402313 : Blo 235815 402313 := bstep (se 2 (by rfl) ⟨150867, by rfl⟩ : syracuseStep 402313 = 301735) B301735
theorem B1680475 : Blo 235815 1680475 := bstep (se 1 (by rfl) ⟨1260356, by rfl⟩ : syracuseStep 1680475 = 2520713) B2520713
theorem B533951 : Blo 235815 533951 := bstep (se 1 (by rfl) ⟨400463, by rfl⟩ : syracuseStep 533951 = 800927) B800927
theorem B534527 : Blo 235815 534527 := bstep (se 1 (by rfl) ⟨400895, by rfl⟩ : syracuseStep 534527 = 801791) B801791
theorem B404473 : Blo 235815 404473 := bstep (se 2 (by rfl) ⟨151677, by rfl⟩ : syracuseStep 404473 = 303355) B303355
theorem B31075811 : Blo 235815 31075811 := bstep (se 1 (by rfl) ⟨23306858, by rfl⟩ : syracuseStep 31075811 = 46613717) B46613717
theorem B536489 : Blo 235815 536489 := bstep (se 2 (by rfl) ⟨201183, by rfl⟩ : syracuseStep 536489 = 402367) B402367
theorem B22032431 : Blo 235815 22032431 := bstep (se 1 (by rfl) ⟨16524323, by rfl⟩ : syracuseStep 22032431 = 33048647) B33048647
theorem B46609037 : Blo 235815 46609037 := bstep (se 3 (by rfl) ⟨8739194, by rfl⟩ : syracuseStep 46609037 = 17478389) B17478389
theorem B8434529 : Blo 235815 8434529 := bstep (se 2 (by rfl) ⟨3162948, by rfl⟩ : syracuseStep 8434529 = 6325897) B6325897
theorem B1717787 : Blo 235815 1717787 := bstep (se 1 (by rfl) ⟨1288340, by rfl⟩ : syracuseStep 1717787 = 2576681) B2576681
theorem B23018039 : Blo 235815 23018039 := bstep (se 1 (by rfl) ⟨17263529, by rfl⟩ : syracuseStep 23018039 = 34527059) B34527059
theorem B1524203 : Blo 235815 1524203 := bstep (se 1 (by rfl) ⟨1143152, by rfl⟩ : syracuseStep 1524203 = 2286305) B2286305
theorem B606761 : Blo 235815 606761 := bstep (se 2 (by rfl) ⟨227535, by rfl⟩ : syracuseStep 606761 = 455071) B455071
theorem B1362365 : Blo 235815 1362365 := bstep (se 3 (by rfl) ⟨255443, by rfl⟩ : syracuseStep 1362365 = 510887) B510887
theorem B1792367 : Blo 235815 1792367 := bstep (se 1 (by rfl) ⟨1344275, by rfl⟩ : syracuseStep 1792367 = 2688551) B2688551
theorem B319231 : Blo 235815 319231 := bstep (se 1 (by rfl) ⟨239423, by rfl⟩ : syracuseStep 319231 = 478847) B478847
theorem B1795283 : Blo 235815 1795283 := bstep (se 1 (by rfl) ⟨1346462, by rfl⟩ : syracuseStep 1795283 = 2692925) B2692925
theorem B355433 : Blo 235815 355433 := bstep (se 2 (by rfl) ⟨133287, by rfl⟩ : syracuseStep 355433 = 266575) B266575
theorem B355823 : Blo 235815 355823 := bstep (se 1 (by rfl) ⟨266867, by rfl⟩ : syracuseStep 355823 = 533735) B533735
theorem B14741261 : Blo 235815 14741261 := bstep (se 3 (by rfl) ⟨2763986, by rfl⟩ : syracuseStep 14741261 = 5527973) B5527973
theorem B356123 : Blo 235815 356123 := bstep (se 1 (by rfl) ⟨267092, by rfl⟩ : syracuseStep 356123 = 534185) B534185
theorem B356393 : Blo 235815 356393 := bstep (se 2 (by rfl) ⟨133647, by rfl⟩ : syracuseStep 356393 = 267295) B267295
theorem B356399 : Blo 235815 356399 := bstep (se 1 (by rfl) ⟨267299, by rfl⟩ : syracuseStep 356399 = 534599) B534599
theorem B358247 : Blo 235815 358247 := bstep (se 1 (by rfl) ⟨268685, by rfl⟩ : syracuseStep 358247 = 537371) B537371
theorem B358607 : Blo 235815 358607 := bstep (se 1 (by rfl) ⟨268955, by rfl⟩ : syracuseStep 358607 = 537911) B537911
theorem B686945 : Blo 235815 686945 := bstep (se 2 (by rfl) ⟨257604, by rfl⟩ : syracuseStep 686945 = 515209) B515209
theorem B359615 : Blo 235815 359615 := bstep (se 1 (by rfl) ⟨269711, by rfl⟩ : syracuseStep 359615 = 539423) B539423
theorem B9699587 : Blo 235815 9699587 := bstep (se 1 (by rfl) ⟨7274690, by rfl⟩ : syracuseStep 9699587 = 14549381) B14549381
theorem B1016135 : Blo 235815 1016135 := bstep (se 1 (by rfl) ⟨762101, by rfl⟩ : syracuseStep 1016135 = 1524203) B1524203
theorem B2033363 : Blo 235815 2033363 := bstep (se 1 (by rfl) ⟨1525022, by rfl⟩ : syracuseStep 2033363 = 3050045) B3050045
theorem B265855 : Blo 235815 265855 := bstep (se 1 (by rfl) ⟨199391, by rfl⟩ : syracuseStep 265855 = 398783) B398783
theorem B266719 : Blo 235815 266719 := bstep (se 1 (by rfl) ⟨200039, by rfl⟩ : syracuseStep 266719 = 400079) B400079
theorem B267007 : Blo 235815 267007 := bstep (se 1 (by rfl) ⟨200255, by rfl⟩ : syracuseStep 267007 = 400511) B400511
theorem B922855 : Blo 235815 922855 := bstep (se 1 (by rfl) ⟨692141, by rfl⟩ : syracuseStep 922855 = 1384283) B1384283
theorem B857999 : Blo 235815 857999 := bstep (se 1 (by rfl) ⟨643499, by rfl⟩ : syracuseStep 857999 = 1286999) B1286999
theorem B236955 : Blo 235815 236955 := bstep (se 1 (by rfl) ⟨177716, by rfl⟩ : syracuseStep 236955 = 355433) B355433
theorem B20717207 : Blo 235815 20717207 := bstep (se 1 (by rfl) ⟨15537905, by rfl⟩ : syracuseStep 20717207 = 31075811) B31075811
theorem B237215 : Blo 235815 237215 := bstep (se 1 (by rfl) ⟨177911, by rfl⟩ : syracuseStep 237215 = 355823) B355823
theorem B237415 : Blo 235815 237415 := bstep (se 1 (by rfl) ⟨178061, by rfl⟩ : syracuseStep 237415 = 356123) B356123
theorem B237595 : Blo 235815 237595 := bstep (se 1 (by rfl) ⟨178196, by rfl⟩ : syracuseStep 237595 = 356393) B356393
theorem B237599 : Blo 235815 237599 := bstep (se 1 (by rfl) ⟨178199, by rfl⟩ : syracuseStep 237599 = 356399) B356399
theorem B14688287 : Blo 235815 14688287 := bstep (se 1 (by rfl) ⟨11016215, by rfl⟩ : syracuseStep 14688287 = 22032431) B22032431
theorem B532601 : Blo 235815 532601 := bstep (se 2 (by rfl) ⟨199725, by rfl⟩ : syracuseStep 532601 = 399451) B399451
theorem B31072691 : Blo 235815 31072691 := bstep (se 1 (by rfl) ⟨23304518, by rfl⟩ : syracuseStep 31072691 = 46609037) B46609037
theorem B238831 : Blo 235815 238831 := bstep (se 1 (by rfl) ⟨179123, by rfl⟩ : syracuseStep 238831 = 358247) B358247
theorem B239071 : Blo 235815 239071 := bstep (se 1 (by rfl) ⟨179303, by rfl⟩ : syracuseStep 239071 = 358607) B358607
theorem B15345359 : Blo 235815 15345359 := bstep (se 1 (by rfl) ⟨11509019, by rfl⟩ : syracuseStep 15345359 = 23018039) B23018039
theorem B239743 : Blo 235815 239743 := bstep (se 1 (by rfl) ⟨179807, by rfl⟩ : syracuseStep 239743 = 359615) B359615
theorem B404507 : Blo 235815 404507 := bstep (se 1 (by rfl) ⟨303380, by rfl⟩ : syracuseStep 404507 = 606761) B606761
theorem B536417 : Blo 235815 536417 := bstep (se 2 (by rfl) ⟨201156, by rfl⟩ : syracuseStep 536417 = 402313) B402313
theorem B2240633 : Blo 235815 2240633 := bstep (se 2 (by rfl) ⟨840237, by rfl⟩ : syracuseStep 2240633 = 1680475) B1680475
theorem B18528173 : Blo 235815 18528173 := bstep (se 3 (by rfl) ⟨3474032, by rfl⟩ : syracuseStep 18528173 = 6948065) B6948065
theorem B539297 : Blo 235815 539297 := bstep (se 2 (by rfl) ⟨202236, by rfl⟩ : syracuseStep 539297 = 404473) B404473
theorem B1194911 : Blo 235815 1194911 := bstep (se 1 (by rfl) ⟨896183, by rfl⟩ : syracuseStep 1194911 = 1792367) B1792367
theorem B1196855 : Blo 235815 1196855 := bstep (se 1 (by rfl) ⟨897641, by rfl⟩ : syracuseStep 1196855 = 1795283) B1795283
theorem B5623019 : Blo 235815 5623019 := bstep (se 1 (by rfl) ⟨4217264, by rfl⟩ : syracuseStep 5623019 = 8434529) B8434529
theorem B3855545 : Blo 235815 3855545 := bstep (se 2 (by rfl) ⟨1445829, by rfl⟩ : syracuseStep 3855545 = 2891659) B2891659
theorem B13817465 : Blo 235815 13817465 := bstep (se 2 (by rfl) ⟨5181549, by rfl⟩ : syracuseStep 13817465 = 10363099) B10363099
theorem B809243 : Blo 235815 809243 := bstep (se 1 (by rfl) ⟨606932, by rfl⟩ : syracuseStep 809243 = 1213865) B1213865
theorem B1137233 : Blo 235815 1137233 := bstep (se 2 (by rfl) ⟨426462, by rfl⟩ : syracuseStep 1137233 = 852925) B852925
theorem B908243 : Blo 235815 908243 := bstep (se 1 (by rfl) ⟨681182, by rfl⟩ : syracuseStep 908243 = 1362365) B1362365
theorem B1532303 : Blo 235815 1532303 := bstep (se 1 (by rfl) ⟨1149227, by rfl⟩ : syracuseStep 1532303 = 2298455) B2298455
theorem B503407487 : Blo 235815 503407487 := bstep (se 1 (by rfl) ⟨377555615, by rfl⟩ : syracuseStep 503407487 = 755111231) B755111231
theorem B353759 : Blo 235815 353759 := bstep (se 1 (by rfl) ⟨265319, by rfl⟩ : syracuseStep 353759 = 530639) B530639
theorem B353951 : Blo 235815 353951 := bstep (se 1 (by rfl) ⟨265463, by rfl⟩ : syracuseStep 353951 = 530927) B530927
theorem B2910343 : Blo 235815 2910343 := bstep (se 1 (by rfl) ⟨2182757, by rfl⟩ : syracuseStep 2910343 = 4365515) B4365515
theorem B4417907 : Blo 235815 4417907 := bstep (se 1 (by rfl) ⟨3313430, by rfl⟩ : syracuseStep 4417907 = 6626861) B6626861
theorem B354857 : Blo 235815 354857 := bstep (se 2 (by rfl) ⟨133071, by rfl⟩ : syracuseStep 354857 = 266143) B266143
theorem B1797227 : Blo 235815 1797227 := bstep (se 1 (by rfl) ⟨1347920, by rfl⟩ : syracuseStep 1797227 = 2695841) B2695841
theorem B355967 : Blo 235815 355967 := bstep (se 1 (by rfl) ⟨266975, by rfl⟩ : syracuseStep 355967 = 533951) B533951
theorem B356105 : Blo 235815 356105 := bstep (se 2 (by rfl) ⟨133539, by rfl⟩ : syracuseStep 356105 = 267079) B267079
theorem B356351 : Blo 235815 356351 := bstep (se 1 (by rfl) ⟨267263, by rfl⟩ : syracuseStep 356351 = 534527) B534527
theorem B9827507 : Blo 235815 9827507 := bstep (se 1 (by rfl) ⟨7370630, by rfl⟩ : syracuseStep 9827507 = 14741261) B14741261
theorem B357659 : Blo 235815 357659 := bstep (se 1 (by rfl) ⟨268244, by rfl⟩ : syracuseStep 357659 = 536489) B536489
theorem B1145191 : Blo 235815 1145191 := bstep (se 1 (by rfl) ⟨858893, by rfl⟩ : syracuseStep 1145191 = 1717787) B1717787
theorem B1702565 : Blo 235815 1702565 := bstep (se 4 (by rfl) ⟨159615, by rfl⟩ : syracuseStep 1702565 = 319231) B319231
theorem B457963 : Blo 235815 457963 := bstep (se 1 (by rfl) ⟨343472, by rfl⟩ : syracuseStep 457963 = 686945) B686945
theorem B9211643 : Blo 235815 9211643 := bstep (se 1 (by rfl) ⟨6908732, by rfl⟩ : syracuseStep 9211643 = 13817465) B13817465
theorem B758155 : Blo 235815 758155 := bstep (se 1 (by rfl) ⟨568616, by rfl⟩ : syracuseStep 758155 = 1137233) B1137233
theorem B1021535 : Blo 235815 1021535 := bstep (se 1 (by rfl) ⟨766151, by rfl⟩ : syracuseStep 1021535 = 1532303) B1532303
theorem B235839 : Blo 235815 235839 := bstep (se 1 (by rfl) ⟨176879, by rfl⟩ : syracuseStep 235839 = 353759) B353759
theorem B235967 : Blo 235815 235967 := bstep (se 1 (by rfl) ⟨176975, by rfl⟩ : syracuseStep 235967 = 353951) B353951
theorem B10230239 : Blo 235815 10230239 := bstep (se 1 (by rfl) ⟨7672679, by rfl⟩ : syracuseStep 10230239 = 15345359) B15345359
theorem B236571 : Blo 235815 236571 := bstep (se 1 (by rfl) ⟨177428, by rfl⟩ : syracuseStep 236571 = 354857) B354857
theorem B269671 : Blo 235815 269671 := bstep (se 1 (by rfl) ⟨202253, by rfl⟩ : syracuseStep 269671 = 404507) B404507
theorem B237311 : Blo 235815 237311 := bstep (se 1 (by rfl) ⟨177983, by rfl⟩ : syracuseStep 237311 = 355967) B355967
theorem B237403 : Blo 235815 237403 := bstep (se 1 (by rfl) ⟨178052, by rfl⟩ : syracuseStep 237403 = 356105) B356105
theorem B237567 : Blo 235815 237567 := bstep (se 1 (by rfl) ⟨178175, by rfl⟩ : syracuseStep 237567 = 356351) B356351
theorem B238439 : Blo 235815 238439 := bstep (se 1 (by rfl) ⟨178829, by rfl⟩ : syracuseStep 238439 = 357659) B357659
theorem B796607 : Blo 235815 796607 := bstep (se 1 (by rfl) ⟨597455, by rfl⟩ : syracuseStep 796607 = 1194911) B1194911
theorem B6466391 : Blo 235815 6466391 := bstep (se 1 (by rfl) ⟨4849793, by rfl⟩ : syracuseStep 6466391 = 9699587) B9699587
theorem B5975021 : Blo 235815 5975021 := bstep (se 3 (by rfl) ⟨1120316, by rfl⟩ : syracuseStep 5975021 = 2240633) B2240633
theorem B797903 : Blo 235815 797903 := bstep (se 1 (by rfl) ⟨598427, by rfl⟩ : syracuseStep 797903 = 1196855) B1196855
theorem B1355575 : Blo 235815 1355575 := bstep (se 1 (by rfl) ⟨1016681, by rfl⟩ : syracuseStep 1355575 = 2033363) B2033363
theorem B3748679 : Blo 235815 3748679 := bstep (se 1 (by rfl) ⟨2811509, by rfl⟩ : syracuseStep 3748679 = 5623019) B5623019
theorem B3880457 : Blo 235815 3880457 := bstep (se 2 (by rfl) ⟨1455171, by rfl⟩ : syracuseStep 3880457 = 2910343) B2910343
theorem B2570363 : Blo 235815 2570363 := bstep (se 1 (by rfl) ⟨1927772, by rfl⟩ : syracuseStep 2570363 = 3855545) B3855545
theorem B539495 : Blo 235815 539495 := bstep (se 1 (by rfl) ⟨404621, by rfl⟩ : syracuseStep 539495 = 809243) B809243
theorem B605495 : Blo 235815 605495 := bstep (se 1 (by rfl) ⟨454121, by rfl⟩ : syracuseStep 605495 = 908243) B908243
theorem B13811471 : Blo 235815 13811471 := bstep (se 1 (by rfl) ⟨10358603, by rfl⟩ : syracuseStep 13811471 = 20717207) B20717207
theorem B11781085 : Blo 235815 11781085 := bstep (se 3 (by rfl) ⟨2208953, by rfl⟩ : syracuseStep 11781085 = 4417907) B4417907
theorem B2442469 : Blo 235815 2442469 := bstep (se 4 (by rfl) ⟨228981, by rfl⟩ : syracuseStep 2442469 = 457963) B457963
theorem B1230473 : Blo 235815 1230473 := bstep (se 2 (by rfl) ⟨461427, by rfl⟩ : syracuseStep 1230473 = 922855) B922855
theorem B1198151 : Blo 235815 1198151 := bstep (se 1 (by rfl) ⟨898613, by rfl⟩ : syracuseStep 1198151 = 1797227) B1797227
theorem B1526921 : Blo 235815 1526921 := bstep (se 2 (by rfl) ⟨572595, by rfl⟩ : syracuseStep 1526921 = 1145191) B1145191
theorem B1135043 : Blo 235815 1135043 := bstep (se 1 (by rfl) ⟨851282, by rfl⟩ : syracuseStep 1135043 = 1702565) B1702565
theorem B677423 : Blo 235815 677423 := bstep (se 1 (by rfl) ⟨508067, by rfl⟩ : syracuseStep 677423 = 1016135) B1016135
theorem B82860509 : Blo 235815 82860509 := bstep (se 3 (by rfl) ⟨15536345, by rfl⟩ : syracuseStep 82860509 = 31072691) B31072691
theorem B26206685 : Blo 235815 26206685 := bstep (se 3 (by rfl) ⟨4913753, by rfl⟩ : syracuseStep 26206685 = 9827507) B9827507
theorem B354473 : Blo 235815 354473 := bstep (se 2 (by rfl) ⟨132927, by rfl⟩ : syracuseStep 354473 = 265855) B265855
theorem B2287997 : Blo 235815 2287997 := bstep (se 3 (by rfl) ⟨428999, by rfl⟩ : syracuseStep 2287997 = 857999) B857999
theorem B9792191 : Blo 235815 9792191 := bstep (se 1 (by rfl) ⟨7344143, by rfl⟩ : syracuseStep 9792191 = 14688287) B14688287
theorem B355067 : Blo 235815 355067 := bstep (se 1 (by rfl) ⟨266300, by rfl⟩ : syracuseStep 355067 = 532601) B532601
theorem B335604991 : Blo 235815 335604991 := bstep (se 1 (by rfl) ⟨251703743, by rfl⟩ : syracuseStep 335604991 = 503407487) B503407487
theorem B355625 : Blo 235815 355625 := bstep (se 2 (by rfl) ⟨133359, by rfl⟩ : syracuseStep 355625 = 266719) B266719
theorem B356009 : Blo 235815 356009 := bstep (se 2 (by rfl) ⟨133503, by rfl⟩ : syracuseStep 356009 = 267007) B267007
theorem B357611 : Blo 235815 357611 := bstep (se 1 (by rfl) ⟨268208, by rfl⟩ : syracuseStep 357611 = 536417) B536417
theorem B12352115 : Blo 235815 12352115 := bstep (se 1 (by rfl) ⟨9264086, by rfl⟩ : syracuseStep 12352115 = 18528173) B18528173
theorem B359531 : Blo 235815 359531 := bstep (se 1 (by rfl) ⟨269648, by rfl⟩ : syracuseStep 359531 = 539297) B539297
theorem B820315 : Blo 235815 820315 := bstep (se 1 (by rfl) ⟨615236, by rfl⟩ : syracuseStep 820315 = 1230473) B1230473
theorem B1017947 : Blo 235815 1017947 := bstep (se 1 (by rfl) ⟨763460, by rfl⟩ : syracuseStep 1017947 = 1526921) B1526921
theorem B756695 : Blo 235815 756695 := bstep (se 1 (by rfl) ⟨567521, by rfl⟩ : syracuseStep 756695 = 1135043) B1135043
theorem B1806461 : Blo 235815 1806461 := bstep (se 3 (by rfl) ⟨338711, by rfl⟩ : syracuseStep 1806461 = 677423) B677423
theorem B6820159 : Blo 235815 6820159 := bstep (se 1 (by rfl) ⟨5115119, by rfl⟩ : syracuseStep 6820159 = 10230239) B10230239
theorem B1807433 : Blo 235815 1807433 := bstep (se 2 (by rfl) ⟨677787, by rfl⟩ : syracuseStep 1807433 = 1355575) B1355575
theorem B17471123 : Blo 235815 17471123 := bstep (se 1 (by rfl) ⟨13103342, by rfl⟩ : syracuseStep 17471123 = 26206685) B26206685
theorem B531071 : Blo 235815 531071 := bstep (se 1 (by rfl) ⟨398303, by rfl⟩ : syracuseStep 531071 = 796607) B796607
theorem B236315 : Blo 235815 236315 := bstep (se 1 (by rfl) ⟨177236, by rfl⟩ : syracuseStep 236315 = 354473) B354473
theorem B6528127 : Blo 235815 6528127 := bstep (se 1 (by rfl) ⟨4896095, by rfl⟩ : syracuseStep 6528127 = 9792191) B9792191
theorem B236711 : Blo 235815 236711 := bstep (se 1 (by rfl) ⟨177533, by rfl⟩ : syracuseStep 236711 = 355067) B355067
theorem B531935 : Blo 235815 531935 := bstep (se 1 (by rfl) ⟨398951, by rfl⟩ : syracuseStep 531935 = 797903) B797903
theorem B237083 : Blo 235815 237083 := bstep (se 1 (by rfl) ⟨177812, by rfl⟩ : syracuseStep 237083 = 355625) B355625
theorem B237339 : Blo 235815 237339 := bstep (se 1 (by rfl) ⟨178004, by rfl⟩ : syracuseStep 237339 = 356009) B356009
theorem B2499119 : Blo 235815 2499119 := bstep (se 1 (by rfl) ⟨1874339, by rfl⟩ : syracuseStep 2499119 = 3748679) B3748679
theorem B238407 : Blo 235815 238407 := bstep (se 1 (by rfl) ⟨178805, by rfl⟩ : syracuseStep 238407 = 357611) B357611
theorem B1713575 : Blo 235815 1713575 := bstep (se 1 (by rfl) ⟨1285181, by rfl⟩ : syracuseStep 1713575 = 2570363) B2570363
theorem B8234743 : Blo 235815 8234743 := bstep (se 1 (by rfl) ⟨6176057, by rfl⟩ : syracuseStep 8234743 = 12352115) B12352115
theorem B239687 : Blo 235815 239687 := bstep (se 1 (by rfl) ⟨179765, by rfl⟩ : syracuseStep 239687 = 359531) B359531
theorem B403663 : Blo 235815 403663 := bstep (se 1 (by rfl) ⟨302747, by rfl⟩ : syracuseStep 403663 = 605495) B605495
theorem B15708113 : Blo 235815 15708113 := bstep (se 2 (by rfl) ⟨5890542, by rfl⟩ : syracuseStep 15708113 = 11781085) B11781085
theorem B798767 : Blo 235815 798767 := bstep (se 1 (by rfl) ⟨599075, by rfl⟩ : syracuseStep 798767 = 1198151) B1198151
theorem B3256625 : Blo 235815 3256625 := bstep (se 2 (by rfl) ⟨1221234, by rfl⟩ : syracuseStep 3256625 = 2442469) B2442469
theorem B6141095 : Blo 235815 6141095 := bstep (se 1 (by rfl) ⟨4605821, by rfl⟩ : syracuseStep 6141095 = 9211643) B9211643
theorem B1525331 : Blo 235815 1525331 := bstep (se 1 (by rfl) ⟨1143998, by rfl⟩ : syracuseStep 1525331 = 2287997) B2287997
theorem B4310927 : Blo 235815 4310927 := bstep (se 1 (by rfl) ⟨3233195, by rfl⟩ : syracuseStep 4310927 = 6466391) B6466391
theorem B3983347 : Blo 235815 3983347 := bstep (se 1 (by rfl) ⟨2987510, by rfl⟩ : syracuseStep 3983347 = 5975021) B5975021
theorem B681023 : Blo 235815 681023 := bstep (se 1 (by rfl) ⟨510767, by rfl⟩ : syracuseStep 681023 = 1021535) B1021535
theorem B55240339 : Blo 235815 55240339 := bstep (se 1 (by rfl) ⟨41430254, by rfl⟩ : syracuseStep 55240339 = 82860509) B82860509
theorem B447473321 : Blo 235815 447473321 := bstep (se 2 (by rfl) ⟨167802495, by rfl⟩ : syracuseStep 447473321 = 335604991) B335604991
theorem B1010873 : Blo 235815 1010873 := bstep (se 2 (by rfl) ⟨379077, by rfl⟩ : syracuseStep 1010873 = 758155) B758155
theorem B2586971 : Blo 235815 2586971 := bstep (se 1 (by rfl) ⟨1940228, by rfl⟩ : syracuseStep 2586971 = 3880457) B3880457
theorem B359561 : Blo 235815 359561 := bstep (se 2 (by rfl) ⟨134835, by rfl⟩ : syracuseStep 359561 = 269671) B269671
theorem B359663 : Blo 235815 359663 := bstep (se 1 (by rfl) ⟨269747, by rfl⟩ : syracuseStep 359663 = 539495) B539495
theorem B9207647 : Blo 235815 9207647 := bstep (se 1 (by rfl) ⟨6905735, by rfl⟩ : syracuseStep 9207647 = 13811471) B13811471
theorem B1016887 : Blo 235815 1016887 := bstep (se 1 (by rfl) ⟨762665, by rfl⟩ : syracuseStep 1016887 = 1525331) B1525331
theorem B10979657 : Blo 235815 10979657 := bstep (se 2 (by rfl) ⟨4117371, by rfl⟩ : syracuseStep 10979657 = 8234743) B8234743
theorem B5311129 : Blo 235815 5311129 := bstep (se 2 (by rfl) ⟨1991673, by rfl⟩ : syracuseStep 5311129 = 3983347) B3983347
theorem B532511 : Blo 235815 532511 := bstep (se 1 (by rfl) ⟨399383, by rfl⟩ : syracuseStep 532511 = 798767) B798767
theorem B2171083 : Blo 235815 2171083 := bstep (se 1 (by rfl) ⟨1628312, by rfl⟩ : syracuseStep 2171083 = 3256625) B3256625
theorem B239707 : Blo 235815 239707 := bstep (se 1 (by rfl) ⟨179780, by rfl⟩ : syracuseStep 239707 = 359561) B359561
theorem B239775 : Blo 235815 239775 := bstep (se 1 (by rfl) ⟨179831, by rfl⟩ : syracuseStep 239775 = 359663) B359663
theorem B6138431 : Blo 235815 6138431 := bstep (se 1 (by rfl) ⟨4603823, by rfl⟩ : syracuseStep 6138431 = 9207647) B9207647
theorem B1093753 : Blo 235815 1093753 := bstep (se 2 (by rfl) ⟨410157, by rfl⟩ : syracuseStep 1093753 = 820315) B820315
theorem B504463 : Blo 235815 504463 := bstep (se 1 (by rfl) ⟨378347, by rfl⟩ : syracuseStep 504463 = 756695) B756695
theorem B538217 : Blo 235815 538217 := bstep (se 2 (by rfl) ⟨201831, by rfl⟩ : syracuseStep 538217 = 403663) B403663
theorem B11647415 : Blo 235815 11647415 := bstep (se 1 (by rfl) ⟨8735561, by rfl⟩ : syracuseStep 11647415 = 17471123) B17471123
theorem B4569533 : Blo 235815 4569533 := bstep (se 3 (by rfl) ⟨856787, by rfl⟩ : syracuseStep 4569533 = 1713575) B1713575
theorem B9093545 : Blo 235815 9093545 := bstep (se 2 (by rfl) ⟨3410079, by rfl⟩ : syracuseStep 9093545 = 6820159) B6820159
theorem B673915 : Blo 235815 673915 := bstep (se 1 (by rfl) ⟨505436, by rfl⟩ : syracuseStep 673915 = 1010873) B1010873
theorem B10472075 : Blo 235815 10472075 := bstep (se 1 (by rfl) ⟨7854056, by rfl⟩ : syracuseStep 10472075 = 15708113) B15708113
theorem B8704169 : Blo 235815 8704169 := bstep (se 2 (by rfl) ⟨3264063, by rfl⟩ : syracuseStep 8704169 = 6528127) B6528127
theorem B1724647 : Blo 235815 1724647 := bstep (se 1 (by rfl) ⟨1293485, by rfl⟩ : syracuseStep 1724647 = 2586971) B2586971
theorem B2873951 : Blo 235815 2873951 := bstep (se 1 (by rfl) ⟨2155463, by rfl⟩ : syracuseStep 2873951 = 4310927) B4310927
theorem B678631 : Blo 235815 678631 := bstep (se 1 (by rfl) ⟨508973, by rfl⟩ : syracuseStep 678631 = 1017947) B1017947
theorem B73653785 : Blo 235815 73653785 := bstep (se 2 (by rfl) ⟨27620169, by rfl⟩ : syracuseStep 73653785 = 55240339) B55240339
theorem B1204307 : Blo 235815 1204307 := bstep (se 1 (by rfl) ⟨903230, by rfl⟩ : syracuseStep 1204307 = 1806461) B1806461
theorem B1204955 : Blo 235815 1204955 := bstep (se 1 (by rfl) ⟨903716, by rfl⟩ : syracuseStep 1204955 = 1807433) B1807433
theorem B354047 : Blo 235815 354047 := bstep (se 1 (by rfl) ⟨265535, by rfl⟩ : syracuseStep 354047 = 531071) B531071
theorem B354623 : Blo 235815 354623 := bstep (se 1 (by rfl) ⟨265967, by rfl⟩ : syracuseStep 354623 = 531935) B531935
theorem B1666079 : Blo 235815 1666079 := bstep (se 1 (by rfl) ⟨1249559, by rfl⟩ : syracuseStep 1666079 = 2499119) B2499119
theorem B454015 : Blo 235815 454015 := bstep (se 1 (by rfl) ⟨340511, by rfl⟩ : syracuseStep 454015 = 681023) B681023
theorem B298315547 : Blo 235815 298315547 := bstep (se 1 (by rfl) ⟨223736660, by rfl⟩ : syracuseStep 298315547 = 447473321) B447473321
theorem B4094063 : Blo 235815 4094063 := bstep (se 1 (by rfl) ⟨3070547, by rfl⟩ : syracuseStep 4094063 = 6141095) B6141095
theorem B6062363 : Blo 235815 6062363 := bstep (se 1 (by rfl) ⟨4546772, by rfl⟩ : syracuseStep 6062363 = 9093545) B9093545
theorem B6981383 : Blo 235815 6981383 := bstep (se 1 (by rfl) ⟨5236037, by rfl⟩ : syracuseStep 6981383 = 10472075) B10472075
theorem B5802779 : Blo 235815 5802779 := bstep (se 1 (by rfl) ⟨4352084, by rfl⟩ : syracuseStep 5802779 = 8704169) B8704169
theorem B7081505 : Blo 235815 7081505 := bstep (se 2 (by rfl) ⟨2655564, by rfl⟩ : syracuseStep 7081505 = 5311129) B5311129
theorem B2299529 : Blo 235815 2299529 := bstep (se 2 (by rfl) ⟨862323, by rfl⟩ : syracuseStep 2299529 = 1724647) B1724647
theorem B236031 : Blo 235815 236031 := bstep (se 1 (by rfl) ⟨177023, by rfl⟩ : syracuseStep 236031 = 354047) B354047
theorem B236415 : Blo 235815 236415 := bstep (se 1 (by rfl) ⟨177311, by rfl⟩ : syracuseStep 236415 = 354623) B354623
theorem B198877031 : Blo 235815 198877031 := bstep (se 1 (by rfl) ⟨149157773, by rfl⟩ : syracuseStep 198877031 = 298315547) B298315547
theorem B2729375 : Blo 235815 2729375 := bstep (se 1 (by rfl) ⟨2047031, by rfl⟩ : syracuseStep 2729375 = 4094063) B4094063
theorem B2894777 : Blo 235815 2894777 := bstep (se 2 (by rfl) ⟨1085541, by rfl⟩ : syracuseStep 2894777 = 2171083) B2171083
theorem B1355849 : Blo 235815 1355849 := bstep (se 2 (by rfl) ⟨508443, by rfl⟩ : syracuseStep 1355849 = 1016887) B1016887
theorem B7319771 : Blo 235815 7319771 := bstep (se 1 (by rfl) ⟨5489828, by rfl⟩ : syracuseStep 7319771 = 10979657) B10979657
theorem B898553 : Blo 235815 898553 := bstep (se 2 (by rfl) ⟨336957, by rfl⟩ : syracuseStep 898553 = 673915) B673915
theorem B1915967 : Blo 235815 1915967 := bstep (se 1 (by rfl) ⟨1436975, by rfl⟩ : syracuseStep 1915967 = 2873951) B2873951
theorem B605353 : Blo 235815 605353 := bstep (se 2 (by rfl) ⟨227007, by rfl⟩ : syracuseStep 605353 = 454015) B454015
theorem B49102523 : Blo 235815 49102523 := bstep (se 1 (by rfl) ⟨36826892, by rfl⟩ : syracuseStep 49102523 = 73653785) B73653785
theorem B802871 : Blo 235815 802871 := bstep (se 1 (by rfl) ⟨602153, by rfl⟩ : syracuseStep 802871 = 1204307) B1204307
theorem B1458337 : Blo 235815 1458337 := bstep (se 2 (by rfl) ⟨546876, by rfl⟩ : syracuseStep 1458337 = 1093753) B1093753
theorem B803303 : Blo 235815 803303 := bstep (se 1 (by rfl) ⟨602477, by rfl⟩ : syracuseStep 803303 = 1204955) B1204955
theorem B672617 : Blo 235815 672617 := bstep (se 2 (by rfl) ⟨252231, by rfl⟩ : syracuseStep 672617 = 504463) B504463
theorem B904841 : Blo 235815 904841 := bstep (se 2 (by rfl) ⟨339315, by rfl⟩ : syracuseStep 904841 = 678631) B678631
theorem B319609 : Blo 235815 319609 := bstep (se 2 (by rfl) ⟨119853, by rfl⟩ : syracuseStep 319609 = 239707) B239707
theorem B355007 : Blo 235815 355007 := bstep (se 1 (by rfl) ⟨266255, by rfl⟩ : syracuseStep 355007 = 532511) B532511
theorem B4092287 : Blo 235815 4092287 := bstep (se 1 (by rfl) ⟨3069215, by rfl⟩ : syracuseStep 4092287 = 6138431) B6138431
theorem B1110719 : Blo 235815 1110719 := bstep (se 1 (by rfl) ⟨833039, by rfl⟩ : syracuseStep 1110719 = 1666079) B1666079
theorem B358811 : Blo 235815 358811 := bstep (se 1 (by rfl) ⟨269108, by rfl⟩ : syracuseStep 358811 = 538217) B538217
theorem B7764943 : Blo 235815 7764943 := bstep (se 1 (by rfl) ⟨5823707, by rfl⟩ : syracuseStep 7764943 = 11647415) B11647415
theorem B3046355 : Blo 235815 3046355 := bstep (se 1 (by rfl) ⟨2284766, by rfl⟩ : syracuseStep 3046355 = 4569533) B4569533
theorem B426145 : Blo 235815 426145 := bstep (se 2 (by rfl) ⟨159804, by rfl⟩ : syracuseStep 426145 = 319609) B319609
theorem B10912765 : Blo 235815 10912765 := bstep (se 3 (by rfl) ⟨2046143, by rfl⟩ : syracuseStep 10912765 = 4092287) B4092287
theorem B4654255 : Blo 235815 4654255 := bstep (se 1 (by rfl) ⟨3490691, by rfl⟩ : syracuseStep 4654255 = 6981383) B6981383
theorem B3868519 : Blo 235815 3868519 := bstep (se 1 (by rfl) ⟨2901389, by rfl⟩ : syracuseStep 3868519 = 5802779) B5802779
theorem B4721003 : Blo 235815 4721003 := bstep (se 1 (by rfl) ⟨3540752, by rfl⟩ : syracuseStep 4721003 = 7081505) B7081505
theorem B132584687 : Blo 235815 132584687 := bstep (se 1 (by rfl) ⟨99438515, by rfl⟩ : syracuseStep 132584687 = 198877031) B198877031
theorem B236671 : Blo 235815 236671 := bstep (se 1 (by rfl) ⟨177503, by rfl⟩ : syracuseStep 236671 = 355007) B355007
theorem B599035 : Blo 235815 599035 := bstep (se 1 (by rfl) ⟨449276, by rfl⟩ : syracuseStep 599035 = 898553) B898553
theorem B239207 : Blo 235815 239207 := bstep (se 1 (by rfl) ⟨179405, by rfl⟩ : syracuseStep 239207 = 358811) B358811
theorem B535247 : Blo 235815 535247 := bstep (se 1 (by rfl) ⟨401435, by rfl⟩ : syracuseStep 535247 = 802871) B802871
theorem B4041575 : Blo 235815 4041575 := bstep (se 1 (by rfl) ⟨3031181, by rfl⟩ : syracuseStep 4041575 = 6062363) B6062363
theorem B1944449 : Blo 235815 1944449 := bstep (se 2 (by rfl) ⟨729168, by rfl⟩ : syracuseStep 1944449 = 1458337) B1458337
theorem B535535 : Blo 235815 535535 := bstep (se 1 (by rfl) ⟨401651, by rfl⟩ : syracuseStep 535535 = 803303) B803303
theorem B2961917 : Blo 235815 2961917 := bstep (se 3 (by rfl) ⟨555359, by rfl⟩ : syracuseStep 2961917 = 1110719) B1110719
theorem B603227 : Blo 235815 603227 := bstep (se 1 (by rfl) ⟨452420, by rfl⟩ : syracuseStep 603227 = 904841) B904841
theorem B1819583 : Blo 235815 1819583 := bstep (se 1 (by rfl) ⟨1364687, by rfl⟩ : syracuseStep 1819583 = 2729375) B2729375
theorem B903899 : Blo 235815 903899 := bstep (se 1 (by rfl) ⟨677924, by rfl⟩ : syracuseStep 903899 = 1355849) B1355849
theorem B807137 : Blo 235815 807137 := bstep (se 2 (by rfl) ⟨302676, by rfl⟩ : syracuseStep 807137 = 605353) B605353
theorem B448411 : Blo 235815 448411 := bstep (se 1 (by rfl) ⟨336308, by rfl⟩ : syracuseStep 448411 = 672617) B672617
theorem B1533019 : Blo 235815 1533019 := bstep (se 1 (by rfl) ⟨1149764, by rfl⟩ : syracuseStep 1533019 = 2299529) B2299529
theorem B1929851 : Blo 235815 1929851 := bstep (se 1 (by rfl) ⟨1447388, by rfl⟩ : syracuseStep 1929851 = 2894777) B2894777
theorem B4879847 : Blo 235815 4879847 := bstep (se 1 (by rfl) ⟨3659885, by rfl⟩ : syracuseStep 4879847 = 7319771) B7319771
theorem B10353257 : Blo 235815 10353257 := bstep (se 2 (by rfl) ⟨3882471, by rfl⟩ : syracuseStep 10353257 = 7764943) B7764943
theorem B2030903 : Blo 235815 2030903 := bstep (se 1 (by rfl) ⟨1523177, by rfl⟩ : syracuseStep 2030903 = 3046355) B3046355
theorem B1277311 : Blo 235815 1277311 := bstep (se 1 (by rfl) ⟨957983, by rfl⟩ : syracuseStep 1277311 = 1915967) B1915967
theorem B32735015 : Blo 235815 32735015 := bstep (se 1 (by rfl) ⟨24551261, by rfl⟩ : syracuseStep 32735015 = 49102523) B49102523
theorem B1213055 : Blo 235815 1213055 := bstep (se 1 (by rfl) ⟨909791, by rfl⟩ : syracuseStep 1213055 = 1819583) B1819583
theorem B14550353 : Blo 235815 14550353 := bstep (se 2 (by rfl) ⟨5456382, by rfl⟩ : syracuseStep 14550353 = 10912765) B10912765
theorem B3147335 : Blo 235815 3147335 := bstep (se 1 (by rfl) ⟨2360501, by rfl⟩ : syracuseStep 3147335 = 4721003) B4721003
theorem B2694383 : Blo 235815 2694383 := bstep (se 1 (by rfl) ⟨2020787, by rfl⟩ : syracuseStep 2694383 = 4041575) B4041575
theorem B597881 : Blo 235815 597881 := bstep (se 2 (by rfl) ⟨224205, by rfl⟩ : syracuseStep 597881 = 448411) B448411
theorem B1974611 : Blo 235815 1974611 := bstep (se 1 (by rfl) ⟨1480958, by rfl⟩ : syracuseStep 1974611 = 2961917) B2961917
theorem B1286567 : Blo 235815 1286567 := bstep (se 1 (by rfl) ⟨964925, by rfl⟩ : syracuseStep 1286567 = 1929851) B1929851
theorem B402151 : Blo 235815 402151 := bstep (se 1 (by rfl) ⟨301613, by rfl⟩ : syracuseStep 402151 = 603227) B603227
theorem B3253231 : Blo 235815 3253231 := bstep (se 1 (by rfl) ⟨2439923, by rfl⟩ : syracuseStep 3253231 = 4879847) B4879847
theorem B1353935 : Blo 235815 1353935 := bstep (se 1 (by rfl) ⟨1015451, by rfl⟩ : syracuseStep 1353935 = 2030903) B2030903
theorem B568193 : Blo 235815 568193 := bstep (se 2 (by rfl) ⟨213072, by rfl⟩ : syracuseStep 568193 = 426145) B426145
theorem B798713 : Blo 235815 798713 := bstep (se 2 (by rfl) ⟨299517, by rfl⟩ : syracuseStep 798713 = 599035) B599035
theorem B2044025 : Blo 235815 2044025 := bstep (se 2 (by rfl) ⟨766509, by rfl⟩ : syracuseStep 2044025 = 1533019) B1533019
theorem B6205673 : Blo 235815 6205673 := bstep (se 2 (by rfl) ⟨2327127, by rfl⟩ : syracuseStep 6205673 = 4654255) B4654255
theorem B602599 : Blo 235815 602599 := bstep (se 1 (by rfl) ⟨451949, by rfl⟩ : syracuseStep 602599 = 903899) B903899
theorem B5158025 : Blo 235815 5158025 := bstep (se 2 (by rfl) ⟨1934259, by rfl⟩ : syracuseStep 5158025 = 3868519) B3868519
theorem B538091 : Blo 235815 538091 := bstep (se 1 (by rfl) ⟨403568, by rfl⟩ : syracuseStep 538091 = 807137) B807137
theorem B88389791 : Blo 235815 88389791 := bstep (se 1 (by rfl) ⟨66292343, by rfl⟩ : syracuseStep 88389791 = 132584687) B132584687
theorem B1296299 : Blo 235815 1296299 := bstep (se 1 (by rfl) ⟨972224, by rfl⟩ : syracuseStep 1296299 = 1944449) B1944449
theorem B6902171 : Blo 235815 6902171 := bstep (se 1 (by rfl) ⟨5176628, by rfl⟩ : syracuseStep 6902171 = 10353257) B10353257
theorem B356831 : Blo 235815 356831 := bstep (se 1 (by rfl) ⟨267623, by rfl⟩ : syracuseStep 356831 = 535247) B535247
theorem B357023 : Blo 235815 357023 := bstep (se 1 (by rfl) ⟨267767, by rfl⟩ : syracuseStep 357023 = 535535) B535535
theorem B1703081 : Blo 235815 1703081 := bstep (se 2 (by rfl) ⟨638655, by rfl⟩ : syracuseStep 1703081 = 1277311) B1277311
theorem B21823343 : Blo 235815 21823343 := bstep (se 1 (by rfl) ⟨16367507, by rfl⟩ : syracuseStep 21823343 = 32735015) B32735015
theorem B16548461 : Blo 235815 16548461 := bstep (se 3 (by rfl) ⟨3102836, by rfl⟩ : syracuseStep 16548461 = 6205673) B6205673
theorem B9700235 : Blo 235815 9700235 := bstep (se 1 (by rfl) ⟨7275176, by rfl⟩ : syracuseStep 9700235 = 14550353) B14550353
theorem B2098223 : Blo 235815 2098223 := bstep (se 1 (by rfl) ⟨1573667, by rfl⟩ : syracuseStep 2098223 = 3147335) B3147335
theorem B398587 : Blo 235815 398587 := bstep (se 1 (by rfl) ⟨298940, by rfl⟩ : syracuseStep 398587 = 597881) B597881
theorem B1316407 : Blo 235815 1316407 := bstep (se 1 (by rfl) ⟨987305, by rfl⟩ : syracuseStep 1316407 = 1974611) B1974611
theorem B857711 : Blo 235815 857711 := bstep (se 1 (by rfl) ⟨643283, by rfl⟩ : syracuseStep 857711 = 1286567) B1286567
theorem B1515181 : Blo 235815 1515181 := bstep (se 3 (by rfl) ⟨284096, by rfl⟩ : syracuseStep 1515181 = 568193) B568193
theorem B532475 : Blo 235815 532475 := bstep (se 1 (by rfl) ⟨399356, by rfl⟩ : syracuseStep 532475 = 798713) B798713
theorem B237887 : Blo 235815 237887 := bstep (se 1 (by rfl) ⟨178415, by rfl⟩ : syracuseStep 237887 = 356831) B356831
theorem B238015 : Blo 235815 238015 := bstep (se 1 (by rfl) ⟨178511, by rfl⟩ : syracuseStep 238015 = 357023) B357023
theorem B58926527 : Blo 235815 58926527 := bstep (se 1 (by rfl) ⟨44194895, by rfl⟩ : syracuseStep 58926527 = 88389791) B88389791
theorem B536201 : Blo 235815 536201 := bstep (se 2 (by rfl) ⟨201075, by rfl⟩ : syracuseStep 536201 = 402151) B402151
theorem B864199 : Blo 235815 864199 := bstep (se 1 (by rfl) ⟨648149, by rfl⟩ : syracuseStep 864199 = 1296299) B1296299
theorem B4337641 : Blo 235815 4337641 := bstep (se 2 (by rfl) ⟨1626615, by rfl⟩ : syracuseStep 4337641 = 3253231) B3253231
theorem B4601447 : Blo 235815 4601447 := bstep (se 1 (by rfl) ⟨3451085, by rfl⟩ : syracuseStep 4601447 = 6902171) B6902171
theorem B803465 : Blo 235815 803465 := bstep (se 2 (by rfl) ⟨301299, by rfl⟩ : syracuseStep 803465 = 602599) B602599
theorem B902623 : Blo 235815 902623 := bstep (se 1 (by rfl) ⟨676967, by rfl⟩ : syracuseStep 902623 = 1353935) B1353935
theorem B1362683 : Blo 235815 1362683 := bstep (se 1 (by rfl) ⟨1022012, by rfl⟩ : syracuseStep 1362683 = 2044025) B2044025
theorem B1135387 : Blo 235815 1135387 := bstep (se 1 (by rfl) ⟨851540, by rfl⟩ : syracuseStep 1135387 = 1703081) B1703081
theorem B808703 : Blo 235815 808703 := bstep (se 1 (by rfl) ⟨606527, by rfl⟩ : syracuseStep 808703 = 1213055) B1213055
theorem B1796255 : Blo 235815 1796255 := bstep (se 1 (by rfl) ⟨1347191, by rfl⟩ : syracuseStep 1796255 = 2694383) B2694383
theorem B3438683 : Blo 235815 3438683 := bstep (se 1 (by rfl) ⟨2579012, by rfl⟩ : syracuseStep 3438683 = 5158025) B5158025
theorem B358727 : Blo 235815 358727 := bstep (se 1 (by rfl) ⟨269045, by rfl⟩ : syracuseStep 358727 = 538091) B538091
theorem B14548895 : Blo 235815 14548895 := bstep (se 1 (by rfl) ⟨10911671, by rfl⟩ : syracuseStep 14548895 = 21823343) B21823343
theorem B1152265 : Blo 235815 1152265 := bstep (se 2 (by rfl) ⟨432099, by rfl⟩ : syracuseStep 1152265 = 864199) B864199
theorem B1513849 : Blo 235815 1513849 := bstep (se 2 (by rfl) ⟨567693, by rfl⟩ : syracuseStep 1513849 = 1135387) B1135387
theorem B531449 : Blo 235815 531449 := bstep (se 2 (by rfl) ⟨199293, by rfl⟩ : syracuseStep 531449 = 398587) B398587
theorem B239151 : Blo 235815 239151 := bstep (se 1 (by rfl) ⟨179363, by rfl⟩ : syracuseStep 239151 = 358727) B358727
theorem B535643 : Blo 235815 535643 := bstep (se 1 (by rfl) ⟨401732, by rfl⟩ : syracuseStep 535643 = 803465) B803465
theorem B6466823 : Blo 235815 6466823 := bstep (se 1 (by rfl) ⟨4850117, by rfl⟩ : syracuseStep 6466823 = 9700235) B9700235
theorem B571807 : Blo 235815 571807 := bstep (se 1 (by rfl) ⟨428855, by rfl⟩ : syracuseStep 571807 = 857711) B857711
theorem B539135 : Blo 235815 539135 := bstep (se 1 (by rfl) ⟨404351, by rfl⟩ : syracuseStep 539135 = 808703) B808703
theorem B5783521 : Blo 235815 5783521 := bstep (se 2 (by rfl) ⟨2168820, by rfl⟩ : syracuseStep 5783521 = 4337641) B4337641
theorem B1197503 : Blo 235815 1197503 := bstep (se 1 (by rfl) ⟨898127, by rfl⟩ : syracuseStep 1197503 = 1796255) B1796255
theorem B1755209 : Blo 235815 1755209 := bstep (se 2 (by rfl) ⟨658203, by rfl⟩ : syracuseStep 1755209 = 1316407) B1316407
theorem B3067631 : Blo 235815 3067631 := bstep (se 1 (by rfl) ⟨2300723, by rfl⟩ : syracuseStep 3067631 = 4601447) B4601447
theorem B2020241 : Blo 235815 2020241 := bstep (se 2 (by rfl) ⟨757590, by rfl⟩ : syracuseStep 2020241 = 1515181) B1515181
theorem B11032307 : Blo 235815 11032307 := bstep (se 1 (by rfl) ⟨8274230, by rfl⟩ : syracuseStep 11032307 = 16548461) B16548461
theorem B1398815 : Blo 235815 1398815 := bstep (se 1 (by rfl) ⟨1049111, by rfl⟩ : syracuseStep 1398815 = 2098223) B2098223
theorem B908455 : Blo 235815 908455 := bstep (se 1 (by rfl) ⟨681341, by rfl⟩ : syracuseStep 908455 = 1362683) B1362683
theorem B1203497 : Blo 235815 1203497 := bstep (se 2 (by rfl) ⟨451311, by rfl⟩ : syracuseStep 1203497 = 902623) B902623
theorem B354983 : Blo 235815 354983 := bstep (se 1 (by rfl) ⟨266237, by rfl⟩ : syracuseStep 354983 = 532475) B532475
theorem B39284351 : Blo 235815 39284351 := bstep (se 1 (by rfl) ⟨29463263, by rfl⟩ : syracuseStep 39284351 = 58926527) B58926527
theorem B357467 : Blo 235815 357467 := bstep (se 1 (by rfl) ⟨268100, by rfl⟩ : syracuseStep 357467 = 536201) B536201
theorem B2292455 : Blo 235815 2292455 := bstep (se 1 (by rfl) ⟨1719341, by rfl⟩ : syracuseStep 2292455 = 3438683) B3438683
theorem B9699263 : Blo 235815 9699263 := bstep (se 1 (by rfl) ⟨7274447, by rfl⟩ : syracuseStep 9699263 = 14548895) B14548895
theorem B1346827 : Blo 235815 1346827 := bstep (se 1 (by rfl) ⟨1010120, by rfl⟩ : syracuseStep 1346827 = 2020241) B2020241
theorem B236655 : Blo 235815 236655 := bstep (se 1 (by rfl) ⟨177491, by rfl⟩ : syracuseStep 236655 = 354983) B354983
theorem B26189567 : Blo 235815 26189567 := bstep (se 1 (by rfl) ⟨19642175, by rfl⟩ : syracuseStep 26189567 = 39284351) B39284351
theorem B762409 : Blo 235815 762409 := bstep (se 2 (by rfl) ⟨285903, by rfl⟩ : syracuseStep 762409 = 571807) B571807
theorem B238311 : Blo 235815 238311 := bstep (se 1 (by rfl) ⟨178733, by rfl⟩ : syracuseStep 238311 = 357467) B357467
theorem B6466175 : Blo 235815 6466175 := bstep (se 1 (by rfl) ⟨4849631, by rfl⟩ : syracuseStep 6466175 = 9699263) B9699263
theorem B7711361 : Blo 235815 7711361 := bstep (se 2 (by rfl) ⟨2891760, by rfl⟩ : syracuseStep 7711361 = 5783521) B5783521
theorem B798335 : Blo 235815 798335 := bstep (se 1 (by rfl) ⟨598751, by rfl⟩ : syracuseStep 798335 = 1197503) B1197503
theorem B2045087 : Blo 235815 2045087 := bstep (se 1 (by rfl) ⟨1533815, by rfl⟩ : syracuseStep 2045087 = 3067631) B3067631
theorem B7354871 : Blo 235815 7354871 := bstep (se 1 (by rfl) ⟨5516153, by rfl⟩ : syracuseStep 7354871 = 11032307) B11032307
theorem B932543 : Blo 235815 932543 := bstep (se 1 (by rfl) ⟨699407, by rfl⟩ : syracuseStep 932543 = 1398815) B1398815
theorem B802331 : Blo 235815 802331 := bstep (se 1 (by rfl) ⟨601748, by rfl⟩ : syracuseStep 802331 = 1203497) B1203497
theorem B4311215 : Blo 235815 4311215 := bstep (se 1 (by rfl) ⟨3233411, by rfl⟩ : syracuseStep 4311215 = 6466823) B6466823
theorem B2018465 : Blo 235815 2018465 := bstep (se 2 (by rfl) ⟨756924, by rfl⟩ : syracuseStep 2018465 = 1513849) B1513849
theorem B1528303 : Blo 235815 1528303 := bstep (se 1 (by rfl) ⟨1146227, by rfl⟩ : syracuseStep 1528303 = 2292455) B2292455
theorem B354299 : Blo 235815 354299 := bstep (se 1 (by rfl) ⟨265724, by rfl⟩ : syracuseStep 354299 = 531449) B531449
theorem B4680557 : Blo 235815 4680557 := bstep (se 3 (by rfl) ⟨877604, by rfl⟩ : syracuseStep 4680557 = 1755209) B1755209
theorem B1536353 : Blo 235815 1536353 := bstep (se 2 (by rfl) ⟨576132, by rfl⟩ : syracuseStep 1536353 = 1152265) B1152265
theorem B357095 : Blo 235815 357095 := bstep (se 1 (by rfl) ⟨267821, by rfl⟩ : syracuseStep 357095 = 535643) B535643
theorem B1211273 : Blo 235815 1211273 := bstep (se 2 (by rfl) ⟨454227, by rfl⟩ : syracuseStep 1211273 = 908455) B908455
theorem B359423 : Blo 235815 359423 := bstep (se 1 (by rfl) ⟨269567, by rfl⟩ : syracuseStep 359423 = 539135) B539135
theorem B1016545 : Blo 235815 1016545 := bstep (se 2 (by rfl) ⟨381204, by rfl⟩ : syracuseStep 1016545 = 762409) B762409
theorem B1345643 : Blo 235815 1345643 := bstep (se 1 (by rfl) ⟨1009232, by rfl⟩ : syracuseStep 1345643 = 2018465) B2018465
theorem B2037737 : Blo 235815 2037737 := bstep (se 2 (by rfl) ⟨764151, by rfl⟩ : syracuseStep 2037737 = 1528303) B1528303
theorem B236199 : Blo 235815 236199 := bstep (se 1 (by rfl) ⟨177149, by rfl⟩ : syracuseStep 236199 = 354299) B354299
theorem B3120371 : Blo 235815 3120371 := bstep (se 1 (by rfl) ⟨2340278, by rfl⟩ : syracuseStep 3120371 = 4680557) B4680557
theorem B532223 : Blo 235815 532223 := bstep (se 1 (by rfl) ⟨399167, by rfl⟩ : syracuseStep 532223 = 798335) B798335
theorem B1024235 : Blo 235815 1024235 := bstep (se 1 (by rfl) ⟨768176, by rfl⟩ : syracuseStep 1024235 = 1536353) B1536353
theorem B238063 : Blo 235815 238063 := bstep (se 1 (by rfl) ⟨178547, by rfl⟩ : syracuseStep 238063 = 357095) B357095
theorem B239615 : Blo 235815 239615 := bstep (se 1 (by rfl) ⟨179711, by rfl⟩ : syracuseStep 239615 = 359423) B359423
theorem B534887 : Blo 235815 534887 := bstep (se 1 (by rfl) ⟨401165, by rfl⟩ : syracuseStep 534887 = 802331) B802331
theorem B4310783 : Blo 235815 4310783 := bstep (se 1 (by rfl) ⟨3233087, by rfl⟩ : syracuseStep 4310783 = 6466175) B6466175
theorem B1363391 : Blo 235815 1363391 := bstep (se 1 (by rfl) ⟨1022543, by rfl⟩ : syracuseStep 1363391 = 2045087) B2045087
theorem B4903247 : Blo 235815 4903247 := bstep (se 1 (by rfl) ⟨3677435, by rfl⟩ : syracuseStep 4903247 = 7354871) B7354871
theorem B807515 : Blo 235815 807515 := bstep (se 1 (by rfl) ⟨605636, by rfl⟩ : syracuseStep 807515 = 1211273) B1211273
theorem B2874143 : Blo 235815 2874143 := bstep (se 1 (by rfl) ⟨2155607, by rfl⟩ : syracuseStep 2874143 = 4311215) B4311215
theorem B1795769 : Blo 235815 1795769 := bstep (se 2 (by rfl) ⟨673413, by rfl⟩ : syracuseStep 1795769 = 1346827) B1346827
theorem B17459711 : Blo 235815 17459711 := bstep (se 1 (by rfl) ⟨13094783, by rfl⟩ : syracuseStep 17459711 = 26189567) B26189567
theorem B5140907 : Blo 235815 5140907 := bstep (se 1 (by rfl) ⟨3855680, by rfl⟩ : syracuseStep 5140907 = 7711361) B7711361
theorem B621695 : Blo 235815 621695 := bstep (se 1 (by rfl) ⟨466271, by rfl⟩ : syracuseStep 621695 = 932543) B932543
theorem B11639807 : Blo 235815 11639807 := bstep (se 1 (by rfl) ⟨8729855, by rfl⟩ : syracuseStep 11639807 = 17459711) B17459711
theorem B1355393 : Blo 235815 1355393 := bstep (se 2 (by rfl) ⟨508272, by rfl⟩ : syracuseStep 1355393 = 1016545) B1016545
theorem B897095 : Blo 235815 897095 := bstep (se 1 (by rfl) ⟨672821, by rfl⟩ : syracuseStep 897095 = 1345643) B1345643
theorem B538343 : Blo 235815 538343 := bstep (se 1 (by rfl) ⟨403757, by rfl⟩ : syracuseStep 538343 = 807515) B807515
theorem B1358491 : Blo 235815 1358491 := bstep (se 1 (by rfl) ⟨1018868, by rfl⟩ : syracuseStep 1358491 = 2037737) B2037737
theorem B1916095 : Blo 235815 1916095 := bstep (se 1 (by rfl) ⟨1437071, by rfl⟩ : syracuseStep 1916095 = 2874143) B2874143
theorem B2080247 : Blo 235815 2080247 := bstep (se 1 (by rfl) ⟨1560185, by rfl⟩ : syracuseStep 2080247 = 3120371) B3120371
theorem B1197179 : Blo 235815 1197179 := bstep (se 1 (by rfl) ⟨897884, by rfl⟩ : syracuseStep 1197179 = 1795769) B1795769
theorem B3427271 : Blo 235815 3427271 := bstep (se 1 (by rfl) ⟨2570453, by rfl⟩ : syracuseStep 3427271 = 5140907) B5140907
theorem B414463 : Blo 235815 414463 := bstep (se 1 (by rfl) ⟨310847, by rfl⟩ : syracuseStep 414463 = 621695) B621695
theorem B2873855 : Blo 235815 2873855 := bstep (se 1 (by rfl) ⟨2155391, by rfl⟩ : syracuseStep 2873855 = 4310783) B4310783
theorem B908927 : Blo 235815 908927 := bstep (se 1 (by rfl) ⟨681695, by rfl⟩ : syracuseStep 908927 = 1363391) B1363391
theorem B3268831 : Blo 235815 3268831 := bstep (se 1 (by rfl) ⟨2451623, by rfl⟩ : syracuseStep 3268831 = 4903247) B4903247
theorem B354815 : Blo 235815 354815 := bstep (se 1 (by rfl) ⟨266111, by rfl⟩ : syracuseStep 354815 = 532223) B532223
theorem B682823 : Blo 235815 682823 := bstep (se 1 (by rfl) ⟨512117, by rfl⟩ : syracuseStep 682823 = 1024235) B1024235
theorem B356591 : Blo 235815 356591 := bstep (se 1 (by rfl) ⟨267443, by rfl⟩ : syracuseStep 356591 = 534887) B534887
theorem B4358441 : Blo 235815 4358441 := bstep (se 2 (by rfl) ⟨1634415, by rfl⟩ : syracuseStep 4358441 = 3268831) B3268831
theorem B236543 : Blo 235815 236543 := bstep (se 1 (by rfl) ⟨177407, by rfl⟩ : syracuseStep 236543 = 354815) B354815
theorem B598063 : Blo 235815 598063 := bstep (se 1 (by rfl) ⟨448547, by rfl⟩ : syracuseStep 598063 = 897095) B897095
theorem B237727 : Blo 235815 237727 := bstep (se 1 (by rfl) ⟨178295, by rfl⟩ : syracuseStep 237727 = 356591) B356591
theorem B1811321 : Blo 235815 1811321 := bstep (se 2 (by rfl) ⟨679245, by rfl⟩ : syracuseStep 1811321 = 1358491) B1358491
theorem B5547325 : Blo 235815 5547325 := bstep (se 3 (by rfl) ⟨1040123, by rfl⟩ : syracuseStep 5547325 = 2080247) B2080247
theorem B798119 : Blo 235815 798119 := bstep (se 1 (by rfl) ⟨598589, by rfl⟩ : syracuseStep 798119 = 1197179) B1197179
theorem B1915903 : Blo 235815 1915903 := bstep (se 1 (by rfl) ⟨1436927, by rfl⟩ : syracuseStep 1915903 = 2873855) B2873855
theorem B605951 : Blo 235815 605951 := bstep (se 1 (by rfl) ⟨454463, by rfl⟩ : syracuseStep 605951 = 908927) B908927
theorem B903595 : Blo 235815 903595 := bstep (se 1 (by rfl) ⟨677696, by rfl⟩ : syracuseStep 903595 = 1355393) B1355393
theorem B2284847 : Blo 235815 2284847 := bstep (se 1 (by rfl) ⟨1713635, by rfl⟩ : syracuseStep 2284847 = 3427271) B3427271
theorem B7759871 : Blo 235815 7759871 := bstep (se 1 (by rfl) ⟨5819903, by rfl⟩ : syracuseStep 7759871 = 11639807) B11639807
theorem B552617 : Blo 235815 552617 := bstep (se 2 (by rfl) ⟨207231, by rfl⟩ : syracuseStep 552617 = 414463) B414463
theorem B455215 : Blo 235815 455215 := bstep (se 1 (by rfl) ⟨341411, by rfl⟩ : syracuseStep 455215 = 682823) B682823
theorem B358895 : Blo 235815 358895 := bstep (se 1 (by rfl) ⟨269171, by rfl⟩ : syracuseStep 358895 = 538343) B538343
theorem B2554793 : Blo 235815 2554793 := bstep (se 2 (by rfl) ⟨958047, by rfl⟩ : syracuseStep 2554793 = 1916095) B1916095
theorem B532079 : Blo 235815 532079 := bstep (se 1 (by rfl) ⟨399059, by rfl⟩ : syracuseStep 532079 = 798119) B798119
theorem B368411 : Blo 235815 368411 := bstep (se 1 (by rfl) ⟨276308, by rfl⟩ : syracuseStep 368411 = 552617) B552617
theorem B239263 : Blo 235815 239263 := bstep (se 1 (by rfl) ⟨179447, by rfl⟩ : syracuseStep 239263 = 358895) B358895
theorem B403967 : Blo 235815 403967 := bstep (se 1 (by rfl) ⟨302975, by rfl⟩ : syracuseStep 403967 = 605951) B605951
theorem B797417 : Blo 235815 797417 := bstep (se 2 (by rfl) ⟨299031, by rfl⟩ : syracuseStep 797417 = 598063) B598063
theorem B1523231 : Blo 235815 1523231 := bstep (se 1 (by rfl) ⟨1142423, by rfl⟩ : syracuseStep 1523231 = 2284847) B2284847
theorem B606953 : Blo 235815 606953 := bstep (se 2 (by rfl) ⟨227607, by rfl⟩ : syracuseStep 606953 = 455215) B455215
theorem B2905627 : Blo 235815 2905627 := bstep (se 1 (by rfl) ⟨2179220, by rfl⟩ : syracuseStep 2905627 = 4358441) B4358441
theorem B7396433 : Blo 235815 7396433 := bstep (se 2 (by rfl) ⟨2773662, by rfl⟩ : syracuseStep 7396433 = 5547325) B5547325
theorem B1204793 : Blo 235815 1204793 := bstep (se 2 (by rfl) ⟨451797, by rfl⟩ : syracuseStep 1204793 = 903595) B903595
theorem B1207547 : Blo 235815 1207547 := bstep (se 1 (by rfl) ⟨905660, by rfl⟩ : syracuseStep 1207547 = 1811321) B1811321
theorem B5173247 : Blo 235815 5173247 := bstep (se 1 (by rfl) ⟨3879935, by rfl⟩ : syracuseStep 5173247 = 7759871) B7759871
theorem B2554537 : Blo 235815 2554537 := bstep (se 2 (by rfl) ⟨957951, by rfl⟩ : syracuseStep 2554537 = 1915903) B1915903
theorem B1703195 : Blo 235815 1703195 := bstep (se 1 (by rfl) ⟨1277396, by rfl⟩ : syracuseStep 1703195 = 2554793) B2554793
theorem B269311 : Blo 235815 269311 := bstep (se 1 (by rfl) ⟨201983, by rfl⟩ : syracuseStep 269311 = 403967) B403967
theorem B531611 : Blo 235815 531611 := bstep (se 1 (by rfl) ⟨398708, by rfl⟩ : syracuseStep 531611 = 797417) B797417
theorem B3874169 : Blo 235815 3874169 := bstep (se 2 (by rfl) ⟨1452813, by rfl⟩ : syracuseStep 3874169 = 2905627) B2905627
theorem B3448831 : Blo 235815 3448831 := bstep (se 1 (by rfl) ⟨2586623, by rfl⟩ : syracuseStep 3448831 = 5173247) B5173247
theorem B404635 : Blo 235815 404635 := bstep (se 1 (by rfl) ⟨303476, by rfl⟩ : syracuseStep 404635 = 606953) B606953
theorem B4930955 : Blo 235815 4930955 := bstep (se 1 (by rfl) ⟨3698216, by rfl⟩ : syracuseStep 4930955 = 7396433) B7396433
theorem B803195 : Blo 235815 803195 := bstep (se 1 (by rfl) ⟨602396, by rfl⟩ : syracuseStep 803195 = 1204793) B1204793
theorem B805031 : Blo 235815 805031 := bstep (se 1 (by rfl) ⟨603773, by rfl⟩ : syracuseStep 805031 = 1207547) B1207547
theorem B1135463 : Blo 235815 1135463 := bstep (se 1 (by rfl) ⟨851597, by rfl⟩ : syracuseStep 1135463 = 1703195) B1703195
theorem B354719 : Blo 235815 354719 := bstep (se 1 (by rfl) ⟨266039, by rfl⟩ : syracuseStep 354719 = 532079) B532079
theorem B3929717 : Blo 235815 3929717 := bstep (se 5 (by rfl) ⟨184205, by rfl⟩ : syracuseStep 3929717 = 368411) B368411
theorem B3406049 : Blo 235815 3406049 := bstep (se 2 (by rfl) ⟨1277268, by rfl⟩ : syracuseStep 3406049 = 2554537) B2554537
theorem B1015487 : Blo 235815 1015487 := bstep (se 1 (by rfl) ⟨761615, by rfl⟩ : syracuseStep 1015487 = 1523231) B1523231
theorem B236479 : Blo 235815 236479 := bstep (se 1 (by rfl) ⟨177359, by rfl⟩ : syracuseStep 236479 = 354719) B354719
theorem B2270699 : Blo 235815 2270699 := bstep (se 1 (by rfl) ⟨1703024, by rfl⟩ : syracuseStep 2270699 = 3406049) B3406049
theorem B3287303 : Blo 235815 3287303 := bstep (se 1 (by rfl) ⟨2465477, by rfl⟩ : syracuseStep 3287303 = 4930955) B4930955
theorem B4598441 : Blo 235815 4598441 := bstep (se 2 (by rfl) ⟨1724415, by rfl⟩ : syracuseStep 4598441 = 3448831) B3448831
theorem B535463 : Blo 235815 535463 := bstep (se 1 (by rfl) ⟨401597, by rfl⟩ : syracuseStep 535463 = 803195) B803195
theorem B536687 : Blo 235815 536687 := bstep (se 1 (by rfl) ⟨402515, by rfl⟩ : syracuseStep 536687 = 805031) B805031
theorem B3027901 : Blo 235815 3027901 := bstep (se 3 (by rfl) ⟨567731, by rfl⟩ : syracuseStep 3027901 = 1135463) B1135463
theorem B539513 : Blo 235815 539513 := bstep (se 2 (by rfl) ⟨202317, by rfl⟩ : syracuseStep 539513 = 404635) B404635
theorem B676991 : Blo 235815 676991 := bstep (se 1 (by rfl) ⟨507743, by rfl⟩ : syracuseStep 676991 = 1015487) B1015487
theorem B354407 : Blo 235815 354407 := bstep (se 1 (by rfl) ⟨265805, by rfl⟩ : syracuseStep 354407 = 531611) B531611
theorem B2582779 : Blo 235815 2582779 := bstep (se 1 (by rfl) ⟨1937084, by rfl⟩ : syracuseStep 2582779 = 3874169) B3874169
theorem B2619811 : Blo 235815 2619811 := bstep (se 1 (by rfl) ⟨1964858, by rfl⟩ : syracuseStep 2619811 = 3929717) B3929717
theorem B359081 : Blo 235815 359081 := bstep (se 2 (by rfl) ⟨134655, by rfl⟩ : syracuseStep 359081 = 269311) B269311
theorem B3443705 : Blo 235815 3443705 := bstep (se 2 (by rfl) ⟨1291389, by rfl⟩ : syracuseStep 3443705 = 2582779) B2582779
theorem B1513799 : Blo 235815 1513799 := bstep (se 1 (by rfl) ⟨1135349, by rfl⟩ : syracuseStep 1513799 = 2270699) B2270699
theorem B4037201 : Blo 235815 4037201 := bstep (se 2 (by rfl) ⟨1513950, by rfl⟩ : syracuseStep 4037201 = 3027901) B3027901
theorem B236271 : Blo 235815 236271 := bstep (se 1 (by rfl) ⟨177203, by rfl⟩ : syracuseStep 236271 = 354407) B354407
theorem B239387 : Blo 235815 239387 := bstep (se 1 (by rfl) ⟨179540, by rfl⟩ : syracuseStep 239387 = 359081) B359081
theorem B3065627 : Blo 235815 3065627 := bstep (se 1 (by rfl) ⟨2299220, by rfl⟩ : syracuseStep 3065627 = 4598441) B4598441
theorem B3493081 : Blo 235815 3493081 := bstep (se 2 (by rfl) ⟨1309905, by rfl⟩ : syracuseStep 3493081 = 2619811) B2619811
theorem B451327 : Blo 235815 451327 := bstep (se 1 (by rfl) ⟨338495, by rfl⟩ : syracuseStep 451327 = 676991) B676991
theorem B2191535 : Blo 235815 2191535 := bstep (se 1 (by rfl) ⟨1643651, by rfl⟩ : syracuseStep 2191535 = 3287303) B3287303
theorem B356975 : Blo 235815 356975 := bstep (se 1 (by rfl) ⟨267731, by rfl⟩ : syracuseStep 356975 = 535463) B535463
theorem B357791 : Blo 235815 357791 := bstep (se 1 (by rfl) ⟨268343, by rfl⟩ : syracuseStep 357791 = 536687) B536687
theorem B359675 : Blo 235815 359675 := bstep (se 1 (by rfl) ⟨269756, by rfl⟩ : syracuseStep 359675 = 539513) B539513
theorem B2295803 : Blo 235815 2295803 := bstep (se 1 (by rfl) ⟨1721852, by rfl⟩ : syracuseStep 2295803 = 3443705) B3443705
theorem B4657441 : Blo 235815 4657441 := bstep (se 2 (by rfl) ⟨1746540, by rfl⟩ : syracuseStep 4657441 = 3493081) B3493081
theorem B2691467 : Blo 235815 2691467 := bstep (se 1 (by rfl) ⟨2018600, by rfl⟩ : syracuseStep 2691467 = 4037201) B4037201
theorem B237983 : Blo 235815 237983 := bstep (se 1 (by rfl) ⟨178487, by rfl⟩ : syracuseStep 237983 = 356975) B356975
theorem B238527 : Blo 235815 238527 := bstep (se 1 (by rfl) ⟨178895, by rfl⟩ : syracuseStep 238527 = 357791) B357791
theorem B239783 : Blo 235815 239783 := bstep (se 1 (by rfl) ⟨179837, by rfl⟩ : syracuseStep 239783 = 359675) B359675
theorem B601769 : Blo 235815 601769 := bstep (se 2 (by rfl) ⟨225663, by rfl⟩ : syracuseStep 601769 = 451327) B451327
theorem B2043751 : Blo 235815 2043751 := bstep (se 1 (by rfl) ⟨1532813, by rfl⟩ : syracuseStep 2043751 = 3065627) B3065627
theorem B1461023 : Blo 235815 1461023 := bstep (se 1 (by rfl) ⟨1095767, by rfl⟩ : syracuseStep 1461023 = 2191535) B2191535
theorem B1009199 : Blo 235815 1009199 := bstep (se 1 (by rfl) ⟨756899, by rfl⟩ : syracuseStep 1009199 = 1513799) B1513799
theorem B2725001 : Blo 235815 2725001 := bstep (se 2 (by rfl) ⟨1021875, by rfl⟩ : syracuseStep 2725001 = 2043751) B2043751
theorem B401179 : Blo 235815 401179 := bstep (se 1 (by rfl) ⟨300884, by rfl⟩ : syracuseStep 401179 = 601769) B601769
theorem B6209921 : Blo 235815 6209921 := bstep (se 2 (by rfl) ⟨2328720, by rfl⟩ : syracuseStep 6209921 = 4657441) B4657441
theorem B672799 : Blo 235815 672799 := bstep (se 1 (by rfl) ⟨504599, by rfl⟩ : syracuseStep 672799 = 1009199) B1009199
theorem B1530535 : Blo 235815 1530535 := bstep (se 1 (by rfl) ⟨1147901, by rfl⟩ : syracuseStep 1530535 = 2295803) B2295803
theorem B974015 : Blo 235815 974015 := bstep (se 1 (by rfl) ⟨730511, by rfl⟩ : syracuseStep 974015 = 1461023) B1461023
theorem B1794311 : Blo 235815 1794311 := bstep (se 1 (by rfl) ⟨1345733, by rfl⟩ : syracuseStep 1794311 = 2691467) B2691467
theorem B2040713 : Blo 235815 2040713 := bstep (se 2 (by rfl) ⟨765267, by rfl⟩ : syracuseStep 2040713 = 1530535) B1530535
theorem B534905 : Blo 235815 534905 := bstep (se 2 (by rfl) ⟨200589, by rfl⟩ : syracuseStep 534905 = 401179) B401179
theorem B4139947 : Blo 235815 4139947 := bstep (se 1 (by rfl) ⟨3104960, by rfl⟩ : syracuseStep 4139947 = 6209921) B6209921
theorem B897065 : Blo 235815 897065 := bstep (se 2 (by rfl) ⟨336399, by rfl⟩ : syracuseStep 897065 = 672799) B672799
theorem B1816667 : Blo 235815 1816667 := bstep (se 1 (by rfl) ⟨1362500, by rfl⟩ : syracuseStep 1816667 = 2725001) B2725001
theorem B1196207 : Blo 235815 1196207 := bstep (se 1 (by rfl) ⟨897155, by rfl⟩ : syracuseStep 1196207 = 1794311) B1794311
theorem B649343 : Blo 235815 649343 := bstep (se 1 (by rfl) ⟨487007, by rfl⟩ : syracuseStep 649343 = 974015) B974015
theorem B598043 : Blo 235815 598043 := bstep (se 1 (by rfl) ⟨448532, by rfl⟩ : syracuseStep 598043 = 897065) B897065
theorem B797471 : Blo 235815 797471 := bstep (se 1 (by rfl) ⟨598103, by rfl⟩ : syracuseStep 797471 = 1196207) B1196207
theorem B5519929 : Blo 235815 5519929 := bstep (se 2 (by rfl) ⟨2069973, by rfl⟩ : syracuseStep 5519929 = 4139947) B4139947
theorem B1360475 : Blo 235815 1360475 := bstep (se 1 (by rfl) ⟨1020356, by rfl⟩ : syracuseStep 1360475 = 2040713) B2040713
theorem B1731581 : Blo 235815 1731581 := bstep (se 3 (by rfl) ⟨324671, by rfl⟩ : syracuseStep 1731581 = 649343) B649343
theorem B356603 : Blo 235815 356603 := bstep (se 1 (by rfl) ⟨267452, by rfl⟩ : syracuseStep 356603 = 534905) B534905
theorem B1211111 : Blo 235815 1211111 := bstep (se 1 (by rfl) ⟨908333, by rfl⟩ : syracuseStep 1211111 = 1816667) B1816667
theorem B398695 : Blo 235815 398695 := bstep (se 1 (by rfl) ⟨299021, by rfl⟩ : syracuseStep 398695 = 598043) B598043
theorem B531647 : Blo 235815 531647 := bstep (se 1 (by rfl) ⟨398735, by rfl⟩ : syracuseStep 531647 = 797471) B797471
theorem B1154387 : Blo 235815 1154387 := bstep (se 1 (by rfl) ⟨865790, by rfl⟩ : syracuseStep 1154387 = 1731581) B1731581
theorem B237735 : Blo 235815 237735 := bstep (se 1 (by rfl) ⟨178301, by rfl⟩ : syracuseStep 237735 = 356603) B356603
theorem B7359905 : Blo 235815 7359905 := bstep (se 2 (by rfl) ⟨2759964, by rfl⟩ : syracuseStep 7359905 = 5519929) B5519929
theorem B807407 : Blo 235815 807407 := bstep (se 1 (by rfl) ⟨605555, by rfl⟩ : syracuseStep 807407 = 1211111) B1211111
theorem B906983 : Blo 235815 906983 := bstep (se 1 (by rfl) ⟨680237, by rfl⟩ : syracuseStep 906983 = 1360475) B1360475
theorem B531593 : Blo 235815 531593 := bstep (se 2 (by rfl) ⟨199347, by rfl⟩ : syracuseStep 531593 = 398695) B398695
theorem B538271 : Blo 235815 538271 := bstep (se 1 (by rfl) ⟨403703, by rfl⟩ : syracuseStep 538271 = 807407) B807407
theorem B604655 : Blo 235815 604655 := bstep (se 1 (by rfl) ⟨453491, by rfl⟩ : syracuseStep 604655 = 906983) B906983
theorem B769591 : Blo 235815 769591 := bstep (se 1 (by rfl) ⟨577193, by rfl⟩ : syracuseStep 769591 = 1154387) B1154387
theorem B4906603 : Blo 235815 4906603 := bstep (se 1 (by rfl) ⟨3679952, by rfl⟩ : syracuseStep 4906603 = 7359905) B7359905
theorem B354431 : Blo 235815 354431 := bstep (se 1 (by rfl) ⟨265823, by rfl⟩ : syracuseStep 354431 = 531647) B531647
theorem B236287 : Blo 235815 236287 := bstep (se 1 (by rfl) ⟨177215, by rfl⟩ : syracuseStep 236287 = 354431) B354431
theorem B403103 : Blo 235815 403103 := bstep (se 1 (by rfl) ⟨302327, by rfl⟩ : syracuseStep 403103 = 604655) B604655
theorem B1026121 : Blo 235815 1026121 := bstep (se 2 (by rfl) ⟨384795, by rfl⟩ : syracuseStep 1026121 = 769591) B769591
theorem B6542137 : Blo 235815 6542137 := bstep (se 2 (by rfl) ⟨2453301, by rfl⟩ : syracuseStep 6542137 = 4906603) B4906603
theorem B354395 : Blo 235815 354395 := bstep (se 1 (by rfl) ⟨265796, by rfl⟩ : syracuseStep 354395 = 531593) B531593
theorem B358847 : Blo 235815 358847 := bstep (se 1 (by rfl) ⟨269135, by rfl⟩ : syracuseStep 358847 = 538271) B538271
theorem B268735 : Blo 235815 268735 := bstep (se 1 (by rfl) ⟨201551, by rfl⟩ : syracuseStep 268735 = 403103) B403103
theorem B236263 : Blo 235815 236263 := bstep (se 1 (by rfl) ⟨177197, by rfl⟩ : syracuseStep 236263 = 354395) B354395
theorem B239231 : Blo 235815 239231 := bstep (se 1 (by rfl) ⟨179423, by rfl⟩ : syracuseStep 239231 = 358847) B358847
theorem B1368161 : Blo 235815 1368161 := bstep (se 2 (by rfl) ⟨513060, by rfl⟩ : syracuseStep 1368161 = 1026121) B1026121
theorem B34891397 : Blo 235815 34891397 := bstep (se 4 (by rfl) ⟨3271068, by rfl⟩ : syracuseStep 34891397 = 6542137) B6542137
theorem B912107 : Blo 235815 912107 := bstep (se 1 (by rfl) ⟨684080, by rfl⟩ : syracuseStep 912107 = 1368161) B1368161
theorem B23260931 : Blo 235815 23260931 := bstep (se 1 (by rfl) ⟨17445698, by rfl⟩ : syracuseStep 23260931 = 34891397) B34891397
theorem B358313 : Blo 235815 358313 := bstep (se 2 (by rfl) ⟨134367, by rfl⟩ : syracuseStep 358313 = 268735) B268735
theorem B15507287 : Blo 235815 15507287 := bstep (se 1 (by rfl) ⟨11630465, by rfl⟩ : syracuseStep 15507287 = 23260931) B23260931
theorem B238875 : Blo 235815 238875 := bstep (se 1 (by rfl) ⟨179156, by rfl⟩ : syracuseStep 238875 = 358313) B358313
theorem B608071 : Blo 235815 608071 := bstep (se 1 (by rfl) ⟨456053, by rfl⟩ : syracuseStep 608071 = 912107) B912107
theorem B10338191 : Blo 235815 10338191 := bstep (se 1 (by rfl) ⟨7753643, by rfl⟩ : syracuseStep 10338191 = 15507287) B15507287
theorem B810761 : Blo 235815 810761 := bstep (se 2 (by rfl) ⟨304035, by rfl⟩ : syracuseStep 810761 = 608071) B608071
theorem B6892127 : Blo 235815 6892127 := bstep (se 1 (by rfl) ⟨5169095, by rfl⟩ : syracuseStep 6892127 = 10338191) B10338191
theorem B8648117 : Blo 235815 8648117 := bstep (se 5 (by rfl) ⟨405380, by rfl⟩ : syracuseStep 8648117 = 810761) B810761
theorem B4594751 : Blo 235815 4594751 := bstep (se 1 (by rfl) ⟨3446063, by rfl⟩ : syracuseStep 4594751 = 6892127) B6892127
theorem B5765411 : Blo 235815 5765411 := bstep (se 1 (by rfl) ⟨4324058, by rfl⟩ : syracuseStep 5765411 = 8648117) B8648117
theorem B3843607 : Blo 235815 3843607 := bstep (se 1 (by rfl) ⟨2882705, by rfl⟩ : syracuseStep 3843607 = 5765411) B5765411
theorem B3063167 : Blo 235815 3063167 := bstep (se 1 (by rfl) ⟨2297375, by rfl⟩ : syracuseStep 3063167 = 4594751) B4594751
theorem B2042111 : Blo 235815 2042111 := bstep (se 1 (by rfl) ⟨1531583, by rfl⟩ : syracuseStep 2042111 = 3063167) B3063167
theorem B5124809 : Blo 235815 5124809 := bstep (se 2 (by rfl) ⟨1921803, by rfl⟩ : syracuseStep 5124809 = 3843607) B3843607
theorem B3416539 : Blo 235815 3416539 := bstep (se 1 (by rfl) ⟨2562404, by rfl⟩ : syracuseStep 3416539 = 5124809) B5124809
theorem B1361407 : Blo 235815 1361407 := bstep (se 1 (by rfl) ⟨1021055, by rfl⟩ : syracuseStep 1361407 = 2042111) B2042111
theorem B4555385 : Blo 235815 4555385 := bstep (se 2 (by rfl) ⟨1708269, by rfl⟩ : syracuseStep 4555385 = 3416539) B3416539
theorem B1815209 : Blo 235815 1815209 := bstep (se 2 (by rfl) ⟨680703, by rfl⟩ : syracuseStep 1815209 = 1361407) B1361407
theorem B3036923 : Blo 235815 3036923 := bstep (se 1 (by rfl) ⟨2277692, by rfl⟩ : syracuseStep 3036923 = 4555385) B4555385
theorem B1210139 : Blo 235815 1210139 := bstep (se 1 (by rfl) ⟨907604, by rfl⟩ : syracuseStep 1210139 = 1815209) B1815209
theorem B806759 : Blo 235815 806759 := bstep (se 1 (by rfl) ⟨605069, by rfl⟩ : syracuseStep 806759 = 1210139) B1210139
theorem B2024615 : Blo 235815 2024615 := bstep (se 1 (by rfl) ⟨1518461, by rfl⟩ : syracuseStep 2024615 = 3036923) B3036923
theorem B1349743 : Blo 235815 1349743 := bstep (se 1 (by rfl) ⟨1012307, by rfl⟩ : syracuseStep 1349743 = 2024615) B2024615
theorem B537839 : Blo 235815 537839 := bstep (se 1 (by rfl) ⟨403379, by rfl⟩ : syracuseStep 537839 = 806759) B806759
theorem B1799657 : Blo 235815 1799657 := bstep (se 2 (by rfl) ⟨674871, by rfl⟩ : syracuseStep 1799657 = 1349743) B1349743
theorem B358559 : Blo 235815 358559 := bstep (se 1 (by rfl) ⟨268919, by rfl⟩ : syracuseStep 358559 = 537839) B537839
theorem B239039 : Blo 235815 239039 := bstep (se 1 (by rfl) ⟨179279, by rfl⟩ : syracuseStep 239039 = 358559) B358559
theorem B1199771 : Blo 235815 1199771 := bstep (se 1 (by rfl) ⟨899828, by rfl⟩ : syracuseStep 1199771 = 1799657) B1799657
theorem B799847 : Blo 235815 799847 := bstep (se 1 (by rfl) ⟨599885, by rfl⟩ : syracuseStep 799847 = 1199771) B1199771
theorem B533231 : Blo 235815 533231 := bstep (se 1 (by rfl) ⟨399923, by rfl⟩ : syracuseStep 533231 = 799847) B799847
theorem B355487 : Blo 235815 355487 := bstep (se 1 (by rfl) ⟨266615, by rfl⟩ : syracuseStep 355487 = 533231) B533231
theorem B236991 : Blo 235815 236991 := bstep (se 1 (by rfl) ⟨177743, by rfl⟩ : syracuseStep 236991 = 355487) B355487

theorem C0 (j : ℕ) (h1 : 58953 ≤ j) (h2 : j ≤ 59652) : Blo 235815 (4 * j + 3) := by
  interval_cases j
  · exact B235815
  · exact B235819
  · exact B235823
  · exact B235827
  · exact B235831
  · exact B235835
  · exact B235839
  · exact B235843
  · exact B235847
  · exact B235851
  · exact B235855
  · exact B235859
  · exact B235863
  · exact B235867
  · exact B235871
  · exact B235875
  · exact B235879
  · exact B235883
  · exact B235887
  · exact B235891
  · exact B235895
  · exact B235899
  · exact B235903
  · exact B235907
  · exact B235911
  · exact B235915
  · exact B235919
  · exact B235923
  · exact B235927
  · exact B235931
  · exact B235935
  · exact B235939
  · exact B235943
  · exact B235947
  · exact B235951
  · exact B235955
  · exact B235959
  · exact B235963
  · exact B235967
  · exact B235971
  · exact B235975
  · exact B235979
  · exact B235983
  · exact B235987
  · exact B235991
  · exact B235995
  · exact B235999
  · exact B236003
  · exact B236007
  · exact B236011
  · exact B236015
  · exact B236019
  · exact B236023
  · exact B236027
  · exact B236031
  · exact B236035
  · exact B236039
  · exact B236043
  · exact B236047
  · exact B236051
  · exact B236055
  · exact B236059
  · exact B236063
  · exact B236067
  · exact B236071
  · exact B236075
  · exact B236079
  · exact B236083
  · exact B236087
  · exact B236091
  · exact B236095
  · exact B236099
  · exact B236103
  · exact B236107
  · exact B236111
  · exact B236115
  · exact B236119
  · exact B236123
  · exact B236127
  · exact B236131
  · exact B236135
  · exact B236139
  · exact B236143
  · exact B236147
  · exact B236151
  · exact B236155
  · exact B236159
  · exact B236163
  · exact B236167
  · exact B236171
  · exact B236175
  · exact B236179
  · exact B236183
  · exact B236187
  · exact B236191
  · exact B236195
  · exact B236199
  · exact B236203
  · exact B236207
  · exact B236211
  · exact B236215
  · exact B236219
  · exact B236223
  · exact B236227
  · exact B236231
  · exact B236235
  · exact B236239
  · exact B236243
  · exact B236247
  · exact B236251
  · exact B236255
  · exact B236259
  · exact B236263
  · exact B236267
  · exact B236271
  · exact B236275
  · exact B236279
  · exact B236283
  · exact B236287
  · exact B236291
  · exact B236295
  · exact B236299
  · exact B236303
  · exact B236307
  · exact B236311
  · exact B236315
  · exact B236319
  · exact B236323
  · exact B236327
  · exact B236331
  · exact B236335
  · exact B236339
  · exact B236343
  · exact B236347
  · exact B236351
  · exact B236355
  · exact B236359
  · exact B236363
  · exact B236367
  · exact B236371
  · exact B236375
  · exact B236379
  · exact B236383
  · exact B236387
  · exact B236391
  · exact B236395
  · exact B236399
  · exact B236403
  · exact B236407
  · exact B236411
  · exact B236415
  · exact B236419
  · exact B236423
  · exact B236427
  · exact B236431
  · exact B236435
  · exact B236439
  · exact B236443
  · exact B236447
  · exact B236451
  · exact B236455
  · exact B236459
  · exact B236463
  · exact B236467
  · exact B236471
  · exact B236475
  · exact B236479
  · exact B236483
  · exact B236487
  · exact B236491
  · exact B236495
  · exact B236499
  · exact B236503
  · exact B236507
  · exact B236511
  · exact B236515
  · exact B236519
  · exact B236523
  · exact B236527
  · exact B236531
  · exact B236535
  · exact B236539
  · exact B236543
  · exact B236547
  · exact B236551
  · exact B236555
  · exact B236559
  · exact B236563
  · exact B236567
  · exact B236571
  · exact B236575
  · exact B236579
  · exact B236583
  · exact B236587
  · exact B236591
  · exact B236595
  · exact B236599
  · exact B236603
  · exact B236607
  · exact B236611
  · exact B236615
  · exact B236619
  · exact B236623
  · exact B236627
  · exact B236631
  · exact B236635
  · exact B236639
  · exact B236643
  · exact B236647
  · exact B236651
  · exact B236655
  · exact B236659
  · exact B236663
  · exact B236667
  · exact B236671
  · exact B236675
  · exact B236679
  · exact B236683
  · exact B236687
  · exact B236691
  · exact B236695
  · exact B236699
  · exact B236703
  · exact B236707
  · exact B236711
  · exact B236715
  · exact B236719
  · exact B236723
  · exact B236727
  · exact B236731
  · exact B236735
  · exact B236739
  · exact B236743
  · exact B236747
  · exact B236751
  · exact B236755
  · exact B236759
  · exact B236763
  · exact B236767
  · exact B236771
  · exact B236775
  · exact B236779
  · exact B236783
  · exact B236787
  · exact B236791
  · exact B236795
  · exact B236799
  · exact B236803
  · exact B236807
  · exact B236811
  · exact B236815
  · exact B236819
  · exact B236823
  · exact B236827
  · exact B236831
  · exact B236835
  · exact B236839
  · exact B236843
  · exact B236847
  · exact B236851
  · exact B236855
  · exact B236859
  · exact B236863
  · exact B236867
  · exact B236871
  · exact B236875
  · exact B236879
  · exact B236883
  · exact B236887
  · exact B236891
  · exact B236895
  · exact B236899
  · exact B236903
  · exact B236907
  · exact B236911
  · exact B236915
  · exact B236919
  · exact B236923
  · exact B236927
  · exact B236931
  · exact B236935
  · exact B236939
  · exact B236943
  · exact B236947
  · exact B236951
  · exact B236955
  · exact B236959
  · exact B236963
  · exact B236967
  · exact B236971
  · exact B236975
  · exact B236979
  · exact B236983
  · exact B236987
  · exact B236991
  · exact B236995
  · exact B236999
  · exact B237003
  · exact B237007
  · exact B237011
  · exact B237015
  · exact B237019
  · exact B237023
  · exact B237027
  · exact B237031
  · exact B237035
  · exact B237039
  · exact B237043
  · exact B237047
  · exact B237051
  · exact B237055
  · exact B237059
  · exact B237063
  · exact B237067
  · exact B237071
  · exact B237075
  · exact B237079
  · exact B237083
  · exact B237087
  · exact B237091
  · exact B237095
  · exact B237099
  · exact B237103
  · exact B237107
  · exact B237111
  · exact B237115
  · exact B237119
  · exact B237123
  · exact B237127
  · exact B237131
  · exact B237135
  · exact B237139
  · exact B237143
  · exact B237147
  · exact B237151
  · exact B237155
  · exact B237159
  · exact B237163
  · exact B237167
  · exact B237171
  · exact B237175
  · exact B237179
  · exact B237183
  · exact B237187
  · exact B237191
  · exact B237195
  · exact B237199
  · exact B237203
  · exact B237207
  · exact B237211
  · exact B237215
  · exact B237219
  · exact B237223
  · exact B237227
  · exact B237231
  · exact B237235
  · exact B237239
  · exact B237243
  · exact B237247
  · exact B237251
  · exact B237255
  · exact B237259
  · exact B237263
  · exact B237267
  · exact B237271
  · exact B237275
  · exact B237279
  · exact B237283
  · exact B237287
  · exact B237291
  · exact B237295
  · exact B237299
  · exact B237303
  · exact B237307
  · exact B237311
  · exact B237315
  · exact B237319
  · exact B237323
  · exact B237327
  · exact B237331
  · exact B237335
  · exact B237339
  · exact B237343
  · exact B237347
  · exact B237351
  · exact B237355
  · exact B237359
  · exact B237363
  · exact B237367
  · exact B237371
  · exact B237375
  · exact B237379
  · exact B237383
  · exact B237387
  · exact B237391
  · exact B237395
  · exact B237399
  · exact B237403
  · exact B237407
  · exact B237411
  · exact B237415
  · exact B237419
  · exact B237423
  · exact B237427
  · exact B237431
  · exact B237435
  · exact B237439
  · exact B237443
  · exact B237447
  · exact B237451
  · exact B237455
  · exact B237459
  · exact B237463
  · exact B237467
  · exact B237471
  · exact B237475
  · exact B237479
  · exact B237483
  · exact B237487
  · exact B237491
  · exact B237495
  · exact B237499
  · exact B237503
  · exact B237507
  · exact B237511
  · exact B237515
  · exact B237519
  · exact B237523
  · exact B237527
  · exact B237531
  · exact B237535
  · exact B237539
  · exact B237543
  · exact B237547
  · exact B237551
  · exact B237555
  · exact B237559
  · exact B237563
  · exact B237567
  · exact B237571
  · exact B237575
  · exact B237579
  · exact B237583
  · exact B237587
  · exact B237591
  · exact B237595
  · exact B237599
  · exact B237603
  · exact B237607
  · exact B237611
  · exact B237615
  · exact B237619
  · exact B237623
  · exact B237627
  · exact B237631
  · exact B237635
  · exact B237639
  · exact B237643
  · exact B237647
  · exact B237651
  · exact B237655
  · exact B237659
  · exact B237663
  · exact B237667
  · exact B237671
  · exact B237675
  · exact B237679
  · exact B237683
  · exact B237687
  · exact B237691
  · exact B237695
  · exact B237699
  · exact B237703
  · exact B237707
  · exact B237711
  · exact B237715
  · exact B237719
  · exact B237723
  · exact B237727
  · exact B237731
  · exact B237735
  · exact B237739
  · exact B237743
  · exact B237747
  · exact B237751
  · exact B237755
  · exact B237759
  · exact B237763
  · exact B237767
  · exact B237771
  · exact B237775
  · exact B237779
  · exact B237783
  · exact B237787
  · exact B237791
  · exact B237795
  · exact B237799
  · exact B237803
  · exact B237807
  · exact B237811
  · exact B237815
  · exact B237819
  · exact B237823
  · exact B237827
  · exact B237831
  · exact B237835
  · exact B237839
  · exact B237843
  · exact B237847
  · exact B237851
  · exact B237855
  · exact B237859
  · exact B237863
  · exact B237867
  · exact B237871
  · exact B237875
  · exact B237879
  · exact B237883
  · exact B237887
  · exact B237891
  · exact B237895
  · exact B237899
  · exact B237903
  · exact B237907
  · exact B237911
  · exact B237915
  · exact B237919
  · exact B237923
  · exact B237927
  · exact B237931
  · exact B237935
  · exact B237939
  · exact B237943
  · exact B237947
  · exact B237951
  · exact B237955
  · exact B237959
  · exact B237963
  · exact B237967
  · exact B237971
  · exact B237975
  · exact B237979
  · exact B237983
  · exact B237987
  · exact B237991
  · exact B237995
  · exact B237999
  · exact B238003
  · exact B238007
  · exact B238011
  · exact B238015
  · exact B238019
  · exact B238023
  · exact B238027
  · exact B238031
  · exact B238035
  · exact B238039
  · exact B238043
  · exact B238047
  · exact B238051
  · exact B238055
  · exact B238059
  · exact B238063
  · exact B238067
  · exact B238071
  · exact B238075
  · exact B238079
  · exact B238083
  · exact B238087
  · exact B238091
  · exact B238095
  · exact B238099
  · exact B238103
  · exact B238107
  · exact B238111
  · exact B238115
  · exact B238119
  · exact B238123
  · exact B238127
  · exact B238131
  · exact B238135
  · exact B238139
  · exact B238143
  · exact B238147
  · exact B238151
  · exact B238155
  · exact B238159
  · exact B238163
  · exact B238167
  · exact B238171
  · exact B238175
  · exact B238179
  · exact B238183
  · exact B238187
  · exact B238191
  · exact B238195
  · exact B238199
  · exact B238203
  · exact B238207
  · exact B238211
  · exact B238215
  · exact B238219
  · exact B238223
  · exact B238227
  · exact B238231
  · exact B238235
  · exact B238239
  · exact B238243
  · exact B238247
  · exact B238251
  · exact B238255
  · exact B238259
  · exact B238263
  · exact B238267
  · exact B238271
  · exact B238275
  · exact B238279
  · exact B238283
  · exact B238287
  · exact B238291
  · exact B238295
  · exact B238299
  · exact B238303
  · exact B238307
  · exact B238311
  · exact B238315
  · exact B238319
  · exact B238323
  · exact B238327
  · exact B238331
  · exact B238335
  · exact B238339
  · exact B238343
  · exact B238347
  · exact B238351
  · exact B238355
  · exact B238359
  · exact B238363
  · exact B238367
  · exact B238371
  · exact B238375
  · exact B238379
  · exact B238383
  · exact B238387
  · exact B238391
  · exact B238395
  · exact B238399
  · exact B238403
  · exact B238407
  · exact B238411
  · exact B238415
  · exact B238419
  · exact B238423
  · exact B238427
  · exact B238431
  · exact B238435
  · exact B238439
  · exact B238443
  · exact B238447
  · exact B238451
  · exact B238455
  · exact B238459
  · exact B238463
  · exact B238467
  · exact B238471
  · exact B238475
  · exact B238479
  · exact B238483
  · exact B238487
  · exact B238491
  · exact B238495
  · exact B238499
  · exact B238503
  · exact B238507
  · exact B238511
  · exact B238515
  · exact B238519
  · exact B238523
  · exact B238527
  · exact B238531
  · exact B238535
  · exact B238539
  · exact B238543
  · exact B238547
  · exact B238551
  · exact B238555
  · exact B238559
  · exact B238563
  · exact B238567
  · exact B238571
  · exact B238575
  · exact B238579
  · exact B238583
  · exact B238587
  · exact B238591
  · exact B238595
  · exact B238599
  · exact B238603
  · exact B238607
  · exact B238611

theorem C1 (j : ℕ) (h1 : 59653 ≤ j) (h2 : j ≤ 59953) : Blo 235815 (4 * j + 3) := by
  interval_cases j
  · exact B238615
  · exact B238619
  · exact B238623
  · exact B238627
  · exact B238631
  · exact B238635
  · exact B238639
  · exact B238643
  · exact B238647
  · exact B238651
  · exact B238655
  · exact B238659
  · exact B238663
  · exact B238667
  · exact B238671
  · exact B238675
  · exact B238679
  · exact B238683
  · exact B238687
  · exact B238691
  · exact B238695
  · exact B238699
  · exact B238703
  · exact B238707
  · exact B238711
  · exact B238715
  · exact B238719
  · exact B238723
  · exact B238727
  · exact B238731
  · exact B238735
  · exact B238739
  · exact B238743
  · exact B238747
  · exact B238751
  · exact B238755
  · exact B238759
  · exact B238763
  · exact B238767
  · exact B238771
  · exact B238775
  · exact B238779
  · exact B238783
  · exact B238787
  · exact B238791
  · exact B238795
  · exact B238799
  · exact B238803
  · exact B238807
  · exact B238811
  · exact B238815
  · exact B238819
  · exact B238823
  · exact B238827
  · exact B238831
  · exact B238835
  · exact B238839
  · exact B238843
  · exact B238847
  · exact B238851
  · exact B238855
  · exact B238859
  · exact B238863
  · exact B238867
  · exact B238871
  · exact B238875
  · exact B238879
  · exact B238883
  · exact B238887
  · exact B238891
  · exact B238895
  · exact B238899
  · exact B238903
  · exact B238907
  · exact B238911
  · exact B238915
  · exact B238919
  · exact B238923
  · exact B238927
  · exact B238931
  · exact B238935
  · exact B238939
  · exact B238943
  · exact B238947
  · exact B238951
  · exact B238955
  · exact B238959
  · exact B238963
  · exact B238967
  · exact B238971
  · exact B238975
  · exact B238979
  · exact B238983
  · exact B238987
  · exact B238991
  · exact B238995
  · exact B238999
  · exact B239003
  · exact B239007
  · exact B239011
  · exact B239015
  · exact B239019
  · exact B239023
  · exact B239027
  · exact B239031
  · exact B239035
  · exact B239039
  · exact B239043
  · exact B239047
  · exact B239051
  · exact B239055
  · exact B239059
  · exact B239063
  · exact B239067
  · exact B239071
  · exact B239075
  · exact B239079
  · exact B239083
  · exact B239087
  · exact B239091
  · exact B239095
  · exact B239099
  · exact B239103
  · exact B239107
  · exact B239111
  · exact B239115
  · exact B239119
  · exact B239123
  · exact B239127
  · exact B239131
  · exact B239135
  · exact B239139
  · exact B239143
  · exact B239147
  · exact B239151
  · exact B239155
  · exact B239159
  · exact B239163
  · exact B239167
  · exact B239171
  · exact B239175
  · exact B239179
  · exact B239183
  · exact B239187
  · exact B239191
  · exact B239195
  · exact B239199
  · exact B239203
  · exact B239207
  · exact B239211
  · exact B239215
  · exact B239219
  · exact B239223
  · exact B239227
  · exact B239231
  · exact B239235
  · exact B239239
  · exact B239243
  · exact B239247
  · exact B239251
  · exact B239255
  · exact B239259
  · exact B239263
  · exact B239267
  · exact B239271
  · exact B239275
  · exact B239279
  · exact B239283
  · exact B239287
  · exact B239291
  · exact B239295
  · exact B239299
  · exact B239303
  · exact B239307
  · exact B239311
  · exact B239315
  · exact B239319
  · exact B239323
  · exact B239327
  · exact B239331
  · exact B239335
  · exact B239339
  · exact B239343
  · exact B239347
  · exact B239351
  · exact B239355
  · exact B239359
  · exact B239363
  · exact B239367
  · exact B239371
  · exact B239375
  · exact B239379
  · exact B239383
  · exact B239387
  · exact B239391
  · exact B239395
  · exact B239399
  · exact B239403
  · exact B239407
  · exact B239411
  · exact B239415
  · exact B239419
  · exact B239423
  · exact B239427
  · exact B239431
  · exact B239435
  · exact B239439
  · exact B239443
  · exact B239447
  · exact B239451
  · exact B239455
  · exact B239459
  · exact B239463
  · exact B239467
  · exact B239471
  · exact B239475
  · exact B239479
  · exact B239483
  · exact B239487
  · exact B239491
  · exact B239495
  · exact B239499
  · exact B239503
  · exact B239507
  · exact B239511
  · exact B239515
  · exact B239519
  · exact B239523
  · exact B239527
  · exact B239531
  · exact B239535
  · exact B239539
  · exact B239543
  · exact B239547
  · exact B239551
  · exact B239555
  · exact B239559
  · exact B239563
  · exact B239567
  · exact B239571
  · exact B239575
  · exact B239579
  · exact B239583
  · exact B239587
  · exact B239591
  · exact B239595
  · exact B239599
  · exact B239603
  · exact B239607
  · exact B239611
  · exact B239615
  · exact B239619
  · exact B239623
  · exact B239627
  · exact B239631
  · exact B239635
  · exact B239639
  · exact B239643
  · exact B239647
  · exact B239651
  · exact B239655
  · exact B239659
  · exact B239663
  · exact B239667
  · exact B239671
  · exact B239675
  · exact B239679
  · exact B239683
  · exact B239687
  · exact B239691
  · exact B239695
  · exact B239699
  · exact B239703
  · exact B239707
  · exact B239711
  · exact B239715
  · exact B239719
  · exact B239723
  · exact B239727
  · exact B239731
  · exact B239735
  · exact B239739
  · exact B239743
  · exact B239747
  · exact B239751
  · exact B239755
  · exact B239759
  · exact B239763
  · exact B239767
  · exact B239771
  · exact B239775
  · exact B239779
  · exact B239783
  · exact B239787
  · exact B239791
  · exact B239795
  · exact B239799
  · exact B239803
  · exact B239807
  · exact B239811
  · exact B239815

theorem solution (m : ℕ) (hlo : 235815 ≤ m) (hhi : m ≤ 239815) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 58953 ≤ j := by omega
    have hj2 : j ≤ 59953 := by omega
    have hb : Blo 235815 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 59653 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
