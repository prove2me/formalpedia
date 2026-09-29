-- Prove2me | solution 1 for syracuse_descends_range_163797_167797
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:42.601323+00:00
-- url     : https://prove2.me/submissions/027b0ca4-9181-4b9c-94cc-adb924842bfd

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


theorem B852133 : Blo 163797 852133 := bbase (se 4 (by rfl) ⟨79887, by rfl⟩ : syracuseStep 852133 = 159775) (by norm_num)
theorem B950453 : Blo 163797 950453 := bbase (se 5 (by rfl) ⟨44552, by rfl⟩ : syracuseStep 950453 = 89105) (by norm_num)
theorem B557333 : Blo 163797 557333 := bbase (se 6 (by rfl) ⟨13062, by rfl⟩ : syracuseStep 557333 = 26125) (by norm_num)
theorem B393653 : Blo 163797 393653 := bbase (se 5 (by rfl) ⟨18452, by rfl⟩ : syracuseStep 393653 = 36905) (by norm_num)
theorem B262645 : Blo 163797 262645 := bbase (se 5 (by rfl) ⟨12311, by rfl⟩ : syracuseStep 262645 = 24623) (by norm_num)
theorem B623173 : Blo 163797 623173 := bbase (se 4 (by rfl) ⟨58422, by rfl⟩ : syracuseStep 623173 = 116845) (by norm_num)
theorem B557765 : Blo 163797 557765 := bbase (se 4 (by rfl) ⟨52290, by rfl⟩ : syracuseStep 557765 = 104581) (by norm_num)
theorem B1016597 : Blo 163797 1016597 := bbase (se 6 (by rfl) ⟨23826, by rfl⟩ : syracuseStep 1016597 = 47653) (by norm_num)
theorem B197417 : Blo 163797 197417 := bbase (se 2 (by rfl) ⟨74031, by rfl⟩ : syracuseStep 197417 = 148063) (by norm_num)
theorem B394037 : Blo 163797 394037 := bbase (se 5 (by rfl) ⟨18470, by rfl⟩ : syracuseStep 394037 = 36941) (by norm_num)
theorem B623477 : Blo 163797 623477 := bbase (se 5 (by rfl) ⟨29225, by rfl⟩ : syracuseStep 623477 = 58451) (by norm_num)
theorem B885653 : Blo 163797 885653 := bbase (se 6 (by rfl) ⟨20757, by rfl⟩ : syracuseStep 885653 = 41515) (by norm_num)
theorem B1344437 : Blo 163797 1344437 := bbase (se 5 (by rfl) ⟨63020, by rfl⟩ : syracuseStep 1344437 = 126041) (by norm_num)
theorem B263101 : Blo 163797 263101 := bbase (se 3 (by rfl) ⟨49331, by rfl⟩ : syracuseStep 263101 = 98663) (by norm_num)
theorem B394237 : Blo 163797 394237 := bbase (se 3 (by rfl) ⟨73919, by rfl⟩ : syracuseStep 394237 = 147839) (by norm_num)
theorem B197749 : Blo 163797 197749 := bbase (se 5 (by rfl) ⟨9269, by rfl⟩ : syracuseStep 197749 = 18539) (by norm_num)
theorem B558197 : Blo 163797 558197 := bbase (se 5 (by rfl) ⟨26165, by rfl⟩ : syracuseStep 558197 = 52331) (by norm_num)
theorem B361589 : Blo 163797 361589 := bbase (se 5 (by rfl) ⟨16949, by rfl⟩ : syracuseStep 361589 = 33899) (by norm_num)
theorem B787765 : Blo 163797 787765 := bbase (se 5 (by rfl) ⟨36926, by rfl⟩ : syracuseStep 787765 = 73853) (by norm_num)
theorem B755077 : Blo 163797 755077 := bbase (se 4 (by rfl) ⟨70788, by rfl⟩ : syracuseStep 755077 = 141577) (by norm_num)
theorem B558629 : Blo 163797 558629 := bbase (se 4 (by rfl) ⟨52371, by rfl⟩ : syracuseStep 558629 = 104743) (by norm_num)
theorem B263773 : Blo 163797 263773 := bbase (se 3 (by rfl) ⟨49457, by rfl⟩ : syracuseStep 263773 = 98915) (by norm_num)
theorem B296629 : Blo 163797 296629 := bbase (se 5 (by rfl) ⟨13904, by rfl⟩ : syracuseStep 296629 = 27809) (by norm_num)
theorem B198445 : Blo 163797 198445 := bbase (se 3 (by rfl) ⟨37208, by rfl⟩ : syracuseStep 198445 = 74417) (by norm_num)
theorem B296797 : Blo 163797 296797 := bbase (se 3 (by rfl) ⟨55649, by rfl⟩ : syracuseStep 296797 = 111299) (by norm_num)
theorem B198493 : Blo 163797 198493 := bbase (se 3 (by rfl) ⟨37217, by rfl⟩ : syracuseStep 198493 = 74435) (by norm_num)
theorem B526213 : Blo 163797 526213 := bbase (se 4 (by rfl) ⟨49332, by rfl⟩ : syracuseStep 526213 = 98665) (by norm_num)
theorem B427933 : Blo 163797 427933 := bbase (se 3 (by rfl) ⟨80237, by rfl⟩ : syracuseStep 427933 = 160475) (by norm_num)
theorem B427949 : Blo 163797 427949 := bbase (se 3 (by rfl) ⟨80240, by rfl⟩ : syracuseStep 427949 = 160481) (by norm_num)
theorem B559061 : Blo 163797 559061 := bbase (se 7 (by rfl) ⟨6551, by rfl⟩ : syracuseStep 559061 = 13103) (by norm_num)
theorem B264197 : Blo 163797 264197 := bbase (se 4 (by rfl) ⟨24768, by rfl⟩ : syracuseStep 264197 = 49537) (by norm_num)
theorem B166141 : Blo 163797 166141 := bbase (se 3 (by rfl) ⟨31151, by rfl⟩ : syracuseStep 166141 = 62303) (by norm_num)
theorem B264485 : Blo 163797 264485 := bbase (se 4 (by rfl) ⟨24795, by rfl⟩ : syracuseStep 264485 = 49591) (by norm_num)
theorem B559493 : Blo 163797 559493 := bbase (se 4 (by rfl) ⟨52452, by rfl⟩ : syracuseStep 559493 = 104905) (by norm_num)
theorem B297373 : Blo 163797 297373 := bbase (se 3 (by rfl) ⟨55757, by rfl⟩ : syracuseStep 297373 = 111515) (by norm_num)
theorem B395813 : Blo 163797 395813 := bbase (se 4 (by rfl) ⟨37107, by rfl⟩ : syracuseStep 395813 = 74215) (by norm_num)
theorem B1870613 : Blo 163797 1870613 := bbase (se 6 (by rfl) ⟨43842, by rfl⟩ : syracuseStep 1870613 = 87685) (by norm_num)
theorem B559925 : Blo 163797 559925 := bbase (se 5 (by rfl) ⟨26246, by rfl⟩ : syracuseStep 559925 = 52493) (by norm_num)
theorem B166757 : Blo 163797 166757 := bbase (se 4 (by rfl) ⟨15633, by rfl⟩ : syracuseStep 166757 = 31267) (by norm_num)
theorem B199541 : Blo 163797 199541 := bbase (se 5 (by rfl) ⟨9353, by rfl⟩ : syracuseStep 199541 = 18707) (by norm_num)
theorem B625589 : Blo 163797 625589 := bbase (se 5 (by rfl) ⟨29324, by rfl⟩ : syracuseStep 625589 = 58649) (by norm_num)
theorem B298013 : Blo 163797 298013 := bbase (se 3 (by rfl) ⟨55877, by rfl⟩ : syracuseStep 298013 = 111755) (by norm_num)
theorem B265285 : Blo 163797 265285 := bbase (se 4 (by rfl) ⟨24870, by rfl⟩ : syracuseStep 265285 = 49741) (by norm_num)
theorem B167017 : Blo 163797 167017 := bbase (se 2 (by rfl) ⟨62631, by rfl⟩ : syracuseStep 167017 = 125263) (by norm_num)
theorem B199849 : Blo 163797 199849 := bbase (se 2 (by rfl) ⟨74943, by rfl⟩ : syracuseStep 199849 = 149887) (by norm_num)
theorem B298181 : Blo 163797 298181 := bbase (se 4 (by rfl) ⟨27954, by rfl⟩ : syracuseStep 298181 = 55909) (by norm_num)
theorem B527573 : Blo 163797 527573 := bbase (se 7 (by rfl) ⟨6182, by rfl⟩ : syracuseStep 527573 = 12365) (by norm_num)
theorem B625877 : Blo 163797 625877 := bbase (se 7 (by rfl) ⟨7334, by rfl⟩ : syracuseStep 625877 = 14669) (by norm_num)
theorem B560357 : Blo 163797 560357 := bbase (se 4 (by rfl) ⟨52533, by rfl⟩ : syracuseStep 560357 = 105067) (by norm_num)
theorem B1248533 : Blo 163797 1248533 := bbase (se 6 (by rfl) ⟨29262, by rfl⟩ : syracuseStep 1248533 = 58525) (by norm_num)
theorem B593173 : Blo 163797 593173 := bbase (se 6 (by rfl) ⟨13902, by rfl⟩ : syracuseStep 593173 = 27805) (by norm_num)
theorem B200017 : Blo 163797 200017 := bbase (se 2 (by rfl) ⟨75006, by rfl⟩ : syracuseStep 200017 = 150013) (by norm_num)
theorem B200213 : Blo 163797 200213 := bbase (se 6 (by rfl) ⟨4692, by rfl⟩ : syracuseStep 200213 = 9385) (by norm_num)
theorem B265837 : Blo 163797 265837 := bbase (se 3 (by rfl) ⟨49844, by rfl⟩ : syracuseStep 265837 = 99689) (by norm_num)
theorem B1183349 : Blo 163797 1183349 := bbase (se 5 (by rfl) ⟨55469, by rfl⟩ : syracuseStep 1183349 = 110939) (by norm_num)
theorem B560789 : Blo 163797 560789 := bbase (se 6 (by rfl) ⟨13143, by rfl⟩ : syracuseStep 560789 = 26287) (by norm_num)
theorem B167617 : Blo 163797 167617 := bbase (se 2 (by rfl) ⟨62856, by rfl⟩ : syracuseStep 167617 = 125713) (by norm_num)
theorem B266093 : Blo 163797 266093 := bbase (se 3 (by rfl) ⟨49892, by rfl⟩ : syracuseStep 266093 = 99785) (by norm_num)
theorem B397237 : Blo 163797 397237 := bbase (se 5 (by rfl) ⟨18620, by rfl⟩ : syracuseStep 397237 = 37241) (by norm_num)
theorem B561221 : Blo 163797 561221 := bbase (se 4 (by rfl) ⟨52614, by rfl⟩ : syracuseStep 561221 = 105229) (by norm_num)
theorem B627061 : Blo 163797 627061 := bbase (se 5 (by rfl) ⟨29393, by rfl⟩ : syracuseStep 627061 = 58787) (by norm_num)
theorem B233941 : Blo 163797 233941 := bbase (se 7 (by rfl) ⟨2741, by rfl⟩ : syracuseStep 233941 = 5483) (by norm_num)
theorem B561653 : Blo 163797 561653 := bbase (se 5 (by rfl) ⟨26327, by rfl⟩ : syracuseStep 561653 = 52655) (by norm_num)
theorem B266797 : Blo 163797 266797 := bbase (se 3 (by rfl) ⟨50024, by rfl⟩ : syracuseStep 266797 = 100049) (by norm_num)
theorem B168517 : Blo 163797 168517 := bbase (se 4 (by rfl) ⟨15798, by rfl⟩ : syracuseStep 168517 = 31597) (by norm_num)
theorem B397909 : Blo 163797 397909 := bbase (se 8 (by rfl) ⟨2331, by rfl⟩ : syracuseStep 397909 = 4663) (by norm_num)
theorem B7246421 : Blo 163797 7246421 := bbase (se 8 (by rfl) ⟨42459, by rfl⟩ : syracuseStep 7246421 = 84919) (by norm_num)
theorem B627365 : Blo 163797 627365 := bbase (se 4 (by rfl) ⟨58815, by rfl⟩ : syracuseStep 627365 = 117631) (by norm_num)
theorem B1577717 : Blo 163797 1577717 := bbase (se 5 (by rfl) ⟨73955, by rfl⟩ : syracuseStep 1577717 = 147911) (by norm_num)
theorem B2036501 : Blo 163797 2036501 := bbase (se 6 (by rfl) ⟨47730, by rfl⟩ : syracuseStep 2036501 = 95461) (by norm_num)
theorem B398141 : Blo 163797 398141 := bbase (se 3 (by rfl) ⟨74651, by rfl⟩ : syracuseStep 398141 = 149303) (by norm_num)
theorem B398189 : Blo 163797 398189 := bbase (se 3 (by rfl) ⟨74660, by rfl⟩ : syracuseStep 398189 = 149321) (by norm_num)
theorem B562085 : Blo 163797 562085 := bbase (se 4 (by rfl) ⟨52695, by rfl⟩ : syracuseStep 562085 = 105391) (by norm_num)
theorem B267221 : Blo 163797 267221 := bbase (se 7 (by rfl) ⟨3131, by rfl⟩ : syracuseStep 267221 = 6263) (by norm_num)
theorem B300061 : Blo 163797 300061 := bbase (se 3 (by rfl) ⟨56261, by rfl⟩ : syracuseStep 300061 = 112523) (by norm_num)
theorem B234533 : Blo 163797 234533 := bbase (se 4 (by rfl) ⟨21987, by rfl⟩ : syracuseStep 234533 = 43975) (by norm_num)
theorem B234613 : Blo 163797 234613 := bbase (se 5 (by rfl) ⟨10997, by rfl⟩ : syracuseStep 234613 = 21995) (by norm_num)
theorem B234733 : Blo 163797 234733 := bbase (se 3 (by rfl) ⟨44012, by rfl⟩ : syracuseStep 234733 = 88025) (by norm_num)
theorem B300277 : Blo 163797 300277 := bbase (se 5 (by rfl) ⟨14075, by rfl⟩ : syracuseStep 300277 = 28151) (by norm_num)
theorem B267509 : Blo 163797 267509 := bbase (se 5 (by rfl) ⟨12539, by rfl⟩ : syracuseStep 267509 = 25079) (by norm_num)
theorem B234829 : Blo 163797 234829 := bbase (se 3 (by rfl) ⟨44030, by rfl⟩ : syracuseStep 234829 = 88061) (by norm_num)
theorem B562517 : Blo 163797 562517 := bbase (se 14 (by rfl) ⟨51, by rfl⟩ : syracuseStep 562517 = 103) (by norm_num)
theorem B333157 : Blo 163797 333157 := bbase (se 4 (by rfl) ⟨31233, by rfl⟩ : syracuseStep 333157 = 62467) (by norm_num)
theorem B267733 : Blo 163797 267733 := bbase (se 7 (by rfl) ⟨3137, by rfl⟩ : syracuseStep 267733 = 6275) (by norm_num)
theorem B955925 : Blo 163797 955925 := bbase (se 6 (by rfl) ⟨22404, by rfl⟩ : syracuseStep 955925 = 44809) (by norm_num)
theorem B169661 : Blo 163797 169661 := bbase (se 3 (by rfl) ⟨31811, by rfl⟩ : syracuseStep 169661 = 63623) (by norm_num)
theorem B562949 : Blo 163797 562949 := bbase (se 4 (by rfl) ⟨52776, by rfl⟩ : syracuseStep 562949 = 105553) (by norm_num)
theorem B235325 : Blo 163797 235325 := bbase (se 3 (by rfl) ⟨44123, by rfl⟩ : syracuseStep 235325 = 88247) (by norm_num)
theorem B366557 : Blo 163797 366557 := bbase (se 3 (by rfl) ⟨68729, by rfl⟩ : syracuseStep 366557 = 137459) (by norm_num)
theorem B301085 : Blo 163797 301085 := bbase (se 3 (by rfl) ⟨56453, by rfl⟩ : syracuseStep 301085 = 112907) (by norm_num)
theorem B170081 : Blo 163797 170081 := bbase (se 2 (by rfl) ⟨63780, by rfl⟩ : syracuseStep 170081 = 127561) (by norm_num)
theorem B563381 : Blo 163797 563381 := bbase (se 5 (by rfl) ⟨26408, by rfl⟩ : syracuseStep 563381 = 52817) (by norm_num)
theorem B5445845 : Blo 163797 5445845 := bbase (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) (by norm_num)
theorem B399581 : Blo 163797 399581 := bbase (se 3 (by rfl) ⟨74921, by rfl⟩ : syracuseStep 399581 = 149843) (by norm_num)
theorem B235877 : Blo 163797 235877 := bbase (se 4 (by rfl) ⟨22113, by rfl⟩ : syracuseStep 235877 = 44227) (by norm_num)
theorem B399773 : Blo 163797 399773 := bbase (se 3 (by rfl) ⟨74957, by rfl⟩ : syracuseStep 399773 = 149915) (by norm_num)
theorem B530981 : Blo 163797 530981 := bbase (se 4 (by rfl) ⟨49779, by rfl⟩ : syracuseStep 530981 = 99559) (by norm_num)
theorem B563813 : Blo 163797 563813 := bbase (se 4 (by rfl) ⟨52857, by rfl⟩ : syracuseStep 563813 = 105715) (by norm_num)
theorem B498325 : Blo 163797 498325 := bbase (se 6 (by rfl) ⟨11679, by rfl⟩ : syracuseStep 498325 = 23359) (by norm_num)
theorem B629477 : Blo 163797 629477 := bbase (se 4 (by rfl) ⟨59013, by rfl⟩ : syracuseStep 629477 = 118027) (by norm_num)
theorem B760661 : Blo 163797 760661 := bbase (se 9 (by rfl) ⟨2228, by rfl⟩ : syracuseStep 760661 = 4457) (by norm_num)
theorem B629765 : Blo 163797 629765 := bbase (se 4 (by rfl) ⟨59040, by rfl⟩ : syracuseStep 629765 = 118081) (by norm_num)
theorem B564245 : Blo 163797 564245 := bbase (se 6 (by rfl) ⟨13224, by rfl⟩ : syracuseStep 564245 = 26449) (by norm_num)
theorem B236629 : Blo 163797 236629 := bbase (se 8 (by rfl) ⟨1386, by rfl⟩ : syracuseStep 236629 = 2773) (by norm_num)
theorem B171433 : Blo 163797 171433 := bbase (se 2 (by rfl) ⟨64287, by rfl⟩ : syracuseStep 171433 = 128575) (by norm_num)
theorem B1416629 : Blo 163797 1416629 := bbase (se 5 (by rfl) ⟨66404, by rfl⟩ : syracuseStep 1416629 = 132809) (by norm_num)
theorem B564677 : Blo 163797 564677 := bbase (se 4 (by rfl) ⟨52938, by rfl⟩ : syracuseStep 564677 = 105877) (by norm_num)
theorem B466469 : Blo 163797 466469 := bbase (se 4 (by rfl) ⟨43731, by rfl⟩ : syracuseStep 466469 = 87463) (by norm_num)
theorem B597557 : Blo 163797 597557 := bbase (se 5 (by rfl) ⟨28010, by rfl⟩ : syracuseStep 597557 = 56021) (by norm_num)
theorem B859733 : Blo 163797 859733 := bbase (se 8 (by rfl) ⟨5037, by rfl⟩ : syracuseStep 859733 = 10075) (by norm_num)
theorem B335477 : Blo 163797 335477 := bbase (se 5 (by rfl) ⟨15725, by rfl⟩ : syracuseStep 335477 = 31451) (by norm_num)
theorem B532261 : Blo 163797 532261 := bbase (se 4 (by rfl) ⟨49899, by rfl⟩ : syracuseStep 532261 = 99799) (by norm_num)
theorem B237421 : Blo 163797 237421 := bbase (se 3 (by rfl) ⟨44516, by rfl⟩ : syracuseStep 237421 = 89033) (by norm_num)
theorem B565109 : Blo 163797 565109 := bbase (se 5 (by rfl) ⟨26489, by rfl⟩ : syracuseStep 565109 = 52979) (by norm_num)
theorem B434069 : Blo 163797 434069 := bbase (se 6 (by rfl) ⟨10173, by rfl⟩ : syracuseStep 434069 = 20347) (by norm_num)
theorem B368549 : Blo 163797 368549 := bbase (se 4 (by rfl) ⟨34551, by rfl⟩ : syracuseStep 368549 = 69103) (by norm_num)
theorem B794549 : Blo 163797 794549 := bbase (se 5 (by rfl) ⟨37244, by rfl⟩ : syracuseStep 794549 = 74489) (by norm_num)
theorem B368621 : Blo 163797 368621 := bbase (se 3 (by rfl) ⟨69116, by rfl⟩ : syracuseStep 368621 = 138233) (by norm_num)
theorem B1351669 : Blo 163797 1351669 := bbase (se 5 (by rfl) ⟨63359, by rfl⟩ : syracuseStep 1351669 = 126719) (by norm_num)
theorem B368693 : Blo 163797 368693 := bbase (se 5 (by rfl) ⟨17282, by rfl⟩ : syracuseStep 368693 = 34565) (by norm_num)
theorem B532565 : Blo 163797 532565 := bbase (se 8 (by rfl) ⟨3120, by rfl⟩ : syracuseStep 532565 = 6241) (by norm_num)
theorem B368765 : Blo 163797 368765 := bbase (se 3 (by rfl) ⟨69143, by rfl⟩ : syracuseStep 368765 = 138287) (by norm_num)
theorem B630949 : Blo 163797 630949 := bbase (se 4 (by rfl) ⟨59151, by rfl⟩ : syracuseStep 630949 = 118303) (by norm_num)
theorem B237757 : Blo 163797 237757 := bbase (se 3 (by rfl) ⟨44579, by rfl⟩ : syracuseStep 237757 = 89159) (by norm_num)
theorem B368837 : Blo 163797 368837 := bbase (se 4 (by rfl) ⟨34578, by rfl⟩ : syracuseStep 368837 = 69157) (by norm_num)
theorem B1646837 : Blo 163797 1646837 := bbase (se 5 (by rfl) ⟨77195, by rfl⟩ : syracuseStep 1646837 = 154391) (by norm_num)
theorem B368909 : Blo 163797 368909 := bbase (se 3 (by rfl) ⟨69170, by rfl⟩ : syracuseStep 368909 = 138341) (by norm_num)
theorem B467221 : Blo 163797 467221 := bbase (se 6 (by rfl) ⟨10950, by rfl⟩ : syracuseStep 467221 = 21901) (by norm_num)
theorem B565541 : Blo 163797 565541 := bbase (se 4 (by rfl) ⟨53019, by rfl⟩ : syracuseStep 565541 = 106039) (by norm_num)
theorem B368981 : Blo 163797 368981 := bbase (se 10 (by rfl) ⟨540, by rfl⟩ : syracuseStep 368981 = 1081) (by norm_num)
theorem B401773 : Blo 163797 401773 := bbase (se 3 (by rfl) ⟨75332, by rfl⟩ : syracuseStep 401773 = 150665) (by norm_num)
theorem B1057141 : Blo 163797 1057141 := bbase (se 5 (by rfl) ⟨49553, by rfl⟩ : syracuseStep 1057141 = 99107) (by norm_num)
theorem B237973 : Blo 163797 237973 := bbase (se 6 (by rfl) ⟨5577, by rfl⟩ : syracuseStep 237973 = 11155) (by norm_num)
theorem B369053 : Blo 163797 369053 := bbase (se 3 (by rfl) ⟨69197, by rfl⟩ : syracuseStep 369053 = 138395) (by norm_num)
theorem B631253 : Blo 163797 631253 := bbase (se 7 (by rfl) ⟨7397, by rfl⟩ : syracuseStep 631253 = 14795) (by norm_num)
theorem B369125 : Blo 163797 369125 := bbase (se 4 (by rfl) ⟨34605, by rfl⟩ : syracuseStep 369125 = 69211) (by norm_num)
theorem B369197 : Blo 163797 369197 := bbase (se 3 (by rfl) ⟨69224, by rfl⟩ : syracuseStep 369197 = 138449) (by norm_num)
theorem B369269 : Blo 163797 369269 := bbase (se 5 (by rfl) ⟨17309, by rfl⟩ : syracuseStep 369269 = 34619) (by norm_num)
theorem B565925 : Blo 163797 565925 := bbase (se 4 (by rfl) ⟨53055, by rfl⟩ : syracuseStep 565925 = 106111) (by norm_num)
theorem B369341 : Blo 163797 369341 := bbase (se 3 (by rfl) ⟨69251, by rfl⟩ : syracuseStep 369341 = 138503) (by norm_num)
theorem B565973 : Blo 163797 565973 := bbase (se 7 (by rfl) ⟨6632, by rfl⟩ : syracuseStep 565973 = 13265) (by norm_num)
theorem B402149 : Blo 163797 402149 := bbase (se 4 (by rfl) ⟨37701, by rfl⟩ : syracuseStep 402149 = 75403) (by norm_num)
theorem B369413 : Blo 163797 369413 := bbase (se 4 (by rfl) ⟨34632, by rfl⟩ : syracuseStep 369413 = 69265) (by norm_num)
theorem B238349 : Blo 163797 238349 := bbase (se 3 (by rfl) ⟨44690, by rfl⟩ : syracuseStep 238349 = 89381) (by norm_num)
theorem B402221 : Blo 163797 402221 := bbase (se 3 (by rfl) ⟨75416, by rfl⟩ : syracuseStep 402221 = 150833) (by norm_num)
theorem B369485 : Blo 163797 369485 := bbase (se 3 (by rfl) ⟨69278, by rfl⟩ : syracuseStep 369485 = 138557) (by norm_num)
theorem B369557 : Blo 163797 369557 := bbase (se 6 (by rfl) ⟨8661, by rfl⟩ : syracuseStep 369557 = 17323) (by norm_num)
theorem B402349 : Blo 163797 402349 := bbase (se 3 (by rfl) ⟨75440, by rfl⟩ : syracuseStep 402349 = 150881) (by norm_num)
theorem B369629 : Blo 163797 369629 := bbase (se 3 (by rfl) ⟨69305, by rfl⟩ : syracuseStep 369629 = 138611) (by norm_num)
theorem B762853 : Blo 163797 762853 := bbase (se 4 (by rfl) ⟨71517, by rfl⟩ : syracuseStep 762853 = 143035) (by norm_num)
theorem B369701 : Blo 163797 369701 := bbase (se 4 (by rfl) ⟨34659, by rfl⟩ : syracuseStep 369701 = 69319) (by norm_num)
theorem B369773 : Blo 163797 369773 := bbase (se 3 (by rfl) ⟨69332, by rfl⟩ : syracuseStep 369773 = 138665) (by norm_num)
theorem B533621 : Blo 163797 533621 := bbase (se 5 (by rfl) ⟨25013, by rfl⟩ : syracuseStep 533621 = 50027) (by norm_num)
theorem B369845 : Blo 163797 369845 := bbase (se 5 (by rfl) ⟨17336, by rfl⟩ : syracuseStep 369845 = 34673) (by norm_num)
theorem B533749 : Blo 163797 533749 := bbase (se 5 (by rfl) ⟨25019, by rfl⟩ : syracuseStep 533749 = 50039) (by norm_num)
theorem B402677 : Blo 163797 402677 := bbase (se 5 (by rfl) ⟨18875, by rfl⟩ : syracuseStep 402677 = 37751) (by norm_num)
theorem B369917 : Blo 163797 369917 := bbase (se 3 (by rfl) ⟨69359, by rfl⟩ : syracuseStep 369917 = 138719) (by norm_num)
theorem B402733 : Blo 163797 402733 := bbase (se 3 (by rfl) ⟨75512, by rfl⟩ : syracuseStep 402733 = 151025) (by norm_num)
theorem B369989 : Blo 163797 369989 := bbase (se 4 (by rfl) ⟨34686, by rfl⟩ : syracuseStep 369989 = 69373) (by norm_num)
theorem B763253 : Blo 163797 763253 := bbase (se 5 (by rfl) ⟨35777, by rfl⟩ : syracuseStep 763253 = 71555) (by norm_num)
theorem B370061 : Blo 163797 370061 := bbase (se 3 (by rfl) ⟨69386, by rfl⟩ : syracuseStep 370061 = 138773) (by norm_num)
theorem B370133 : Blo 163797 370133 := bbase (se 7 (by rfl) ⟨4337, by rfl⟩ : syracuseStep 370133 = 8675) (by norm_num)
theorem B534005 : Blo 163797 534005 := bbase (se 5 (by rfl) ⟨25031, by rfl⟩ : syracuseStep 534005 = 50063) (by norm_num)
theorem B763397 : Blo 163797 763397 := bbase (se 4 (by rfl) ⟨71568, by rfl⟩ : syracuseStep 763397 = 143137) (by norm_num)
theorem B402965 : Blo 163797 402965 := bbase (se 6 (by rfl) ⟨9444, by rfl⟩ : syracuseStep 402965 = 18889) (by norm_num)
theorem B370205 : Blo 163797 370205 := bbase (se 3 (by rfl) ⟨69413, by rfl⟩ : syracuseStep 370205 = 138827) (by norm_num)
theorem B370277 : Blo 163797 370277 := bbase (se 4 (by rfl) ⟨34713, by rfl⟩ : syracuseStep 370277 = 69427) (by norm_num)
theorem B370349 : Blo 163797 370349 := bbase (se 3 (by rfl) ⟨69440, by rfl⟩ : syracuseStep 370349 = 138881) (by norm_num)
theorem B403157 : Blo 163797 403157 := bbase (se 7 (by rfl) ⟨4724, by rfl⟩ : syracuseStep 403157 = 9449) (by norm_num)
theorem B370421 : Blo 163797 370421 := bbase (se 5 (by rfl) ⟨17363, by rfl⟩ : syracuseStep 370421 = 34727) (by norm_num)
theorem B370493 : Blo 163797 370493 := bbase (se 3 (by rfl) ⟨69467, by rfl⟩ : syracuseStep 370493 = 138935) (by norm_num)
theorem B370565 : Blo 163797 370565 := bbase (se 4 (by rfl) ⟨34740, by rfl⟩ : syracuseStep 370565 = 69481) (by norm_num)
theorem B370637 : Blo 163797 370637 := bbase (se 3 (by rfl) ⟨69494, by rfl⟩ : syracuseStep 370637 = 138989) (by norm_num)
theorem B370709 : Blo 163797 370709 := bbase (se 6 (by rfl) ⟨8688, by rfl⟩ : syracuseStep 370709 = 17377) (by norm_num)
theorem B370781 : Blo 163797 370781 := bbase (se 3 (by rfl) ⟨69521, by rfl⟩ : syracuseStep 370781 = 139043) (by norm_num)
theorem B665765 : Blo 163797 665765 := bbase (se 4 (by rfl) ⟨62415, by rfl⟩ : syracuseStep 665765 = 124831) (by norm_num)
theorem B370853 : Blo 163797 370853 := bbase (se 4 (by rfl) ⟨34767, by rfl⟩ : syracuseStep 370853 = 69535) (by norm_num)
theorem B370925 : Blo 163797 370925 := bbase (se 3 (by rfl) ⟨69548, by rfl⟩ : syracuseStep 370925 = 139097) (by norm_num)
theorem B239893 : Blo 163797 239893 := bbase (se 6 (by rfl) ⟨5622, by rfl⟩ : syracuseStep 239893 = 11245) (by norm_num)
theorem B370997 : Blo 163797 370997 := bbase (se 5 (by rfl) ⟨17390, by rfl⟩ : syracuseStep 370997 = 34781) (by norm_num)
theorem B1419605 : Blo 163797 1419605 := bbase (se 10 (by rfl) ⟨2079, by rfl⟩ : syracuseStep 1419605 = 4159) (by norm_num)
theorem B371069 : Blo 163797 371069 := bbase (se 3 (by rfl) ⟨69575, by rfl⟩ : syracuseStep 371069 = 139151) (by norm_num)
theorem B371141 : Blo 163797 371141 := bbase (se 4 (by rfl) ⟨34794, by rfl⟩ : syracuseStep 371141 = 69589) (by norm_num)
theorem B829925 : Blo 163797 829925 := bbase (se 4 (by rfl) ⟨77805, by rfl⟩ : syracuseStep 829925 = 155611) (by norm_num)
theorem B371213 : Blo 163797 371213 := bbase (se 3 (by rfl) ⟨69602, by rfl⟩ : syracuseStep 371213 = 139205) (by norm_num)
theorem B633365 : Blo 163797 633365 := bbase (se 6 (by rfl) ⟨14844, by rfl⟩ : syracuseStep 633365 = 29689) (by norm_num)
theorem B371285 : Blo 163797 371285 := bbase (se 8 (by rfl) ⟨2175, by rfl⟩ : syracuseStep 371285 = 4351) (by norm_num)
theorem B207461 : Blo 163797 207461 := bbase (se 4 (by rfl) ⟨19449, by rfl⟩ : syracuseStep 207461 = 38899) (by norm_num)
theorem B207517 : Blo 163797 207517 := bbase (se 3 (by rfl) ⟨38909, by rfl⟩ : syracuseStep 207517 = 77819) (by norm_num)
theorem B371357 : Blo 163797 371357 := bbase (se 3 (by rfl) ⟨69629, by rfl⟩ : syracuseStep 371357 = 139259) (by norm_num)
theorem B371429 : Blo 163797 371429 := bbase (se 4 (by rfl) ⟨34821, by rfl⟩ : syracuseStep 371429 = 69643) (by norm_num)
theorem B207613 : Blo 163797 207613 := bbase (se 3 (by rfl) ⟨38927, by rfl⟩ : syracuseStep 207613 = 77855) (by norm_num)
theorem B371501 : Blo 163797 371501 := bbase (se 3 (by rfl) ⟨69656, by rfl⟩ : syracuseStep 371501 = 139313) (by norm_num)
theorem B633653 : Blo 163797 633653 := bbase (se 5 (by rfl) ⟨29702, by rfl⟩ : syracuseStep 633653 = 59405) (by norm_num)
theorem B371573 : Blo 163797 371573 := bbase (se 5 (by rfl) ⟨17417, by rfl⟩ : syracuseStep 371573 = 34835) (by norm_num)
theorem B1256309 : Blo 163797 1256309 := bbase (se 5 (by rfl) ⟨58889, by rfl⟩ : syracuseStep 1256309 = 117779) (by norm_num)
theorem B207785 : Blo 163797 207785 := bbase (se 2 (by rfl) ⟨77919, by rfl⟩ : syracuseStep 207785 = 155839) (by norm_num)
theorem B371645 : Blo 163797 371645 := bbase (se 3 (by rfl) ⟨69683, by rfl⟩ : syracuseStep 371645 = 139367) (by norm_num)
theorem B207841 : Blo 163797 207841 := bbase (se 2 (by rfl) ⟨77940, by rfl⟩ : syracuseStep 207841 = 155881) (by norm_num)
theorem B371717 : Blo 163797 371717 := bbase (se 4 (by rfl) ⟨34848, by rfl⟩ : syracuseStep 371717 = 69697) (by norm_num)
theorem B797701 : Blo 163797 797701 := bbase (se 4 (by rfl) ⟨74784, by rfl⟩ : syracuseStep 797701 = 149569) (by norm_num)
theorem B470069 : Blo 163797 470069 := bbase (se 5 (by rfl) ⟨22034, by rfl⟩ : syracuseStep 470069 = 44069) (by norm_num)
theorem B175165 : Blo 163797 175165 := bbase (se 3 (by rfl) ⟨32843, by rfl⟩ : syracuseStep 175165 = 65687) (by norm_num)
theorem B339005 : Blo 163797 339005 := bbase (se 3 (by rfl) ⟨63563, by rfl⟩ : syracuseStep 339005 = 127127) (by norm_num)
theorem B207937 : Blo 163797 207937 := bbase (se 2 (by rfl) ⟨77976, by rfl⟩ : syracuseStep 207937 = 155953) (by norm_num)
theorem B371789 : Blo 163797 371789 := bbase (se 3 (by rfl) ⟨69710, by rfl⟩ : syracuseStep 371789 = 139421) (by norm_num)
theorem B371861 : Blo 163797 371861 := bbase (se 6 (by rfl) ⟨8715, by rfl⟩ : syracuseStep 371861 = 17431) (by norm_num)
theorem B339109 : Blo 163797 339109 := bbase (se 4 (by rfl) ⟨31791, by rfl⟩ : syracuseStep 339109 = 63583) (by norm_num)
theorem B175285 : Blo 163797 175285 := bbase (se 5 (by rfl) ⟨8216, by rfl⟩ : syracuseStep 175285 = 16433) (by norm_num)
theorem B371933 : Blo 163797 371933 := bbase (se 3 (by rfl) ⟨69737, by rfl⟩ : syracuseStep 371933 = 139475) (by norm_num)
theorem B208109 : Blo 163797 208109 := bbase (se 3 (by rfl) ⟨39020, by rfl⟩ : syracuseStep 208109 = 78041) (by norm_num)
theorem B208165 : Blo 163797 208165 := bbase (se 4 (by rfl) ⟨19515, by rfl⟩ : syracuseStep 208165 = 39031) (by norm_num)
theorem B372005 : Blo 163797 372005 := bbase (se 4 (by rfl) ⟨34875, by rfl⟩ : syracuseStep 372005 = 69751) (by norm_num)
theorem B372077 : Blo 163797 372077 := bbase (se 3 (by rfl) ⟨69764, by rfl⟩ : syracuseStep 372077 = 139529) (by norm_num)
theorem B208261 : Blo 163797 208261 := bbase (se 4 (by rfl) ⟨19524, by rfl⟩ : syracuseStep 208261 = 39049) (by norm_num)
theorem B175537 : Blo 163797 175537 := bbase (se 2 (by rfl) ⟨65826, by rfl⟩ : syracuseStep 175537 = 131653) (by norm_num)
theorem B175541 : Blo 163797 175541 := bbase (se 5 (by rfl) ⟨8228, by rfl⟩ : syracuseStep 175541 = 16457) (by norm_num)
theorem B372149 : Blo 163797 372149 := bbase (se 5 (by rfl) ⟨17444, by rfl⟩ : syracuseStep 372149 = 34889) (by norm_num)
theorem B372221 : Blo 163797 372221 := bbase (se 3 (by rfl) ⟨69791, by rfl⟩ : syracuseStep 372221 = 139583) (by norm_num)
theorem B208433 : Blo 163797 208433 := bbase (se 2 (by rfl) ⟨78162, by rfl⟩ : syracuseStep 208433 = 156325) (by norm_num)
theorem B372293 : Blo 163797 372293 := bbase (se 4 (by rfl) ⟨34902, by rfl⟩ : syracuseStep 372293 = 69805) (by norm_num)
theorem B536149 : Blo 163797 536149 := bbase (se 8 (by rfl) ⟨3141, by rfl⟩ : syracuseStep 536149 = 6283) (by norm_num)
theorem B208489 : Blo 163797 208489 := bbase (se 2 (by rfl) ⟨78183, by rfl⟩ : syracuseStep 208489 = 156367) (by norm_num)
theorem B372365 : Blo 163797 372365 := bbase (se 3 (by rfl) ⟨69818, by rfl⟩ : syracuseStep 372365 = 139637) (by norm_num)
theorem B208585 : Blo 163797 208585 := bbase (se 2 (by rfl) ⟨78219, by rfl⟩ : syracuseStep 208585 = 156439) (by norm_num)
theorem B372437 : Blo 163797 372437 := bbase (se 7 (by rfl) ⟨4364, by rfl⟩ : syracuseStep 372437 = 8729) (by norm_num)
theorem B569045 : Blo 163797 569045 := bbase (se 7 (by rfl) ⟨6668, by rfl⟩ : syracuseStep 569045 = 13337) (by norm_num)
theorem B831221 : Blo 163797 831221 := bbase (se 5 (by rfl) ⟨38963, by rfl⟩ : syracuseStep 831221 = 77927) (by norm_num)
theorem B372509 : Blo 163797 372509 := bbase (se 3 (by rfl) ⟨69845, by rfl⟩ : syracuseStep 372509 = 139691) (by norm_num)
theorem B372581 : Blo 163797 372581 := bbase (se 4 (by rfl) ⟨34929, by rfl⟩ : syracuseStep 372581 = 69859) (by norm_num)
theorem B208757 : Blo 163797 208757 := bbase (se 5 (by rfl) ⟨9785, by rfl⟩ : syracuseStep 208757 = 19571) (by norm_num)
theorem B536453 : Blo 163797 536453 := bbase (se 4 (by rfl) ⟨50292, by rfl⟩ : syracuseStep 536453 = 100585) (by norm_num)
theorem B208813 : Blo 163797 208813 := bbase (se 3 (by rfl) ⟨39152, by rfl⟩ : syracuseStep 208813 = 78305) (by norm_num)
theorem B372653 : Blo 163797 372653 := bbase (se 3 (by rfl) ⟨69872, by rfl⟩ : syracuseStep 372653 = 139745) (by norm_num)
theorem B634837 : Blo 163797 634837 := bbase (se 7 (by rfl) ⟨7439, by rfl⟩ : syracuseStep 634837 = 14879) (by norm_num)
theorem B176105 : Blo 163797 176105 := bbase (se 2 (by rfl) ⟨66039, by rfl⟩ : syracuseStep 176105 = 132079) (by norm_num)
theorem B372725 : Blo 163797 372725 := bbase (se 5 (by rfl) ⟨17471, by rfl⟩ : syracuseStep 372725 = 34943) (by norm_num)
theorem B208909 : Blo 163797 208909 := bbase (se 3 (by rfl) ⟨39170, by rfl⟩ : syracuseStep 208909 = 78341) (by norm_num)
theorem B372797 : Blo 163797 372797 := bbase (se 3 (by rfl) ⟨69899, by rfl⟩ : syracuseStep 372797 = 139799) (by norm_num)
theorem B3223637 : Blo 163797 3223637 := bbase (se 8 (by rfl) ⟨18888, by rfl⟩ : syracuseStep 3223637 = 37777) (by norm_num)
theorem B372869 : Blo 163797 372869 := bbase (se 4 (by rfl) ⟨34956, by rfl⟩ : syracuseStep 372869 = 69913) (by norm_num)
theorem B176293 : Blo 163797 176293 := bbase (se 4 (by rfl) ⟨16527, by rfl⟩ : syracuseStep 176293 = 33055) (by norm_num)
theorem B209081 : Blo 163797 209081 := bbase (se 2 (by rfl) ⟨78405, by rfl⟩ : syracuseStep 209081 = 156811) (by norm_num)
theorem B372941 : Blo 163797 372941 := bbase (se 3 (by rfl) ⟨69926, by rfl⟩ : syracuseStep 372941 = 139853) (by norm_num)
theorem B471253 : Blo 163797 471253 := bbase (se 7 (by rfl) ⟨5522, by rfl⟩ : syracuseStep 471253 = 11045) (by norm_num)
theorem B209137 : Blo 163797 209137 := bbase (se 2 (by rfl) ⟨78426, by rfl⟩ : syracuseStep 209137 = 156853) (by norm_num)
theorem B635141 : Blo 163797 635141 := bbase (se 4 (by rfl) ⟨59544, by rfl⟩ : syracuseStep 635141 = 119089) (by norm_num)
theorem B373013 : Blo 163797 373013 := bbase (se 6 (by rfl) ⟨8742, by rfl⟩ : syracuseStep 373013 = 17485) (by norm_num)
theorem B209233 : Blo 163797 209233 := bbase (se 2 (by rfl) ⟨78462, by rfl⟩ : syracuseStep 209233 = 156925) (by norm_num)
theorem B373085 : Blo 163797 373085 := bbase (se 3 (by rfl) ⟨69953, by rfl⟩ : syracuseStep 373085 = 139907) (by norm_num)
theorem B471413 : Blo 163797 471413 := bbase (se 5 (by rfl) ⟨22097, by rfl⟩ : syracuseStep 471413 = 44195) (by norm_num)
theorem B373157 : Blo 163797 373157 := bbase (se 4 (by rfl) ⟨34983, by rfl⟩ : syracuseStep 373157 = 69967) (by norm_num)
theorem B373229 : Blo 163797 373229 := bbase (se 3 (by rfl) ⟨69980, by rfl⟩ : syracuseStep 373229 = 139961) (by norm_num)
theorem B209405 : Blo 163797 209405 := bbase (se 3 (by rfl) ⟨39263, by rfl⟩ : syracuseStep 209405 = 78527) (by norm_num)
theorem B209461 : Blo 163797 209461 := bbase (se 5 (by rfl) ⟨9818, by rfl⟩ : syracuseStep 209461 = 19637) (by norm_num)
theorem B373301 : Blo 163797 373301 := bbase (se 5 (by rfl) ⟨17498, by rfl⟩ : syracuseStep 373301 = 34997) (by norm_num)
theorem B471653 : Blo 163797 471653 := bbase (se 4 (by rfl) ⟨44217, by rfl⟩ : syracuseStep 471653 = 88435) (by norm_num)
theorem B373373 : Blo 163797 373373 := bbase (se 3 (by rfl) ⟨70007, by rfl⟩ : syracuseStep 373373 = 140015) (by norm_num)
theorem B209557 : Blo 163797 209557 := bbase (se 6 (by rfl) ⟨4911, by rfl⟩ : syracuseStep 209557 = 9823) (by norm_num)
theorem B373445 : Blo 163797 373445 := bbase (se 4 (by rfl) ⟨35010, by rfl⟩ : syracuseStep 373445 = 70021) (by norm_num)
theorem B373517 : Blo 163797 373517 := bbase (se 3 (by rfl) ⟨70034, by rfl⟩ : syracuseStep 373517 = 140069) (by norm_num)
theorem B471845 : Blo 163797 471845 := bbase (se 4 (by rfl) ⟨44235, by rfl⟩ : syracuseStep 471845 = 88471) (by norm_num)
theorem B209729 : Blo 163797 209729 := bbase (se 2 (by rfl) ⟨78648, by rfl⟩ : syracuseStep 209729 = 157297) (by norm_num)
theorem B373589 : Blo 163797 373589 := bbase (se 9 (by rfl) ⟨1094, by rfl⟩ : syracuseStep 373589 = 2189) (by norm_num)
theorem B209785 : Blo 163797 209785 := bbase (se 2 (by rfl) ⟨78669, by rfl⟩ : syracuseStep 209785 = 157339) (by norm_num)
theorem B373661 : Blo 163797 373661 := bbase (se 3 (by rfl) ⟨70061, by rfl⟩ : syracuseStep 373661 = 140123) (by norm_num)
theorem B209881 : Blo 163797 209881 := bbase (se 2 (by rfl) ⟨78705, by rfl⟩ : syracuseStep 209881 = 157411) (by norm_num)
theorem B177113 : Blo 163797 177113 := bbase (se 2 (by rfl) ⟨66417, by rfl⟩ : syracuseStep 177113 = 132835) (by norm_num)
theorem B373733 : Blo 163797 373733 := bbase (se 4 (by rfl) ⟨35037, by rfl⟩ : syracuseStep 373733 = 70075) (by norm_num)
theorem B832517 : Blo 163797 832517 := bbase (se 4 (by rfl) ⟨78048, by rfl⟩ : syracuseStep 832517 = 156097) (by norm_num)
theorem B373781 : Blo 163797 373781 := bbase (se 6 (by rfl) ⟨8760, by rfl⟩ : syracuseStep 373781 = 17521) (by norm_num)
theorem B766997 : Blo 163797 766997 := bbase (se 6 (by rfl) ⟨17976, by rfl⟩ : syracuseStep 766997 = 35953) (by norm_num)
theorem B373805 : Blo 163797 373805 := bbase (se 3 (by rfl) ⟨70088, by rfl⟩ : syracuseStep 373805 = 140177) (by norm_num)
theorem B373837 : Blo 163797 373837 := bbase (se 3 (by rfl) ⟨70094, by rfl⟩ : syracuseStep 373837 = 140189) (by norm_num)
theorem B373877 : Blo 163797 373877 := bbase (se 5 (by rfl) ⟨17525, by rfl⟩ : syracuseStep 373877 = 35051) (by norm_num)
theorem B210053 : Blo 163797 210053 := bbase (se 4 (by rfl) ⟨19692, by rfl⟩ : syracuseStep 210053 = 39385) (by norm_num)
theorem B373909 : Blo 163797 373909 := bbase (se 6 (by rfl) ⟨8763, by rfl⟩ : syracuseStep 373909 = 17527) (by norm_num)
theorem B210109 : Blo 163797 210109 := bbase (se 3 (by rfl) ⟨39395, by rfl⟩ : syracuseStep 210109 = 78791) (by norm_num)
theorem B373949 : Blo 163797 373949 := bbase (se 3 (by rfl) ⟨70115, by rfl⟩ : syracuseStep 373949 = 140231) (by norm_num)
theorem B374021 : Blo 163797 374021 := bbase (se 4 (by rfl) ⟨35064, by rfl⟩ : syracuseStep 374021 = 70129) (by norm_num)
theorem B210205 : Blo 163797 210205 := bbase (se 3 (by rfl) ⟨39413, by rfl⟩ : syracuseStep 210205 = 78827) (by norm_num)
theorem B374093 : Blo 163797 374093 := bbase (se 3 (by rfl) ⟨70142, by rfl⟩ : syracuseStep 374093 = 140285) (by norm_num)
theorem B177557 : Blo 163797 177557 := bbase (se 6 (by rfl) ⟨4161, by rfl⟩ : syracuseStep 177557 = 8323) (by norm_num)
theorem B374165 : Blo 163797 374165 := bbase (se 6 (by rfl) ⟨8769, by rfl⟩ : syracuseStep 374165 = 17539) (by norm_num)
theorem B210377 : Blo 163797 210377 := bbase (se 2 (by rfl) ⟨78891, by rfl⟩ : syracuseStep 210377 = 157783) (by norm_num)
theorem B374237 : Blo 163797 374237 := bbase (se 3 (by rfl) ⟨70169, by rfl⟩ : syracuseStep 374237 = 140339) (by norm_num)
theorem B210433 : Blo 163797 210433 := bbase (se 2 (by rfl) ⟨78912, by rfl⟩ : syracuseStep 210433 = 157825) (by norm_num)
theorem B374309 : Blo 163797 374309 := bbase (se 4 (by rfl) ⟨35091, by rfl⟩ : syracuseStep 374309 = 70183) (by norm_num)
theorem B210529 : Blo 163797 210529 := bbase (se 2 (by rfl) ⟨78948, by rfl⟩ : syracuseStep 210529 = 157897) (by norm_num)
theorem B374381 : Blo 163797 374381 := bbase (se 3 (by rfl) ⟨70196, by rfl⟩ : syracuseStep 374381 = 140393) (by norm_num)
theorem B177805 : Blo 163797 177805 := bbase (se 3 (by rfl) ⟨33338, by rfl⟩ : syracuseStep 177805 = 66677) (by norm_num)
theorem B177833 : Blo 163797 177833 := bbase (se 2 (by rfl) ⟨66687, by rfl⟩ : syracuseStep 177833 = 133375) (by norm_num)
theorem B374453 : Blo 163797 374453 := bbase (se 5 (by rfl) ⟨17552, by rfl⟩ : syracuseStep 374453 = 35105) (by norm_num)
theorem B669397 : Blo 163797 669397 := bbase (se 7 (by rfl) ⟨7844, by rfl⟩ : syracuseStep 669397 = 15689) (by norm_num)
theorem B341741 : Blo 163797 341741 := bbase (se 3 (by rfl) ⟨64076, by rfl⟩ : syracuseStep 341741 = 128153) (by norm_num)
theorem B374525 : Blo 163797 374525 := bbase (se 3 (by rfl) ⟨70223, by rfl⟩ : syracuseStep 374525 = 140447) (by norm_num)
theorem B472837 : Blo 163797 472837 := bbase (se 4 (by rfl) ⟨44328, by rfl⟩ : syracuseStep 472837 = 88657) (by norm_num)
theorem B210701 : Blo 163797 210701 := bbase (se 3 (by rfl) ⟨39506, by rfl⟩ : syracuseStep 210701 = 79013) (by norm_num)
theorem B374597 : Blo 163797 374597 := bbase (se 4 (by rfl) ⟨35118, by rfl⟩ : syracuseStep 374597 = 70237) (by norm_num)
theorem B210757 : Blo 163797 210757 := bbase (se 4 (by rfl) ⟨19758, by rfl⟩ : syracuseStep 210757 = 39517) (by norm_num)
theorem B374669 : Blo 163797 374669 := bbase (se 3 (by rfl) ⟨70250, by rfl⟩ : syracuseStep 374669 = 140501) (by norm_num)
theorem B210853 : Blo 163797 210853 := bbase (se 4 (by rfl) ⟨19767, by rfl⟩ : syracuseStep 210853 = 39535) (by norm_num)
theorem B374741 : Blo 163797 374741 := bbase (se 7 (by rfl) ⟨4391, by rfl⟩ : syracuseStep 374741 = 8783) (by norm_num)
theorem B276493 : Blo 163797 276493 := bbase (se 3 (by rfl) ⟨51842, by rfl⟩ : syracuseStep 276493 = 103685) (by norm_num)
theorem B374813 : Blo 163797 374813 := bbase (se 3 (by rfl) ⟨70277, by rfl⟩ : syracuseStep 374813 = 140555) (by norm_num)
theorem B178237 : Blo 163797 178237 := bbase (se 3 (by rfl) ⟨33419, by rfl⟩ : syracuseStep 178237 = 66839) (by norm_num)
theorem B800837 : Blo 163797 800837 := bbase (se 4 (by rfl) ⟨75078, by rfl⟩ : syracuseStep 800837 = 150157) (by norm_num)
theorem B211025 : Blo 163797 211025 := bbase (se 2 (by rfl) ⟨79134, by rfl⟩ : syracuseStep 211025 = 158269) (by norm_num)
theorem B276581 : Blo 163797 276581 := bbase (se 4 (by rfl) ⟨25929, by rfl⟩ : syracuseStep 276581 = 51859) (by norm_num)
theorem B374885 : Blo 163797 374885 := bbase (se 4 (by rfl) ⟨35145, by rfl⟩ : syracuseStep 374885 = 70291) (by norm_num)
theorem B178309 : Blo 163797 178309 := bbase (se 4 (by rfl) ⟨16716, by rfl⟩ : syracuseStep 178309 = 33433) (by norm_num)
theorem B211081 : Blo 163797 211081 := bbase (se 2 (by rfl) ⟨79155, by rfl⟩ : syracuseStep 211081 = 158311) (by norm_num)
theorem B374957 : Blo 163797 374957 := bbase (se 3 (by rfl) ⟨70304, by rfl⟩ : syracuseStep 374957 = 140609) (by norm_num)
theorem B276709 : Blo 163797 276709 := bbase (se 4 (by rfl) ⟨25941, by rfl⟩ : syracuseStep 276709 = 51883) (by norm_num)
theorem B211177 : Blo 163797 211177 := bbase (se 2 (by rfl) ⟨79191, by rfl⟩ : syracuseStep 211177 = 158383) (by norm_num)
theorem B375029 : Blo 163797 375029 := bbase (se 5 (by rfl) ⟨17579, by rfl⟩ : syracuseStep 375029 = 35159) (by norm_num)
theorem B833813 : Blo 163797 833813 := bbase (se 6 (by rfl) ⟨19542, by rfl⟩ : syracuseStep 833813 = 39085) (by norm_num)
theorem B899381 : Blo 163797 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B276797 : Blo 163797 276797 := bbase (se 3 (by rfl) ⟨51899, by rfl⟩ : syracuseStep 276797 = 103799) (by norm_num)
theorem B375101 : Blo 163797 375101 := bbase (se 3 (by rfl) ⟨70331, by rfl⟩ : syracuseStep 375101 = 140663) (by norm_num)
theorem B375173 : Blo 163797 375173 := bbase (se 4 (by rfl) ⟨35172, by rfl⟩ : syracuseStep 375173 = 70345) (by norm_num)
theorem B211349 : Blo 163797 211349 := bbase (se 6 (by rfl) ⟨4953, by rfl⟩ : syracuseStep 211349 = 9907) (by norm_num)
theorem B276925 : Blo 163797 276925 := bbase (se 3 (by rfl) ⟨51923, by rfl⟩ : syracuseStep 276925 = 103847) (by norm_num)
theorem B702917 : Blo 163797 702917 := bbase (se 4 (by rfl) ⟨65898, by rfl⟩ : syracuseStep 702917 = 131797) (by norm_num)
theorem B375245 : Blo 163797 375245 := bbase (se 3 (by rfl) ⟨70358, by rfl⟩ : syracuseStep 375245 = 140717) (by norm_num)
theorem B211405 : Blo 163797 211405 := bbase (se 3 (by rfl) ⟨39638, by rfl⟩ : syracuseStep 211405 = 79277) (by norm_num)
theorem B178681 : Blo 163797 178681 := bbase (se 2 (by rfl) ⟨67005, by rfl⟩ : syracuseStep 178681 = 134011) (by norm_num)
theorem B277013 : Blo 163797 277013 := bbase (se 6 (by rfl) ⟨6492, by rfl⟩ : syracuseStep 277013 = 12985) (by norm_num)
theorem B375317 : Blo 163797 375317 := bbase (se 6 (by rfl) ⟨8796, by rfl⟩ : syracuseStep 375317 = 17593) (by norm_num)
theorem B211501 : Blo 163797 211501 := bbase (se 3 (by rfl) ⟨39656, by rfl⟩ : syracuseStep 211501 = 79313) (by norm_num)
theorem B375389 : Blo 163797 375389 := bbase (se 3 (by rfl) ⟨70385, by rfl⟩ : syracuseStep 375389 = 140771) (by norm_num)
theorem B277141 : Blo 163797 277141 := bbase (se 6 (by rfl) ⟨6495, by rfl⟩ : syracuseStep 277141 = 12991) (by norm_num)
theorem B375461 : Blo 163797 375461 := bbase (se 4 (by rfl) ⟨35199, by rfl⟩ : syracuseStep 375461 = 70399) (by norm_num)
theorem B211673 : Blo 163797 211673 := bbase (se 2 (by rfl) ⟨79377, by rfl⟩ : syracuseStep 211673 = 158755) (by norm_num)
theorem B277229 : Blo 163797 277229 := bbase (se 3 (by rfl) ⟨51980, by rfl⟩ : syracuseStep 277229 = 103961) (by norm_num)
theorem B375533 : Blo 163797 375533 := bbase (se 3 (by rfl) ⟨70412, by rfl⟩ : syracuseStep 375533 = 140825) (by norm_num)
theorem B211729 : Blo 163797 211729 := bbase (se 2 (by rfl) ⟨79398, by rfl⟩ : syracuseStep 211729 = 158797) (by norm_num)
theorem B375605 : Blo 163797 375605 := bbase (se 5 (by rfl) ⟨17606, by rfl⟩ : syracuseStep 375605 = 35213) (by norm_num)
theorem B473941 : Blo 163797 473941 := bbase (se 9 (by rfl) ⟨1388, by rfl⟩ : syracuseStep 473941 = 2777) (by norm_num)
theorem B277357 : Blo 163797 277357 := bbase (se 3 (by rfl) ⟨52004, by rfl⟩ : syracuseStep 277357 = 104009) (by norm_num)
theorem B211825 : Blo 163797 211825 := bbase (se 2 (by rfl) ⟨79434, by rfl⟩ : syracuseStep 211825 = 158869) (by norm_num)
theorem B179057 : Blo 163797 179057 := bbase (se 2 (by rfl) ⟨67146, by rfl⟩ : syracuseStep 179057 = 134293) (by norm_num)
theorem B375677 : Blo 163797 375677 := bbase (se 3 (by rfl) ⟨70439, by rfl⟩ : syracuseStep 375677 = 140879) (by norm_num)
theorem B179129 : Blo 163797 179129 := bbase (se 2 (by rfl) ⟨67173, by rfl⟩ : syracuseStep 179129 = 134347) (by norm_num)
theorem B277445 : Blo 163797 277445 := bbase (se 4 (by rfl) ⟨26010, by rfl⟩ : syracuseStep 277445 = 52021) (by norm_num)
theorem B375749 : Blo 163797 375749 := bbase (se 4 (by rfl) ⟨35226, by rfl⟩ : syracuseStep 375749 = 70453) (by norm_num)
theorem B1391573 : Blo 163797 1391573 := bbase (se 7 (by rfl) ⟨16307, by rfl⟩ : syracuseStep 1391573 = 32615) (by norm_num)
theorem B375821 : Blo 163797 375821 := bbase (se 3 (by rfl) ⟨70466, by rfl⟩ : syracuseStep 375821 = 140933) (by norm_num)
theorem B211997 : Blo 163797 211997 := bbase (se 3 (by rfl) ⟨39749, by rfl⟩ : syracuseStep 211997 = 79499) (by norm_num)
theorem B277573 : Blo 163797 277573 := bbase (se 4 (by rfl) ⟨26022, by rfl⟩ : syracuseStep 277573 = 52045) (by norm_num)
theorem B375893 : Blo 163797 375893 := bbase (se 8 (by rfl) ⟨2202, by rfl⟩ : syracuseStep 375893 = 4405) (by norm_num)
theorem B212053 : Blo 163797 212053 := bbase (se 8 (by rfl) ⟨1242, by rfl⟩ : syracuseStep 212053 = 2485) (by norm_num)
theorem B277661 : Blo 163797 277661 := bbase (se 3 (by rfl) ⟨52061, by rfl⟩ : syracuseStep 277661 = 104123) (by norm_num)
theorem B375965 : Blo 163797 375965 := bbase (se 3 (by rfl) ⟨70493, by rfl⟩ : syracuseStep 375965 = 140987) (by norm_num)
theorem B212149 : Blo 163797 212149 := bbase (se 5 (by rfl) ⟨9944, by rfl⟩ : syracuseStep 212149 = 19889) (by norm_num)
theorem B376037 : Blo 163797 376037 := bbase (se 4 (by rfl) ⟨35253, by rfl⟩ : syracuseStep 376037 = 70507) (by norm_num)
theorem B277789 : Blo 163797 277789 := bbase (se 3 (by rfl) ⟨52085, by rfl⟩ : syracuseStep 277789 = 104171) (by norm_num)
theorem B343325 : Blo 163797 343325 := bbase (se 3 (by rfl) ⟨64373, by rfl⟩ : syracuseStep 343325 = 128747) (by norm_num)
theorem B376109 : Blo 163797 376109 := bbase (se 3 (by rfl) ⟨70520, by rfl⟩ : syracuseStep 376109 = 141041) (by norm_num)
theorem B212321 : Blo 163797 212321 := bbase (se 2 (by rfl) ⟨79620, by rfl⟩ : syracuseStep 212321 = 159241) (by norm_num)
theorem B277877 : Blo 163797 277877 := bbase (se 5 (by rfl) ⟨13025, by rfl⟩ : syracuseStep 277877 = 26051) (by norm_num)
theorem B376181 : Blo 163797 376181 := bbase (se 5 (by rfl) ⟨17633, by rfl⟩ : syracuseStep 376181 = 35267) (by norm_num)
theorem B376253 : Blo 163797 376253 := bbase (se 3 (by rfl) ⟨70547, by rfl⟩ : syracuseStep 376253 = 141095) (by norm_num)
theorem B278005 : Blo 163797 278005 := bbase (se 5 (by rfl) ⟨13031, by rfl⟩ : syracuseStep 278005 = 26063) (by norm_num)
theorem B376325 : Blo 163797 376325 := bbase (se 4 (by rfl) ⟨35280, by rfl⟩ : syracuseStep 376325 = 70561) (by norm_num)
theorem B900629 : Blo 163797 900629 := bbase (se 6 (by rfl) ⟨21108, by rfl⟩ : syracuseStep 900629 = 42217) (by norm_num)
theorem B835109 : Blo 163797 835109 := bbase (se 4 (by rfl) ⟨78291, by rfl⟩ : syracuseStep 835109 = 156583) (by norm_num)
theorem B1064501 : Blo 163797 1064501 := bbase (se 5 (by rfl) ⟨49898, by rfl⟩ : syracuseStep 1064501 = 99797) (by norm_num)
theorem B278093 : Blo 163797 278093 := bbase (se 3 (by rfl) ⟨52142, by rfl⟩ : syracuseStep 278093 = 104285) (by norm_num)
theorem B376397 : Blo 163797 376397 := bbase (se 3 (by rfl) ⟨70574, by rfl⟩ : syracuseStep 376397 = 141149) (by norm_num)
theorem B376469 : Blo 163797 376469 := bbase (se 6 (by rfl) ⟨8823, by rfl⟩ : syracuseStep 376469 = 17647) (by norm_num)
theorem B278221 : Blo 163797 278221 := bbase (se 3 (by rfl) ⟨52166, by rfl⟩ : syracuseStep 278221 = 104333) (by norm_num)
theorem B376541 : Blo 163797 376541 := bbase (se 3 (by rfl) ⟨70601, by rfl⟩ : syracuseStep 376541 = 141203) (by norm_num)
theorem B278309 : Blo 163797 278309 := bbase (se 4 (by rfl) ⟨26091, by rfl⟩ : syracuseStep 278309 = 52183) (by norm_num)
theorem B376613 : Blo 163797 376613 := bbase (se 4 (by rfl) ⟨35307, by rfl⟩ : syracuseStep 376613 = 70615) (by norm_num)
theorem B376685 : Blo 163797 376685 := bbase (se 3 (by rfl) ⟨70628, by rfl⟩ : syracuseStep 376685 = 141257) (by norm_num)
theorem B278437 : Blo 163797 278437 := bbase (se 4 (by rfl) ⟨26103, by rfl⟩ : syracuseStep 278437 = 52207) (by norm_num)
theorem B376757 : Blo 163797 376757 := bbase (se 5 (by rfl) ⟨17660, by rfl⟩ : syracuseStep 376757 = 35321) (by norm_num)
theorem B245717 : Blo 163797 245717 := bbase (se 7 (by rfl) ⟨2879, by rfl⟩ : syracuseStep 245717 = 5759) (by norm_num)
theorem B245741 : Blo 163797 245741 := bbase (se 3 (by rfl) ⟨46076, by rfl⟩ : syracuseStep 245741 = 92153) (by norm_num)
theorem B278525 : Blo 163797 278525 := bbase (se 3 (by rfl) ⟨52223, by rfl⟩ : syracuseStep 278525 = 104447) (by norm_num)
theorem B376829 : Blo 163797 376829 := bbase (se 3 (by rfl) ⟨70655, by rfl⟩ : syracuseStep 376829 = 141311) (by norm_num)
theorem B245765 : Blo 163797 245765 := bbase (se 4 (by rfl) ⟨23040, by rfl⟩ : syracuseStep 245765 = 46081) (by norm_num)
theorem B245789 : Blo 163797 245789 := bbase (se 3 (by rfl) ⟨46085, by rfl⟩ : syracuseStep 245789 = 92171) (by norm_num)
theorem B245813 : Blo 163797 245813 := bbase (se 5 (by rfl) ⟨11522, by rfl⟩ : syracuseStep 245813 = 23045) (by norm_num)
theorem B376901 : Blo 163797 376901 := bbase (se 4 (by rfl) ⟨35334, by rfl⟩ : syracuseStep 376901 = 70669) (by norm_num)
theorem B245837 : Blo 163797 245837 := bbase (se 3 (by rfl) ⟨46094, by rfl⟩ : syracuseStep 245837 = 92189) (by norm_num)
theorem B245861 : Blo 163797 245861 := bbase (se 4 (by rfl) ⟨23049, by rfl⟩ : syracuseStep 245861 = 46099) (by norm_num)
theorem B245885 : Blo 163797 245885 := bbase (se 3 (by rfl) ⟨46103, by rfl⟩ : syracuseStep 245885 = 92207) (by norm_num)
theorem B278653 : Blo 163797 278653 := bbase (se 3 (by rfl) ⟨52247, by rfl⟩ : syracuseStep 278653 = 104495) (by norm_num)
theorem B213125 : Blo 163797 213125 := bbase (se 4 (by rfl) ⟨19980, by rfl⟩ : syracuseStep 213125 = 39961) (by norm_num)
theorem B376973 : Blo 163797 376973 := bbase (se 3 (by rfl) ⟨70682, by rfl⟩ : syracuseStep 376973 = 141365) (by norm_num)
theorem B245909 : Blo 163797 245909 := bbase (se 6 (by rfl) ⟨5763, by rfl⟩ : syracuseStep 245909 = 11527) (by norm_num)
theorem B1130645 : Blo 163797 1130645 := bbase (se 6 (by rfl) ⟨26499, by rfl⟩ : syracuseStep 1130645 = 52999) (by norm_num)
theorem B245933 : Blo 163797 245933 := bbase (se 3 (by rfl) ⟨46112, by rfl⟩ : syracuseStep 245933 = 92225) (by norm_num)
theorem B704693 : Blo 163797 704693 := bbase (se 5 (by rfl) ⟨33032, by rfl⟩ : syracuseStep 704693 = 66065) (by norm_num)
theorem B245957 : Blo 163797 245957 := bbase (se 4 (by rfl) ⟨23058, by rfl⟩ : syracuseStep 245957 = 46117) (by norm_num)
theorem B278741 : Blo 163797 278741 := bbase (se 7 (by rfl) ⟨3266, by rfl⟩ : syracuseStep 278741 = 6533) (by norm_num)
theorem B377045 : Blo 163797 377045 := bbase (se 7 (by rfl) ⟨4418, by rfl⟩ : syracuseStep 377045 = 8837) (by norm_num)
theorem B245981 : Blo 163797 245981 := bbase (se 3 (by rfl) ⟨46121, by rfl⟩ : syracuseStep 245981 = 92243) (by norm_num)
theorem B213229 : Blo 163797 213229 := bbase (se 3 (by rfl) ⟨39980, by rfl⟩ : syracuseStep 213229 = 79961) (by norm_num)
theorem B246005 : Blo 163797 246005 := bbase (se 5 (by rfl) ⟨11531, by rfl⟩ : syracuseStep 246005 = 23063) (by norm_num)
theorem B246029 : Blo 163797 246029 := bbase (se 3 (by rfl) ⟨46130, by rfl⟩ : syracuseStep 246029 = 92261) (by norm_num)
theorem B377117 : Blo 163797 377117 := bbase (se 3 (by rfl) ⟨70709, by rfl⟩ : syracuseStep 377117 = 141419) (by norm_num)
theorem B246053 : Blo 163797 246053 := bbase (se 4 (by rfl) ⟨23067, by rfl⟩ : syracuseStep 246053 = 46135) (by norm_num)
theorem B475445 : Blo 163797 475445 := bbase (se 5 (by rfl) ⟨22286, by rfl⟩ : syracuseStep 475445 = 44573) (by norm_num)
theorem B246077 : Blo 163797 246077 := bbase (se 3 (by rfl) ⟨46139, by rfl⟩ : syracuseStep 246077 = 92279) (by norm_num)
theorem B246101 : Blo 163797 246101 := bbase (se 10 (by rfl) ⟨360, by rfl⟩ : syracuseStep 246101 = 721) (by norm_num)
theorem B278869 : Blo 163797 278869 := bbase (se 10 (by rfl) ⟨408, by rfl⟩ : syracuseStep 278869 = 817) (by norm_num)
theorem B377189 : Blo 163797 377189 := bbase (se 4 (by rfl) ⟨35361, by rfl⟩ : syracuseStep 377189 = 70723) (by norm_num)
theorem B246125 : Blo 163797 246125 := bbase (se 3 (by rfl) ⟨46148, by rfl⟩ : syracuseStep 246125 = 92297) (by norm_num)
theorem B246149 : Blo 163797 246149 := bbase (se 4 (by rfl) ⟨23076, by rfl⟩ : syracuseStep 246149 = 46153) (by norm_num)
theorem B409997 : Blo 163797 409997 := bbase (se 3 (by rfl) ⟨76874, by rfl⟩ : syracuseStep 409997 = 153749) (by norm_num)
theorem B311701 : Blo 163797 311701 := bbase (se 6 (by rfl) ⟨7305, by rfl⟩ : syracuseStep 311701 = 14611) (by norm_num)
theorem B246173 : Blo 163797 246173 := bbase (se 3 (by rfl) ⟨46157, by rfl⟩ : syracuseStep 246173 = 92315) (by norm_num)
theorem B704933 : Blo 163797 704933 := bbase (se 4 (by rfl) ⟨66087, by rfl⟩ : syracuseStep 704933 = 132175) (by norm_num)
theorem B278957 : Blo 163797 278957 := bbase (se 3 (by rfl) ⟨52304, by rfl⟩ : syracuseStep 278957 = 104609) (by norm_num)
theorem B377261 : Blo 163797 377261 := bbase (se 3 (by rfl) ⟨70736, by rfl⟩ : syracuseStep 377261 = 141473) (by norm_num)
theorem B246197 : Blo 163797 246197 := bbase (se 5 (by rfl) ⟨11540, by rfl⟩ : syracuseStep 246197 = 23081) (by norm_num)
theorem B213445 : Blo 163797 213445 := bbase (se 4 (by rfl) ⟨20010, by rfl⟩ : syracuseStep 213445 = 40021) (by norm_num)
theorem B246221 : Blo 163797 246221 := bbase (se 3 (by rfl) ⟨46166, by rfl⟩ : syracuseStep 246221 = 92333) (by norm_num)
theorem B4047317 : Blo 163797 4047317 := bbase (se 7 (by rfl) ⟨47429, by rfl⟩ : syracuseStep 4047317 = 94859) (by norm_num)
theorem B246245 : Blo 163797 246245 := bbase (se 4 (by rfl) ⟨23085, by rfl⟩ : syracuseStep 246245 = 46171) (by norm_num)
theorem B377333 : Blo 163797 377333 := bbase (se 5 (by rfl) ⟨17687, by rfl⟩ : syracuseStep 377333 = 35375) (by norm_num)
theorem B246269 : Blo 163797 246269 := bbase (se 3 (by rfl) ⟨46175, by rfl⟩ : syracuseStep 246269 = 92351) (by norm_num)
theorem B246293 : Blo 163797 246293 := bbase (se 6 (by rfl) ⟨5772, by rfl⟩ : syracuseStep 246293 = 11545) (by norm_num)
theorem B311845 : Blo 163797 311845 := bbase (se 4 (by rfl) ⟨29235, by rfl⟩ : syracuseStep 311845 = 58471) (by norm_num)
theorem B246317 : Blo 163797 246317 := bbase (se 3 (by rfl) ⟨46184, by rfl⟩ : syracuseStep 246317 = 92369) (by norm_num)
theorem B279085 : Blo 163797 279085 := bbase (se 3 (by rfl) ⟨52328, by rfl⟩ : syracuseStep 279085 = 104657) (by norm_num)
theorem B377405 : Blo 163797 377405 := bbase (se 3 (by rfl) ⟨70763, by rfl⟩ : syracuseStep 377405 = 141527) (by norm_num)
theorem B246341 : Blo 163797 246341 := bbase (se 4 (by rfl) ⟨23094, by rfl⟩ : syracuseStep 246341 = 46189) (by norm_num)
theorem B246365 : Blo 163797 246365 := bbase (se 3 (by rfl) ⟨46193, by rfl⟩ : syracuseStep 246365 = 92387) (by norm_num)
theorem B246389 : Blo 163797 246389 := bbase (se 5 (by rfl) ⟨11549, by rfl⟩ : syracuseStep 246389 = 23099) (by norm_num)
theorem B279173 : Blo 163797 279173 := bbase (se 4 (by rfl) ⟨26172, by rfl⟩ : syracuseStep 279173 = 52345) (by norm_num)
theorem B377477 : Blo 163797 377477 := bbase (se 4 (by rfl) ⟨35388, by rfl⟩ : syracuseStep 377477 = 70777) (by norm_num)
theorem B246413 : Blo 163797 246413 := bbase (se 3 (by rfl) ⟨46202, by rfl⟩ : syracuseStep 246413 = 92405) (by norm_num)
theorem B246437 : Blo 163797 246437 := bbase (se 4 (by rfl) ⟨23103, by rfl⟩ : syracuseStep 246437 = 46207) (by norm_num)
theorem B246461 : Blo 163797 246461 := bbase (se 3 (by rfl) ⟨46211, by rfl⟩ : syracuseStep 246461 = 92423) (by norm_num)
theorem B312005 : Blo 163797 312005 := bbase (se 4 (by rfl) ⟨29250, by rfl⟩ : syracuseStep 312005 = 58501) (by norm_num)
theorem B246485 : Blo 163797 246485 := bbase (se 7 (by rfl) ⟨2888, by rfl⟩ : syracuseStep 246485 = 5777) (by norm_num)
theorem B541397 : Blo 163797 541397 := bbase (se 7 (by rfl) ⟨6344, by rfl⟩ : syracuseStep 541397 = 12689) (by norm_num)
theorem B246509 : Blo 163797 246509 := bbase (se 3 (by rfl) ⟨46220, by rfl⟩ : syracuseStep 246509 = 92441) (by norm_num)
theorem B246533 : Blo 163797 246533 := bbase (se 4 (by rfl) ⟨23112, by rfl⟩ : syracuseStep 246533 = 46225) (by norm_num)
theorem B279301 : Blo 163797 279301 := bbase (se 4 (by rfl) ⟨26184, by rfl⟩ : syracuseStep 279301 = 52369) (by norm_num)
theorem B246557 : Blo 163797 246557 := bbase (se 3 (by rfl) ⟨46229, by rfl⟩ : syracuseStep 246557 = 92459) (by norm_num)
theorem B803621 : Blo 163797 803621 := bbase (se 4 (by rfl) ⟨75339, by rfl⟩ : syracuseStep 803621 = 150679) (by norm_num)
theorem B246581 : Blo 163797 246581 := bbase (se 5 (by rfl) ⟨11558, by rfl⟩ : syracuseStep 246581 = 23117) (by norm_num)
theorem B836405 : Blo 163797 836405 := bbase (se 5 (by rfl) ⟨39206, by rfl⟩ : syracuseStep 836405 = 78413) (by norm_num)
theorem B246605 : Blo 163797 246605 := bbase (se 3 (by rfl) ⟨46238, by rfl⟩ : syracuseStep 246605 = 92477) (by norm_num)
theorem B312149 : Blo 163797 312149 := bbase (se 9 (by rfl) ⟨914, by rfl⟩ : syracuseStep 312149 = 1829) (by norm_num)
theorem B279389 : Blo 163797 279389 := bbase (se 3 (by rfl) ⟨52385, by rfl⟩ : syracuseStep 279389 = 104771) (by norm_num)
theorem B246629 : Blo 163797 246629 := bbase (se 4 (by rfl) ⟨23121, by rfl⟩ : syracuseStep 246629 = 46243) (by norm_num)
theorem B246653 : Blo 163797 246653 := bbase (se 3 (by rfl) ⟨46247, by rfl⟩ : syracuseStep 246653 = 92495) (by norm_num)
theorem B246677 : Blo 163797 246677 := bbase (se 6 (by rfl) ⟨5781, by rfl⟩ : syracuseStep 246677 = 11563) (by norm_num)
theorem B246701 : Blo 163797 246701 := bbase (se 3 (by rfl) ⟨46256, by rfl⟩ : syracuseStep 246701 = 92513) (by norm_num)
theorem B246725 : Blo 163797 246725 := bbase (se 4 (by rfl) ⟨23130, by rfl⟩ : syracuseStep 246725 = 46261) (by norm_num)
theorem B246749 : Blo 163797 246749 := bbase (se 3 (by rfl) ⟨46265, by rfl⟩ : syracuseStep 246749 = 92531) (by norm_num)
theorem B279517 : Blo 163797 279517 := bbase (se 3 (by rfl) ⟨52409, by rfl⟩ : syracuseStep 279517 = 104819) (by norm_num)
theorem B246773 : Blo 163797 246773 := bbase (se 5 (by rfl) ⟨11567, by rfl⟩ : syracuseStep 246773 = 23135) (by norm_num)
theorem B246797 : Blo 163797 246797 := bbase (se 3 (by rfl) ⟨46274, by rfl⟩ : syracuseStep 246797 = 92549) (by norm_num)
theorem B246821 : Blo 163797 246821 := bbase (se 4 (by rfl) ⟨23139, by rfl⟩ : syracuseStep 246821 = 46279) (by norm_num)
theorem B279605 : Blo 163797 279605 := bbase (se 5 (by rfl) ⟨13106, by rfl⟩ : syracuseStep 279605 = 26213) (by norm_num)
theorem B246845 : Blo 163797 246845 := bbase (se 3 (by rfl) ⟨46283, by rfl⟩ : syracuseStep 246845 = 92567) (by norm_num)
theorem B246869 : Blo 163797 246869 := bbase (se 8 (by rfl) ⟨1446, by rfl⟩ : syracuseStep 246869 = 2893) (by norm_num)
theorem B246893 : Blo 163797 246893 := bbase (se 3 (by rfl) ⟨46292, by rfl⟩ : syracuseStep 246893 = 92585) (by norm_num)
theorem B312437 : Blo 163797 312437 := bbase (se 5 (by rfl) ⟨14645, by rfl⟩ : syracuseStep 312437 = 29291) (by norm_num)
theorem B246917 : Blo 163797 246917 := bbase (se 4 (by rfl) ⟨23148, by rfl⟩ : syracuseStep 246917 = 46297) (by norm_num)
theorem B181397 : Blo 163797 181397 := bbase (se 6 (by rfl) ⟨4251, by rfl⟩ : syracuseStep 181397 = 8503) (by norm_num)
theorem B246941 : Blo 163797 246941 := bbase (se 3 (by rfl) ⟨46301, by rfl⟩ : syracuseStep 246941 = 92603) (by norm_num)
theorem B246965 : Blo 163797 246965 := bbase (se 5 (by rfl) ⟨11576, by rfl⟩ : syracuseStep 246965 = 23153) (by norm_num)
theorem B279733 : Blo 163797 279733 := bbase (se 5 (by rfl) ⟨13112, by rfl⟩ : syracuseStep 279733 = 26225) (by norm_num)
theorem B246989 : Blo 163797 246989 := bbase (se 3 (by rfl) ⟨46310, by rfl⟩ : syracuseStep 246989 = 92621) (by norm_num)
theorem B247013 : Blo 163797 247013 := bbase (se 4 (by rfl) ⟨23157, by rfl⟩ : syracuseStep 247013 = 46315) (by norm_num)
theorem B247037 : Blo 163797 247037 := bbase (se 3 (by rfl) ⟨46319, by rfl⟩ : syracuseStep 247037 = 92639) (by norm_num)
theorem B312589 : Blo 163797 312589 := bbase (se 3 (by rfl) ⟨58610, by rfl⟩ : syracuseStep 312589 = 117221) (by norm_num)
theorem B279821 : Blo 163797 279821 := bbase (se 3 (by rfl) ⟨52466, by rfl⟩ : syracuseStep 279821 = 104933) (by norm_num)
theorem B247061 : Blo 163797 247061 := bbase (se 6 (by rfl) ⟨5790, by rfl⟩ : syracuseStep 247061 = 11581) (by norm_num)
theorem B1525013 : Blo 163797 1525013 := bbase (se 6 (by rfl) ⟨35742, by rfl⟩ : syracuseStep 1525013 = 71485) (by norm_num)
theorem B247085 : Blo 163797 247085 := bbase (se 3 (by rfl) ⟨46328, by rfl⟩ : syracuseStep 247085 = 92657) (by norm_num)
theorem B247109 : Blo 163797 247109 := bbase (se 4 (by rfl) ⟨23166, by rfl⟩ : syracuseStep 247109 = 46333) (by norm_num)
theorem B247133 : Blo 163797 247133 := bbase (se 3 (by rfl) ⟨46337, by rfl⟩ : syracuseStep 247133 = 92675) (by norm_num)
theorem B247157 : Blo 163797 247157 := bbase (se 5 (by rfl) ⟨11585, by rfl⟩ : syracuseStep 247157 = 23171) (by norm_num)
theorem B247181 : Blo 163797 247181 := bbase (se 3 (by rfl) ⟨46346, by rfl⟩ : syracuseStep 247181 = 92693) (by norm_num)
theorem B279949 : Blo 163797 279949 := bbase (se 3 (by rfl) ⟨52490, by rfl⟩ : syracuseStep 279949 = 104981) (by norm_num)
theorem B247205 : Blo 163797 247205 := bbase (se 4 (by rfl) ⟨23175, by rfl⟩ : syracuseStep 247205 = 46351) (by norm_num)
theorem B247229 : Blo 163797 247229 := bbase (se 3 (by rfl) ⟨46355, by rfl⟩ : syracuseStep 247229 = 92711) (by norm_num)
theorem B247253 : Blo 163797 247253 := bbase (se 7 (by rfl) ⟨2897, by rfl⟩ : syracuseStep 247253 = 5795) (by norm_num)
theorem B2803157 : Blo 163797 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B378341 : Blo 163797 378341 := bbase (se 4 (by rfl) ⟨35469, by rfl⟩ : syracuseStep 378341 = 70939) (by norm_num)
theorem B280037 : Blo 163797 280037 := bbase (se 4 (by rfl) ⟨26253, by rfl⟩ : syracuseStep 280037 = 52507) (by norm_num)
theorem B247277 : Blo 163797 247277 := bbase (se 3 (by rfl) ⟨46364, by rfl⟩ : syracuseStep 247277 = 92729) (by norm_num)
theorem B247301 : Blo 163797 247301 := bbase (se 4 (by rfl) ⟨23184, by rfl⟩ : syracuseStep 247301 = 46369) (by norm_num)
theorem B247325 : Blo 163797 247325 := bbase (se 3 (by rfl) ⟨46373, by rfl⟩ : syracuseStep 247325 = 92747) (by norm_num)
theorem B247349 : Blo 163797 247349 := bbase (se 5 (by rfl) ⟨11594, by rfl⟩ : syracuseStep 247349 = 23189) (by norm_num)
theorem B1525301 : Blo 163797 1525301 := bbase (se 5 (by rfl) ⟨71498, by rfl⟩ : syracuseStep 1525301 = 142997) (by norm_num)
theorem B312893 : Blo 163797 312893 := bbase (se 3 (by rfl) ⟨58667, by rfl⟩ : syracuseStep 312893 = 117335) (by norm_num)
theorem B247373 : Blo 163797 247373 := bbase (se 3 (by rfl) ⟨46382, by rfl⟩ : syracuseStep 247373 = 92765) (by norm_num)
theorem B247397 : Blo 163797 247397 := bbase (se 4 (by rfl) ⟨23193, by rfl⟩ : syracuseStep 247397 = 46387) (by norm_num)
theorem B280165 : Blo 163797 280165 := bbase (se 4 (by rfl) ⟨26265, by rfl⟩ : syracuseStep 280165 = 52531) (by norm_num)
theorem B247421 : Blo 163797 247421 := bbase (se 3 (by rfl) ⟨46391, by rfl⟩ : syracuseStep 247421 = 92783) (by norm_num)
theorem B247445 : Blo 163797 247445 := bbase (se 6 (by rfl) ⟨5799, by rfl⟩ : syracuseStep 247445 = 11599) (by norm_num)
theorem B247469 : Blo 163797 247469 := bbase (se 3 (by rfl) ⟨46400, by rfl⟩ : syracuseStep 247469 = 92801) (by norm_num)
theorem B280253 : Blo 163797 280253 := bbase (se 3 (by rfl) ⟨52547, by rfl⟩ : syracuseStep 280253 = 105095) (by norm_num)
theorem B247493 : Blo 163797 247493 := bbase (se 4 (by rfl) ⟨23202, by rfl⟩ : syracuseStep 247493 = 46405) (by norm_num)
theorem B247517 : Blo 163797 247517 := bbase (se 3 (by rfl) ⟨46409, by rfl⟩ : syracuseStep 247517 = 92819) (by norm_num)
theorem B247541 : Blo 163797 247541 := bbase (se 5 (by rfl) ⟨11603, by rfl⟩ : syracuseStep 247541 = 23207) (by norm_num)
theorem B247565 : Blo 163797 247565 := bbase (se 3 (by rfl) ⟨46418, by rfl⟩ : syracuseStep 247565 = 92837) (by norm_num)
theorem B247589 : Blo 163797 247589 := bbase (se 4 (by rfl) ⟨23211, by rfl⟩ : syracuseStep 247589 = 46423) (by norm_num)
theorem B247613 : Blo 163797 247613 := bbase (se 3 (by rfl) ⟨46427, by rfl⟩ : syracuseStep 247613 = 92855) (by norm_num)
theorem B280381 : Blo 163797 280381 := bbase (se 3 (by rfl) ⟨52571, by rfl⟩ : syracuseStep 280381 = 105143) (by norm_num)
theorem B247637 : Blo 163797 247637 := bbase (se 9 (by rfl) ⟨725, by rfl⟩ : syracuseStep 247637 = 1451) (by norm_num)
theorem B477029 : Blo 163797 477029 := bbase (se 4 (by rfl) ⟨44721, by rfl⟩ : syracuseStep 477029 = 89443) (by norm_num)
theorem B247661 : Blo 163797 247661 := bbase (se 3 (by rfl) ⟨46436, by rfl⟩ : syracuseStep 247661 = 92873) (by norm_num)
theorem B247685 : Blo 163797 247685 := bbase (se 4 (by rfl) ⟨23220, by rfl⟩ : syracuseStep 247685 = 46441) (by norm_num)
theorem B280469 : Blo 163797 280469 := bbase (se 6 (by rfl) ⟨6573, by rfl⟩ : syracuseStep 280469 = 13147) (by norm_num)
theorem B247709 : Blo 163797 247709 := bbase (se 3 (by rfl) ⟨46445, by rfl⟩ : syracuseStep 247709 = 92891) (by norm_num)
theorem B1427381 : Blo 163797 1427381 := bbase (se 5 (by rfl) ⟨66908, by rfl⟩ : syracuseStep 1427381 = 133817) (by norm_num)
theorem B247733 : Blo 163797 247733 := bbase (se 5 (by rfl) ⟨11612, by rfl⟩ : syracuseStep 247733 = 23225) (by norm_num)
theorem B542645 : Blo 163797 542645 := bbase (se 5 (by rfl) ⟨25436, by rfl⟩ : syracuseStep 542645 = 50873) (by norm_num)
theorem B247757 : Blo 163797 247757 := bbase (se 3 (by rfl) ⟨46454, by rfl⟩ : syracuseStep 247757 = 92909) (by norm_num)
theorem B280541 : Blo 163797 280541 := bbase (se 3 (by rfl) ⟨52601, by rfl⟩ : syracuseStep 280541 = 105203) (by norm_num)
theorem B247781 : Blo 163797 247781 := bbase (se 4 (by rfl) ⟨23229, by rfl⟩ : syracuseStep 247781 = 46459) (by norm_num)
theorem B247805 : Blo 163797 247805 := bbase (se 3 (by rfl) ⟨46463, by rfl⟩ : syracuseStep 247805 = 92927) (by norm_num)
theorem B2803733 : Blo 163797 2803733 := bbase (se 6 (by rfl) ⟨65712, by rfl⟩ : syracuseStep 2803733 = 131425) (by norm_num)
theorem B247829 : Blo 163797 247829 := bbase (se 6 (by rfl) ⟨5808, by rfl⟩ : syracuseStep 247829 = 11617) (by norm_num)
theorem B280597 : Blo 163797 280597 := bbase (se 6 (by rfl) ⟨6576, by rfl⟩ : syracuseStep 280597 = 13153) (by norm_num)
theorem B247853 : Blo 163797 247853 := bbase (se 3 (by rfl) ⟨46472, by rfl⟩ : syracuseStep 247853 = 92945) (by norm_num)
theorem B280637 : Blo 163797 280637 := bbase (se 3 (by rfl) ⟨52619, by rfl⟩ : syracuseStep 280637 = 105239) (by norm_num)
theorem B247877 : Blo 163797 247877 := bbase (se 4 (by rfl) ⟨23238, by rfl⟩ : syracuseStep 247877 = 46477) (by norm_num)
theorem B837701 : Blo 163797 837701 := bbase (se 4 (by rfl) ⟨78534, by rfl⟩ : syracuseStep 837701 = 157069) (by norm_num)
theorem B247901 : Blo 163797 247901 := bbase (se 3 (by rfl) ⟨46481, by rfl⟩ : syracuseStep 247901 = 92963) (by norm_num)
theorem B280685 : Blo 163797 280685 := bbase (se 3 (by rfl) ⟨52628, by rfl⟩ : syracuseStep 280685 = 105257) (by norm_num)
theorem B247925 : Blo 163797 247925 := bbase (se 5 (by rfl) ⟨11621, by rfl⟩ : syracuseStep 247925 = 23243) (by norm_num)
theorem B247949 : Blo 163797 247949 := bbase (se 3 (by rfl) ⟨46490, by rfl⟩ : syracuseStep 247949 = 92981) (by norm_num)
theorem B247973 : Blo 163797 247973 := bbase (se 4 (by rfl) ⟨23247, by rfl⟩ : syracuseStep 247973 = 46495) (by norm_num)
theorem B247997 : Blo 163797 247997 := bbase (se 3 (by rfl) ⟨46499, by rfl⟩ : syracuseStep 247997 = 92999) (by norm_num)
theorem B248021 : Blo 163797 248021 := bbase (se 7 (by rfl) ⟨2906, by rfl⟩ : syracuseStep 248021 = 5813) (by norm_num)
theorem B248045 : Blo 163797 248045 := bbase (se 3 (by rfl) ⟨46508, by rfl⟩ : syracuseStep 248045 = 93017) (by norm_num)
theorem B280813 : Blo 163797 280813 := bbase (se 3 (by rfl) ⟨52652, by rfl⟩ : syracuseStep 280813 = 105305) (by norm_num)
theorem B248069 : Blo 163797 248069 := bbase (se 4 (by rfl) ⟨23256, by rfl⟩ : syracuseStep 248069 = 46513) (by norm_num)
theorem B248093 : Blo 163797 248093 := bbase (se 3 (by rfl) ⟨46517, by rfl⟩ : syracuseStep 248093 = 93035) (by norm_num)
theorem B313645 : Blo 163797 313645 := bbase (se 3 (by rfl) ⟨58808, by rfl⟩ : syracuseStep 313645 = 117617) (by norm_num)
theorem B248117 : Blo 163797 248117 := bbase (se 5 (by rfl) ⟨11630, by rfl⟩ : syracuseStep 248117 = 23261) (by norm_num)
theorem B280901 : Blo 163797 280901 := bbase (se 4 (by rfl) ⟨26334, by rfl⟩ : syracuseStep 280901 = 52669) (by norm_num)
theorem B248141 : Blo 163797 248141 := bbase (se 3 (by rfl) ⟨46526, by rfl⟩ : syracuseStep 248141 = 93053) (by norm_num)
theorem B248165 : Blo 163797 248165 := bbase (se 4 (by rfl) ⟨23265, by rfl⟩ : syracuseStep 248165 = 46531) (by norm_num)
theorem B248189 : Blo 163797 248189 := bbase (se 3 (by rfl) ⟨46535, by rfl⟩ : syracuseStep 248189 = 93071) (by norm_num)
theorem B248213 : Blo 163797 248213 := bbase (se 6 (by rfl) ⟨5817, by rfl⟩ : syracuseStep 248213 = 11635) (by norm_num)
theorem B248237 : Blo 163797 248237 := bbase (se 3 (by rfl) ⟨46544, by rfl⟩ : syracuseStep 248237 = 93089) (by norm_num)
theorem B313789 : Blo 163797 313789 := bbase (se 3 (by rfl) ⟨58835, by rfl⟩ : syracuseStep 313789 = 117671) (by norm_num)
theorem B248261 : Blo 163797 248261 := bbase (se 4 (by rfl) ⟨23274, by rfl⟩ : syracuseStep 248261 = 46549) (by norm_num)
theorem B281029 : Blo 163797 281029 := bbase (se 4 (by rfl) ⟨26346, by rfl⟩ : syracuseStep 281029 = 52693) (by norm_num)
theorem B1264085 : Blo 163797 1264085 := bbase (se 7 (by rfl) ⟨14813, by rfl⟩ : syracuseStep 1264085 = 29627) (by norm_num)
theorem B248285 : Blo 163797 248285 := bbase (se 3 (by rfl) ⟨46553, by rfl⟩ : syracuseStep 248285 = 93107) (by norm_num)
theorem B444901 : Blo 163797 444901 := bbase (se 4 (by rfl) ⟨41709, by rfl⟩ : syracuseStep 444901 = 83419) (by norm_num)
theorem B248309 : Blo 163797 248309 := bbase (se 5 (by rfl) ⟨11639, by rfl⟩ : syracuseStep 248309 = 23279) (by norm_num)
theorem B477701 : Blo 163797 477701 := bbase (se 4 (by rfl) ⟨44784, by rfl⟩ : syracuseStep 477701 = 89569) (by norm_num)
theorem B248333 : Blo 163797 248333 := bbase (se 3 (by rfl) ⟨46562, by rfl⟩ : syracuseStep 248333 = 93125) (by norm_num)
theorem B281117 : Blo 163797 281117 := bbase (se 3 (by rfl) ⟨52709, by rfl⟩ : syracuseStep 281117 = 105419) (by norm_num)
theorem B248357 : Blo 163797 248357 := bbase (se 4 (by rfl) ⟨23283, by rfl⟩ : syracuseStep 248357 = 46567) (by norm_num)
theorem B248381 : Blo 163797 248381 := bbase (se 3 (by rfl) ⟨46571, by rfl⟩ : syracuseStep 248381 = 93143) (by norm_num)
theorem B248405 : Blo 163797 248405 := bbase (se 8 (by rfl) ⟨1455, by rfl⟩ : syracuseStep 248405 = 2911) (by norm_num)
theorem B313949 : Blo 163797 313949 := bbase (se 3 (by rfl) ⟨58865, by rfl⟩ : syracuseStep 313949 = 117731) (by norm_num)
theorem B248429 : Blo 163797 248429 := bbase (se 3 (by rfl) ⟨46580, by rfl⟩ : syracuseStep 248429 = 93161) (by norm_num)
theorem B248453 : Blo 163797 248453 := bbase (se 4 (by rfl) ⟨23292, by rfl⟩ : syracuseStep 248453 = 46585) (by norm_num)
theorem B707221 : Blo 163797 707221 := bbase (se 6 (by rfl) ⟨16575, by rfl⟩ : syracuseStep 707221 = 33151) (by norm_num)
theorem B248477 : Blo 163797 248477 := bbase (se 3 (by rfl) ⟨46589, by rfl⟩ : syracuseStep 248477 = 93179) (by norm_num)
theorem B281245 : Blo 163797 281245 := bbase (se 3 (by rfl) ⟨52733, by rfl⟩ : syracuseStep 281245 = 105467) (by norm_num)
theorem B936629 : Blo 163797 936629 := bbase (se 5 (by rfl) ⟨43904, by rfl⟩ : syracuseStep 936629 = 87809) (by norm_num)
theorem B248501 : Blo 163797 248501 := bbase (se 5 (by rfl) ⟨11648, by rfl⟩ : syracuseStep 248501 = 23297) (by norm_num)
theorem B1067701 : Blo 163797 1067701 := bbase (se 5 (by rfl) ⟨50048, by rfl⟩ : syracuseStep 1067701 = 100097) (by norm_num)
theorem B248525 : Blo 163797 248525 := bbase (se 3 (by rfl) ⟨46598, by rfl⟩ : syracuseStep 248525 = 93197) (by norm_num)
theorem B248549 : Blo 163797 248549 := bbase (se 4 (by rfl) ⟨23301, by rfl⟩ : syracuseStep 248549 = 46603) (by norm_num)
theorem B314093 : Blo 163797 314093 := bbase (se 3 (by rfl) ⟨58892, by rfl⟩ : syracuseStep 314093 = 117785) (by norm_num)
theorem B281333 : Blo 163797 281333 := bbase (se 5 (by rfl) ⟨13187, by rfl⟩ : syracuseStep 281333 = 26375) (by norm_num)
theorem B248573 : Blo 163797 248573 := bbase (se 3 (by rfl) ⟨46607, by rfl⟩ : syracuseStep 248573 = 93215) (by norm_num)
theorem B248597 : Blo 163797 248597 := bbase (se 6 (by rfl) ⟨5826, by rfl⟩ : syracuseStep 248597 = 11653) (by norm_num)
theorem B248621 : Blo 163797 248621 := bbase (se 3 (by rfl) ⟨46616, by rfl⟩ : syracuseStep 248621 = 93233) (by norm_num)
theorem B248645 : Blo 163797 248645 := bbase (se 4 (by rfl) ⟨23310, by rfl⟩ : syracuseStep 248645 = 46621) (by norm_num)
theorem B248669 : Blo 163797 248669 := bbase (se 3 (by rfl) ⟨46625, by rfl⟩ : syracuseStep 248669 = 93251) (by norm_num)
theorem B248693 : Blo 163797 248693 := bbase (se 5 (by rfl) ⟨11657, by rfl⟩ : syracuseStep 248693 = 23315) (by norm_num)
theorem B281461 : Blo 163797 281461 := bbase (se 5 (by rfl) ⟨13193, by rfl⟩ : syracuseStep 281461 = 26387) (by norm_num)
theorem B248717 : Blo 163797 248717 := bbase (se 3 (by rfl) ⟨46634, by rfl⟩ : syracuseStep 248717 = 93269) (by norm_num)
theorem B248741 : Blo 163797 248741 := bbase (se 4 (by rfl) ⟨23319, by rfl⟩ : syracuseStep 248741 = 46639) (by norm_num)
theorem B248765 : Blo 163797 248765 := bbase (se 3 (by rfl) ⟨46643, by rfl⟩ : syracuseStep 248765 = 93287) (by norm_num)
theorem B281549 : Blo 163797 281549 := bbase (se 3 (by rfl) ⟨52790, by rfl⟩ : syracuseStep 281549 = 105581) (by norm_num)
theorem B248789 : Blo 163797 248789 := bbase (se 7 (by rfl) ⟨2915, by rfl⟩ : syracuseStep 248789 = 5831) (by norm_num)
theorem B248813 : Blo 163797 248813 := bbase (se 3 (by rfl) ⟨46652, by rfl⟩ : syracuseStep 248813 = 93305) (by norm_num)
theorem B248837 : Blo 163797 248837 := bbase (se 4 (by rfl) ⟨23328, by rfl⟩ : syracuseStep 248837 = 46657) (by norm_num)
theorem B314381 : Blo 163797 314381 := bbase (se 3 (by rfl) ⟨58946, by rfl⟩ : syracuseStep 314381 = 117893) (by norm_num)
theorem B248861 : Blo 163797 248861 := bbase (se 3 (by rfl) ⟨46661, by rfl⟩ : syracuseStep 248861 = 93323) (by norm_num)
theorem B248885 : Blo 163797 248885 := bbase (se 5 (by rfl) ⟨11666, by rfl⟩ : syracuseStep 248885 = 23333) (by norm_num)
theorem B248909 : Blo 163797 248909 := bbase (se 3 (by rfl) ⟨46670, by rfl⟩ : syracuseStep 248909 = 93341) (by norm_num)
theorem B281677 : Blo 163797 281677 := bbase (se 3 (by rfl) ⟨52814, by rfl⟩ : syracuseStep 281677 = 105629) (by norm_num)
theorem B248933 : Blo 163797 248933 := bbase (se 4 (by rfl) ⟨23337, by rfl⟩ : syracuseStep 248933 = 46675) (by norm_num)
theorem B248957 : Blo 163797 248957 := bbase (se 3 (by rfl) ⟨46679, by rfl⟩ : syracuseStep 248957 = 93359) (by norm_num)
theorem B248981 : Blo 163797 248981 := bbase (se 6 (by rfl) ⟨5835, by rfl⟩ : syracuseStep 248981 = 11671) (by norm_num)
theorem B314533 : Blo 163797 314533 := bbase (se 4 (by rfl) ⟨29487, by rfl⟩ : syracuseStep 314533 = 58975) (by norm_num)
theorem B281765 : Blo 163797 281765 := bbase (se 4 (by rfl) ⟨26415, by rfl⟩ : syracuseStep 281765 = 52831) (by norm_num)
theorem B249005 : Blo 163797 249005 := bbase (se 3 (by rfl) ⟨46688, by rfl⟩ : syracuseStep 249005 = 93377) (by norm_num)
theorem B249029 : Blo 163797 249029 := bbase (se 4 (by rfl) ⟨23346, by rfl⟩ : syracuseStep 249029 = 46693) (by norm_num)
theorem B249053 : Blo 163797 249053 := bbase (se 3 (by rfl) ⟨46697, by rfl⟩ : syracuseStep 249053 = 93395) (by norm_num)
theorem B249077 : Blo 163797 249077 := bbase (se 5 (by rfl) ⟨11675, by rfl⟩ : syracuseStep 249077 = 23351) (by norm_num)
theorem B249101 : Blo 163797 249101 := bbase (se 3 (by rfl) ⟨46706, by rfl⟩ : syracuseStep 249101 = 93413) (by norm_num)
theorem B249125 : Blo 163797 249125 := bbase (se 4 (by rfl) ⟨23355, by rfl⟩ : syracuseStep 249125 = 46711) (by norm_num)
theorem B281893 : Blo 163797 281893 := bbase (se 4 (by rfl) ⟨26427, by rfl⟩ : syracuseStep 281893 = 52855) (by norm_num)
theorem B249149 : Blo 163797 249149 := bbase (se 3 (by rfl) ⟨46715, by rfl⟩ : syracuseStep 249149 = 93431) (by norm_num)
theorem B249157 : Blo 163797 249157 := bbase (se 4 (by rfl) ⟨23358, by rfl⟩ : syracuseStep 249157 = 46717) (by norm_num)
theorem B838997 : Blo 163797 838997 := bbase (se 11 (by rfl) ⟨614, by rfl⟩ : syracuseStep 838997 = 1229) (by norm_num)
theorem B249173 : Blo 163797 249173 := bbase (se 11 (by rfl) ⟨182, by rfl⟩ : syracuseStep 249173 = 365) (by norm_num)
theorem B249197 : Blo 163797 249197 := bbase (se 3 (by rfl) ⟨46724, by rfl⟩ : syracuseStep 249197 = 93449) (by norm_num)
theorem B281981 : Blo 163797 281981 := bbase (se 3 (by rfl) ⟨52871, by rfl⟩ : syracuseStep 281981 = 105743) (by norm_num)
theorem B249221 : Blo 163797 249221 := bbase (se 4 (by rfl) ⟨23364, by rfl⟩ : syracuseStep 249221 = 46729) (by norm_num)
theorem B249245 : Blo 163797 249245 := bbase (se 3 (by rfl) ⟨46733, by rfl⟩ : syracuseStep 249245 = 93467) (by norm_num)
theorem B249269 : Blo 163797 249269 := bbase (se 5 (by rfl) ⟨11684, by rfl⟩ : syracuseStep 249269 = 23369) (by norm_num)
theorem B282053 : Blo 163797 282053 := bbase (se 4 (by rfl) ⟨26442, by rfl⟩ : syracuseStep 282053 = 52885) (by norm_num)
theorem B249293 : Blo 163797 249293 := bbase (se 3 (by rfl) ⟨46742, by rfl⟩ : syracuseStep 249293 = 93485) (by norm_num)
theorem B314837 : Blo 163797 314837 := bbase (se 7 (by rfl) ⟨3689, by rfl⟩ : syracuseStep 314837 = 7379) (by norm_num)
theorem B249317 : Blo 163797 249317 := bbase (se 4 (by rfl) ⟨23373, by rfl⟩ : syracuseStep 249317 = 46747) (by norm_num)
theorem B675317 : Blo 163797 675317 := bbase (se 5 (by rfl) ⟨31655, by rfl⟩ : syracuseStep 675317 = 63311) (by norm_num)
theorem B249341 : Blo 163797 249341 := bbase (se 3 (by rfl) ⟨46751, by rfl⟩ : syracuseStep 249341 = 93503) (by norm_num)
theorem B282109 : Blo 163797 282109 := bbase (se 3 (by rfl) ⟨52895, by rfl⟩ : syracuseStep 282109 = 105791) (by norm_num)
theorem B249365 : Blo 163797 249365 := bbase (se 6 (by rfl) ⟨5844, by rfl⟩ : syracuseStep 249365 = 11689) (by norm_num)
theorem B249389 : Blo 163797 249389 := bbase (se 3 (by rfl) ⟨46760, by rfl⟩ : syracuseStep 249389 = 93521) (by norm_num)
theorem B249413 : Blo 163797 249413 := bbase (se 4 (by rfl) ⟨23382, by rfl⟩ : syracuseStep 249413 = 46765) (by norm_num)
theorem B282197 : Blo 163797 282197 := bbase (se 8 (by rfl) ⟨1653, by rfl⟩ : syracuseStep 282197 = 3307) (by norm_num)
theorem B249437 : Blo 163797 249437 := bbase (se 3 (by rfl) ⟨46769, by rfl⟩ : syracuseStep 249437 = 93539) (by norm_num)
theorem B609893 : Blo 163797 609893 := bbase (se 4 (by rfl) ⟨57177, by rfl⟩ : syracuseStep 609893 = 114355) (by norm_num)
theorem B446069 : Blo 163797 446069 := bbase (se 5 (by rfl) ⟨20909, by rfl⟩ : syracuseStep 446069 = 41819) (by norm_num)
theorem B249461 : Blo 163797 249461 := bbase (se 5 (by rfl) ⟨11693, by rfl⟩ : syracuseStep 249461 = 23387) (by norm_num)
theorem B675461 : Blo 163797 675461 := bbase (se 4 (by rfl) ⟨63324, by rfl⟩ : syracuseStep 675461 = 126649) (by norm_num)
theorem B249485 : Blo 163797 249485 := bbase (se 3 (by rfl) ⟨46778, by rfl⟩ : syracuseStep 249485 = 93557) (by norm_num)
theorem B249509 : Blo 163797 249509 := bbase (se 4 (by rfl) ⟨23391, by rfl⟩ : syracuseStep 249509 = 46783) (by norm_num)
theorem B249533 : Blo 163797 249533 := bbase (se 3 (by rfl) ⟨46787, by rfl⟩ : syracuseStep 249533 = 93575) (by norm_num)
theorem B249557 : Blo 163797 249557 := bbase (se 7 (by rfl) ⟨2924, by rfl⟩ : syracuseStep 249557 = 5849) (by norm_num)
theorem B282325 : Blo 163797 282325 := bbase (se 7 (by rfl) ⟨3308, by rfl⟩ : syracuseStep 282325 = 6617) (by norm_num)
theorem B249581 : Blo 163797 249581 := bbase (se 3 (by rfl) ⟨46796, by rfl⟩ : syracuseStep 249581 = 93593) (by norm_num)
theorem B249605 : Blo 163797 249605 := bbase (se 4 (by rfl) ⟨23400, by rfl⟩ : syracuseStep 249605 = 46801) (by norm_num)
theorem B249629 : Blo 163797 249629 := bbase (se 3 (by rfl) ⟨46805, by rfl⟩ : syracuseStep 249629 = 93611) (by norm_num)
theorem B282413 : Blo 163797 282413 := bbase (se 3 (by rfl) ⟨52952, by rfl⟩ : syracuseStep 282413 = 105905) (by norm_num)
theorem B249653 : Blo 163797 249653 := bbase (se 5 (by rfl) ⟨11702, by rfl⟩ : syracuseStep 249653 = 23405) (by norm_num)
theorem B249677 : Blo 163797 249677 := bbase (se 3 (by rfl) ⟨46814, by rfl⟩ : syracuseStep 249677 = 93629) (by norm_num)
theorem B249701 : Blo 163797 249701 := bbase (se 4 (by rfl) ⟨23409, by rfl⟩ : syracuseStep 249701 = 46819) (by norm_num)
theorem B249725 : Blo 163797 249725 := bbase (se 3 (by rfl) ⟨46823, by rfl⟩ : syracuseStep 249725 = 93647) (by norm_num)
theorem B249749 : Blo 163797 249749 := bbase (se 6 (by rfl) ⟨5853, by rfl⟩ : syracuseStep 249749 = 11707) (by norm_num)
theorem B249773 : Blo 163797 249773 := bbase (se 3 (by rfl) ⟨46832, by rfl⟩ : syracuseStep 249773 = 93665) (by norm_num)
theorem B282541 : Blo 163797 282541 := bbase (se 3 (by rfl) ⟨52976, by rfl⟩ : syracuseStep 282541 = 105953) (by norm_num)
theorem B249797 : Blo 163797 249797 := bbase (se 4 (by rfl) ⟨23418, by rfl⟩ : syracuseStep 249797 = 46837) (by norm_num)
theorem B249821 : Blo 163797 249821 := bbase (se 3 (by rfl) ⟨46841, by rfl⟩ : syracuseStep 249821 = 93683) (by norm_num)
theorem B184297 : Blo 163797 184297 := bbase (se 2 (by rfl) ⟨69111, by rfl⟩ : syracuseStep 184297 = 138223) (by norm_num)
theorem B249845 : Blo 163797 249845 := bbase (se 5 (by rfl) ⟨11711, by rfl⟩ : syracuseStep 249845 = 23423) (by norm_num)
theorem B282629 : Blo 163797 282629 := bbase (se 4 (by rfl) ⟨26496, by rfl⟩ : syracuseStep 282629 = 52993) (by norm_num)
theorem B184333 : Blo 163797 184333 := bbase (se 3 (by rfl) ⟨34562, by rfl⟩ : syracuseStep 184333 = 69125) (by norm_num)
theorem B249869 : Blo 163797 249869 := bbase (se 3 (by rfl) ⟨46850, by rfl⟩ : syracuseStep 249869 = 93701) (by norm_num)
theorem B249893 : Blo 163797 249893 := bbase (se 4 (by rfl) ⟨23427, by rfl⟩ : syracuseStep 249893 = 46855) (by norm_num)
theorem B184369 : Blo 163797 184369 := bbase (se 2 (by rfl) ⟨69138, by rfl⟩ : syracuseStep 184369 = 138277) (by norm_num)
theorem B249917 : Blo 163797 249917 := bbase (se 3 (by rfl) ⟨46859, by rfl⟩ : syracuseStep 249917 = 93719) (by norm_num)
theorem B184405 : Blo 163797 184405 := bbase (se 8 (by rfl) ⟨1080, by rfl⟩ : syracuseStep 184405 = 2161) (by norm_num)
theorem B249941 : Blo 163797 249941 := bbase (se 8 (by rfl) ⟨1464, by rfl⟩ : syracuseStep 249941 = 2929) (by norm_num)
theorem B708709 : Blo 163797 708709 := bbase (se 4 (by rfl) ⟨66441, by rfl⟩ : syracuseStep 708709 = 132883) (by norm_num)
theorem B249965 : Blo 163797 249965 := bbase (se 3 (by rfl) ⟨46868, by rfl⟩ : syracuseStep 249965 = 93737) (by norm_num)
theorem B708725 : Blo 163797 708725 := bbase (se 5 (by rfl) ⟨33221, by rfl⟩ : syracuseStep 708725 = 66443) (by norm_num)
theorem B184441 : Blo 163797 184441 := bbase (se 2 (by rfl) ⟨69165, by rfl⟩ : syracuseStep 184441 = 138331) (by norm_num)
theorem B249989 : Blo 163797 249989 := bbase (se 4 (by rfl) ⟨23436, by rfl⟩ : syracuseStep 249989 = 46873) (by norm_num)
theorem B282757 : Blo 163797 282757 := bbase (se 4 (by rfl) ⟨26508, by rfl⟩ : syracuseStep 282757 = 53017) (by norm_num)
theorem B184477 : Blo 163797 184477 := bbase (se 3 (by rfl) ⟨34589, by rfl⟩ : syracuseStep 184477 = 69179) (by norm_num)
theorem B250013 : Blo 163797 250013 := bbase (se 3 (by rfl) ⟨46877, by rfl⟩ : syracuseStep 250013 = 93755) (by norm_num)
theorem B250037 : Blo 163797 250037 := bbase (se 5 (by rfl) ⟨11720, by rfl⟩ : syracuseStep 250037 = 23441) (by norm_num)
theorem B184513 : Blo 163797 184513 := bbase (se 2 (by rfl) ⟨69192, by rfl⟩ : syracuseStep 184513 = 138385) (by norm_num)
theorem B315589 : Blo 163797 315589 := bbase (se 4 (by rfl) ⟨29586, by rfl⟩ : syracuseStep 315589 = 59173) (by norm_num)
theorem B250061 : Blo 163797 250061 := bbase (se 3 (by rfl) ⟨46886, by rfl⟩ : syracuseStep 250061 = 93773) (by norm_num)
theorem B282845 : Blo 163797 282845 := bbase (se 3 (by rfl) ⟨53033, by rfl⟩ : syracuseStep 282845 = 106067) (by norm_num)
theorem B184549 : Blo 163797 184549 := bbase (se 4 (by rfl) ⟨17301, by rfl⟩ : syracuseStep 184549 = 34603) (by norm_num)
theorem B250085 : Blo 163797 250085 := bbase (se 4 (by rfl) ⟨23445, by rfl⟩ : syracuseStep 250085 = 46891) (by norm_num)
theorem B250109 : Blo 163797 250109 := bbase (se 3 (by rfl) ⟨46895, by rfl⟩ : syracuseStep 250109 = 93791) (by norm_num)
theorem B184585 : Blo 163797 184585 := bbase (se 2 (by rfl) ⟨69219, by rfl⟩ : syracuseStep 184585 = 138439) (by norm_num)
theorem B250133 : Blo 163797 250133 := bbase (se 6 (by rfl) ⟨5862, by rfl⟩ : syracuseStep 250133 = 11725) (by norm_num)
theorem B184621 : Blo 163797 184621 := bbase (se 3 (by rfl) ⟨34616, by rfl⟩ : syracuseStep 184621 = 69233) (by norm_num)
theorem B250157 : Blo 163797 250157 := bbase (se 3 (by rfl) ⟨46904, by rfl⟩ : syracuseStep 250157 = 93809) (by norm_num)
theorem B250181 : Blo 163797 250181 := bbase (se 4 (by rfl) ⟨23454, by rfl⟩ : syracuseStep 250181 = 46909) (by norm_num)
theorem B184657 : Blo 163797 184657 := bbase (se 2 (by rfl) ⟨69246, by rfl⟩ : syracuseStep 184657 = 138493) (by norm_num)
theorem B315733 : Blo 163797 315733 := bbase (se 10 (by rfl) ⟨462, by rfl⟩ : syracuseStep 315733 = 925) (by norm_num)
theorem B250205 : Blo 163797 250205 := bbase (se 3 (by rfl) ⟨46913, by rfl⟩ : syracuseStep 250205 = 93827) (by norm_num)
theorem B282973 : Blo 163797 282973 := bbase (se 3 (by rfl) ⟨53057, by rfl⟩ : syracuseStep 282973 = 106115) (by norm_num)
theorem B184693 : Blo 163797 184693 := bbase (se 5 (by rfl) ⟨8657, by rfl⟩ : syracuseStep 184693 = 17315) (by norm_num)
theorem B250229 : Blo 163797 250229 := bbase (se 5 (by rfl) ⟨11729, by rfl⟩ : syracuseStep 250229 = 23459) (by norm_num)
theorem B250253 : Blo 163797 250253 := bbase (se 3 (by rfl) ⟨46922, by rfl⟩ : syracuseStep 250253 = 93845) (by norm_num)
theorem B184729 : Blo 163797 184729 := bbase (se 2 (by rfl) ⟨69273, by rfl⟩ : syracuseStep 184729 = 138547) (by norm_num)
theorem B250277 : Blo 163797 250277 := bbase (se 4 (by rfl) ⟨23463, by rfl⟩ : syracuseStep 250277 = 46927) (by norm_num)
theorem B283061 : Blo 163797 283061 := bbase (se 5 (by rfl) ⟨13268, by rfl⟩ : syracuseStep 283061 = 26537) (by norm_num)
theorem B184765 : Blo 163797 184765 := bbase (se 3 (by rfl) ⟨34643, by rfl⟩ : syracuseStep 184765 = 69287) (by norm_num)
theorem B250301 : Blo 163797 250301 := bbase (se 3 (by rfl) ⟨46931, by rfl⟩ : syracuseStep 250301 = 93863) (by norm_num)
theorem B250325 : Blo 163797 250325 := bbase (se 7 (by rfl) ⟨2933, by rfl⟩ : syracuseStep 250325 = 5867) (by norm_num)
theorem B184801 : Blo 163797 184801 := bbase (se 2 (by rfl) ⟨69300, by rfl⟩ : syracuseStep 184801 = 138601) (by norm_num)
theorem B250349 : Blo 163797 250349 := bbase (se 3 (by rfl) ⟨46940, by rfl⟩ : syracuseStep 250349 = 93881) (by norm_num)
theorem B315893 : Blo 163797 315893 := bbase (se 5 (by rfl) ⟨14807, by rfl⟩ : syracuseStep 315893 = 29615) (by norm_num)
theorem B184837 : Blo 163797 184837 := bbase (se 4 (by rfl) ⟨17328, by rfl⟩ : syracuseStep 184837 = 34657) (by norm_num)
theorem B250373 : Blo 163797 250373 := bbase (se 4 (by rfl) ⟨23472, by rfl⟩ : syracuseStep 250373 = 46945) (by norm_num)
theorem B250397 : Blo 163797 250397 := bbase (se 3 (by rfl) ⟨46949, by rfl⟩ : syracuseStep 250397 = 93899) (by norm_num)
theorem B184873 : Blo 163797 184873 := bbase (se 2 (by rfl) ⟨69327, by rfl⟩ : syracuseStep 184873 = 138655) (by norm_num)
theorem B250421 : Blo 163797 250421 := bbase (se 5 (by rfl) ⟨11738, by rfl⟩ : syracuseStep 250421 = 23477) (by norm_num)
theorem B184909 : Blo 163797 184909 := bbase (se 3 (by rfl) ⟨34670, by rfl⟩ : syracuseStep 184909 = 69341) (by norm_num)
theorem B250445 : Blo 163797 250445 := bbase (se 3 (by rfl) ⟨46958, by rfl⟩ : syracuseStep 250445 = 93917) (by norm_num)
theorem B840293 : Blo 163797 840293 := bbase (se 4 (by rfl) ⟨78777, by rfl⟩ : syracuseStep 840293 = 157555) (by norm_num)
theorem B250469 : Blo 163797 250469 := bbase (se 4 (by rfl) ⟨23481, by rfl⟩ : syracuseStep 250469 = 46963) (by norm_num)
theorem B184945 : Blo 163797 184945 := bbase (se 2 (by rfl) ⟨69354, by rfl⟩ : syracuseStep 184945 = 138709) (by norm_num)
theorem B250493 : Blo 163797 250493 := bbase (se 3 (by rfl) ⟨46967, by rfl⟩ : syracuseStep 250493 = 93935) (by norm_num)
theorem B316037 : Blo 163797 316037 := bbase (se 4 (by rfl) ⟨29628, by rfl⟩ : syracuseStep 316037 = 59257) (by norm_num)
theorem B184981 : Blo 163797 184981 := bbase (se 6 (by rfl) ⟨4335, by rfl⟩ : syracuseStep 184981 = 8671) (by norm_num)
theorem B250517 : Blo 163797 250517 := bbase (se 6 (by rfl) ⟨5871, by rfl⟩ : syracuseStep 250517 = 11743) (by norm_num)
theorem B250541 : Blo 163797 250541 := bbase (se 3 (by rfl) ⟨46976, by rfl⟩ : syracuseStep 250541 = 93953) (by norm_num)
theorem B348845 : Blo 163797 348845 := bbase (se 3 (by rfl) ⟨65408, by rfl⟩ : syracuseStep 348845 = 130817) (by norm_num)
theorem B185017 : Blo 163797 185017 := bbase (se 2 (by rfl) ⟨69381, by rfl⟩ : syracuseStep 185017 = 138763) (by norm_num)
theorem B250565 : Blo 163797 250565 := bbase (se 4 (by rfl) ⟨23490, by rfl⟩ : syracuseStep 250565 = 46981) (by norm_num)
theorem B185053 : Blo 163797 185053 := bbase (se 3 (by rfl) ⟨34697, by rfl⟩ : syracuseStep 185053 = 69395) (by norm_num)
theorem B250589 : Blo 163797 250589 := bbase (se 3 (by rfl) ⟨46985, by rfl⟩ : syracuseStep 250589 = 93971) (by norm_num)
theorem B250613 : Blo 163797 250613 := bbase (se 5 (by rfl) ⟨11747, by rfl⟩ : syracuseStep 250613 = 23495) (by norm_num)
theorem B185089 : Blo 163797 185089 := bbase (se 2 (by rfl) ⟨69408, by rfl⟩ : syracuseStep 185089 = 138817) (by norm_num)
theorem B250637 : Blo 163797 250637 := bbase (se 3 (by rfl) ⟨46994, by rfl⟩ : syracuseStep 250637 = 93989) (by norm_num)
theorem B185125 : Blo 163797 185125 := bbase (se 4 (by rfl) ⟨17355, by rfl⟩ : syracuseStep 185125 = 34711) (by norm_num)
theorem B250661 : Blo 163797 250661 := bbase (se 4 (by rfl) ⟨23499, by rfl⟩ : syracuseStep 250661 = 46999) (by norm_num)
theorem B250685 : Blo 163797 250685 := bbase (se 3 (by rfl) ⟨47003, by rfl⟩ : syracuseStep 250685 = 94007) (by norm_num)
theorem B185161 : Blo 163797 185161 := bbase (se 2 (by rfl) ⟨69435, by rfl⟩ : syracuseStep 185161 = 138871) (by norm_num)
theorem B250709 : Blo 163797 250709 := bbase (se 9 (by rfl) ⟨734, by rfl⟩ : syracuseStep 250709 = 1469) (by norm_num)
theorem B185197 : Blo 163797 185197 := bbase (se 3 (by rfl) ⟨34724, by rfl⟩ : syracuseStep 185197 = 69449) (by norm_num)
theorem B250733 : Blo 163797 250733 := bbase (se 3 (by rfl) ⟨47012, by rfl⟩ : syracuseStep 250733 = 94025) (by norm_num)
theorem B250757 : Blo 163797 250757 := bbase (se 4 (by rfl) ⟨23508, by rfl⟩ : syracuseStep 250757 = 47017) (by norm_num)
theorem B185233 : Blo 163797 185233 := bbase (se 2 (by rfl) ⟨69462, by rfl⟩ : syracuseStep 185233 = 138925) (by norm_num)
theorem B676757 : Blo 163797 676757 := bbase (se 6 (by rfl) ⟨15861, by rfl⟩ : syracuseStep 676757 = 31723) (by norm_num)
theorem B250781 : Blo 163797 250781 := bbase (se 3 (by rfl) ⟨47021, by rfl⟩ : syracuseStep 250781 = 94043) (by norm_num)
theorem B414629 : Blo 163797 414629 := bbase (se 4 (by rfl) ⟨38871, by rfl⟩ : syracuseStep 414629 = 77743) (by norm_num)
theorem B316325 : Blo 163797 316325 := bbase (se 4 (by rfl) ⟨29655, by rfl⟩ : syracuseStep 316325 = 59311) (by norm_num)
theorem B185269 : Blo 163797 185269 := bbase (se 5 (by rfl) ⟨8684, by rfl⟩ : syracuseStep 185269 = 17369) (by norm_num)
theorem B250805 : Blo 163797 250805 := bbase (se 5 (by rfl) ⟨11756, by rfl⟩ : syracuseStep 250805 = 23513) (by norm_num)
theorem B250829 : Blo 163797 250829 := bbase (se 3 (by rfl) ⟨47030, by rfl⟩ : syracuseStep 250829 = 94061) (by norm_num)
theorem B185305 : Blo 163797 185305 := bbase (se 2 (by rfl) ⟨69489, by rfl⟩ : syracuseStep 185305 = 138979) (by norm_num)
theorem B250853 : Blo 163797 250853 := bbase (se 4 (by rfl) ⟨23517, by rfl⟩ : syracuseStep 250853 = 47035) (by norm_num)
theorem B185341 : Blo 163797 185341 := bbase (se 3 (by rfl) ⟨34751, by rfl⟩ : syracuseStep 185341 = 69503) (by norm_num)
theorem B250877 : Blo 163797 250877 := bbase (se 3 (by rfl) ⟨47039, by rfl⟩ : syracuseStep 250877 = 94079) (by norm_num)
theorem B250901 : Blo 163797 250901 := bbase (se 6 (by rfl) ⟨5880, by rfl⟩ : syracuseStep 250901 = 11761) (by norm_num)
theorem B185377 : Blo 163797 185377 := bbase (se 2 (by rfl) ⟨69516, by rfl⟩ : syracuseStep 185377 = 139033) (by norm_num)
theorem B250925 : Blo 163797 250925 := bbase (se 3 (by rfl) ⟨47048, by rfl⟩ : syracuseStep 250925 = 94097) (by norm_num)
theorem B316477 : Blo 163797 316477 := bbase (se 3 (by rfl) ⟨59339, by rfl⟩ : syracuseStep 316477 = 118679) (by norm_num)
theorem B185413 : Blo 163797 185413 := bbase (se 4 (by rfl) ⟨17382, by rfl⟩ : syracuseStep 185413 = 34765) (by norm_num)
theorem B250949 : Blo 163797 250949 := bbase (se 4 (by rfl) ⟨23526, by rfl⟩ : syracuseStep 250949 = 47053) (by norm_num)
theorem B250973 : Blo 163797 250973 := bbase (se 3 (by rfl) ⟨47057, by rfl⟩ : syracuseStep 250973 = 94115) (by norm_num)
theorem B414821 : Blo 163797 414821 := bbase (se 4 (by rfl) ⟨38889, by rfl⟩ : syracuseStep 414821 = 77779) (by norm_num)
theorem B185449 : Blo 163797 185449 := bbase (se 2 (by rfl) ⟨69543, by rfl⟩ : syracuseStep 185449 = 139087) (by norm_num)
theorem B250997 : Blo 163797 250997 := bbase (se 5 (by rfl) ⟨11765, by rfl⟩ : syracuseStep 250997 = 23531) (by norm_num)
theorem B185485 : Blo 163797 185485 := bbase (se 3 (by rfl) ⟨34778, by rfl⟩ : syracuseStep 185485 = 69557) (by norm_num)
theorem B251021 : Blo 163797 251021 := bbase (se 3 (by rfl) ⟨47066, by rfl⟩ : syracuseStep 251021 = 94133) (by norm_num)
theorem B251045 : Blo 163797 251045 := bbase (se 4 (by rfl) ⟨23535, by rfl⟩ : syracuseStep 251045 = 47071) (by norm_num)
theorem B185521 : Blo 163797 185521 := bbase (se 2 (by rfl) ⟨69570, by rfl⟩ : syracuseStep 185521 = 139141) (by norm_num)
theorem B251069 : Blo 163797 251069 := bbase (se 3 (by rfl) ⟨47075, by rfl⟩ : syracuseStep 251069 = 94151) (by norm_num)
theorem B185557 : Blo 163797 185557 := bbase (se 7 (by rfl) ⟨2174, by rfl⟩ : syracuseStep 185557 = 4349) (by norm_num)
theorem B251093 : Blo 163797 251093 := bbase (se 7 (by rfl) ⟨2942, by rfl⟩ : syracuseStep 251093 = 5885) (by norm_num)
theorem B251117 : Blo 163797 251117 := bbase (se 3 (by rfl) ⟨47084, by rfl⟩ : syracuseStep 251117 = 94169) (by norm_num)
theorem B185593 : Blo 163797 185593 := bbase (se 2 (by rfl) ⟨69597, by rfl⟩ : syracuseStep 185593 = 139195) (by norm_num)
theorem B251141 : Blo 163797 251141 := bbase (se 4 (by rfl) ⟨23544, by rfl⟩ : syracuseStep 251141 = 47089) (by norm_num)
theorem B185629 : Blo 163797 185629 := bbase (se 3 (by rfl) ⟨34805, by rfl⟩ : syracuseStep 185629 = 69611) (by norm_num)
theorem B251165 : Blo 163797 251165 := bbase (se 3 (by rfl) ⟨47093, by rfl⟩ : syracuseStep 251165 = 94187) (by norm_num)
theorem B251189 : Blo 163797 251189 := bbase (se 5 (by rfl) ⟨11774, by rfl⟩ : syracuseStep 251189 = 23549) (by norm_num)
theorem B185665 : Blo 163797 185665 := bbase (se 2 (by rfl) ⟨69624, by rfl⟩ : syracuseStep 185665 = 139249) (by norm_num)
theorem B251213 : Blo 163797 251213 := bbase (se 3 (by rfl) ⟨47102, by rfl⟩ : syracuseStep 251213 = 94205) (by norm_num)
theorem B185701 : Blo 163797 185701 := bbase (se 4 (by rfl) ⟨17409, by rfl⟩ : syracuseStep 185701 = 34819) (by norm_num)
theorem B251237 : Blo 163797 251237 := bbase (se 4 (by rfl) ⟨23553, by rfl⟩ : syracuseStep 251237 = 47107) (by norm_num)
theorem B316781 : Blo 163797 316781 := bbase (se 3 (by rfl) ⟨59396, by rfl⟩ : syracuseStep 316781 = 118793) (by norm_num)
theorem B251261 : Blo 163797 251261 := bbase (se 3 (by rfl) ⟨47111, by rfl⟩ : syracuseStep 251261 = 94223) (by norm_num)
theorem B185737 : Blo 163797 185737 := bbase (se 2 (by rfl) ⟨69651, by rfl⟩ : syracuseStep 185737 = 139303) (by norm_num)
theorem B251285 : Blo 163797 251285 := bbase (se 6 (by rfl) ⟨5889, by rfl⟩ : syracuseStep 251285 = 11779) (by norm_num)
theorem B185773 : Blo 163797 185773 := bbase (se 3 (by rfl) ⟨34832, by rfl⟩ : syracuseStep 185773 = 69665) (by norm_num)
theorem B251309 : Blo 163797 251309 := bbase (se 3 (by rfl) ⟨47120, by rfl⟩ : syracuseStep 251309 = 94241) (by norm_num)
theorem B415165 : Blo 163797 415165 := bbase (se 3 (by rfl) ⟨77843, by rfl⟩ : syracuseStep 415165 = 155687) (by norm_num)
theorem B251333 : Blo 163797 251333 := bbase (se 4 (by rfl) ⟨23562, by rfl⟩ : syracuseStep 251333 = 47125) (by norm_num)
theorem B185809 : Blo 163797 185809 := bbase (se 2 (by rfl) ⟨69678, by rfl⟩ : syracuseStep 185809 = 139357) (by norm_num)
theorem B251357 : Blo 163797 251357 := bbase (se 3 (by rfl) ⟨47129, by rfl⟩ : syracuseStep 251357 = 94259) (by norm_num)
theorem B185845 : Blo 163797 185845 := bbase (se 5 (by rfl) ⟨8711, by rfl⟩ : syracuseStep 185845 = 17423) (by norm_num)
theorem B1136117 : Blo 163797 1136117 := bbase (se 5 (by rfl) ⟨53255, by rfl⟩ : syracuseStep 1136117 = 106511) (by norm_num)
theorem B251381 : Blo 163797 251381 := bbase (se 5 (by rfl) ⟨11783, by rfl⟩ : syracuseStep 251381 = 23567) (by norm_num)
theorem B251405 : Blo 163797 251405 := bbase (se 3 (by rfl) ⟨47138, by rfl⟩ : syracuseStep 251405 = 94277) (by norm_num)
theorem B185881 : Blo 163797 185881 := bbase (se 2 (by rfl) ⟨69705, by rfl⟩ : syracuseStep 185881 = 139411) (by norm_num)
theorem B251429 : Blo 163797 251429 := bbase (se 4 (by rfl) ⟨23571, by rfl⟩ : syracuseStep 251429 = 47143) (by norm_num)
theorem B415277 : Blo 163797 415277 := bbase (se 3 (by rfl) ⟨77864, by rfl⟩ : syracuseStep 415277 = 155729) (by norm_num)
theorem B185917 : Blo 163797 185917 := bbase (se 3 (by rfl) ⟨34859, by rfl⟩ : syracuseStep 185917 = 69719) (by norm_num)
theorem B251453 : Blo 163797 251453 := bbase (se 3 (by rfl) ⟨47147, by rfl⟩ : syracuseStep 251453 = 94295) (by norm_num)
theorem B251477 : Blo 163797 251477 := bbase (se 8 (by rfl) ⟨1473, by rfl⟩ : syracuseStep 251477 = 2947) (by norm_num)
theorem B185953 : Blo 163797 185953 := bbase (se 2 (by rfl) ⟨69732, by rfl⟩ : syracuseStep 185953 = 139465) (by norm_num)
theorem B251501 : Blo 163797 251501 := bbase (se 3 (by rfl) ⟨47156, by rfl⟩ : syracuseStep 251501 = 94313) (by norm_num)
theorem B185989 : Blo 163797 185989 := bbase (se 4 (by rfl) ⟨17436, by rfl⟩ : syracuseStep 185989 = 34873) (by norm_num)
theorem B251525 : Blo 163797 251525 := bbase (se 4 (by rfl) ⟨23580, by rfl⟩ : syracuseStep 251525 = 47161) (by norm_num)
theorem B251549 : Blo 163797 251549 := bbase (se 3 (by rfl) ⟨47165, by rfl⟩ : syracuseStep 251549 = 94331) (by norm_num)
theorem B186025 : Blo 163797 186025 := bbase (se 2 (by rfl) ⟨69759, by rfl⟩ : syracuseStep 186025 = 139519) (by norm_num)
theorem B251573 : Blo 163797 251573 := bbase (se 5 (by rfl) ⟨11792, by rfl⟩ : syracuseStep 251573 = 23585) (by norm_num)
theorem B186061 : Blo 163797 186061 := bbase (se 3 (by rfl) ⟨34886, by rfl⟩ : syracuseStep 186061 = 69773) (by norm_num)
theorem B251597 : Blo 163797 251597 := bbase (se 3 (by rfl) ⟨47174, by rfl⟩ : syracuseStep 251597 = 94349) (by norm_num)
theorem B677605 : Blo 163797 677605 := bbase (se 4 (by rfl) ⟨63525, by rfl⟩ : syracuseStep 677605 = 127051) (by norm_num)
theorem B251621 : Blo 163797 251621 := bbase (se 4 (by rfl) ⟨23589, by rfl⟩ : syracuseStep 251621 = 47179) (by norm_num)
theorem B415469 : Blo 163797 415469 := bbase (se 3 (by rfl) ⟨77900, by rfl⟩ : syracuseStep 415469 = 155801) (by norm_num)
theorem B186097 : Blo 163797 186097 := bbase (se 2 (by rfl) ⟨69786, by rfl⟩ : syracuseStep 186097 = 139573) (by norm_num)
theorem B906997 : Blo 163797 906997 := bbase (se 5 (by rfl) ⟨42515, by rfl⟩ : syracuseStep 906997 = 85031) (by norm_num)
theorem B251645 : Blo 163797 251645 := bbase (se 3 (by rfl) ⟨47183, by rfl⟩ : syracuseStep 251645 = 94367) (by norm_num)
theorem B186133 : Blo 163797 186133 := bbase (se 6 (by rfl) ⟨4362, by rfl⟩ : syracuseStep 186133 = 8725) (by norm_num)
theorem B251669 : Blo 163797 251669 := bbase (se 6 (by rfl) ⟨5898, by rfl⟩ : syracuseStep 251669 = 11797) (by norm_num)
theorem B251693 : Blo 163797 251693 := bbase (se 3 (by rfl) ⟨47192, by rfl⟩ : syracuseStep 251693 = 94385) (by norm_num)
theorem B186169 : Blo 163797 186169 := bbase (se 2 (by rfl) ⟨69813, by rfl⟩ : syracuseStep 186169 = 139627) (by norm_num)
theorem B186205 : Blo 163797 186205 := bbase (se 3 (by rfl) ⟨34913, by rfl⟩ : syracuseStep 186205 = 69827) (by norm_num)
theorem B841589 : Blo 163797 841589 := bbase (se 5 (by rfl) ⟨39449, by rfl⟩ : syracuseStep 841589 = 78899) (by norm_num)
theorem B186241 : Blo 163797 186241 := bbase (se 2 (by rfl) ⟨69840, by rfl⟩ : syracuseStep 186241 = 139681) (by norm_num)
theorem B186277 : Blo 163797 186277 := bbase (se 4 (by rfl) ⟨17463, by rfl⟩ : syracuseStep 186277 = 34927) (by norm_num)
theorem B186313 : Blo 163797 186313 := bbase (se 2 (by rfl) ⟨69867, by rfl⟩ : syracuseStep 186313 = 139735) (by norm_num)
theorem B186349 : Blo 163797 186349 := bbase (se 3 (by rfl) ⟨34940, by rfl⟩ : syracuseStep 186349 = 69881) (by norm_num)
theorem B186385 : Blo 163797 186385 := bbase (se 2 (by rfl) ⟨69894, by rfl⟩ : syracuseStep 186385 = 139789) (by norm_num)
theorem B186421 : Blo 163797 186421 := bbase (se 5 (by rfl) ⟨8738, by rfl⟩ : syracuseStep 186421 = 17477) (by norm_num)
theorem B415813 : Blo 163797 415813 := bbase (se 4 (by rfl) ⟨38982, by rfl⟩ : syracuseStep 415813 = 77965) (by norm_num)
theorem B186457 : Blo 163797 186457 := bbase (se 2 (by rfl) ⟨69921, by rfl⟩ : syracuseStep 186457 = 139843) (by norm_num)
theorem B317533 : Blo 163797 317533 := bbase (se 3 (by rfl) ⟨59537, by rfl⟩ : syracuseStep 317533 = 119075) (by norm_num)
theorem B186493 : Blo 163797 186493 := bbase (se 3 (by rfl) ⟨34967, by rfl⟩ : syracuseStep 186493 = 69935) (by norm_num)
theorem B350365 : Blo 163797 350365 := bbase (se 3 (by rfl) ⟨65693, by rfl⟩ : syracuseStep 350365 = 131387) (by norm_num)
theorem B186529 : Blo 163797 186529 := bbase (se 2 (by rfl) ⟨69948, by rfl⟩ : syracuseStep 186529 = 139897) (by norm_num)
theorem B415925 : Blo 163797 415925 := bbase (se 5 (by rfl) ⟨19496, by rfl⟩ : syracuseStep 415925 = 38993) (by norm_num)
theorem B186565 : Blo 163797 186565 := bbase (se 4 (by rfl) ⟨17490, by rfl⟩ : syracuseStep 186565 = 34981) (by norm_num)
theorem B186601 : Blo 163797 186601 := bbase (se 2 (by rfl) ⟨69975, by rfl⟩ : syracuseStep 186601 = 139951) (by norm_num)
theorem B317677 : Blo 163797 317677 := bbase (se 3 (by rfl) ⟨59564, by rfl⟩ : syracuseStep 317677 = 119129) (by norm_num)
theorem B186637 : Blo 163797 186637 := bbase (se 3 (by rfl) ⟨34994, by rfl⟩ : syracuseStep 186637 = 69989) (by norm_num)
theorem B186673 : Blo 163797 186673 := bbase (se 2 (by rfl) ⟨70002, by rfl⟩ : syracuseStep 186673 = 140005) (by norm_num)
theorem B710981 : Blo 163797 710981 := bbase (se 4 (by rfl) ⟨66654, by rfl⟩ : syracuseStep 710981 = 133309) (by norm_num)
theorem B186709 : Blo 163797 186709 := bbase (se 10 (by rfl) ⟨273, by rfl⟩ : syracuseStep 186709 = 547) (by norm_num)
theorem B416117 : Blo 163797 416117 := bbase (se 5 (by rfl) ⟨19505, by rfl⟩ : syracuseStep 416117 = 39011) (by norm_num)
theorem B186745 : Blo 163797 186745 := bbase (se 2 (by rfl) ⟨70029, by rfl⟩ : syracuseStep 186745 = 140059) (by norm_num)
theorem B317837 : Blo 163797 317837 := bbase (se 3 (by rfl) ⟨59594, by rfl⟩ : syracuseStep 317837 = 119189) (by norm_num)
theorem B186781 : Blo 163797 186781 := bbase (se 3 (by rfl) ⟨35021, by rfl⟩ : syracuseStep 186781 = 70043) (by norm_num)
theorem B186817 : Blo 163797 186817 := bbase (se 2 (by rfl) ⟨70056, by rfl⟩ : syracuseStep 186817 = 140113) (by norm_num)
theorem B3365333 : Blo 163797 3365333 := bbase (se 7 (by rfl) ⟨39437, by rfl⟩ : syracuseStep 3365333 = 78875) (by norm_num)
theorem B186853 : Blo 163797 186853 := bbase (se 4 (by rfl) ⟨17517, by rfl⟩ : syracuseStep 186853 = 35035) (by norm_num)
theorem B186889 : Blo 163797 186889 := bbase (se 2 (by rfl) ⟨70083, by rfl⟩ : syracuseStep 186889 = 140167) (by norm_num)
theorem B317981 : Blo 163797 317981 := bbase (se 3 (by rfl) ⟨59621, by rfl⟩ : syracuseStep 317981 = 119243) (by norm_num)
theorem B186925 : Blo 163797 186925 := bbase (se 3 (by rfl) ⟨35048, by rfl⟩ : syracuseStep 186925 = 70097) (by norm_num)
theorem B186961 : Blo 163797 186961 := bbase (se 2 (by rfl) ⟨70110, by rfl⟩ : syracuseStep 186961 = 140221) (by norm_num)
theorem B481877 : Blo 163797 481877 := bbase (se 8 (by rfl) ⟨2823, by rfl⟩ : syracuseStep 481877 = 5647) (by norm_num)
theorem B186997 : Blo 163797 186997 := bbase (se 5 (by rfl) ⟨8765, by rfl⟩ : syracuseStep 186997 = 17531) (by norm_num)
theorem B645749 : Blo 163797 645749 := bbase (se 5 (by rfl) ⟨30269, by rfl⟩ : syracuseStep 645749 = 60539) (by norm_num)
theorem B187033 : Blo 163797 187033 := bbase (se 2 (by rfl) ⟨70137, by rfl⟩ : syracuseStep 187033 = 140275) (by norm_num)
theorem B187069 : Blo 163797 187069 := bbase (se 3 (by rfl) ⟨35075, by rfl⟩ : syracuseStep 187069 = 70151) (by norm_num)
theorem B416461 : Blo 163797 416461 := bbase (se 3 (by rfl) ⟨78086, by rfl⟩ : syracuseStep 416461 = 156173) (by norm_num)
theorem B187105 : Blo 163797 187105 := bbase (se 2 (by rfl) ⟨70164, by rfl⟩ : syracuseStep 187105 = 140329) (by norm_num)
theorem B187141 : Blo 163797 187141 := bbase (se 4 (by rfl) ⟨17544, by rfl⟩ : syracuseStep 187141 = 35089) (by norm_num)
theorem B187177 : Blo 163797 187177 := bbase (se 2 (by rfl) ⟨70191, by rfl⟩ : syracuseStep 187177 = 140383) (by norm_num)
theorem B416573 : Blo 163797 416573 := bbase (se 3 (by rfl) ⟨78107, by rfl⟩ : syracuseStep 416573 = 156215) (by norm_num)
theorem B318269 : Blo 163797 318269 := bbase (se 3 (by rfl) ⟨59675, by rfl⟩ : syracuseStep 318269 = 119351) (by norm_num)
theorem B187213 : Blo 163797 187213 := bbase (se 3 (by rfl) ⟨35102, by rfl⟩ : syracuseStep 187213 = 70205) (by norm_num)
theorem B2087765 : Blo 163797 2087765 := bbase (se 9 (by rfl) ⟨6116, by rfl⟩ : syracuseStep 2087765 = 12233) (by norm_num)
theorem B187249 : Blo 163797 187249 := bbase (se 2 (by rfl) ⟨70218, by rfl⟩ : syracuseStep 187249 = 140437) (by norm_num)
theorem B187285 : Blo 163797 187285 := bbase (se 6 (by rfl) ⟨4389, by rfl⟩ : syracuseStep 187285 = 8779) (by norm_num)
theorem B187321 : Blo 163797 187321 := bbase (se 2 (by rfl) ⟨70245, by rfl⟩ : syracuseStep 187321 = 140491) (by norm_num)
theorem B318421 : Blo 163797 318421 := bbase (se 7 (by rfl) ⟨3731, by rfl⟩ : syracuseStep 318421 = 7463) (by norm_num)
theorem B187357 : Blo 163797 187357 := bbase (se 3 (by rfl) ⟨35129, by rfl⟩ : syracuseStep 187357 = 70259) (by norm_num)
theorem B416765 : Blo 163797 416765 := bbase (se 3 (by rfl) ⟨78143, by rfl⟩ : syracuseStep 416765 = 156287) (by norm_num)
theorem B187393 : Blo 163797 187393 := bbase (se 2 (by rfl) ⟨70272, by rfl⟩ : syracuseStep 187393 = 140545) (by norm_num)
theorem B351253 : Blo 163797 351253 := bbase (se 6 (by rfl) ⟨8232, by rfl⟩ : syracuseStep 351253 = 16465) (by norm_num)
theorem B187429 : Blo 163797 187429 := bbase (se 4 (by rfl) ⟨17571, by rfl⟩ : syracuseStep 187429 = 35143) (by norm_num)
theorem B187465 : Blo 163797 187465 := bbase (se 2 (by rfl) ⟨70299, by rfl⟩ : syracuseStep 187465 = 140599) (by norm_num)
theorem B187501 : Blo 163797 187501 := bbase (se 3 (by rfl) ⟨35156, by rfl⟩ : syracuseStep 187501 = 70313) (by norm_num)
theorem B187525 : Blo 163797 187525 := bbase (se 4 (by rfl) ⟨17580, by rfl⟩ : syracuseStep 187525 = 35161) (by norm_num)
theorem B842885 : Blo 163797 842885 := bbase (se 4 (by rfl) ⟨79020, by rfl⟩ : syracuseStep 842885 = 158041) (by norm_num)
theorem B351373 : Blo 163797 351373 := bbase (se 3 (by rfl) ⟨65882, by rfl⟩ : syracuseStep 351373 = 131765) (by norm_num)
theorem B187537 : Blo 163797 187537 := bbase (se 2 (by rfl) ⟨70326, by rfl⟩ : syracuseStep 187537 = 140653) (by norm_num)
theorem B187573 : Blo 163797 187573 := bbase (se 5 (by rfl) ⟨8792, by rfl⟩ : syracuseStep 187573 = 17585) (by norm_num)
theorem B515285 : Blo 163797 515285 := bbase (se 7 (by rfl) ⟨6038, by rfl⟩ : syracuseStep 515285 = 12077) (by norm_num)
theorem B187609 : Blo 163797 187609 := bbase (se 2 (by rfl) ⟨70353, by rfl⟩ : syracuseStep 187609 = 140707) (by norm_num)
theorem B187645 : Blo 163797 187645 := bbase (se 3 (by rfl) ⟨35183, by rfl⟩ : syracuseStep 187645 = 70367) (by norm_num)
theorem B187681 : Blo 163797 187681 := bbase (se 2 (by rfl) ⟨70380, by rfl⟩ : syracuseStep 187681 = 140761) (by norm_num)
theorem B187717 : Blo 163797 187717 := bbase (se 4 (by rfl) ⟨17598, by rfl⟩ : syracuseStep 187717 = 35197) (by norm_num)
theorem B417109 : Blo 163797 417109 := bbase (se 11 (by rfl) ⟨305, by rfl⟩ : syracuseStep 417109 = 611) (by norm_num)
theorem B187753 : Blo 163797 187753 := bbase (se 2 (by rfl) ⟨70407, by rfl⟩ : syracuseStep 187753 = 140815) (by norm_num)
theorem B351629 : Blo 163797 351629 := bbase (se 3 (by rfl) ⟨65930, by rfl⟩ : syracuseStep 351629 = 131861) (by norm_num)
theorem B187789 : Blo 163797 187789 := bbase (se 3 (by rfl) ⟨35210, by rfl⟩ : syracuseStep 187789 = 70421) (by norm_num)
theorem B187825 : Blo 163797 187825 := bbase (se 2 (by rfl) ⟨70434, by rfl⟩ : syracuseStep 187825 = 140869) (by norm_num)
theorem B417221 : Blo 163797 417221 := bbase (se 4 (by rfl) ⟨39114, by rfl⟩ : syracuseStep 417221 = 78229) (by norm_num)
theorem B187861 : Blo 163797 187861 := bbase (se 7 (by rfl) ⟨2201, by rfl⟩ : syracuseStep 187861 = 4403) (by norm_num)
theorem B187897 : Blo 163797 187897 := bbase (se 2 (by rfl) ⟨70461, by rfl⟩ : syracuseStep 187897 = 140923) (by norm_num)
theorem B187933 : Blo 163797 187933 := bbase (se 3 (by rfl) ⟨35237, by rfl⟩ : syracuseStep 187933 = 70475) (by norm_num)
theorem B187969 : Blo 163797 187969 := bbase (se 2 (by rfl) ⟨70488, by rfl⟩ : syracuseStep 187969 = 140977) (by norm_num)
theorem B188005 : Blo 163797 188005 := bbase (se 4 (by rfl) ⟨17625, by rfl⟩ : syracuseStep 188005 = 35251) (by norm_num)
theorem B417413 : Blo 163797 417413 := bbase (se 4 (by rfl) ⟨39132, by rfl⟩ : syracuseStep 417413 = 78265) (by norm_num)
theorem B188041 : Blo 163797 188041 := bbase (se 2 (by rfl) ⟨70515, by rfl⟩ : syracuseStep 188041 = 141031) (by norm_num)
theorem B286357 : Blo 163797 286357 := bbase (se 6 (by rfl) ⟨6711, by rfl⟩ : syracuseStep 286357 = 13423) (by norm_num)
theorem B188077 : Blo 163797 188077 := bbase (se 3 (by rfl) ⟨35264, by rfl⟩ : syracuseStep 188077 = 70529) (by norm_num)
theorem B188113 : Blo 163797 188113 := bbase (se 2 (by rfl) ⟨70542, by rfl⟩ : syracuseStep 188113 = 141085) (by norm_num)
theorem B188149 : Blo 163797 188149 := bbase (se 5 (by rfl) ⟨8819, by rfl⟩ : syracuseStep 188149 = 17639) (by norm_num)
theorem B188185 : Blo 163797 188185 := bbase (se 2 (by rfl) ⟨70569, by rfl⟩ : syracuseStep 188185 = 141139) (by norm_num)
theorem B188221 : Blo 163797 188221 := bbase (se 3 (by rfl) ⟨35291, by rfl⟩ : syracuseStep 188221 = 70583) (by norm_num)
theorem B188257 : Blo 163797 188257 := bbase (se 2 (by rfl) ⟨70596, by rfl⟩ : syracuseStep 188257 = 141193) (by norm_num)
theorem B188293 : Blo 163797 188293 := bbase (se 4 (by rfl) ⟨17652, by rfl⟩ : syracuseStep 188293 = 35305) (by norm_num)
theorem B188329 : Blo 163797 188329 := bbase (se 2 (by rfl) ⟨70623, by rfl⟩ : syracuseStep 188329 = 141247) (by norm_num)
theorem B319405 : Blo 163797 319405 := bbase (se 3 (by rfl) ⟨59888, by rfl⟩ : syracuseStep 319405 = 119777) (by norm_num)
theorem B188365 : Blo 163797 188365 := bbase (se 3 (by rfl) ⟨35318, by rfl⟩ : syracuseStep 188365 = 70637) (by norm_num)
theorem B417757 : Blo 163797 417757 := bbase (se 3 (by rfl) ⟨78329, by rfl⟩ : syracuseStep 417757 = 156659) (by norm_num)
theorem B188401 : Blo 163797 188401 := bbase (se 2 (by rfl) ⟨70650, by rfl⟩ : syracuseStep 188401 = 141301) (by norm_num)
theorem B188437 : Blo 163797 188437 := bbase (se 6 (by rfl) ⟨4416, by rfl⟩ : syracuseStep 188437 = 8833) (by norm_num)
theorem B188473 : Blo 163797 188473 := bbase (se 2 (by rfl) ⟨70677, by rfl⟩ : syracuseStep 188473 = 141355) (by norm_num)
theorem B417869 : Blo 163797 417869 := bbase (se 3 (by rfl) ⟨78350, by rfl⟩ : syracuseStep 417869 = 156701) (by norm_num)
theorem B188509 : Blo 163797 188509 := bbase (se 3 (by rfl) ⟨35345, by rfl⟩ : syracuseStep 188509 = 70691) (by norm_num)
theorem B450677 : Blo 163797 450677 := bbase (se 5 (by rfl) ⟨21125, by rfl⟩ : syracuseStep 450677 = 42251) (by norm_num)
theorem B188545 : Blo 163797 188545 := bbase (se 2 (by rfl) ⟨70704, by rfl⟩ : syracuseStep 188545 = 141409) (by norm_num)
theorem B188581 : Blo 163797 188581 := bbase (se 4 (by rfl) ⟨17679, by rfl⟩ : syracuseStep 188581 = 35359) (by norm_num)
theorem B188617 : Blo 163797 188617 := bbase (se 2 (by rfl) ⟨70731, by rfl⟩ : syracuseStep 188617 = 141463) (by norm_num)
theorem B188653 : Blo 163797 188653 := bbase (se 3 (by rfl) ⟨35372, by rfl⟩ : syracuseStep 188653 = 70745) (by norm_num)
theorem B352517 : Blo 163797 352517 := bbase (se 4 (by rfl) ⟨33048, by rfl⟩ : syracuseStep 352517 = 66097) (by norm_num)
theorem B418061 : Blo 163797 418061 := bbase (se 3 (by rfl) ⟨78386, by rfl⟩ : syracuseStep 418061 = 156773) (by norm_num)
theorem B188689 : Blo 163797 188689 := bbase (se 2 (by rfl) ⟨70758, by rfl⟩ : syracuseStep 188689 = 141517) (by norm_num)
theorem B188725 : Blo 163797 188725 := bbase (se 5 (by rfl) ⟨8846, by rfl⟩ : syracuseStep 188725 = 17693) (by norm_num)
theorem B188761 : Blo 163797 188761 := bbase (se 2 (by rfl) ⟨70785, by rfl⟩ : syracuseStep 188761 = 141571) (by norm_num)
theorem B483685 : Blo 163797 483685 := bbase (se 4 (by rfl) ⟨45345, by rfl⟩ : syracuseStep 483685 = 90691) (by norm_num)
theorem B844181 : Blo 163797 844181 := bbase (se 6 (by rfl) ⟨19785, by rfl⟩ : syracuseStep 844181 = 39571) (by norm_num)
theorem B352757 : Blo 163797 352757 := bbase (se 5 (by rfl) ⟨16535, by rfl⟩ : syracuseStep 352757 = 33071) (by norm_num)
theorem B1073749 : Blo 163797 1073749 := bbase (se 8 (by rfl) ⟨6291, by rfl⟩ : syracuseStep 1073749 = 12583) (by norm_num)
theorem B418405 : Blo 163797 418405 := bbase (se 4 (by rfl) ⟨39225, by rfl⟩ : syracuseStep 418405 = 78451) (by norm_num)
theorem B418517 : Blo 163797 418517 := bbase (se 7 (by rfl) ⟨4904, by rfl⟩ : syracuseStep 418517 = 9809) (by norm_num)
theorem B189317 : Blo 163797 189317 := bbase (se 4 (by rfl) ⟨17748, by rfl⟩ : syracuseStep 189317 = 35497) (by norm_num)
theorem B418709 : Blo 163797 418709 := bbase (se 6 (by rfl) ⟨9813, by rfl⟩ : syracuseStep 418709 = 19627) (by norm_num)
theorem B254917 : Blo 163797 254917 := bbase (se 4 (by rfl) ⟨23898, by rfl⟩ : syracuseStep 254917 = 47797) (by norm_num)
theorem B353261 : Blo 163797 353261 := bbase (se 3 (by rfl) ⟨66236, by rfl⟩ : syracuseStep 353261 = 132473) (by norm_num)
theorem B353269 : Blo 163797 353269 := bbase (se 5 (by rfl) ⟨16559, by rfl⟩ : syracuseStep 353269 = 33119) (by norm_num)
theorem B419053 : Blo 163797 419053 := bbase (se 3 (by rfl) ⟨78572, by rfl⟩ : syracuseStep 419053 = 157145) (by norm_num)
theorem B419165 : Blo 163797 419165 := bbase (se 3 (by rfl) ⟨78593, by rfl⟩ : syracuseStep 419165 = 157187) (by norm_num)
theorem B189901 : Blo 163797 189901 := bbase (se 3 (by rfl) ⟨35606, by rfl⟩ : syracuseStep 189901 = 71213) (by norm_num)
theorem B419357 : Blo 163797 419357 := bbase (se 3 (by rfl) ⟨78629, by rfl⟩ : syracuseStep 419357 = 157259) (by norm_num)
theorem B222797 : Blo 163797 222797 := bbase (se 3 (by rfl) ⟨41774, by rfl⟩ : syracuseStep 222797 = 83549) (by norm_num)
theorem B845477 : Blo 163797 845477 := bbase (se 4 (by rfl) ⟨79263, by rfl⟩ : syracuseStep 845477 = 158527) (by norm_num)
theorem B419701 : Blo 163797 419701 := bbase (se 5 (by rfl) ⟨19673, by rfl⟩ : syracuseStep 419701 = 39347) (by norm_num)
theorem B419813 : Blo 163797 419813 := bbase (se 4 (by rfl) ⟨39357, by rfl⟩ : syracuseStep 419813 = 78715) (by norm_num)
theorem B190517 : Blo 163797 190517 := bbase (se 5 (by rfl) ⟨8930, by rfl⟩ : syracuseStep 190517 = 17861) (by norm_num)
theorem B1271861 : Blo 163797 1271861 := bbase (se 5 (by rfl) ⟨59618, by rfl⟩ : syracuseStep 1271861 = 119237) (by norm_num)
theorem B354397 : Blo 163797 354397 := bbase (se 3 (by rfl) ⟨66449, by rfl⟩ : syracuseStep 354397 = 132899) (by norm_num)
theorem B911477 : Blo 163797 911477 := bbase (se 5 (by rfl) ⟨42725, by rfl⟩ : syracuseStep 911477 = 85451) (by norm_num)
theorem B420005 : Blo 163797 420005 := bbase (se 4 (by rfl) ⟨39375, by rfl⟩ : syracuseStep 420005 = 78751) (by norm_num)
theorem B3565781 : Blo 163797 3565781 := bbase (se 7 (by rfl) ⟨41786, by rfl⟩ : syracuseStep 3565781 = 83573) (by norm_num)
theorem B715013 : Blo 163797 715013 := bbase (se 4 (by rfl) ⟨67032, by rfl⟩ : syracuseStep 715013 = 134065) (by norm_num)
theorem B354773 : Blo 163797 354773 := bbase (se 7 (by rfl) ⟨4157, by rfl⟩ : syracuseStep 354773 = 8315) (by norm_num)
theorem B420349 : Blo 163797 420349 := bbase (se 3 (by rfl) ⟨78815, by rfl⟩ : syracuseStep 420349 = 157631) (by norm_num)
theorem B944693 : Blo 163797 944693 := bbase (se 5 (by rfl) ⟨44282, by rfl⟩ : syracuseStep 944693 = 88565) (by norm_num)
theorem B453205 : Blo 163797 453205 := bbase (se 8 (by rfl) ⟨2655, by rfl⟩ : syracuseStep 453205 = 5311) (by norm_num)
theorem B420461 : Blo 163797 420461 := bbase (se 3 (by rfl) ⟨78836, by rfl⟩ : syracuseStep 420461 = 157673) (by norm_num)
theorem B224029 : Blo 163797 224029 := bbase (se 3 (by rfl) ⟨42005, by rfl⟩ : syracuseStep 224029 = 84011) (by norm_num)
theorem B420653 : Blo 163797 420653 := bbase (se 3 (by rfl) ⟨78872, by rfl⟩ : syracuseStep 420653 = 157745) (by norm_num)
theorem B846773 : Blo 163797 846773 := bbase (se 5 (by rfl) ⟨39692, by rfl⟩ : syracuseStep 846773 = 79385) (by norm_num)
theorem B191489 : Blo 163797 191489 := bbase (se 2 (by rfl) ⟨71808, by rfl⟩ : syracuseStep 191489 = 143617) (by norm_num)
theorem B420997 : Blo 163797 420997 := bbase (se 4 (by rfl) ⟨39468, by rfl⟩ : syracuseStep 420997 = 78937) (by norm_num)
theorem B421109 : Blo 163797 421109 := bbase (se 5 (by rfl) ⟨19739, by rfl⟩ : syracuseStep 421109 = 39479) (by norm_num)
theorem B421301 : Blo 163797 421301 := bbase (se 5 (by rfl) ⟨19748, by rfl⟩ : syracuseStep 421301 = 39497) (by norm_num)
theorem B355909 : Blo 163797 355909 := bbase (se 4 (by rfl) ⟨33366, by rfl⟩ : syracuseStep 355909 = 66733) (by norm_num)
theorem B945877 : Blo 163797 945877 := bbase (se 7 (by rfl) ⟨11084, by rfl⟩ : syracuseStep 945877 = 22169) (by norm_num)
theorem B421613 : Blo 163797 421613 := bbase (se 3 (by rfl) ⟨79052, by rfl⟩ : syracuseStep 421613 = 158105) (by norm_num)
theorem B421645 : Blo 163797 421645 := bbase (se 3 (by rfl) ⟨79058, by rfl⟩ : syracuseStep 421645 = 158117) (by norm_num)
theorem B716597 : Blo 163797 716597 := bbase (se 5 (by rfl) ⟨33590, by rfl⟩ : syracuseStep 716597 = 67181) (by norm_num)
theorem B421757 : Blo 163797 421757 := bbase (se 3 (by rfl) ⟨79079, by rfl⟩ : syracuseStep 421757 = 158159) (by norm_num)
theorem B553013 : Blo 163797 553013 := bbase (se 5 (by rfl) ⟨25922, by rfl⟩ : syracuseStep 553013 = 51845) (by norm_num)
theorem B421949 : Blo 163797 421949 := bbase (se 3 (by rfl) ⟨79115, by rfl⟩ : syracuseStep 421949 = 158231) (by norm_num)
theorem B356413 : Blo 163797 356413 := bbase (se 3 (by rfl) ⟨66827, by rfl⟩ : syracuseStep 356413 = 133655) (by norm_num)
theorem B422021 : Blo 163797 422021 := bbase (se 4 (by rfl) ⟨39564, by rfl⟩ : syracuseStep 422021 = 79129) (by norm_num)
theorem B848069 : Blo 163797 848069 := bbase (se 4 (by rfl) ⟨79506, by rfl⟩ : syracuseStep 848069 = 159013) (by norm_num)
theorem B422293 : Blo 163797 422293 := bbase (se 6 (by rfl) ⟨9897, by rfl⟩ : syracuseStep 422293 = 19795) (by norm_num)
theorem B553445 : Blo 163797 553445 := bbase (se 4 (by rfl) ⟨51885, by rfl⟩ : syracuseStep 553445 = 103771) (by norm_num)
theorem B422405 : Blo 163797 422405 := bbase (se 4 (by rfl) ⟨39600, by rfl⟩ : syracuseStep 422405 = 79201) (by norm_num)
theorem B422597 : Blo 163797 422597 := bbase (se 4 (by rfl) ⟨39618, by rfl⟩ : syracuseStep 422597 = 79237) (by norm_num)
theorem B1504021 : Blo 163797 1504021 := bbase (se 6 (by rfl) ⟨35250, by rfl⟩ : syracuseStep 1504021 = 70501) (by norm_num)
theorem B750389 : Blo 163797 750389 := bbase (se 5 (by rfl) ⟨35174, by rfl⟩ : syracuseStep 750389 = 70349) (by norm_num)
theorem B553877 : Blo 163797 553877 := bbase (se 6 (by rfl) ⟨12981, by rfl⟩ : syracuseStep 553877 = 25963) (by norm_num)
theorem B357301 : Blo 163797 357301 := bbase (se 5 (by rfl) ⟨16748, by rfl⟩ : syracuseStep 357301 = 33497) (by norm_num)
theorem B422941 : Blo 163797 422941 := bbase (se 3 (by rfl) ⟨79301, by rfl⟩ : syracuseStep 422941 = 158603) (by norm_num)
theorem B423053 : Blo 163797 423053 := bbase (se 3 (by rfl) ⟨79322, by rfl⟩ : syracuseStep 423053 = 158645) (by norm_num)
theorem B554309 : Blo 163797 554309 := bbase (se 4 (by rfl) ⟨51966, by rfl⟩ : syracuseStep 554309 = 103933) (by norm_num)
theorem B423245 : Blo 163797 423245 := bbase (se 3 (by rfl) ⟨79358, by rfl⟩ : syracuseStep 423245 = 158717) (by norm_num)
theorem B357797 : Blo 163797 357797 := bbase (se 4 (by rfl) ⟨33543, by rfl⟩ : syracuseStep 357797 = 67087) (by norm_num)
theorem B849365 : Blo 163797 849365 := bbase (se 7 (by rfl) ⟨9953, by rfl⟩ : syracuseStep 849365 = 19907) (by norm_num)
theorem B947861 : Blo 163797 947861 := bbase (se 6 (by rfl) ⟨22215, by rfl⟩ : syracuseStep 947861 = 44431) (by norm_num)
theorem B423589 : Blo 163797 423589 := bbase (se 4 (by rfl) ⟨39711, by rfl⟩ : syracuseStep 423589 = 79423) (by norm_num)
theorem B554741 : Blo 163797 554741 := bbase (se 5 (by rfl) ⟨26003, by rfl⟩ : syracuseStep 554741 = 52007) (by norm_num)
theorem B423701 : Blo 163797 423701 := bbase (se 6 (by rfl) ⟨9930, by rfl⟩ : syracuseStep 423701 = 19861) (by norm_num)
theorem B423893 : Blo 163797 423893 := bbase (se 7 (by rfl) ⟨4967, by rfl⟩ : syracuseStep 423893 = 9935) (by norm_num)
theorem B555173 : Blo 163797 555173 := bbase (se 4 (by rfl) ⟨52047, by rfl⟩ : syracuseStep 555173 = 104095) (by norm_num)
theorem B424237 : Blo 163797 424237 := bbase (se 3 (by rfl) ⟨79544, by rfl⟩ : syracuseStep 424237 = 159089) (by norm_num)
theorem B424261 : Blo 163797 424261 := bbase (se 4 (by rfl) ⟨39774, by rfl⟩ : syracuseStep 424261 = 79549) (by norm_num)
theorem B424349 : Blo 163797 424349 := bbase (se 3 (by rfl) ⟨79565, by rfl⟩ : syracuseStep 424349 = 159131) (by norm_num)
theorem B555605 : Blo 163797 555605 := bbase (se 8 (by rfl) ⟨3255, by rfl⟩ : syracuseStep 555605 = 6511) (by norm_num)
theorem B424541 : Blo 163797 424541 := bbase (se 3 (by rfl) ⟨79601, by rfl⟩ : syracuseStep 424541 = 159203) (by norm_num)
theorem B556037 : Blo 163797 556037 := bbase (se 4 (by rfl) ⟨52128, by rfl⟩ : syracuseStep 556037 = 104257) (by norm_num)
theorem B1440949 : Blo 163797 1440949 := bbase (se 5 (by rfl) ⟨67544, by rfl⟩ : syracuseStep 1440949 = 135089) (by norm_num)
theorem B425245 : Blo 163797 425245 := bbase (se 3 (by rfl) ⟨79733, by rfl⟩ : syracuseStep 425245 = 159467) (by norm_num)
theorem B621989 : Blo 163797 621989 := bbase (se 4 (by rfl) ⟨58311, by rfl⟩ : syracuseStep 621989 = 116623) (by norm_num)
theorem B556469 : Blo 163797 556469 := bbase (se 5 (by rfl) ⟨26084, by rfl⟩ : syracuseStep 556469 = 52169) (by norm_num)
theorem B1703605 : Blo 163797 1703605 := bbase (se 5 (by rfl) ⟨79856, by rfl⟩ : syracuseStep 1703605 = 159713) (by norm_num)
theorem B294701 : Blo 163797 294701 := bbase (se 3 (by rfl) ⟨55256, by rfl⟩ : syracuseStep 294701 = 110513) (by norm_num)
theorem B950069 : Blo 163797 950069 := bbase (se 5 (by rfl) ⟨44534, by rfl⟩ : syracuseStep 950069 = 89069) (by norm_num)
theorem B556901 : Blo 163797 556901 := bbase (se 4 (by rfl) ⟨52209, by rfl⟩ : syracuseStep 556901 = 104419) (by norm_num)
theorem B163843 : Blo 163797 163843 := bstep (se 1 (by rfl) ⟨122882, by rfl⟩ : syracuseStep 163843 = 245765) B245765
theorem B163859 : Blo 163797 163859 := bstep (se 1 (by rfl) ⟨122894, by rfl⟩ : syracuseStep 163859 = 245789) B245789
theorem B163875 : Blo 163797 163875 := bstep (se 1 (by rfl) ⟨122906, by rfl⟩ : syracuseStep 163875 = 245813) B245813
theorem B163891 : Blo 163797 163891 := bstep (se 1 (by rfl) ⟨122918, by rfl⟩ : syracuseStep 163891 = 245837) B245837
theorem B163907 : Blo 163797 163907 := bstep (se 1 (by rfl) ⟨122930, by rfl⟩ : syracuseStep 163907 = 245861) B245861
theorem B163923 : Blo 163797 163923 := bstep (se 1 (by rfl) ⟨122942, by rfl⟩ : syracuseStep 163923 = 245885) B245885
theorem B163939 : Blo 163797 163939 := bstep (se 1 (by rfl) ⟨122954, by rfl⟩ : syracuseStep 163939 = 245909) B245909
theorem B163955 : Blo 163797 163955 := bstep (se 1 (by rfl) ⟨122966, by rfl⟩ : syracuseStep 163955 = 245933) B245933
theorem B163971 : Blo 163797 163971 := bstep (se 1 (by rfl) ⟨122978, by rfl⟩ : syracuseStep 163971 = 245957) B245957
theorem B163987 : Blo 163797 163987 := bstep (se 1 (by rfl) ⟨122990, by rfl⟩ : syracuseStep 163987 = 245981) B245981
theorem B164003 : Blo 163797 164003 := bstep (se 1 (by rfl) ⟨123002, by rfl⟩ : syracuseStep 164003 = 246005) B246005
theorem B164019 : Blo 163797 164019 := bstep (se 1 (by rfl) ⟨123014, by rfl⟩ : syracuseStep 164019 = 246029) B246029
theorem B164035 : Blo 163797 164035 := bstep (se 1 (by rfl) ⟨123026, by rfl⟩ : syracuseStep 164035 = 246053) B246053
theorem B164051 : Blo 163797 164051 := bstep (se 1 (by rfl) ⟨123038, by rfl⟩ : syracuseStep 164051 = 246077) B246077
theorem B164067 : Blo 163797 164067 := bstep (se 1 (by rfl) ⟨123050, by rfl⟩ : syracuseStep 164067 = 246101) B246101
theorem B164083 : Blo 163797 164083 := bstep (se 1 (by rfl) ⟨123062, by rfl⟩ : syracuseStep 164083 = 246125) B246125
theorem B164099 : Blo 163797 164099 := bstep (se 1 (by rfl) ⟨123074, by rfl⟩ : syracuseStep 164099 = 246149) B246149
theorem B164115 : Blo 163797 164115 := bstep (se 1 (by rfl) ⟨123086, by rfl⟩ : syracuseStep 164115 = 246173) B246173
theorem B262435 : Blo 163797 262435 := bstep (se 1 (by rfl) ⟨196826, by rfl⟩ : syracuseStep 262435 = 393653) B393653
theorem B164131 : Blo 163797 164131 := bstep (se 1 (by rfl) ⟨123098, by rfl⟩ : syracuseStep 164131 = 246197) B246197
theorem B164147 : Blo 163797 164147 := bstep (se 1 (by rfl) ⟨123110, by rfl⟩ : syracuseStep 164147 = 246221) B246221
theorem B164163 : Blo 163797 164163 := bstep (se 1 (by rfl) ⟨123122, by rfl⟩ : syracuseStep 164163 = 246245) B246245
theorem B164179 : Blo 163797 164179 := bstep (se 1 (by rfl) ⟨123134, by rfl⟩ : syracuseStep 164179 = 246269) B246269
theorem B164195 : Blo 163797 164195 := bstep (se 1 (by rfl) ⟨123146, by rfl⟩ : syracuseStep 164195 = 246293) B246293
theorem B622961 : Blo 163797 622961 := bstep (se 2 (by rfl) ⟨233610, by rfl⟩ : syracuseStep 622961 = 467221) B467221
theorem B164211 : Blo 163797 164211 := bstep (se 1 (by rfl) ⟨123158, by rfl⟩ : syracuseStep 164211 = 246317) B246317
theorem B164227 : Blo 163797 164227 := bstep (se 1 (by rfl) ⟨123170, by rfl⟩ : syracuseStep 164227 = 246341) B246341
theorem B3015053 : Blo 163797 3015053 := bstep (se 3 (by rfl) ⟨565322, by rfl⟩ : syracuseStep 3015053 = 1130645) B1130645
theorem B164243 : Blo 163797 164243 := bstep (se 1 (by rfl) ⟨123182, by rfl⟩ : syracuseStep 164243 = 246365) B246365
theorem B164259 : Blo 163797 164259 := bstep (se 1 (by rfl) ⟨123194, by rfl⟩ : syracuseStep 164259 = 246389) B246389
theorem B164275 : Blo 163797 164275 := bstep (se 1 (by rfl) ⟨123206, by rfl⟩ : syracuseStep 164275 = 246413) B246413
theorem B164291 : Blo 163797 164291 := bstep (se 1 (by rfl) ⟨123218, by rfl⟩ : syracuseStep 164291 = 246437) B246437
theorem B164307 : Blo 163797 164307 := bstep (se 1 (by rfl) ⟨123230, by rfl⟩ : syracuseStep 164307 = 246461) B246461
theorem B164323 : Blo 163797 164323 := bstep (se 1 (by rfl) ⟨123242, by rfl⟩ : syracuseStep 164323 = 246485) B246485
theorem B360931 : Blo 163797 360931 := bstep (se 1 (by rfl) ⟨270698, by rfl⟩ : syracuseStep 360931 = 541397) B541397
theorem B557549 : Blo 163797 557549 := bstep (se 3 (by rfl) ⟨104540, by rfl⟩ : syracuseStep 557549 = 209081) B209081
theorem B1409521 : Blo 163797 1409521 := bstep (se 2 (by rfl) ⟨528570, by rfl⟩ : syracuseStep 1409521 = 1057141) B1057141
theorem B164339 : Blo 163797 164339 := bstep (se 1 (by rfl) ⟨123254, by rfl⟩ : syracuseStep 164339 = 246509) B246509
theorem B164355 : Blo 163797 164355 := bstep (se 1 (by rfl) ⟨123266, by rfl⟩ : syracuseStep 164355 = 246533) B246533
theorem B164371 : Blo 163797 164371 := bstep (se 1 (by rfl) ⟨123278, by rfl⟩ : syracuseStep 164371 = 246557) B246557
theorem B262691 : Blo 163797 262691 := bstep (se 1 (by rfl) ⟨197018, by rfl⟩ : syracuseStep 262691 = 394037) B394037
theorem B164387 : Blo 163797 164387 := bstep (se 1 (by rfl) ⟨123290, by rfl⟩ : syracuseStep 164387 = 246581) B246581
theorem B557603 : Blo 163797 557603 := bstep (se 1 (by rfl) ⟨418202, by rfl⟩ : syracuseStep 557603 = 836405) B836405
theorem B164403 : Blo 163797 164403 := bstep (se 1 (by rfl) ⟨123302, by rfl⟩ : syracuseStep 164403 = 246605) B246605
theorem B164419 : Blo 163797 164419 := bstep (se 1 (by rfl) ⟨123314, by rfl⟩ : syracuseStep 164419 = 246629) B246629
theorem B164435 : Blo 163797 164435 := bstep (se 1 (by rfl) ⟨123326, by rfl⟩ : syracuseStep 164435 = 246653) B246653
theorem B590435 : Blo 163797 590435 := bstep (se 1 (by rfl) ⟨442826, by rfl⟩ : syracuseStep 590435 = 885653) B885653
theorem B164451 : Blo 163797 164451 := bstep (se 1 (by rfl) ⟨123338, by rfl⟩ : syracuseStep 164451 = 246677) B246677
theorem B164467 : Blo 163797 164467 := bstep (se 1 (by rfl) ⟨123350, by rfl⟩ : syracuseStep 164467 = 246701) B246701
theorem B164483 : Blo 163797 164483 := bstep (se 1 (by rfl) ⟨123362, by rfl⟩ : syracuseStep 164483 = 246725) B246725
theorem B164499 : Blo 163797 164499 := bstep (se 1 (by rfl) ⟨123374, by rfl⟩ : syracuseStep 164499 = 246749) B246749
theorem B164515 : Blo 163797 164515 := bstep (se 1 (by rfl) ⟨123386, by rfl⟩ : syracuseStep 164515 = 246773) B246773
theorem B164531 : Blo 163797 164531 := bstep (se 1 (by rfl) ⟨123398, by rfl⟩ : syracuseStep 164531 = 246797) B246797
theorem B164547 : Blo 163797 164547 := bstep (se 1 (by rfl) ⟨123410, by rfl⟩ : syracuseStep 164547 = 246821) B246821
theorem B164563 : Blo 163797 164563 := bstep (se 1 (by rfl) ⟨123422, by rfl⟩ : syracuseStep 164563 = 246845) B246845
theorem B164579 : Blo 163797 164579 := bstep (se 1 (by rfl) ⟨123434, by rfl⟩ : syracuseStep 164579 = 246869) B246869
theorem B164595 : Blo 163797 164595 := bstep (se 1 (by rfl) ⟨123446, by rfl⟩ : syracuseStep 164595 = 246893) B246893
theorem B164611 : Blo 163797 164611 := bstep (se 1 (by rfl) ⟨123458, by rfl⟩ : syracuseStep 164611 = 246917) B246917
theorem B164627 : Blo 163797 164627 := bstep (se 1 (by rfl) ⟨123470, by rfl⟩ : syracuseStep 164627 = 246941) B246941
theorem B164643 : Blo 163797 164643 := bstep (se 1 (by rfl) ⟨123482, by rfl⟩ : syracuseStep 164643 = 246965) B246965
theorem B557873 : Blo 163797 557873 := bstep (se 2 (by rfl) ⟨209202, by rfl⟩ : syracuseStep 557873 = 418405) B418405
theorem B164659 : Blo 163797 164659 := bstep (se 1 (by rfl) ⟨123494, by rfl⟩ : syracuseStep 164659 = 246989) B246989
theorem B164675 : Blo 163797 164675 := bstep (se 1 (by rfl) ⟨123506, by rfl⟩ : syracuseStep 164675 = 247013) B247013
theorem B164691 : Blo 163797 164691 := bstep (se 1 (by rfl) ⟨123518, by rfl⟩ : syracuseStep 164691 = 247037) B247037
theorem B164707 : Blo 163797 164707 := bstep (se 1 (by rfl) ⟨123530, by rfl⟩ : syracuseStep 164707 = 247061) B247061
theorem B1016675 : Blo 163797 1016675 := bstep (se 1 (by rfl) ⟨762506, by rfl⟩ : syracuseStep 1016675 = 1525013) B1525013
theorem B164723 : Blo 163797 164723 := bstep (se 1 (by rfl) ⟨123542, by rfl⟩ : syracuseStep 164723 = 247085) B247085
theorem B164739 : Blo 163797 164739 := bstep (se 1 (by rfl) ⟨123554, by rfl⟩ : syracuseStep 164739 = 247109) B247109
theorem B164755 : Blo 163797 164755 := bstep (se 1 (by rfl) ⟨123566, by rfl⟩ : syracuseStep 164755 = 247133) B247133
theorem B164771 : Blo 163797 164771 := bstep (se 1 (by rfl) ⟨123578, by rfl⟩ : syracuseStep 164771 = 247157) B247157
theorem B164787 : Blo 163797 164787 := bstep (se 1 (by rfl) ⟨123590, by rfl⟩ : syracuseStep 164787 = 247181) B247181
theorem B164803 : Blo 163797 164803 := bstep (se 1 (by rfl) ⟨123602, by rfl⟩ : syracuseStep 164803 = 247205) B247205
theorem B164819 : Blo 163797 164819 := bstep (se 1 (by rfl) ⟨123614, by rfl⟩ : syracuseStep 164819 = 247229) B247229
theorem B164835 : Blo 163797 164835 := bstep (se 1 (by rfl) ⟨123626, by rfl⟩ : syracuseStep 164835 = 247253) B247253
theorem B1868771 : Blo 163797 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B164851 : Blo 163797 164851 := bstep (se 1 (by rfl) ⟨123638, by rfl⟩ : syracuseStep 164851 = 247277) B247277
theorem B164867 : Blo 163797 164867 := bstep (se 1 (by rfl) ⟨123650, by rfl⟩ : syracuseStep 164867 = 247301) B247301
theorem B164883 : Blo 163797 164883 := bstep (se 1 (by rfl) ⟨123662, by rfl⟩ : syracuseStep 164883 = 247325) B247325
theorem B164899 : Blo 163797 164899 := bstep (se 1 (by rfl) ⟨123674, by rfl⟩ : syracuseStep 164899 = 247349) B247349
theorem B1016867 : Blo 163797 1016867 := bstep (se 1 (by rfl) ⟨762650, by rfl⟩ : syracuseStep 1016867 = 1525301) B1525301
theorem B164915 : Blo 163797 164915 := bstep (se 1 (by rfl) ⟨123686, by rfl⟩ : syracuseStep 164915 = 247373) B247373
theorem B164931 : Blo 163797 164931 := bstep (se 1 (by rfl) ⟨123698, by rfl⟩ : syracuseStep 164931 = 247397) B247397
theorem B164947 : Blo 163797 164947 := bstep (se 1 (by rfl) ⟨123710, by rfl⟩ : syracuseStep 164947 = 247421) B247421
theorem B164963 : Blo 163797 164963 := bstep (se 1 (by rfl) ⟨123722, by rfl⟩ : syracuseStep 164963 = 247445) B247445
theorem B164979 : Blo 163797 164979 := bstep (se 1 (by rfl) ⟨123734, by rfl⟩ : syracuseStep 164979 = 247469) B247469
theorem B164995 : Blo 163797 164995 := bstep (se 1 (by rfl) ⟨123746, by rfl⟩ : syracuseStep 164995 = 247493) B247493
theorem B165011 : Blo 163797 165011 := bstep (se 1 (by rfl) ⟨123758, by rfl⟩ : syracuseStep 165011 = 247517) B247517
theorem B165027 : Blo 163797 165027 := bstep (se 1 (by rfl) ⟨123770, by rfl⟩ : syracuseStep 165027 = 247541) B247541
theorem B165043 : Blo 163797 165043 := bstep (se 1 (by rfl) ⟨123782, by rfl⟩ : syracuseStep 165043 = 247565) B247565
theorem B165059 : Blo 163797 165059 := bstep (se 1 (by rfl) ⟨123794, by rfl⟩ : syracuseStep 165059 = 247589) B247589
theorem B165075 : Blo 163797 165075 := bstep (se 1 (by rfl) ⟨123806, by rfl⟩ : syracuseStep 165075 = 247613) B247613
theorem B165091 : Blo 163797 165091 := bstep (se 1 (by rfl) ⟨123818, by rfl⟩ : syracuseStep 165091 = 247637) B247637
theorem B165107 : Blo 163797 165107 := bstep (se 1 (by rfl) ⟨123830, by rfl⟩ : syracuseStep 165107 = 247661) B247661
theorem B165123 : Blo 163797 165123 := bstep (se 1 (by rfl) ⟨123842, by rfl⟩ : syracuseStep 165123 = 247685) B247685
theorem B165139 : Blo 163797 165139 := bstep (se 1 (by rfl) ⟨123854, by rfl⟩ : syracuseStep 165139 = 247709) B247709
theorem B951587 : Blo 163797 951587 := bstep (se 1 (by rfl) ⟨713690, by rfl⟩ : syracuseStep 951587 = 1427381) B1427381
theorem B165155 : Blo 163797 165155 := bstep (se 1 (by rfl) ⟨123866, by rfl⟩ : syracuseStep 165155 = 247733) B247733
theorem B361763 : Blo 163797 361763 := bstep (se 1 (by rfl) ⟨271322, by rfl⟩ : syracuseStep 361763 = 542645) B542645
theorem B1017137 : Blo 163797 1017137 := bstep (se 2 (by rfl) ⟨381426, by rfl⟩ : syracuseStep 1017137 = 762853) B762853
theorem B165171 : Blo 163797 165171 := bstep (se 1 (by rfl) ⟨123878, by rfl⟩ : syracuseStep 165171 = 247757) B247757
theorem B165187 : Blo 163797 165187 := bstep (se 1 (by rfl) ⟨123890, by rfl⟩ : syracuseStep 165187 = 247781) B247781
theorem B886085 : Blo 163797 886085 := bstep (se 4 (by rfl) ⟨83070, by rfl⟩ : syracuseStep 886085 = 166141) B166141
theorem B558413 : Blo 163797 558413 := bstep (se 3 (by rfl) ⟨104702, by rfl⟩ : syracuseStep 558413 = 209405) B209405
theorem B165203 : Blo 163797 165203 := bstep (se 1 (by rfl) ⟨123902, by rfl⟩ : syracuseStep 165203 = 247805) B247805
theorem B1869155 : Blo 163797 1869155 := bstep (se 1 (by rfl) ⟨1401866, by rfl⟩ : syracuseStep 1869155 = 2803733) B2803733
theorem B165219 : Blo 163797 165219 := bstep (se 1 (by rfl) ⟨123914, by rfl⟩ : syracuseStep 165219 = 247829) B247829
theorem B165235 : Blo 163797 165235 := bstep (se 1 (by rfl) ⟨123926, by rfl⟩ : syracuseStep 165235 = 247853) B247853
theorem B165251 : Blo 163797 165251 := bstep (se 1 (by rfl) ⟨123938, by rfl⟩ : syracuseStep 165251 = 247877) B247877
theorem B558467 : Blo 163797 558467 := bstep (se 1 (by rfl) ⟨418850, by rfl⟩ : syracuseStep 558467 = 837701) B837701
theorem B165267 : Blo 163797 165267 := bstep (se 1 (by rfl) ⟨123950, by rfl⟩ : syracuseStep 165267 = 247901) B247901
theorem B165283 : Blo 163797 165283 := bstep (se 1 (by rfl) ⟨123962, by rfl⟩ : syracuseStep 165283 = 247925) B247925
theorem B165299 : Blo 163797 165299 := bstep (se 1 (by rfl) ⟨123974, by rfl⟩ : syracuseStep 165299 = 247949) B247949
theorem B165315 : Blo 163797 165315 := bstep (se 1 (by rfl) ⟨123986, by rfl⟩ : syracuseStep 165315 = 247973) B247973
theorem B165331 : Blo 163797 165331 := bstep (se 1 (by rfl) ⟨123998, by rfl⟩ : syracuseStep 165331 = 247997) B247997
theorem B165347 : Blo 163797 165347 := bstep (se 1 (by rfl) ⟨124010, by rfl⟩ : syracuseStep 165347 = 248021) B248021
theorem B263665 : Blo 163797 263665 := bstep (se 2 (by rfl) ⟨98874, by rfl⟩ : syracuseStep 263665 = 197749) B197749
theorem B165363 : Blo 163797 165363 := bstep (se 1 (by rfl) ⟨124022, by rfl⟩ : syracuseStep 165363 = 248045) B248045
theorem B165379 : Blo 163797 165379 := bstep (se 1 (by rfl) ⟨124034, by rfl⟩ : syracuseStep 165379 = 248069) B248069
theorem B165395 : Blo 163797 165395 := bstep (se 1 (by rfl) ⟨124046, by rfl⟩ : syracuseStep 165395 = 248093) B248093
theorem B165411 : Blo 163797 165411 := bstep (se 1 (by rfl) ⟨124058, by rfl⟩ : syracuseStep 165411 = 248117) B248117
theorem B165427 : Blo 163797 165427 := bstep (se 1 (by rfl) ⟨124070, by rfl⟩ : syracuseStep 165427 = 248141) B248141
theorem B165443 : Blo 163797 165443 := bstep (se 1 (by rfl) ⟨124082, by rfl⟩ : syracuseStep 165443 = 248165) B248165
theorem B165459 : Blo 163797 165459 := bstep (se 1 (by rfl) ⟨124094, by rfl⟩ : syracuseStep 165459 = 248189) B248189
theorem B165475 : Blo 163797 165475 := bstep (se 1 (by rfl) ⟨124106, by rfl⟩ : syracuseStep 165475 = 248213) B248213
theorem B165491 : Blo 163797 165491 := bstep (se 1 (by rfl) ⟨124118, by rfl⟩ : syracuseStep 165491 = 248237) B248237
theorem B165507 : Blo 163797 165507 := bstep (se 1 (by rfl) ⟨124130, by rfl⟩ : syracuseStep 165507 = 248261) B248261
theorem B558737 : Blo 163797 558737 := bstep (se 2 (by rfl) ⟨209526, by rfl⟩ : syracuseStep 558737 = 419053) B419053
theorem B165523 : Blo 163797 165523 := bstep (se 1 (by rfl) ⟨124142, by rfl⟩ : syracuseStep 165523 = 248285) B248285
theorem B165539 : Blo 163797 165539 := bstep (se 1 (by rfl) ⟨124154, by rfl⟩ : syracuseStep 165539 = 248309) B248309
theorem B165555 : Blo 163797 165555 := bstep (se 1 (by rfl) ⟨124166, by rfl⟩ : syracuseStep 165555 = 248333) B248333
theorem B165571 : Blo 163797 165571 := bstep (se 1 (by rfl) ⟨124178, by rfl⟩ : syracuseStep 165571 = 248357) B248357
theorem B2262725 : Blo 163797 2262725 := bstep (se 4 (by rfl) ⟨212130, by rfl⟩ : syracuseStep 2262725 = 424261) B424261
theorem B165587 : Blo 163797 165587 := bstep (se 1 (by rfl) ⟨124190, by rfl⟩ : syracuseStep 165587 = 248381) B248381
theorem B165603 : Blo 163797 165603 := bstep (se 1 (by rfl) ⟨124202, by rfl⟩ : syracuseStep 165603 = 248405) B248405
theorem B1050353 : Blo 163797 1050353 := bstep (se 2 (by rfl) ⟨393882, by rfl⟩ : syracuseStep 1050353 = 787765) B787765
theorem B165619 : Blo 163797 165619 := bstep (se 1 (by rfl) ⟨124214, by rfl⟩ : syracuseStep 165619 = 248429) B248429
theorem B165635 : Blo 163797 165635 := bstep (se 1 (by rfl) ⟨124226, by rfl⟩ : syracuseStep 165635 = 248453) B248453
theorem B1509133 : Blo 163797 1509133 := bstep (se 3 (by rfl) ⟨282962, by rfl⟩ : syracuseStep 1509133 = 565925) B565925
theorem B165651 : Blo 163797 165651 := bstep (se 1 (by rfl) ⟨124238, by rfl⟩ : syracuseStep 165651 = 248477) B248477
theorem B624419 : Blo 163797 624419 := bstep (se 1 (by rfl) ⟨468314, by rfl⟩ : syracuseStep 624419 = 936629) B936629
theorem B165667 : Blo 163797 165667 := bstep (se 1 (by rfl) ⟨124250, by rfl⟩ : syracuseStep 165667 = 248501) B248501
theorem B165683 : Blo 163797 165683 := bstep (se 1 (by rfl) ⟨124262, by rfl⟩ : syracuseStep 165683 = 248525) B248525
theorem B165699 : Blo 163797 165699 := bstep (se 1 (by rfl) ⟨124274, by rfl⟩ : syracuseStep 165699 = 248549) B248549
theorem B165715 : Blo 163797 165715 := bstep (se 1 (by rfl) ⟨124286, by rfl⟩ : syracuseStep 165715 = 248573) B248573
theorem B1247075 : Blo 163797 1247075 := bstep (se 1 (by rfl) ⟨935306, by rfl⟩ : syracuseStep 1247075 = 1870613) B1870613
theorem B165731 : Blo 163797 165731 := bstep (se 1 (by rfl) ⟨124298, by rfl⟩ : syracuseStep 165731 = 248597) B248597
theorem B165747 : Blo 163797 165747 := bstep (se 1 (by rfl) ⟨124310, by rfl⟩ : syracuseStep 165747 = 248621) B248621
theorem B165763 : Blo 163797 165763 := bstep (se 1 (by rfl) ⟨124322, by rfl⟩ : syracuseStep 165763 = 248645) B248645
theorem B165779 : Blo 163797 165779 := bstep (se 1 (by rfl) ⟨124334, by rfl⟩ : syracuseStep 165779 = 248669) B248669
theorem B165795 : Blo 163797 165795 := bstep (se 1 (by rfl) ⟨124346, by rfl⟩ : syracuseStep 165795 = 248693) B248693
theorem B165811 : Blo 163797 165811 := bstep (se 1 (by rfl) ⟨124358, by rfl⟩ : syracuseStep 165811 = 248717) B248717
theorem B165827 : Blo 163797 165827 := bstep (se 1 (by rfl) ⟨124370, by rfl⟩ : syracuseStep 165827 = 248741) B248741
theorem B165843 : Blo 163797 165843 := bstep (se 1 (by rfl) ⟨124382, by rfl⟩ : syracuseStep 165843 = 248765) B248765
theorem B165859 : Blo 163797 165859 := bstep (se 1 (by rfl) ⟨124394, by rfl⟩ : syracuseStep 165859 = 248789) B248789
theorem B165875 : Blo 163797 165875 := bstep (se 1 (by rfl) ⟨124406, by rfl⟩ : syracuseStep 165875 = 248813) B248813
theorem B165891 : Blo 163797 165891 := bstep (se 1 (by rfl) ⟨124418, by rfl⟩ : syracuseStep 165891 = 248837) B248837
theorem B165907 : Blo 163797 165907 := bstep (se 1 (by rfl) ⟨124430, by rfl⟩ : syracuseStep 165907 = 248861) B248861
theorem B165923 : Blo 163797 165923 := bstep (se 1 (by rfl) ⟨124442, by rfl⟩ : syracuseStep 165923 = 248885) B248885
theorem B165939 : Blo 163797 165939 := bstep (se 1 (by rfl) ⟨124454, by rfl⟩ : syracuseStep 165939 = 248909) B248909
theorem B165955 : Blo 163797 165955 := bstep (se 1 (by rfl) ⟨124466, by rfl⟩ : syracuseStep 165955 = 248933) B248933
theorem B165971 : Blo 163797 165971 := bstep (se 1 (by rfl) ⟨124478, by rfl⟩ : syracuseStep 165971 = 248957) B248957
theorem B165987 : Blo 163797 165987 := bstep (se 1 (by rfl) ⟨124490, by rfl⟩ : syracuseStep 165987 = 248981) B248981
theorem B526445 : Blo 163797 526445 := bstep (se 3 (by rfl) ⟨98708, by rfl⟩ : syracuseStep 526445 = 197417) B197417
theorem B166003 : Blo 163797 166003 := bstep (se 1 (by rfl) ⟨124502, by rfl⟩ : syracuseStep 166003 = 249005) B249005
theorem B198787 : Blo 163797 198787 := bstep (se 1 (by rfl) ⟨149090, by rfl⟩ : syracuseStep 198787 = 298181) B298181
theorem B166019 : Blo 163797 166019 := bstep (se 1 (by rfl) ⟨124514, by rfl⟩ : syracuseStep 166019 = 249029) B249029
theorem B2001037 : Blo 163797 2001037 := bstep (se 3 (by rfl) ⟨375194, by rfl⟩ : syracuseStep 2001037 = 750389) B750389
theorem B166035 : Blo 163797 166035 := bstep (se 1 (by rfl) ⟨124526, by rfl⟩ : syracuseStep 166035 = 249053) B249053
theorem B166051 : Blo 163797 166051 := bstep (se 1 (by rfl) ⟨124538, by rfl⟩ : syracuseStep 166051 = 249077) B249077
theorem B559277 : Blo 163797 559277 := bstep (se 3 (by rfl) ⟨104864, by rfl⟩ : syracuseStep 559277 = 209729) B209729
theorem B166067 : Blo 163797 166067 := bstep (se 1 (by rfl) ⟨124550, by rfl⟩ : syracuseStep 166067 = 249101) B249101
theorem B166083 : Blo 163797 166083 := bstep (se 1 (by rfl) ⟨124562, by rfl⟩ : syracuseStep 166083 = 249125) B249125
theorem B166099 : Blo 163797 166099 := bstep (se 1 (by rfl) ⟨124574, by rfl⟩ : syracuseStep 166099 = 249149) B249149
theorem B559331 : Blo 163797 559331 := bstep (se 1 (by rfl) ⟨419498, by rfl⟩ : syracuseStep 559331 = 838997) B838997
theorem B166115 : Blo 163797 166115 := bstep (se 1 (by rfl) ⟨124586, by rfl⟩ : syracuseStep 166115 = 249173) B249173
theorem B166131 : Blo 163797 166131 := bstep (se 1 (by rfl) ⟨124598, by rfl⟩ : syracuseStep 166131 = 249197) B249197
theorem B166147 : Blo 163797 166147 := bstep (se 1 (by rfl) ⟨124610, by rfl⟩ : syracuseStep 166147 = 249221) B249221
theorem B166163 : Blo 163797 166163 := bstep (se 1 (by rfl) ⟨124622, by rfl⟩ : syracuseStep 166163 = 249245) B249245
theorem B166179 : Blo 163797 166179 := bstep (se 1 (by rfl) ⟨124634, by rfl⟩ : syracuseStep 166179 = 249269) B249269
theorem B166195 : Blo 163797 166195 := bstep (se 1 (by rfl) ⟨124646, by rfl⟩ : syracuseStep 166195 = 249293) B249293
theorem B166211 : Blo 163797 166211 := bstep (se 1 (by rfl) ⟨124658, by rfl⟩ : syracuseStep 166211 = 249317) B249317
theorem B166227 : Blo 163797 166227 := bstep (se 1 (by rfl) ⟨124670, by rfl⟩ : syracuseStep 166227 = 249341) B249341
theorem B166243 : Blo 163797 166243 := bstep (se 1 (by rfl) ⟨124682, by rfl⟩ : syracuseStep 166243 = 249365) B249365
theorem B166259 : Blo 163797 166259 := bstep (se 1 (by rfl) ⟨124694, by rfl⟩ : syracuseStep 166259 = 249389) B249389
theorem B166275 : Blo 163797 166275 := bstep (se 1 (by rfl) ⟨124706, by rfl⟩ : syracuseStep 166275 = 249413) B249413
theorem B1804685 : Blo 163797 1804685 := bstep (se 3 (by rfl) ⟨338378, by rfl⟩ : syracuseStep 1804685 = 676757) B676757
theorem B264593 : Blo 163797 264593 := bstep (se 2 (by rfl) ⟨99222, by rfl⟩ : syracuseStep 264593 = 198445) B198445
theorem B166291 : Blo 163797 166291 := bstep (se 1 (by rfl) ⟨124718, by rfl⟩ : syracuseStep 166291 = 249437) B249437
theorem B788899 : Blo 163797 788899 := bstep (se 1 (by rfl) ⟨591674, by rfl⟩ : syracuseStep 788899 = 1183349) B1183349
theorem B297379 : Blo 163797 297379 := bstep (se 1 (by rfl) ⟨223034, by rfl⟩ : syracuseStep 297379 = 446069) B446069
theorem B166307 : Blo 163797 166307 := bstep (se 1 (by rfl) ⟨124730, by rfl⟩ : syracuseStep 166307 = 249461) B249461
theorem B166323 : Blo 163797 166323 := bstep (se 1 (by rfl) ⟨124742, by rfl⟩ : syracuseStep 166323 = 249485) B249485
theorem B166339 : Blo 163797 166339 := bstep (se 1 (by rfl) ⟨124754, by rfl⟩ : syracuseStep 166339 = 249509) B249509
theorem B395729 : Blo 163797 395729 := bstep (se 2 (by rfl) ⟨148398, by rfl⟩ : syracuseStep 395729 = 296797) B296797
theorem B166355 : Blo 163797 166355 := bstep (se 1 (by rfl) ⟨124766, by rfl⟩ : syracuseStep 166355 = 249533) B249533
theorem B166371 : Blo 163797 166371 := bstep (se 1 (by rfl) ⟨124778, by rfl⟩ : syracuseStep 166371 = 249557) B249557
theorem B559601 : Blo 163797 559601 := bstep (se 2 (by rfl) ⟨209850, by rfl⟩ : syracuseStep 559601 = 419701) B419701
theorem B166387 : Blo 163797 166387 := bstep (se 1 (by rfl) ⟨124790, by rfl⟩ : syracuseStep 166387 = 249581) B249581
theorem B166403 : Blo 163797 166403 := bstep (se 1 (by rfl) ⟨124802, by rfl⟩ : syracuseStep 166403 = 249605) B249605
theorem B166419 : Blo 163797 166419 := bstep (se 1 (by rfl) ⟨124814, by rfl⟩ : syracuseStep 166419 = 249629) B249629
theorem B166435 : Blo 163797 166435 := bstep (se 1 (by rfl) ⟨124826, by rfl⟩ : syracuseStep 166435 = 249653) B249653
theorem B166451 : Blo 163797 166451 := bstep (se 1 (by rfl) ⟨124838, by rfl⟩ : syracuseStep 166451 = 249677) B249677
theorem B166467 : Blo 163797 166467 := bstep (se 1 (by rfl) ⟨124850, by rfl⟩ : syracuseStep 166467 = 249701) B249701
theorem B166483 : Blo 163797 166483 := bstep (se 1 (by rfl) ⟨124862, by rfl⟩ : syracuseStep 166483 = 249725) B249725
theorem B166499 : Blo 163797 166499 := bstep (se 1 (by rfl) ⟨124874, by rfl⟩ : syracuseStep 166499 = 249749) B249749
theorem B166515 : Blo 163797 166515 := bstep (se 1 (by rfl) ⟨124886, by rfl⟩ : syracuseStep 166515 = 249773) B249773
theorem B166531 : Blo 163797 166531 := bstep (se 1 (by rfl) ⟨124898, by rfl⟩ : syracuseStep 166531 = 249797) B249797
theorem B166547 : Blo 163797 166547 := bstep (se 1 (by rfl) ⟨124910, by rfl⟩ : syracuseStep 166547 = 249821) B249821
theorem B166563 : Blo 163797 166563 := bstep (se 1 (by rfl) ⟨124922, by rfl⟩ : syracuseStep 166563 = 249845) B249845
theorem B166579 : Blo 163797 166579 := bstep (se 1 (by rfl) ⟨124934, by rfl⟩ : syracuseStep 166579 = 249869) B249869
theorem B166595 : Blo 163797 166595 := bstep (se 1 (by rfl) ⟨124946, by rfl⟩ : syracuseStep 166595 = 249893) B249893
theorem B166611 : Blo 163797 166611 := bstep (se 1 (by rfl) ⟨124958, by rfl⟩ : syracuseStep 166611 = 249917) B249917
theorem B166627 : Blo 163797 166627 := bstep (se 1 (by rfl) ⟨124970, by rfl⟩ : syracuseStep 166627 = 249941) B249941
theorem B166643 : Blo 163797 166643 := bstep (se 1 (by rfl) ⟨124982, by rfl⟩ : syracuseStep 166643 = 249965) B249965
theorem B166659 : Blo 163797 166659 := bstep (se 1 (by rfl) ⟨124994, by rfl⟩ : syracuseStep 166659 = 249989) B249989
theorem B625421 : Blo 163797 625421 := bstep (se 3 (by rfl) ⟨117266, by rfl⟩ : syracuseStep 625421 = 234533) B234533
theorem B166675 : Blo 163797 166675 := bstep (se 1 (by rfl) ⟨125006, by rfl⟩ : syracuseStep 166675 = 250013) B250013
theorem B166691 : Blo 163797 166691 := bstep (se 1 (by rfl) ⟨125018, by rfl⟩ : syracuseStep 166691 = 250037) B250037
theorem B166707 : Blo 163797 166707 := bstep (se 1 (by rfl) ⟨125030, by rfl⟩ : syracuseStep 166707 = 250061) B250061
theorem B166723 : Blo 163797 166723 := bstep (se 1 (by rfl) ⟨125042, by rfl⟩ : syracuseStep 166723 = 250085) B250085
theorem B166739 : Blo 163797 166739 := bstep (se 1 (by rfl) ⟨125054, by rfl⟩ : syracuseStep 166739 = 250109) B250109
theorem B166755 : Blo 163797 166755 := bstep (se 1 (by rfl) ⟨125066, by rfl⟩ : syracuseStep 166755 = 250133) B250133
theorem B166771 : Blo 163797 166771 := bstep (se 1 (by rfl) ⟨125078, by rfl⟩ : syracuseStep 166771 = 250157) B250157
theorem B166787 : Blo 163797 166787 := bstep (se 1 (by rfl) ⟨125090, by rfl⟩ : syracuseStep 166787 = 250181) B250181
theorem B166803 : Blo 163797 166803 := bstep (se 1 (by rfl) ⟨125102, by rfl⟩ : syracuseStep 166803 = 250205) B250205
theorem B166819 : Blo 163797 166819 := bstep (se 1 (by rfl) ⟨125114, by rfl⟩ : syracuseStep 166819 = 250229) B250229
theorem B166835 : Blo 163797 166835 := bstep (se 1 (by rfl) ⟨125126, by rfl⟩ : syracuseStep 166835 = 250253) B250253
theorem B166851 : Blo 163797 166851 := bstep (se 1 (by rfl) ⟨125138, by rfl⟩ : syracuseStep 166851 = 250277) B250277
theorem B166867 : Blo 163797 166867 := bstep (se 1 (by rfl) ⟨125150, by rfl⟩ : syracuseStep 166867 = 250301) B250301
theorem B166883 : Blo 163797 166883 := bstep (se 1 (by rfl) ⟨125162, by rfl⟩ : syracuseStep 166883 = 250325) B250325
theorem B166899 : Blo 163797 166899 := bstep (se 1 (by rfl) ⟨125174, by rfl⟩ : syracuseStep 166899 = 250349) B250349
theorem B166915 : Blo 163797 166915 := bstep (se 1 (by rfl) ⟨125186, by rfl⟩ : syracuseStep 166915 = 250373) B250373
theorem B560141 : Blo 163797 560141 := bstep (se 3 (by rfl) ⟨105026, by rfl⟩ : syracuseStep 560141 = 210053) B210053
theorem B166931 : Blo 163797 166931 := bstep (se 1 (by rfl) ⟨125198, by rfl⟩ : syracuseStep 166931 = 250397) B250397
theorem B166947 : Blo 163797 166947 := bstep (se 1 (by rfl) ⟨125210, by rfl⟩ : syracuseStep 166947 = 250421) B250421
theorem B166963 : Blo 163797 166963 := bstep (se 1 (by rfl) ⟨125222, by rfl⟩ : syracuseStep 166963 = 250445) B250445
theorem B560195 : Blo 163797 560195 := bstep (se 1 (by rfl) ⟨420146, by rfl⟩ : syracuseStep 560195 = 840293) B840293
theorem B166979 : Blo 163797 166979 := bstep (se 1 (by rfl) ⟨125234, by rfl⟩ : syracuseStep 166979 = 250469) B250469
theorem B166995 : Blo 163797 166995 := bstep (se 1 (by rfl) ⟨125246, by rfl⟩ : syracuseStep 166995 = 250493) B250493
theorem B167011 : Blo 163797 167011 := bstep (se 1 (by rfl) ⟨125258, by rfl⟩ : syracuseStep 167011 = 250517) B250517
theorem B167027 : Blo 163797 167027 := bstep (se 1 (by rfl) ⟨125270, by rfl⟩ : syracuseStep 167027 = 250541) B250541
theorem B167043 : Blo 163797 167043 := bstep (se 1 (by rfl) ⟨125282, by rfl⟩ : syracuseStep 167043 = 250565) B250565
theorem B167059 : Blo 163797 167059 := bstep (se 1 (by rfl) ⟨125294, by rfl⟩ : syracuseStep 167059 = 250589) B250589
theorem B1051811 : Blo 163797 1051811 := bstep (se 1 (by rfl) ⟨788858, by rfl⟩ : syracuseStep 1051811 = 1577717) B1577717
theorem B167075 : Blo 163797 167075 := bstep (se 1 (by rfl) ⟨125306, by rfl⟩ : syracuseStep 167075 = 250613) B250613
theorem B167091 : Blo 163797 167091 := bstep (se 1 (by rfl) ⟨125318, by rfl⟩ : syracuseStep 167091 = 250637) B250637
theorem B167107 : Blo 163797 167107 := bstep (se 1 (by rfl) ⟨125330, by rfl⟩ : syracuseStep 167107 = 250661) B250661
theorem B396497 : Blo 163797 396497 := bstep (se 2 (by rfl) ⟨148686, by rfl⟩ : syracuseStep 396497 = 297373) B297373
theorem B265427 : Blo 163797 265427 := bstep (se 1 (by rfl) ⟨199070, by rfl⟩ : syracuseStep 265427 = 398141) B398141
theorem B167123 : Blo 163797 167123 := bstep (se 1 (by rfl) ⟨125342, by rfl⟩ : syracuseStep 167123 = 250685) B250685
theorem B167139 : Blo 163797 167139 := bstep (se 1 (by rfl) ⟨125354, by rfl⟩ : syracuseStep 167139 = 250709) B250709
theorem B265459 : Blo 163797 265459 := bstep (se 1 (by rfl) ⟨199094, by rfl⟩ : syracuseStep 265459 = 398189) B398189
theorem B167155 : Blo 163797 167155 := bstep (se 1 (by rfl) ⟨125366, by rfl⟩ : syracuseStep 167155 = 250733) B250733
theorem B167171 : Blo 163797 167171 := bstep (se 1 (by rfl) ⟨125378, by rfl⟩ : syracuseStep 167171 = 250757) B250757
theorem B167187 : Blo 163797 167187 := bstep (se 1 (by rfl) ⟨125390, by rfl⟩ : syracuseStep 167187 = 250781) B250781
theorem B167203 : Blo 163797 167203 := bstep (se 1 (by rfl) ⟨125402, by rfl⟩ : syracuseStep 167203 = 250805) B250805
theorem B593201 : Blo 163797 593201 := bstep (se 2 (by rfl) ⟨222450, by rfl⟩ : syracuseStep 593201 = 444901) B444901
theorem B167219 : Blo 163797 167219 := bstep (se 1 (by rfl) ⟨125414, by rfl⟩ : syracuseStep 167219 = 250829) B250829
theorem B167235 : Blo 163797 167235 := bstep (se 1 (by rfl) ⟨125426, by rfl⟩ : syracuseStep 167235 = 250853) B250853
theorem B560465 : Blo 163797 560465 := bstep (se 2 (by rfl) ⟨210174, by rfl⟩ : syracuseStep 560465 = 420349) B420349
theorem B167251 : Blo 163797 167251 := bstep (se 1 (by rfl) ⟨125438, by rfl⟩ : syracuseStep 167251 = 250877) B250877
theorem B167267 : Blo 163797 167267 := bstep (se 1 (by rfl) ⟨125450, by rfl⟩ : syracuseStep 167267 = 250901) B250901
theorem B167283 : Blo 163797 167283 := bstep (se 1 (by rfl) ⟨125462, by rfl⟩ : syracuseStep 167283 = 250925) B250925
theorem B167299 : Blo 163797 167299 := bstep (se 1 (by rfl) ⟨125474, by rfl⟩ : syracuseStep 167299 = 250949) B250949
theorem B167315 : Blo 163797 167315 := bstep (se 1 (by rfl) ⟨125486, by rfl⟩ : syracuseStep 167315 = 250973) B250973
theorem B167331 : Blo 163797 167331 := bstep (se 1 (by rfl) ⟨125498, by rfl⟩ : syracuseStep 167331 = 250997) B250997
theorem B167347 : Blo 163797 167347 := bstep (se 1 (by rfl) ⟨125510, by rfl⟩ : syracuseStep 167347 = 251021) B251021
theorem B167363 : Blo 163797 167363 := bstep (se 1 (by rfl) ⟨125522, by rfl⟩ : syracuseStep 167363 = 251045) B251045
theorem B167379 : Blo 163797 167379 := bstep (se 1 (by rfl) ⟨125534, by rfl⟩ : syracuseStep 167379 = 251069) B251069
theorem B167395 : Blo 163797 167395 := bstep (se 1 (by rfl) ⟨125546, by rfl⟩ : syracuseStep 167395 = 251093) B251093
theorem B167411 : Blo 163797 167411 := bstep (se 1 (by rfl) ⟨125558, by rfl⟩ : syracuseStep 167411 = 251117) B251117
theorem B167427 : Blo 163797 167427 := bstep (se 1 (by rfl) ⟨125570, by rfl⟩ : syracuseStep 167427 = 251141) B251141
theorem B167443 : Blo 163797 167443 := bstep (se 1 (by rfl) ⟨125582, by rfl⟩ : syracuseStep 167443 = 251165) B251165
theorem B167459 : Blo 163797 167459 := bstep (se 1 (by rfl) ⟨125594, by rfl⟩ : syracuseStep 167459 = 251189) B251189
theorem B167475 : Blo 163797 167475 := bstep (se 1 (by rfl) ⟨125606, by rfl⟩ : syracuseStep 167475 = 251213) B251213
theorem B167491 : Blo 163797 167491 := bstep (se 1 (by rfl) ⟨125618, by rfl⟩ : syracuseStep 167491 = 251237) B251237
theorem B167507 : Blo 163797 167507 := bstep (se 1 (by rfl) ⟨125630, by rfl⟩ : syracuseStep 167507 = 251261) B251261
theorem B167523 : Blo 163797 167523 := bstep (se 1 (by rfl) ⟨125642, by rfl⟩ : syracuseStep 167523 = 251285) B251285
theorem B167539 : Blo 163797 167539 := bstep (se 1 (by rfl) ⟨125654, by rfl⟩ : syracuseStep 167539 = 251309) B251309
theorem B167555 : Blo 163797 167555 := bstep (se 1 (by rfl) ⟨125666, by rfl⟩ : syracuseStep 167555 = 251333) B251333
theorem B167571 : Blo 163797 167571 := bstep (se 1 (by rfl) ⟨125678, by rfl⟩ : syracuseStep 167571 = 251357) B251357
theorem B167587 : Blo 163797 167587 := bstep (se 1 (by rfl) ⟨125690, by rfl⟩ : syracuseStep 167587 = 251381) B251381
theorem B167603 : Blo 163797 167603 := bstep (se 1 (by rfl) ⟨125702, by rfl⟩ : syracuseStep 167603 = 251405) B251405
theorem B167619 : Blo 163797 167619 := bstep (se 1 (by rfl) ⟨125714, by rfl⟩ : syracuseStep 167619 = 251429) B251429
theorem B167635 : Blo 163797 167635 := bstep (se 1 (by rfl) ⟨125726, by rfl⟩ : syracuseStep 167635 = 251453) B251453
theorem B167651 : Blo 163797 167651 := bstep (se 1 (by rfl) ⟨125738, by rfl⟩ : syracuseStep 167651 = 251477) B251477
theorem B167667 : Blo 163797 167667 := bstep (se 1 (by rfl) ⟨125750, by rfl⟩ : syracuseStep 167667 = 251501) B251501
theorem B167683 : Blo 163797 167683 := bstep (se 1 (by rfl) ⟨125762, by rfl⟩ : syracuseStep 167683 = 251525) B251525
theorem B954125 : Blo 163797 954125 := bstep (se 3 (by rfl) ⟨178898, by rfl⟩ : syracuseStep 954125 = 357797) B357797
theorem B167699 : Blo 163797 167699 := bstep (se 1 (by rfl) ⟨125774, by rfl⟩ : syracuseStep 167699 = 251549) B251549
theorem B167715 : Blo 163797 167715 := bstep (se 1 (by rfl) ⟨125786, by rfl⟩ : syracuseStep 167715 = 251573) B251573
theorem B167731 : Blo 163797 167731 := bstep (se 1 (by rfl) ⟨125798, by rfl⟩ : syracuseStep 167731 = 251597) B251597
theorem B167747 : Blo 163797 167747 := bstep (se 1 (by rfl) ⟨125810, by rfl⟩ : syracuseStep 167747 = 251621) B251621
theorem B167763 : Blo 163797 167763 := bstep (se 1 (by rfl) ⟨125822, by rfl⟩ : syracuseStep 167763 = 251645) B251645
theorem B167779 : Blo 163797 167779 := bstep (se 1 (by rfl) ⟨125834, by rfl⟩ : syracuseStep 167779 = 251669) B251669
theorem B561005 : Blo 163797 561005 := bstep (se 3 (by rfl) ⟨105188, by rfl⟩ : syracuseStep 561005 = 210377) B210377
theorem B167795 : Blo 163797 167795 := bstep (se 1 (by rfl) ⟨125846, by rfl⟩ : syracuseStep 167795 = 251693) B251693
theorem B561059 : Blo 163797 561059 := bstep (se 1 (by rfl) ⟨420794, by rfl⟩ : syracuseStep 561059 = 841589) B841589
theorem B200723 : Blo 163797 200723 := bstep (se 1 (by rfl) ⟨150542, by rfl⟩ : syracuseStep 200723 = 301085) B301085
theorem B266387 : Blo 163797 266387 := bstep (se 1 (by rfl) ⟨199790, by rfl⟩ : syracuseStep 266387 = 399581) B399581
theorem B561329 : Blo 163797 561329 := bstep (se 2 (by rfl) ⟨210498, by rfl⟩ : syracuseStep 561329 = 420997) B420997
theorem B594125 : Blo 163797 594125 := bstep (se 3 (by rfl) ⟨111398, by rfl⟩ : syracuseStep 594125 = 222797) B222797
theorem B266465 : Blo 163797 266465 := bstep (se 2 (by rfl) ⟨99924, by rfl⟩ : syracuseStep 266465 = 199849) B199849
theorem B233713 : Blo 163797 233713 := bstep (se 2 (by rfl) ⟨87642, by rfl⟩ : syracuseStep 233713 = 175285) B175285
theorem B790897 : Blo 163797 790897 := bstep (se 2 (by rfl) ⟨296586, by rfl⟩ : syracuseStep 790897 = 593173) B593173
theorem B430499 : Blo 163797 430499 := bstep (se 1 (by rfl) ⟨322874, by rfl⟩ : syracuseStep 430499 = 645749) B645749
theorem B332209 : Blo 163797 332209 := bstep (se 2 (by rfl) ⟨124578, by rfl⟩ : syracuseStep 332209 = 249157) B249157
theorem B266689 : Blo 163797 266689 := bstep (se 2 (by rfl) ⟨100008, by rfl⟩ : syracuseStep 266689 = 200017) B200017
theorem B561869 : Blo 163797 561869 := bstep (se 3 (by rfl) ⟨105350, by rfl⟩ : syracuseStep 561869 = 210701) B210701
theorem B561923 : Blo 163797 561923 := bstep (se 1 (by rfl) ⟨421442, by rfl⟩ : syracuseStep 561923 = 842885) B842885
theorem B627533 : Blo 163797 627533 := bstep (se 3 (by rfl) ⟨117662, by rfl⟩ : syracuseStep 627533 = 235325) B235325
theorem B234419 : Blo 163797 234419 := bstep (se 1 (by rfl) ⟨175814, by rfl⟩ : syracuseStep 234419 = 351629) B351629
theorem B1905605 : Blo 163797 1905605 := bstep (se 4 (by rfl) ⟨178650, by rfl⟩ : syracuseStep 1905605 = 357301) B357301
theorem B562193 : Blo 163797 562193 := bstep (se 2 (by rfl) ⟨210822, by rfl⟩ : syracuseStep 562193 = 421645) B421645
theorem B398371 : Blo 163797 398371 := bstep (se 1 (by rfl) ⟨298778, by rfl⟩ : syracuseStep 398371 = 597557) B597557
theorem B529649 : Blo 163797 529649 := bstep (se 2 (by rfl) ⟨198618, by rfl⟩ : syracuseStep 529649 = 397237) B397237
theorem B529699 : Blo 163797 529699 := bstep (se 1 (by rfl) ⟨397274, by rfl⟩ : syracuseStep 529699 = 794549) B794549
theorem B2102597 : Blo 163797 2102597 := bstep (se 4 (by rfl) ⟨197118, by rfl⟩ : syracuseStep 2102597 = 394237) B394237
theorem B300451 : Blo 163797 300451 := bstep (se 1 (by rfl) ⟨225338, by rfl⟩ : syracuseStep 300451 = 450677) B450677
theorem B562733 : Blo 163797 562733 := bstep (se 3 (by rfl) ⟨105512, by rfl⟩ : syracuseStep 562733 = 211025) B211025
theorem B235057 : Blo 163797 235057 := bstep (se 2 (by rfl) ⟨88146, by rfl⟩ : syracuseStep 235057 = 176293) B176293
theorem B2135605 : Blo 163797 2135605 := bstep (se 5 (by rfl) ⟨100106, by rfl⟩ : syracuseStep 2135605 = 200213) B200213
theorem B562787 : Blo 163797 562787 := bstep (se 1 (by rfl) ⟨422090, by rfl⟩ : syracuseStep 562787 = 844181) B844181
theorem B628337 : Blo 163797 628337 := bstep (se 2 (by rfl) ⟨235626, by rfl⟩ : syracuseStep 628337 = 471253) B471253
theorem B235171 : Blo 163797 235171 := bstep (se 1 (by rfl) ⟨176378, by rfl⟩ : syracuseStep 235171 = 352757) B352757
theorem B1414853 : Blo 163797 1414853 := bstep (se 4 (by rfl) ⟨132642, by rfl⟩ : syracuseStep 1414853 = 265285) B265285
theorem B5117717 : Blo 163797 5117717 := bstep (se 6 (by rfl) ⟨119946, by rfl⟩ : syracuseStep 5117717 = 239893) B239893
theorem B563057 : Blo 163797 563057 := bstep (se 2 (by rfl) ⟨211146, by rfl⟩ : syracuseStep 563057 = 422293) B422293
theorem B268147 : Blo 163797 268147 := bstep (se 1 (by rfl) ⟨201110, by rfl⟩ : syracuseStep 268147 = 402221) B402221
theorem B530545 : Blo 163797 530545 := bstep (se 2 (by rfl) ⟨198954, by rfl⟩ : syracuseStep 530545 = 397909) B397909
theorem B2398349 : Blo 163797 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B268451 : Blo 163797 268451 := bstep (se 1 (by rfl) ⟨201338, by rfl⟩ : syracuseStep 268451 = 402677) B402677
theorem B1808581 : Blo 163797 1808581 := bstep (se 4 (by rfl) ⟨169554, by rfl⟩ : syracuseStep 1808581 = 339109) B339109
theorem B629005 : Blo 163797 629005 := bstep (se 3 (by rfl) ⟨117938, by rfl⟩ : syracuseStep 629005 = 235877) B235877
theorem B268643 : Blo 163797 268643 := bstep (se 1 (by rfl) ⟨201482, by rfl⟩ : syracuseStep 268643 = 402965) B402965
theorem B2005361 : Blo 163797 2005361 := bstep (se 2 (by rfl) ⟨752010, by rfl⟩ : syracuseStep 2005361 = 1504021) B1504021
theorem B563597 : Blo 163797 563597 := bstep (se 3 (by rfl) ⟨105674, by rfl⟩ : syracuseStep 563597 = 211349) B211349
theorem B563651 : Blo 163797 563651 := bstep (se 1 (by rfl) ⟨422738, by rfl⟩ : syracuseStep 563651 = 845477) B845477
theorem B268771 : Blo 163797 268771 := bstep (se 1 (by rfl) ⟨201578, by rfl⟩ : syracuseStep 268771 = 403157) B403157
theorem B400081 : Blo 163797 400081 := bstep (se 2 (by rfl) ⟨150030, by rfl⟩ : syracuseStep 400081 = 300061) B300061
theorem B563921 : Blo 163797 563921 := bstep (se 2 (by rfl) ⟨211470, by rfl⟩ : syracuseStep 563921 = 422941) B422941
theorem B1055501 : Blo 163797 1055501 := bstep (se 3 (by rfl) ⟨197906, by rfl⟩ : syracuseStep 1055501 = 395813) B395813
theorem B498449 : Blo 163797 498449 := bstep (se 2 (by rfl) ⟨186918, by rfl⟩ : syracuseStep 498449 = 373837) B373837
theorem B498545 : Blo 163797 498545 := bstep (se 2 (by rfl) ⟨186954, by rfl⟩ : syracuseStep 498545 = 373909) B373909
theorem B236515 : Blo 163797 236515 := bstep (se 1 (by rfl) ⟨177386, by rfl⟩ : syracuseStep 236515 = 354773) B354773
theorem B629795 : Blo 163797 629795 := bstep (se 1 (by rfl) ⟨472346, by rfl⟩ : syracuseStep 629795 = 944693) B944693
theorem B1252421 : Blo 163797 1252421 := bstep (se 4 (by rfl) ⟨117414, by rfl⟩ : syracuseStep 1252421 = 234829) B234829
theorem B564461 : Blo 163797 564461 := bstep (se 3 (by rfl) ⟨105836, by rfl⟩ : syracuseStep 564461 = 211673) B211673
theorem B564515 : Blo 163797 564515 := bstep (se 1 (by rfl) ⟨423386, by rfl⟩ : syracuseStep 564515 = 846773) B846773
theorem B564785 : Blo 163797 564785 := bstep (se 2 (by rfl) ⟨211794, by rfl⟩ : syracuseStep 564785 = 423589) B423589
theorem B892529 : Blo 163797 892529 := bstep (se 2 (by rfl) ⟨334698, by rfl⟩ : syracuseStep 892529 = 669397) B669397
theorem B532109 : Blo 163797 532109 := bstep (se 3 (by rfl) ⟨99770, by rfl⟩ : syracuseStep 532109 = 199541) B199541
theorem B630449 : Blo 163797 630449 := bstep (se 2 (by rfl) ⟨236418, by rfl⟩ : syracuseStep 630449 = 472837) B472837
theorem B3710861 : Blo 163797 3710861 := bstep (se 3 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 3710861 = 1391573) B1391573
theorem B368657 : Blo 163797 368657 := bstep (se 2 (by rfl) ⟨138246, by rfl⟩ : syracuseStep 368657 = 276493) B276493
theorem B368675 : Blo 163797 368675 := bstep (se 1 (by rfl) ⟨276506, by rfl⟩ : syracuseStep 368675 = 553013) B553013
theorem B794701 : Blo 163797 794701 := bstep (se 3 (by rfl) ⟨149006, by rfl⟩ : syracuseStep 794701 = 298013) B298013
theorem B565325 : Blo 163797 565325 := bstep (se 3 (by rfl) ⟨105998, by rfl⟩ : syracuseStep 565325 = 211997) B211997
theorem B237649 : Blo 163797 237649 := bstep (se 2 (by rfl) ⟨89118, by rfl⟩ : syracuseStep 237649 = 178237) B178237
theorem B565379 : Blo 163797 565379 := bstep (se 1 (by rfl) ⟨424034, by rfl⟩ : syracuseStep 565379 = 848069) B848069
theorem B237745 : Blo 163797 237745 := bstep (se 2 (by rfl) ⟨89154, by rfl⟩ : syracuseStep 237745 = 178309) B178309
theorem B467153 : Blo 163797 467153 := bstep (se 2 (by rfl) ⟨175182, by rfl⟩ : syracuseStep 467153 = 350365) B350365
theorem B368945 : Blo 163797 368945 := bstep (se 2 (by rfl) ⟨138354, by rfl⟩ : syracuseStep 368945 = 276709) B276709
theorem B368963 : Blo 163797 368963 := bstep (se 1 (by rfl) ⟨276722, by rfl⟩ : syracuseStep 368963 = 553445) B553445
theorem B565649 : Blo 163797 565649 := bstep (se 2 (by rfl) ⟨212118, by rfl⟩ : syracuseStep 565649 = 424237) B424237
theorem B369233 : Blo 163797 369233 := bstep (se 2 (by rfl) ⟨138462, by rfl⟩ : syracuseStep 369233 = 276925) B276925
theorem B369251 : Blo 163797 369251 := bstep (se 1 (by rfl) ⟨276938, by rfl⟩ : syracuseStep 369251 = 553877) B553877
theorem B238241 : Blo 163797 238241 := bstep (se 2 (by rfl) ⟨89340, by rfl⟩ : syracuseStep 238241 = 178681) B178681
theorem B664433 : Blo 163797 664433 := bstep (se 2 (by rfl) ⟨249162, by rfl⟩ : syracuseStep 664433 = 498325) B498325
theorem B369521 : Blo 163797 369521 := bstep (se 2 (by rfl) ⟨138570, by rfl⟩ : syracuseStep 369521 = 277141) B277141
theorem B369539 : Blo 163797 369539 := bstep (se 1 (by rfl) ⟨277154, by rfl⟩ : syracuseStep 369539 = 554309) B554309
theorem B566189 : Blo 163797 566189 := bstep (se 3 (by rfl) ⟨106160, by rfl⟩ : syracuseStep 566189 = 212321) B212321
theorem B1582021 : Blo 163797 1582021 := bstep (se 4 (by rfl) ⟨148314, by rfl⟩ : syracuseStep 1582021 = 296629) B296629
theorem B566243 : Blo 163797 566243 := bstep (se 1 (by rfl) ⟨424682, by rfl⟩ : syracuseStep 566243 = 849365) B849365
theorem B631907 : Blo 163797 631907 := bstep (se 1 (by rfl) ⟨473930, by rfl⟩ : syracuseStep 631907 = 947861) B947861
theorem B631921 : Blo 163797 631921 := bstep (se 2 (by rfl) ⟨236970, by rfl⟩ : syracuseStep 631921 = 473941) B473941
theorem B468109 : Blo 163797 468109 := bstep (se 3 (by rfl) ⟨87770, by rfl⟩ : syracuseStep 468109 = 175541) B175541
theorem B369809 : Blo 163797 369809 := bstep (se 2 (by rfl) ⟨138678, by rfl⟩ : syracuseStep 369809 = 277357) B277357
theorem B369827 : Blo 163797 369827 := bstep (se 1 (by rfl) ⟨277370, by rfl⟩ : syracuseStep 369827 = 554741) B554741
theorem B468337 : Blo 163797 468337 := bstep (se 2 (by rfl) ⟨175626, by rfl⟩ : syracuseStep 468337 = 351253) B351253
theorem B533891 : Blo 163797 533891 := bstep (se 1 (by rfl) ⟨400418, by rfl⟩ : syracuseStep 533891 = 800837) B800837
theorem B370097 : Blo 163797 370097 := bstep (se 2 (by rfl) ⟨138786, by rfl⟩ : syracuseStep 370097 = 277573) B277573
theorem B370115 : Blo 163797 370115 := bstep (se 1 (by rfl) ⟨277586, by rfl⟩ : syracuseStep 370115 = 555173) B555173
theorem B468497 : Blo 163797 468497 := bstep (se 2 (by rfl) ⟨175686, by rfl⟩ : syracuseStep 468497 = 351373) B351373
theorem B468611 : Blo 163797 468611 := bstep (se 1 (by rfl) ⟨351458, by rfl⟩ : syracuseStep 468611 = 702917) B702917
theorem B370385 : Blo 163797 370385 := bstep (se 2 (by rfl) ⟨138894, by rfl⟩ : syracuseStep 370385 = 277789) B277789
theorem B566993 : Blo 163797 566993 := bstep (se 2 (by rfl) ⟨212622, by rfl⟩ : syracuseStep 566993 = 425245) B425245
theorem B370403 : Blo 163797 370403 := bstep (se 1 (by rfl) ⟨277802, by rfl⟩ : syracuseStep 370403 = 555605) B555605
theorem B1058629 : Blo 163797 1058629 := bstep (se 4 (by rfl) ⟨99246, by rfl⟩ : syracuseStep 1058629 = 198493) B198493
theorem B1517453 : Blo 163797 1517453 := bstep (se 3 (by rfl) ⟨284522, by rfl⟩ : syracuseStep 1517453 = 569045) B569045
theorem B370673 : Blo 163797 370673 := bstep (se 2 (by rfl) ⟨139002, by rfl⟩ : syracuseStep 370673 = 278005) B278005
theorem B370691 : Blo 163797 370691 := bstep (se 1 (by rfl) ⟨278018, by rfl⟩ : syracuseStep 370691 = 556037) B556037
theorem B2271473 : Blo 163797 2271473 := bstep (se 2 (by rfl) ⟨851802, by rfl⟩ : syracuseStep 2271473 = 1703605) B1703605
theorem B370961 : Blo 163797 370961 := bstep (se 2 (by rfl) ⟨139110, by rfl⟩ : syracuseStep 370961 = 278221) B278221
theorem B370979 : Blo 163797 370979 := bstep (se 1 (by rfl) ⟨278234, by rfl⟩ : syracuseStep 370979 = 556469) B556469
theorem B3909941 : Blo 163797 3909941 := bstep (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) B366557
theorem B600419 : Blo 163797 600419 := bstep (se 1 (by rfl) ⟨450314, by rfl⟩ : syracuseStep 600419 = 900629) B900629
theorem B633379 : Blo 163797 633379 := bstep (se 1 (by rfl) ⟨475034, by rfl⟩ : syracuseStep 633379 = 950069) B950069
theorem B371249 : Blo 163797 371249 := bstep (se 2 (by rfl) ⟨139218, by rfl⟩ : syracuseStep 371249 = 278437) B278437
theorem B371267 : Blo 163797 371267 := bstep (se 1 (by rfl) ⟨278450, by rfl⟩ : syracuseStep 371267 = 556901) B556901
theorem B469613 : Blo 163797 469613 := bstep (se 3 (by rfl) ⟨88052, by rfl⟩ : syracuseStep 469613 = 176105) B176105
theorem B633635 : Blo 163797 633635 := bstep (se 1 (by rfl) ⟨475226, by rfl⟩ : syracuseStep 633635 = 950453) B950453
theorem B469795 : Blo 163797 469795 := bstep (se 1 (by rfl) ⟨352346, by rfl⟩ : syracuseStep 469795 = 704693) B704693
theorem B371537 : Blo 163797 371537 := bstep (se 2 (by rfl) ⟨139326, by rfl⟩ : syracuseStep 371537 = 278653) B278653
theorem B371555 : Blo 163797 371555 := bstep (se 1 (by rfl) ⟨278666, by rfl⟩ : syracuseStep 371555 = 557333) B557333
theorem B273331 : Blo 163797 273331 := bstep (se 1 (by rfl) ⟨204998, by rfl⟩ : syracuseStep 273331 = 409997) B409997
theorem B469955 : Blo 163797 469955 := bstep (se 1 (by rfl) ⟨352466, by rfl⟩ : syracuseStep 469955 = 704933) B704933
theorem B2698211 : Blo 163797 2698211 := bstep (se 1 (by rfl) ⟨2023658, by rfl⟩ : syracuseStep 2698211 = 4047317) B4047317
theorem B1125389 : Blo 163797 1125389 := bstep (se 3 (by rfl) ⟨211010, by rfl⟩ : syracuseStep 1125389 = 422021) B422021
theorem B568333 : Blo 163797 568333 := bstep (se 3 (by rfl) ⟨106562, by rfl⟩ : syracuseStep 568333 = 213125) B213125
theorem B371825 : Blo 163797 371825 := bstep (se 2 (by rfl) ⟨139434, by rfl⟩ : syracuseStep 371825 = 278869) B278869
theorem B208003 : Blo 163797 208003 := bstep (se 1 (by rfl) ⟨156002, by rfl⟩ : syracuseStep 208003 = 312005) B312005
theorem B371843 : Blo 163797 371843 := bstep (se 1 (by rfl) ⟨278882, by rfl⟩ : syracuseStep 371843 = 557765) B557765
theorem B535697 : Blo 163797 535697 := bstep (se 2 (by rfl) ⟨200886, by rfl⟩ : syracuseStep 535697 = 401773) B401773
theorem B535747 : Blo 163797 535747 := bstep (se 1 (by rfl) ⟨401810, by rfl⟩ : syracuseStep 535747 = 803621) B803621
theorem B208099 : Blo 163797 208099 := bstep (se 1 (by rfl) ⟨156074, by rfl⟩ : syracuseStep 208099 = 312149) B312149
theorem B896291 : Blo 163797 896291 := bstep (se 1 (by rfl) ⟨672218, by rfl⟩ : syracuseStep 896291 = 1344437) B1344437
theorem B372113 : Blo 163797 372113 := bstep (se 2 (by rfl) ⟨139542, by rfl⟩ : syracuseStep 372113 = 279085) B279085
theorem B372131 : Blo 163797 372131 := bstep (se 1 (by rfl) ⟨279098, by rfl⟩ : syracuseStep 372131 = 558197) B558197
theorem B830897 : Blo 163797 830897 := bstep (se 2 (by rfl) ⟨311586, by rfl⟩ : syracuseStep 830897 = 623173) B623173
theorem B372401 : Blo 163797 372401 := bstep (se 2 (by rfl) ⟨139650, by rfl⟩ : syracuseStep 372401 = 279301) B279301
theorem B1814197 : Blo 163797 1814197 := bstep (se 5 (by rfl) ⟨85040, by rfl⟩ : syracuseStep 1814197 = 170081) B170081
theorem B372419 : Blo 163797 372419 := bstep (se 1 (by rfl) ⟨279314, by rfl⟩ : syracuseStep 372419 = 558629) B558629
theorem B208595 : Blo 163797 208595 := bstep (se 1 (by rfl) ⟨156446, by rfl⟩ : syracuseStep 208595 = 312893) B312893
theorem B536465 : Blo 163797 536465 := bstep (se 2 (by rfl) ⟨201174, by rfl⟩ : syracuseStep 536465 = 402349) B402349
theorem B339889 : Blo 163797 339889 := bstep (se 2 (by rfl) ⟨127458, by rfl⟩ : syracuseStep 339889 = 254917) B254917
theorem B372689 : Blo 163797 372689 := bstep (se 2 (by rfl) ⟨139758, by rfl⟩ : syracuseStep 372689 = 279517) B279517
theorem B372707 : Blo 163797 372707 := bstep (se 1 (by rfl) ⟨279530, by rfl⟩ : syracuseStep 372707 = 559061) B559061
theorem B471025 : Blo 163797 471025 := bstep (se 2 (by rfl) ⟨176634, by rfl⟩ : syracuseStep 471025 = 353269) B353269
theorem B176131 : Blo 163797 176131 := bstep (se 1 (by rfl) ⟨132098, by rfl⟩ : syracuseStep 176131 = 264197) B264197
theorem B372977 : Blo 163797 372977 := bstep (se 2 (by rfl) ⟨139866, by rfl⟩ : syracuseStep 372977 = 279733) B279733
theorem B372995 : Blo 163797 372995 := bstep (se 1 (by rfl) ⟨279746, by rfl⟩ : syracuseStep 372995 = 559493) B559493
theorem B536977 : Blo 163797 536977 := bstep (se 2 (by rfl) ⟨201366, by rfl⟩ : syracuseStep 536977 = 402733) B402733
theorem B209299 : Blo 163797 209299 := bstep (se 1 (by rfl) ⟨156974, by rfl⟩ : syracuseStep 209299 = 313949) B313949
theorem B930253 : Blo 163797 930253 := bstep (se 3 (by rfl) ⟨174422, by rfl⟩ : syracuseStep 930253 = 348845) B348845
theorem B209395 : Blo 163797 209395 := bstep (se 1 (by rfl) ⟨157046, by rfl⟩ : syracuseStep 209395 = 314093) B314093
theorem B373265 : Blo 163797 373265 := bstep (se 2 (by rfl) ⟨139974, by rfl⟩ : syracuseStep 373265 = 279949) B279949
theorem B373283 : Blo 163797 373283 := bstep (se 1 (by rfl) ⟨279962, by rfl⟩ : syracuseStep 373283 = 559925) B559925
theorem B635597 : Blo 163797 635597 := bstep (se 3 (by rfl) ⟨119174, by rfl⟩ : syracuseStep 635597 = 238349) B238349
theorem B1258253 : Blo 163797 1258253 := bstep (se 3 (by rfl) ⟨235922, by rfl⟩ : syracuseStep 1258253 = 471845) B471845
theorem B373553 : Blo 163797 373553 := bstep (se 2 (by rfl) ⟨140082, by rfl⟩ : syracuseStep 373553 = 280165) B280165
theorem B373571 : Blo 163797 373571 := bstep (se 1 (by rfl) ⟨280178, by rfl⟩ : syracuseStep 373571 = 560357) B560357
theorem B832355 : Blo 163797 832355 := bstep (se 1 (by rfl) ⟨624266, by rfl⟩ : syracuseStep 832355 = 1248533) B1248533
theorem B209891 : Blo 163797 209891 := bstep (se 1 (by rfl) ⟨157418, by rfl⟩ : syracuseStep 209891 = 314837) B314837
theorem B504845 : Blo 163797 504845 := bstep (se 3 (by rfl) ⟨94658, by rfl⟩ : syracuseStep 504845 = 189317) B189317
theorem B406595 : Blo 163797 406595 := bstep (se 1 (by rfl) ⟨304946, by rfl⟩ : syracuseStep 406595 = 609893) B609893
theorem B373841 : Blo 163797 373841 := bstep (se 2 (by rfl) ⟨140190, by rfl⟩ : syracuseStep 373841 = 280381) B280381
theorem B373859 : Blo 163797 373859 := bstep (se 1 (by rfl) ⟨280394, by rfl⟩ : syracuseStep 373859 = 560789) B560789
theorem B701617 : Blo 163797 701617 := bstep (se 2 (by rfl) ⟨263106, by rfl⟩ : syracuseStep 701617 = 526213) B526213
theorem B570577 : Blo 163797 570577 := bstep (se 2 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 570577 = 427933) B427933
theorem B472301 : Blo 163797 472301 := bstep (se 3 (by rfl) ⟨88556, by rfl⟩ : syracuseStep 472301 = 177113) B177113
theorem B177395 : Blo 163797 177395 := bstep (se 1 (by rfl) ⟨133046, by rfl⟩ : syracuseStep 177395 = 266093) B266093
theorem B374129 : Blo 163797 374129 := bstep (se 2 (by rfl) ⟨140298, by rfl⟩ : syracuseStep 374129 = 280597) B280597
theorem B374147 : Blo 163797 374147 := bstep (se 1 (by rfl) ⟨280610, by rfl⟩ : syracuseStep 374147 = 561221) B561221
theorem B996749 : Blo 163797 996749 := bstep (se 3 (by rfl) ⟨186890, by rfl⟩ : syracuseStep 996749 = 373781) B373781
theorem B472483 : Blo 163797 472483 := bstep (se 1 (by rfl) ⟨354362, by rfl⟩ : syracuseStep 472483 = 708725) B708725
theorem B472529 : Blo 163797 472529 := bstep (se 2 (by rfl) ⟨177198, by rfl⟩ : syracuseStep 472529 = 354397) B354397
theorem B1422917 : Blo 163797 1422917 := bstep (se 4 (by rfl) ⟨133398, by rfl⟩ : syracuseStep 1422917 = 266797) B266797
theorem B833165 : Blo 163797 833165 := bstep (se 3 (by rfl) ⟨156218, by rfl⟩ : syracuseStep 833165 = 312437) B312437
theorem B964237 : Blo 163797 964237 := bstep (se 3 (by rfl) ⟨180794, by rfl⟩ : syracuseStep 964237 = 361589) B361589
theorem B374417 : Blo 163797 374417 := bstep (se 2 (by rfl) ⟨140406, by rfl⟩ : syracuseStep 374417 = 280813) B280813
theorem B210595 : Blo 163797 210595 := bstep (se 1 (by rfl) ⟨157946, by rfl⟩ : syracuseStep 210595 = 315893) B315893
theorem B374435 : Blo 163797 374435 := bstep (se 1 (by rfl) ⟨280826, by rfl⟩ : syracuseStep 374435 = 561653) B561653
theorem B4830947 : Blo 163797 4830947 := bstep (se 1 (by rfl) ⟨3623210, by rfl⟩ : syracuseStep 4830947 = 7246421) B7246421
theorem B210691 : Blo 163797 210691 := bstep (se 1 (by rfl) ⟨158018, by rfl⟩ : syracuseStep 210691 = 316037) B316037
theorem B1357667 : Blo 163797 1357667 := bstep (se 1 (by rfl) ⟨1018250, by rfl⟩ : syracuseStep 1357667 = 2036501) B2036501
theorem B374705 : Blo 163797 374705 := bstep (se 2 (by rfl) ⟨140514, by rfl⟩ : syracuseStep 374705 = 281029) B281029
theorem B276419 : Blo 163797 276419 := bstep (se 1 (by rfl) ⟨207314, by rfl⟩ : syracuseStep 276419 = 414629) B414629
theorem B374723 : Blo 163797 374723 := bstep (se 1 (by rfl) ⟨281042, by rfl⟩ : syracuseStep 374723 = 562085) B562085
theorem B178147 : Blo 163797 178147 := bstep (se 1 (by rfl) ⟨133610, by rfl⟩ : syracuseStep 178147 = 267221) B267221
theorem B276547 : Blo 163797 276547 := bstep (se 1 (by rfl) ⟨207410, by rfl⟩ : syracuseStep 276547 = 414821) B414821
theorem B604273 : Blo 163797 604273 := bstep (se 2 (by rfl) ⟨226602, by rfl⟩ : syracuseStep 604273 = 453205) B453205
theorem B1128653 : Blo 163797 1128653 := bstep (se 3 (by rfl) ⟨211622, by rfl⟩ : syracuseStep 1128653 = 423245) B423245
theorem B276689 : Blo 163797 276689 := bstep (se 2 (by rfl) ⟨103758, by rfl⟩ : syracuseStep 276689 = 207517) B207517
theorem B374993 : Blo 163797 374993 := bstep (se 2 (by rfl) ⟨140622, by rfl⟩ : syracuseStep 374993 = 281245) B281245
theorem B375011 : Blo 163797 375011 := bstep (se 1 (by rfl) ⟨281258, by rfl⟩ : syracuseStep 375011 = 562517) B562517
theorem B1423601 : Blo 163797 1423601 := bstep (se 2 (by rfl) ⟨533850, by rfl⟩ : syracuseStep 1423601 = 1067701) B1067701
theorem B211187 : Blo 163797 211187 := bstep (se 1 (by rfl) ⟨158390, by rfl⟩ : syracuseStep 211187 = 316781) B316781
theorem B276817 : Blo 163797 276817 := bstep (se 2 (by rfl) ⟨103806, by rfl⟩ : syracuseStep 276817 = 207613) B207613
theorem B637283 : Blo 163797 637283 := bstep (se 1 (by rfl) ⟨477962, by rfl⟩ : syracuseStep 637283 = 955925) B955925
theorem B276851 : Blo 163797 276851 := bstep (se 1 (by rfl) ⟨207638, by rfl⟩ : syracuseStep 276851 = 415277) B415277
theorem B375281 : Blo 163797 375281 := bstep (se 2 (by rfl) ⟨140730, by rfl⟩ : syracuseStep 375281 = 281461) B281461
theorem B276979 : Blo 163797 276979 := bstep (se 1 (by rfl) ⟨207734, by rfl⟩ : syracuseStep 276979 = 415469) B415469
theorem B375299 : Blo 163797 375299 := bstep (se 1 (by rfl) ⟨281474, by rfl⟩ : syracuseStep 375299 = 562949) B562949
theorem B277121 : Blo 163797 277121 := bstep (se 2 (by rfl) ⟨103920, by rfl⟩ : syracuseStep 277121 = 207841) B207841
theorem B3029645 : Blo 163797 3029645 := bstep (se 3 (by rfl) ⟨568058, by rfl⟩ : syracuseStep 3029645 = 1136117) B1136117
theorem B1063601 : Blo 163797 1063601 := bstep (se 2 (by rfl) ⟨398850, by rfl⟩ : syracuseStep 1063601 = 797701) B797701
theorem B277249 : Blo 163797 277249 := bstep (se 2 (by rfl) ⟨103968, by rfl⟩ : syracuseStep 277249 = 207937) B207937
theorem B375569 : Blo 163797 375569 := bstep (se 2 (by rfl) ⟨140838, by rfl⟩ : syracuseStep 375569 = 281677) B281677
theorem B277283 : Blo 163797 277283 := bstep (se 1 (by rfl) ⟨207962, by rfl⟩ : syracuseStep 277283 = 415925) B415925
theorem B375587 : Blo 163797 375587 := bstep (se 1 (by rfl) ⟨281690, by rfl⟩ : syracuseStep 375587 = 563381) B563381
theorem B1194821 : Blo 163797 1194821 := bstep (se 4 (by rfl) ⟨112014, by rfl⟩ : syracuseStep 1194821 = 224029) B224029
theorem B473987 : Blo 163797 473987 := bstep (se 1 (by rfl) ⟨355490, by rfl⟩ : syracuseStep 473987 = 710981) B710981
theorem B277411 : Blo 163797 277411 := bstep (se 1 (by rfl) ⟨208058, by rfl⟩ : syracuseStep 277411 = 416117) B416117
theorem B211891 : Blo 163797 211891 := bstep (se 1 (by rfl) ⟨158918, by rfl⟩ : syracuseStep 211891 = 317837) B317837
theorem B2243555 : Blo 163797 2243555 := bstep (se 1 (by rfl) ⟨1682666, by rfl⟩ : syracuseStep 2243555 = 3365333) B3365333
theorem B211987 : Blo 163797 211987 := bstep (se 1 (by rfl) ⟨158990, by rfl⟩ : syracuseStep 211987 = 317981) B317981
theorem B277553 : Blo 163797 277553 := bstep (se 2 (by rfl) ⟨104082, by rfl⟩ : syracuseStep 277553 = 208165) B208165
theorem B375857 : Blo 163797 375857 := bstep (se 2 (by rfl) ⟨140946, by rfl⟩ : syracuseStep 375857 = 281893) B281893
theorem B375875 : Blo 163797 375875 := bstep (se 1 (by rfl) ⟨281906, by rfl⟩ : syracuseStep 375875 = 563813) B563813
theorem B474221 : Blo 163797 474221 := bstep (se 3 (by rfl) ⟨88916, by rfl⟩ : syracuseStep 474221 = 177833) B177833
theorem B277681 : Blo 163797 277681 := bstep (se 2 (by rfl) ⟨104130, by rfl⟩ : syracuseStep 277681 = 208261) B208261
theorem B277715 : Blo 163797 277715 := bstep (se 1 (by rfl) ⟨208286, by rfl⟩ : syracuseStep 277715 = 416573) B416573
theorem B1391843 : Blo 163797 1391843 := bstep (se 1 (by rfl) ⟨1043882, by rfl⟩ : syracuseStep 1391843 = 2087765) B2087765
theorem B507107 : Blo 163797 507107 := bstep (se 1 (by rfl) ⟨380330, by rfl⟩ : syracuseStep 507107 = 760661) B760661
theorem B376145 : Blo 163797 376145 := bstep (se 2 (by rfl) ⟨141054, by rfl⟩ : syracuseStep 376145 = 282109) B282109
theorem B277843 : Blo 163797 277843 := bstep (se 1 (by rfl) ⟨208382, by rfl⟩ : syracuseStep 277843 = 416765) B416765
theorem B376163 : Blo 163797 376163 := bstep (se 1 (by rfl) ⟨282122, by rfl⟩ : syracuseStep 376163 = 564245) B564245
theorem B474545 : Blo 163797 474545 := bstep (se 2 (by rfl) ⟨177954, by rfl⟩ : syracuseStep 474545 = 355909) B355909
theorem B277985 : Blo 163797 277985 := bstep (se 2 (by rfl) ⟨104244, by rfl⟩ : syracuseStep 277985 = 208489) B208489
theorem B343523 : Blo 163797 343523 := bstep (se 1 (by rfl) ⟨257642, by rfl⟩ : syracuseStep 343523 = 515285) B515285
theorem B278113 : Blo 163797 278113 := bstep (se 2 (by rfl) ⟨104292, by rfl⟩ : syracuseStep 278113 = 208585) B208585
theorem B1261169 : Blo 163797 1261169 := bstep (se 2 (by rfl) ⟨472938, by rfl⟩ : syracuseStep 1261169 = 945877) B945877
theorem B376433 : Blo 163797 376433 := bstep (se 2 (by rfl) ⟨141162, by rfl⟩ : syracuseStep 376433 = 282325) B282325
theorem B278147 : Blo 163797 278147 := bstep (se 1 (by rfl) ⟨208610, by rfl⟩ : syracuseStep 278147 = 417221) B417221
theorem B376451 : Blo 163797 376451 := bstep (se 1 (by rfl) ⟨282338, by rfl⟩ : syracuseStep 376451 = 564677) B564677
theorem B310979 : Blo 163797 310979 := bstep (se 1 (by rfl) ⟨233234, by rfl⟩ : syracuseStep 310979 = 466469) B466469
theorem B573155 : Blo 163797 573155 := bstep (se 1 (by rfl) ⟨429866, by rfl⟩ : syracuseStep 573155 = 859733) B859733
theorem B278275 : Blo 163797 278275 := bstep (se 1 (by rfl) ⟨208706, by rfl⟩ : syracuseStep 278275 = 417413) B417413
theorem B278417 : Blo 163797 278417 := bstep (se 2 (by rfl) ⟨104406, by rfl⟩ : syracuseStep 278417 = 208813) B208813
theorem B376721 : Blo 163797 376721 := bstep (se 2 (by rfl) ⟨141270, by rfl⟩ : syracuseStep 376721 = 282541) B282541
theorem B376739 : Blo 163797 376739 := bstep (se 1 (by rfl) ⟨282554, by rfl⟩ : syracuseStep 376739 = 565109) B565109
theorem B245699 : Blo 163797 245699 := bstep (se 1 (by rfl) ⟨184274, by rfl⟩ : syracuseStep 245699 = 368549) B368549
theorem B245729 : Blo 163797 245729 := bstep (se 2 (by rfl) ⟨92148, by rfl⟩ : syracuseStep 245729 = 184297) B184297
theorem B245747 : Blo 163797 245747 := bstep (se 1 (by rfl) ⟨184310, by rfl⟩ : syracuseStep 245747 = 368621) B368621
theorem B245777 : Blo 163797 245777 := bstep (se 2 (by rfl) ⟨92166, by rfl⟩ : syracuseStep 245777 = 184333) B184333
theorem B278545 : Blo 163797 278545 := bstep (se 2 (by rfl) ⟨104454, by rfl⟩ : syracuseStep 278545 = 208909) B208909
theorem B245795 : Blo 163797 245795 := bstep (se 1 (by rfl) ⟨184346, by rfl⟩ : syracuseStep 245795 = 368693) B368693
theorem B278579 : Blo 163797 278579 := bstep (se 1 (by rfl) ⟨208934, by rfl⟩ : syracuseStep 278579 = 417869) B417869
theorem B245825 : Blo 163797 245825 := bstep (se 2 (by rfl) ⟨92184, by rfl⟩ : syracuseStep 245825 = 184369) B184369
theorem B475217 : Blo 163797 475217 := bstep (se 2 (by rfl) ⟨178206, by rfl⟩ : syracuseStep 475217 = 356413) B356413
theorem B245843 : Blo 163797 245843 := bstep (se 1 (by rfl) ⟨184382, by rfl⟩ : syracuseStep 245843 = 368765) B368765
theorem B245873 : Blo 163797 245873 := bstep (se 2 (by rfl) ⟨92202, by rfl⟩ : syracuseStep 245873 = 184405) B184405
theorem B245891 : Blo 163797 245891 := bstep (se 1 (by rfl) ⟨184418, by rfl⟩ : syracuseStep 245891 = 368837) B368837
theorem B508045 : Blo 163797 508045 := bstep (se 3 (by rfl) ⟨95258, by rfl⟩ : syracuseStep 508045 = 190517) B190517
theorem B245921 : Blo 163797 245921 := bstep (se 2 (by rfl) ⟨92220, by rfl⟩ : syracuseStep 245921 = 184441) B184441
theorem B1097891 : Blo 163797 1097891 := bstep (se 1 (by rfl) ⟨823418, by rfl⟩ : syracuseStep 1097891 = 1646837) B1646837
theorem B377009 : Blo 163797 377009 := bstep (se 2 (by rfl) ⟨141378, by rfl⟩ : syracuseStep 377009 = 282757) B282757
theorem B245939 : Blo 163797 245939 := bstep (se 1 (by rfl) ⟨184454, by rfl⟩ : syracuseStep 245939 = 368909) B368909
theorem B278707 : Blo 163797 278707 := bstep (se 1 (by rfl) ⟨209030, by rfl⟩ : syracuseStep 278707 = 418061) B418061
theorem B377027 : Blo 163797 377027 := bstep (se 1 (by rfl) ⟨282770, by rfl⟩ : syracuseStep 377027 = 565541) B565541
theorem B245969 : Blo 163797 245969 := bstep (se 2 (by rfl) ⟨92238, by rfl⟩ : syracuseStep 245969 = 184477) B184477
theorem B245987 : Blo 163797 245987 := bstep (se 1 (by rfl) ⟨184490, by rfl⟩ : syracuseStep 245987 = 368981) B368981
theorem B246017 : Blo 163797 246017 := bstep (se 2 (by rfl) ⟨92256, by rfl⟩ : syracuseStep 246017 = 184513) B184513
theorem B246035 : Blo 163797 246035 := bstep (se 1 (by rfl) ⟨184526, by rfl⟩ : syracuseStep 246035 = 369053) B369053
theorem B246065 : Blo 163797 246065 := bstep (se 2 (by rfl) ⟨92274, by rfl⟩ : syracuseStep 246065 = 184549) B184549
theorem B278849 : Blo 163797 278849 := bstep (se 2 (by rfl) ⟨104568, by rfl⟩ : syracuseStep 278849 = 209137) B209137
theorem B246083 : Blo 163797 246083 := bstep (se 1 (by rfl) ⟨184562, by rfl⟩ : syracuseStep 246083 = 369125) B369125
theorem B934213 : Blo 163797 934213 := bstep (se 4 (by rfl) ⟨87582, by rfl⟩ : syracuseStep 934213 = 175165) B175165
theorem B246113 : Blo 163797 246113 := bstep (se 2 (by rfl) ⟨92292, by rfl⟩ : syracuseStep 246113 = 184585) B184585
theorem B246131 : Blo 163797 246131 := bstep (se 1 (by rfl) ⟨184598, by rfl⟩ : syracuseStep 246131 = 369197) B369197
theorem B246161 : Blo 163797 246161 := bstep (se 2 (by rfl) ⟨92310, by rfl⟩ : syracuseStep 246161 = 184621) B184621
theorem B246179 : Blo 163797 246179 := bstep (se 1 (by rfl) ⟨184634, by rfl⟩ : syracuseStep 246179 = 369269) B369269
theorem B246209 : Blo 163797 246209 := bstep (se 2 (by rfl) ⟨92328, by rfl⟩ : syracuseStep 246209 = 184657) B184657
theorem B278977 : Blo 163797 278977 := bstep (se 2 (by rfl) ⟨104616, by rfl⟩ : syracuseStep 278977 = 209233) B209233
theorem B377297 : Blo 163797 377297 := bstep (se 2 (by rfl) ⟨141486, by rfl⟩ : syracuseStep 377297 = 282973) B282973
theorem B246227 : Blo 163797 246227 := bstep (se 1 (by rfl) ⟨184670, by rfl⟩ : syracuseStep 246227 = 369341) B369341
theorem B279011 : Blo 163797 279011 := bstep (se 1 (by rfl) ⟨209258, by rfl⟩ : syracuseStep 279011 = 418517) B418517
theorem B377315 : Blo 163797 377315 := bstep (se 1 (by rfl) ⟨282986, by rfl⟩ : syracuseStep 377315 = 565973) B565973
theorem B246257 : Blo 163797 246257 := bstep (se 2 (by rfl) ⟨92346, by rfl⟩ : syracuseStep 246257 = 184693) B184693
theorem B836081 : Blo 163797 836081 := bstep (se 2 (by rfl) ⟨313530, by rfl⟩ : syracuseStep 836081 = 627061) B627061
theorem B246275 : Blo 163797 246275 := bstep (se 1 (by rfl) ⟨184706, by rfl⟩ : syracuseStep 246275 = 369413) B369413
theorem B246305 : Blo 163797 246305 := bstep (se 2 (by rfl) ⟨92364, by rfl⟩ : syracuseStep 246305 = 184729) B184729
theorem B246323 : Blo 163797 246323 := bstep (se 1 (by rfl) ⟨184742, by rfl⟩ : syracuseStep 246323 = 369485) B369485
theorem B246353 : Blo 163797 246353 := bstep (se 2 (by rfl) ⟨92382, by rfl⟩ : syracuseStep 246353 = 184765) B184765
theorem B246371 : Blo 163797 246371 := bstep (se 1 (by rfl) ⟨184778, by rfl⟩ : syracuseStep 246371 = 369557) B369557
theorem B279139 : Blo 163797 279139 := bstep (se 1 (by rfl) ⟨209354, by rfl⟩ : syracuseStep 279139 = 418709) B418709
theorem B311921 : Blo 163797 311921 := bstep (se 2 (by rfl) ⟨116970, by rfl⟩ : syracuseStep 311921 = 233941) B233941
theorem B246401 : Blo 163797 246401 := bstep (se 2 (by rfl) ⟨92400, by rfl⟩ : syracuseStep 246401 = 184801) B184801
theorem B246419 : Blo 163797 246419 := bstep (se 1 (by rfl) ⟨184814, by rfl⟩ : syracuseStep 246419 = 369629) B369629
theorem B246449 : Blo 163797 246449 := bstep (se 2 (by rfl) ⟨92418, by rfl⟩ : syracuseStep 246449 = 184837) B184837
theorem B246467 : Blo 163797 246467 := bstep (se 1 (by rfl) ⟨184850, by rfl⟩ : syracuseStep 246467 = 369701) B369701
theorem B1000133 : Blo 163797 1000133 := bstep (se 4 (by rfl) ⟨93762, by rfl⟩ : syracuseStep 1000133 = 187525) B187525
theorem B246497 : Blo 163797 246497 := bstep (se 2 (by rfl) ⟨92436, by rfl⟩ : syracuseStep 246497 = 184873) B184873
theorem B279281 : Blo 163797 279281 := bstep (se 2 (by rfl) ⟨104730, by rfl⟩ : syracuseStep 279281 = 209461) B209461
theorem B246515 : Blo 163797 246515 := bstep (se 1 (by rfl) ⟨184886, by rfl⟩ : syracuseStep 246515 = 369773) B369773
theorem B705293 : Blo 163797 705293 := bstep (se 3 (by rfl) ⟨132242, by rfl⟩ : syracuseStep 705293 = 264485) B264485
theorem B246545 : Blo 163797 246545 := bstep (se 2 (by rfl) ⟨92454, by rfl⟩ : syracuseStep 246545 = 184909) B184909
theorem B246563 : Blo 163797 246563 := bstep (se 1 (by rfl) ⟨184922, by rfl⟩ : syracuseStep 246563 = 369845) B369845
theorem B246593 : Blo 163797 246593 := bstep (se 2 (by rfl) ⟨92472, by rfl⟩ : syracuseStep 246593 = 184945) B184945
theorem B246611 : Blo 163797 246611 := bstep (se 1 (by rfl) ⟨184958, by rfl⟩ : syracuseStep 246611 = 369917) B369917
theorem B246641 : Blo 163797 246641 := bstep (se 2 (by rfl) ⟨92490, by rfl⟩ : syracuseStep 246641 = 184981) B184981
theorem B279409 : Blo 163797 279409 := bstep (se 2 (by rfl) ⟨104778, by rfl⟩ : syracuseStep 279409 = 209557) B209557
theorem B246659 : Blo 163797 246659 := bstep (se 1 (by rfl) ⟨184994, by rfl⟩ : syracuseStep 246659 = 369989) B369989
theorem B279443 : Blo 163797 279443 := bstep (se 1 (by rfl) ⟨209582, by rfl⟩ : syracuseStep 279443 = 419165) B419165
theorem B246689 : Blo 163797 246689 := bstep (se 2 (by rfl) ⟨92508, by rfl⟩ : syracuseStep 246689 = 185017) B185017
theorem B508835 : Blo 163797 508835 := bstep (se 1 (by rfl) ⟨381626, by rfl⟩ : syracuseStep 508835 = 763253) B763253
theorem B246707 : Blo 163797 246707 := bstep (se 1 (by rfl) ⟨185030, by rfl⟩ : syracuseStep 246707 = 370061) B370061
theorem B246737 : Blo 163797 246737 := bstep (se 2 (by rfl) ⟨92526, by rfl⟩ : syracuseStep 246737 = 185053) B185053
theorem B246755 : Blo 163797 246755 := bstep (se 1 (by rfl) ⟨185066, by rfl⟩ : syracuseStep 246755 = 370133) B370133
theorem B246785 : Blo 163797 246785 := bstep (se 2 (by rfl) ⟨92544, by rfl⟩ : syracuseStep 246785 = 185089) B185089
theorem B508931 : Blo 163797 508931 := bstep (se 1 (by rfl) ⟨381698, by rfl⟩ : syracuseStep 508931 = 763397) B763397
theorem B246803 : Blo 163797 246803 := bstep (se 1 (by rfl) ⟨185102, by rfl⟩ : syracuseStep 246803 = 370205) B370205
theorem B279571 : Blo 163797 279571 := bstep (se 1 (by rfl) ⟨209678, by rfl⟩ : syracuseStep 279571 = 419357) B419357
theorem B246833 : Blo 163797 246833 := bstep (se 2 (by rfl) ⟨92562, by rfl⟩ : syracuseStep 246833 = 185125) B185125
theorem B246851 : Blo 163797 246851 := bstep (se 1 (by rfl) ⟨185138, by rfl⟩ : syracuseStep 246851 = 370277) B370277
theorem B1066061 : Blo 163797 1066061 := bstep (se 3 (by rfl) ⟨199886, by rfl⟩ : syracuseStep 1066061 = 399773) B399773
theorem B246881 : Blo 163797 246881 := bstep (se 2 (by rfl) ⟨92580, by rfl⟩ : syracuseStep 246881 = 185161) B185161
theorem B246899 : Blo 163797 246899 := bstep (se 1 (by rfl) ⟨185174, by rfl⟩ : syracuseStep 246899 = 370349) B370349
theorem B246929 : Blo 163797 246929 := bstep (se 2 (by rfl) ⟨92598, by rfl⟩ : syracuseStep 246929 = 185197) B185197
theorem B279713 : Blo 163797 279713 := bstep (se 2 (by rfl) ⟨104892, by rfl⟩ : syracuseStep 279713 = 209785) B209785
theorem B246947 : Blo 163797 246947 := bstep (se 1 (by rfl) ⟨185210, by rfl⟩ : syracuseStep 246947 = 370421) B370421
theorem B246977 : Blo 163797 246977 := bstep (se 2 (by rfl) ⟨92616, by rfl⟩ : syracuseStep 246977 = 185233) B185233
theorem B246995 : Blo 163797 246995 := bstep (se 1 (by rfl) ⟨185246, by rfl⟩ : syracuseStep 246995 = 370493) B370493
theorem B247025 : Blo 163797 247025 := bstep (se 2 (by rfl) ⟨92634, by rfl⟩ : syracuseStep 247025 = 185269) B185269
theorem B247043 : Blo 163797 247043 := bstep (se 1 (by rfl) ⟨185282, by rfl⟩ : syracuseStep 247043 = 370565) B370565
theorem B247073 : Blo 163797 247073 := bstep (se 2 (by rfl) ⟨92652, by rfl⟩ : syracuseStep 247073 = 185305) B185305
theorem B279841 : Blo 163797 279841 := bstep (se 2 (by rfl) ⟨104940, by rfl⟩ : syracuseStep 279841 = 209881) B209881
theorem B247091 : Blo 163797 247091 := bstep (se 1 (by rfl) ⟨185318, by rfl⟩ : syracuseStep 247091 = 370637) B370637
theorem B279875 : Blo 163797 279875 := bstep (se 1 (by rfl) ⟨209906, by rfl⟩ : syracuseStep 279875 = 419813) B419813
theorem B247121 : Blo 163797 247121 := bstep (se 2 (by rfl) ⟨92670, by rfl⟩ : syracuseStep 247121 = 185341) B185341
theorem B247139 : Blo 163797 247139 := bstep (se 1 (by rfl) ⟨185354, by rfl⟩ : syracuseStep 247139 = 370709) B370709
theorem B247169 : Blo 163797 247169 := bstep (se 2 (by rfl) ⟨92688, by rfl⟩ : syracuseStep 247169 = 185377) B185377
theorem B247187 : Blo 163797 247187 := bstep (se 1 (by rfl) ⟨185390, by rfl⟩ : syracuseStep 247187 = 370781) B370781
theorem B607651 : Blo 163797 607651 := bstep (se 1 (by rfl) ⟨455738, by rfl⟩ : syracuseStep 607651 = 911477) B911477
theorem B247217 : Blo 163797 247217 := bstep (se 2 (by rfl) ⟨92706, by rfl⟩ : syracuseStep 247217 = 185413) B185413
theorem B443843 : Blo 163797 443843 := bstep (se 1 (by rfl) ⟨332882, by rfl⟩ : syracuseStep 443843 = 665765) B665765
theorem B247235 : Blo 163797 247235 := bstep (se 1 (by rfl) ⟨185426, by rfl⟩ : syracuseStep 247235 = 370853) B370853
theorem B280003 : Blo 163797 280003 := bstep (se 1 (by rfl) ⟨210002, by rfl⟩ : syracuseStep 280003 = 420005) B420005
theorem B247265 : Blo 163797 247265 := bstep (se 2 (by rfl) ⟨92724, by rfl⟩ : syracuseStep 247265 = 185449) B185449
theorem B2377187 : Blo 163797 2377187 := bstep (se 1 (by rfl) ⟨1782890, by rfl⟩ : syracuseStep 2377187 = 3565781) B3565781
theorem B312817 : Blo 163797 312817 := bstep (se 2 (by rfl) ⟨117306, by rfl⟩ : syracuseStep 312817 = 234613) B234613
theorem B247283 : Blo 163797 247283 := bstep (se 1 (by rfl) ⟨185462, by rfl⟩ : syracuseStep 247283 = 370925) B370925
theorem B476675 : Blo 163797 476675 := bstep (se 1 (by rfl) ⟨357506, by rfl⟩ : syracuseStep 476675 = 715013) B715013
theorem B247313 : Blo 163797 247313 := bstep (se 2 (by rfl) ⟨92742, by rfl⟩ : syracuseStep 247313 = 185485) B185485
theorem B247331 : Blo 163797 247331 := bstep (se 1 (by rfl) ⟨185498, by rfl⟩ : syracuseStep 247331 = 370997) B370997
theorem B247361 : Blo 163797 247361 := bstep (se 2 (by rfl) ⟨92760, by rfl⟩ : syracuseStep 247361 = 185521) B185521
theorem B280145 : Blo 163797 280145 := bstep (se 2 (by rfl) ⟨105054, by rfl⟩ : syracuseStep 280145 = 210109) B210109
theorem B247379 : Blo 163797 247379 := bstep (se 1 (by rfl) ⟨185534, by rfl⟩ : syracuseStep 247379 = 371069) B371069
theorem B247409 : Blo 163797 247409 := bstep (se 2 (by rfl) ⟨92778, by rfl⟩ : syracuseStep 247409 = 185557) B185557
theorem B247427 : Blo 163797 247427 := bstep (se 1 (by rfl) ⟨185570, by rfl⟩ : syracuseStep 247427 = 371141) B371141
theorem B312977 : Blo 163797 312977 := bstep (se 2 (by rfl) ⟨117366, by rfl⟩ : syracuseStep 312977 = 234733) B234733
theorem B247457 : Blo 163797 247457 := bstep (se 2 (by rfl) ⟨92796, by rfl⟩ : syracuseStep 247457 = 185593) B185593
theorem B247475 : Blo 163797 247475 := bstep (se 1 (by rfl) ⟨185606, by rfl⟩ : syracuseStep 247475 = 371213) B371213
theorem B247505 : Blo 163797 247505 := bstep (se 2 (by rfl) ⟨92814, by rfl⟩ : syracuseStep 247505 = 185629) B185629
theorem B280273 : Blo 163797 280273 := bstep (se 2 (by rfl) ⟨105102, by rfl⟩ : syracuseStep 280273 = 210205) B210205
theorem B247523 : Blo 163797 247523 := bstep (se 1 (by rfl) ⟨185642, by rfl⟩ : syracuseStep 247523 = 371285) B371285
theorem B280307 : Blo 163797 280307 := bstep (se 1 (by rfl) ⟨210230, by rfl⟩ : syracuseStep 280307 = 420461) B420461
theorem B247553 : Blo 163797 247553 := bstep (se 2 (by rfl) ⟨92832, by rfl⟩ : syracuseStep 247553 = 185665) B185665
theorem B247571 : Blo 163797 247571 := bstep (se 1 (by rfl) ⟨185678, by rfl⟩ : syracuseStep 247571 = 371357) B371357
theorem B444209 : Blo 163797 444209 := bstep (se 2 (by rfl) ⟨166578, by rfl⟩ : syracuseStep 444209 = 333157) B333157
theorem B247601 : Blo 163797 247601 := bstep (se 2 (by rfl) ⟨92850, by rfl⟩ : syracuseStep 247601 = 185701) B185701
theorem B247619 : Blo 163797 247619 := bstep (se 1 (by rfl) ⟨185714, by rfl⟩ : syracuseStep 247619 = 371429) B371429
theorem B247649 : Blo 163797 247649 := bstep (se 2 (by rfl) ⟨92868, by rfl⟩ : syracuseStep 247649 = 185737) B185737
theorem B247667 : Blo 163797 247667 := bstep (se 1 (by rfl) ⟨185750, by rfl⟩ : syracuseStep 247667 = 371501) B371501
theorem B280435 : Blo 163797 280435 := bstep (se 1 (by rfl) ⟨210326, by rfl⟩ : syracuseStep 280435 = 420653) B420653
theorem B247697 : Blo 163797 247697 := bstep (se 2 (by rfl) ⟨92886, by rfl⟩ : syracuseStep 247697 = 185773) B185773
theorem B247715 : Blo 163797 247715 := bstep (se 1 (by rfl) ⟨185786, by rfl⟩ : syracuseStep 247715 = 371573) B371573
theorem B837539 : Blo 163797 837539 := bstep (se 1 (by rfl) ⟨628154, by rfl⟩ : syracuseStep 837539 = 1256309) B1256309
theorem B247745 : Blo 163797 247745 := bstep (se 2 (by rfl) ⟨92904, by rfl⟩ : syracuseStep 247745 = 185809) B185809
theorem B247763 : Blo 163797 247763 := bstep (se 1 (by rfl) ⟨185822, by rfl⟩ : syracuseStep 247763 = 371645) B371645
theorem B247793 : Blo 163797 247793 := bstep (se 2 (by rfl) ⟨92922, by rfl⟩ : syracuseStep 247793 = 185845) B185845
theorem B280577 : Blo 163797 280577 := bstep (se 2 (by rfl) ⟨105216, by rfl⟩ : syracuseStep 280577 = 210433) B210433
theorem B247811 : Blo 163797 247811 := bstep (se 1 (by rfl) ⟨185858, by rfl⟩ : syracuseStep 247811 = 371717) B371717
theorem B247841 : Blo 163797 247841 := bstep (se 2 (by rfl) ⟨92940, by rfl⟩ : syracuseStep 247841 = 185881) B185881
theorem B313379 : Blo 163797 313379 := bstep (se 1 (by rfl) ⟨235034, by rfl⟩ : syracuseStep 313379 = 470069) B470069
theorem B247859 : Blo 163797 247859 := bstep (se 1 (by rfl) ⟨185894, by rfl⟩ : syracuseStep 247859 = 371789) B371789
theorem B247889 : Blo 163797 247889 := bstep (se 2 (by rfl) ⟨92958, by rfl⟩ : syracuseStep 247889 = 185917) B185917
theorem B247907 : Blo 163797 247907 := bstep (se 1 (by rfl) ⟨185930, by rfl⟩ : syracuseStep 247907 = 371861) B371861
theorem B247937 : Blo 163797 247937 := bstep (se 2 (by rfl) ⟨92976, by rfl⟩ : syracuseStep 247937 = 185953) B185953
theorem B280705 : Blo 163797 280705 := bstep (se 2 (by rfl) ⟨105264, by rfl⟩ : syracuseStep 280705 = 210529) B210529
theorem B247955 : Blo 163797 247955 := bstep (se 1 (by rfl) ⟨185966, by rfl⟩ : syracuseStep 247955 = 371933) B371933
theorem B280739 : Blo 163797 280739 := bstep (se 1 (by rfl) ⟨210554, by rfl⟩ : syracuseStep 280739 = 421109) B421109
theorem B247985 : Blo 163797 247985 := bstep (se 2 (by rfl) ⟨92994, by rfl⟩ : syracuseStep 247985 = 185989) B185989
theorem B248003 : Blo 163797 248003 := bstep (se 1 (by rfl) ⟨186002, by rfl⟩ : syracuseStep 248003 = 372005) B372005
theorem B248033 : Blo 163797 248033 := bstep (se 2 (by rfl) ⟨93012, by rfl⟩ : syracuseStep 248033 = 186025) B186025
theorem B248051 : Blo 163797 248051 := bstep (se 1 (by rfl) ⟨186038, by rfl⟩ : syracuseStep 248051 = 372077) B372077
theorem B936197 : Blo 163797 936197 := bstep (se 4 (by rfl) ⟨87768, by rfl⟩ : syracuseStep 936197 = 175537) B175537
theorem B444685 : Blo 163797 444685 := bstep (se 3 (by rfl) ⟨83378, by rfl⟩ : syracuseStep 444685 = 166757) B166757
theorem B248081 : Blo 163797 248081 := bstep (se 2 (by rfl) ⟨93030, by rfl⟩ : syracuseStep 248081 = 186061) B186061
theorem B248099 : Blo 163797 248099 := bstep (se 1 (by rfl) ⟨186074, by rfl⟩ : syracuseStep 248099 = 372149) B372149
theorem B280867 : Blo 163797 280867 := bstep (se 1 (by rfl) ⟨210650, by rfl⟩ : syracuseStep 280867 = 421301) B421301
theorem B477485 : Blo 163797 477485 := bstep (se 3 (by rfl) ⟨89528, by rfl⟩ : syracuseStep 477485 = 179057) B179057
theorem B903473 : Blo 163797 903473 := bstep (se 2 (by rfl) ⟨338802, by rfl⟩ : syracuseStep 903473 = 677605) B677605
theorem B248129 : Blo 163797 248129 := bstep (se 2 (by rfl) ⟨93048, by rfl⟩ : syracuseStep 248129 = 186097) B186097
theorem B248147 : Blo 163797 248147 := bstep (se 1 (by rfl) ⟨186110, by rfl⟩ : syracuseStep 248147 = 372221) B372221
theorem B248177 : Blo 163797 248177 := bstep (se 2 (by rfl) ⟨93066, by rfl⟩ : syracuseStep 248177 = 186133) B186133
theorem B248195 : Blo 163797 248195 := bstep (se 1 (by rfl) ⟨186146, by rfl⟩ : syracuseStep 248195 = 372293) B372293
theorem B248225 : Blo 163797 248225 := bstep (se 2 (by rfl) ⟨93084, by rfl⟩ : syracuseStep 248225 = 186169) B186169
theorem B281009 : Blo 163797 281009 := bstep (se 2 (by rfl) ⟨105378, by rfl⟩ : syracuseStep 281009 = 210757) B210757
theorem B248243 : Blo 163797 248243 := bstep (se 1 (by rfl) ⟨186182, by rfl⟩ : syracuseStep 248243 = 372365) B372365
theorem B248273 : Blo 163797 248273 := bstep (se 2 (by rfl) ⟨93102, by rfl⟩ : syracuseStep 248273 = 186205) B186205
theorem B248291 : Blo 163797 248291 := bstep (se 1 (by rfl) ⟨186218, by rfl⟩ : syracuseStep 248291 = 372437) B372437
theorem B477677 : Blo 163797 477677 := bstep (se 3 (by rfl) ⟨89564, by rfl⟩ : syracuseStep 477677 = 179129) B179129
theorem B281075 : Blo 163797 281075 := bstep (se 1 (by rfl) ⟨210806, by rfl⟩ : syracuseStep 281075 = 421613) B421613
theorem B248321 : Blo 163797 248321 := bstep (se 2 (by rfl) ⟨93120, by rfl⟩ : syracuseStep 248321 = 186241) B186241
theorem B248339 : Blo 163797 248339 := bstep (se 1 (by rfl) ⟨186254, by rfl⟩ : syracuseStep 248339 = 372509) B372509
theorem B477731 : Blo 163797 477731 := bstep (se 1 (by rfl) ⟨358298, by rfl⟩ : syracuseStep 477731 = 716597) B716597
theorem B248369 : Blo 163797 248369 := bstep (se 2 (by rfl) ⟨93138, by rfl⟩ : syracuseStep 248369 = 186277) B186277
theorem B281137 : Blo 163797 281137 := bstep (se 2 (by rfl) ⟨105426, by rfl⟩ : syracuseStep 281137 = 210853) B210853
theorem B248387 : Blo 163797 248387 := bstep (se 1 (by rfl) ⟨186290, by rfl⟩ : syracuseStep 248387 = 372581) B372581
theorem B281171 : Blo 163797 281171 := bstep (se 1 (by rfl) ⟨210878, by rfl⟩ : syracuseStep 281171 = 421757) B421757
theorem B248417 : Blo 163797 248417 := bstep (se 2 (by rfl) ⟨93156, by rfl⟩ : syracuseStep 248417 = 186313) B186313
theorem B248435 : Blo 163797 248435 := bstep (se 1 (by rfl) ⟨186326, by rfl⟩ : syracuseStep 248435 = 372653) B372653
theorem B248465 : Blo 163797 248465 := bstep (se 2 (by rfl) ⟨93174, by rfl⟩ : syracuseStep 248465 = 186349) B186349
theorem B248483 : Blo 163797 248483 := bstep (se 1 (by rfl) ⟨186362, by rfl⟩ : syracuseStep 248483 = 372725) B372725
theorem B510637 : Blo 163797 510637 := bstep (se 3 (by rfl) ⟨95744, by rfl⟩ : syracuseStep 510637 = 191489) B191489
theorem B248513 : Blo 163797 248513 := bstep (se 2 (by rfl) ⟨93192, by rfl⟩ : syracuseStep 248513 = 186385) B186385
theorem B838349 : Blo 163797 838349 := bstep (se 3 (by rfl) ⟨157190, by rfl⟩ : syracuseStep 838349 = 314381) B314381
theorem B248531 : Blo 163797 248531 := bstep (se 1 (by rfl) ⟨186398, by rfl⟩ : syracuseStep 248531 = 372797) B372797
theorem B281299 : Blo 163797 281299 := bstep (se 1 (by rfl) ⟨210974, by rfl⟩ : syracuseStep 281299 = 421949) B421949
theorem B2149091 : Blo 163797 2149091 := bstep (se 1 (by rfl) ⟨1611818, by rfl⟩ : syracuseStep 2149091 = 3223637) B3223637
theorem B248561 : Blo 163797 248561 := bstep (se 2 (by rfl) ⟨93210, by rfl⟩ : syracuseStep 248561 = 186421) B186421
theorem B248579 : Blo 163797 248579 := bstep (se 1 (by rfl) ⟨186434, by rfl⟩ : syracuseStep 248579 = 372869) B372869
theorem B248609 : Blo 163797 248609 := bstep (se 2 (by rfl) ⟨93228, by rfl⟩ : syracuseStep 248609 = 186457) B186457
theorem B248627 : Blo 163797 248627 := bstep (se 1 (by rfl) ⟨186470, by rfl⟩ : syracuseStep 248627 = 372941) B372941
theorem B248657 : Blo 163797 248657 := bstep (se 2 (by rfl) ⟨93246, by rfl⟩ : syracuseStep 248657 = 186493) B186493
theorem B281441 : Blo 163797 281441 := bstep (se 2 (by rfl) ⟨105540, by rfl⟩ : syracuseStep 281441 = 211081) B211081
theorem B248675 : Blo 163797 248675 := bstep (se 1 (by rfl) ⟨186506, by rfl⟩ : syracuseStep 248675 = 373013) B373013
theorem B248705 : Blo 163797 248705 := bstep (se 2 (by rfl) ⟨93264, by rfl⟩ : syracuseStep 248705 = 186529) B186529
theorem B248723 : Blo 163797 248723 := bstep (se 1 (by rfl) ⟨186542, by rfl⟩ : syracuseStep 248723 = 373085) B373085
theorem B314275 : Blo 163797 314275 := bstep (se 1 (by rfl) ⟨235706, by rfl⟩ : syracuseStep 314275 = 471413) B471413
theorem B248753 : Blo 163797 248753 := bstep (se 2 (by rfl) ⟨93282, by rfl⟩ : syracuseStep 248753 = 186565) B186565
theorem B248771 : Blo 163797 248771 := bstep (se 1 (by rfl) ⟨186578, by rfl⟩ : syracuseStep 248771 = 373157) B373157
theorem B248801 : Blo 163797 248801 := bstep (se 2 (by rfl) ⟨93300, by rfl⟩ : syracuseStep 248801 = 186601) B186601
theorem B281569 : Blo 163797 281569 := bstep (se 2 (by rfl) ⟨105588, by rfl⟩ : syracuseStep 281569 = 211177) B211177
theorem B248819 : Blo 163797 248819 := bstep (se 1 (by rfl) ⟨186614, by rfl⟩ : syracuseStep 248819 = 373229) B373229
theorem B281603 : Blo 163797 281603 := bstep (se 1 (by rfl) ⟨211202, by rfl⟩ : syracuseStep 281603 = 422405) B422405
theorem B248849 : Blo 163797 248849 := bstep (se 2 (by rfl) ⟨93318, by rfl⟩ : syracuseStep 248849 = 186637) B186637
theorem B248867 : Blo 163797 248867 := bstep (se 1 (by rfl) ⟨186650, by rfl⟩ : syracuseStep 248867 = 373301) B373301
theorem B248897 : Blo 163797 248897 := bstep (se 2 (by rfl) ⟨93336, by rfl⟩ : syracuseStep 248897 = 186673) B186673
theorem B314435 : Blo 163797 314435 := bstep (se 1 (by rfl) ⟨235826, by rfl⟩ : syracuseStep 314435 = 471653) B471653
theorem B248915 : Blo 163797 248915 := bstep (se 1 (by rfl) ⟨186686, by rfl⟩ : syracuseStep 248915 = 373373) B373373
theorem B248945 : Blo 163797 248945 := bstep (se 2 (by rfl) ⟨93354, by rfl⟩ : syracuseStep 248945 = 186709) B186709
theorem B248963 : Blo 163797 248963 := bstep (se 1 (by rfl) ⟨186722, by rfl⟩ : syracuseStep 248963 = 373445) B373445
theorem B281731 : Blo 163797 281731 := bstep (se 1 (by rfl) ⟨211298, by rfl⟩ : syracuseStep 281731 = 422597) B422597
theorem B248993 : Blo 163797 248993 := bstep (se 2 (by rfl) ⟨93372, by rfl⟩ : syracuseStep 248993 = 186745) B186745
theorem B249011 : Blo 163797 249011 := bstep (se 1 (by rfl) ⟨186758, by rfl⟩ : syracuseStep 249011 = 373517) B373517
theorem B249041 : Blo 163797 249041 := bstep (se 2 (by rfl) ⟨93390, by rfl⟩ : syracuseStep 249041 = 186781) B186781
theorem B249059 : Blo 163797 249059 := bstep (se 1 (by rfl) ⟨186794, by rfl⟩ : syracuseStep 249059 = 373589) B373589
theorem B249089 : Blo 163797 249089 := bstep (se 2 (by rfl) ⟨93408, by rfl⟩ : syracuseStep 249089 = 186817) B186817
theorem B281873 : Blo 163797 281873 := bstep (se 2 (by rfl) ⟨105702, by rfl⟩ : syracuseStep 281873 = 211405) B211405
theorem B249107 : Blo 163797 249107 := bstep (se 1 (by rfl) ⟨186830, by rfl⟩ : syracuseStep 249107 = 373661) B373661
theorem B249137 : Blo 163797 249137 := bstep (se 2 (by rfl) ⟨93426, by rfl⟩ : syracuseStep 249137 = 186853) B186853
theorem B249155 : Blo 163797 249155 := bstep (se 1 (by rfl) ⟨186866, by rfl⟩ : syracuseStep 249155 = 373733) B373733
theorem B249185 : Blo 163797 249185 := bstep (se 2 (by rfl) ⟨93444, by rfl⟩ : syracuseStep 249185 = 186889) B186889
theorem B511331 : Blo 163797 511331 := bstep (se 1 (by rfl) ⟨383498, by rfl⟩ : syracuseStep 511331 = 766997) B766997
theorem B249203 : Blo 163797 249203 := bstep (se 1 (by rfl) ⟨186902, by rfl⟩ : syracuseStep 249203 = 373805) B373805
theorem B249233 : Blo 163797 249233 := bstep (se 2 (by rfl) ⟨93462, by rfl⟩ : syracuseStep 249233 = 186925) B186925
theorem B282001 : Blo 163797 282001 := bstep (se 2 (by rfl) ⟨105750, by rfl⟩ : syracuseStep 282001 = 211501) B211501
theorem B249251 : Blo 163797 249251 := bstep (se 1 (by rfl) ⟨186938, by rfl⟩ : syracuseStep 249251 = 373877) B373877
theorem B282035 : Blo 163797 282035 := bstep (se 1 (by rfl) ⟨211526, by rfl⟩ : syracuseStep 282035 = 423053) B423053
theorem B249281 : Blo 163797 249281 := bstep (se 2 (by rfl) ⟨93480, by rfl⟩ : syracuseStep 249281 = 186961) B186961
theorem B249299 : Blo 163797 249299 := bstep (se 1 (by rfl) ⟨186974, by rfl⟩ : syracuseStep 249299 = 373949) B373949
theorem B249329 : Blo 163797 249329 := bstep (se 2 (by rfl) ⟨93498, by rfl⟩ : syracuseStep 249329 = 186997) B186997
theorem B249347 : Blo 163797 249347 := bstep (se 1 (by rfl) ⟨187010, by rfl⟩ : syracuseStep 249347 = 374021) B374021
theorem B249377 : Blo 163797 249377 := bstep (se 2 (by rfl) ⟨93516, by rfl⟩ : syracuseStep 249377 = 187033) B187033
theorem B249395 : Blo 163797 249395 := bstep (se 1 (by rfl) ⟨187046, by rfl⟩ : syracuseStep 249395 = 374093) B374093
theorem B282163 : Blo 163797 282163 := bstep (se 1 (by rfl) ⟨211622, by rfl⟩ : syracuseStep 282163 = 423245) B423245
theorem B249425 : Blo 163797 249425 := bstep (se 2 (by rfl) ⟨93534, by rfl⟩ : syracuseStep 249425 = 187069) B187069
theorem B249443 : Blo 163797 249443 := bstep (se 1 (by rfl) ⟨187082, by rfl⟩ : syracuseStep 249443 = 374165) B374165
theorem B249473 : Blo 163797 249473 := bstep (se 2 (by rfl) ⟨93552, by rfl⟩ : syracuseStep 249473 = 187105) B187105
theorem B249491 : Blo 163797 249491 := bstep (se 1 (by rfl) ⟨187118, by rfl⟩ : syracuseStep 249491 = 374237) B374237
theorem B249521 : Blo 163797 249521 := bstep (se 2 (by rfl) ⟨93570, by rfl⟩ : syracuseStep 249521 = 187141) B187141
theorem B282305 : Blo 163797 282305 := bstep (se 2 (by rfl) ⟨105864, by rfl⟩ : syracuseStep 282305 = 211729) B211729
theorem B249539 : Blo 163797 249539 := bstep (se 1 (by rfl) ⟨187154, by rfl⟩ : syracuseStep 249539 = 374309) B374309
theorem B249569 : Blo 163797 249569 := bstep (se 2 (by rfl) ⟨93588, by rfl⟩ : syracuseStep 249569 = 187177) B187177
theorem B249587 : Blo 163797 249587 := bstep (se 1 (by rfl) ⟨187190, by rfl⟩ : syracuseStep 249587 = 374381) B374381
theorem B249617 : Blo 163797 249617 := bstep (se 2 (by rfl) ⟨93606, by rfl⟩ : syracuseStep 249617 = 187213) B187213
theorem B249635 : Blo 163797 249635 := bstep (se 1 (by rfl) ⟨187226, by rfl⟩ : syracuseStep 249635 = 374453) B374453
theorem B249665 : Blo 163797 249665 := bstep (se 2 (by rfl) ⟨93624, by rfl⟩ : syracuseStep 249665 = 187249) B187249
theorem B282433 : Blo 163797 282433 := bstep (se 2 (by rfl) ⟨105912, by rfl⟩ : syracuseStep 282433 = 211825) B211825
theorem B249683 : Blo 163797 249683 := bstep (se 1 (by rfl) ⟨187262, by rfl⟩ : syracuseStep 249683 = 374525) B374525
theorem B282467 : Blo 163797 282467 := bstep (se 1 (by rfl) ⟨211850, by rfl⟩ : syracuseStep 282467 = 423701) B423701
theorem B249713 : Blo 163797 249713 := bstep (se 2 (by rfl) ⟨93642, by rfl⟩ : syracuseStep 249713 = 187285) B187285
theorem B249731 : Blo 163797 249731 := bstep (se 1 (by rfl) ⟨187298, by rfl⟩ : syracuseStep 249731 = 374597) B374597
theorem B249761 : Blo 163797 249761 := bstep (se 2 (by rfl) ⟨93660, by rfl⟩ : syracuseStep 249761 = 187321) B187321
theorem B249779 : Blo 163797 249779 := bstep (se 1 (by rfl) ⟨187334, by rfl⟩ : syracuseStep 249779 = 374669) B374669
theorem B249809 : Blo 163797 249809 := bstep (se 2 (by rfl) ⟨93678, by rfl⟩ : syracuseStep 249809 = 187357) B187357
theorem B249827 : Blo 163797 249827 := bstep (se 1 (by rfl) ⟨187370, by rfl⟩ : syracuseStep 249827 = 374741) B374741
theorem B282595 : Blo 163797 282595 := bstep (se 1 (by rfl) ⟨211946, by rfl⟩ : syracuseStep 282595 = 423893) B423893
theorem B249857 : Blo 163797 249857 := bstep (se 2 (by rfl) ⟨93696, by rfl⟩ : syracuseStep 249857 = 187393) B187393
theorem B249875 : Blo 163797 249875 := bstep (se 1 (by rfl) ⟨187406, by rfl⟩ : syracuseStep 249875 = 374813) B374813
theorem B249905 : Blo 163797 249905 := bstep (se 2 (by rfl) ⟨93714, by rfl⟩ : syracuseStep 249905 = 187429) B187429
theorem B184387 : Blo 163797 184387 := bstep (se 1 (by rfl) ⟨138290, by rfl⟩ : syracuseStep 184387 = 276581) B276581
theorem B249923 : Blo 163797 249923 := bstep (se 1 (by rfl) ⟨187442, by rfl⟩ : syracuseStep 249923 = 374885) B374885
theorem B249953 : Blo 163797 249953 := bstep (se 2 (by rfl) ⟨93732, by rfl⟩ : syracuseStep 249953 = 187465) B187465
theorem B315505 : Blo 163797 315505 := bstep (se 2 (by rfl) ⟨118314, by rfl⟩ : syracuseStep 315505 = 236629) B236629
theorem B282737 : Blo 163797 282737 := bstep (se 2 (by rfl) ⟨106026, by rfl⟩ : syracuseStep 282737 = 212053) B212053
theorem B249971 : Blo 163797 249971 := bstep (se 1 (by rfl) ⟨187478, by rfl⟩ : syracuseStep 249971 = 374957) B374957
theorem B250001 : Blo 163797 250001 := bstep (se 2 (by rfl) ⟨93750, by rfl⟩ : syracuseStep 250001 = 187501) B187501
theorem B250019 : Blo 163797 250019 := bstep (se 1 (by rfl) ⟨187514, by rfl⟩ : syracuseStep 250019 = 375029) B375029
theorem B250049 : Blo 163797 250049 := bstep (se 2 (by rfl) ⟨93768, by rfl⟩ : syracuseStep 250049 = 187537) B187537
theorem B2838725 : Blo 163797 2838725 := bstep (se 4 (by rfl) ⟨266130, by rfl⟩ : syracuseStep 2838725 = 532261) B532261
theorem B184531 : Blo 163797 184531 := bstep (se 1 (by rfl) ⟨138398, by rfl⟩ : syracuseStep 184531 = 276797) B276797
theorem B250067 : Blo 163797 250067 := bstep (se 1 (by rfl) ⟨187550, by rfl⟩ : syracuseStep 250067 = 375101) B375101
theorem B1921265 : Blo 163797 1921265 := bstep (se 2 (by rfl) ⟨720474, by rfl⟩ : syracuseStep 1921265 = 1440949) B1440949
theorem B250097 : Blo 163797 250097 := bstep (se 2 (by rfl) ⟨93786, by rfl⟩ : syracuseStep 250097 = 187573) B187573
theorem B282865 : Blo 163797 282865 := bstep (se 2 (by rfl) ⟨106074, by rfl⟩ : syracuseStep 282865 = 212149) B212149
theorem B250115 : Blo 163797 250115 := bstep (se 1 (by rfl) ⟨187586, by rfl⟩ : syracuseStep 250115 = 375173) B375173
theorem B282899 : Blo 163797 282899 := bstep (se 1 (by rfl) ⟨212174, by rfl⟩ : syracuseStep 282899 = 424349) B424349
theorem B250145 : Blo 163797 250145 := bstep (se 2 (by rfl) ⟨93804, by rfl⟩ : syracuseStep 250145 = 187609) B187609
theorem B250163 : Blo 163797 250163 := bstep (se 1 (by rfl) ⟨187622, by rfl⟩ : syracuseStep 250163 = 375245) B375245
theorem B250193 : Blo 163797 250193 := bstep (se 2 (by rfl) ⟨93822, by rfl⟩ : syracuseStep 250193 = 187645) B187645
theorem B184675 : Blo 163797 184675 := bstep (se 1 (by rfl) ⟨138506, by rfl⟩ : syracuseStep 184675 = 277013) B277013
theorem B250211 : Blo 163797 250211 := bstep (se 1 (by rfl) ⟨187658, by rfl⟩ : syracuseStep 250211 = 375317) B375317
theorem B250241 : Blo 163797 250241 := bstep (se 2 (by rfl) ⟨93840, by rfl⟩ : syracuseStep 250241 = 187681) B187681
theorem B250259 : Blo 163797 250259 := bstep (se 1 (by rfl) ⟨187694, by rfl⟩ : syracuseStep 250259 = 375389) B375389
theorem B283027 : Blo 163797 283027 := bstep (se 1 (by rfl) ⟨212270, by rfl⟩ : syracuseStep 283027 = 424541) B424541
theorem B250289 : Blo 163797 250289 := bstep (se 2 (by rfl) ⟨93858, by rfl⟩ : syracuseStep 250289 = 187717) B187717
theorem B250307 : Blo 163797 250307 := bstep (se 1 (by rfl) ⟨187730, by rfl⟩ : syracuseStep 250307 = 375461) B375461
theorem B250337 : Blo 163797 250337 := bstep (se 2 (by rfl) ⟨93876, by rfl⟩ : syracuseStep 250337 = 187753) B187753
theorem B184819 : Blo 163797 184819 := bstep (se 1 (by rfl) ⟨138614, by rfl⟩ : syracuseStep 184819 = 277229) B277229
theorem B250355 : Blo 163797 250355 := bstep (se 1 (by rfl) ⟨187766, by rfl⟩ : syracuseStep 250355 = 375533) B375533
theorem B250385 : Blo 163797 250385 := bstep (se 2 (by rfl) ⟨93894, by rfl⟩ : syracuseStep 250385 = 187789) B187789
theorem B250403 : Blo 163797 250403 := bstep (se 1 (by rfl) ⟨187802, by rfl⟩ : syracuseStep 250403 = 375605) B375605
theorem B250433 : Blo 163797 250433 := bstep (se 2 (by rfl) ⟨93912, by rfl⟩ : syracuseStep 250433 = 187825) B187825
theorem B250451 : Blo 163797 250451 := bstep (se 1 (by rfl) ⟨187838, by rfl⟩ : syracuseStep 250451 = 375677) B375677
theorem B250481 : Blo 163797 250481 := bstep (se 2 (by rfl) ⟨93930, by rfl⟩ : syracuseStep 250481 = 187861) B187861
theorem B184963 : Blo 163797 184963 := bstep (se 1 (by rfl) ⟨138722, by rfl⟩ : syracuseStep 184963 = 277445) B277445
theorem B250499 : Blo 163797 250499 := bstep (se 1 (by rfl) ⟨187874, by rfl⟩ : syracuseStep 250499 = 375749) B375749
theorem B250529 : Blo 163797 250529 := bstep (se 2 (by rfl) ⟨93948, by rfl⟩ : syracuseStep 250529 = 187897) B187897
theorem B250547 : Blo 163797 250547 := bstep (se 1 (by rfl) ⟨187910, by rfl⟩ : syracuseStep 250547 = 375821) B375821
theorem B250577 : Blo 163797 250577 := bstep (se 2 (by rfl) ⟨93966, by rfl⟩ : syracuseStep 250577 = 187933) B187933
theorem B250595 : Blo 163797 250595 := bstep (se 1 (by rfl) ⟨187946, by rfl⟩ : syracuseStep 250595 = 375893) B375893
theorem B250625 : Blo 163797 250625 := bstep (se 2 (by rfl) ⟨93984, by rfl⟩ : syracuseStep 250625 = 187969) B187969
theorem B185107 : Blo 163797 185107 := bstep (se 1 (by rfl) ⟨138830, by rfl⟩ : syracuseStep 185107 = 277661) B277661
theorem B250643 : Blo 163797 250643 := bstep (se 1 (by rfl) ⟨187982, by rfl⟩ : syracuseStep 250643 = 375965) B375965
theorem B250673 : Blo 163797 250673 := bstep (se 2 (by rfl) ⟨94002, by rfl⟩ : syracuseStep 250673 = 188005) B188005
theorem B250691 : Blo 163797 250691 := bstep (se 1 (by rfl) ⟨188018, by rfl⟩ : syracuseStep 250691 = 376037) B376037
theorem B250721 : Blo 163797 250721 := bstep (se 2 (by rfl) ⟨94020, by rfl⟩ : syracuseStep 250721 = 188041) B188041
theorem B381809 : Blo 163797 381809 := bstep (se 2 (by rfl) ⟨143178, by rfl⟩ : syracuseStep 381809 = 286357) B286357
theorem B250739 : Blo 163797 250739 := bstep (se 1 (by rfl) ⟨188054, by rfl⟩ : syracuseStep 250739 = 376109) B376109
theorem B250769 : Blo 163797 250769 := bstep (se 2 (by rfl) ⟨94038, by rfl⟩ : syracuseStep 250769 = 188077) B188077
theorem B185251 : Blo 163797 185251 := bstep (se 1 (by rfl) ⟨138938, by rfl⟩ : syracuseStep 185251 = 277877) B277877
theorem B250787 : Blo 163797 250787 := bstep (se 1 (by rfl) ⟨188090, by rfl⟩ : syracuseStep 250787 = 376181) B376181
theorem B250817 : Blo 163797 250817 := bstep (se 2 (by rfl) ⟨94056, by rfl⟩ : syracuseStep 250817 = 188113) B188113
theorem B414659 : Blo 163797 414659 := bstep (se 1 (by rfl) ⟨310994, by rfl⟩ : syracuseStep 414659 = 621989) B621989
theorem B250835 : Blo 163797 250835 := bstep (se 1 (by rfl) ⟨188126, by rfl⟩ : syracuseStep 250835 = 376253) B376253
theorem B250865 : Blo 163797 250865 := bstep (se 2 (by rfl) ⟨94074, by rfl⟩ : syracuseStep 250865 = 188149) B188149
theorem B250883 : Blo 163797 250883 := bstep (se 1 (by rfl) ⟨188162, by rfl⟩ : syracuseStep 250883 = 376325) B376325
theorem B250913 : Blo 163797 250913 := bstep (se 2 (by rfl) ⟨94092, by rfl⟩ : syracuseStep 250913 = 188185) B188185
theorem B709667 : Blo 163797 709667 := bstep (se 1 (by rfl) ⟨532250, by rfl⟩ : syracuseStep 709667 = 1064501) B1064501
theorem B185395 : Blo 163797 185395 := bstep (se 1 (by rfl) ⟨139046, by rfl⟩ : syracuseStep 185395 = 278093) B278093
theorem B250931 : Blo 163797 250931 := bstep (se 1 (by rfl) ⟨188198, by rfl⟩ : syracuseStep 250931 = 376397) B376397
theorem B250961 : Blo 163797 250961 := bstep (se 2 (by rfl) ⟨94110, by rfl⟩ : syracuseStep 250961 = 188221) B188221
theorem B250979 : Blo 163797 250979 := bstep (se 1 (by rfl) ⟨188234, by rfl⟩ : syracuseStep 250979 = 376469) B376469
theorem B251009 : Blo 163797 251009 := bstep (se 2 (by rfl) ⟨94128, by rfl⟩ : syracuseStep 251009 = 188257) B188257
theorem B316561 : Blo 163797 316561 := bstep (se 2 (by rfl) ⟨118710, by rfl⟩ : syracuseStep 316561 = 237421) B237421
theorem B251027 : Blo 163797 251027 := bstep (se 1 (by rfl) ⟨188270, by rfl⟩ : syracuseStep 251027 = 376541) B376541
theorem B251057 : Blo 163797 251057 := bstep (se 2 (by rfl) ⟨94146, by rfl⟩ : syracuseStep 251057 = 188293) B188293
theorem B185539 : Blo 163797 185539 := bstep (se 1 (by rfl) ⟨139154, by rfl⟩ : syracuseStep 185539 = 278309) B278309
theorem B251075 : Blo 163797 251075 := bstep (se 1 (by rfl) ⟨188306, by rfl⟩ : syracuseStep 251075 = 376613) B376613
theorem B251105 : Blo 163797 251105 := bstep (se 2 (by rfl) ⟨94164, by rfl⟩ : syracuseStep 251105 = 188329) B188329
theorem B251123 : Blo 163797 251123 := bstep (se 1 (by rfl) ⟨188342, by rfl⟩ : syracuseStep 251123 = 376685) B376685
theorem B251153 : Blo 163797 251153 := bstep (se 2 (by rfl) ⟨94182, by rfl⟩ : syracuseStep 251153 = 188365) B188365
theorem B251171 : Blo 163797 251171 := bstep (se 1 (by rfl) ⟨188378, by rfl⟩ : syracuseStep 251171 = 376757) B376757
theorem B251201 : Blo 163797 251201 := bstep (se 2 (by rfl) ⟨94200, by rfl⟩ : syracuseStep 251201 = 188401) B188401
theorem B185683 : Blo 163797 185683 := bstep (se 1 (by rfl) ⟨139262, by rfl⟩ : syracuseStep 185683 = 278525) B278525
theorem B251219 : Blo 163797 251219 := bstep (se 1 (by rfl) ⟨188414, by rfl⟩ : syracuseStep 251219 = 376829) B376829
theorem B251249 : Blo 163797 251249 := bstep (se 2 (by rfl) ⟨94218, by rfl⟩ : syracuseStep 251249 = 188437) B188437
theorem B251267 : Blo 163797 251267 := bstep (se 1 (by rfl) ⟨188450, by rfl⟩ : syracuseStep 251267 = 376901) B376901
theorem B251297 : Blo 163797 251297 := bstep (se 2 (by rfl) ⟨94236, by rfl⟩ : syracuseStep 251297 = 188473) B188473
theorem B251315 : Blo 163797 251315 := bstep (se 1 (by rfl) ⟨188486, by rfl⟩ : syracuseStep 251315 = 376973) B376973
theorem B251345 : Blo 163797 251345 := bstep (se 2 (by rfl) ⟨94254, by rfl⟩ : syracuseStep 251345 = 188509) B188509
theorem B185827 : Blo 163797 185827 := bstep (se 1 (by rfl) ⟨139370, by rfl⟩ : syracuseStep 185827 = 278741) B278741
theorem B251363 : Blo 163797 251363 := bstep (se 1 (by rfl) ⟨188522, by rfl⟩ : syracuseStep 251363 = 377045) B377045
theorem B251393 : Blo 163797 251393 := bstep (se 2 (by rfl) ⟨94272, by rfl⟩ : syracuseStep 251393 = 188545) B188545
theorem B251411 : Blo 163797 251411 := bstep (se 1 (by rfl) ⟨188558, by rfl⟩ : syracuseStep 251411 = 377117) B377117
theorem B316963 : Blo 163797 316963 := bstep (se 1 (by rfl) ⟨237722, by rfl⟩ : syracuseStep 316963 = 475445) B475445
theorem B1136177 : Blo 163797 1136177 := bstep (se 2 (by rfl) ⟨426066, by rfl⟩ : syracuseStep 1136177 = 852133) B852133
theorem B841265 : Blo 163797 841265 := bstep (se 2 (by rfl) ⟨315474, by rfl⟩ : syracuseStep 841265 = 630949) B630949
theorem B251441 : Blo 163797 251441 := bstep (se 2 (by rfl) ⟨94290, by rfl⟩ : syracuseStep 251441 = 188581) B188581
theorem B251459 : Blo 163797 251459 := bstep (se 1 (by rfl) ⟨188594, by rfl⟩ : syracuseStep 251459 = 377189) B377189
theorem B317009 : Blo 163797 317009 := bstep (se 2 (by rfl) ⟨118878, by rfl⟩ : syracuseStep 317009 = 237757) B237757
theorem B251489 : Blo 163797 251489 := bstep (se 2 (by rfl) ⟨94308, by rfl⟩ : syracuseStep 251489 = 188617) B188617
theorem B185971 : Blo 163797 185971 := bstep (se 1 (by rfl) ⟨139478, by rfl⟩ : syracuseStep 185971 = 278957) B278957
theorem B251507 : Blo 163797 251507 := bstep (se 1 (by rfl) ⟨188630, by rfl⟩ : syracuseStep 251507 = 377261) B377261
theorem B284305 : Blo 163797 284305 := bstep (se 2 (by rfl) ⟨106614, by rfl⟩ : syracuseStep 284305 = 213229) B213229
theorem B251537 : Blo 163797 251537 := bstep (se 2 (by rfl) ⟨94326, by rfl⟩ : syracuseStep 251537 = 188653) B188653
theorem B251555 : Blo 163797 251555 := bstep (se 1 (by rfl) ⟨188666, by rfl⟩ : syracuseStep 251555 = 377333) B377333
theorem B251585 : Blo 163797 251585 := bstep (se 2 (by rfl) ⟨94344, by rfl⟩ : syracuseStep 251585 = 188689) B188689
theorem B251603 : Blo 163797 251603 := bstep (se 1 (by rfl) ⟨188702, by rfl⟩ : syracuseStep 251603 = 377405) B377405
theorem B251633 : Blo 163797 251633 := bstep (se 2 (by rfl) ⟨94362, by rfl⟩ : syracuseStep 251633 = 188725) B188725
theorem B186115 : Blo 163797 186115 := bstep (se 1 (by rfl) ⟨139586, by rfl⟩ : syracuseStep 186115 = 279173) B279173
theorem B251651 : Blo 163797 251651 := bstep (se 1 (by rfl) ⟨188738, by rfl⟩ : syracuseStep 251651 = 377477) B377477
theorem B251681 : Blo 163797 251681 := bstep (se 2 (by rfl) ⟨94380, by rfl⟩ : syracuseStep 251681 = 188761) B188761
theorem B677731 : Blo 163797 677731 := bstep (se 1 (by rfl) ⟨508298, by rfl⟩ : syracuseStep 677731 = 1016597) B1016597
theorem B415601 : Blo 163797 415601 := bstep (se 2 (by rfl) ⟨155850, by rfl⟩ : syracuseStep 415601 = 311701) B311701
theorem B317297 : Blo 163797 317297 := bstep (se 2 (by rfl) ⟨118986, by rfl⟩ : syracuseStep 317297 = 237973) B237973
theorem B186259 : Blo 163797 186259 := bstep (se 1 (by rfl) ⟨139694, by rfl⟩ : syracuseStep 186259 = 279389) B279389
theorem B415651 : Blo 163797 415651 := bstep (se 1 (by rfl) ⟨311738, by rfl⟩ : syracuseStep 415651 = 623477) B623477
theorem B284593 : Blo 163797 284593 := bstep (se 2 (by rfl) ⟨106722, by rfl⟩ : syracuseStep 284593 = 213445) B213445
theorem B940045 : Blo 163797 940045 := bstep (se 3 (by rfl) ⟨176258, by rfl⟩ : syracuseStep 940045 = 352517) B352517
theorem B186403 : Blo 163797 186403 := bstep (se 1 (by rfl) ⟨139802, by rfl⟩ : syracuseStep 186403 = 279605) B279605
theorem B415793 : Blo 163797 415793 := bstep (se 2 (by rfl) ⟨155922, by rfl⟩ : syracuseStep 415793 = 311845) B311845
theorem B1431665 : Blo 163797 1431665 := bstep (se 2 (by rfl) ⟨536874, by rfl⟩ : syracuseStep 1431665 = 1073749) B1073749
theorem B186547 : Blo 163797 186547 := bstep (se 1 (by rfl) ⟨139910, by rfl⟩ : syracuseStep 186547 = 279821) B279821
theorem B252227 : Blo 163797 252227 := bstep (se 1 (by rfl) ⟨189170, by rfl⟩ : syracuseStep 252227 = 378341) B378341
theorem B186691 : Blo 163797 186691 := bstep (se 1 (by rfl) ⟨140018, by rfl⟩ : syracuseStep 186691 = 280037) B280037
theorem B186835 : Blo 163797 186835 := bstep (se 1 (by rfl) ⟨140126, by rfl⟩ : syracuseStep 186835 = 280253) B280253
theorem B318019 : Blo 163797 318019 := bstep (se 1 (by rfl) ⟨238514, by rfl⟩ : syracuseStep 318019 = 477029) B477029
theorem B350801 : Blo 163797 350801 := bstep (se 2 (by rfl) ⟨131550, by rfl⟩ : syracuseStep 350801 = 263101) B263101
theorem B186979 : Blo 163797 186979 := bstep (se 1 (by rfl) ⟨140234, by rfl⟩ : syracuseStep 186979 = 280469) B280469
theorem B285299 : Blo 163797 285299 := bstep (se 1 (by rfl) ⟨213974, by rfl⟩ : syracuseStep 285299 = 427949) B427949
theorem B187091 : Blo 163797 187091 := bstep (se 1 (by rfl) ⟨140318, by rfl⟩ : syracuseStep 187091 = 280637) B280637
theorem B187123 : Blo 163797 187123 := bstep (se 1 (by rfl) ⟨140342, by rfl⟩ : syracuseStep 187123 = 280685) B280685
theorem B187267 : Blo 163797 187267 := bstep (se 1 (by rfl) ⟨140450, by rfl⟩ : syracuseStep 187267 = 280901) B280901
theorem B842723 : Blo 163797 842723 := bstep (se 1 (by rfl) ⟨632042, by rfl⟩ : syracuseStep 842723 = 1264085) B1264085
theorem B711665 : Blo 163797 711665 := bstep (se 2 (by rfl) ⟨266874, by rfl⟩ : syracuseStep 711665 = 533749) B533749
theorem B318467 : Blo 163797 318467 := bstep (se 1 (by rfl) ⟨238850, by rfl⟩ : syracuseStep 318467 = 477701) B477701
theorem B416785 : Blo 163797 416785 := bstep (se 2 (by rfl) ⟨156294, by rfl⟩ : syracuseStep 416785 = 312589) B312589
theorem B187411 : Blo 163797 187411 := bstep (se 1 (by rfl) ⟨140558, by rfl⟩ : syracuseStep 187411 = 281117) B281117
theorem B187555 : Blo 163797 187555 := bstep (se 1 (by rfl) ⟨140666, by rfl⟩ : syracuseStep 187555 = 281333) B281333
theorem B1006769 : Blo 163797 1006769 := bstep (se 2 (by rfl) ⟨377538, by rfl⟩ : syracuseStep 1006769 = 755077) B755077
theorem B2579653 : Blo 163797 2579653 := bstep (se 4 (by rfl) ⟨241842, by rfl⟩ : syracuseStep 2579653 = 483685) B483685
theorem B1072397 : Blo 163797 1072397 := bstep (se 3 (by rfl) ⟨201074, by rfl⟩ : syracuseStep 1072397 = 402149) B402149
theorem B253201 : Blo 163797 253201 := bstep (se 2 (by rfl) ⟨94950, by rfl⟩ : syracuseStep 253201 = 189901) B189901
theorem B417059 : Blo 163797 417059 := bstep (se 1 (by rfl) ⟨312794, by rfl⟩ : syracuseStep 417059 = 625589) B625589
theorem B187699 : Blo 163797 187699 := bstep (se 1 (by rfl) ⟨140774, by rfl⟩ : syracuseStep 187699 = 281549) B281549
theorem B187843 : Blo 163797 187843 := bstep (se 1 (by rfl) ⟨140882, by rfl⟩ : syracuseStep 187843 = 281765) B281765
theorem B351697 : Blo 163797 351697 := bstep (se 2 (by rfl) ⟨131886, by rfl⟩ : syracuseStep 351697 = 263773) B263773
theorem B351715 : Blo 163797 351715 := bstep (se 1 (by rfl) ⟨263786, by rfl⟩ : syracuseStep 351715 = 527573) B527573
theorem B417251 : Blo 163797 417251 := bstep (se 1 (by rfl) ⟨312938, by rfl⟩ : syracuseStep 417251 = 625877) B625877
theorem B187987 : Blo 163797 187987 := bstep (se 1 (by rfl) ⟨140990, by rfl⟩ : syracuseStep 187987 = 281981) B281981
theorem B450211 : Blo 163797 450211 := bstep (se 1 (by rfl) ⟨337658, by rfl⟩ : syracuseStep 450211 = 675317) B675317
theorem B188131 : Blo 163797 188131 := bstep (se 1 (by rfl) ⟨141098, by rfl⟩ : syracuseStep 188131 = 282197) B282197
theorem B450307 : Blo 163797 450307 := bstep (se 1 (by rfl) ⟨337730, by rfl⟩ : syracuseStep 450307 = 675461) B675461
theorem B843533 : Blo 163797 843533 := bstep (se 3 (by rfl) ⟨158162, by rfl⟩ : syracuseStep 843533 = 316325) B316325
theorem B188275 : Blo 163797 188275 := bstep (se 1 (by rfl) ⟨141206, by rfl⟩ : syracuseStep 188275 = 282413) B282413
theorem B1400773 : Blo 163797 1400773 := bstep (se 4 (by rfl) ⟨131322, by rfl⟩ : syracuseStep 1400773 = 262645) B262645
theorem B942029 : Blo 163797 942029 := bstep (se 3 (by rfl) ⟨176630, by rfl⟩ : syracuseStep 942029 = 353261) B353261
theorem B188419 : Blo 163797 188419 := bstep (se 1 (by rfl) ⟨141314, by rfl⟩ : syracuseStep 188419 = 282629) B282629
theorem B188563 : Blo 163797 188563 := bstep (se 1 (by rfl) ⟨141422, by rfl⟩ : syracuseStep 188563 = 282845) B282845
theorem B188707 : Blo 163797 188707 := bstep (se 1 (by rfl) ⟨141530, by rfl⟩ : syracuseStep 188707 = 283061) B283061
theorem B483725 : Blo 163797 483725 := bstep (se 3 (by rfl) ⟨90698, by rfl⟩ : syracuseStep 483725 = 181397) B181397
theorem B418193 : Blo 163797 418193 := bstep (se 2 (by rfl) ⟨156822, by rfl⟩ : syracuseStep 418193 = 313645) B313645
theorem B418243 : Blo 163797 418243 := bstep (se 1 (by rfl) ⟨313682, by rfl⟩ : syracuseStep 418243 = 627365) B627365
theorem B418385 : Blo 163797 418385 := bstep (se 2 (by rfl) ⟨156894, by rfl⟩ : syracuseStep 418385 = 313789) B313789
theorem B713357 : Blo 163797 713357 := bstep (se 3 (by rfl) ⟨133754, by rfl⟩ : syracuseStep 713357 = 267509) B267509
theorem B942961 : Blo 163797 942961 := bstep (se 2 (by rfl) ⟨353610, by rfl⟩ : syracuseStep 942961 = 707221) B707221
theorem B222689 : Blo 163797 222689 := bstep (se 2 (by rfl) ⟨83508, by rfl⟩ : syracuseStep 222689 = 167017) B167017
theorem B3630563 : Blo 163797 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B419377 : Blo 163797 419377 := bstep (se 2 (by rfl) ⟨157266, by rfl⟩ : syracuseStep 419377 = 314533) B314533
theorem B1893941 : Blo 163797 1893941 := bstep (se 5 (by rfl) ⟨88778, by rfl⟩ : syracuseStep 1893941 = 177557) B177557
theorem B353987 : Blo 163797 353987 := bstep (se 1 (by rfl) ⟨265490, by rfl⟩ : syracuseStep 353987 = 530981) B530981
theorem B321251 : Blo 163797 321251 := bstep (se 1 (by rfl) ⟨240938, by rfl⟩ : syracuseStep 321251 = 481877) B481877
theorem B419651 : Blo 163797 419651 := bstep (se 1 (by rfl) ⟨314738, by rfl⟩ : syracuseStep 419651 = 629477) B629477
theorem B452429 : Blo 163797 452429 := bstep (se 3 (by rfl) ⟨84830, by rfl⟩ : syracuseStep 452429 = 169661) B169661
theorem B419843 : Blo 163797 419843 := bstep (se 1 (by rfl) ⟨314882, by rfl⟩ : syracuseStep 419843 = 629765) B629765
theorem B714865 : Blo 163797 714865 := bstep (se 2 (by rfl) ⟨268074, by rfl⟩ : syracuseStep 714865 = 536149) B536149
theorem B354449 : Blo 163797 354449 := bstep (se 2 (by rfl) ⟨132918, by rfl⟩ : syracuseStep 354449 = 265837) B265837
theorem B223489 : Blo 163797 223489 := bstep (se 2 (by rfl) ⟨83808, by rfl⟩ : syracuseStep 223489 = 167617) B167617
theorem B944419 : Blo 163797 944419 := bstep (se 1 (by rfl) ⟨708314, by rfl⟩ : syracuseStep 944419 = 1416629) B1416629
theorem B223651 : Blo 163797 223651 := bstep (se 1 (by rfl) ⟨167738, by rfl⟩ : syracuseStep 223651 = 335477) B335477
theorem B748109 : Blo 163797 748109 := bstep (se 3 (by rfl) ⟨140270, by rfl⟩ : syracuseStep 748109 = 280541) B280541
theorem B289379 : Blo 163797 289379 := bstep (se 1 (by rfl) ⟨217034, by rfl⟩ : syracuseStep 289379 = 434069) B434069
theorem B846449 : Blo 163797 846449 := bstep (se 2 (by rfl) ⟨317418, by rfl⟩ : syracuseStep 846449 = 634837) B634837
theorem B355043 : Blo 163797 355043 := bstep (se 1 (by rfl) ⟨266282, by rfl⟩ : syracuseStep 355043 = 532565) B532565
theorem B944945 : Blo 163797 944945 := bstep (se 2 (by rfl) ⟨354354, by rfl⟩ : syracuseStep 944945 = 708709) B708709
theorem B420785 : Blo 163797 420785 := bstep (se 2 (by rfl) ⟨157794, by rfl⟩ : syracuseStep 420785 = 315589) B315589
theorem B420835 : Blo 163797 420835 := bstep (se 1 (by rfl) ⟨315626, by rfl⟩ : syracuseStep 420835 = 631253) B631253
theorem B420977 : Blo 163797 420977 := bstep (se 2 (by rfl) ⟨157866, by rfl⟩ : syracuseStep 420977 = 315733) B315733
theorem B355747 : Blo 163797 355747 := bstep (se 1 (by rfl) ⟨266810, by rfl⟩ : syracuseStep 355747 = 533621) B533621
theorem B224689 : Blo 163797 224689 := bstep (se 2 (by rfl) ⟨84258, by rfl⟩ : syracuseStep 224689 = 168517) B168517
theorem B356003 : Blo 163797 356003 := bstep (se 1 (by rfl) ⟨267002, by rfl⟩ : syracuseStep 356003 = 534005) B534005
theorem B1601477 : Blo 163797 1601477 := bstep (se 4 (by rfl) ⟨150138, by rfl⟩ : syracuseStep 1601477 = 300277) B300277
theorem B847907 : Blo 163797 847907 := bstep (se 1 (by rfl) ⟨635930, by rfl⟩ : syracuseStep 847907 = 1271861) B1271861
theorem B421969 : Blo 163797 421969 := bstep (se 2 (by rfl) ⟨158238, by rfl⟩ : syracuseStep 421969 = 316477) B316477
theorem B946403 : Blo 163797 946403 := bstep (se 1 (by rfl) ⟨709802, by rfl⟩ : syracuseStep 946403 = 1419605) B1419605
theorem B553229 : Blo 163797 553229 := bstep (se 3 (by rfl) ⟨103730, by rfl⟩ : syracuseStep 553229 = 207461) B207461
theorem B553283 : Blo 163797 553283 := bstep (se 1 (by rfl) ⟨414962, by rfl⟩ : syracuseStep 553283 = 829925) B829925
theorem B422243 : Blo 163797 422243 := bstep (se 1 (by rfl) ⟨316682, by rfl⟩ : syracuseStep 422243 = 633365) B633365
theorem B422435 : Blo 163797 422435 := bstep (se 1 (by rfl) ⟨316826, by rfl⟩ : syracuseStep 422435 = 633653) B633653
theorem B553553 : Blo 163797 553553 := bstep (se 2 (by rfl) ⟨207582, by rfl⟩ : syracuseStep 553553 = 415165) B415165
theorem B356977 : Blo 163797 356977 := bstep (se 2 (by rfl) ⟨133866, by rfl⟩ : syracuseStep 356977 = 267733) B267733
theorem B226003 : Blo 163797 226003 := bstep (se 1 (by rfl) ⟨169502, by rfl⟩ : syracuseStep 226003 = 339005) B339005
theorem B848717 : Blo 163797 848717 := bstep (se 3 (by rfl) ⟨159134, by rfl⟩ : syracuseStep 848717 = 318269) B318269
theorem B1209329 : Blo 163797 1209329 := bstep (se 2 (by rfl) ⟨453498, by rfl⟩ : syracuseStep 1209329 = 906997) B906997
theorem B554093 : Blo 163797 554093 := bstep (se 3 (by rfl) ⟨103892, by rfl⟩ : syracuseStep 554093 = 207785) B207785
theorem B554147 : Blo 163797 554147 := bstep (se 1 (by rfl) ⟨415610, by rfl⟩ : syracuseStep 554147 = 831221) B831221
theorem B357635 : Blo 163797 357635 := bstep (se 1 (by rfl) ⟨268226, by rfl⟩ : syracuseStep 357635 = 536453) B536453
theorem B554417 : Blo 163797 554417 := bstep (se 2 (by rfl) ⟨207906, by rfl⟩ : syracuseStep 554417 = 415813) B415813
theorem B423377 : Blo 163797 423377 := bstep (se 2 (by rfl) ⟨158766, by rfl⟩ : syracuseStep 423377 = 317533) B317533
theorem B423427 : Blo 163797 423427 := bstep (se 1 (by rfl) ⟨317570, by rfl⟩ : syracuseStep 423427 = 635141) B635141
theorem B423569 : Blo 163797 423569 := bstep (se 2 (by rfl) ⟨158838, by rfl⟩ : syracuseStep 423569 = 317677) B317677
theorem B3143477 : Blo 163797 3143477 := bstep (se 5 (by rfl) ⟨147350, by rfl⟩ : syracuseStep 3143477 = 294701) B294701
theorem B554957 : Blo 163797 554957 := bstep (se 3 (by rfl) ⟨104054, by rfl⟩ : syracuseStep 554957 = 208109) B208109
theorem B555011 : Blo 163797 555011 := bstep (se 1 (by rfl) ⟨416258, by rfl⟩ : syracuseStep 555011 = 832517) B832517
theorem B948293 : Blo 163797 948293 := bstep (se 4 (by rfl) ⟨88902, by rfl⟩ : syracuseStep 948293 = 177805) B177805
theorem B555281 : Blo 163797 555281 := bstep (se 2 (by rfl) ⟨208230, by rfl⟩ : syracuseStep 555281 = 416461) B416461
theorem B227827 : Blo 163797 227827 := bstep (se 1 (by rfl) ⟨170870, by rfl⟩ : syracuseStep 227827 = 341741) B341741
theorem B752141 : Blo 163797 752141 := bstep (se 3 (by rfl) ⟨141026, by rfl⟩ : syracuseStep 752141 = 282053) B282053
theorem B424561 : Blo 163797 424561 := bstep (se 2 (by rfl) ⟨159210, by rfl⟩ : syracuseStep 424561 = 318421) B318421
theorem B555821 : Blo 163797 555821 := bstep (se 3 (by rfl) ⟨104216, by rfl⟩ : syracuseStep 555821 = 208433) B208433
theorem B555875 : Blo 163797 555875 := bstep (se 1 (by rfl) ⟨416906, by rfl⟩ : syracuseStep 555875 = 833813) B833813
theorem B556145 : Blo 163797 556145 := bstep (se 2 (by rfl) ⟨208554, by rfl⟩ : syracuseStep 556145 = 417109) B417109
theorem B228577 : Blo 163797 228577 := bstep (se 2 (by rfl) ⟨85716, by rfl⟩ : syracuseStep 228577 = 171433) B171433
theorem B228883 : Blo 163797 228883 := bstep (se 1 (by rfl) ⟨171662, by rfl⟩ : syracuseStep 228883 = 343325) B343325
theorem B556685 : Blo 163797 556685 := bstep (se 3 (by rfl) ⟨104378, by rfl⟩ : syracuseStep 556685 = 208757) B208757
theorem B556739 : Blo 163797 556739 := bstep (se 1 (by rfl) ⟨417554, by rfl⟩ : syracuseStep 556739 = 835109) B835109
theorem B425873 : Blo 163797 425873 := bstep (se 2 (by rfl) ⟨159702, by rfl⟩ : syracuseStep 425873 = 319405) B319405
theorem B557009 : Blo 163797 557009 := bstep (se 2 (by rfl) ⟨208878, by rfl⟩ : syracuseStep 557009 = 417757) B417757
theorem B163811 : Blo 163797 163811 := bstep (se 1 (by rfl) ⟨122858, by rfl⟩ : syracuseStep 163811 = 245717) B245717
theorem B1802225 : Blo 163797 1802225 := bstep (se 2 (by rfl) ⟨675834, by rfl⟩ : syracuseStep 1802225 = 1351669) B1351669
theorem B163827 : Blo 163797 163827 := bstep (se 1 (by rfl) ⟨122870, by rfl⟩ : syracuseStep 163827 = 245741) B245741
theorem B163851 : Blo 163797 163851 := bstep (se 1 (by rfl) ⟨122888, by rfl⟩ : syracuseStep 163851 = 245777) B245777
theorem B163863 : Blo 163797 163863 := bstep (se 1 (by rfl) ⟨122897, by rfl⟩ : syracuseStep 163863 = 245795) B245795
theorem B163883 : Blo 163797 163883 := bstep (se 1 (by rfl) ⟨122912, by rfl⟩ : syracuseStep 163883 = 245825) B245825
theorem B163895 : Blo 163797 163895 := bstep (se 1 (by rfl) ⟨122921, by rfl⟩ : syracuseStep 163895 = 245843) B245843
theorem B163915 : Blo 163797 163915 := bstep (se 1 (by rfl) ⟨122936, by rfl⟩ : syracuseStep 163915 = 245873) B245873
theorem B163927 : Blo 163797 163927 := bstep (se 1 (by rfl) ⟨122945, by rfl⟩ : syracuseStep 163927 = 245891) B245891
theorem B163947 : Blo 163797 163947 := bstep (se 1 (by rfl) ⟨122960, by rfl⟩ : syracuseStep 163947 = 245921) B245921
theorem B163959 : Blo 163797 163959 := bstep (se 1 (by rfl) ⟨122969, by rfl⟩ : syracuseStep 163959 = 245939) B245939
theorem B163979 : Blo 163797 163979 := bstep (se 1 (by rfl) ⟨122984, by rfl⟩ : syracuseStep 163979 = 245969) B245969
theorem B163991 : Blo 163797 163991 := bstep (se 1 (by rfl) ⟨122993, by rfl⟩ : syracuseStep 163991 = 245987) B245987
theorem B164011 : Blo 163797 164011 := bstep (se 1 (by rfl) ⟨123008, by rfl⟩ : syracuseStep 164011 = 246017) B246017
theorem B164023 : Blo 163797 164023 := bstep (se 1 (by rfl) ⟨123017, by rfl⟩ : syracuseStep 164023 = 246035) B246035
theorem B164043 : Blo 163797 164043 := bstep (se 1 (by rfl) ⟨123032, by rfl⟩ : syracuseStep 164043 = 246065) B246065
theorem B164055 : Blo 163797 164055 := bstep (se 1 (by rfl) ⟨123041, by rfl⟩ : syracuseStep 164055 = 246083) B246083
theorem B164075 : Blo 163797 164075 := bstep (se 1 (by rfl) ⟨123056, by rfl⟩ : syracuseStep 164075 = 246113) B246113
theorem B164087 : Blo 163797 164087 := bstep (se 1 (by rfl) ⟨123065, by rfl⟩ : syracuseStep 164087 = 246131) B246131
theorem B164107 : Blo 163797 164107 := bstep (se 1 (by rfl) ⟨123080, by rfl⟩ : syracuseStep 164107 = 246161) B246161
theorem B164119 : Blo 163797 164119 := bstep (se 1 (by rfl) ⟨123089, by rfl⟩ : syracuseStep 164119 = 246179) B246179
theorem B164139 : Blo 163797 164139 := bstep (se 1 (by rfl) ⟨123104, by rfl⟩ : syracuseStep 164139 = 246209) B246209
theorem B164151 : Blo 163797 164151 := bstep (se 1 (by rfl) ⟨123113, by rfl⟩ : syracuseStep 164151 = 246227) B246227
theorem B164171 : Blo 163797 164171 := bstep (se 1 (by rfl) ⟨123128, by rfl⟩ : syracuseStep 164171 = 246257) B246257
theorem B557387 : Blo 163797 557387 := bstep (se 1 (by rfl) ⟨418040, by rfl⟩ : syracuseStep 557387 = 836081) B836081
theorem B164183 : Blo 163797 164183 := bstep (se 1 (by rfl) ⟨123137, by rfl⟩ : syracuseStep 164183 = 246275) B246275
theorem B164203 : Blo 163797 164203 := bstep (se 1 (by rfl) ⟨123152, by rfl⟩ : syracuseStep 164203 = 246305) B246305
theorem B164215 : Blo 163797 164215 := bstep (se 1 (by rfl) ⟨123161, by rfl⟩ : syracuseStep 164215 = 246323) B246323
theorem B164235 : Blo 163797 164235 := bstep (se 1 (by rfl) ⟨123176, by rfl⟩ : syracuseStep 164235 = 246353) B246353
theorem B4882837 : Blo 163797 4882837 := bstep (se 6 (by rfl) ⟨114441, by rfl⟩ : syracuseStep 4882837 = 228883) B228883
theorem B393623 : Blo 163797 393623 := bstep (se 1 (by rfl) ⟨295217, by rfl⟩ : syracuseStep 393623 = 590435) B590435
theorem B164247 : Blo 163797 164247 := bstep (se 1 (by rfl) ⟨123185, by rfl⟩ : syracuseStep 164247 = 246371) B246371
theorem B164267 : Blo 163797 164267 := bstep (se 1 (by rfl) ⟨123200, by rfl⟩ : syracuseStep 164267 = 246401) B246401
theorem B1245617 : Blo 163797 1245617 := bstep (se 2 (by rfl) ⟨467106, by rfl⟩ : syracuseStep 1245617 = 934213) B934213
theorem B164279 : Blo 163797 164279 := bstep (se 1 (by rfl) ⟨123209, by rfl⟩ : syracuseStep 164279 = 246419) B246419
theorem B164299 : Blo 163797 164299 := bstep (se 1 (by rfl) ⟨123224, by rfl⟩ : syracuseStep 164299 = 246449) B246449
theorem B164311 : Blo 163797 164311 := bstep (se 1 (by rfl) ⟨123233, by rfl⟩ : syracuseStep 164311 = 246467) B246467
theorem B164331 : Blo 163797 164331 := bstep (se 1 (by rfl) ⟨123248, by rfl⟩ : syracuseStep 164331 = 246497) B246497
theorem B164343 : Blo 163797 164343 := bstep (se 1 (by rfl) ⟨123257, by rfl⟩ : syracuseStep 164343 = 246515) B246515
theorem B164363 : Blo 163797 164363 := bstep (se 1 (by rfl) ⟨123272, by rfl⟩ : syracuseStep 164363 = 246545) B246545
theorem B164375 : Blo 163797 164375 := bstep (se 1 (by rfl) ⟨123281, by rfl⟩ : syracuseStep 164375 = 246563) B246563
theorem B164395 : Blo 163797 164395 := bstep (se 1 (by rfl) ⟨123296, by rfl⟩ : syracuseStep 164395 = 246593) B246593
theorem B164407 : Blo 163797 164407 := bstep (se 1 (by rfl) ⟨123305, by rfl⟩ : syracuseStep 164407 = 246611) B246611
theorem B164427 : Blo 163797 164427 := bstep (se 1 (by rfl) ⟨123320, by rfl⟩ : syracuseStep 164427 = 246641) B246641
theorem B164439 : Blo 163797 164439 := bstep (se 1 (by rfl) ⟨123329, by rfl⟩ : syracuseStep 164439 = 246659) B246659
theorem B557657 : Blo 163797 557657 := bstep (se 2 (by rfl) ⟨209121, by rfl⟩ : syracuseStep 557657 = 418243) B418243
theorem B164459 : Blo 163797 164459 := bstep (se 1 (by rfl) ⟨123344, by rfl⟩ : syracuseStep 164459 = 246689) B246689
theorem B164471 : Blo 163797 164471 := bstep (se 1 (by rfl) ⟨123353, by rfl⟩ : syracuseStep 164471 = 246707) B246707
theorem B164491 : Blo 163797 164491 := bstep (se 1 (by rfl) ⟨123368, by rfl⟩ : syracuseStep 164491 = 246737) B246737
theorem B164503 : Blo 163797 164503 := bstep (se 1 (by rfl) ⟨123377, by rfl⟩ : syracuseStep 164503 = 246755) B246755
theorem B164523 : Blo 163797 164523 := bstep (se 1 (by rfl) ⟨123392, by rfl⟩ : syracuseStep 164523 = 246785) B246785
theorem B164535 : Blo 163797 164535 := bstep (se 1 (by rfl) ⟨123401, by rfl⟩ : syracuseStep 164535 = 246803) B246803
theorem B164555 : Blo 163797 164555 := bstep (se 1 (by rfl) ⟨123416, by rfl⟩ : syracuseStep 164555 = 246833) B246833
theorem B164567 : Blo 163797 164567 := bstep (se 1 (by rfl) ⟨123425, by rfl⟩ : syracuseStep 164567 = 246851) B246851
theorem B164587 : Blo 163797 164587 := bstep (se 1 (by rfl) ⟨123440, by rfl⟩ : syracuseStep 164587 = 246881) B246881
theorem B164599 : Blo 163797 164599 := bstep (se 1 (by rfl) ⟨123449, by rfl⟩ : syracuseStep 164599 = 246899) B246899
theorem B164619 : Blo 163797 164619 := bstep (se 1 (by rfl) ⟨123464, by rfl⟩ : syracuseStep 164619 = 246929) B246929
theorem B164631 : Blo 163797 164631 := bstep (se 1 (by rfl) ⟨123473, by rfl⟩ : syracuseStep 164631 = 246947) B246947
theorem B164651 : Blo 163797 164651 := bstep (se 1 (by rfl) ⟨123488, by rfl⟩ : syracuseStep 164651 = 246977) B246977
theorem B164663 : Blo 163797 164663 := bstep (se 1 (by rfl) ⟨123497, by rfl⟩ : syracuseStep 164663 = 246995) B246995
theorem B164683 : Blo 163797 164683 := bstep (se 1 (by rfl) ⟨123512, by rfl⟩ : syracuseStep 164683 = 247025) B247025
theorem B164695 : Blo 163797 164695 := bstep (se 1 (by rfl) ⟨123521, by rfl⟩ : syracuseStep 164695 = 247043) B247043
theorem B164715 : Blo 163797 164715 := bstep (se 1 (by rfl) ⟨123536, by rfl⟩ : syracuseStep 164715 = 247073) B247073
theorem B164727 : Blo 163797 164727 := bstep (se 1 (by rfl) ⟨123545, by rfl⟩ : syracuseStep 164727 = 247091) B247091
theorem B590723 : Blo 163797 590723 := bstep (se 1 (by rfl) ⟨443042, by rfl⟩ : syracuseStep 590723 = 886085) B886085
theorem B164747 : Blo 163797 164747 := bstep (se 1 (by rfl) ⟨123560, by rfl⟩ : syracuseStep 164747 = 247121) B247121
theorem B1246103 : Blo 163797 1246103 := bstep (se 1 (by rfl) ⟨934577, by rfl⟩ : syracuseStep 1246103 = 1869155) B1869155
theorem B164759 : Blo 163797 164759 := bstep (se 1 (by rfl) ⟨123569, by rfl⟩ : syracuseStep 164759 = 247139) B247139
theorem B164779 : Blo 163797 164779 := bstep (se 1 (by rfl) ⟨123584, by rfl⟩ : syracuseStep 164779 = 247169) B247169
theorem B164791 : Blo 163797 164791 := bstep (se 1 (by rfl) ⟨123593, by rfl⟩ : syracuseStep 164791 = 247187) B247187
theorem B164811 : Blo 163797 164811 := bstep (se 1 (by rfl) ⟨123608, by rfl⟩ : syracuseStep 164811 = 247217) B247217
theorem B295895 : Blo 163797 295895 := bstep (se 1 (by rfl) ⟨221921, by rfl⟩ : syracuseStep 295895 = 443843) B443843
theorem B164823 : Blo 163797 164823 := bstep (se 1 (by rfl) ⟨123617, by rfl⟩ : syracuseStep 164823 = 247235) B247235
theorem B164843 : Blo 163797 164843 := bstep (se 1 (by rfl) ⟨123632, by rfl⟩ : syracuseStep 164843 = 247265) B247265
theorem B164855 : Blo 163797 164855 := bstep (se 1 (by rfl) ⟨123641, by rfl⟩ : syracuseStep 164855 = 247283) B247283
theorem B164875 : Blo 163797 164875 := bstep (se 1 (by rfl) ⟨123656, by rfl⟩ : syracuseStep 164875 = 247313) B247313
theorem B164887 : Blo 163797 164887 := bstep (se 1 (by rfl) ⟨123665, by rfl⟩ : syracuseStep 164887 = 247331) B247331
theorem B164907 : Blo 163797 164907 := bstep (se 1 (by rfl) ⟨123680, by rfl⟩ : syracuseStep 164907 = 247361) B247361
theorem B164919 : Blo 163797 164919 := bstep (se 1 (by rfl) ⟨123689, by rfl⟩ : syracuseStep 164919 = 247379) B247379
theorem B164939 : Blo 163797 164939 := bstep (se 1 (by rfl) ⟨123704, by rfl⟩ : syracuseStep 164939 = 247409) B247409
theorem B164951 : Blo 163797 164951 := bstep (se 1 (by rfl) ⟨123713, by rfl⟩ : syracuseStep 164951 = 247427) B247427
theorem B164971 : Blo 163797 164971 := bstep (se 1 (by rfl) ⟨123728, by rfl⟩ : syracuseStep 164971 = 247457) B247457
theorem B164983 : Blo 163797 164983 := bstep (se 1 (by rfl) ⟨123737, by rfl⟩ : syracuseStep 164983 = 247475) B247475
theorem B1508483 : Blo 163797 1508483 := bstep (se 1 (by rfl) ⟨1131362, by rfl⟩ : syracuseStep 1508483 = 2262725) B2262725
theorem B165003 : Blo 163797 165003 := bstep (se 1 (by rfl) ⟨123752, by rfl⟩ : syracuseStep 165003 = 247505) B247505
theorem B165015 : Blo 163797 165015 := bstep (se 1 (by rfl) ⟨123761, by rfl⟩ : syracuseStep 165015 = 247523) B247523
theorem B165035 : Blo 163797 165035 := bstep (se 1 (by rfl) ⟨123776, by rfl⟩ : syracuseStep 165035 = 247553) B247553
theorem B165047 : Blo 163797 165047 := bstep (se 1 (by rfl) ⟨123785, by rfl⟩ : syracuseStep 165047 = 247571) B247571
theorem B165067 : Blo 163797 165067 := bstep (se 1 (by rfl) ⟨123800, by rfl⟩ : syracuseStep 165067 = 247601) B247601
theorem B165079 : Blo 163797 165079 := bstep (se 1 (by rfl) ⟨123809, by rfl⟩ : syracuseStep 165079 = 247619) B247619
theorem B165099 : Blo 163797 165099 := bstep (se 1 (by rfl) ⟨123824, by rfl⟩ : syracuseStep 165099 = 247649) B247649
theorem B165111 : Blo 163797 165111 := bstep (se 1 (by rfl) ⟨123833, by rfl⟩ : syracuseStep 165111 = 247667) B247667
theorem B165131 : Blo 163797 165131 := bstep (se 1 (by rfl) ⟨123848, by rfl⟩ : syracuseStep 165131 = 247697) B247697
theorem B165143 : Blo 163797 165143 := bstep (se 1 (by rfl) ⟨123857, by rfl⟩ : syracuseStep 165143 = 247715) B247715
theorem B558359 : Blo 163797 558359 := bstep (se 1 (by rfl) ⟨418769, by rfl⟩ : syracuseStep 558359 = 837539) B837539
theorem B165163 : Blo 163797 165163 := bstep (se 1 (by rfl) ⟨123872, by rfl⟩ : syracuseStep 165163 = 247745) B247745
theorem B165175 : Blo 163797 165175 := bstep (se 1 (by rfl) ⟨123881, by rfl⟩ : syracuseStep 165175 = 247763) B247763
theorem B165195 : Blo 163797 165195 := bstep (se 1 (by rfl) ⟨123896, by rfl⟩ : syracuseStep 165195 = 247793) B247793
theorem B165207 : Blo 163797 165207 := bstep (se 1 (by rfl) ⟨123905, by rfl⟩ : syracuseStep 165207 = 247811) B247811
theorem B165227 : Blo 163797 165227 := bstep (se 1 (by rfl) ⟨123920, by rfl⟩ : syracuseStep 165227 = 247841) B247841
theorem B165239 : Blo 163797 165239 := bstep (se 1 (by rfl) ⟨123929, by rfl⟩ : syracuseStep 165239 = 247859) B247859
theorem B165259 : Blo 163797 165259 := bstep (se 1 (by rfl) ⟨123944, by rfl⟩ : syracuseStep 165259 = 247889) B247889
theorem B165271 : Blo 163797 165271 := bstep (se 1 (by rfl) ⟨123953, by rfl⟩ : syracuseStep 165271 = 247907) B247907
theorem B165291 : Blo 163797 165291 := bstep (se 1 (by rfl) ⟨123968, by rfl⟩ : syracuseStep 165291 = 247937) B247937
theorem B165303 : Blo 163797 165303 := bstep (se 1 (by rfl) ⟨123977, by rfl⟩ : syracuseStep 165303 = 247955) B247955
theorem B165323 : Blo 163797 165323 := bstep (se 1 (by rfl) ⟨123992, by rfl⟩ : syracuseStep 165323 = 247985) B247985
theorem B165335 : Blo 163797 165335 := bstep (se 1 (by rfl) ⟨124001, by rfl⟩ : syracuseStep 165335 = 248003) B248003
theorem B165355 : Blo 163797 165355 := bstep (se 1 (by rfl) ⟨124016, by rfl⟩ : syracuseStep 165355 = 248033) B248033
theorem B165367 : Blo 163797 165367 := bstep (se 1 (by rfl) ⟨124025, by rfl⟩ : syracuseStep 165367 = 248051) B248051
theorem B624131 : Blo 163797 624131 := bstep (se 1 (by rfl) ⟨468098, by rfl⟩ : syracuseStep 624131 = 936197) B936197
theorem B165387 : Blo 163797 165387 := bstep (se 1 (by rfl) ⟨124040, by rfl⟩ : syracuseStep 165387 = 248081) B248081
theorem B624145 : Blo 163797 624145 := bstep (se 2 (by rfl) ⟨234054, by rfl⟩ : syracuseStep 624145 = 468109) B468109
theorem B165399 : Blo 163797 165399 := bstep (se 1 (by rfl) ⟨124049, by rfl⟩ : syracuseStep 165399 = 248099) B248099
theorem B165419 : Blo 163797 165419 := bstep (se 1 (by rfl) ⟨124064, by rfl⟩ : syracuseStep 165419 = 248129) B248129
theorem B165431 : Blo 163797 165431 := bstep (se 1 (by rfl) ⟨124073, by rfl⟩ : syracuseStep 165431 = 248147) B248147
theorem B165451 : Blo 163797 165451 := bstep (se 1 (by rfl) ⟨124088, by rfl⟩ : syracuseStep 165451 = 248177) B248177
theorem B165463 : Blo 163797 165463 := bstep (se 1 (by rfl) ⟨124097, by rfl⟩ : syracuseStep 165463 = 248195) B248195
theorem B165483 : Blo 163797 165483 := bstep (se 1 (by rfl) ⟨124112, by rfl⟩ : syracuseStep 165483 = 248225) B248225
theorem B165495 : Blo 163797 165495 := bstep (se 1 (by rfl) ⟨124121, by rfl⟩ : syracuseStep 165495 = 248243) B248243
theorem B263819 : Blo 163797 263819 := bstep (se 1 (by rfl) ⟨197864, by rfl⟩ : syracuseStep 263819 = 395729) B395729
theorem B165515 : Blo 163797 165515 := bstep (se 1 (by rfl) ⟨124136, by rfl⟩ : syracuseStep 165515 = 248273) B248273
theorem B165527 : Blo 163797 165527 := bstep (se 1 (by rfl) ⟨124145, by rfl⟩ : syracuseStep 165527 = 248291) B248291
theorem B165547 : Blo 163797 165547 := bstep (se 1 (by rfl) ⟨124160, by rfl⟩ : syracuseStep 165547 = 248321) B248321
theorem B165559 : Blo 163797 165559 := bstep (se 1 (by rfl) ⟨124169, by rfl⟩ : syracuseStep 165559 = 248339) B248339
theorem B165579 : Blo 163797 165579 := bstep (se 1 (by rfl) ⟨124184, by rfl⟩ : syracuseStep 165579 = 248369) B248369
theorem B165591 : Blo 163797 165591 := bstep (se 1 (by rfl) ⟨124193, by rfl⟩ : syracuseStep 165591 = 248387) B248387
theorem B165611 : Blo 163797 165611 := bstep (se 1 (by rfl) ⟨124208, by rfl⟩ : syracuseStep 165611 = 248417) B248417
theorem B165623 : Blo 163797 165623 := bstep (se 1 (by rfl) ⟨124217, by rfl⟩ : syracuseStep 165623 = 248435) B248435
theorem B165643 : Blo 163797 165643 := bstep (se 1 (by rfl) ⟨124232, by rfl⟩ : syracuseStep 165643 = 248465) B248465
theorem B165655 : Blo 163797 165655 := bstep (se 1 (by rfl) ⟨124241, by rfl⟩ : syracuseStep 165655 = 248483) B248483
theorem B165675 : Blo 163797 165675 := bstep (se 1 (by rfl) ⟨124256, by rfl⟩ : syracuseStep 165675 = 248513) B248513
theorem B558899 : Blo 163797 558899 := bstep (se 1 (by rfl) ⟨419174, by rfl⟩ : syracuseStep 558899 = 838349) B838349
theorem B165687 : Blo 163797 165687 := bstep (se 1 (by rfl) ⟨124265, by rfl⟩ : syracuseStep 165687 = 248531) B248531
theorem B624449 : Blo 163797 624449 := bstep (se 2 (by rfl) ⟨234168, by rfl⟩ : syracuseStep 624449 = 468337) B468337
theorem B165707 : Blo 163797 165707 := bstep (se 1 (by rfl) ⟨124280, by rfl⟩ : syracuseStep 165707 = 248561) B248561
theorem B165719 : Blo 163797 165719 := bstep (se 1 (by rfl) ⟨124289, by rfl⟩ : syracuseStep 165719 = 248579) B248579
theorem B165739 : Blo 163797 165739 := bstep (se 1 (by rfl) ⟨124304, by rfl⟩ : syracuseStep 165739 = 248609) B248609
theorem B165751 : Blo 163797 165751 := bstep (se 1 (by rfl) ⟨124313, by rfl⟩ : syracuseStep 165751 = 248627) B248627
theorem B165771 : Blo 163797 165771 := bstep (se 1 (by rfl) ⟨124328, by rfl⟩ : syracuseStep 165771 = 248657) B248657
theorem B165783 : Blo 163797 165783 := bstep (se 1 (by rfl) ⟨124337, by rfl⟩ : syracuseStep 165783 = 248675) B248675
theorem B165803 : Blo 163797 165803 := bstep (se 1 (by rfl) ⟨124352, by rfl⟩ : syracuseStep 165803 = 248705) B248705
theorem B165815 : Blo 163797 165815 := bstep (se 1 (by rfl) ⟨124361, by rfl⟩ : syracuseStep 165815 = 248723) B248723
theorem B165835 : Blo 163797 165835 := bstep (se 1 (by rfl) ⟨124376, by rfl⟩ : syracuseStep 165835 = 248753) B248753
theorem B165847 : Blo 163797 165847 := bstep (se 1 (by rfl) ⟨124385, by rfl⟩ : syracuseStep 165847 = 248771) B248771
theorem B165867 : Blo 163797 165867 := bstep (se 1 (by rfl) ⟨124400, by rfl⟩ : syracuseStep 165867 = 248801) B248801
theorem B165879 : Blo 163797 165879 := bstep (se 1 (by rfl) ⟨124409, by rfl⟩ : syracuseStep 165879 = 248819) B248819
theorem B165899 : Blo 163797 165899 := bstep (se 1 (by rfl) ⟨124424, by rfl⟩ : syracuseStep 165899 = 248849) B248849
theorem B165911 : Blo 163797 165911 := bstep (se 1 (by rfl) ⟨124433, by rfl⟩ : syracuseStep 165911 = 248867) B248867
theorem B165931 : Blo 163797 165931 := bstep (se 1 (by rfl) ⟨124448, by rfl⟩ : syracuseStep 165931 = 248897) B248897
theorem B165943 : Blo 163797 165943 := bstep (se 1 (by rfl) ⟨124457, by rfl⟩ : syracuseStep 165943 = 248915) B248915
theorem B559169 : Blo 163797 559169 := bstep (se 2 (by rfl) ⟨209688, by rfl⟩ : syracuseStep 559169 = 419377) B419377
theorem B165963 : Blo 163797 165963 := bstep (se 1 (by rfl) ⟨124472, by rfl⟩ : syracuseStep 165963 = 248945) B248945
theorem B165975 : Blo 163797 165975 := bstep (se 1 (by rfl) ⟨124481, by rfl⟩ : syracuseStep 165975 = 248963) B248963
theorem B165995 : Blo 163797 165995 := bstep (se 1 (by rfl) ⟨124496, by rfl⟩ : syracuseStep 165995 = 248993) B248993
theorem B166007 : Blo 163797 166007 := bstep (se 1 (by rfl) ⟨124505, by rfl⟩ : syracuseStep 166007 = 249011) B249011
theorem B264331 : Blo 163797 264331 := bstep (se 1 (by rfl) ⟨198248, by rfl⟩ : syracuseStep 264331 = 396497) B396497
theorem B166027 : Blo 163797 166027 := bstep (se 1 (by rfl) ⟨124520, by rfl⟩ : syracuseStep 166027 = 249041) B249041
theorem B166039 : Blo 163797 166039 := bstep (se 1 (by rfl) ⟨124529, by rfl⟩ : syracuseStep 166039 = 249059) B249059
theorem B166059 : Blo 163797 166059 := bstep (se 1 (by rfl) ⟨124544, by rfl⟩ : syracuseStep 166059 = 249089) B249089
theorem B166071 : Blo 163797 166071 := bstep (se 1 (by rfl) ⟨124553, by rfl⟩ : syracuseStep 166071 = 249107) B249107
theorem B166091 : Blo 163797 166091 := bstep (se 1 (by rfl) ⟨124568, by rfl⟩ : syracuseStep 166091 = 249137) B249137
theorem B166103 : Blo 163797 166103 := bstep (se 1 (by rfl) ⟨124577, by rfl⟩ : syracuseStep 166103 = 249155) B249155
theorem B166123 : Blo 163797 166123 := bstep (se 1 (by rfl) ⟨124592, by rfl⟩ : syracuseStep 166123 = 249185) B249185
theorem B166135 : Blo 163797 166135 := bstep (se 1 (by rfl) ⟨124601, by rfl⟩ : syracuseStep 166135 = 249203) B249203
theorem B166155 : Blo 163797 166155 := bstep (se 1 (by rfl) ⟨124616, by rfl⟩ : syracuseStep 166155 = 249233) B249233
theorem B166167 : Blo 163797 166167 := bstep (se 1 (by rfl) ⟨124625, by rfl⟩ : syracuseStep 166167 = 249251) B249251
theorem B166187 : Blo 163797 166187 := bstep (se 1 (by rfl) ⟨124640, by rfl⟩ : syracuseStep 166187 = 249281) B249281
theorem B166199 : Blo 163797 166199 := bstep (se 1 (by rfl) ⟨124649, by rfl⟩ : syracuseStep 166199 = 249299) B249299
theorem B166219 : Blo 163797 166219 := bstep (se 1 (by rfl) ⟨124664, by rfl⟩ : syracuseStep 166219 = 249329) B249329
theorem B166231 : Blo 163797 166231 := bstep (se 1 (by rfl) ⟨124673, by rfl⟩ : syracuseStep 166231 = 249347) B249347
theorem B166251 : Blo 163797 166251 := bstep (se 1 (by rfl) ⟨124688, by rfl⟩ : syracuseStep 166251 = 249377) B249377
theorem B166263 : Blo 163797 166263 := bstep (se 1 (by rfl) ⟨124697, by rfl⟩ : syracuseStep 166263 = 249395) B249395
theorem B166283 : Blo 163797 166283 := bstep (se 1 (by rfl) ⟨124712, by rfl⟩ : syracuseStep 166283 = 249425) B249425
theorem B166295 : Blo 163797 166295 := bstep (se 1 (by rfl) ⟨124721, by rfl⟩ : syracuseStep 166295 = 249443) B249443
theorem B166315 : Blo 163797 166315 := bstep (se 1 (by rfl) ⟨124736, by rfl⟩ : syracuseStep 166315 = 249473) B249473
theorem B1411505 : Blo 163797 1411505 := bstep (se 2 (by rfl) ⟨529314, by rfl⟩ : syracuseStep 1411505 = 1058629) B1058629
theorem B166327 : Blo 163797 166327 := bstep (se 1 (by rfl) ⟨124745, by rfl⟩ : syracuseStep 166327 = 249491) B249491
theorem B166347 : Blo 163797 166347 := bstep (se 1 (by rfl) ⟨124760, by rfl⟩ : syracuseStep 166347 = 249521) B249521
theorem B166359 : Blo 163797 166359 := bstep (se 1 (by rfl) ⟨124769, by rfl⟩ : syracuseStep 166359 = 249539) B249539
theorem B625117 : Blo 163797 625117 := bstep (se 3 (by rfl) ⟨117209, by rfl⟩ : syracuseStep 625117 = 234419) B234419
theorem B166379 : Blo 163797 166379 := bstep (se 1 (by rfl) ⟨124784, by rfl⟩ : syracuseStep 166379 = 249569) B249569
theorem B166391 : Blo 163797 166391 := bstep (se 1 (by rfl) ⟨124793, by rfl⟩ : syracuseStep 166391 = 249587) B249587
theorem B166411 : Blo 163797 166411 := bstep (se 1 (by rfl) ⟨124808, by rfl⟩ : syracuseStep 166411 = 249617) B249617
theorem B166423 : Blo 163797 166423 := bstep (se 1 (by rfl) ⟨124817, by rfl⟩ : syracuseStep 166423 = 249635) B249635
theorem B166443 : Blo 163797 166443 := bstep (se 1 (by rfl) ⟨124832, by rfl⟩ : syracuseStep 166443 = 249665) B249665
theorem B166455 : Blo 163797 166455 := bstep (se 1 (by rfl) ⟨124841, by rfl⟩ : syracuseStep 166455 = 249683) B249683
theorem B166475 : Blo 163797 166475 := bstep (se 1 (by rfl) ⟨124856, by rfl⟩ : syracuseStep 166475 = 249713) B249713
theorem B166487 : Blo 163797 166487 := bstep (se 1 (by rfl) ⟨124865, by rfl⟩ : syracuseStep 166487 = 249731) B249731
theorem B559709 : Blo 163797 559709 := bstep (se 3 (by rfl) ⟨104945, by rfl⟩ : syracuseStep 559709 = 209891) B209891
theorem B4983389 : Blo 163797 4983389 := bstep (se 3 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 4983389 = 1868771) B1868771
theorem B166507 : Blo 163797 166507 := bstep (se 1 (by rfl) ⟨124880, by rfl⟩ : syracuseStep 166507 = 249761) B249761
theorem B166519 : Blo 163797 166519 := bstep (se 1 (by rfl) ⟨124889, by rfl⟩ : syracuseStep 166519 = 249779) B249779
theorem B166539 : Blo 163797 166539 := bstep (se 1 (by rfl) ⟨124904, by rfl⟩ : syracuseStep 166539 = 249809) B249809
theorem B166551 : Blo 163797 166551 := bstep (se 1 (by rfl) ⟨124913, by rfl⟩ : syracuseStep 166551 = 249827) B249827
theorem B166571 : Blo 163797 166571 := bstep (se 1 (by rfl) ⟨124928, by rfl⟩ : syracuseStep 166571 = 249857) B249857
theorem B166583 : Blo 163797 166583 := bstep (se 1 (by rfl) ⟨124937, by rfl⟩ : syracuseStep 166583 = 249875) B249875
theorem B166603 : Blo 163797 166603 := bstep (se 1 (by rfl) ⟨124952, by rfl⟩ : syracuseStep 166603 = 249905) B249905
theorem B166615 : Blo 163797 166615 := bstep (se 1 (by rfl) ⟨124961, by rfl⟩ : syracuseStep 166615 = 249923) B249923
theorem B166635 : Blo 163797 166635 := bstep (se 1 (by rfl) ⟨124976, by rfl⟩ : syracuseStep 166635 = 249953) B249953
theorem B166647 : Blo 163797 166647 := bstep (se 1 (by rfl) ⟨124985, by rfl⟩ : syracuseStep 166647 = 249971) B249971
theorem B166667 : Blo 163797 166667 := bstep (se 1 (by rfl) ⟨125000, by rfl⟩ : syracuseStep 166667 = 250001) B250001
theorem B166679 : Blo 163797 166679 := bstep (se 1 (by rfl) ⟨125009, by rfl⟩ : syracuseStep 166679 = 250019) B250019
theorem B166699 : Blo 163797 166699 := bstep (se 1 (by rfl) ⟨125024, by rfl⟩ : syracuseStep 166699 = 250049) B250049
theorem B396083 : Blo 163797 396083 := bstep (se 1 (by rfl) ⟨297062, by rfl⟩ : syracuseStep 396083 = 594125) B594125
theorem B166711 : Blo 163797 166711 := bstep (se 1 (by rfl) ⟨125033, by rfl⟩ : syracuseStep 166711 = 250067) B250067
theorem B953153 : Blo 163797 953153 := bstep (se 2 (by rfl) ⟨357432, by rfl⟩ : syracuseStep 953153 = 714865) B714865
theorem B1280843 : Blo 163797 1280843 := bstep (se 1 (by rfl) ⟨960632, by rfl⟩ : syracuseStep 1280843 = 1921265) B1921265
theorem B166731 : Blo 163797 166731 := bstep (se 1 (by rfl) ⟨125048, by rfl⟩ : syracuseStep 166731 = 250097) B250097
theorem B166743 : Blo 163797 166743 := bstep (se 1 (by rfl) ⟨125057, by rfl⟩ : syracuseStep 166743 = 250115) B250115
theorem B265049 : Blo 163797 265049 := bstep (se 2 (by rfl) ⟨99393, by rfl⟩ : syracuseStep 265049 = 198787) B198787
theorem B166763 : Blo 163797 166763 := bstep (se 1 (by rfl) ⟨125072, by rfl⟩ : syracuseStep 166763 = 250145) B250145
theorem B166775 : Blo 163797 166775 := bstep (se 1 (by rfl) ⟨125081, by rfl⟩ : syracuseStep 166775 = 250163) B250163
theorem B166795 : Blo 163797 166795 := bstep (se 1 (by rfl) ⟨125096, by rfl⟩ : syracuseStep 166795 = 250193) B250193
theorem B166807 : Blo 163797 166807 := bstep (se 1 (by rfl) ⟨125105, by rfl⟩ : syracuseStep 166807 = 250211) B250211
theorem B166827 : Blo 163797 166827 := bstep (se 1 (by rfl) ⟨125120, by rfl⟩ : syracuseStep 166827 = 250241) B250241
theorem B166839 : Blo 163797 166839 := bstep (se 1 (by rfl) ⟨125129, by rfl⟩ : syracuseStep 166839 = 250259) B250259
theorem B166859 : Blo 163797 166859 := bstep (se 1 (by rfl) ⟨125144, by rfl⟩ : syracuseStep 166859 = 250289) B250289
theorem B166871 : Blo 163797 166871 := bstep (se 1 (by rfl) ⟨125153, by rfl⟩ : syracuseStep 166871 = 250307) B250307
theorem B166891 : Blo 163797 166891 := bstep (se 1 (by rfl) ⟨125168, by rfl⟩ : syracuseStep 166891 = 250337) B250337
theorem B166903 : Blo 163797 166903 := bstep (se 1 (by rfl) ⟨125177, by rfl⟩ : syracuseStep 166903 = 250355) B250355
theorem B297985 : Blo 163797 297985 := bstep (se 2 (by rfl) ⟨111744, by rfl⟩ : syracuseStep 297985 = 223489) B223489
theorem B166923 : Blo 163797 166923 := bstep (se 1 (by rfl) ⟨125192, by rfl⟩ : syracuseStep 166923 = 250385) B250385
theorem B592913 : Blo 163797 592913 := bstep (se 2 (by rfl) ⟨222342, by rfl⟩ : syracuseStep 592913 = 444685) B444685
theorem B166935 : Blo 163797 166935 := bstep (se 1 (by rfl) ⟨125201, by rfl⟩ : syracuseStep 166935 = 250403) B250403
theorem B166955 : Blo 163797 166955 := bstep (se 1 (by rfl) ⟨125216, by rfl⟩ : syracuseStep 166955 = 250433) B250433
theorem B166967 : Blo 163797 166967 := bstep (se 1 (by rfl) ⟨125225, by rfl⟩ : syracuseStep 166967 = 250451) B250451
theorem B166987 : Blo 163797 166987 := bstep (se 1 (by rfl) ⟨125240, by rfl⟩ : syracuseStep 166987 = 250481) B250481
theorem B166999 : Blo 163797 166999 := bstep (se 1 (by rfl) ⟨125249, by rfl⟩ : syracuseStep 166999 = 250499) B250499
theorem B167019 : Blo 163797 167019 := bstep (se 1 (by rfl) ⟨125264, by rfl⟩ : syracuseStep 167019 = 250529) B250529
theorem B167031 : Blo 163797 167031 := bstep (se 1 (by rfl) ⟨125273, by rfl⟩ : syracuseStep 167031 = 250547) B250547
theorem B167051 : Blo 163797 167051 := bstep (se 1 (by rfl) ⟨125288, by rfl⟩ : syracuseStep 167051 = 250577) B250577
theorem B167063 : Blo 163797 167063 := bstep (se 1 (by rfl) ⟨125297, by rfl⟩ : syracuseStep 167063 = 250595) B250595
theorem B167083 : Blo 163797 167083 := bstep (se 1 (by rfl) ⟨125312, by rfl⟩ : syracuseStep 167083 = 250625) B250625
theorem B167095 : Blo 163797 167095 := bstep (se 1 (by rfl) ⟨125321, by rfl⟩ : syracuseStep 167095 = 250643) B250643
theorem B167115 : Blo 163797 167115 := bstep (se 1 (by rfl) ⟨125336, by rfl⟩ : syracuseStep 167115 = 250673) B250673
theorem B167127 : Blo 163797 167127 := bstep (se 1 (by rfl) ⟨125345, by rfl⟩ : syracuseStep 167127 = 250691) B250691
theorem B1051865 : Blo 163797 1051865 := bstep (se 2 (by rfl) ⟨394449, by rfl⟩ : syracuseStep 1051865 = 788899) B788899
theorem B396505 : Blo 163797 396505 := bstep (se 2 (by rfl) ⟨148689, by rfl⟩ : syracuseStep 396505 = 297379) B297379
theorem B167147 : Blo 163797 167147 := bstep (se 1 (by rfl) ⟨125360, by rfl⟩ : syracuseStep 167147 = 250721) B250721
theorem B167159 : Blo 163797 167159 := bstep (se 1 (by rfl) ⟨125369, by rfl⟩ : syracuseStep 167159 = 250739) B250739
theorem B167179 : Blo 163797 167179 := bstep (se 1 (by rfl) ⟨125384, by rfl⟩ : syracuseStep 167179 = 250769) B250769
theorem B167191 : Blo 163797 167191 := bstep (se 1 (by rfl) ⟨125393, by rfl⟩ : syracuseStep 167191 = 250787) B250787
theorem B167211 : Blo 163797 167211 := bstep (se 1 (by rfl) ⟨125408, by rfl⟩ : syracuseStep 167211 = 250817) B250817
theorem B167223 : Blo 163797 167223 := bstep (se 1 (by rfl) ⟨125417, by rfl⟩ : syracuseStep 167223 = 250835) B250835
theorem B167243 : Blo 163797 167243 := bstep (se 1 (by rfl) ⟨125432, by rfl⟩ : syracuseStep 167243 = 250865) B250865
theorem B167255 : Blo 163797 167255 := bstep (se 1 (by rfl) ⟨125441, by rfl⟩ : syracuseStep 167255 = 250883) B250883
theorem B953693 : Blo 163797 953693 := bstep (se 3 (by rfl) ⟨178817, by rfl⟩ : syracuseStep 953693 = 357635) B357635
theorem B167275 : Blo 163797 167275 := bstep (se 1 (by rfl) ⟨125456, by rfl⟩ : syracuseStep 167275 = 250913) B250913
theorem B167287 : Blo 163797 167287 := bstep (se 1 (by rfl) ⟨125465, by rfl⟩ : syracuseStep 167287 = 250931) B250931
theorem B167307 : Blo 163797 167307 := bstep (se 1 (by rfl) ⟨125480, by rfl⟩ : syracuseStep 167307 = 250961) B250961
theorem B167319 : Blo 163797 167319 := bstep (se 1 (by rfl) ⟨125489, by rfl⟩ : syracuseStep 167319 = 250979) B250979
theorem B167339 : Blo 163797 167339 := bstep (se 1 (by rfl) ⟨125504, by rfl⟩ : syracuseStep 167339 = 251009) B251009
theorem B167351 : Blo 163797 167351 := bstep (se 1 (by rfl) ⟨125513, by rfl⟩ : syracuseStep 167351 = 251027) B251027
theorem B167371 : Blo 163797 167371 := bstep (se 1 (by rfl) ⟨125528, by rfl⟩ : syracuseStep 167371 = 251057) B251057
theorem B167383 : Blo 163797 167383 := bstep (se 1 (by rfl) ⟨125537, by rfl⟩ : syracuseStep 167383 = 251075) B251075
theorem B167403 : Blo 163797 167403 := bstep (se 1 (by rfl) ⟨125552, by rfl⟩ : syracuseStep 167403 = 251105) B251105
theorem B167415 : Blo 163797 167415 := bstep (se 1 (by rfl) ⟨125561, by rfl⟩ : syracuseStep 167415 = 251123) B251123
theorem B167435 : Blo 163797 167435 := bstep (se 1 (by rfl) ⟨125576, by rfl⟩ : syracuseStep 167435 = 251153) B251153
theorem B167447 : Blo 163797 167447 := bstep (se 1 (by rfl) ⟨125585, by rfl⟩ : syracuseStep 167447 = 251171) B251171
theorem B167467 : Blo 163797 167467 := bstep (se 1 (by rfl) ⟨125600, by rfl⟩ : syracuseStep 167467 = 251201) B251201
theorem B167479 : Blo 163797 167479 := bstep (se 1 (by rfl) ⟨125609, by rfl⟩ : syracuseStep 167479 = 251219) B251219
theorem B167499 : Blo 163797 167499 := bstep (se 1 (by rfl) ⟨125624, by rfl⟩ : syracuseStep 167499 = 251249) B251249
theorem B167511 : Blo 163797 167511 := bstep (se 1 (by rfl) ⟨125633, by rfl⟩ : syracuseStep 167511 = 251267) B251267
theorem B167531 : Blo 163797 167531 := bstep (se 1 (by rfl) ⟨125648, by rfl⟩ : syracuseStep 167531 = 251297) B251297
theorem B167543 : Blo 163797 167543 := bstep (se 1 (by rfl) ⟨125657, by rfl⟩ : syracuseStep 167543 = 251315) B251315
theorem B167563 : Blo 163797 167563 := bstep (se 1 (by rfl) ⟨125672, by rfl⟩ : syracuseStep 167563 = 251345) B251345
theorem B167575 : Blo 163797 167575 := bstep (se 1 (by rfl) ⟨125681, by rfl⟩ : syracuseStep 167575 = 251363) B251363
theorem B167595 : Blo 163797 167595 := bstep (se 1 (by rfl) ⟨125696, by rfl⟩ : syracuseStep 167595 = 251393) B251393
theorem B167607 : Blo 163797 167607 := bstep (se 1 (by rfl) ⟨125705, by rfl⟩ : syracuseStep 167607 = 251411) B251411
theorem B757451 : Blo 163797 757451 := bstep (se 1 (by rfl) ⟨568088, by rfl⟩ : syracuseStep 757451 = 1136177) B1136177
theorem B560843 : Blo 163797 560843 := bstep (se 1 (by rfl) ⟨420632, by rfl⟩ : syracuseStep 560843 = 841265) B841265
theorem B167627 : Blo 163797 167627 := bstep (se 1 (by rfl) ⟨125720, by rfl⟩ : syracuseStep 167627 = 251441) B251441
theorem B167639 : Blo 163797 167639 := bstep (se 1 (by rfl) ⟨125729, by rfl⟩ : syracuseStep 167639 = 251459) B251459
theorem B626393 : Blo 163797 626393 := bstep (se 2 (by rfl) ⟨234897, by rfl⟩ : syracuseStep 626393 = 469795) B469795
theorem B167659 : Blo 163797 167659 := bstep (se 1 (by rfl) ⟨125744, by rfl⟩ : syracuseStep 167659 = 251489) B251489
theorem B167671 : Blo 163797 167671 := bstep (se 1 (by rfl) ⟨125753, by rfl⟩ : syracuseStep 167671 = 251507) B251507
theorem B167691 : Blo 163797 167691 := bstep (se 1 (by rfl) ⟨125768, by rfl⟩ : syracuseStep 167691 = 251537) B251537
theorem B167703 : Blo 163797 167703 := bstep (se 1 (by rfl) ⟨125777, by rfl⟩ : syracuseStep 167703 = 251555) B251555
theorem B167723 : Blo 163797 167723 := bstep (se 1 (by rfl) ⟨125792, by rfl⟩ : syracuseStep 167723 = 251585) B251585
theorem B167735 : Blo 163797 167735 := bstep (se 1 (by rfl) ⟨125801, by rfl⟩ : syracuseStep 167735 = 251603) B251603
theorem B167755 : Blo 163797 167755 := bstep (se 1 (by rfl) ⟨125816, by rfl⟩ : syracuseStep 167755 = 251633) B251633
theorem B167767 : Blo 163797 167767 := bstep (se 1 (by rfl) ⟨125825, by rfl⟩ : syracuseStep 167767 = 251651) B251651
theorem B3411811 : Blo 163797 3411811 := bstep (se 1 (by rfl) ⟨2558858, by rfl⟩ : syracuseStep 3411811 = 5117717) B5117717
theorem B167787 : Blo 163797 167787 := bstep (se 1 (by rfl) ⟨125840, by rfl⟩ : syracuseStep 167787 = 251681) B251681
theorem B364441 : Blo 163797 364441 := bstep (se 2 (by rfl) ⟨136665, by rfl⟩ : syracuseStep 364441 = 273331) B273331
theorem B593837 : Blo 163797 593837 := bstep (se 3 (by rfl) ⟨111344, by rfl⟩ : syracuseStep 593837 = 222689) B222689
theorem B561113 : Blo 163797 561113 := bstep (se 2 (by rfl) ⟨210417, by rfl⟩ : syracuseStep 561113 = 420835) B420835
theorem B757777 : Blo 163797 757777 := bstep (se 2 (by rfl) ⟨284166, by rfl⟩ : syracuseStep 757777 = 568333) B568333
theorem B954443 : Blo 163797 954443 := bstep (se 1 (by rfl) ⟨715832, by rfl⟩ : syracuseStep 954443 = 1431665) B1431665
theorem B233867 : Blo 163797 233867 := bstep (se 1 (by rfl) ⟨175400, by rfl⟩ : syracuseStep 233867 = 350801) B350801
theorem B332299 : Blo 163797 332299 := bstep (se 1 (by rfl) ⟨249224, by rfl⟩ : syracuseStep 332299 = 498449) B498449
theorem B299585 : Blo 163797 299585 := bstep (se 2 (by rfl) ⟨112344, by rfl⟩ : syracuseStep 299585 = 224689) B224689
theorem B332363 : Blo 163797 332363 := bstep (se 1 (by rfl) ⟨249272, by rfl⟩ : syracuseStep 332363 = 498545) B498545
theorem B856669 : Blo 163797 856669 := bstep (se 3 (by rfl) ⟨160625, by rfl⟩ : syracuseStep 856669 = 321251) B321251
theorem B561815 : Blo 163797 561815 := bstep (se 1 (by rfl) ⟨421361, by rfl⟩ : syracuseStep 561815 = 842723) B842723
theorem B1184557 : Blo 163797 1184557 := bstep (se 3 (by rfl) ⟨222104, by rfl⟩ : syracuseStep 1184557 = 444209) B444209
theorem B595019 : Blo 163797 595019 := bstep (se 1 (by rfl) ⟨446264, by rfl⟩ : syracuseStep 595019 = 892529) B892529
theorem B562355 : Blo 163797 562355 := bstep (se 1 (by rfl) ⟨421766, by rfl⟩ : syracuseStep 562355 = 843533) B843533
theorem B628019 : Blo 163797 628019 := bstep (se 1 (by rfl) ⟨471014, by rfl⟩ : syracuseStep 628019 = 942029) B942029
theorem B628033 : Blo 163797 628033 := bstep (se 2 (by rfl) ⟨235512, by rfl⟩ : syracuseStep 628033 = 471025) B471025
theorem B234841 : Blo 163797 234841 := bstep (se 2 (by rfl) ⟨88065, by rfl⟩ : syracuseStep 234841 = 176131) B176131
theorem B562625 : Blo 163797 562625 := bstep (se 2 (by rfl) ⟨210984, by rfl⟩ : syracuseStep 562625 = 421969) B421969
theorem B1054529 : Blo 163797 1054529 := bstep (se 2 (by rfl) ⟨395448, by rfl⟩ : syracuseStep 1054529 = 790897) B790897
theorem B563165 : Blo 163797 563165 := bstep (se 3 (by rfl) ⟨105593, by rfl⟩ : syracuseStep 563165 = 211187) B211187
theorem B301337 : Blo 163797 301337 := bstep (se 2 (by rfl) ⟨113001, by rfl⟩ : syracuseStep 301337 = 226003) B226003
theorem B235991 : Blo 163797 235991 := bstep (se 1 (by rfl) ⟨176993, by rfl⟩ : syracuseStep 235991 = 353987) B353987
theorem B301619 : Blo 163797 301619 := bstep (se 1 (by rfl) ⟨226214, by rfl⟩ : syracuseStep 301619 = 452429) B452429
theorem B531161 : Blo 163797 531161 := bstep (se 2 (by rfl) ⟨199185, by rfl⟩ : syracuseStep 531161 = 398371) B398371
theorem B236299 : Blo 163797 236299 := bstep (se 1 (by rfl) ⟨177224, by rfl⟩ : syracuseStep 236299 = 354449) B354449
theorem B1514315 : Blo 163797 1514315 := bstep (se 1 (by rfl) ⟨1135736, by rfl⟩ : syracuseStep 1514315 = 2271473) B2271473
theorem B760769 : Blo 163797 760769 := bstep (se 2 (by rfl) ⟨285288, by rfl⟩ : syracuseStep 760769 = 570577) B570577
theorem B498739 : Blo 163797 498739 := bstep (se 1 (by rfl) ⟨374054, by rfl⟩ : syracuseStep 498739 = 748109) B748109
theorem B564299 : Blo 163797 564299 := bstep (se 1 (by rfl) ⟨423224, by rfl⟩ : syracuseStep 564299 = 846449) B846449
theorem B236695 : Blo 163797 236695 := bstep (se 1 (by rfl) ⟨177521, by rfl⟩ : syracuseStep 236695 = 355043) B355043
theorem B629963 : Blo 163797 629963 := bstep (se 1 (by rfl) ⟨472472, by rfl⟩ : syracuseStep 629963 = 944945) B944945
theorem B629977 : Blo 163797 629977 := bstep (se 2 (by rfl) ⟨236241, by rfl⟩ : syracuseStep 629977 = 472483) B472483
theorem B400601 : Blo 163797 400601 := bstep (se 2 (by rfl) ⟨150225, by rfl⟩ : syracuseStep 400601 = 300451) B300451
theorem B564569 : Blo 163797 564569 := bstep (se 2 (by rfl) ⟨211713, by rfl⟩ : syracuseStep 564569 = 423427) B423427
theorem B1285649 : Blo 163797 1285649 := bstep (se 2 (by rfl) ⟨482118, by rfl⟩ : syracuseStep 1285649 = 964237) B964237
theorem B597527 : Blo 163797 597527 := bstep (se 1 (by rfl) ⟨448145, by rfl⟩ : syracuseStep 597527 = 896291) B896291
theorem B237335 : Blo 163797 237335 := bstep (se 1 (by rfl) ⟨178001, by rfl⟩ : syracuseStep 237335 = 356003) B356003
theorem B237529 : Blo 163797 237529 := bstep (se 2 (by rfl) ⟨89073, by rfl⟩ : syracuseStep 237529 = 178147) B178147
theorem B1253393 : Blo 163797 1253393 := bstep (se 2 (by rfl) ⟨470022, by rfl⟩ : syracuseStep 1253393 = 940045) B940045
theorem B565271 : Blo 163797 565271 := bstep (se 1 (by rfl) ⟨423953, by rfl⟩ : syracuseStep 565271 = 847907) B847907
theorem B368729 : Blo 163797 368729 := bstep (se 2 (by rfl) ⟨138273, by rfl⟩ : syracuseStep 368729 = 276547) B276547
theorem B630935 : Blo 163797 630935 := bstep (se 1 (by rfl) ⟨473201, by rfl⟩ : syracuseStep 630935 = 946403) B946403
theorem B368819 : Blo 163797 368819 := bstep (se 1 (by rfl) ⟨276614, by rfl⟩ : syracuseStep 368819 = 553229) B553229
theorem B368855 : Blo 163797 368855 := bstep (se 1 (by rfl) ⟨276641, by rfl⟩ : syracuseStep 368855 = 553283) B553283
theorem B369035 : Blo 163797 369035 := bstep (se 1 (by rfl) ⟨276776, by rfl⟩ : syracuseStep 369035 = 553553) B553553
theorem B369089 : Blo 163797 369089 := bstep (se 2 (by rfl) ⟨138408, by rfl⟩ : syracuseStep 369089 = 276817) B276817
theorem B565811 : Blo 163797 565811 := bstep (se 1 (by rfl) ⟨424358, by rfl⟩ : syracuseStep 565811 = 848717) B848717
theorem B3711581 : Blo 163797 3711581 := bstep (se 3 (by rfl) ⟨695921, by rfl⟩ : syracuseStep 3711581 = 1391843) B1391843
theorem B1352285 : Blo 163797 1352285 := bstep (se 3 (by rfl) ⟨253553, by rfl⟩ : syracuseStep 1352285 = 507107) B507107
theorem B369305 : Blo 163797 369305 := bstep (se 2 (by rfl) ⟨138489, by rfl⟩ : syracuseStep 369305 = 276979) B276979
theorem B303769 : Blo 163797 303769 := bstep (se 2 (by rfl) ⟨113913, by rfl⟩ : syracuseStep 303769 = 227827) B227827
theorem B336563 : Blo 163797 336563 := bstep (se 1 (by rfl) ⟨252422, by rfl⟩ : syracuseStep 336563 = 504845) B504845
theorem B2859725 : Blo 163797 2859725 := bstep (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) B1072397
theorem B271063 : Blo 163797 271063 := bstep (se 1 (by rfl) ⟨203297, by rfl⟩ : syracuseStep 271063 = 406595) B406595
theorem B369395 : Blo 163797 369395 := bstep (se 1 (by rfl) ⟨277046, by rfl⟩ : syracuseStep 369395 = 554093) B554093
theorem B369431 : Blo 163797 369431 := bstep (se 1 (by rfl) ⟨277073, by rfl⟩ : syracuseStep 369431 = 554147) B554147
theorem B1581869 : Blo 163797 1581869 := bstep (se 3 (by rfl) ⟨296600, by rfl⟩ : syracuseStep 1581869 = 593201) B593201
theorem B566081 : Blo 163797 566081 := bstep (se 2 (by rfl) ⟨212280, by rfl⟩ : syracuseStep 566081 = 424561) B424561
theorem B664499 : Blo 163797 664499 := bstep (se 1 (by rfl) ⟨498374, by rfl⟩ : syracuseStep 664499 = 996749) B996749
theorem B533441 : Blo 163797 533441 := bstep (se 2 (by rfl) ⟨200040, by rfl⟩ : syracuseStep 533441 = 400081) B400081
theorem B369611 : Blo 163797 369611 := bstep (se 1 (by rfl) ⟨277208, by rfl⟩ : syracuseStep 369611 = 554417) B554417
theorem B369665 : Blo 163797 369665 := bstep (se 2 (by rfl) ⟨138624, by rfl⟩ : syracuseStep 369665 = 277249) B277249
theorem B3220631 : Blo 163797 3220631 := bstep (se 1 (by rfl) ⟨2415473, by rfl⟩ : syracuseStep 3220631 = 4830947) B4830947
theorem B369881 : Blo 163797 369881 := bstep (se 2 (by rfl) ⟨138705, by rfl⟩ : syracuseStep 369881 = 277411) B277411
theorem B369971 : Blo 163797 369971 := bstep (se 1 (by rfl) ⟨277478, by rfl⟩ : syracuseStep 369971 = 554957) B554957
theorem B370007 : Blo 163797 370007 := bstep (se 1 (by rfl) ⟨277505, by rfl⟩ : syracuseStep 370007 = 555011) B555011
theorem B632195 : Blo 163797 632195 := bstep (se 1 (by rfl) ⟨474146, by rfl⟩ : syracuseStep 632195 = 948293) B948293
theorem B370187 : Blo 163797 370187 := bstep (se 1 (by rfl) ⟨277640, by rfl⟩ : syracuseStep 370187 = 555281) B555281
theorem B370241 : Blo 163797 370241 := bstep (se 2 (by rfl) ⟨138840, by rfl⟩ : syracuseStep 370241 = 277681) B277681
theorem B304769 : Blo 163797 304769 := bstep (se 2 (by rfl) ⟨114288, by rfl⟩ : syracuseStep 304769 = 228577) B228577
theorem B501427 : Blo 163797 501427 := bstep (se 1 (by rfl) ⟨376070, by rfl⟩ : syracuseStep 501427 = 752141) B752141
theorem B337601 : Blo 163797 337601 := bstep (se 2 (by rfl) ⟨126600, by rfl⟩ : syracuseStep 337601 = 253201) B253201
theorem B370457 : Blo 163797 370457 := bstep (se 2 (by rfl) ⟨138921, by rfl⟩ : syracuseStep 370457 = 277843) B277843
theorem B829277 : Blo 163797 829277 := bstep (se 3 (by rfl) ⟨155489, by rfl⟩ : syracuseStep 829277 = 310979) B310979
theorem B370547 : Blo 163797 370547 := bstep (se 1 (by rfl) ⟨277910, by rfl⟩ : syracuseStep 370547 = 555821) B555821
theorem B796547 : Blo 163797 796547 := bstep (se 1 (by rfl) ⟨597410, by rfl⟩ : syracuseStep 796547 = 1194821) B1194821
theorem B370583 : Blo 163797 370583 := bstep (se 1 (by rfl) ⟨277937, by rfl⟩ : syracuseStep 370583 = 555875) B555875
theorem B468929 : Blo 163797 468929 := bstep (se 2 (by rfl) ⟨175848, by rfl⟩ : syracuseStep 468929 = 351697) B351697
theorem B468953 : Blo 163797 468953 := bstep (se 2 (by rfl) ⟨175857, by rfl⟩ : syracuseStep 468953 = 351715) B351715
theorem B370763 : Blo 163797 370763 := bstep (se 1 (by rfl) ⟨278072, by rfl⟩ : syracuseStep 370763 = 556145) B556145
theorem B370817 : Blo 163797 370817 := bstep (se 2 (by rfl) ⟨139056, by rfl⟩ : syracuseStep 370817 = 278113) B278113
theorem B600281 : Blo 163797 600281 := bstep (se 2 (by rfl) ⟨225105, by rfl⟩ : syracuseStep 600281 = 450211) B450211
theorem B371033 : Blo 163797 371033 := bstep (se 2 (by rfl) ⟨139137, by rfl⟩ : syracuseStep 371033 = 278275) B278275
theorem B600409 : Blo 163797 600409 := bstep (se 2 (by rfl) ⟨225153, by rfl⟩ : syracuseStep 600409 = 450307) B450307
theorem B371123 : Blo 163797 371123 := bstep (se 1 (by rfl) ⟨278342, by rfl⟩ : syracuseStep 371123 = 556685) B556685
theorem B371159 : Blo 163797 371159 := bstep (se 1 (by rfl) ⟨278369, by rfl⟩ : syracuseStep 371159 = 556739) B556739
theorem B371339 : Blo 163797 371339 := bstep (se 1 (by rfl) ⟨278504, by rfl⟩ : syracuseStep 371339 = 557009) B557009
theorem B371393 : Blo 163797 371393 := bstep (se 2 (by rfl) ⟨139272, by rfl⟩ : syracuseStep 371393 = 278545) B278545
theorem B535261 : Blo 163797 535261 := bstep (se 3 (by rfl) ⟨100361, by rfl⟩ : syracuseStep 535261 = 200723) B200723
theorem B731927 : Blo 163797 731927 := bstep (se 1 (by rfl) ⟨548945, by rfl⟩ : syracuseStep 731927 = 1097891) B1097891
theorem B371609 : Blo 163797 371609 := bstep (se 2 (by rfl) ⟨139353, by rfl⟩ : syracuseStep 371609 = 278707) B278707
theorem B2010035 : Blo 163797 2010035 := bstep (se 1 (by rfl) ⟨1507526, by rfl⟩ : syracuseStep 2010035 = 3015053) B3015053
theorem B371699 : Blo 163797 371699 := bstep (se 1 (by rfl) ⟨278774, by rfl⟩ : syracuseStep 371699 = 557549) B557549
theorem B175127 : Blo 163797 175127 := bstep (se 1 (by rfl) ⟨131345, by rfl⟩ : syracuseStep 175127 = 262691) B262691
theorem B371735 : Blo 163797 371735 := bstep (se 1 (by rfl) ⟨278801, by rfl⟩ : syracuseStep 371735 = 557603) B557603
theorem B4238405 : Blo 163797 4238405 := bstep (se 4 (by rfl) ⟨397350, by rfl⟩ : syracuseStep 4238405 = 794701) B794701
theorem B207947 : Blo 163797 207947 := bstep (se 1 (by rfl) ⟨155960, by rfl⟩ : syracuseStep 207947 = 311921) B311921
theorem B666755 : Blo 163797 666755 := bstep (se 1 (by rfl) ⟨500066, by rfl⟩ : syracuseStep 666755 = 1000133) B1000133
theorem B470195 : Blo 163797 470195 := bstep (se 1 (by rfl) ⟨352646, by rfl⟩ : syracuseStep 470195 = 705293) B705293
theorem B371915 : Blo 163797 371915 := bstep (se 1 (by rfl) ⟨278936, by rfl⟩ : syracuseStep 371915 = 557873) B557873
theorem B371969 : Blo 163797 371969 := bstep (se 2 (by rfl) ⟨139488, by rfl⟩ : syracuseStep 371969 = 278977) B278977
theorem B339223 : Blo 163797 339223 := bstep (se 1 (by rfl) ⟨254417, by rfl⟩ : syracuseStep 339223 = 508835) B508835
theorem B1879361 : Blo 163797 1879361 := bstep (se 2 (by rfl) ⟨704760, by rfl⟩ : syracuseStep 1879361 = 1409521) B1409521
theorem B339287 : Blo 163797 339287 := bstep (se 1 (by rfl) ⟨254465, by rfl⟩ : syracuseStep 339287 = 508931) B508931
theorem B372185 : Blo 163797 372185 := bstep (se 2 (by rfl) ⟨139569, by rfl⟩ : syracuseStep 372185 = 279139) B279139
theorem B634391 : Blo 163797 634391 := bstep (se 1 (by rfl) ⟨475793, by rfl⟩ : syracuseStep 634391 = 951587) B951587
theorem B241175 : Blo 163797 241175 := bstep (se 1 (by rfl) ⟨180881, by rfl⟩ : syracuseStep 241175 = 361763) B361763
theorem B372275 : Blo 163797 372275 := bstep (se 1 (by rfl) ⟨279206, by rfl⟩ : syracuseStep 372275 = 558413) B558413
theorem B372311 : Blo 163797 372311 := bstep (se 1 (by rfl) ⟨279233, by rfl⟩ : syracuseStep 372311 = 558467) B558467
theorem B1584791 : Blo 163797 1584791 := bstep (se 1 (by rfl) ⟨1188593, by rfl⟩ : syracuseStep 1584791 = 2377187) B2377187
theorem B208651 : Blo 163797 208651 := bstep (se 1 (by rfl) ⟨156488, by rfl⟩ : syracuseStep 208651 = 312977) B312977
theorem B372491 : Blo 163797 372491 := bstep (se 1 (by rfl) ⟨279368, by rfl⟩ : syracuseStep 372491 = 558737) B558737
theorem B1257281 : Blo 163797 1257281 := bstep (se 2 (by rfl) ⟨471480, by rfl⟩ : syracuseStep 1257281 = 942961) B942961
theorem B372545 : Blo 163797 372545 := bstep (se 2 (by rfl) ⟨139704, by rfl⟩ : syracuseStep 372545 = 279409) B279409
theorem B700235 : Blo 163797 700235 := bstep (se 1 (by rfl) ⟨525176, by rfl⟩ : syracuseStep 700235 = 1050353) B1050353
theorem B831383 : Blo 163797 831383 := bstep (se 1 (by rfl) ⟨623537, by rfl⟩ : syracuseStep 831383 = 1247075) B1247075
theorem B2109361 : Blo 163797 2109361 := bstep (se 2 (by rfl) ⟨791010, by rfl⟩ : syracuseStep 2109361 = 1582021) B1582021
theorem B208919 : Blo 163797 208919 := bstep (se 1 (by rfl) ⟨156689, by rfl⟩ : syracuseStep 208919 = 313379) B313379
theorem B372761 : Blo 163797 372761 := bstep (se 2 (by rfl) ⟨139785, by rfl⟩ : syracuseStep 372761 = 279571) B279571
theorem B372851 : Blo 163797 372851 := bstep (se 1 (by rfl) ⟨279638, by rfl⟩ : syracuseStep 372851 = 559277) B559277
theorem B372887 : Blo 163797 372887 := bstep (se 1 (by rfl) ⟨279665, by rfl⟩ : syracuseStep 372887 = 559331) B559331
theorem B602315 : Blo 163797 602315 := bstep (se 1 (by rfl) ⟨451736, by rfl⟩ : syracuseStep 602315 = 903473) B903473
theorem B373067 : Blo 163797 373067 := bstep (se 1 (by rfl) ⟨279800, by rfl⟩ : syracuseStep 373067 = 559601) B559601
theorem B373121 : Blo 163797 373121 := bstep (se 2 (by rfl) ⟨139920, by rfl⟩ : syracuseStep 373121 = 279841) B279841
theorem B635309 : Blo 163797 635309 := bstep (se 3 (by rfl) ⟨119120, by rfl⟩ : syracuseStep 635309 = 238241) B238241
theorem B373337 : Blo 163797 373337 := bstep (se 2 (by rfl) ⟨140001, by rfl⟩ : syracuseStep 373337 = 280003) B280003
theorem B373427 : Blo 163797 373427 := bstep (se 1 (by rfl) ⟨280070, by rfl⟩ : syracuseStep 373427 = 560141) B560141
theorem B209623 : Blo 163797 209623 := bstep (se 1 (by rfl) ⟨157217, by rfl⟩ : syracuseStep 209623 = 314435) B314435
theorem B373463 : Blo 163797 373463 := bstep (se 1 (by rfl) ⟨280097, by rfl⟩ : syracuseStep 373463 = 560195) B560195
theorem B701207 : Blo 163797 701207 := bstep (se 1 (by rfl) ⟨525905, by rfl⟩ : syracuseStep 701207 = 1051811) B1051811
theorem B176951 : Blo 163797 176951 := bstep (se 1 (by rfl) ⟨132713, by rfl⟩ : syracuseStep 176951 = 265427) B265427
theorem B1192805 : Blo 163797 1192805 := bstep (se 4 (by rfl) ⟨111825, by rfl⟩ : syracuseStep 1192805 = 223651) B223651
theorem B373643 : Blo 163797 373643 := bstep (se 1 (by rfl) ⟨280232, by rfl⟩ : syracuseStep 373643 = 560465) B560465
theorem B373697 : Blo 163797 373697 := bstep (se 2 (by rfl) ⟨140136, by rfl⟩ : syracuseStep 373697 = 280273) B280273
theorem B2012177 : Blo 163797 2012177 := bstep (se 2 (by rfl) ⟨754566, by rfl⟩ : syracuseStep 2012177 = 1509133) B1509133
theorem B373913 : Blo 163797 373913 := bstep (se 2 (by rfl) ⟨140217, by rfl⟩ : syracuseStep 373913 = 280435) B280435
theorem B636083 : Blo 163797 636083 := bstep (se 1 (by rfl) ⟨477062, by rfl⟩ : syracuseStep 636083 = 954125) B954125
theorem B374003 : Blo 163797 374003 := bstep (se 1 (by rfl) ⟨280502, by rfl⟩ : syracuseStep 374003 = 561005) B561005
theorem B374039 : Blo 163797 374039 := bstep (se 1 (by rfl) ⟨280529, by rfl⟩ : syracuseStep 374039 = 561059) B561059
theorem B374219 : Blo 163797 374219 := bstep (se 1 (by rfl) ⟨280664, by rfl⟩ : syracuseStep 374219 = 561329) B561329
theorem B177643 : Blo 163797 177643 := bstep (se 1 (by rfl) ⟨133232, by rfl⟩ : syracuseStep 177643 = 266465) B266465
theorem B374273 : Blo 163797 374273 := bstep (se 2 (by rfl) ⟨140352, by rfl⟩ : syracuseStep 374273 = 280705) B280705
theorem B2668049 : Blo 163797 2668049 := bstep (se 2 (by rfl) ⟨1000518, by rfl⟩ : syracuseStep 2668049 = 2001037) B2001037
theorem B1259225 : Blo 163797 1259225 := bstep (se 2 (by rfl) ⟨472209, by rfl⟩ : syracuseStep 1259225 = 944419) B944419
theorem B374489 : Blo 163797 374489 := bstep (se 2 (by rfl) ⟨140433, by rfl⟩ : syracuseStep 374489 = 280867) B280867
theorem B374579 : Blo 163797 374579 := bstep (se 1 (by rfl) ⟨280934, by rfl⟩ : syracuseStep 374579 = 561869) B561869
theorem B374615 : Blo 163797 374615 := bstep (se 1 (by rfl) ⟨280961, by rfl⟩ : syracuseStep 374615 = 561923) B561923
theorem B276439 : Blo 163797 276439 := bstep (se 1 (by rfl) ⟨207329, by rfl⟩ : syracuseStep 276439 = 414659) B414659
theorem B473053 : Blo 163797 473053 := bstep (se 3 (by rfl) ⟨88697, by rfl⟩ : syracuseStep 473053 = 177395) B177395
theorem B374795 : Blo 163797 374795 := bstep (se 1 (by rfl) ⟨281096, by rfl⟩ : syracuseStep 374795 = 562193) B562193
theorem B473111 : Blo 163797 473111 := bstep (se 1 (by rfl) ⟨354833, by rfl⟩ : syracuseStep 473111 = 709667) B709667
theorem B374849 : Blo 163797 374849 := bstep (se 2 (by rfl) ⟨140568, by rfl⟩ : syracuseStep 374849 = 281137) B281137
theorem B375065 : Blo 163797 375065 := bstep (se 2 (by rfl) ⟨140649, by rfl⟩ : syracuseStep 375065 = 281299) B281299
theorem B375155 : Blo 163797 375155 := bstep (se 1 (by rfl) ⟨281366, by rfl⟩ : syracuseStep 375155 = 562733) B562733
theorem B211339 : Blo 163797 211339 := bstep (se 1 (by rfl) ⟨158504, by rfl⟩ : syracuseStep 211339 = 317009) B317009
theorem B375191 : Blo 163797 375191 := bstep (se 1 (by rfl) ⟨281393, by rfl⟩ : syracuseStep 375191 = 562787) B562787
theorem B277067 : Blo 163797 277067 := bstep (se 1 (by rfl) ⟨207800, by rfl⟩ : syracuseStep 277067 = 415601) B415601
theorem B375371 : Blo 163797 375371 := bstep (se 1 (by rfl) ⟨281528, by rfl⟩ : syracuseStep 375371 = 563057) B563057
theorem B375425 : Blo 163797 375425 := bstep (se 2 (by rfl) ⟨140784, by rfl⟩ : syracuseStep 375425 = 281569) B281569
theorem B277195 : Blo 163797 277195 := bstep (se 1 (by rfl) ⟨207896, by rfl⟩ : syracuseStep 277195 = 415793) B415793
theorem B178967 : Blo 163797 178967 := bstep (se 1 (by rfl) ⟨134225, by rfl⟩ : syracuseStep 178967 = 268451) B268451
theorem B277337 : Blo 163797 277337 := bstep (se 2 (by rfl) ⟨104001, by rfl⟩ : syracuseStep 277337 = 208003) B208003
theorem B375641 : Blo 163797 375641 := bstep (se 2 (by rfl) ⟨140865, by rfl⟩ : syracuseStep 375641 = 281731) B281731
theorem B179095 : Blo 163797 179095 := bstep (se 1 (by rfl) ⟨134321, by rfl⟩ : syracuseStep 179095 = 268643) B268643
theorem B375731 : Blo 163797 375731 := bstep (se 1 (by rfl) ⟨281798, by rfl⟩ : syracuseStep 375731 = 563597) B563597
theorem B375767 : Blo 163797 375767 := bstep (se 1 (by rfl) ⟨281825, by rfl⟩ : syracuseStep 375767 = 563651) B563651
theorem B277465 : Blo 163797 277465 := bstep (se 2 (by rfl) ⟨104049, by rfl⟩ : syracuseStep 277465 = 208099) B208099
theorem B375947 : Blo 163797 375947 := bstep (se 1 (by rfl) ⟨281960, by rfl⟩ : syracuseStep 375947 = 563921) B563921
theorem B703667 : Blo 163797 703667 := bstep (se 1 (by rfl) ⟨527750, by rfl⟩ : syracuseStep 703667 = 1055501) B1055501
theorem B376001 : Blo 163797 376001 := bstep (se 2 (by rfl) ⟨141000, by rfl⟩ : syracuseStep 376001 = 282001) B282001
theorem B474329 : Blo 163797 474329 := bstep (se 2 (by rfl) ⟨177873, by rfl⟩ : syracuseStep 474329 = 355747) B355747
theorem B474443 : Blo 163797 474443 := bstep (se 1 (by rfl) ⟨355832, by rfl⟩ : syracuseStep 474443 = 711665) B711665
theorem B212311 : Blo 163797 212311 := bstep (se 1 (by rfl) ⟨159233, by rfl⟩ : syracuseStep 212311 = 318467) B318467
theorem B834947 : Blo 163797 834947 := bstep (se 1 (by rfl) ⟨626210, by rfl⟩ : syracuseStep 834947 = 1252421) B1252421
theorem B376217 : Blo 163797 376217 := bstep (se 2 (by rfl) ⟨141081, by rfl⟩ : syracuseStep 376217 = 282163) B282163
theorem B671179 : Blo 163797 671179 := bstep (se 1 (by rfl) ⟨503384, by rfl⟩ : syracuseStep 671179 = 1006769) B1006769
theorem B376307 : Blo 163797 376307 := bstep (se 1 (by rfl) ⟨282230, by rfl⟩ : syracuseStep 376307 = 564461) B564461
theorem B278039 : Blo 163797 278039 := bstep (se 1 (by rfl) ⟨208529, by rfl⟩ : syracuseStep 278039 = 417059) B417059
theorem B376343 : Blo 163797 376343 := bstep (se 1 (by rfl) ⟨282257, by rfl⟩ : syracuseStep 376343 = 564515) B564515
theorem B278167 : Blo 163797 278167 := bstep (se 1 (by rfl) ⟨208625, by rfl⟩ : syracuseStep 278167 = 417251) B417251
theorem B376523 : Blo 163797 376523 := bstep (se 1 (by rfl) ⟨282392, by rfl⟩ : syracuseStep 376523 = 564785) B564785
theorem B376577 : Blo 163797 376577 := bstep (se 2 (by rfl) ⟨141216, by rfl⟩ : syracuseStep 376577 = 282433) B282433
theorem B2473907 : Blo 163797 2473907 := bstep (se 1 (by rfl) ⟨1855430, by rfl⟩ : syracuseStep 2473907 = 3710861) B3710861
theorem B376793 : Blo 163797 376793 := bstep (se 2 (by rfl) ⟨141297, by rfl⟩ : syracuseStep 376793 = 282595) B282595
theorem B245771 : Blo 163797 245771 := bstep (se 1 (by rfl) ⟨184328, by rfl⟩ : syracuseStep 245771 = 368657) B368657
theorem B245783 : Blo 163797 245783 := bstep (se 1 (by rfl) ⟨184337, by rfl⟩ : syracuseStep 245783 = 368675) B368675
theorem B376883 : Blo 163797 376883 := bstep (se 1 (by rfl) ⟨282662, by rfl⟩ : syracuseStep 376883 = 565325) B565325
theorem B376919 : Blo 163797 376919 := bstep (se 1 (by rfl) ⟨282689, by rfl⟩ : syracuseStep 376919 = 565379) B565379
theorem B245849 : Blo 163797 245849 := bstep (se 2 (by rfl) ⟨92193, by rfl⟩ : syracuseStep 245849 = 184387) B184387
theorem B311435 : Blo 163797 311435 := bstep (se 1 (by rfl) ⟨233576, by rfl⟩ : syracuseStep 311435 = 467153) B467153
theorem B245963 : Blo 163797 245963 := bstep (se 1 (by rfl) ⟨184472, by rfl⟩ : syracuseStep 245963 = 368945) B368945
theorem B245975 : Blo 163797 245975 := bstep (se 1 (by rfl) ⟨184481, by rfl⟩ : syracuseStep 245975 = 368963) B368963
theorem B278795 : Blo 163797 278795 := bstep (se 1 (by rfl) ⟨209096, by rfl⟩ : syracuseStep 278795 = 418193) B418193
theorem B377099 : Blo 163797 377099 := bstep (se 1 (by rfl) ⟨282824, by rfl⟩ : syracuseStep 377099 = 565649) B565649
theorem B246041 : Blo 163797 246041 := bstep (se 2 (by rfl) ⟨92265, by rfl⟩ : syracuseStep 246041 = 184531) B184531
theorem B311617 : Blo 163797 311617 := bstep (se 2 (by rfl) ⟨116856, by rfl⟩ : syracuseStep 311617 = 233713) B233713
theorem B377153 : Blo 163797 377153 := bstep (se 2 (by rfl) ⟨141432, by rfl⟩ : syracuseStep 377153 = 282865) B282865
theorem B246155 : Blo 163797 246155 := bstep (se 1 (by rfl) ⟨184616, by rfl⟩ : syracuseStep 246155 = 369233) B369233
theorem B278923 : Blo 163797 278923 := bstep (se 1 (by rfl) ⟨209192, by rfl⟩ : syracuseStep 278923 = 418385) B418385
theorem B246167 : Blo 163797 246167 := bstep (se 1 (by rfl) ⟨184625, by rfl⟩ : syracuseStep 246167 = 369251) B369251
theorem B475571 : Blo 163797 475571 := bstep (se 1 (by rfl) ⟨356678, by rfl⟩ : syracuseStep 475571 = 713357) B713357
theorem B246233 : Blo 163797 246233 := bstep (se 2 (by rfl) ⟨92337, by rfl⟩ : syracuseStep 246233 = 184675) B184675
theorem B279065 : Blo 163797 279065 := bstep (se 2 (by rfl) ⟨104649, by rfl⟩ : syracuseStep 279065 = 209299) B209299
theorem B377369 : Blo 163797 377369 := bstep (se 2 (by rfl) ⟨141513, by rfl⟩ : syracuseStep 377369 = 283027) B283027
theorem B442945 : Blo 163797 442945 := bstep (se 2 (by rfl) ⟨166104, by rfl⟩ : syracuseStep 442945 = 332209) B332209
theorem B442955 : Blo 163797 442955 := bstep (se 1 (by rfl) ⟨332216, by rfl⟩ : syracuseStep 442955 = 664433) B664433
theorem B246347 : Blo 163797 246347 := bstep (se 1 (by rfl) ⟨184760, by rfl⟩ : syracuseStep 246347 = 369521) B369521
theorem B246359 : Blo 163797 246359 := bstep (se 1 (by rfl) ⟨184769, by rfl⟩ : syracuseStep 246359 = 369539) B369539
theorem B377459 : Blo 163797 377459 := bstep (se 1 (by rfl) ⟨283094, by rfl⟩ : syracuseStep 377459 = 566189) B566189
theorem B377495 : Blo 163797 377495 := bstep (se 1 (by rfl) ⟨283121, by rfl⟩ : syracuseStep 377495 = 566243) B566243
theorem B246425 : Blo 163797 246425 := bstep (se 2 (by rfl) ⟨92409, by rfl⟩ : syracuseStep 246425 = 184819) B184819
theorem B279193 : Blo 163797 279193 := bstep (se 2 (by rfl) ⟨104697, by rfl⟩ : syracuseStep 279193 = 209395) B209395
theorem B246539 : Blo 163797 246539 := bstep (se 1 (by rfl) ⟨184904, by rfl⟩ : syracuseStep 246539 = 369809) B369809
theorem B246551 : Blo 163797 246551 := bstep (se 1 (by rfl) ⟨184913, by rfl⟩ : syracuseStep 246551 = 369827) B369827
theorem B475969 : Blo 163797 475969 := bstep (se 2 (by rfl) ⟨178488, by rfl⟩ : syracuseStep 475969 = 356977) B356977
theorem B246617 : Blo 163797 246617 := bstep (se 2 (by rfl) ⟨92481, by rfl⟩ : syracuseStep 246617 = 184963) B184963
theorem B672605 : Blo 163797 672605 := bstep (se 3 (by rfl) ⟨126113, by rfl⟩ : syracuseStep 672605 = 252227) B252227
theorem B246731 : Blo 163797 246731 := bstep (se 1 (by rfl) ⟨185048, by rfl⟩ : syracuseStep 246731 = 370097) B370097
theorem B246743 : Blo 163797 246743 := bstep (se 1 (by rfl) ⟨185057, by rfl⟩ : syracuseStep 246743 = 370115) B370115
theorem B312331 : Blo 163797 312331 := bstep (se 1 (by rfl) ⟨234248, by rfl⟩ : syracuseStep 312331 = 468497) B468497
theorem B246809 : Blo 163797 246809 := bstep (se 2 (by rfl) ⟨92553, by rfl⟩ : syracuseStep 246809 = 185107) B185107
theorem B1262627 : Blo 163797 1262627 := bstep (se 1 (by rfl) ⟨946970, by rfl⟩ : syracuseStep 1262627 = 1893941) B1893941
theorem B705581 : Blo 163797 705581 := bstep (se 3 (by rfl) ⟨132296, by rfl⟩ : syracuseStep 705581 = 264593) B264593
theorem B312407 : Blo 163797 312407 := bstep (se 1 (by rfl) ⟨234305, by rfl⟩ : syracuseStep 312407 = 468611) B468611
theorem B246923 : Blo 163797 246923 := bstep (se 1 (by rfl) ⟨185192, by rfl⟩ : syracuseStep 246923 = 370385) B370385
theorem B377995 : Blo 163797 377995 := bstep (se 1 (by rfl) ⟨283496, by rfl⟩ : syracuseStep 377995 = 566993) B566993
theorem B246935 : Blo 163797 246935 := bstep (se 1 (by rfl) ⟨185201, by rfl⟩ : syracuseStep 246935 = 370403) B370403
theorem B279767 : Blo 163797 279767 := bstep (se 1 (by rfl) ⟨209825, by rfl⟩ : syracuseStep 279767 = 419651) B419651
theorem B247001 : Blo 163797 247001 := bstep (se 2 (by rfl) ⟨92625, by rfl⟩ : syracuseStep 247001 = 185251) B185251
theorem B247115 : Blo 163797 247115 := bstep (se 1 (by rfl) ⟨185336, by rfl⟩ : syracuseStep 247115 = 370673) B370673
theorem B247127 : Blo 163797 247127 := bstep (se 1 (by rfl) ⟨185345, by rfl⟩ : syracuseStep 247127 = 370691) B370691
theorem B279895 : Blo 163797 279895 := bstep (se 1 (by rfl) ⟨209921, by rfl⟩ : syracuseStep 279895 = 419843) B419843
theorem B247193 : Blo 163797 247193 := bstep (se 2 (by rfl) ⟨92697, by rfl⟩ : syracuseStep 247193 = 185395) B185395
theorem B247307 : Blo 163797 247307 := bstep (se 1 (by rfl) ⟨185480, by rfl⟩ : syracuseStep 247307 = 370961) B370961
theorem B247319 : Blo 163797 247319 := bstep (se 1 (by rfl) ⟨185489, by rfl⟩ : syracuseStep 247319 = 370979) B370979
theorem B2606627 : Blo 163797 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B935489 : Blo 163797 935489 := bstep (se 2 (by rfl) ⟨350808, by rfl⟩ : syracuseStep 935489 = 701617) B701617
theorem B247385 : Blo 163797 247385 := bstep (se 2 (by rfl) ⟨92769, by rfl⟩ : syracuseStep 247385 = 185539) B185539
theorem B771677 : Blo 163797 771677 := bstep (se 3 (by rfl) ⟨144689, by rfl⟩ : syracuseStep 771677 = 289379) B289379
theorem B247499 : Blo 163797 247499 := bstep (se 1 (by rfl) ⟨185624, by rfl⟩ : syracuseStep 247499 = 371249) B371249
theorem B247511 : Blo 163797 247511 := bstep (se 1 (by rfl) ⟨185633, by rfl⟩ : syracuseStep 247511 = 371267) B371267
theorem B706265 : Blo 163797 706265 := bstep (se 2 (by rfl) ⟨264849, by rfl⟩ : syracuseStep 706265 = 529699) B529699
theorem B313075 : Blo 163797 313075 := bstep (se 1 (by rfl) ⟨234806, by rfl⟩ : syracuseStep 313075 = 469613) B469613
theorem B247577 : Blo 163797 247577 := bstep (se 2 (by rfl) ⟨92841, by rfl⟩ : syracuseStep 247577 = 185683) B185683
theorem B247691 : Blo 163797 247691 := bstep (se 1 (by rfl) ⟨185768, by rfl⟩ : syracuseStep 247691 = 371537) B371537
theorem B247703 : Blo 163797 247703 := bstep (se 1 (by rfl) ⟨185777, by rfl⟩ : syracuseStep 247703 = 371555) B371555
theorem B280523 : Blo 163797 280523 := bstep (se 1 (by rfl) ⟨210392, by rfl⟩ : syracuseStep 280523 = 420785) B420785
theorem B313303 : Blo 163797 313303 := bstep (se 1 (by rfl) ⟨234977, by rfl⟩ : syracuseStep 313303 = 469955) B469955
theorem B247769 : Blo 163797 247769 := bstep (se 2 (by rfl) ⟨92913, by rfl⟩ : syracuseStep 247769 = 185827) B185827
theorem B313409 : Blo 163797 313409 := bstep (se 2 (by rfl) ⟨117528, by rfl⟩ : syracuseStep 313409 = 235057) B235057
theorem B247883 : Blo 163797 247883 := bstep (se 1 (by rfl) ⟨185912, by rfl⟩ : syracuseStep 247883 = 371825) B371825
theorem B280651 : Blo 163797 280651 := bstep (se 1 (by rfl) ⟨210488, by rfl⟩ : syracuseStep 280651 = 420977) B420977
theorem B247895 : Blo 163797 247895 := bstep (se 1 (by rfl) ⟨185921, by rfl⟩ : syracuseStep 247895 = 371843) B371843
theorem B247961 : Blo 163797 247961 := bstep (se 2 (by rfl) ⟨92985, by rfl⟩ : syracuseStep 247961 = 185971) B185971
theorem B379073 : Blo 163797 379073 := bstep (se 2 (by rfl) ⟨142152, by rfl⟩ : syracuseStep 379073 = 284305) B284305
theorem B313561 : Blo 163797 313561 := bstep (se 2 (by rfl) ⟨117585, by rfl⟩ : syracuseStep 313561 = 235171) B235171
theorem B280793 : Blo 163797 280793 := bstep (se 2 (by rfl) ⟨105297, by rfl⟩ : syracuseStep 280793 = 210595) B210595
theorem B248075 : Blo 163797 248075 := bstep (se 1 (by rfl) ⟨186056, by rfl⟩ : syracuseStep 248075 = 372113) B372113
theorem B248087 : Blo 163797 248087 := bstep (se 1 (by rfl) ⟨186065, by rfl⟩ : syracuseStep 248087 = 372131) B372131
theorem B248153 : Blo 163797 248153 := bstep (se 2 (by rfl) ⟨93057, by rfl⟩ : syracuseStep 248153 = 186115) B186115
theorem B280921 : Blo 163797 280921 := bstep (se 2 (by rfl) ⟨105345, by rfl⟩ : syracuseStep 280921 = 210691) B210691
theorem B248267 : Blo 163797 248267 := bstep (se 1 (by rfl) ⟨186200, by rfl⟩ : syracuseStep 248267 = 372401) B372401
theorem B248279 : Blo 163797 248279 := bstep (se 1 (by rfl) ⟨186209, by rfl⟩ : syracuseStep 248279 = 372419) B372419
theorem B903641 : Blo 163797 903641 := bstep (se 2 (by rfl) ⟨338865, by rfl⟩ : syracuseStep 903641 = 677731) B677731
theorem B248345 : Blo 163797 248345 := bstep (se 2 (by rfl) ⟨93129, by rfl⟩ : syracuseStep 248345 = 186259) B186259
theorem B379457 : Blo 163797 379457 := bstep (se 2 (by rfl) ⟨142296, by rfl⟩ : syracuseStep 379457 = 284593) B284593
theorem B1067651 : Blo 163797 1067651 := bstep (se 1 (by rfl) ⟨800738, by rfl⟩ : syracuseStep 1067651 = 1601477) B1601477
theorem B248459 : Blo 163797 248459 := bstep (se 1 (by rfl) ⟨186344, by rfl⟩ : syracuseStep 248459 = 372689) B372689
theorem B248471 : Blo 163797 248471 := bstep (se 1 (by rfl) ⟨186353, by rfl⟩ : syracuseStep 248471 = 372707) B372707
theorem B248537 : Blo 163797 248537 := bstep (se 2 (by rfl) ⟨93201, by rfl⟩ : syracuseStep 248537 = 186403) B186403
theorem B707393 : Blo 163797 707393 := bstep (se 2 (by rfl) ⟨265272, by rfl⟩ : syracuseStep 707393 = 530545) B530545
theorem B805697 : Blo 163797 805697 := bstep (se 2 (by rfl) ⟨302136, by rfl⟩ : syracuseStep 805697 = 604273) B604273
theorem B248651 : Blo 163797 248651 := bstep (se 1 (by rfl) ⟨186488, by rfl⟩ : syracuseStep 248651 = 372977) B372977
theorem B248663 : Blo 163797 248663 := bstep (se 1 (by rfl) ⟨186497, by rfl⟩ : syracuseStep 248663 = 372995) B372995
theorem B281495 : Blo 163797 281495 := bstep (se 1 (by rfl) ⟨211121, by rfl⟩ : syracuseStep 281495 = 422243) B422243
theorem B248729 : Blo 163797 248729 := bstep (se 2 (by rfl) ⟨93273, by rfl⟩ : syracuseStep 248729 = 186547) B186547
theorem B2411441 : Blo 163797 2411441 := bstep (se 2 (by rfl) ⟨904290, by rfl⟩ : syracuseStep 2411441 = 1808581) B1808581
theorem B248843 : Blo 163797 248843 := bstep (se 1 (by rfl) ⟨186632, by rfl⟩ : syracuseStep 248843 = 373265) B373265
theorem B838673 : Blo 163797 838673 := bstep (se 2 (by rfl) ⟨314502, by rfl⟩ : syracuseStep 838673 = 629005) B629005
theorem B248855 : Blo 163797 248855 := bstep (se 1 (by rfl) ⟨186641, by rfl⟩ : syracuseStep 248855 = 373283) B373283
theorem B281623 : Blo 163797 281623 := bstep (se 1 (by rfl) ⟨211217, by rfl⟩ : syracuseStep 281623 = 422435) B422435
theorem B248921 : Blo 163797 248921 := bstep (se 2 (by rfl) ⟨93345, by rfl⟩ : syracuseStep 248921 = 186691) B186691
theorem B838835 : Blo 163797 838835 := bstep (se 1 (by rfl) ⟨629126, by rfl⟩ : syracuseStep 838835 = 1258253) B1258253
theorem B249035 : Blo 163797 249035 := bstep (se 1 (by rfl) ⟨186776, by rfl⟩ : syracuseStep 249035 = 373553) B373553
theorem B249047 : Blo 163797 249047 := bstep (se 1 (by rfl) ⟨186785, by rfl⟩ : syracuseStep 249047 = 373571) B373571
theorem B249113 : Blo 163797 249113 := bstep (se 2 (by rfl) ⟨93417, by rfl⟩ : syracuseStep 249113 = 186835) B186835
theorem B806219 : Blo 163797 806219 := bstep (se 1 (by rfl) ⟨604664, by rfl⟩ : syracuseStep 806219 = 1209329) B1209329
theorem B249227 : Blo 163797 249227 := bstep (se 1 (by rfl) ⟨186920, by rfl⟩ : syracuseStep 249227 = 373841) B373841
theorem B249239 : Blo 163797 249239 := bstep (se 1 (by rfl) ⟨186929, by rfl⟩ : syracuseStep 249239 = 373859) B373859
theorem B249305 : Blo 163797 249305 := bstep (se 2 (by rfl) ⟨93489, by rfl⟩ : syracuseStep 249305 = 186979) B186979
theorem B314867 : Blo 163797 314867 := bstep (se 1 (by rfl) ⟨236150, by rfl⟩ : syracuseStep 314867 = 472301) B472301
theorem B249419 : Blo 163797 249419 := bstep (se 1 (by rfl) ⟨187064, by rfl⟩ : syracuseStep 249419 = 374129) B374129
theorem B249431 : Blo 163797 249431 := bstep (se 1 (by rfl) ⟨187073, by rfl⟩ : syracuseStep 249431 = 374147) B374147
theorem B1363549 : Blo 163797 1363549 := bstep (se 3 (by rfl) ⟨255665, by rfl⟩ : syracuseStep 1363549 = 511331) B511331
theorem B315019 : Blo 163797 315019 := bstep (se 1 (by rfl) ⟨236264, by rfl⟩ : syracuseStep 315019 = 472529) B472529
theorem B282251 : Blo 163797 282251 := bstep (se 1 (by rfl) ⟨211688, by rfl⟩ : syracuseStep 282251 = 423377) B423377
theorem B249497 : Blo 163797 249497 := bstep (se 2 (by rfl) ⟨93561, by rfl⟩ : syracuseStep 249497 = 187123) B187123
theorem B249611 : Blo 163797 249611 := bstep (se 1 (by rfl) ⟨187208, by rfl⟩ : syracuseStep 249611 = 374417) B374417
theorem B282379 : Blo 163797 282379 := bstep (se 1 (by rfl) ⟨211784, by rfl⟩ : syracuseStep 282379 = 423569) B423569
theorem B249623 : Blo 163797 249623 := bstep (se 1 (by rfl) ⟨187217, by rfl⟩ : syracuseStep 249623 = 374435) B374435
theorem B1265453 : Blo 163797 1265453 := bstep (se 3 (by rfl) ⟨237272, by rfl⟩ : syracuseStep 1265453 = 474545) B474545
theorem B249689 : Blo 163797 249689 := bstep (se 2 (by rfl) ⟨93633, by rfl⟩ : syracuseStep 249689 = 187267) B187267
theorem B905111 : Blo 163797 905111 := bstep (se 1 (by rfl) ⟨678833, by rfl⟩ : syracuseStep 905111 = 1357667) B1357667
theorem B282521 : Blo 163797 282521 := bstep (se 2 (by rfl) ⟨105945, by rfl⟩ : syracuseStep 282521 = 211891) B211891
theorem B249803 : Blo 163797 249803 := bstep (se 1 (by rfl) ⟨187352, by rfl⟩ : syracuseStep 249803 = 374705) B374705
theorem B184279 : Blo 163797 184279 := bstep (se 1 (by rfl) ⟨138209, by rfl⟩ : syracuseStep 184279 = 276419) B276419
theorem B249815 : Blo 163797 249815 := bstep (se 1 (by rfl) ⟨187361, by rfl⟩ : syracuseStep 249815 = 374723) B374723
theorem B315353 : Blo 163797 315353 := bstep (se 2 (by rfl) ⟨118257, by rfl⟩ : syracuseStep 315353 = 236515) B236515
theorem B249881 : Blo 163797 249881 := bstep (se 2 (by rfl) ⟨93705, by rfl⟩ : syracuseStep 249881 = 187411) B187411
theorem B282649 : Blo 163797 282649 := bstep (se 2 (by rfl) ⟨105993, by rfl⟩ : syracuseStep 282649 = 211987) B211987
theorem B184459 : Blo 163797 184459 := bstep (se 1 (by rfl) ⟨138344, by rfl⟩ : syracuseStep 184459 = 276689) B276689
theorem B249995 : Blo 163797 249995 := bstep (se 1 (by rfl) ⟨187496, by rfl⟩ : syracuseStep 249995 = 374993) B374993
theorem B250007 : Blo 163797 250007 := bstep (se 1 (by rfl) ⟨187505, by rfl⟩ : syracuseStep 250007 = 375011) B375011
theorem B250073 : Blo 163797 250073 := bstep (se 2 (by rfl) ⟨93777, by rfl⟩ : syracuseStep 250073 = 187555) B187555
theorem B184567 : Blo 163797 184567 := bstep (se 1 (by rfl) ⟨138425, by rfl⟩ : syracuseStep 184567 = 276851) B276851
theorem B250187 : Blo 163797 250187 := bstep (se 1 (by rfl) ⟨187640, by rfl⟩ : syracuseStep 250187 = 375281) B375281
theorem B250199 : Blo 163797 250199 := bstep (se 1 (by rfl) ⟨187649, by rfl⟩ : syracuseStep 250199 = 375299) B375299
theorem B250265 : Blo 163797 250265 := bstep (se 2 (by rfl) ⟨93849, by rfl⟩ : syracuseStep 250265 = 187699) B187699
theorem B184747 : Blo 163797 184747 := bstep (se 1 (by rfl) ⟨138560, by rfl⟩ : syracuseStep 184747 = 277121) B277121
theorem B2019763 : Blo 163797 2019763 := bstep (se 1 (by rfl) ⟨1514822, by rfl⟩ : syracuseStep 2019763 = 3029645) B3029645
theorem B709067 : Blo 163797 709067 := bstep (se 1 (by rfl) ⟨531800, by rfl⟩ : syracuseStep 709067 = 1063601) B1063601
theorem B250379 : Blo 163797 250379 := bstep (se 1 (by rfl) ⟨187784, by rfl⟩ : syracuseStep 250379 = 375569) B375569
theorem B184855 : Blo 163797 184855 := bstep (se 1 (by rfl) ⟨138641, by rfl⟩ : syracuseStep 184855 = 277283) B277283
theorem B250391 : Blo 163797 250391 := bstep (se 1 (by rfl) ⟨187793, by rfl⟩ : syracuseStep 250391 = 375587) B375587
theorem B315991 : Blo 163797 315991 := bstep (se 1 (by rfl) ⟨236993, by rfl⟩ : syracuseStep 315991 = 473987) B473987
theorem B250457 : Blo 163797 250457 := bstep (se 2 (by rfl) ⟨93921, by rfl⟩ : syracuseStep 250457 = 187843) B187843
theorem B1495703 : Blo 163797 1495703 := bstep (se 1 (by rfl) ⟨1121777, by rfl⟩ : syracuseStep 1495703 = 2243555) B2243555
theorem B185035 : Blo 163797 185035 := bstep (se 1 (by rfl) ⟨138776, by rfl⟩ : syracuseStep 185035 = 277553) B277553
theorem B250571 : Blo 163797 250571 := bstep (se 1 (by rfl) ⟨187928, by rfl⟩ : syracuseStep 250571 = 375857) B375857
theorem B250583 : Blo 163797 250583 := bstep (se 1 (by rfl) ⟨187937, by rfl⟩ : syracuseStep 250583 = 375875) B375875
theorem B316147 : Blo 163797 316147 := bstep (se 1 (by rfl) ⟨237110, by rfl⟩ : syracuseStep 316147 = 474221) B474221
theorem B250649 : Blo 163797 250649 := bstep (se 2 (by rfl) ⟨93993, by rfl⟩ : syracuseStep 250649 = 187987) B187987
theorem B185143 : Blo 163797 185143 := bstep (se 1 (by rfl) ⟨138857, by rfl⟩ : syracuseStep 185143 = 277715) B277715
theorem B250763 : Blo 163797 250763 := bstep (se 1 (by rfl) ⟨188072, by rfl⟩ : syracuseStep 250763 = 376145) B376145
theorem B250775 : Blo 163797 250775 := bstep (se 1 (by rfl) ⟨188081, by rfl⟩ : syracuseStep 250775 = 376163) B376163
theorem B250841 : Blo 163797 250841 := bstep (se 2 (by rfl) ⟨94065, by rfl⟩ : syracuseStep 250841 = 188131) B188131
theorem B185323 : Blo 163797 185323 := bstep (se 1 (by rfl) ⟨138992, by rfl⟩ : syracuseStep 185323 = 277985) B277985
theorem B840779 : Blo 163797 840779 := bstep (se 1 (by rfl) ⟨630584, by rfl⟩ : syracuseStep 840779 = 1261169) B1261169
theorem B250955 : Blo 163797 250955 := bstep (se 1 (by rfl) ⟨188216, by rfl⟩ : syracuseStep 250955 = 376433) B376433
theorem B185431 : Blo 163797 185431 := bstep (se 1 (by rfl) ⟨139073, by rfl⟩ : syracuseStep 185431 = 278147) B278147
theorem B250967 : Blo 163797 250967 := bstep (se 1 (by rfl) ⟨188225, by rfl⟩ : syracuseStep 250967 = 376451) B376451
theorem B382103 : Blo 163797 382103 := bstep (se 1 (by rfl) ⟨286577, by rfl⟩ : syracuseStep 382103 = 573155) B573155
theorem B251033 : Blo 163797 251033 := bstep (se 2 (by rfl) ⟨94137, by rfl⟩ : syracuseStep 251033 = 188275) B188275
theorem B185611 : Blo 163797 185611 := bstep (se 1 (by rfl) ⟨139208, by rfl⟩ : syracuseStep 185611 = 278417) B278417
theorem B283915 : Blo 163797 283915 := bstep (se 1 (by rfl) ⟨212936, by rfl⟩ : syracuseStep 283915 = 425873) B425873
theorem B251147 : Blo 163797 251147 := bstep (se 1 (by rfl) ⟨188360, by rfl⟩ : syracuseStep 251147 = 376721) B376721
theorem B251159 : Blo 163797 251159 := bstep (se 1 (by rfl) ⟨188369, by rfl⟩ : syracuseStep 251159 = 376739) B376739
theorem B1201483 : Blo 163797 1201483 := bstep (se 1 (by rfl) ⟨901112, by rfl⟩ : syracuseStep 1201483 = 1802225) B1802225
theorem B251225 : Blo 163797 251225 := bstep (se 2 (by rfl) ⟨94209, by rfl⟩ : syracuseStep 251225 = 188419) B188419
theorem B185719 : Blo 163797 185719 := bstep (se 1 (by rfl) ⟨139289, by rfl⟩ : syracuseStep 185719 = 278579) B278579
theorem B316811 : Blo 163797 316811 := bstep (se 1 (by rfl) ⟨237608, by rfl⟩ : syracuseStep 316811 = 475217) B475217
theorem B316865 : Blo 163797 316865 := bstep (se 2 (by rfl) ⟨118824, by rfl⟩ : syracuseStep 316865 = 237649) B237649
theorem B251339 : Blo 163797 251339 := bstep (se 1 (by rfl) ⟨188504, by rfl⟩ : syracuseStep 251339 = 377009) B377009
theorem B251351 : Blo 163797 251351 := bstep (se 1 (by rfl) ⟨188513, by rfl⟩ : syracuseStep 251351 = 377027) B377027
theorem B677393 : Blo 163797 677393 := bstep (se 2 (by rfl) ⟨254022, by rfl⟩ : syracuseStep 677393 = 508045) B508045
theorem B251417 : Blo 163797 251417 := bstep (se 2 (by rfl) ⟨94281, by rfl⟩ : syracuseStep 251417 = 188563) B188563
theorem B185899 : Blo 163797 185899 := bstep (se 1 (by rfl) ⟨139424, by rfl⟩ : syracuseStep 185899 = 278849) B278849
theorem B415307 : Blo 163797 415307 := bstep (se 1 (by rfl) ⟨311480, by rfl⟩ : syracuseStep 415307 = 622961) B622961
theorem B251531 : Blo 163797 251531 := bstep (se 1 (by rfl) ⟨188648, by rfl⟩ : syracuseStep 251531 = 377297) B377297
theorem B186007 : Blo 163797 186007 := bstep (se 1 (by rfl) ⟨139505, by rfl⟩ : syracuseStep 186007 = 279011) B279011
theorem B251543 : Blo 163797 251543 := bstep (se 1 (by rfl) ⟨188657, by rfl⟩ : syracuseStep 251543 = 377315) B377315
theorem B349913 : Blo 163797 349913 := bstep (se 2 (by rfl) ⟨131217, by rfl⟩ : syracuseStep 349913 = 262435) B262435
theorem B251609 : Blo 163797 251609 := bstep (se 2 (by rfl) ⟨94353, by rfl⟩ : syracuseStep 251609 = 188707) B188707
theorem B710365 : Blo 163797 710365 := bstep (se 3 (by rfl) ⟨133193, by rfl⟩ : syracuseStep 710365 = 266387) B266387
theorem B186187 : Blo 163797 186187 := bstep (se 1 (by rfl) ⟨139640, by rfl⟩ : syracuseStep 186187 = 279281) B279281
theorem B677783 : Blo 163797 677783 := bstep (se 1 (by rfl) ⟨508337, by rfl⟩ : syracuseStep 677783 = 1016675) B1016675
theorem B186295 : Blo 163797 186295 := bstep (se 1 (by rfl) ⟨139721, by rfl⟩ : syracuseStep 186295 = 279443) B279443
theorem B481241 : Blo 163797 481241 := bstep (se 2 (by rfl) ⟨180465, by rfl⟩ : syracuseStep 481241 = 360931) B360931
theorem B677911 : Blo 163797 677911 := bstep (se 1 (by rfl) ⟨508433, by rfl⟩ : syracuseStep 677911 = 1016867) B1016867
theorem B710707 : Blo 163797 710707 := bstep (se 1 (by rfl) ⟨533030, by rfl⟩ : syracuseStep 710707 = 1066061) B1066061
theorem B186475 : Blo 163797 186475 := bstep (se 1 (by rfl) ⟨139856, by rfl⟩ : syracuseStep 186475 = 279713) B279713
theorem B678091 : Blo 163797 678091 := bstep (se 1 (by rfl) ⟨508568, by rfl⟩ : syracuseStep 678091 = 1017137) B1017137
theorem B186583 : Blo 163797 186583 := bstep (se 1 (by rfl) ⟨139937, by rfl⟩ : syracuseStep 186583 = 279875) B279875
theorem B1267973 : Blo 163797 1267973 := bstep (se 4 (by rfl) ⟨118872, by rfl⟩ : syracuseStep 1267973 = 237745) B237745
theorem B317783 : Blo 163797 317783 := bstep (se 1 (by rfl) ⟨238337, by rfl⟩ : syracuseStep 317783 = 476675) B476675
theorem B186763 : Blo 163797 186763 := bstep (se 1 (by rfl) ⟨140072, by rfl⟩ : syracuseStep 186763 = 280145) B280145
theorem B186871 : Blo 163797 186871 := bstep (se 1 (by rfl) ⟨140153, by rfl⟩ : syracuseStep 186871 = 280307) B280307
theorem B416279 : Blo 163797 416279 := bstep (se 1 (by rfl) ⟨312209, by rfl⟩ : syracuseStep 416279 = 624419) B624419
theorem B187051 : Blo 163797 187051 := bstep (se 1 (by rfl) ⟨140288, by rfl⟩ : syracuseStep 187051 = 280577) B280577
theorem B350963 : Blo 163797 350963 := bstep (se 1 (by rfl) ⟨263222, by rfl⟩ : syracuseStep 350963 = 526445) B526445
theorem B187159 : Blo 163797 187159 := bstep (se 1 (by rfl) ⟨140369, by rfl⟩ : syracuseStep 187159 = 280739) B280739
theorem B842561 : Blo 163797 842561 := bstep (se 2 (by rfl) ⟨315960, by rfl⟩ : syracuseStep 842561 = 631921) B631921
theorem B318323 : Blo 163797 318323 := bstep (se 1 (by rfl) ⟨238742, by rfl⟩ : syracuseStep 318323 = 477485) B477485
theorem B187339 : Blo 163797 187339 := bstep (se 1 (by rfl) ⟨140504, by rfl⟩ : syracuseStep 187339 = 281009) B281009
theorem B318487 : Blo 163797 318487 := bstep (se 1 (by rfl) ⟨238865, by rfl⟩ : syracuseStep 318487 = 477731) B477731
theorem B187447 : Blo 163797 187447 := bstep (se 1 (by rfl) ⟨140585, by rfl⟩ : syracuseStep 187447 = 281171) B281171
theorem B1432727 : Blo 163797 1432727 := bstep (se 1 (by rfl) ⟨1074545, by rfl⟩ : syracuseStep 1432727 = 2149091) B2149091
theorem B416947 : Blo 163797 416947 := bstep (se 1 (by rfl) ⟨312710, by rfl⟩ : syracuseStep 416947 = 625421) B625421
theorem B187627 : Blo 163797 187627 := bstep (se 1 (by rfl) ⟨140720, by rfl⟩ : syracuseStep 187627 = 281441) B281441
theorem B351553 : Blo 163797 351553 := bstep (se 2 (by rfl) ⟨131832, by rfl⟩ : syracuseStep 351553 = 263665) B263665
theorem B417089 : Blo 163797 417089 := bstep (se 2 (by rfl) ⟨156408, by rfl⟩ : syracuseStep 417089 = 312817) B312817
theorem B187735 : Blo 163797 187735 := bstep (se 1 (by rfl) ⟨140801, by rfl⟩ : syracuseStep 187735 = 281603) B281603
theorem B187915 : Blo 163797 187915 := bstep (se 1 (by rfl) ⟨140936, by rfl⟩ : syracuseStep 187915 = 281873) B281873
theorem B188023 : Blo 163797 188023 := bstep (se 1 (by rfl) ⟨141017, by rfl⟩ : syracuseStep 188023 = 282035) B282035
theorem B188203 : Blo 163797 188203 := bstep (se 1 (by rfl) ⟨141152, by rfl⟩ : syracuseStep 188203 = 282305) B282305
theorem B188311 : Blo 163797 188311 := bstep (se 1 (by rfl) ⟨141233, by rfl⟩ : syracuseStep 188311 = 282467) B282467
theorem B188491 : Blo 163797 188491 := bstep (se 1 (by rfl) ⟨141368, by rfl⟩ : syracuseStep 188491 = 282737) B282737
theorem B1892483 : Blo 163797 1892483 := bstep (se 1 (by rfl) ⟨1419362, by rfl⟩ : syracuseStep 1892483 = 2838725) B2838725
theorem B188599 : Blo 163797 188599 := bstep (se 1 (by rfl) ⟨141449, by rfl⟩ : syracuseStep 188599 = 282899) B282899
theorem B286999 : Blo 163797 286999 := bstep (se 1 (by rfl) ⟨215249, by rfl⟩ : syracuseStep 286999 = 430499) B430499
theorem B418355 : Blo 163797 418355 := bstep (se 1 (by rfl) ⟨313766, by rfl⟩ : syracuseStep 418355 = 627533) B627533
theorem B254539 : Blo 163797 254539 := bstep (se 1 (by rfl) ⟨190904, by rfl⟩ : syracuseStep 254539 = 381809) B381809
theorem B1270403 : Blo 163797 1270403 := bstep (se 1 (by rfl) ⟨952802, by rfl⟩ : syracuseStep 1270403 = 1905605) B1905605
theorem B844505 : Blo 163797 844505 := bstep (se 2 (by rfl) ⟨316689, by rfl⟩ : syracuseStep 844505 = 633379) B633379
theorem B353099 : Blo 163797 353099 := bstep (se 1 (by rfl) ⟨264824, by rfl⟩ : syracuseStep 353099 = 529649) B529649
theorem B1401731 : Blo 163797 1401731 := bstep (se 1 (by rfl) ⟨1051298, by rfl⟩ : syracuseStep 1401731 = 2102597) B2102597
theorem B680849 : Blo 163797 680849 := bstep (se 2 (by rfl) ⟨255318, by rfl⟩ : syracuseStep 680849 = 510637) B510637
theorem B418891 : Blo 163797 418891 := bstep (se 1 (by rfl) ⟨314168, by rfl⟩ : syracuseStep 418891 = 628337) B628337
theorem B943235 : Blo 163797 943235 := bstep (se 1 (by rfl) ⟨707426, by rfl⟩ : syracuseStep 943235 = 1414853) B1414853
theorem B419033 : Blo 163797 419033 := bstep (se 2 (by rfl) ⟨157137, by rfl⟩ : syracuseStep 419033 = 314275) B314275
theorem B1598899 : Blo 163797 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B1336907 : Blo 163797 1336907 := bstep (se 1 (by rfl) ⟨1002680, by rfl⟩ : syracuseStep 1336907 = 2005361) B2005361
theorem B714329 : Blo 163797 714329 := bstep (se 2 (by rfl) ⟨267873, by rfl⟩ : syracuseStep 714329 = 535747) B535747
theorem B353945 : Blo 163797 353945 := bstep (se 2 (by rfl) ⟨132729, by rfl⟩ : syracuseStep 353945 = 265459) B265459
theorem B190199 : Blo 163797 190199 := bstep (se 1 (by rfl) ⟨142649, by rfl⟩ : syracuseStep 190199 = 285299) B285299
theorem B419863 : Blo 163797 419863 := bstep (se 1 (by rfl) ⟨314897, by rfl⟩ : syracuseStep 419863 = 629795) B629795
theorem B2418929 : Blo 163797 2418929 := bstep (se 2 (by rfl) ⟨907098, by rfl⟩ : syracuseStep 2418929 = 1814197) B1814197
theorem B846125 : Blo 163797 846125 := bstep (se 3 (by rfl) ⟨158648, by rfl⟩ : syracuseStep 846125 = 317297) B317297
theorem B354739 : Blo 163797 354739 := bstep (se 1 (by rfl) ⟨266054, by rfl⟩ : syracuseStep 354739 = 532109) B532109
theorem B420299 : Blo 163797 420299 := bstep (se 1 (by rfl) ⟨315224, by rfl⟩ : syracuseStep 420299 = 630449) B630449
theorem B453185 : Blo 163797 453185 := bstep (se 2 (by rfl) ⟨169944, by rfl⟩ : syracuseStep 453185 = 339889) B339889
theorem B420673 : Blo 163797 420673 := bstep (se 2 (by rfl) ⟨157752, by rfl⟩ : syracuseStep 420673 = 315505) B315505
theorem B322483 : Blo 163797 322483 := bstep (se 1 (by rfl) ⟨241862, by rfl⟩ : syracuseStep 322483 = 483725) B483725
theorem B715969 : Blo 163797 715969 := bstep (se 2 (by rfl) ⟨268488, by rfl⟩ : syracuseStep 715969 = 536977) B536977
theorem B355585 : Blo 163797 355585 := bstep (se 2 (by rfl) ⟨133344, by rfl⟩ : syracuseStep 355585 = 266689) B266689
theorem B1240337 : Blo 163797 1240337 := bstep (se 2 (by rfl) ⟨465126, by rfl⟩ : syracuseStep 1240337 = 930253) B930253
theorem B421271 : Blo 163797 421271 := bstep (se 1 (by rfl) ⟨315953, by rfl⟩ : syracuseStep 421271 = 631907) B631907
theorem B355927 : Blo 163797 355927 := bstep (se 1 (by rfl) ⟨266945, by rfl⟩ : syracuseStep 355927 = 533891) B533891
theorem B1601117 : Blo 163797 1601117 := bstep (se 3 (by rfl) ⟨300209, by rfl⟩ : syracuseStep 1601117 = 600419) B600419
theorem B2420375 : Blo 163797 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B13758149 : Blo 163797 13758149 := bstep (se 4 (by rfl) ⟨1289826, by rfl⟩ : syracuseStep 13758149 = 2579653) B2579653
theorem B4812493 : Blo 163797 4812493 := bstep (se 3 (by rfl) ⟨902342, by rfl⟩ : syracuseStep 4812493 = 1804685) B1804685
theorem B1011635 : Blo 163797 1011635 := bstep (se 1 (by rfl) ⟨758726, by rfl⟩ : syracuseStep 1011635 = 1517453) B1517453
theorem B1273805 : Blo 163797 1273805 := bstep (se 3 (by rfl) ⟨238838, by rfl⟩ : syracuseStep 1273805 = 477677) B477677
theorem B749533 : Blo 163797 749533 := bstep (se 3 (by rfl) ⟨140537, by rfl⟩ : syracuseStep 749533 = 281075) B281075
theorem B422081 : Blo 163797 422081 := bstep (se 2 (by rfl) ⟨158280, by rfl⟩ : syracuseStep 422081 = 316561) B316561
theorem B422423 : Blo 163797 422423 := bstep (se 1 (by rfl) ⟨316817, by rfl⟩ : syracuseStep 422423 = 633635) B633635
theorem B1798807 : Blo 163797 1798807 := bstep (se 1 (by rfl) ⟨1349105, by rfl⟩ : syracuseStep 1798807 = 2698211) B2698211
theorem B750259 : Blo 163797 750259 := bstep (se 1 (by rfl) ⟨562694, by rfl⟩ : syracuseStep 750259 = 1125389) B1125389
theorem B422617 : Blo 163797 422617 := bstep (se 2 (by rfl) ⟨158481, by rfl⟩ : syracuseStep 422617 = 316963) B316963
theorem B2847473 : Blo 163797 2847473 := bstep (se 2 (by rfl) ⟨1067802, by rfl⟩ : syracuseStep 2847473 = 2135605) B2135605
theorem B357131 : Blo 163797 357131 := bstep (se 1 (by rfl) ⟨267848, by rfl⟩ : syracuseStep 357131 = 535697) B535697
theorem B3240805 : Blo 163797 3240805 := bstep (se 4 (by rfl) ⟨303825, by rfl⟩ : syracuseStep 3240805 = 607651) B607651
theorem B1995637 : Blo 163797 1995637 := bstep (se 5 (by rfl) ⟨93545, by rfl⟩ : syracuseStep 1995637 = 187091) B187091
theorem B553931 : Blo 163797 553931 := bstep (se 1 (by rfl) ⟨415448, by rfl⟩ : syracuseStep 553931 = 830897) B830897
theorem B357529 : Blo 163797 357529 := bstep (se 2 (by rfl) ⟨134073, by rfl⟩ : syracuseStep 357529 = 268147) B268147
theorem B554201 : Blo 163797 554201 := bstep (se 2 (by rfl) ⟨207825, by rfl⟩ : syracuseStep 554201 = 415651) B415651
theorem B357643 : Blo 163797 357643 := bstep (se 1 (by rfl) ⟨268232, by rfl⟩ : syracuseStep 357643 = 536465) B536465
theorem B423731 : Blo 163797 423731 := bstep (se 1 (by rfl) ⟨317798, by rfl⟩ : syracuseStep 423731 = 635597) B635597
theorem B554903 : Blo 163797 554903 := bstep (se 1 (by rfl) ⟨416177, by rfl⟩ : syracuseStep 554903 = 832355) B832355
theorem B358361 : Blo 163797 358361 := bstep (se 2 (by rfl) ⟨134385, by rfl⟩ : syracuseStep 358361 = 268771) B268771
theorem B424025 : Blo 163797 424025 := bstep (se 2 (by rfl) ⟨159009, by rfl⟩ : syracuseStep 424025 = 318019) B318019
theorem B948611 : Blo 163797 948611 := bstep (se 1 (by rfl) ⟨711458, by rfl⟩ : syracuseStep 948611 = 1422917) B1422917
theorem B555443 : Blo 163797 555443 := bstep (se 1 (by rfl) ⟨416582, by rfl⟩ : syracuseStep 555443 = 833165) B833165
theorem B2095651 : Blo 163797 2095651 := bstep (se 1 (by rfl) ⟨1571738, by rfl⟩ : syracuseStep 2095651 = 3143477) B3143477
theorem B555713 : Blo 163797 555713 := bstep (se 2 (by rfl) ⟨208392, by rfl⟩ : syracuseStep 555713 = 416785) B416785
theorem B752435 : Blo 163797 752435 := bstep (se 1 (by rfl) ⟨564326, by rfl⟩ : syracuseStep 752435 = 1128653) B1128653
theorem B949067 : Blo 163797 949067 := bstep (se 1 (by rfl) ⟨711800, by rfl⟩ : syracuseStep 949067 = 1423601) B1423601
theorem B424855 : Blo 163797 424855 := bstep (se 1 (by rfl) ⟨318641, by rfl⟩ : syracuseStep 424855 = 637283) B637283
theorem B556253 : Blo 163797 556253 := bstep (se 3 (by rfl) ⟨104297, by rfl⟩ : syracuseStep 556253 = 208595) B208595
theorem B229015 : Blo 163797 229015 := bstep (se 1 (by rfl) ⟨171761, by rfl⟩ : syracuseStep 229015 = 343523) B343523
theorem B1867697 : Blo 163797 1867697 := bstep (se 2 (by rfl) ⟨700386, by rfl⟩ : syracuseStep 1867697 = 1400773) B1400773
theorem B163799 : Blo 163797 163799 := bstep (se 1 (by rfl) ⟨122849, by rfl⟩ : syracuseStep 163799 = 245699) B245699
theorem B163819 : Blo 163797 163819 := bstep (se 1 (by rfl) ⟨122864, by rfl⟩ : syracuseStep 163819 = 245729) B245729
theorem B163831 : Blo 163797 163831 := bstep (se 1 (by rfl) ⟨122873, by rfl⟩ : syracuseStep 163831 = 245747) B245747
theorem B163847 : Blo 163797 163847 := bstep (se 1 (by rfl) ⟨122885, by rfl⟩ : syracuseStep 163847 = 245771) B245771
theorem B163855 : Blo 163797 163855 := bstep (se 1 (by rfl) ⟨122891, by rfl⟩ : syracuseStep 163855 = 245783) B245783
theorem B163899 : Blo 163797 163899 := bstep (se 1 (by rfl) ⟨122924, by rfl⟩ : syracuseStep 163899 = 245849) B245849
theorem B557117 : Blo 163797 557117 := bstep (se 3 (by rfl) ⟨104459, by rfl⟩ : syracuseStep 557117 = 208919) B208919
theorem B163975 : Blo 163797 163975 := bstep (se 1 (by rfl) ⟨122981, by rfl⟩ : syracuseStep 163975 = 245963) B245963
theorem B163983 : Blo 163797 163983 := bstep (se 1 (by rfl) ⟨122987, by rfl⟩ : syracuseStep 163983 = 245975) B245975
theorem B164027 : Blo 163797 164027 := bstep (se 1 (by rfl) ⟨123020, by rfl⟩ : syracuseStep 164027 = 246041) B246041
theorem B164103 : Blo 163797 164103 := bstep (se 1 (by rfl) ⟨123077, by rfl⟩ : syracuseStep 164103 = 246155) B246155
theorem B262415 : Blo 163797 262415 := bstep (se 1 (by rfl) ⟨196811, by rfl⟩ : syracuseStep 262415 = 393623) B393623
theorem B164111 : Blo 163797 164111 := bstep (se 1 (by rfl) ⟨123083, by rfl⟩ : syracuseStep 164111 = 246167) B246167
theorem B164155 : Blo 163797 164155 := bstep (se 1 (by rfl) ⟨123116, by rfl⟩ : syracuseStep 164155 = 246233) B246233
theorem B164231 : Blo 163797 164231 := bstep (se 1 (by rfl) ⟨123173, by rfl⟩ : syracuseStep 164231 = 246347) B246347
theorem B164239 : Blo 163797 164239 := bstep (se 1 (by rfl) ⟨123179, by rfl⟩ : syracuseStep 164239 = 246359) B246359
theorem B164283 : Blo 163797 164283 := bstep (se 1 (by rfl) ⟨123212, by rfl⟩ : syracuseStep 164283 = 246425) B246425
theorem B164359 : Blo 163797 164359 := bstep (se 1 (by rfl) ⟨123269, by rfl⟩ : syracuseStep 164359 = 246539) B246539
theorem B164367 : Blo 163797 164367 := bstep (se 1 (by rfl) ⟨123275, by rfl⟩ : syracuseStep 164367 = 246551) B246551
theorem B164411 : Blo 163797 164411 := bstep (se 1 (by rfl) ⟨123308, by rfl⟩ : syracuseStep 164411 = 246617) B246617
theorem B393815 : Blo 163797 393815 := bstep (se 1 (by rfl) ⟨295361, by rfl⟩ : syracuseStep 393815 = 590723) B590723
theorem B164487 : Blo 163797 164487 := bstep (se 1 (by rfl) ⟨123365, by rfl⟩ : syracuseStep 164487 = 246731) B246731
theorem B197263 : Blo 163797 197263 := bstep (se 1 (by rfl) ⟨147947, by rfl⟩ : syracuseStep 197263 = 295895) B295895
theorem B164495 : Blo 163797 164495 := bstep (se 1 (by rfl) ⟨123371, by rfl⟩ : syracuseStep 164495 = 246743) B246743
theorem B164539 : Blo 163797 164539 := bstep (se 1 (by rfl) ⟨123404, by rfl⟩ : syracuseStep 164539 = 246809) B246809
theorem B590593 : Blo 163797 590593 := bstep (se 2 (by rfl) ⟨221472, by rfl⟩ : syracuseStep 590593 = 442945) B442945
theorem B164615 : Blo 163797 164615 := bstep (se 1 (by rfl) ⟨123461, by rfl⟩ : syracuseStep 164615 = 246923) B246923
theorem B164623 : Blo 163797 164623 := bstep (se 1 (by rfl) ⟨123467, by rfl⟩ : syracuseStep 164623 = 246935) B246935
theorem B164667 : Blo 163797 164667 := bstep (se 1 (by rfl) ⟨123500, by rfl⟩ : syracuseStep 164667 = 247001) B247001
theorem B164743 : Blo 163797 164743 := bstep (se 1 (by rfl) ⟨123557, by rfl⟩ : syracuseStep 164743 = 247115) B247115
theorem B164751 : Blo 163797 164751 := bstep (se 1 (by rfl) ⟨123563, by rfl⟩ : syracuseStep 164751 = 247127) B247127
theorem B164795 : Blo 163797 164795 := bstep (se 1 (by rfl) ⟨123596, by rfl⟩ : syracuseStep 164795 = 247193) B247193
theorem B361417 : Blo 163797 361417 := bstep (se 2 (by rfl) ⟨135531, by rfl⟩ : syracuseStep 361417 = 271063) B271063
theorem B164871 : Blo 163797 164871 := bstep (se 1 (by rfl) ⟨123653, by rfl⟩ : syracuseStep 164871 = 247307) B247307
theorem B164879 : Blo 163797 164879 := bstep (se 1 (by rfl) ⟨123659, by rfl⟩ : syracuseStep 164879 = 247319) B247319
theorem B623645 : Blo 163797 623645 := bstep (se 3 (by rfl) ⟨116933, by rfl⟩ : syracuseStep 623645 = 233867) B233867
theorem B623659 : Blo 163797 623659 := bstep (se 1 (by rfl) ⟨467744, by rfl⟩ : syracuseStep 623659 = 935489) B935489
theorem B164923 : Blo 163797 164923 := bstep (se 1 (by rfl) ⟨123692, by rfl⟩ : syracuseStep 164923 = 247385) B247385
theorem B164999 : Blo 163797 164999 := bstep (se 1 (by rfl) ⟨123749, by rfl⟩ : syracuseStep 164999 = 247499) B247499
theorem B165007 : Blo 163797 165007 := bstep (se 1 (by rfl) ⟨123755, by rfl⟩ : syracuseStep 165007 = 247511) B247511
theorem B165051 : Blo 163797 165051 := bstep (se 1 (by rfl) ⟨123788, by rfl⟩ : syracuseStep 165051 = 247577) B247577
theorem B165127 : Blo 163797 165127 := bstep (se 1 (by rfl) ⟨123845, by rfl⟩ : syracuseStep 165127 = 247691) B247691
theorem B165135 : Blo 163797 165135 := bstep (se 1 (by rfl) ⟨123851, by rfl⟩ : syracuseStep 165135 = 247703) B247703
theorem B165179 : Blo 163797 165179 := bstep (se 1 (by rfl) ⟨123884, by rfl⟩ : syracuseStep 165179 = 247769) B247769
theorem B165255 : Blo 163797 165255 := bstep (se 1 (by rfl) ⟨123941, by rfl⟩ : syracuseStep 165255 = 247883) B247883
theorem B165263 : Blo 163797 165263 := bstep (se 1 (by rfl) ⟨123947, by rfl⟩ : syracuseStep 165263 = 247895) B247895
theorem B558521 : Blo 163797 558521 := bstep (se 2 (by rfl) ⟨209445, by rfl⟩ : syracuseStep 558521 = 418891) B418891
theorem B165307 : Blo 163797 165307 := bstep (se 1 (by rfl) ⟨123980, by rfl⟩ : syracuseStep 165307 = 247961) B247961
theorem B165383 : Blo 163797 165383 := bstep (se 1 (by rfl) ⟨124037, by rfl⟩ : syracuseStep 165383 = 248075) B248075
theorem B165391 : Blo 163797 165391 := bstep (se 1 (by rfl) ⟨124043, by rfl⟩ : syracuseStep 165391 = 248087) B248087
theorem B1181213 : Blo 163797 1181213 := bstep (se 3 (by rfl) ⟨221477, by rfl⟩ : syracuseStep 1181213 = 442955) B442955
theorem B886301 : Blo 163797 886301 := bstep (se 3 (by rfl) ⟨166181, by rfl⟩ : syracuseStep 886301 = 332363) B332363
theorem B165435 : Blo 163797 165435 := bstep (se 1 (by rfl) ⟨124076, by rfl⟩ : syracuseStep 165435 = 248153) B248153
theorem B165511 : Blo 163797 165511 := bstep (se 1 (by rfl) ⟨124133, by rfl⟩ : syracuseStep 165511 = 248267) B248267
theorem B165519 : Blo 163797 165519 := bstep (se 1 (by rfl) ⟨124139, by rfl⟩ : syracuseStep 165519 = 248279) B248279
theorem B165563 : Blo 163797 165563 := bstep (se 1 (by rfl) ⟨124172, by rfl⟩ : syracuseStep 165563 = 248345) B248345
theorem B165639 : Blo 163797 165639 := bstep (se 1 (by rfl) ⟨124229, by rfl⟩ : syracuseStep 165639 = 248459) B248459
theorem B165647 : Blo 163797 165647 := bstep (se 1 (by rfl) ⟨124235, by rfl⟩ : syracuseStep 165647 = 248471) B248471
theorem B165691 : Blo 163797 165691 := bstep (se 1 (by rfl) ⟨124268, by rfl⟩ : syracuseStep 165691 = 248537) B248537
theorem B264055 : Blo 163797 264055 := bstep (se 1 (by rfl) ⟨198041, by rfl⟩ : syracuseStep 264055 = 396083) B396083
theorem B165767 : Blo 163797 165767 := bstep (se 1 (by rfl) ⟨124325, by rfl⟩ : syracuseStep 165767 = 248651) B248651
theorem B853895 : Blo 163797 853895 := bstep (se 1 (by rfl) ⟨640421, by rfl⟩ : syracuseStep 853895 = 1280843) B1280843
theorem B165775 : Blo 163797 165775 := bstep (se 1 (by rfl) ⟨124331, by rfl⟩ : syracuseStep 165775 = 248663) B248663
theorem B2131865 : Blo 163797 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B165819 : Blo 163797 165819 := bstep (se 1 (by rfl) ⟨124364, by rfl⟩ : syracuseStep 165819 = 248729) B248729
theorem B1607627 : Blo 163797 1607627 := bstep (se 1 (by rfl) ⟨1205720, by rfl⟩ : syracuseStep 1607627 = 2411441) B2411441
theorem B165895 : Blo 163797 165895 := bstep (se 1 (by rfl) ⟨124421, by rfl⟩ : syracuseStep 165895 = 248843) B248843
theorem B395275 : Blo 163797 395275 := bstep (se 1 (by rfl) ⟨296456, by rfl⟩ : syracuseStep 395275 = 592913) B592913
theorem B559115 : Blo 163797 559115 := bstep (se 1 (by rfl) ⟨419336, by rfl⟩ : syracuseStep 559115 = 838673) B838673
theorem B165903 : Blo 163797 165903 := bstep (se 1 (by rfl) ⟨124427, by rfl⟩ : syracuseStep 165903 = 248855) B248855
theorem B165947 : Blo 163797 165947 := bstep (se 1 (by rfl) ⟨124460, by rfl⟩ : syracuseStep 165947 = 248921) B248921
theorem B559223 : Blo 163797 559223 := bstep (se 1 (by rfl) ⟨419417, by rfl⟩ : syracuseStep 559223 = 838835) B838835
theorem B166023 : Blo 163797 166023 := bstep (se 1 (by rfl) ⟨124517, by rfl⟩ : syracuseStep 166023 = 249035) B249035
theorem B166031 : Blo 163797 166031 := bstep (se 1 (by rfl) ⟨124523, by rfl⟩ : syracuseStep 166031 = 249047) B249047
theorem B166075 : Blo 163797 166075 := bstep (se 1 (by rfl) ⟨124556, by rfl⟩ : syracuseStep 166075 = 249113) B249113
theorem B166151 : Blo 163797 166151 := bstep (se 1 (by rfl) ⟨124613, by rfl⟩ : syracuseStep 166151 = 249227) B249227
theorem B166159 : Blo 163797 166159 := bstep (se 1 (by rfl) ⟨124619, by rfl⟩ : syracuseStep 166159 = 249239) B249239
theorem B166203 : Blo 163797 166203 := bstep (se 1 (by rfl) ⟨124652, by rfl⟩ : syracuseStep 166203 = 249305) B249305
theorem B166279 : Blo 163797 166279 := bstep (se 1 (by rfl) ⟨124709, by rfl⟩ : syracuseStep 166279 = 249419) B249419
theorem B166287 : Blo 163797 166287 := bstep (se 1 (by rfl) ⟨124715, by rfl⟩ : syracuseStep 166287 = 249431) B249431
theorem B166331 : Blo 163797 166331 := bstep (se 1 (by rfl) ⟨124748, by rfl⟩ : syracuseStep 166331 = 249497) B249497
theorem B166407 : Blo 163797 166407 := bstep (se 1 (by rfl) ⟨124805, by rfl⟩ : syracuseStep 166407 = 249611) B249611
theorem B166415 : Blo 163797 166415 := bstep (se 1 (by rfl) ⟨124811, by rfl⟩ : syracuseStep 166415 = 249623) B249623
theorem B166459 : Blo 163797 166459 := bstep (se 1 (by rfl) ⟨124844, by rfl⟩ : syracuseStep 166459 = 249689) B249689
theorem B395891 : Blo 163797 395891 := bstep (se 1 (by rfl) ⟨296918, by rfl⟩ : syracuseStep 395891 = 593837) B593837
theorem B166535 : Blo 163797 166535 := bstep (se 1 (by rfl) ⟨124901, by rfl⟩ : syracuseStep 166535 = 249803) B249803
theorem B166543 : Blo 163797 166543 := bstep (se 1 (by rfl) ⟨124907, by rfl⟩ : syracuseStep 166543 = 249815) B249815
theorem B166587 : Blo 163797 166587 := bstep (se 1 (by rfl) ⟨124940, by rfl⟩ : syracuseStep 166587 = 249881) B249881
theorem B559817 : Blo 163797 559817 := bstep (se 2 (by rfl) ⟨209931, by rfl⟩ : syracuseStep 559817 = 419863) B419863
theorem B166663 : Blo 163797 166663 := bstep (se 1 (by rfl) ⟨124997, by rfl⟩ : syracuseStep 166663 = 249995) B249995
theorem B166671 : Blo 163797 166671 := bstep (se 1 (by rfl) ⟨125003, by rfl⟩ : syracuseStep 166671 = 250007) B250007
theorem B166715 : Blo 163797 166715 := bstep (se 1 (by rfl) ⟨125036, by rfl⟩ : syracuseStep 166715 = 250073) B250073
theorem B166791 : Blo 163797 166791 := bstep (se 1 (by rfl) ⟨125093, by rfl⟩ : syracuseStep 166791 = 250187) B250187
theorem B166799 : Blo 163797 166799 := bstep (se 1 (by rfl) ⟨125099, by rfl⟩ : syracuseStep 166799 = 250199) B250199
theorem B166843 : Blo 163797 166843 := bstep (se 1 (by rfl) ⟨125132, by rfl⟩ : syracuseStep 166843 = 250265) B250265
theorem B166919 : Blo 163797 166919 := bstep (se 1 (by rfl) ⟨125189, by rfl⟩ : syracuseStep 166919 = 250379) B250379
theorem B166927 : Blo 163797 166927 := bstep (se 1 (by rfl) ⟨125195, by rfl⟩ : syracuseStep 166927 = 250391) B250391
theorem B166971 : Blo 163797 166971 := bstep (se 1 (by rfl) ⟨125228, by rfl⟩ : syracuseStep 166971 = 250457) B250457
theorem B167047 : Blo 163797 167047 := bstep (se 1 (by rfl) ⟨125285, by rfl⟩ : syracuseStep 167047 = 250571) B250571
theorem B167055 : Blo 163797 167055 := bstep (se 1 (by rfl) ⟨125291, by rfl⟩ : syracuseStep 167055 = 250583) B250583
theorem B167099 : Blo 163797 167099 := bstep (se 1 (by rfl) ⟨125324, by rfl⟩ : syracuseStep 167099 = 250649) B250649
theorem B167175 : Blo 163797 167175 := bstep (se 1 (by rfl) ⟨125381, by rfl⟩ : syracuseStep 167175 = 250763) B250763
theorem B167183 : Blo 163797 167183 := bstep (se 1 (by rfl) ⟨125387, by rfl⟩ : syracuseStep 167183 = 250775) B250775
theorem B167227 : Blo 163797 167227 := bstep (se 1 (by rfl) ⟨125420, by rfl⟩ : syracuseStep 167227 = 250841) B250841
theorem B396679 : Blo 163797 396679 := bstep (se 1 (by rfl) ⟨297509, by rfl⟩ : syracuseStep 396679 = 595019) B595019
theorem B560519 : Blo 163797 560519 := bstep (se 1 (by rfl) ⟨420389, by rfl⟩ : syracuseStep 560519 = 840779) B840779
theorem B167303 : Blo 163797 167303 := bstep (se 1 (by rfl) ⟨125477, by rfl⟩ : syracuseStep 167303 = 250955) B250955
theorem B167311 : Blo 163797 167311 := bstep (se 1 (by rfl) ⟨125483, by rfl⟩ : syracuseStep 167311 = 250967) B250967
theorem B167355 : Blo 163797 167355 := bstep (se 1 (by rfl) ⟨125516, by rfl⟩ : syracuseStep 167355 = 251033) B251033
theorem B167431 : Blo 163797 167431 := bstep (se 1 (by rfl) ⟨125573, by rfl⟩ : syracuseStep 167431 = 251147) B251147
theorem B167439 : Blo 163797 167439 := bstep (se 1 (by rfl) ⟨125579, by rfl⟩ : syracuseStep 167439 = 251159) B251159
theorem B167483 : Blo 163797 167483 := bstep (se 1 (by rfl) ⟨125612, by rfl⟩ : syracuseStep 167483 = 251225) B251225
theorem B167559 : Blo 163797 167559 := bstep (se 1 (by rfl) ⟨125669, by rfl⟩ : syracuseStep 167559 = 251339) B251339
theorem B167567 : Blo 163797 167567 := bstep (se 1 (by rfl) ⟨125675, by rfl⟩ : syracuseStep 167567 = 251351) B251351
theorem B167611 : Blo 163797 167611 := bstep (se 1 (by rfl) ⟨125708, by rfl⟩ : syracuseStep 167611 = 251417) B251417
theorem B560897 : Blo 163797 560897 := bstep (se 2 (by rfl) ⟨210336, by rfl⟩ : syracuseStep 560897 = 420673) B420673
theorem B167687 : Blo 163797 167687 := bstep (se 1 (by rfl) ⟨125765, by rfl⟩ : syracuseStep 167687 = 251531) B251531
theorem B167695 : Blo 163797 167695 := bstep (se 1 (by rfl) ⟨125771, by rfl⟩ : syracuseStep 167695 = 251543) B251543
theorem B233275 : Blo 163797 233275 := bstep (se 1 (by rfl) ⟨174956, by rfl⟩ : syracuseStep 233275 = 349913) B349913
theorem B167739 : Blo 163797 167739 := bstep (se 1 (by rfl) ⟨125804, by rfl⟩ : syracuseStep 167739 = 251609) B251609
theorem B429977 : Blo 163797 429977 := bstep (se 2 (by rfl) ⟨161241, by rfl⟩ : syracuseStep 429977 = 322483) B322483
theorem B397313 : Blo 163797 397313 := bstep (se 2 (by rfl) ⟨148992, by rfl⟩ : syracuseStep 397313 = 297985) B297985
theorem B6951005 : Blo 163797 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B200891 : Blo 163797 200891 := bstep (se 1 (by rfl) ⟨150668, by rfl⟩ : syracuseStep 200891 = 301337) B301337
theorem B954625 : Blo 163797 954625 := bstep (se 2 (by rfl) ⟨357984, by rfl⟩ : syracuseStep 954625 = 715969) B715969
theorem B201079 : Blo 163797 201079 := bstep (se 1 (by rfl) ⟨150809, by rfl⟩ : syracuseStep 201079 = 301619) B301619
theorem B233975 : Blo 163797 233975 := bstep (se 1 (by rfl) ⟨175481, by rfl⟩ : syracuseStep 233975 = 350963) B350963
theorem B561707 : Blo 163797 561707 := bstep (se 1 (by rfl) ⟨421280, by rfl⟩ : syracuseStep 561707 = 842561) B842561
theorem B955151 : Blo 163797 955151 := bstep (se 1 (by rfl) ⟨716363, by rfl⟩ : syracuseStep 955151 = 1432727) B1432727
theorem B2265893 : Blo 163797 2265893 := bstep (se 4 (by rfl) ⟨212427, by rfl⟩ : syracuseStep 2265893 = 424855) B424855
theorem B267067 : Blo 163797 267067 := bstep (se 1 (by rfl) ⟨200300, by rfl⟩ : syracuseStep 267067 = 400601) B400601
theorem B857099 : Blo 163797 857099 := bstep (se 1 (by rfl) ⟨642824, by rfl⟩ : syracuseStep 857099 = 1285649) B1285649
theorem B398351 : Blo 163797 398351 := bstep (se 1 (by rfl) ⟨298763, by rfl⟩ : syracuseStep 398351 = 597527) B597527
theorem B1250477 : Blo 163797 1250477 := bstep (se 3 (by rfl) ⟨234464, by rfl⟩ : syracuseStep 1250477 = 468929) B468929
theorem B1283309 : Blo 163797 1283309 := bstep (se 3 (by rfl) ⟨240620, by rfl⟩ : syracuseStep 1283309 = 481241) B481241
theorem B563003 : Blo 163797 563003 := bstep (se 1 (by rfl) ⟨422252, by rfl⟩ : syracuseStep 563003 = 844505) B844505
theorem B1054579 : Blo 163797 1054579 := bstep (se 1 (by rfl) ⟨790934, by rfl⟩ : syracuseStep 1054579 = 1581869) B1581869
theorem B235399 : Blo 163797 235399 := bstep (se 1 (by rfl) ⟨176549, by rfl⟩ : syracuseStep 235399 = 353099) B353099
theorem B2693017 : Blo 163797 2693017 := bstep (se 2 (by rfl) ⟨1009881, by rfl⟩ : syracuseStep 2693017 = 2019763) B2019763
theorem B628823 : Blo 163797 628823 := bstep (se 1 (by rfl) ⟨471617, by rfl⟩ : syracuseStep 628823 = 943235) B943235
theorem B2398409 : Blo 163797 2398409 := bstep (se 2 (by rfl) ⟨899403, by rfl⟩ : syracuseStep 2398409 = 1798807) B1798807
theorem B563489 : Blo 163797 563489 := bstep (se 2 (by rfl) ⟨211308, by rfl⟩ : syracuseStep 563489 = 422617) B422617
theorem B891271 : Blo 163797 891271 := bstep (se 1 (by rfl) ⟨668453, by rfl⟩ : syracuseStep 891271 = 1336907) B1336907
theorem B1579409 : Blo 163797 1579409 := bstep (se 2 (by rfl) ⟨592278, by rfl⟩ : syracuseStep 1579409 = 1184557) B1184557
theorem B235963 : Blo 163797 235963 := bstep (se 1 (by rfl) ⟨176972, by rfl⟩ : syracuseStep 235963 = 353945) B353945
theorem B2660849 : Blo 163797 2660849 := bstep (se 2 (by rfl) ⟨997818, by rfl⟩ : syracuseStep 2660849 = 1995637) B1995637
theorem B629309 : Blo 163797 629309 := bstep (se 3 (by rfl) ⟨117995, by rfl⟩ : syracuseStep 629309 = 235991) B235991
theorem B531031 : Blo 163797 531031 := bstep (se 1 (by rfl) ⟨398273, by rfl⟩ : syracuseStep 531031 = 796547) B796547
theorem B400187 : Blo 163797 400187 := bstep (se 1 (by rfl) ⟨300140, by rfl⟩ : syracuseStep 400187 = 600281) B600281
theorem B1612619 : Blo 163797 1612619 := bstep (se 1 (by rfl) ⟨1209464, by rfl⟩ : syracuseStep 1612619 = 2418929) B2418929
theorem B564083 : Blo 163797 564083 := bstep (se 1 (by rfl) ⟨423062, by rfl⟩ : syracuseStep 564083 = 846125) B846125
theorem B302123 : Blo 163797 302123 := bstep (se 1 (by rfl) ⟨226592, by rfl⟩ : syracuseStep 302123 = 453185) B453185
theorem B236857 : Blo 163797 236857 := bstep (se 2 (by rfl) ⟨88821, by rfl⟩ : syracuseStep 236857 = 177643) B177643
theorem B2825603 : Blo 163797 2825603 := bstep (se 1 (by rfl) ⟨2119202, by rfl⟩ : syracuseStep 2825603 = 4238405) B4238405
theorem B826891 : Blo 163797 826891 := bstep (se 1 (by rfl) ⟨620168, by rfl⟩ : syracuseStep 826891 = 1240337) B1240337
theorem B4038173 : Blo 163797 4038173 := bstep (se 3 (by rfl) ⟨757157, by rfl⟩ : syracuseStep 4038173 = 1514315) B1514315
theorem B1252907 : Blo 163797 1252907 := bstep (se 1 (by rfl) ⟨939680, by rfl⟩ : syracuseStep 1252907 = 1879361) B1879361
theorem B1056527 : Blo 163797 1056527 := bstep (se 1 (by rfl) ⟨792395, by rfl⟩ : syracuseStep 1056527 = 1584791) B1584791
theorem B466823 : Blo 163797 466823 := bstep (se 1 (by rfl) ⟨350117, by rfl⟩ : syracuseStep 466823 = 700235) B700235
theorem B368585 : Blo 163797 368585 := bstep (se 2 (by rfl) ⟨138219, by rfl⟩ : syracuseStep 368585 = 276439) B276439
theorem B630737 : Blo 163797 630737 := bstep (se 2 (by rfl) ⟨236526, by rfl⟩ : syracuseStep 630737 = 473053) B473053
theorem B467005 : Blo 163797 467005 := bstep (se 3 (by rfl) ⟨87563, by rfl⟩ : syracuseStep 467005 = 175127) B175127
theorem B401543 : Blo 163797 401543 := bstep (se 1 (by rfl) ⟨301157, by rfl⟩ : syracuseStep 401543 = 602315) B602315
theorem B1876445 : Blo 163797 1876445 := bstep (se 3 (by rfl) ⟨351833, by rfl⟩ : syracuseStep 1876445 = 703667) B703667
theorem B238087 : Blo 163797 238087 := bstep (se 1 (by rfl) ⟨178565, by rfl⟩ : syracuseStep 238087 = 357131) B357131
theorem B467471 : Blo 163797 467471 := bstep (se 1 (by rfl) ⟨350603, by rfl⟩ : syracuseStep 467471 = 701207) B701207
theorem B795203 : Blo 163797 795203 := bstep (se 1 (by rfl) ⟨596402, by rfl⟩ : syracuseStep 795203 = 1192805) B1192805
theorem B369287 : Blo 163797 369287 := bstep (se 1 (by rfl) ⟨276965, by rfl⟩ : syracuseStep 369287 = 553931) B553931
theorem B2794201 : Blo 163797 2794201 := bstep (se 2 (by rfl) ⟨1047825, by rfl⟩ : syracuseStep 2794201 = 2095651) B2095651
theorem B369467 : Blo 163797 369467 := bstep (se 1 (by rfl) ⟨277100, by rfl⟩ : syracuseStep 369467 = 554201) B554201
theorem B369593 : Blo 163797 369593 := bstep (se 2 (by rfl) ⟨138597, by rfl⟩ : syracuseStep 369593 = 277195) B277195
theorem B1778699 : Blo 163797 1778699 := bstep (se 1 (by rfl) ⟨1334024, by rfl⟩ : syracuseStep 1778699 = 2668049) B2668049
theorem B238793 : Blo 163797 238793 := bstep (se 2 (by rfl) ⟨89547, by rfl⟩ : syracuseStep 238793 = 179095) B179095
theorem B369935 : Blo 163797 369935 := bstep (se 1 (by rfl) ⟨277451, by rfl⟩ : syracuseStep 369935 = 554903) B554903
theorem B369953 : Blo 163797 369953 := bstep (se 2 (by rfl) ⟨138732, by rfl⟩ : syracuseStep 369953 = 277465) B277465
theorem B238907 : Blo 163797 238907 := bstep (se 1 (by rfl) ⟨179180, by rfl⟩ : syracuseStep 238907 = 358361) B358361
theorem B664985 : Blo 163797 664985 := bstep (se 2 (by rfl) ⟨249369, by rfl⟩ : syracuseStep 664985 = 498739) B498739
theorem B632407 : Blo 163797 632407 := bstep (se 1 (by rfl) ⟨474305, by rfl⟩ : syracuseStep 632407 = 948611) B948611
theorem B370295 : Blo 163797 370295 := bstep (se 1 (by rfl) ⟨277721, by rfl⟩ : syracuseStep 370295 = 555443) B555443
theorem B468737 : Blo 163797 468737 := bstep (se 2 (by rfl) ⟨175776, by rfl⟩ : syracuseStep 468737 = 351553) B351553
theorem B370475 : Blo 163797 370475 := bstep (se 1 (by rfl) ⟨277856, by rfl⟩ : syracuseStep 370475 = 555713) B555713
theorem B26388341 : Blo 163797 26388341 := bstep (se 5 (by rfl) ⟨1236953, by rfl⟩ : syracuseStep 26388341 = 2473907) B2473907
theorem B501623 : Blo 163797 501623 := bstep (se 1 (by rfl) ⟨376217, by rfl⟩ : syracuseStep 501623 = 752435) B752435
theorem B632711 : Blo 163797 632711 := bstep (se 1 (by rfl) ⟨474533, by rfl⟩ : syracuseStep 632711 = 949067) B949067
theorem B894905 : Blo 163797 894905 := bstep (se 2 (by rfl) ⟨335589, by rfl⟩ : syracuseStep 894905 = 671179) B671179
theorem B632893 : Blo 163797 632893 := bstep (se 3 (by rfl) ⟨118667, by rfl⟩ : syracuseStep 632893 = 237335) B237335
theorem B370835 : Blo 163797 370835 := bstep (se 1 (by rfl) ⟨278126, by rfl⟩ : syracuseStep 370835 = 556253) B556253
theorem B370889 : Blo 163797 370889 := bstep (se 2 (by rfl) ⟨139083, by rfl⟩ : syracuseStep 370889 = 278167) B278167
theorem B305353 : Blo 163797 305353 := bstep (se 2 (by rfl) ⟨114507, by rfl⟩ : syracuseStep 305353 = 229015) B229015
theorem B207623 : Blo 163797 207623 := bstep (se 1 (by rfl) ⟨155717, by rfl⟩ : syracuseStep 207623 = 311435) B311435
theorem B371591 : Blo 163797 371591 := bstep (se 1 (by rfl) ⟨278693, by rfl⟩ : syracuseStep 371591 = 557387) B557387
theorem B830411 : Blo 163797 830411 := bstep (se 1 (by rfl) ⟨622808, by rfl⟩ : syracuseStep 830411 = 1245617) B1245617
theorem B371771 : Blo 163797 371771 := bstep (se 1 (by rfl) ⟨278828, by rfl⟩ : syracuseStep 371771 = 557657) B557657
theorem B371897 : Blo 163797 371897 := bstep (se 2 (by rfl) ⟨139461, by rfl⟩ : syracuseStep 371897 = 278923) B278923
theorem B830735 : Blo 163797 830735 := bstep (se 1 (by rfl) ⟨623051, by rfl⟩ : syracuseStep 830735 = 1246103) B1246103
theorem B470387 : Blo 163797 470387 := bstep (se 1 (by rfl) ⟨352790, by rfl⟩ : syracuseStep 470387 = 705581) B705581
theorem B208271 : Blo 163797 208271 := bstep (se 1 (by rfl) ⟨156203, by rfl⟩ : syracuseStep 208271 = 312407) B312407
theorem B339385 : Blo 163797 339385 := bstep (se 2 (by rfl) ⟨127269, by rfl⟩ : syracuseStep 339385 = 254539) B254539
theorem B372239 : Blo 163797 372239 := bstep (se 1 (by rfl) ⟨279179, by rfl⟩ : syracuseStep 372239 = 558359) B558359
theorem B372257 : Blo 163797 372257 := bstep (se 2 (by rfl) ⟨139596, by rfl⟩ : syracuseStep 372257 = 279193) B279193
theorem B634625 : Blo 163797 634625 := bstep (se 2 (by rfl) ⟨237984, by rfl⟩ : syracuseStep 634625 = 475969) B475969
theorem B175879 : Blo 163797 175879 := bstep (se 1 (by rfl) ⟨131909, by rfl⟩ : syracuseStep 175879 = 263819) B263819
theorem B470843 : Blo 163797 470843 := bstep (se 1 (by rfl) ⟨353132, by rfl⟩ : syracuseStep 470843 = 706265) B706265
theorem B372599 : Blo 163797 372599 := bstep (se 1 (by rfl) ⟨279449, by rfl⟩ : syracuseStep 372599 = 558899) B558899
theorem B372779 : Blo 163797 372779 := bstep (se 1 (by rfl) ⟨279584, by rfl⟩ : syracuseStep 372779 = 559169) B559169
theorem B798893 : Blo 163797 798893 := bstep (se 3 (by rfl) ⟨149792, by rfl⟩ : syracuseStep 798893 = 299585) B299585
theorem B503993 : Blo 163797 503993 := bstep (se 2 (by rfl) ⟨188997, by rfl⟩ : syracuseStep 503993 = 377995) B377995
theorem B373139 : Blo 163797 373139 := bstep (se 1 (by rfl) ⟨279854, by rfl⟩ : syracuseStep 373139 = 559709) B559709
theorem B3322259 : Blo 163797 3322259 := bstep (se 1 (by rfl) ⟨2491694, by rfl⟩ : syracuseStep 3322259 = 4983389) B4983389
theorem B373193 : Blo 163797 373193 := bstep (se 2 (by rfl) ⟨139947, by rfl⟩ : syracuseStep 373193 = 279895) B279895
theorem B635435 : Blo 163797 635435 := bstep (se 1 (by rfl) ⟨476576, by rfl⟩ : syracuseStep 635435 = 953153) B953153
theorem B471595 : Blo 163797 471595 := bstep (se 1 (by rfl) ⟨353696, by rfl⟩ : syracuseStep 471595 = 707393) B707393
theorem B537131 : Blo 163797 537131 := bstep (se 1 (by rfl) ⟨402848, by rfl⟩ : syracuseStep 537131 = 805697) B805697
theorem B176699 : Blo 163797 176699 := bstep (se 1 (by rfl) ⟨132524, by rfl⟩ : syracuseStep 176699 = 265049) B265049
theorem B832193 : Blo 163797 832193 := bstep (se 2 (by rfl) ⟨312072, by rfl⟩ : syracuseStep 832193 = 624145) B624145
theorem B701243 : Blo 163797 701243 := bstep (se 1 (by rfl) ⟨525932, by rfl⟩ : syracuseStep 701243 = 1051865) B1051865
theorem B471869 : Blo 163797 471869 := bstep (se 3 (by rfl) ⟨88475, by rfl⟩ : syracuseStep 471869 = 176951) B176951
theorem B537479 : Blo 163797 537479 := bstep (se 1 (by rfl) ⟨403109, by rfl⟩ : syracuseStep 537479 = 806219) B806219
theorem B635795 : Blo 163797 635795 := bstep (se 1 (by rfl) ⟨476846, by rfl⟩ : syracuseStep 635795 = 953693) B953693
theorem B668569 : Blo 163797 668569 := bstep (se 2 (by rfl) ⟨250713, by rfl⟩ : syracuseStep 668569 = 501427) B501427
theorem B504967 : Blo 163797 504967 := bstep (se 1 (by rfl) ⟨378725, by rfl⟩ : syracuseStep 504967 = 757451) B757451
theorem B373895 : Blo 163797 373895 := bstep (se 1 (by rfl) ⟨280421, by rfl⟩ : syracuseStep 373895 = 560843) B560843
theorem B603407 : Blo 163797 603407 := bstep (se 1 (by rfl) ⟨452555, by rfl⟩ : syracuseStep 603407 = 905111) B905111
theorem B374075 : Blo 163797 374075 := bstep (se 1 (by rfl) ⟨280556, by rfl⟩ : syracuseStep 374075 = 561113) B561113
theorem B636295 : Blo 163797 636295 := bstep (se 1 (by rfl) ⟨477221, by rfl⟩ : syracuseStep 636295 = 954443) B954443
theorem B374201 : Blo 163797 374201 := bstep (se 2 (by rfl) ⟨140325, by rfl⟩ : syracuseStep 374201 = 280651) B280651
theorem B472711 : Blo 163797 472711 := bstep (se 1 (by rfl) ⟨354533, by rfl⟩ : syracuseStep 472711 = 709067) B709067
theorem B374543 : Blo 163797 374543 := bstep (se 1 (by rfl) ⟨280907, by rfl⟩ : syracuseStep 374543 = 561815) B561815
theorem B374561 : Blo 163797 374561 := bstep (se 2 (by rfl) ⟨140460, by rfl⟩ : syracuseStep 374561 = 280921) B280921
theorem B800545 : Blo 163797 800545 := bstep (se 2 (by rfl) ⟨300204, by rfl⟩ : syracuseStep 800545 = 600409) B600409
theorem B472985 : Blo 163797 472985 := bstep (se 2 (by rfl) ⟨177369, by rfl⟩ : syracuseStep 472985 = 354739) B354739
theorem B833489 : Blo 163797 833489 := bstep (se 2 (by rfl) ⟨312558, by rfl⟩ : syracuseStep 833489 = 625117) B625117
theorem B374903 : Blo 163797 374903 := bstep (se 1 (by rfl) ⟨281177, by rfl⟩ : syracuseStep 374903 = 562355) B562355
theorem B1620101 : Blo 163797 1620101 := bstep (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) B303769
theorem B375083 : Blo 163797 375083 := bstep (se 1 (by rfl) ⟨281312, by rfl⟩ : syracuseStep 375083 = 562625) B562625
theorem B211243 : Blo 163797 211243 := bstep (se 1 (by rfl) ⟨158432, by rfl⟩ : syracuseStep 211243 = 316865) B316865
theorem B276871 : Blo 163797 276871 := bstep (se 1 (by rfl) ⟨207653, by rfl⟩ : syracuseStep 276871 = 415307) B415307
theorem B703019 : Blo 163797 703019 := bstep (se 1 (by rfl) ⟨527264, by rfl⟩ : syracuseStep 703019 = 1054529) B1054529
theorem B375443 : Blo 163797 375443 := bstep (se 1 (by rfl) ⟨281582, by rfl⟩ : syracuseStep 375443 = 563165) B563165
theorem B375497 : Blo 163797 375497 := bstep (se 2 (by rfl) ⟨140811, by rfl⟩ : syracuseStep 375497 = 281623) B281623
theorem B474113 : Blo 163797 474113 := bstep (se 2 (by rfl) ⟨177792, by rfl⟩ : syracuseStep 474113 = 355585) B355585
theorem B277519 : Blo 163797 277519 := bstep (se 1 (by rfl) ⟨208139, by rfl⟩ : syracuseStep 277519 = 416279) B416279
theorem B212215 : Blo 163797 212215 := bstep (se 1 (by rfl) ⟨159161, by rfl⟩ : syracuseStep 212215 = 318323) B318323
theorem B507179 : Blo 163797 507179 := bstep (se 1 (by rfl) ⟨380384, by rfl⟩ : syracuseStep 507179 = 760769) B760769
theorem B507197 : Blo 163797 507197 := bstep (se 3 (by rfl) ⟨95099, by rfl⟩ : syracuseStep 507197 = 190199) B190199
theorem B376199 : Blo 163797 376199 := bstep (se 1 (by rfl) ⟨282149, by rfl⟩ : syracuseStep 376199 = 564299) B564299
theorem B474569 : Blo 163797 474569 := bstep (se 2 (by rfl) ⟨177963, by rfl⟩ : syracuseStep 474569 = 355927) B355927
theorem B1818065 : Blo 163797 1818065 := bstep (se 2 (by rfl) ⟨681774, by rfl⟩ : syracuseStep 1818065 = 1363549) B1363549
theorem B278059 : Blo 163797 278059 := bstep (se 1 (by rfl) ⟨208544, by rfl⟩ : syracuseStep 278059 = 417089) B417089
theorem B376379 : Blo 163797 376379 := bstep (se 1 (by rfl) ⟨282284, by rfl⟩ : syracuseStep 376379 = 564569) B564569
theorem B278201 : Blo 163797 278201 := bstep (se 2 (by rfl) ⟨104325, by rfl⟩ : syracuseStep 278201 = 208651) B208651
theorem B376505 : Blo 163797 376505 := bstep (se 2 (by rfl) ⟨141189, by rfl⟩ : syracuseStep 376505 = 282379) B282379
theorem B245705 : Blo 163797 245705 := bstep (se 2 (by rfl) ⟨92139, by rfl⟩ : syracuseStep 245705 = 184279) B184279
theorem B999377 : Blo 163797 999377 := bstep (se 2 (by rfl) ⟨374766, by rfl⟩ : syracuseStep 999377 = 749533) B749533
theorem B835595 : Blo 163797 835595 := bstep (se 1 (by rfl) ⟨626696, by rfl⟩ : syracuseStep 835595 = 1253393) B1253393
theorem B376847 : Blo 163797 376847 := bstep (se 1 (by rfl) ⟨282635, by rfl⟩ : syracuseStep 376847 = 565271) B565271
theorem B376865 : Blo 163797 376865 := bstep (se 2 (by rfl) ⟨141324, by rfl⟩ : syracuseStep 376865 = 282649) B282649
theorem B245819 : Blo 163797 245819 := bstep (se 1 (by rfl) ⟨184364, by rfl⟩ : syracuseStep 245819 = 368729) B368729
theorem B1261655 : Blo 163797 1261655 := bstep (se 1 (by rfl) ⟨946241, by rfl⟩ : syracuseStep 1261655 = 1892483) B1892483
theorem B245879 : Blo 163797 245879 := bstep (se 1 (by rfl) ⟨184409, by rfl⟩ : syracuseStep 245879 = 368819) B368819
theorem B245903 : Blo 163797 245903 := bstep (se 1 (by rfl) ⟨184427, by rfl⟩ : syracuseStep 245903 = 368855) B368855
theorem B835757 : Blo 163797 835757 := bstep (se 3 (by rfl) ⟨156704, by rfl⟩ : syracuseStep 835757 = 313409) B313409
theorem B245945 : Blo 163797 245945 := bstep (se 2 (by rfl) ⟨92229, by rfl⟩ : syracuseStep 245945 = 184459) B184459
theorem B246023 : Blo 163797 246023 := bstep (se 1 (by rfl) ⟨184517, by rfl⟩ : syracuseStep 246023 = 369035) B369035
theorem B246059 : Blo 163797 246059 := bstep (se 1 (by rfl) ⟨184544, by rfl⟩ : syracuseStep 246059 = 369089) B369089
theorem B246089 : Blo 163797 246089 := bstep (se 2 (by rfl) ⟨92283, by rfl⟩ : syracuseStep 246089 = 184567) B184567
theorem B278903 : Blo 163797 278903 := bstep (se 1 (by rfl) ⟨209177, by rfl⟩ : syracuseStep 278903 = 418355) B418355
theorem B377207 : Blo 163797 377207 := bstep (se 1 (by rfl) ⟨282905, by rfl⟩ : syracuseStep 377207 = 565811) B565811
theorem B2474387 : Blo 163797 2474387 := bstep (se 1 (by rfl) ⟨1855790, by rfl⟩ : syracuseStep 2474387 = 3711581) B3711581
theorem B901523 : Blo 163797 901523 := bstep (se 1 (by rfl) ⟨676142, by rfl⟩ : syracuseStep 901523 = 1352285) B1352285
theorem B246203 : Blo 163797 246203 := bstep (se 1 (by rfl) ⟨184652, by rfl⟩ : syracuseStep 246203 = 369305) B369305
theorem B246263 : Blo 163797 246263 := bstep (se 1 (by rfl) ⟨184697, by rfl⟩ : syracuseStep 246263 = 369395) B369395
theorem B246287 : Blo 163797 246287 := bstep (se 1 (by rfl) ⟨184715, by rfl⟩ : syracuseStep 246287 = 369431) B369431
theorem B377387 : Blo 163797 377387 := bstep (se 1 (by rfl) ⟨283040, by rfl⟩ : syracuseStep 377387 = 566081) B566081
theorem B246329 : Blo 163797 246329 := bstep (se 2 (by rfl) ⟨92373, by rfl⟩ : syracuseStep 246329 = 184747) B184747
theorem B934487 : Blo 163797 934487 := bstep (se 1 (by rfl) ⟨700865, by rfl⟩ : syracuseStep 934487 = 1401731) B1401731
theorem B442999 : Blo 163797 442999 := bstep (se 1 (by rfl) ⟨332249, by rfl⟩ : syracuseStep 442999 = 664499) B664499
theorem B246407 : Blo 163797 246407 := bstep (se 1 (by rfl) ⟨184805, by rfl⟩ : syracuseStep 246407 = 369611) B369611
theorem B246443 : Blo 163797 246443 := bstep (se 1 (by rfl) ⟨184832, by rfl⟩ : syracuseStep 246443 = 369665) B369665
theorem B443065 : Blo 163797 443065 := bstep (se 2 (by rfl) ⟨166149, by rfl⟩ : syracuseStep 443065 = 332299) B332299
theorem B246473 : Blo 163797 246473 := bstep (se 2 (by rfl) ⟨92427, by rfl⟩ : syracuseStep 246473 = 184855) B184855
theorem B2147087 : Blo 163797 2147087 := bstep (se 1 (by rfl) ⟨1610315, by rfl⟩ : syracuseStep 2147087 = 3220631) B3220631
theorem B246587 : Blo 163797 246587 := bstep (se 1 (by rfl) ⟨184940, by rfl⟩ : syracuseStep 246587 = 369881) B369881
theorem B279355 : Blo 163797 279355 := bstep (se 1 (by rfl) ⟨209516, by rfl⟩ : syracuseStep 279355 = 419033) B419033
theorem B246647 : Blo 163797 246647 := bstep (se 1 (by rfl) ⟨184985, by rfl⟩ : syracuseStep 246647 = 369971) B369971
theorem B246671 : Blo 163797 246671 := bstep (se 1 (by rfl) ⟨185003, by rfl⟩ : syracuseStep 246671 = 370007) B370007
theorem B1000345 : Blo 163797 1000345 := bstep (se 2 (by rfl) ⟨375129, by rfl⟩ : syracuseStep 1000345 = 750259) B750259
theorem B246713 : Blo 163797 246713 := bstep (se 2 (by rfl) ⟨92517, by rfl⟩ : syracuseStep 246713 = 185035) B185035
theorem B279497 : Blo 163797 279497 := bstep (se 2 (by rfl) ⟨104811, by rfl⟩ : syracuseStep 279497 = 209623) B209623
theorem B246791 : Blo 163797 246791 := bstep (se 1 (by rfl) ⟨185093, by rfl⟩ : syracuseStep 246791 = 370187) B370187
theorem B246827 : Blo 163797 246827 := bstep (se 1 (by rfl) ⟨185120, by rfl⟩ : syracuseStep 246827 = 370241) B370241
theorem B476219 : Blo 163797 476219 := bstep (se 1 (by rfl) ⟨357164, by rfl⟩ : syracuseStep 476219 = 714329) B714329
theorem B246857 : Blo 163797 246857 := bstep (se 2 (by rfl) ⟨92571, by rfl⟩ : syracuseStep 246857 = 185143) B185143
theorem B2114693 : Blo 163797 2114693 := bstep (se 4 (by rfl) ⟨198252, by rfl⟩ : syracuseStep 2114693 = 396505) B396505
theorem B246971 : Blo 163797 246971 := bstep (se 1 (by rfl) ⟨185228, by rfl⟩ : syracuseStep 246971 = 370457) B370457
theorem B2409709 : Blo 163797 2409709 := bstep (se 3 (by rfl) ⟨451820, by rfl⟩ : syracuseStep 2409709 = 903641) B903641
theorem B247031 : Blo 163797 247031 := bstep (se 1 (by rfl) ⟨185273, by rfl⟩ : syracuseStep 247031 = 370547) B370547
theorem B247055 : Blo 163797 247055 := bstep (se 1 (by rfl) ⟨185291, by rfl⟩ : syracuseStep 247055 = 370583) B370583
theorem B247097 : Blo 163797 247097 := bstep (se 2 (by rfl) ⟨92661, by rfl⟩ : syracuseStep 247097 = 185323) B185323
theorem B312635 : Blo 163797 312635 := bstep (se 1 (by rfl) ⟨234476, by rfl⟩ : syracuseStep 312635 = 468953) B468953
theorem B247175 : Blo 163797 247175 := bstep (se 1 (by rfl) ⟨185381, by rfl⟩ : syracuseStep 247175 = 370763) B370763
theorem B247211 : Blo 163797 247211 := bstep (se 1 (by rfl) ⟨185408, by rfl⟩ : syracuseStep 247211 = 370817) B370817
theorem B247241 : Blo 163797 247241 := bstep (se 2 (by rfl) ⟨92715, by rfl⟩ : syracuseStep 247241 = 185431) B185431
theorem B476705 : Blo 163797 476705 := bstep (se 2 (by rfl) ⟨178764, by rfl⟩ : syracuseStep 476705 = 357529) B357529
theorem B247355 : Blo 163797 247355 := bstep (se 1 (by rfl) ⟨185516, by rfl⟩ : syracuseStep 247355 = 371033) B371033
theorem B247415 : Blo 163797 247415 := bstep (se 1 (by rfl) ⟨185561, by rfl⟩ : syracuseStep 247415 = 371123) B371123
theorem B280199 : Blo 163797 280199 := bstep (se 1 (by rfl) ⟨210149, by rfl⟩ : syracuseStep 280199 = 420299) B420299
theorem B247439 : Blo 163797 247439 := bstep (se 1 (by rfl) ⟨185579, by rfl⟩ : syracuseStep 247439 = 371159) B371159
theorem B247481 : Blo 163797 247481 := bstep (se 2 (by rfl) ⟨92805, by rfl⟩ : syracuseStep 247481 = 185611) B185611
theorem B378553 : Blo 163797 378553 := bstep (se 2 (by rfl) ⟨141957, by rfl⟩ : syracuseStep 378553 = 283915) B283915
theorem B476857 : Blo 163797 476857 := bstep (se 2 (by rfl) ⟨178821, by rfl⟩ : syracuseStep 476857 = 357643) B357643
theorem B837377 : Blo 163797 837377 := bstep (se 2 (by rfl) ⟨314016, by rfl⟩ : syracuseStep 837377 = 628033) B628033
theorem B247559 : Blo 163797 247559 := bstep (se 1 (by rfl) ⟨185669, by rfl⟩ : syracuseStep 247559 = 371339) B371339
theorem B313121 : Blo 163797 313121 := bstep (se 2 (by rfl) ⟨117420, by rfl⟩ : syracuseStep 313121 = 234841) B234841
theorem B247595 : Blo 163797 247595 := bstep (se 1 (by rfl) ⟨185696, by rfl⟩ : syracuseStep 247595 = 371393) B371393
theorem B247625 : Blo 163797 247625 := bstep (se 2 (by rfl) ⟨92859, by rfl⟩ : syracuseStep 247625 = 185719) B185719
theorem B247739 : Blo 163797 247739 := bstep (se 1 (by rfl) ⟨185804, by rfl⟩ : syracuseStep 247739 = 371609) B371609
theorem B247799 : Blo 163797 247799 := bstep (se 1 (by rfl) ⟨185849, by rfl⟩ : syracuseStep 247799 = 371699) B371699
theorem B247823 : Blo 163797 247823 := bstep (se 1 (by rfl) ⟨185867, by rfl⟩ : syracuseStep 247823 = 371735) B371735
theorem B247865 : Blo 163797 247865 := bstep (se 2 (by rfl) ⟨92949, by rfl⟩ : syracuseStep 247865 = 185899) B185899
theorem B477245 : Blo 163797 477245 := bstep (se 3 (by rfl) ⟨89483, by rfl⟩ : syracuseStep 477245 = 178967) B178967
theorem B444503 : Blo 163797 444503 := bstep (se 1 (by rfl) ⟨333377, by rfl⟩ : syracuseStep 444503 = 666755) B666755
theorem B313463 : Blo 163797 313463 := bstep (se 1 (by rfl) ⟨235097, by rfl⟩ : syracuseStep 313463 = 470195) B470195
theorem B247943 : Blo 163797 247943 := bstep (se 1 (by rfl) ⟨185957, by rfl⟩ : syracuseStep 247943 = 371915) B371915
theorem B247979 : Blo 163797 247979 := bstep (se 1 (by rfl) ⟨185984, by rfl⟩ : syracuseStep 247979 = 371969) B371969
theorem B248009 : Blo 163797 248009 := bstep (se 2 (by rfl) ⟨93003, by rfl⟩ : syracuseStep 248009 = 186007) B186007
theorem B280847 : Blo 163797 280847 := bstep (se 1 (by rfl) ⟨210635, by rfl⟩ : syracuseStep 280847 = 421271) B421271
theorem B248123 : Blo 163797 248123 := bstep (se 1 (by rfl) ⟨186092, by rfl⟩ : syracuseStep 248123 = 372185) B372185
theorem B248183 : Blo 163797 248183 := bstep (se 1 (by rfl) ⟨186137, by rfl⟩ : syracuseStep 248183 = 372275) B372275
theorem B248207 : Blo 163797 248207 := bstep (se 1 (by rfl) ⟨186155, by rfl⟩ : syracuseStep 248207 = 372311) B372311
theorem B1067411 : Blo 163797 1067411 := bstep (se 1 (by rfl) ⟨800558, by rfl⟩ : syracuseStep 1067411 = 1601117) B1601117
theorem B248249 : Blo 163797 248249 := bstep (se 2 (by rfl) ⟨93093, by rfl⟩ : syracuseStep 248249 = 186187) B186187
theorem B248327 : Blo 163797 248327 := bstep (se 1 (by rfl) ⟨186245, by rfl⟩ : syracuseStep 248327 = 372491) B372491
theorem B838187 : Blo 163797 838187 := bstep (se 1 (by rfl) ⟨628640, by rfl⟩ : syracuseStep 838187 = 1257281) B1257281
theorem B248363 : Blo 163797 248363 := bstep (se 1 (by rfl) ⟨186272, by rfl⟩ : syracuseStep 248363 = 372545) B372545
theorem B248393 : Blo 163797 248393 := bstep (se 2 (by rfl) ⟨93147, by rfl⟩ : syracuseStep 248393 = 186295) B186295
theorem B674423 : Blo 163797 674423 := bstep (se 1 (by rfl) ⟨505817, by rfl⟩ : syracuseStep 674423 = 1011635) B1011635
theorem B248507 : Blo 163797 248507 := bstep (se 1 (by rfl) ⟨186380, by rfl⟩ : syracuseStep 248507 = 372761) B372761
theorem B903881 : Blo 163797 903881 := bstep (se 2 (by rfl) ⟨338955, by rfl⟩ : syracuseStep 903881 = 677911) B677911
theorem B248567 : Blo 163797 248567 := bstep (se 1 (by rfl) ⟨186425, by rfl⟩ : syracuseStep 248567 = 372851) B372851
theorem B248591 : Blo 163797 248591 := bstep (se 1 (by rfl) ⟨186443, by rfl⟩ : syracuseStep 248591 = 372887) B372887
theorem B281387 : Blo 163797 281387 := bstep (se 1 (by rfl) ⟨211040, by rfl⟩ : syracuseStep 281387 = 422081) B422081
theorem B248633 : Blo 163797 248633 := bstep (se 2 (by rfl) ⟨93237, by rfl⟩ : syracuseStep 248633 = 186475) B186475
theorem B248711 : Blo 163797 248711 := bstep (se 1 (by rfl) ⟨186533, by rfl⟩ : syracuseStep 248711 = 373067) B373067
theorem B248747 : Blo 163797 248747 := bstep (se 1 (by rfl) ⟨186560, by rfl⟩ : syracuseStep 248747 = 373121) B373121
theorem B904121 : Blo 163797 904121 := bstep (se 2 (by rfl) ⟨339045, by rfl⟩ : syracuseStep 904121 = 678091) B678091
theorem B248777 : Blo 163797 248777 := bstep (se 2 (by rfl) ⟨93291, by rfl⟩ : syracuseStep 248777 = 186583) B186583
theorem B281615 : Blo 163797 281615 := bstep (se 1 (by rfl) ⟨211211, by rfl⟩ : syracuseStep 281615 = 422423) B422423
theorem B248891 : Blo 163797 248891 := bstep (se 1 (by rfl) ⟨186668, by rfl⟩ : syracuseStep 248891 = 373337) B373337
theorem B248951 : Blo 163797 248951 := bstep (se 1 (by rfl) ⟨186713, by rfl⟩ : syracuseStep 248951 = 373427) B373427
theorem B248975 : Blo 163797 248975 := bstep (se 1 (by rfl) ⟨186731, by rfl⟩ : syracuseStep 248975 = 373463) B373463
theorem B249017 : Blo 163797 249017 := bstep (se 2 (by rfl) ⟨93381, by rfl⟩ : syracuseStep 249017 = 186763) B186763
theorem B281785 : Blo 163797 281785 := bstep (se 2 (by rfl) ⟨105669, by rfl⟩ : syracuseStep 281785 = 211339) B211339
theorem B249095 : Blo 163797 249095 := bstep (se 1 (by rfl) ⟨186821, by rfl⟩ : syracuseStep 249095 = 373643) B373643
theorem B249131 : Blo 163797 249131 := bstep (se 1 (by rfl) ⟨186848, by rfl⟩ : syracuseStep 249131 = 373697) B373697
theorem B249161 : Blo 163797 249161 := bstep (se 2 (by rfl) ⟨93435, by rfl⟩ : syracuseStep 249161 = 186871) B186871
theorem B249275 : Blo 163797 249275 := bstep (se 1 (by rfl) ⟨186956, by rfl⟩ : syracuseStep 249275 = 373913) B373913
theorem B249335 : Blo 163797 249335 := bstep (se 1 (by rfl) ⟨187001, by rfl⟩ : syracuseStep 249335 = 374003) B374003
theorem B249359 : Blo 163797 249359 := bstep (se 1 (by rfl) ⟨187019, by rfl⟩ : syracuseStep 249359 = 374039) B374039
theorem B249401 : Blo 163797 249401 := bstep (se 2 (by rfl) ⟨93525, by rfl⟩ : syracuseStep 249401 = 187051) B187051
theorem B904765 : Blo 163797 904765 := bstep (se 3 (by rfl) ⟨169643, by rfl⟩ : syracuseStep 904765 = 339287) B339287
theorem B249479 : Blo 163797 249479 := bstep (se 1 (by rfl) ⟨187109, by rfl⟩ : syracuseStep 249479 = 374219) B374219
theorem B249515 : Blo 163797 249515 := bstep (se 1 (by rfl) ⟨187136, by rfl⟩ : syracuseStep 249515 = 374273) B374273
theorem B315065 : Blo 163797 315065 := bstep (se 2 (by rfl) ⟨118149, by rfl⟩ : syracuseStep 315065 = 236299) B236299
theorem B249545 : Blo 163797 249545 := bstep (se 2 (by rfl) ⟨93579, by rfl⟩ : syracuseStep 249545 = 187159) B187159
theorem B839483 : Blo 163797 839483 := bstep (se 1 (by rfl) ⟨629612, by rfl⟩ : syracuseStep 839483 = 1259225) B1259225
theorem B249659 : Blo 163797 249659 := bstep (se 1 (by rfl) ⟨187244, by rfl⟩ : syracuseStep 249659 = 374489) B374489
theorem B249719 : Blo 163797 249719 := bstep (se 1 (by rfl) ⟨187289, by rfl⟩ : syracuseStep 249719 = 374579) B374579
theorem B282487 : Blo 163797 282487 := bstep (se 1 (by rfl) ⟨211865, by rfl⟩ : syracuseStep 282487 = 423731) B423731
theorem B249743 : Blo 163797 249743 := bstep (se 1 (by rfl) ⟨187307, by rfl⟩ : syracuseStep 249743 = 374615) B374615
theorem B249785 : Blo 163797 249785 := bstep (se 2 (by rfl) ⟨93669, by rfl⟩ : syracuseStep 249785 = 187339) B187339
theorem B839645 : Blo 163797 839645 := bstep (se 3 (by rfl) ⟨157433, by rfl⟩ : syracuseStep 839645 = 314867) B314867
theorem B249863 : Blo 163797 249863 := bstep (se 1 (by rfl) ⟨187397, by rfl⟩ : syracuseStep 249863 = 374795) B374795
theorem B315407 : Blo 163797 315407 := bstep (se 1 (by rfl) ⟨236555, by rfl⟩ : syracuseStep 315407 = 473111) B473111
theorem B249899 : Blo 163797 249899 := bstep (se 1 (by rfl) ⟨187424, by rfl⟩ : syracuseStep 249899 = 374849) B374849
theorem B282683 : Blo 163797 282683 := bstep (se 1 (by rfl) ⟨212012, by rfl⟩ : syracuseStep 282683 = 424025) B424025
theorem B446525 : Blo 163797 446525 := bstep (se 3 (by rfl) ⟨83723, by rfl⟩ : syracuseStep 446525 = 167447) B167447
theorem B643133 : Blo 163797 643133 := bstep (se 3 (by rfl) ⟨120587, by rfl⟩ : syracuseStep 643133 = 241175) B241175
theorem B249929 : Blo 163797 249929 := bstep (se 2 (by rfl) ⟨93723, by rfl⟩ : syracuseStep 249929 = 187447) B187447
theorem B250043 : Blo 163797 250043 := bstep (se 1 (by rfl) ⟨187532, by rfl⟩ : syracuseStep 250043 = 375065) B375065
theorem B315593 : Blo 163797 315593 := bstep (se 2 (by rfl) ⟨118347, by rfl⟩ : syracuseStep 315593 = 236695) B236695
theorem B250103 : Blo 163797 250103 := bstep (se 1 (by rfl) ⟨187577, by rfl⟩ : syracuseStep 250103 = 375155) B375155
theorem B250127 : Blo 163797 250127 := bstep (se 1 (by rfl) ⟨187595, by rfl⟩ : syracuseStep 250127 = 375191) B375191
theorem B839969 : Blo 163797 839969 := bstep (se 2 (by rfl) ⟨314988, by rfl⟩ : syracuseStep 839969 = 629977) B629977
theorem B250169 : Blo 163797 250169 := bstep (se 2 (by rfl) ⟨93813, by rfl⟩ : syracuseStep 250169 = 187627) B187627
theorem B184711 : Blo 163797 184711 := bstep (se 1 (by rfl) ⟨138533, by rfl⟩ : syracuseStep 184711 = 277067) B277067
theorem B250247 : Blo 163797 250247 := bstep (se 1 (by rfl) ⟨187685, by rfl⟩ : syracuseStep 250247 = 375371) B375371
theorem B250283 : Blo 163797 250283 := bstep (se 1 (by rfl) ⟨187712, by rfl⟩ : syracuseStep 250283 = 375425) B375425
theorem B250313 : Blo 163797 250313 := bstep (se 2 (by rfl) ⟨93867, by rfl⟩ : syracuseStep 250313 = 187735) B187735
theorem B283081 : Blo 163797 283081 := bstep (se 2 (by rfl) ⟨106155, by rfl⟩ : syracuseStep 283081 = 212311) B212311
theorem B184891 : Blo 163797 184891 := bstep (se 1 (by rfl) ⟨138668, by rfl⟩ : syracuseStep 184891 = 277337) B277337
theorem B250427 : Blo 163797 250427 := bstep (se 1 (by rfl) ⟨187820, by rfl⟩ : syracuseStep 250427 = 375641) B375641
theorem B250487 : Blo 163797 250487 := bstep (se 1 (by rfl) ⟨187865, by rfl⟩ : syracuseStep 250487 = 375731) B375731
theorem B250511 : Blo 163797 250511 := bstep (se 1 (by rfl) ⟨187883, by rfl⟩ : syracuseStep 250511 = 375767) B375767
theorem B250553 : Blo 163797 250553 := bstep (se 2 (by rfl) ⟨93957, by rfl⟩ : syracuseStep 250553 = 187915) B187915
theorem B250631 : Blo 163797 250631 := bstep (se 1 (by rfl) ⟨187973, by rfl⟩ : syracuseStep 250631 = 375947) B375947
theorem B250667 : Blo 163797 250667 := bstep (se 1 (by rfl) ⟨188000, by rfl⟩ : syracuseStep 250667 = 376001) B376001
theorem B316219 : Blo 163797 316219 := bstep (se 1 (by rfl) ⟨237164, by rfl⟩ : syracuseStep 316219 = 474329) B474329
theorem B250697 : Blo 163797 250697 := bstep (se 2 (by rfl) ⟨94011, by rfl⟩ : syracuseStep 250697 = 188023) B188023
theorem B316295 : Blo 163797 316295 := bstep (se 1 (by rfl) ⟨237221, by rfl⟩ : syracuseStep 316295 = 474443) B474443
theorem B250811 : Blo 163797 250811 := bstep (se 1 (by rfl) ⟨188108, by rfl⟩ : syracuseStep 250811 = 376217) B376217
theorem B250871 : Blo 163797 250871 := bstep (se 1 (by rfl) ⟨188153, by rfl⟩ : syracuseStep 250871 = 376307) B376307
theorem B185359 : Blo 163797 185359 := bstep (se 1 (by rfl) ⟨139019, by rfl⟩ : syracuseStep 185359 = 278039) B278039
theorem B250895 : Blo 163797 250895 := bstep (se 1 (by rfl) ⟨188171, by rfl⟩ : syracuseStep 250895 = 376343) B376343
theorem B250937 : Blo 163797 250937 := bstep (se 2 (by rfl) ⟨94101, by rfl⟩ : syracuseStep 250937 = 188203) B188203
theorem B251015 : Blo 163797 251015 := bstep (se 1 (by rfl) ⟨188261, by rfl⟩ : syracuseStep 251015 = 376523) B376523
theorem B251051 : Blo 163797 251051 := bstep (se 1 (by rfl) ⟨188288, by rfl⟩ : syracuseStep 251051 = 376577) B376577
theorem B251081 : Blo 163797 251081 := bstep (se 2 (by rfl) ⟨94155, by rfl⟩ : syracuseStep 251081 = 188311) B188311
theorem B840941 : Blo 163797 840941 := bstep (se 3 (by rfl) ⟨157676, by rfl⟩ : syracuseStep 840941 = 315353) B315353
theorem B316705 : Blo 163797 316705 := bstep (se 2 (by rfl) ⟨118764, by rfl⟩ : syracuseStep 316705 = 237529) B237529
theorem B251195 : Blo 163797 251195 := bstep (se 1 (by rfl) ⟨188396, by rfl⟩ : syracuseStep 251195 = 376793) B376793
theorem B251255 : Blo 163797 251255 := bstep (se 1 (by rfl) ⟨188441, by rfl⟩ : syracuseStep 251255 = 376883) B376883
theorem B251279 : Blo 163797 251279 := bstep (se 1 (by rfl) ⟨188459, by rfl⟩ : syracuseStep 251279 = 376919) B376919
theorem B251321 : Blo 163797 251321 := bstep (se 2 (by rfl) ⟨94245, by rfl⟩ : syracuseStep 251321 = 188491) B188491
theorem B185863 : Blo 163797 185863 := bstep (se 1 (by rfl) ⟨139397, by rfl⟩ : syracuseStep 185863 = 278795) B278795
theorem B251399 : Blo 163797 251399 := bstep (se 1 (by rfl) ⟨188549, by rfl⟩ : syracuseStep 251399 = 377099) B377099
theorem B251435 : Blo 163797 251435 := bstep (se 1 (by rfl) ⟨188576, by rfl⟩ : syracuseStep 251435 = 377153) B377153
theorem B251465 : Blo 163797 251465 := bstep (se 2 (by rfl) ⟨94299, by rfl⟩ : syracuseStep 251465 = 188599) B188599
theorem B317047 : Blo 163797 317047 := bstep (se 1 (by rfl) ⟨237785, by rfl⟩ : syracuseStep 317047 = 475571) B475571
theorem B186043 : Blo 163797 186043 := bstep (se 1 (by rfl) ⟨139532, by rfl⟩ : syracuseStep 186043 = 279065) B279065
theorem B251579 : Blo 163797 251579 := bstep (se 1 (by rfl) ⟨188684, by rfl⟩ : syracuseStep 251579 = 377369) B377369
theorem B251639 : Blo 163797 251639 := bstep (se 1 (by rfl) ⟨188729, by rfl⟩ : syracuseStep 251639 = 377459) B377459
theorem B415489 : Blo 163797 415489 := bstep (se 2 (by rfl) ⟨155808, by rfl⟩ : syracuseStep 415489 = 311617) B311617
theorem B251663 : Blo 163797 251663 := bstep (se 1 (by rfl) ⟨188747, by rfl⟩ : syracuseStep 251663 = 377495) B377495
theorem B6510449 : Blo 163797 6510449 := bstep (se 2 (by rfl) ⟨2441418, by rfl⟩ : syracuseStep 6510449 = 4882837) B4882837
theorem B841751 : Blo 163797 841751 := bstep (se 1 (by rfl) ⟨631313, by rfl⟩ : syracuseStep 841751 = 1262627) B1262627
theorem B1005655 : Blo 163797 1005655 := bstep (se 1 (by rfl) ⟨754241, by rfl⟩ : syracuseStep 1005655 = 1508483) B1508483
theorem B186511 : Blo 163797 186511 := bstep (se 1 (by rfl) ⟨139883, by rfl⟩ : syracuseStep 186511 = 279767) B279767
theorem B416087 : Blo 163797 416087 := bstep (se 1 (by rfl) ⟨312065, by rfl⟩ : syracuseStep 416087 = 624131) B624131
theorem B514451 : Blo 163797 514451 := bstep (se 1 (by rfl) ⟨385838, by rfl⟩ : syracuseStep 514451 = 771677) B771677
theorem B416299 : Blo 163797 416299 := bstep (se 1 (by rfl) ⟨312224, by rfl⟩ : syracuseStep 416299 = 624449) B624449
theorem B187015 : Blo 163797 187015 := bstep (se 1 (by rfl) ⟨140261, by rfl⟩ : syracuseStep 187015 = 280523) B280523
theorem B416441 : Blo 163797 416441 := bstep (se 2 (by rfl) ⟨156165, by rfl⟩ : syracuseStep 416441 = 312331) B312331
theorem B1530661 : Blo 163797 1530661 := bstep (se 4 (by rfl) ⟨143499, by rfl⟩ : syracuseStep 1530661 = 286999) B286999
theorem B252715 : Blo 163797 252715 := bstep (se 1 (by rfl) ⟨189536, by rfl⟩ : syracuseStep 252715 = 379073) B379073
theorem B187195 : Blo 163797 187195 := bstep (se 1 (by rfl) ⟨140396, by rfl⟩ : syracuseStep 187195 = 280793) B280793
theorem B941003 : Blo 163797 941003 := bstep (se 1 (by rfl) ⟨705752, by rfl⟩ : syracuseStep 941003 = 1411505) B1411505
theorem B252971 : Blo 163797 252971 := bstep (se 1 (by rfl) ⟨189728, by rfl⟩ : syracuseStep 252971 = 379457) B379457
theorem B3988541 : Blo 163797 3988541 := bstep (se 3 (by rfl) ⟨747851, by rfl⟩ : syracuseStep 3988541 = 1495703) B1495703
theorem B711767 : Blo 163797 711767 := bstep (se 1 (by rfl) ⟨533825, by rfl⟩ : syracuseStep 711767 = 1067651) B1067651
theorem B7625933 : Blo 163797 7625933 := bstep (se 3 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 7625933 = 2859725) B2859725
theorem B187663 : Blo 163797 187663 := bstep (se 1 (by rfl) ⟨140747, by rfl⟩ : syracuseStep 187663 = 281495) B281495
theorem B417433 : Blo 163797 417433 := bstep (se 2 (by rfl) ⟨156537, by rfl⟩ : syracuseStep 417433 = 313075) B313075
theorem B188167 : Blo 163797 188167 := bstep (se 1 (by rfl) ⟨141125, by rfl⟩ : syracuseStep 188167 = 282251) B282251
theorem B417595 : Blo 163797 417595 := bstep (se 1 (by rfl) ⟨313196, by rfl⟩ : syracuseStep 417595 = 626393) B626393
theorem B843635 : Blo 163797 843635 := bstep (se 1 (by rfl) ⟨632726, by rfl⟩ : syracuseStep 843635 = 1265453) B1265453
theorem B188347 : Blo 163797 188347 := bstep (se 1 (by rfl) ⟨141260, by rfl⟩ : syracuseStep 188347 = 282521) B282521
theorem B417737 : Blo 163797 417737 := bstep (se 2 (by rfl) ⟨156651, by rfl⟩ : syracuseStep 417737 = 313303) B313303
theorem B352441 : Blo 163797 352441 := bstep (se 2 (by rfl) ⟨132165, by rfl⟩ : syracuseStep 352441 = 264331) B264331
theorem B418081 : Blo 163797 418081 := bstep (se 2 (by rfl) ⟨156780, by rfl⟩ : syracuseStep 418081 = 313561) B313561
theorem B254735 : Blo 163797 254735 := bstep (se 1 (by rfl) ⟨191051, by rfl⟩ : syracuseStep 254735 = 382103) B382103
theorem B418679 : Blo 163797 418679 := bstep (se 1 (by rfl) ⟨314009, by rfl⟩ : syracuseStep 418679 = 628019) B628019
theorem B713681 : Blo 163797 713681 := bstep (se 2 (by rfl) ⟨267630, by rfl⟩ : syracuseStep 713681 = 535261) B535261
theorem B451595 : Blo 163797 451595 := bstep (se 1 (by rfl) ⟨338696, by rfl⟩ : syracuseStep 451595 = 677393) B677393
theorem B844829 : Blo 163797 844829 := bstep (se 3 (by rfl) ⟨158405, by rfl⟩ : syracuseStep 844829 = 316811) B316811
theorem B451855 : Blo 163797 451855 := bstep (se 1 (by rfl) ⟨338891, by rfl⟩ : syracuseStep 451855 = 677783) B677783
theorem B845315 : Blo 163797 845315 := bstep (se 1 (by rfl) ⟨633986, by rfl⟩ : syracuseStep 845315 = 1267973) B1267973
theorem B812717 : Blo 163797 812717 := bstep (se 3 (by rfl) ⟨152384, by rfl⟩ : syracuseStep 812717 = 304769) B304769
theorem B452297 : Blo 163797 452297 := bstep (se 2 (by rfl) ⟨169611, by rfl⟩ : syracuseStep 452297 = 339223) B339223
theorem B354107 : Blo 163797 354107 := bstep (se 1 (by rfl) ⟨265580, by rfl⟩ : syracuseStep 354107 = 531161) B531161
theorem B419975 : Blo 163797 419975 := bstep (se 1 (by rfl) ⟨314981, by rfl⟩ : syracuseStep 419975 = 629963) B629963
theorem B420025 : Blo 163797 420025 := bstep (se 2 (by rfl) ⟨157509, by rfl⟩ : syracuseStep 420025 = 315019) B315019
theorem B6416657 : Blo 163797 6416657 := bstep (se 2 (by rfl) ⟨2406246, by rfl⟩ : syracuseStep 6416657 = 4812493) B4812493
theorem B4549081 : Blo 163797 4549081 := bstep (se 2 (by rfl) ⟨1705905, by rfl⟩ : syracuseStep 4549081 = 3411811) B3411811
theorem B485921 : Blo 163797 485921 := bstep (se 2 (by rfl) ⟨182220, by rfl⟩ : syracuseStep 485921 = 364441) B364441
theorem B2812481 : Blo 163797 2812481 := bstep (se 2 (by rfl) ⟨1054680, by rfl⟩ : syracuseStep 2812481 = 2109361) B2109361
theorem B1010369 : Blo 163797 1010369 := bstep (se 2 (by rfl) ⟨378888, by rfl⟩ : syracuseStep 1010369 = 757777) B757777
theorem B420623 : Blo 163797 420623 := bstep (se 1 (by rfl) ⟨315467, by rfl⟩ : syracuseStep 420623 = 630935) B630935
theorem B846935 : Blo 163797 846935 := bstep (se 1 (by rfl) ⟨635201, by rfl⟩ : syracuseStep 846935 = 1270403) B1270403
theorem B224375 : Blo 163797 224375 := bstep (se 1 (by rfl) ⟨168281, by rfl⟩ : syracuseStep 224375 = 336563) B336563
theorem B453899 : Blo 163797 453899 := bstep (se 1 (by rfl) ⟨340424, by rfl⟩ : syracuseStep 453899 = 680849) B680849
theorem B355627 : Blo 163797 355627 := bstep (se 1 (by rfl) ⟨266720, by rfl⟩ : syracuseStep 355627 = 533441) B533441
theorem B421321 : Blo 163797 421321 := bstep (se 2 (by rfl) ⟨157995, by rfl⟩ : syracuseStep 421321 = 315991) B315991
theorem B1142225 : Blo 163797 1142225 := bstep (se 2 (by rfl) ⟨428334, by rfl⟩ : syracuseStep 1142225 = 856669) B856669
theorem B847421 : Blo 163797 847421 := bstep (se 3 (by rfl) ⟨158891, by rfl⟩ : syracuseStep 847421 = 317783) B317783
theorem B421463 : Blo 163797 421463 := bstep (se 1 (by rfl) ⟨316097, by rfl⟩ : syracuseStep 421463 = 632195) B632195
theorem B421529 : Blo 163797 421529 := bstep (se 2 (by rfl) ⟨158073, by rfl⟩ : syracuseStep 421529 = 316147) B316147
theorem B225067 : Blo 163797 225067 := bstep (se 1 (by rfl) ⟨168800, by rfl⟩ : syracuseStep 225067 = 337601) B337601
theorem B4321073 : Blo 163797 4321073 := bstep (se 2 (by rfl) ⟨1620402, by rfl⟩ : syracuseStep 4321073 = 3240805) B3240805
theorem B552851 : Blo 163797 552851 := bstep (se 1 (by rfl) ⟨414638, by rfl⟩ : syracuseStep 552851 = 829277) B829277
theorem B1601977 : Blo 163797 1601977 := bstep (se 2 (by rfl) ⟨600741, by rfl⟩ : syracuseStep 1601977 = 1201483) B1201483
theorem B487951 : Blo 163797 487951 := bstep (se 1 (by rfl) ⟨365963, by rfl⟩ : syracuseStep 487951 = 731927) B731927
theorem B1340023 : Blo 163797 1340023 := bstep (se 1 (by rfl) ⟨1005017, by rfl⟩ : syracuseStep 1340023 = 2010035) B2010035
theorem B947153 : Blo 163797 947153 := bstep (se 2 (by rfl) ⟨355182, by rfl⟩ : syracuseStep 947153 = 710365) B710365
theorem B422927 : Blo 163797 422927 := bstep (se 1 (by rfl) ⟨317195, by rfl⟩ : syracuseStep 422927 = 634391) B634391
theorem B9172099 : Blo 163797 9172099 := bstep (se 1 (by rfl) ⟨6879074, by rfl⟩ : syracuseStep 9172099 = 13758149) B13758149
theorem B554255 : Blo 163797 554255 := bstep (se 1 (by rfl) ⟨415691, by rfl⟩ : syracuseStep 554255 = 831383) B831383
theorem B849203 : Blo 163797 849203 := bstep (se 1 (by rfl) ⟨636902, by rfl⟩ : syracuseStep 849203 = 1273805) B1273805
theorem B947609 : Blo 163797 947609 := bstep (se 2 (by rfl) ⟨355353, by rfl⟩ : syracuseStep 947609 = 710707) B710707
theorem B554525 : Blo 163797 554525 := bstep (se 3 (by rfl) ⟨103973, by rfl⟩ : syracuseStep 554525 = 207947) B207947
theorem B423539 : Blo 163797 423539 := bstep (se 1 (by rfl) ⟨317654, by rfl⟩ : syracuseStep 423539 = 635309) B635309
theorem B1898315 : Blo 163797 1898315 := bstep (se 1 (by rfl) ⟨1423736, by rfl⟩ : syracuseStep 1898315 = 2847473) B2847473
theorem B1341451 : Blo 163797 1341451 := bstep (se 1 (by rfl) ⟨1006088, by rfl⟩ : syracuseStep 1341451 = 2012177) B2012177
theorem B424055 : Blo 163797 424055 := bstep (se 1 (by rfl) ⟨318041, by rfl⟩ : syracuseStep 424055 = 636083) B636083
theorem B7174453 : Blo 163797 7174453 := bstep (se 5 (by rfl) ⟨336302, by rfl⟩ : syracuseStep 7174453 = 672605) B672605
theorem B424649 : Blo 163797 424649 := bstep (se 2 (by rfl) ⟨159243, by rfl⟩ : syracuseStep 424649 = 318487) B318487
theorem B555929 : Blo 163797 555929 := bstep (se 2 (by rfl) ⟨208473, by rfl⟩ : syracuseStep 555929 = 416947) B416947
theorem B6454333 : Blo 163797 6454333 := bstep (se 3 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 6454333 = 2420375) B2420375
theorem B556631 : Blo 163797 556631 := bstep (se 1 (by rfl) ⟨417473, by rfl⟩ : syracuseStep 556631 = 834947) B834947
theorem B1245131 : Blo 163797 1245131 := bstep (se 1 (by rfl) ⟨933848, by rfl⟩ : syracuseStep 1245131 = 1867697) B1867697
theorem B557063 : Blo 163797 557063 := bstep (se 1 (by rfl) ⟨417797, by rfl⟩ : syracuseStep 557063 = 835595) B835595
theorem B163879 : Blo 163797 163879 := bstep (se 1 (by rfl) ⟨122909, by rfl⟩ : syracuseStep 163879 = 245819) B245819
theorem B163919 : Blo 163797 163919 := bstep (se 1 (by rfl) ⟨122939, by rfl⟩ : syracuseStep 163919 = 245879) B245879
theorem B622673 : Blo 163797 622673 := bstep (se 2 (by rfl) ⟨233502, by rfl⟩ : syracuseStep 622673 = 467005) B467005
theorem B163935 : Blo 163797 163935 := bstep (se 1 (by rfl) ⟨122951, by rfl⟩ : syracuseStep 163935 = 245903) B245903
theorem B557171 : Blo 163797 557171 := bstep (se 1 (by rfl) ⟨417878, by rfl⟩ : syracuseStep 557171 = 835757) B835757
theorem B163963 : Blo 163797 163963 := bstep (se 1 (by rfl) ⟨122972, by rfl⟩ : syracuseStep 163963 = 245945) B245945
theorem B164015 : Blo 163797 164015 := bstep (se 1 (by rfl) ⟨123011, by rfl⟩ : syracuseStep 164015 = 246023) B246023
theorem B164039 : Blo 163797 164039 := bstep (se 1 (by rfl) ⟨123029, by rfl⟩ : syracuseStep 164039 = 246059) B246059
theorem B164059 : Blo 163797 164059 := bstep (se 1 (by rfl) ⟨123044, by rfl⟩ : syracuseStep 164059 = 246089) B246089
theorem B164135 : Blo 163797 164135 := bstep (se 1 (by rfl) ⟨123101, by rfl⟩ : syracuseStep 164135 = 246203) B246203
theorem B164175 : Blo 163797 164175 := bstep (se 1 (by rfl) ⟨123131, by rfl⟩ : syracuseStep 164175 = 246263) B246263
theorem B164191 : Blo 163797 164191 := bstep (se 1 (by rfl) ⟨123143, by rfl⟩ : syracuseStep 164191 = 246287) B246287
theorem B164219 : Blo 163797 164219 := bstep (se 1 (by rfl) ⟨123164, by rfl⟩ : syracuseStep 164219 = 246329) B246329
theorem B557441 : Blo 163797 557441 := bstep (se 2 (by rfl) ⟨209040, by rfl⟩ : syracuseStep 557441 = 418081) B418081
theorem B262543 : Blo 163797 262543 := bstep (se 1 (by rfl) ⟨196907, by rfl⟩ : syracuseStep 262543 = 393815) B393815
theorem B622991 : Blo 163797 622991 := bstep (se 1 (by rfl) ⟨467243, by rfl⟩ : syracuseStep 622991 = 934487) B934487
theorem B164271 : Blo 163797 164271 := bstep (se 1 (by rfl) ⟨123203, by rfl⟩ : syracuseStep 164271 = 246407) B246407
theorem B164295 : Blo 163797 164295 := bstep (se 1 (by rfl) ⟨123221, by rfl⟩ : syracuseStep 164295 = 246443) B246443
theorem B164315 : Blo 163797 164315 := bstep (se 1 (by rfl) ⟨123236, by rfl⟩ : syracuseStep 164315 = 246473) B246473
theorem B164391 : Blo 163797 164391 := bstep (se 1 (by rfl) ⟨123293, by rfl⟩ : syracuseStep 164391 = 246587) B246587
theorem B164431 : Blo 163797 164431 := bstep (se 1 (by rfl) ⟨123323, by rfl⟩ : syracuseStep 164431 = 246647) B246647
theorem B164447 : Blo 163797 164447 := bstep (se 1 (by rfl) ⟨123335, by rfl⟩ : syracuseStep 164447 = 246671) B246671
theorem B164475 : Blo 163797 164475 := bstep (se 1 (by rfl) ⟨123356, by rfl⟩ : syracuseStep 164475 = 246713) B246713
theorem B164527 : Blo 163797 164527 := bstep (se 1 (by rfl) ⟨123395, by rfl⟩ : syracuseStep 164527 = 246791) B246791
theorem B164551 : Blo 163797 164551 := bstep (se 1 (by rfl) ⟨123413, by rfl⟩ : syracuseStep 164551 = 246827) B246827
theorem B164571 : Blo 163797 164571 := bstep (se 1 (by rfl) ⟨123428, by rfl⟩ : syracuseStep 164571 = 246857) B246857
theorem B1409795 : Blo 163797 1409795 := bstep (se 1 (by rfl) ⟨1057346, by rfl⟩ : syracuseStep 1409795 = 2114693) B2114693
theorem B164647 : Blo 163797 164647 := bstep (se 1 (by rfl) ⟨123485, by rfl⟩ : syracuseStep 164647 = 246971) B246971
theorem B590665 : Blo 163797 590665 := bstep (se 2 (by rfl) ⟨221499, by rfl⟩ : syracuseStep 590665 = 442999) B442999
theorem B164687 : Blo 163797 164687 := bstep (se 1 (by rfl) ⟨123515, by rfl⟩ : syracuseStep 164687 = 247031) B247031
theorem B164703 : Blo 163797 164703 := bstep (se 1 (by rfl) ⟨123527, by rfl⟩ : syracuseStep 164703 = 247055) B247055
theorem B263017 : Blo 163797 263017 := bstep (se 2 (by rfl) ⟨98631, by rfl⟩ : syracuseStep 263017 = 197263) B197263
theorem B164731 : Blo 163797 164731 := bstep (se 1 (by rfl) ⟨123548, by rfl⟩ : syracuseStep 164731 = 247097) B247097
theorem B590753 : Blo 163797 590753 := bstep (se 2 (by rfl) ⟨221532, by rfl⟩ : syracuseStep 590753 = 443065) B443065
theorem B164783 : Blo 163797 164783 := bstep (se 1 (by rfl) ⟨123587, by rfl⟩ : syracuseStep 164783 = 247175) B247175
theorem B164807 : Blo 163797 164807 := bstep (se 1 (by rfl) ⟨123605, by rfl⟩ : syracuseStep 164807 = 247211) B247211
theorem B164827 : Blo 163797 164827 := bstep (se 1 (by rfl) ⟨123620, by rfl⟩ : syracuseStep 164827 = 247241) B247241
theorem B787457 : Blo 163797 787457 := bstep (se 2 (by rfl) ⟨295296, by rfl⟩ : syracuseStep 787457 = 590593) B590593
theorem B787475 : Blo 163797 787475 := bstep (se 1 (by rfl) ⟨590606, by rfl⟩ : syracuseStep 787475 = 1181213) B1181213
theorem B590867 : Blo 163797 590867 := bstep (se 1 (by rfl) ⟨443150, by rfl⟩ : syracuseStep 590867 = 886301) B886301
theorem B164903 : Blo 163797 164903 := bstep (se 1 (by rfl) ⟨123677, by rfl⟩ : syracuseStep 164903 = 247355) B247355
theorem B164943 : Blo 163797 164943 := bstep (se 1 (by rfl) ⟨123707, by rfl⟩ : syracuseStep 164943 = 247415) B247415
theorem B164959 : Blo 163797 164959 := bstep (se 1 (by rfl) ⟨123719, by rfl⟩ : syracuseStep 164959 = 247439) B247439
theorem B164987 : Blo 163797 164987 := bstep (se 1 (by rfl) ⟨123740, by rfl⟩ : syracuseStep 164987 = 247481) B247481
theorem B558251 : Blo 163797 558251 := bstep (se 1 (by rfl) ⟨418688, by rfl⟩ : syracuseStep 558251 = 837377) B837377
theorem B165039 : Blo 163797 165039 := bstep (se 1 (by rfl) ⟨123779, by rfl⟩ : syracuseStep 165039 = 247559) B247559
theorem B165063 : Blo 163797 165063 := bstep (se 1 (by rfl) ⟨123797, by rfl⟩ : syracuseStep 165063 = 247595) B247595
theorem B165083 : Blo 163797 165083 := bstep (se 1 (by rfl) ⟨123812, by rfl⟩ : syracuseStep 165083 = 247625) B247625
theorem B165159 : Blo 163797 165159 := bstep (se 1 (by rfl) ⟨123869, by rfl⟩ : syracuseStep 165159 = 247739) B247739
theorem B623933 : Blo 163797 623933 := bstep (se 3 (by rfl) ⟨116987, by rfl⟩ : syracuseStep 623933 = 233975) B233975
theorem B165199 : Blo 163797 165199 := bstep (se 1 (by rfl) ⟨123899, by rfl⟩ : syracuseStep 165199 = 247799) B247799
theorem B165215 : Blo 163797 165215 := bstep (se 1 (by rfl) ⟨123911, by rfl⟩ : syracuseStep 165215 = 247823) B247823
theorem B165243 : Blo 163797 165243 := bstep (se 1 (by rfl) ⟨123932, by rfl⟩ : syracuseStep 165243 = 247865) B247865
theorem B1246589 : Blo 163797 1246589 := bstep (se 3 (by rfl) ⟨233735, by rfl⟩ : syracuseStep 1246589 = 467471) B467471
theorem B296335 : Blo 163797 296335 := bstep (se 1 (by rfl) ⟨222251, by rfl⟩ : syracuseStep 296335 = 444503) B444503
theorem B165295 : Blo 163797 165295 := bstep (se 1 (by rfl) ⟨123971, by rfl⟩ : syracuseStep 165295 = 247943) B247943
theorem B165319 : Blo 163797 165319 := bstep (se 1 (by rfl) ⟨123989, by rfl⟩ : syracuseStep 165319 = 247979) B247979
theorem B165339 : Blo 163797 165339 := bstep (se 1 (by rfl) ⟨124004, by rfl⟩ : syracuseStep 165339 = 248009) B248009
theorem B165415 : Blo 163797 165415 := bstep (se 1 (by rfl) ⟨124061, by rfl⟩ : syracuseStep 165415 = 248123) B248123
theorem B165455 : Blo 163797 165455 := bstep (se 1 (by rfl) ⟨124091, by rfl⟩ : syracuseStep 165455 = 248183) B248183
theorem B165471 : Blo 163797 165471 := bstep (se 1 (by rfl) ⟨124103, by rfl⟩ : syracuseStep 165471 = 248207) B248207
theorem B165499 : Blo 163797 165499 := bstep (se 1 (by rfl) ⟨124124, by rfl⟩ : syracuseStep 165499 = 248249) B248249
theorem B3212945 : Blo 163797 3212945 := bstep (se 2 (by rfl) ⟨1204854, by rfl⟩ : syracuseStep 3212945 = 2409709) B2409709
theorem B165551 : Blo 163797 165551 := bstep (se 1 (by rfl) ⟨124163, by rfl⟩ : syracuseStep 165551 = 248327) B248327
theorem B558791 : Blo 163797 558791 := bstep (se 1 (by rfl) ⟨419093, by rfl⟩ : syracuseStep 558791 = 838187) B838187
theorem B165575 : Blo 163797 165575 := bstep (se 1 (by rfl) ⟨124181, by rfl⟩ : syracuseStep 165575 = 248363) B248363
theorem B165595 : Blo 163797 165595 := bstep (se 1 (by rfl) ⟨124196, by rfl⟩ : syracuseStep 165595 = 248393) B248393
theorem B263927 : Blo 163797 263927 := bstep (se 1 (by rfl) ⟨197945, by rfl⟩ : syracuseStep 263927 = 395891) B395891
theorem B165671 : Blo 163797 165671 := bstep (se 1 (by rfl) ⟨124253, by rfl⟩ : syracuseStep 165671 = 248507) B248507
theorem B165711 : Blo 163797 165711 := bstep (se 1 (by rfl) ⟨124283, by rfl⟩ : syracuseStep 165711 = 248567) B248567
theorem B165727 : Blo 163797 165727 := bstep (se 1 (by rfl) ⟨124295, by rfl⟩ : syracuseStep 165727 = 248591) B248591
theorem B165755 : Blo 163797 165755 := bstep (se 1 (by rfl) ⟨124316, by rfl⟩ : syracuseStep 165755 = 248633) B248633
theorem B165807 : Blo 163797 165807 := bstep (se 1 (by rfl) ⟨124355, by rfl⟩ : syracuseStep 165807 = 248711) B248711
theorem B165831 : Blo 163797 165831 := bstep (se 1 (by rfl) ⟨124373, by rfl⟩ : syracuseStep 165831 = 248747) B248747
theorem B165851 : Blo 163797 165851 := bstep (se 1 (by rfl) ⟨124388, by rfl⟩ : syracuseStep 165851 = 248777) B248777
theorem B165927 : Blo 163797 165927 := bstep (se 1 (by rfl) ⟨124445, by rfl⟩ : syracuseStep 165927 = 248891) B248891
theorem B165967 : Blo 163797 165967 := bstep (se 1 (by rfl) ⟨124475, by rfl⟩ : syracuseStep 165967 = 248951) B248951
theorem B165983 : Blo 163797 165983 := bstep (se 1 (by rfl) ⟨124487, by rfl⟩ : syracuseStep 165983 = 248975) B248975
theorem B166011 : Blo 163797 166011 := bstep (se 1 (by rfl) ⟨124508, by rfl⟩ : syracuseStep 166011 = 249017) B249017
theorem B166063 : Blo 163797 166063 := bstep (se 1 (by rfl) ⟨124547, by rfl⟩ : syracuseStep 166063 = 249095) B249095
theorem B166087 : Blo 163797 166087 := bstep (se 1 (by rfl) ⟨124565, by rfl⟩ : syracuseStep 166087 = 249131) B249131
theorem B166107 : Blo 163797 166107 := bstep (se 1 (by rfl) ⟨124580, by rfl⟩ : syracuseStep 166107 = 249161) B249161
theorem B166183 : Blo 163797 166183 := bstep (se 1 (by rfl) ⟨124637, by rfl⟩ : syracuseStep 166183 = 249275) B249275
theorem B166223 : Blo 163797 166223 := bstep (se 1 (by rfl) ⟨124667, by rfl⟩ : syracuseStep 166223 = 249335) B249335
theorem B166239 : Blo 163797 166239 := bstep (se 1 (by rfl) ⟨124679, by rfl⟩ : syracuseStep 166239 = 249359) B249359
theorem B166267 : Blo 163797 166267 := bstep (se 1 (by rfl) ⟨124700, by rfl⟩ : syracuseStep 166267 = 249401) B249401
theorem B166319 : Blo 163797 166319 := bstep (se 1 (by rfl) ⟨124739, by rfl⟩ : syracuseStep 166319 = 249479) B249479
theorem B166343 : Blo 163797 166343 := bstep (se 1 (by rfl) ⟨124757, by rfl⟩ : syracuseStep 166343 = 249515) B249515
theorem B166363 : Blo 163797 166363 := bstep (se 1 (by rfl) ⟨124772, by rfl⟩ : syracuseStep 166363 = 249545) B249545
theorem B559655 : Blo 163797 559655 := bstep (se 1 (by rfl) ⟨419741, by rfl⟩ : syracuseStep 559655 = 839483) B839483
theorem B166439 : Blo 163797 166439 := bstep (se 1 (by rfl) ⟨124829, by rfl⟩ : syracuseStep 166439 = 249659) B249659
theorem B166479 : Blo 163797 166479 := bstep (se 1 (by rfl) ⟨124859, by rfl⟩ : syracuseStep 166479 = 249719) B249719
theorem B166495 : Blo 163797 166495 := bstep (se 1 (by rfl) ⟨124871, by rfl⟩ : syracuseStep 166495 = 249743) B249743
theorem B166523 : Blo 163797 166523 := bstep (se 1 (by rfl) ⟨124892, by rfl⟩ : syracuseStep 166523 = 249785) B249785
theorem B559763 : Blo 163797 559763 := bstep (se 1 (by rfl) ⟨419822, by rfl⟩ : syracuseStep 559763 = 839645) B839645
theorem B264875 : Blo 163797 264875 := bstep (se 1 (by rfl) ⟨198656, by rfl⟩ : syracuseStep 264875 = 397313) B397313
theorem B166575 : Blo 163797 166575 := bstep (se 1 (by rfl) ⟨124931, by rfl⟩ : syracuseStep 166575 = 249863) B249863
theorem B527033 : Blo 163797 527033 := bstep (se 2 (by rfl) ⟨197637, by rfl⟩ : syracuseStep 527033 = 395275) B395275
theorem B166599 : Blo 163797 166599 := bstep (se 1 (by rfl) ⟨124949, by rfl⟩ : syracuseStep 166599 = 249899) B249899
theorem B428755 : Blo 163797 428755 := bstep (se 1 (by rfl) ⟨321566, by rfl⟩ : syracuseStep 428755 = 643133) B643133
theorem B297683 : Blo 163797 297683 := bstep (se 1 (by rfl) ⟨223262, by rfl⟩ : syracuseStep 297683 = 446525) B446525
theorem B166619 : Blo 163797 166619 := bstep (se 1 (by rfl) ⟨124964, by rfl⟩ : syracuseStep 166619 = 249929) B249929
theorem B166695 : Blo 163797 166695 := bstep (se 1 (by rfl) ⟨125021, by rfl⟩ : syracuseStep 166695 = 250043) B250043
theorem B166735 : Blo 163797 166735 := bstep (se 1 (by rfl) ⟨125051, by rfl⟩ : syracuseStep 166735 = 250103) B250103
theorem B166751 : Blo 163797 166751 := bstep (se 1 (by rfl) ⟨125063, by rfl⟩ : syracuseStep 166751 = 250127) B250127
theorem B559979 : Blo 163797 559979 := bstep (se 1 (by rfl) ⟨419984, by rfl⟩ : syracuseStep 559979 = 839969) B839969
theorem B166779 : Blo 163797 166779 := bstep (se 1 (by rfl) ⟨125084, by rfl⟩ : syracuseStep 166779 = 250169) B250169
theorem B560033 : Blo 163797 560033 := bstep (se 2 (by rfl) ⟨210012, by rfl⟩ : syracuseStep 560033 = 420025) B420025
theorem B166831 : Blo 163797 166831 := bstep (se 1 (by rfl) ⟨125123, by rfl⟩ : syracuseStep 166831 = 250247) B250247
theorem B166855 : Blo 163797 166855 := bstep (se 1 (by rfl) ⟨125141, by rfl⟩ : syracuseStep 166855 = 250283) B250283
theorem B166875 : Blo 163797 166875 := bstep (se 1 (by rfl) ⟨125156, by rfl⟩ : syracuseStep 166875 = 250313) B250313
theorem B166951 : Blo 163797 166951 := bstep (se 1 (by rfl) ⟨125213, by rfl⟩ : syracuseStep 166951 = 250427) B250427
theorem B166991 : Blo 163797 166991 := bstep (se 1 (by rfl) ⟨125243, by rfl⟩ : syracuseStep 166991 = 250487) B250487
theorem B167007 : Blo 163797 167007 := bstep (se 1 (by rfl) ⟨125255, by rfl⟩ : syracuseStep 167007 = 250511) B250511
theorem B167035 : Blo 163797 167035 := bstep (se 1 (by rfl) ⟨125276, by rfl⟩ : syracuseStep 167035 = 250553) B250553
theorem B167087 : Blo 163797 167087 := bstep (se 1 (by rfl) ⟨125315, by rfl⟩ : syracuseStep 167087 = 250631) B250631
theorem B1510595 : Blo 163797 1510595 := bstep (se 1 (by rfl) ⟨1132946, by rfl⟩ : syracuseStep 1510595 = 2265893) B2265893
theorem B167111 : Blo 163797 167111 := bstep (se 1 (by rfl) ⟨125333, by rfl⟩ : syracuseStep 167111 = 250667) B250667
theorem B167131 : Blo 163797 167131 := bstep (se 1 (by rfl) ⟨125348, by rfl⟩ : syracuseStep 167131 = 250697) B250697
theorem B6065441 : Blo 163797 6065441 := bstep (se 2 (by rfl) ⟨2274540, by rfl⟩ : syracuseStep 6065441 = 4549081) B4549081
theorem B167207 : Blo 163797 167207 := bstep (se 1 (by rfl) ⟨125405, by rfl⟩ : syracuseStep 167207 = 250811) B250811
theorem B167247 : Blo 163797 167247 := bstep (se 1 (by rfl) ⟨125435, by rfl⟩ : syracuseStep 167247 = 250871) B250871
theorem B265567 : Blo 163797 265567 := bstep (se 1 (by rfl) ⟨199175, by rfl⟩ : syracuseStep 265567 = 398351) B398351
theorem B167263 : Blo 163797 167263 := bstep (se 1 (by rfl) ⟨125447, by rfl⟩ : syracuseStep 167263 = 250895) B250895
theorem B167291 : Blo 163797 167291 := bstep (se 1 (by rfl) ⟨125468, by rfl⟩ : syracuseStep 167291 = 250937) B250937
theorem B1609085 : Blo 163797 1609085 := bstep (se 3 (by rfl) ⟨301703, by rfl⟩ : syracuseStep 1609085 = 603407) B603407
theorem B167343 : Blo 163797 167343 := bstep (se 1 (by rfl) ⟨125507, by rfl⟩ : syracuseStep 167343 = 251015) B251015
theorem B167367 : Blo 163797 167367 := bstep (se 1 (by rfl) ⟨125525, by rfl⟩ : syracuseStep 167367 = 251051) B251051
theorem B167387 : Blo 163797 167387 := bstep (se 1 (by rfl) ⟨125540, by rfl⟩ : syracuseStep 167387 = 251081) B251081
theorem B560627 : Blo 163797 560627 := bstep (se 1 (by rfl) ⟨420470, by rfl⟩ : syracuseStep 560627 = 840941) B840941
theorem B855539 : Blo 163797 855539 := bstep (se 1 (by rfl) ⟨641654, by rfl⟩ : syracuseStep 855539 = 1283309) B1283309
theorem B167463 : Blo 163797 167463 := bstep (se 1 (by rfl) ⟨125597, by rfl⟩ : syracuseStep 167463 = 251195) B251195
theorem B167503 : Blo 163797 167503 := bstep (se 1 (by rfl) ⟨125627, by rfl⟩ : syracuseStep 167503 = 251255) B251255
theorem B167519 : Blo 163797 167519 := bstep (se 1 (by rfl) ⟨125639, by rfl⟩ : syracuseStep 167519 = 251279) B251279
theorem B167547 : Blo 163797 167547 := bstep (se 1 (by rfl) ⟨125660, by rfl⟩ : syracuseStep 167547 = 251321) B251321
theorem B167599 : Blo 163797 167599 := bstep (se 1 (by rfl) ⟨125699, by rfl⟩ : syracuseStep 167599 = 251399) B251399
theorem B167623 : Blo 163797 167623 := bstep (se 1 (by rfl) ⟨125717, by rfl⟩ : syracuseStep 167623 = 251435) B251435
theorem B167643 : Blo 163797 167643 := bstep (se 1 (by rfl) ⟨125732, by rfl⟩ : syracuseStep 167643 = 251465) B251465
theorem B167719 : Blo 163797 167719 := bstep (se 1 (by rfl) ⟨125789, by rfl⟩ : syracuseStep 167719 = 251579) B251579
theorem B167759 : Blo 163797 167759 := bstep (se 1 (by rfl) ⟨125819, by rfl⟩ : syracuseStep 167759 = 251639) B251639
theorem B167775 : Blo 163797 167775 := bstep (se 1 (by rfl) ⟨125831, by rfl⟩ : syracuseStep 167775 = 251663) B251663
theorem B561167 : Blo 163797 561167 := bstep (se 1 (by rfl) ⟨420875, by rfl⟩ : syracuseStep 561167 = 841751) B841751
theorem B1052939 : Blo 163797 1052939 := bstep (se 1 (by rfl) ⟨789704, by rfl⟩ : syracuseStep 1052939 = 1579409) B1579409
theorem B1773899 : Blo 163797 1773899 := bstep (se 1 (by rfl) ⟨1330424, by rfl⟩ : syracuseStep 1773899 = 2660849) B2660849
theorem B528905 : Blo 163797 528905 := bstep (se 2 (by rfl) ⟨198339, by rfl⟩ : syracuseStep 528905 = 396679) B396679
theorem B59609621 : Blo 163797 59609621 := bstep (se 6 (by rfl) ⟨1397100, by rfl⟩ : syracuseStep 59609621 = 2794201) B2794201
theorem B561761 : Blo 163797 561761 := bstep (se 2 (by rfl) ⟨210660, by rfl⟩ : syracuseStep 561761 = 421321) B421321
theorem B627335 : Blo 163797 627335 := bstep (se 1 (by rfl) ⟨470501, by rfl⟩ : syracuseStep 627335 = 941003) B941003
theorem B168647 : Blo 163797 168647 := bstep (se 1 (by rfl) ⟨126485, by rfl⟩ : syracuseStep 168647 = 252971) B252971
theorem B201415 : Blo 163797 201415 := bstep (se 1 (by rfl) ⟨151061, by rfl⟩ : syracuseStep 201415 = 302123) B302123
theorem B2659027 : Blo 163797 2659027 := bstep (se 1 (by rfl) ⟨1994270, by rfl⟩ : syracuseStep 2659027 = 3988541) B3988541
theorem B5083955 : Blo 163797 5083955 := bstep (se 1 (by rfl) ⟨3812966, by rfl⟩ : syracuseStep 5083955 = 7625933) B7625933
theorem B234505 : Blo 163797 234505 := bstep (se 2 (by rfl) ⟨87939, by rfl⟩ : syracuseStep 234505 = 175879) B175879
theorem B2692115 : Blo 163797 2692115 := bstep (se 1 (by rfl) ⟨2019086, by rfl⟩ : syracuseStep 2692115 = 4038173) B4038173
theorem B300089 : Blo 163797 300089 := bstep (se 2 (by rfl) ⟨112533, by rfl⟩ : syracuseStep 300089 = 225067) B225067
theorem B267695 : Blo 163797 267695 := bstep (se 1 (by rfl) ⟨200771, by rfl⟩ : syracuseStep 267695 = 401543) B401543
theorem B1250963 : Blo 163797 1250963 := bstep (se 1 (by rfl) ⟨938222, by rfl⟩ : syracuseStep 1250963 = 1876445) B1876445
theorem B530135 : Blo 163797 530135 := bstep (se 1 (by rfl) ⟨397601, by rfl⟩ : syracuseStep 530135 = 795203) B795203
theorem B268105 : Blo 163797 268105 := bstep (se 2 (by rfl) ⟨100539, by rfl⟩ : syracuseStep 268105 = 201079) B201079
theorem B169823 : Blo 163797 169823 := bstep (se 1 (by rfl) ⟨127367, by rfl⟩ : syracuseStep 169823 = 254735) B254735
theorem B2135969 : Blo 163797 2135969 := bstep (se 2 (by rfl) ⟨800988, by rfl⟩ : syracuseStep 2135969 = 1601977) B1601977
theorem B1185799 : Blo 163797 1185799 := bstep (se 1 (by rfl) ⟨889349, by rfl⟩ : syracuseStep 1185799 = 1778699) B1778699
theorem B563219 : Blo 163797 563219 := bstep (se 1 (by rfl) ⟨422414, by rfl⟩ : syracuseStep 563219 = 844829) B844829
theorem B628793 : Blo 163797 628793 := bstep (se 2 (by rfl) ⟨235797, by rfl⟩ : syracuseStep 628793 = 471595) B471595
theorem B563543 : Blo 163797 563543 := bstep (se 1 (by rfl) ⟨422657, by rfl⟩ : syracuseStep 563543 = 845315) B845315
theorem B301531 : Blo 163797 301531 := bstep (se 1 (by rfl) ⟨226148, by rfl⟩ : syracuseStep 301531 = 452297) B452297
theorem B891425 : Blo 163797 891425 := bstep (se 2 (by rfl) ⟨334284, by rfl⟩ : syracuseStep 891425 = 668569) B668569
theorem B236071 : Blo 163797 236071 := bstep (se 1 (by rfl) ⟨177053, by rfl⟩ : syracuseStep 236071 = 354107) B354107
theorem B334415 : Blo 163797 334415 := bstep (se 1 (by rfl) ⟨250811, by rfl⟩ : syracuseStep 334415 = 501623) B501623
theorem B596603 : Blo 163797 596603 := bstep (se 1 (by rfl) ⟨447452, by rfl⟩ : syracuseStep 596603 = 894905) B894905
theorem B12229465 : Blo 163797 12229465 := bstep (se 2 (by rfl) ⟨4586049, by rfl⟩ : syracuseStep 12229465 = 9172099) B9172099
theorem B1874987 : Blo 163797 1874987 := bstep (se 1 (by rfl) ⟨1406240, by rfl⟩ : syracuseStep 1874987 = 2812481) B2812481
theorem B564623 : Blo 163797 564623 := bstep (se 1 (by rfl) ⟨423467, by rfl⟩ : syracuseStep 564623 = 846935) B846935
theorem B302599 : Blo 163797 302599 := bstep (se 1 (by rfl) ⟨226949, by rfl⟩ : syracuseStep 302599 = 453899) B453899
theorem B630281 : Blo 163797 630281 := bstep (se 2 (by rfl) ⟨236355, by rfl⟩ : syracuseStep 630281 = 472711) B472711
theorem B761483 : Blo 163797 761483 := bstep (se 1 (by rfl) ⟨571112, by rfl⟩ : syracuseStep 761483 = 1142225) B1142225
theorem B564947 : Blo 163797 564947 := bstep (se 1 (by rfl) ⟨423710, by rfl⟩ : syracuseStep 564947 = 847421) B847421
theorem B368567 : Blo 163797 368567 := bstep (se 1 (by rfl) ⟨276425, by rfl⟩ : syracuseStep 368567 = 552851) B552851
theorem B532595 : Blo 163797 532595 := bstep (se 1 (by rfl) ⟨399446, by rfl⟩ : syracuseStep 532595 = 798893) B798893
theorem B335995 : Blo 163797 335995 := bstep (se 1 (by rfl) ⟨251996, by rfl⟩ : syracuseStep 335995 = 503993) B503993
theorem B598333 : Blo 163797 598333 := bstep (se 3 (by rfl) ⟨112187, by rfl⟩ : syracuseStep 598333 = 224375) B224375
theorem B369161 : Blo 163797 369161 := bstep (se 2 (by rfl) ⟨138435, by rfl⟩ : syracuseStep 369161 = 276871) B276871
theorem B1188361 : Blo 163797 1188361 := bstep (se 2 (by rfl) ⟨445635, by rfl⟩ : syracuseStep 1188361 = 891271) B891271
theorem B467495 : Blo 163797 467495 := bstep (se 1 (by rfl) ⟨350621, by rfl⟩ : syracuseStep 467495 = 701243) B701243
theorem B631435 : Blo 163797 631435 := bstep (se 1 (by rfl) ⟨473576, by rfl⟩ : syracuseStep 631435 = 947153) B947153
theorem B1352477 : Blo 163797 1352477 := bstep (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) B507179
theorem B369503 : Blo 163797 369503 := bstep (se 1 (by rfl) ⟨277127, by rfl⟩ : syracuseStep 369503 = 554255) B554255
theorem B566135 : Blo 163797 566135 := bstep (se 1 (by rfl) ⟨424601, by rfl⟩ : syracuseStep 566135 = 849203) B849203
theorem B631739 : Blo 163797 631739 := bstep (se 1 (by rfl) ⟨473804, by rfl⟩ : syracuseStep 631739 = 947609) B947609
theorem B1254365 : Blo 163797 1254365 := bstep (se 3 (by rfl) ⟨235193, by rfl⟩ : syracuseStep 1254365 = 470387) B470387
theorem B369683 : Blo 163797 369683 := bstep (se 1 (by rfl) ⟨277262, by rfl⟩ : syracuseStep 369683 = 554525) B554525
theorem B2040881 : Blo 163797 2040881 := bstep (se 2 (by rfl) ⟨765330, by rfl⟩ : syracuseStep 2040881 = 1530661) B1530661
theorem B336953 : Blo 163797 336953 := bstep (se 2 (by rfl) ⟨126357, by rfl⟩ : syracuseStep 336953 = 252715) B252715
theorem B370025 : Blo 163797 370025 := bstep (se 2 (by rfl) ⟨138759, by rfl⟩ : syracuseStep 370025 = 277519) B277519
theorem B468679 : Blo 163797 468679 := bstep (se 1 (by rfl) ⟨351509, by rfl⟩ : syracuseStep 468679 = 703019) B703019
theorem B1124077 : Blo 163797 1124077 := bstep (se 3 (by rfl) ⟨210764, by rfl⟩ : syracuseStep 1124077 = 421529) B421529
theorem B370619 : Blo 163797 370619 := bstep (se 1 (by rfl) ⟨277964, by rfl⟩ : syracuseStep 370619 = 555929) B555929
theorem B370745 : Blo 163797 370745 := bstep (se 2 (by rfl) ⟨139029, by rfl⟩ : syracuseStep 370745 = 278059) B278059
theorem B338131 : Blo 163797 338131 := bstep (se 1 (by rfl) ⟨253598, by rfl⟩ : syracuseStep 338131 = 507197) B507197
theorem B371087 : Blo 163797 371087 := bstep (se 1 (by rfl) ⟨278315, by rfl⟩ : syracuseStep 371087 = 556631) B556631
theorem B830087 : Blo 163797 830087 := bstep (se 1 (by rfl) ⟨622565, by rfl⟩ : syracuseStep 830087 = 1245131) B1245131
theorem B666251 : Blo 163797 666251 := bstep (se 1 (by rfl) ⟨499688, by rfl⟩ : syracuseStep 666251 = 999377) B999377
theorem B371411 : Blo 163797 371411 := bstep (se 1 (by rfl) ⟨278558, by rfl⟩ : syracuseStep 371411 = 557117) B557117
theorem B174943 : Blo 163797 174943 := bstep (se 1 (by rfl) ⟨131207, by rfl⟩ : syracuseStep 174943 = 262415) B262415
theorem B469921 : Blo 163797 469921 := bstep (se 2 (by rfl) ⟨176220, by rfl⟩ : syracuseStep 469921 = 352441) B352441
theorem B1649591 : Blo 163797 1649591 := bstep (se 1 (by rfl) ⟨1237193, by rfl⟩ : syracuseStep 1649591 = 2474387) B2474387
theorem B601015 : Blo 163797 601015 := bstep (se 1 (by rfl) ⟨450761, by rfl⟩ : syracuseStep 601015 = 901523) B901523
theorem B535709 : Blo 163797 535709 := bstep (se 3 (by rfl) ⟨100445, by rfl⟩ : syracuseStep 535709 = 200891) B200891
theorem B208423 : Blo 163797 208423 := bstep (se 1 (by rfl) ⟨156317, by rfl⟩ : syracuseStep 208423 = 312635) B312635
theorem B372347 : Blo 163797 372347 := bstep (se 1 (by rfl) ⟨279260, by rfl⟩ : syracuseStep 372347 = 558521) B558521
theorem B372473 : Blo 163797 372473 := bstep (se 2 (by rfl) ⟨139677, by rfl⟩ : syracuseStep 372473 = 279355) B279355
theorem B208747 : Blo 163797 208747 := bstep (se 1 (by rfl) ⟨156560, by rfl⟩ : syracuseStep 208747 = 313121) B313121
theorem B569263 : Blo 163797 569263 := bstep (se 1 (by rfl) ⟨426947, by rfl⟩ : syracuseStep 569263 = 853895) B853895
theorem B1421243 : Blo 163797 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B372743 : Blo 163797 372743 := bstep (se 1 (by rfl) ⟨279557, by rfl⟩ : syracuseStep 372743 = 559115) B559115
theorem B831545 : Blo 163797 831545 := bstep (se 2 (by rfl) ⟨311829, by rfl⟩ : syracuseStep 831545 = 623659) B623659
theorem B208975 : Blo 163797 208975 := bstep (se 1 (by rfl) ⟨156731, by rfl⟩ : syracuseStep 208975 = 313463) B313463
theorem B372815 : Blo 163797 372815 := bstep (se 1 (by rfl) ⟨279611, by rfl⟩ : syracuseStep 372815 = 559223) B559223
theorem B471197 : Blo 163797 471197 := bstep (se 3 (by rfl) ⟨88349, by rfl⟩ : syracuseStep 471197 = 176699) B176699
theorem B602473 : Blo 163797 602473 := bstep (se 2 (by rfl) ⟨225927, by rfl⟩ : syracuseStep 602473 = 451855) B451855
theorem B373211 : Blo 163797 373211 := bstep (se 1 (by rfl) ⟨279908, by rfl⟩ : syracuseStep 373211 = 559817) B559817
theorem B602587 : Blo 163797 602587 := bstep (se 1 (by rfl) ⟨451940, by rfl⟩ : syracuseStep 602587 = 903881) B903881
theorem B602747 : Blo 163797 602747 := bstep (se 1 (by rfl) ⟨452060, by rfl⟩ : syracuseStep 602747 = 904121) B904121
theorem B504737 : Blo 163797 504737 := bstep (se 2 (by rfl) ⟨189276, by rfl⟩ : syracuseStep 504737 = 378553) B378553
theorem B635809 : Blo 163797 635809 := bstep (se 2 (by rfl) ⟨238428, by rfl⟩ : syracuseStep 635809 = 476857) B476857
theorem B373679 : Blo 163797 373679 := bstep (se 1 (by rfl) ⟨280259, by rfl⟩ : syracuseStep 373679 = 560519) B560519
theorem B210043 : Blo 163797 210043 := bstep (se 1 (by rfl) ⟨157532, by rfl⟩ : syracuseStep 210043 = 315065) B315065
theorem B373931 : Blo 163797 373931 := bstep (se 1 (by rfl) ⟨280448, by rfl⟩ : syracuseStep 373931 = 560897) B560897
theorem B210271 : Blo 163797 210271 := bstep (se 1 (by rfl) ⟨157703, by rfl⟩ : syracuseStep 210271 = 315407) B315407
theorem B4634003 : Blo 163797 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B2602405 : Blo 163797 2602405 := bstep (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) B487951
theorem B210395 : Blo 163797 210395 := bstep (se 1 (by rfl) ⟨157796, by rfl⟩ : syracuseStep 210395 = 315593) B315593
theorem B374471 : Blo 163797 374471 := bstep (se 1 (by rfl) ⟨280853, by rfl⟩ : syracuseStep 374471 = 561707) B561707
theorem B636767 : Blo 163797 636767 := bstep (se 1 (by rfl) ⟨477575, by rfl⟩ : syracuseStep 636767 = 955151) B955151
theorem B636781 : Blo 163797 636781 := bstep (se 3 (by rfl) ⟨119396, by rfl⟩ : syracuseStep 636781 = 238793) B238793
theorem B210863 : Blo 163797 210863 := bstep (se 1 (by rfl) ⟨158147, by rfl⟩ : syracuseStep 210863 = 316295) B316295
theorem B833651 : Blo 163797 833651 := bstep (se 1 (by rfl) ⟨625238, by rfl⟩ : syracuseStep 833651 = 1250477) B1250477
theorem B637085 : Blo 163797 637085 := bstep (se 3 (by rfl) ⟨119453, by rfl⟩ : syracuseStep 637085 = 238907) B238907
theorem B375335 : Blo 163797 375335 := bstep (se 1 (by rfl) ⟨281501, by rfl⟩ : syracuseStep 375335 = 563003) B563003
theorem B4340299 : Blo 163797 4340299 := bstep (se 1 (by rfl) ⟨3255224, by rfl⟩ : syracuseStep 4340299 = 6510449) B6510449
theorem B375659 : Blo 163797 375659 := bstep (se 1 (by rfl) ⟨281744, by rfl⟩ : syracuseStep 375659 = 563489) B563489
theorem B277391 : Blo 163797 277391 := bstep (se 1 (by rfl) ⟨208043, by rfl⟩ : syracuseStep 277391 = 416087) B416087
theorem B375713 : Blo 163797 375713 := bstep (se 2 (by rfl) ⟨140892, by rfl⟩ : syracuseStep 375713 = 281785) B281785
theorem B342967 : Blo 163797 342967 := bstep (se 1 (by rfl) ⟨257225, by rfl⟩ : syracuseStep 342967 = 514451) B514451
theorem B474169 : Blo 163797 474169 := bstep (se 2 (by rfl) ⟨177813, by rfl⟩ : syracuseStep 474169 = 355627) B355627
theorem B277627 : Blo 163797 277627 := bstep (se 1 (by rfl) ⟨208220, by rfl⟩ : syracuseStep 277627 = 416441) B416441
theorem B376055 : Blo 163797 376055 := bstep (se 1 (by rfl) ⟨282041, by rfl⟩ : syracuseStep 376055 = 564083) B564083
theorem B474511 : Blo 163797 474511 := bstep (se 1 (by rfl) ⟨355883, by rfl⟩ : syracuseStep 474511 = 711767) B711767
theorem B1883735 : Blo 163797 1883735 := bstep (se 1 (by rfl) ⟨1412801, by rfl⟩ : syracuseStep 1883735 = 2825603) B2825603
theorem B835271 : Blo 163797 835271 := bstep (se 1 (by rfl) ⟨626453, by rfl⟩ : syracuseStep 835271 = 1252907) B1252907
theorem B311033 : Blo 163797 311033 := bstep (se 2 (by rfl) ⟨116637, by rfl⟩ : syracuseStep 311033 = 233275) B233275
theorem B376649 : Blo 163797 376649 := bstep (se 2 (by rfl) ⟨141243, by rfl⟩ : syracuseStep 376649 = 282487) B282487
theorem B704351 : Blo 163797 704351 := bstep (se 1 (by rfl) ⟨528263, by rfl⟩ : syracuseStep 704351 = 1056527) B1056527
theorem B311215 : Blo 163797 311215 := bstep (se 1 (by rfl) ⟨233411, by rfl⟩ : syracuseStep 311215 = 466823) B466823
theorem B245723 : Blo 163797 245723 := bstep (se 1 (by rfl) ⟨184292, by rfl⟩ : syracuseStep 245723 = 368585) B368585
theorem B278491 : Blo 163797 278491 := bstep (se 1 (by rfl) ⟨208868, by rfl⟩ : syracuseStep 278491 = 417737) B417737
theorem B246191 : Blo 163797 246191 := bstep (se 1 (by rfl) ⟨184643, by rfl⟩ : syracuseStep 246191 = 369287) B369287
theorem B246281 : Blo 163797 246281 := bstep (se 2 (by rfl) ⟨92355, by rfl⟩ : syracuseStep 246281 = 184711) B184711
theorem B246311 : Blo 163797 246311 := bstep (se 1 (by rfl) ⟨184733, by rfl⟩ : syracuseStep 246311 = 369467) B369467
theorem B279119 : Blo 163797 279119 := bstep (se 1 (by rfl) ⟨209339, by rfl⟩ : syracuseStep 279119 = 418679) B418679
theorem B377441 : Blo 163797 377441 := bstep (se 2 (by rfl) ⟨141540, by rfl⟩ : syracuseStep 377441 = 283081) B283081
theorem B246395 : Blo 163797 246395 := bstep (se 1 (by rfl) ⟨184796, by rfl⟩ : syracuseStep 246395 = 369593) B369593
theorem B475787 : Blo 163797 475787 := bstep (se 1 (by rfl) ⟨356840, by rfl⟩ : syracuseStep 475787 = 713681) B713681
theorem B246521 : Blo 163797 246521 := bstep (se 2 (by rfl) ⟨92445, by rfl⟩ : syracuseStep 246521 = 184891) B184891
theorem B1786697 : Blo 163797 1786697 := bstep (se 2 (by rfl) ⟨670011, by rfl⟩ : syracuseStep 1786697 = 1340023) B1340023
theorem B246623 : Blo 163797 246623 := bstep (se 1 (by rfl) ⟨184967, by rfl⟩ : syracuseStep 246623 = 369935) B369935
theorem B246635 : Blo 163797 246635 := bstep (se 1 (by rfl) ⟨184976, by rfl⟩ : syracuseStep 246635 = 369953) B369953
theorem B443323 : Blo 163797 443323 := bstep (se 1 (by rfl) ⟨332492, by rfl⟩ : syracuseStep 443323 = 664985) B664985
theorem B246863 : Blo 163797 246863 := bstep (se 1 (by rfl) ⟨185147, by rfl⟩ : syracuseStep 246863 = 370295) B370295
theorem B541811 : Blo 163797 541811 := bstep (se 1 (by rfl) ⟨406358, by rfl⟩ : syracuseStep 541811 = 812717) B812717
theorem B312491 : Blo 163797 312491 := bstep (se 1 (by rfl) ⟨234368, by rfl⟩ : syracuseStep 312491 = 468737) B468737
theorem B246983 : Blo 163797 246983 := bstep (se 1 (by rfl) ⟨185237, by rfl⟩ : syracuseStep 246983 = 370475) B370475
theorem B247145 : Blo 163797 247145 := bstep (se 2 (by rfl) ⟨92679, by rfl⟩ : syracuseStep 247145 = 185359) B185359
theorem B279983 : Blo 163797 279983 := bstep (se 1 (by rfl) ⟨209987, by rfl⟩ : syracuseStep 279983 = 419975) B419975
theorem B247223 : Blo 163797 247223 := bstep (se 1 (by rfl) ⟨185417, by rfl⟩ : syracuseStep 247223 = 370835) B370835
theorem B247259 : Blo 163797 247259 := bstep (se 1 (by rfl) ⟨185444, by rfl⟩ : syracuseStep 247259 = 370889) B370889
theorem B673289 : Blo 163797 673289 := bstep (se 2 (by rfl) ⟨252483, by rfl⟩ : syracuseStep 673289 = 504967) B504967
theorem B4277771 : Blo 163797 4277771 := bstep (se 1 (by rfl) ⟨3208328, by rfl⟩ : syracuseStep 4277771 = 6416657) B6416657
theorem B673579 : Blo 163797 673579 := bstep (se 1 (by rfl) ⟨505184, by rfl⟩ : syracuseStep 673579 = 1010369) B1010369
theorem B280415 : Blo 163797 280415 := bstep (se 1 (by rfl) ⟨210311, by rfl⟩ : syracuseStep 280415 = 420623) B420623
theorem B247727 : Blo 163797 247727 := bstep (se 1 (by rfl) ⟨185795, by rfl⟩ : syracuseStep 247727 = 371591) B371591
theorem B247817 : Blo 163797 247817 := bstep (se 2 (by rfl) ⟨92931, by rfl⟩ : syracuseStep 247817 = 185863) B185863
theorem B247847 : Blo 163797 247847 := bstep (se 1 (by rfl) ⟨185885, by rfl⟩ : syracuseStep 247847 = 371771) B371771
theorem B247931 : Blo 163797 247931 := bstep (se 1 (by rfl) ⟨185948, by rfl⟩ : syracuseStep 247931 = 371897) B371897
theorem B1067165 : Blo 163797 1067165 := bstep (se 3 (by rfl) ⟨200093, by rfl⟩ : syracuseStep 1067165 = 400187) B400187
theorem B248057 : Blo 163797 248057 := bstep (se 2 (by rfl) ⟨93021, by rfl⟩ : syracuseStep 248057 = 186043) B186043
theorem B248159 : Blo 163797 248159 := bstep (se 1 (by rfl) ⟨186119, by rfl⟩ : syracuseStep 248159 = 372239) B372239
theorem B248171 : Blo 163797 248171 := bstep (se 1 (by rfl) ⟨186128, by rfl⟩ : syracuseStep 248171 = 372257) B372257
theorem B1067393 : Blo 163797 1067393 := bstep (se 2 (by rfl) ⟨400272, by rfl⟩ : syracuseStep 1067393 = 800545) B800545
theorem B280975 : Blo 163797 280975 := bstep (se 1 (by rfl) ⟨210731, by rfl⟩ : syracuseStep 280975 = 421463) B421463
theorem B313865 : Blo 163797 313865 := bstep (se 2 (by rfl) ⟨117699, by rfl⟩ : syracuseStep 313865 = 235399) B235399
theorem B3590689 : Blo 163797 3590689 := bstep (se 2 (by rfl) ⟨1346508, by rfl⟩ : syracuseStep 3590689 = 2693017) B2693017
theorem B313895 : Blo 163797 313895 := bstep (se 1 (by rfl) ⟨235421, by rfl⟩ : syracuseStep 313895 = 470843) B470843
theorem B248399 : Blo 163797 248399 := bstep (se 1 (by rfl) ⟨186299, by rfl⟩ : syracuseStep 248399 = 372599) B372599
theorem B1788601 : Blo 163797 1788601 := bstep (se 2 (by rfl) ⟨670725, by rfl⟩ : syracuseStep 1788601 = 1341451) B1341451
theorem B248519 : Blo 163797 248519 := bstep (se 1 (by rfl) ⟨186389, by rfl⟩ : syracuseStep 248519 = 372779) B372779
theorem B4410085 : Blo 163797 4410085 := bstep (se 4 (by rfl) ⟨413445, by rfl⟩ : syracuseStep 4410085 = 826891) B826891
theorem B248681 : Blo 163797 248681 := bstep (se 2 (by rfl) ⟨93255, by rfl⟩ : syracuseStep 248681 = 186511) B186511
theorem B248759 : Blo 163797 248759 := bstep (se 1 (by rfl) ⟨186569, by rfl⟩ : syracuseStep 248759 = 373139) B373139
theorem B2214839 : Blo 163797 2214839 := bstep (se 1 (by rfl) ⟨1661129, by rfl⟩ : syracuseStep 2214839 = 3322259) B3322259
theorem B248795 : Blo 163797 248795 := bstep (se 1 (by rfl) ⟨186596, by rfl⟩ : syracuseStep 248795 = 373193) B373193
theorem B281657 : Blo 163797 281657 := bstep (se 2 (by rfl) ⟨105621, by rfl⟩ : syracuseStep 281657 = 211243) B211243
theorem B314579 : Blo 163797 314579 := bstep (se 1 (by rfl) ⟨235934, by rfl⟩ : syracuseStep 314579 = 471869) B471869
theorem B314617 : Blo 163797 314617 := bstep (se 2 (by rfl) ⟨117981, by rfl⟩ : syracuseStep 314617 = 235963) B235963
theorem B281951 : Blo 163797 281951 := bstep (se 1 (by rfl) ⟨211463, by rfl⟩ : syracuseStep 281951 = 422927) B422927
theorem B249263 : Blo 163797 249263 := bstep (se 1 (by rfl) ⟨186947, by rfl⟩ : syracuseStep 249263 = 373895) B373895
theorem B708041 : Blo 163797 708041 := bstep (se 2 (by rfl) ⟨265515, by rfl⟩ : syracuseStep 708041 = 531031) B531031
theorem B249353 : Blo 163797 249353 := bstep (se 2 (by rfl) ⟨93507, by rfl⟩ : syracuseStep 249353 = 187015) B187015
theorem B249383 : Blo 163797 249383 := bstep (se 1 (by rfl) ⟨187037, by rfl⟩ : syracuseStep 249383 = 374075) B374075
theorem B249467 : Blo 163797 249467 := bstep (se 1 (by rfl) ⟨187100, by rfl⟩ : syracuseStep 249467 = 374201) B374201
theorem B282359 : Blo 163797 282359 := bstep (se 1 (by rfl) ⟨211769, by rfl⟩ : syracuseStep 282359 = 423539) B423539
theorem B249593 : Blo 163797 249593 := bstep (se 2 (by rfl) ⟨93597, by rfl⟩ : syracuseStep 249593 = 187195) B187195
theorem B249695 : Blo 163797 249695 := bstep (se 1 (by rfl) ⟨187271, by rfl⟩ : syracuseStep 249695 = 374543) B374543
theorem B249707 : Blo 163797 249707 := bstep (se 1 (by rfl) ⟨187280, by rfl⟩ : syracuseStep 249707 = 374561) B374561
theorem B1265543 : Blo 163797 1265543 := bstep (se 1 (by rfl) ⟨949157, by rfl⟩ : syracuseStep 1265543 = 1898315) B1898315
theorem B315323 : Blo 163797 315323 := bstep (se 1 (by rfl) ⟨236492, by rfl⟩ : syracuseStep 315323 = 472985) B472985
theorem B249935 : Blo 163797 249935 := bstep (se 1 (by rfl) ⟨187451, by rfl⟩ : syracuseStep 249935 = 374903) B374903
theorem B282703 : Blo 163797 282703 := bstep (se 1 (by rfl) ⟨212027, by rfl⟩ : syracuseStep 282703 = 424055) B424055
theorem B8605777 : Blo 163797 8605777 := bstep (se 2 (by rfl) ⟨3227166, by rfl⟩ : syracuseStep 8605777 = 6454333) B6454333
theorem B250055 : Blo 163797 250055 := bstep (se 1 (by rfl) ⟨187541, by rfl⟩ : syracuseStep 250055 = 375083) B375083
theorem B282953 : Blo 163797 282953 := bstep (se 2 (by rfl) ⟨106107, by rfl⟩ : syracuseStep 282953 = 212215) B212215
theorem B250217 : Blo 163797 250217 := bstep (se 2 (by rfl) ⟨93831, by rfl⟩ : syracuseStep 250217 = 187663) B187663
theorem B315809 : Blo 163797 315809 := bstep (se 2 (by rfl) ⟨118428, by rfl⟩ : syracuseStep 315809 = 236857) B236857
theorem B250295 : Blo 163797 250295 := bstep (se 1 (by rfl) ⟨187721, by rfl⟩ : syracuseStep 250295 = 375443) B375443
theorem B283099 : Blo 163797 283099 := bstep (se 1 (by rfl) ⟨212324, by rfl⟩ : syracuseStep 283099 = 424649) B424649
theorem B250331 : Blo 163797 250331 := bstep (se 1 (by rfl) ⟨187748, by rfl⟩ : syracuseStep 250331 = 375497) B375497
theorem B316075 : Blo 163797 316075 := bstep (se 1 (by rfl) ⟨237056, by rfl⟩ : syracuseStep 316075 = 474113) B474113
theorem B250799 : Blo 163797 250799 := bstep (se 1 (by rfl) ⟨188099, by rfl⟩ : syracuseStep 250799 = 376199) B376199
theorem B316379 : Blo 163797 316379 := bstep (se 1 (by rfl) ⟨237284, by rfl⟩ : syracuseStep 316379 = 474569) B474569
theorem B2249693 : Blo 163797 2249693 := bstep (se 3 (by rfl) ⟨421817, by rfl⟩ : syracuseStep 2249693 = 843635) B843635
theorem B250889 : Blo 163797 250889 := bstep (se 2 (by rfl) ⟨94083, by rfl⟩ : syracuseStep 250889 = 188167) B188167
theorem B250919 : Blo 163797 250919 := bstep (se 1 (by rfl) ⟨188189, by rfl⟩ : syracuseStep 250919 = 376379) B376379
theorem B185467 : Blo 163797 185467 := bstep (se 1 (by rfl) ⟨139100, by rfl⟩ : syracuseStep 185467 = 278201) B278201
theorem B251003 : Blo 163797 251003 := bstep (se 1 (by rfl) ⟨188252, by rfl⟩ : syracuseStep 251003 = 376505) B376505
theorem B251129 : Blo 163797 251129 := bstep (se 2 (by rfl) ⟨94173, by rfl⟩ : syracuseStep 251129 = 188347) B188347
theorem B251231 : Blo 163797 251231 := bstep (se 1 (by rfl) ⟨188423, by rfl⟩ : syracuseStep 251231 = 376847) B376847
theorem B251243 : Blo 163797 251243 := bstep (se 1 (by rfl) ⟨188432, by rfl⟩ : syracuseStep 251243 = 376865) B376865
theorem B841103 : Blo 163797 841103 := bstep (se 1 (by rfl) ⟨630827, by rfl⟩ : syracuseStep 841103 = 1261655) B1261655
theorem B185935 : Blo 163797 185935 := bstep (se 1 (by rfl) ⟨139451, by rfl⟩ : syracuseStep 185935 = 278903) B278903
theorem B251471 : Blo 163797 251471 := bstep (se 1 (by rfl) ⟨188603, by rfl⟩ : syracuseStep 251471 = 377207) B377207
theorem B251591 : Blo 163797 251591 := bstep (se 1 (by rfl) ⟨188693, by rfl⟩ : syracuseStep 251591 = 377387) B377387
theorem B1431391 : Blo 163797 1431391 := bstep (se 1 (by rfl) ⟨1073543, by rfl⟩ : syracuseStep 1431391 = 2147087) B2147087
theorem B186331 : Blo 163797 186331 := bstep (se 1 (by rfl) ⟨139748, by rfl⟩ : syracuseStep 186331 = 279497) B279497
theorem B317449 : Blo 163797 317449 := bstep (se 2 (by rfl) ⟨119043, by rfl⟩ : syracuseStep 317449 = 238087) B238087
theorem B415763 : Blo 163797 415763 := bstep (se 1 (by rfl) ⟨311822, by rfl⟩ : syracuseStep 415763 = 623645) B623645
theorem B317803 : Blo 163797 317803 := bstep (se 1 (by rfl) ⟨238352, by rfl⟩ : syracuseStep 317803 = 476705) B476705
theorem B1628549 : Blo 163797 1628549 := bstep (se 4 (by rfl) ⟨152676, by rfl⟩ : syracuseStep 1628549 = 305353) B305353
theorem B186799 : Blo 163797 186799 := bstep (se 1 (by rfl) ⟨140099, by rfl⟩ : syracuseStep 186799 = 280199) B280199
theorem B1333793 : Blo 163797 1333793 := bstep (se 2 (by rfl) ⟨500172, by rfl⟩ : syracuseStep 1333793 = 1000345) B1000345
theorem B481889 : Blo 163797 481889 := bstep (se 2 (by rfl) ⟨180708, by rfl⟩ : syracuseStep 481889 = 361417) B361417
theorem B1071751 : Blo 163797 1071751 := bstep (se 1 (by rfl) ⟨803813, by rfl⟩ : syracuseStep 1071751 = 1607627) B1607627
theorem B318163 : Blo 163797 318163 := bstep (se 1 (by rfl) ⟨238622, by rfl⟩ : syracuseStep 318163 = 477245) B477245
theorem B1432349 : Blo 163797 1432349 := bstep (se 3 (by rfl) ⟨268565, by rfl⟩ : syracuseStep 1432349 = 537131) B537131
theorem B187231 : Blo 163797 187231 := bstep (se 1 (by rfl) ⟨140423, by rfl⟩ : syracuseStep 187231 = 280847) B280847
theorem B711607 : Blo 163797 711607 := bstep (se 1 (by rfl) ⟨533705, by rfl⟩ : syracuseStep 711607 = 1067411) B1067411
theorem B449615 : Blo 163797 449615 := bstep (se 1 (by rfl) ⟨337211, by rfl⟩ : syracuseStep 449615 = 674423) B674423
theorem B187591 : Blo 163797 187591 := bstep (se 1 (by rfl) ⟨140693, by rfl⟩ : syracuseStep 187591 = 281387) B281387
theorem B843209 : Blo 163797 843209 := bstep (se 2 (by rfl) ⟨316203, by rfl⟩ : syracuseStep 843209 = 632407) B632407
theorem B352073 : Blo 163797 352073 := bstep (se 2 (by rfl) ⟨132027, by rfl⟩ : syracuseStep 352073 = 264055) B264055
theorem B286651 : Blo 163797 286651 := bstep (se 1 (by rfl) ⟨214988, by rfl⟩ : syracuseStep 286651 = 429977) B429977
theorem B2285597 : Blo 163797 2285597 := bstep (se 3 (by rfl) ⟨428549, by rfl⟩ : syracuseStep 2285597 = 857099) B857099
theorem B1204253 : Blo 163797 1204253 := bstep (se 3 (by rfl) ⟨225797, by rfl⟩ : syracuseStep 1204253 = 451595) B451595
theorem B188455 : Blo 163797 188455 := bstep (se 1 (by rfl) ⟨141341, by rfl⟩ : syracuseStep 188455 = 282683) B282683
theorem B843857 : Blo 163797 843857 := bstep (se 2 (by rfl) ⟨316446, by rfl⟩ : syracuseStep 843857 = 632893) B632893
theorem B1269917 : Blo 163797 1269917 := bstep (se 3 (by rfl) ⟨238109, by rfl⟩ : syracuseStep 1269917 = 476219) B476219
theorem B419215 : Blo 163797 419215 := bstep (se 1 (by rfl) ⟨314411, by rfl⟩ : syracuseStep 419215 = 628823) B628823
theorem B1598939 : Blo 163797 1598939 := bstep (se 1 (by rfl) ⟨1199204, by rfl⟩ : syracuseStep 1598939 = 2398409) B2398409
theorem B419539 : Blo 163797 419539 := bstep (se 1 (by rfl) ⟨314654, by rfl⟩ : syracuseStep 419539 = 629309) B629309
theorem B1075079 : Blo 163797 1075079 := bstep (se 1 (by rfl) ⟨806309, by rfl⟩ : syracuseStep 1075079 = 1612619) B1612619
theorem B452513 : Blo 163797 452513 := bstep (se 2 (by rfl) ⟨169692, by rfl⟩ : syracuseStep 452513 = 339385) B339385
theorem B1206353 : Blo 163797 1206353 := bstep (se 2 (by rfl) ⟨452382, by rfl⟩ : syracuseStep 1206353 = 904765) B904765
theorem B420491 : Blo 163797 420491 := bstep (se 1 (by rfl) ⟨315368, by rfl⟩ : syracuseStep 420491 = 630737) B630737
theorem B1272833 : Blo 163797 1272833 := bstep (se 2 (by rfl) ⟨477312, by rfl⟩ : syracuseStep 1272833 = 954625) B954625
theorem B421625 : Blo 163797 421625 := bstep (se 2 (by rfl) ⟨158109, by rfl⟩ : syracuseStep 421625 = 316219) B316219
theorem B356089 : Blo 163797 356089 := bstep (se 2 (by rfl) ⟨133533, by rfl⟩ : syracuseStep 356089 = 267067) B267067
theorem B17592227 : Blo 163797 17592227 := bstep (se 1 (by rfl) ⟨13194170, by rfl⟩ : syracuseStep 17592227 = 26388341) B26388341
theorem B421807 : Blo 163797 421807 := bstep (se 1 (by rfl) ⟨316355, by rfl⟩ : syracuseStep 421807 = 632711) B632711
theorem B323947 : Blo 163797 323947 := bstep (se 1 (by rfl) ⟨242960, by rfl⟩ : syracuseStep 323947 = 485921) B485921
theorem B422273 : Blo 163797 422273 := bstep (se 2 (by rfl) ⟨158352, by rfl⟩ : syracuseStep 422273 = 316705) B316705
theorem B848393 : Blo 163797 848393 := bstep (se 2 (by rfl) ⟨318147, by rfl⟩ : syracuseStep 848393 = 636295) B636295
theorem B553607 : Blo 163797 553607 := bstep (se 1 (by rfl) ⟨415205, by rfl⟩ : syracuseStep 553607 = 830411) B830411
theorem B553661 : Blo 163797 553661 := bstep (se 3 (by rfl) ⟨103811, by rfl⟩ : syracuseStep 553661 = 207623) B207623
theorem B422729 : Blo 163797 422729 := bstep (se 2 (by rfl) ⟨158523, by rfl⟩ : syracuseStep 422729 = 317047) B317047
theorem B553823 : Blo 163797 553823 := bstep (se 1 (by rfl) ⟨415367, by rfl⟩ : syracuseStep 553823 = 830735) B830735
theorem B553985 : Blo 163797 553985 := bstep (se 2 (by rfl) ⟨207744, by rfl⟩ : syracuseStep 553985 = 415489) B415489
theorem B1406105 : Blo 163797 1406105 := bstep (se 2 (by rfl) ⟨527289, by rfl⟩ : syracuseStep 1406105 = 1054579) B1054579
theorem B423083 : Blo 163797 423083 := bstep (se 1 (by rfl) ⟨317312, by rfl⟩ : syracuseStep 423083 = 634625) B634625
theorem B2880715 : Blo 163797 2880715 := bstep (se 1 (by rfl) ⟨2160536, by rfl⟩ : syracuseStep 2880715 = 4321073) B4321073
theorem B750973 : Blo 163797 750973 := bstep (se 3 (by rfl) ⟨140807, by rfl⟩ : syracuseStep 750973 = 281615) B281615
theorem B1340873 : Blo 163797 1340873 := bstep (se 2 (by rfl) ⟨502827, by rfl⟩ : syracuseStep 1340873 = 1005655) B1005655
theorem B423623 : Blo 163797 423623 := bstep (se 1 (by rfl) ⟨317717, by rfl⟩ : syracuseStep 423623 = 635435) B635435
theorem B9565937 : Blo 163797 9565937 := bstep (se 2 (by rfl) ⟨3587226, by rfl⟩ : syracuseStep 9565937 = 7174453) B7174453
theorem B554795 : Blo 163797 554795 := bstep (se 1 (by rfl) ⟨416096, by rfl⟩ : syracuseStep 554795 = 832193) B832193
theorem B358319 : Blo 163797 358319 := bstep (se 1 (by rfl) ⟨268739, by rfl⟩ : syracuseStep 358319 = 537479) B537479
theorem B423863 : Blo 163797 423863 := bstep (se 1 (by rfl) ⟨317897, by rfl⟩ : syracuseStep 423863 = 635795) B635795
theorem B555065 : Blo 163797 555065 := bstep (se 2 (by rfl) ⟨208149, by rfl⟩ : syracuseStep 555065 = 416299) B416299
theorem B555389 : Blo 163797 555389 := bstep (se 3 (by rfl) ⟨104135, by rfl⟩ : syracuseStep 555389 = 208271) B208271
theorem B555659 : Blo 163797 555659 := bstep (se 1 (by rfl) ⟨416744, by rfl⟩ : syracuseStep 555659 = 833489) B833489
theorem B1080067 : Blo 163797 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B556577 : Blo 163797 556577 := bstep (se 2 (by rfl) ⟨208716, by rfl⟩ : syracuseStep 556577 = 417433) B417433
theorem B1212043 : Blo 163797 1212043 := bstep (se 1 (by rfl) ⟨909032, by rfl⟩ : syracuseStep 1212043 = 1818065) B1818065
theorem B556793 : Blo 163797 556793 := bstep (se 2 (by rfl) ⟨208797, by rfl⟩ : syracuseStep 556793 = 417595) B417595
theorem B163803 : Blo 163797 163803 := bstep (se 1 (by rfl) ⟨122852, by rfl⟩ : syracuseStep 163803 = 245705) B245705
theorem B164127 : Blo 163797 164127 := bstep (se 1 (by rfl) ⟨123095, by rfl⟩ : syracuseStep 164127 = 246191) B246191
theorem B164187 : Blo 163797 164187 := bstep (se 1 (by rfl) ⟨123140, by rfl⟩ : syracuseStep 164187 = 246281) B246281
theorem B164207 : Blo 163797 164207 := bstep (se 1 (by rfl) ⟨123155, by rfl⟩ : syracuseStep 164207 = 246311) B246311
theorem B164263 : Blo 163797 164263 := bstep (se 1 (by rfl) ⟨123197, by rfl⟩ : syracuseStep 164263 = 246395) B246395
theorem B164347 : Blo 163797 164347 := bstep (se 1 (by rfl) ⟨123260, by rfl⟩ : syracuseStep 164347 = 246521) B246521
theorem B164415 : Blo 163797 164415 := bstep (se 1 (by rfl) ⟨123311, by rfl⟩ : syracuseStep 164415 = 246623) B246623
theorem B164423 : Blo 163797 164423 := bstep (se 1 (by rfl) ⟨123317, by rfl⟩ : syracuseStep 164423 = 246635) B246635
theorem B393835 : Blo 163797 393835 := bstep (se 1 (by rfl) ⟨295376, by rfl⟩ : syracuseStep 393835 = 590753) B590753
theorem B524971 : Blo 163797 524971 := bstep (se 1 (by rfl) ⟨393728, by rfl⟩ : syracuseStep 524971 = 787457) B787457
theorem B524983 : Blo 163797 524983 := bstep (se 1 (by rfl) ⟨393737, by rfl⟩ : syracuseStep 524983 = 787475) B787475
theorem B393911 : Blo 163797 393911 := bstep (se 1 (by rfl) ⟨295433, by rfl⟩ : syracuseStep 393911 = 590867) B590867
theorem B164575 : Blo 163797 164575 := bstep (se 1 (by rfl) ⟨123431, by rfl⟩ : syracuseStep 164575 = 246863) B246863
theorem B361207 : Blo 163797 361207 := bstep (se 1 (by rfl) ⟨270905, by rfl⟩ : syracuseStep 361207 = 541811) B541811
theorem B164655 : Blo 163797 164655 := bstep (se 1 (by rfl) ⟨123491, by rfl⟩ : syracuseStep 164655 = 246983) B246983
theorem B164763 : Blo 163797 164763 := bstep (se 1 (by rfl) ⟨123572, by rfl⟩ : syracuseStep 164763 = 247145) B247145
theorem B164815 : Blo 163797 164815 := bstep (se 1 (by rfl) ⟨123611, by rfl⟩ : syracuseStep 164815 = 247223) B247223
theorem B164839 : Blo 163797 164839 := bstep (se 1 (by rfl) ⟨123629, by rfl⟩ : syracuseStep 164839 = 247259) B247259
theorem B2851847 : Blo 163797 2851847 := bstep (se 1 (by rfl) ⟨2138885, by rfl⟩ : syracuseStep 2851847 = 4277771) B4277771
theorem B787553 : Blo 163797 787553 := bstep (se 2 (by rfl) ⟨295332, by rfl⟩ : syracuseStep 787553 = 590665) B590665
theorem B165151 : Blo 163797 165151 := bstep (se 1 (by rfl) ⟨123863, by rfl⟩ : syracuseStep 165151 = 247727) B247727
theorem B165211 : Blo 163797 165211 := bstep (se 1 (by rfl) ⟨123908, by rfl⟩ : syracuseStep 165211 = 247817) B247817
theorem B165231 : Blo 163797 165231 := bstep (se 1 (by rfl) ⟨123923, by rfl⟩ : syracuseStep 165231 = 247847) B247847
theorem B165287 : Blo 163797 165287 := bstep (se 1 (by rfl) ⟨123965, by rfl⟩ : syracuseStep 165287 = 247931) B247931
theorem B165371 : Blo 163797 165371 := bstep (se 1 (by rfl) ⟨124028, by rfl⟩ : syracuseStep 165371 = 248057) B248057
theorem B165439 : Blo 163797 165439 := bstep (se 1 (by rfl) ⟨124079, by rfl⟩ : syracuseStep 165439 = 248159) B248159
theorem B165447 : Blo 163797 165447 := bstep (se 1 (by rfl) ⟨124085, by rfl⟩ : syracuseStep 165447 = 248171) B248171
theorem B165599 : Blo 163797 165599 := bstep (se 1 (by rfl) ⟨124199, by rfl⟩ : syracuseStep 165599 = 248399) B248399
theorem B165679 : Blo 163797 165679 := bstep (se 1 (by rfl) ⟨124259, by rfl⟩ : syracuseStep 165679 = 248519) B248519
theorem B198455 : Blo 163797 198455 := bstep (se 1 (by rfl) ⟨148841, by rfl⟩ : syracuseStep 198455 = 297683) B297683
theorem B395113 : Blo 163797 395113 := bstep (se 2 (by rfl) ⟨148167, by rfl⟩ : syracuseStep 395113 = 296335) B296335
theorem B558953 : Blo 163797 558953 := bstep (se 2 (by rfl) ⟨209607, by rfl⟩ : syracuseStep 558953 = 419215) B419215
theorem B165787 : Blo 163797 165787 := bstep (se 1 (by rfl) ⟨124340, by rfl⟩ : syracuseStep 165787 = 248681) B248681
theorem B165839 : Blo 163797 165839 := bstep (se 1 (by rfl) ⟨124379, by rfl⟩ : syracuseStep 165839 = 248759) B248759
theorem B1476559 : Blo 163797 1476559 := bstep (se 1 (by rfl) ⟨1107419, by rfl⟩ : syracuseStep 1476559 = 2214839) B2214839
theorem B165863 : Blo 163797 165863 := bstep (se 1 (by rfl) ⟨124397, by rfl⟩ : syracuseStep 165863 = 248795) B248795
theorem B3606605 : Blo 163797 3606605 := bstep (se 3 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 3606605 = 1352477) B1352477
theorem B624905 : Blo 163797 624905 := bstep (se 2 (by rfl) ⟨234339, by rfl⟩ : syracuseStep 624905 = 468679) B468679
theorem B559385 : Blo 163797 559385 := bstep (se 2 (by rfl) ⟨209769, by rfl⟩ : syracuseStep 559385 = 419539) B419539
theorem B166175 : Blo 163797 166175 := bstep (se 1 (by rfl) ⟨124631, by rfl⟩ : syracuseStep 166175 = 249263) B249263
theorem B166235 : Blo 163797 166235 := bstep (se 1 (by rfl) ⟨124676, by rfl⟩ : syracuseStep 166235 = 249353) B249353
theorem B166255 : Blo 163797 166255 := bstep (se 1 (by rfl) ⟨124691, by rfl⟩ : syracuseStep 166255 = 249383) B249383
theorem B166311 : Blo 163797 166311 := bstep (se 1 (by rfl) ⟨124733, by rfl⟩ : syracuseStep 166311 = 249467) B249467
theorem B166395 : Blo 163797 166395 := bstep (se 1 (by rfl) ⟨124796, by rfl⟩ : syracuseStep 166395 = 249593) B249593
theorem B166463 : Blo 163797 166463 := bstep (se 1 (by rfl) ⟨124847, by rfl⟩ : syracuseStep 166463 = 249695) B249695
theorem B166471 : Blo 163797 166471 := bstep (se 1 (by rfl) ⟨124853, by rfl⟩ : syracuseStep 166471 = 249707) B249707
theorem B166623 : Blo 163797 166623 := bstep (se 1 (by rfl) ⟨124967, by rfl⟩ : syracuseStep 166623 = 249935) B249935
theorem B5442349 : Blo 163797 5442349 := bstep (se 3 (by rfl) ⟨1020440, by rfl⟩ : syracuseStep 5442349 = 2040881) B2040881
theorem B166703 : Blo 163797 166703 := bstep (se 1 (by rfl) ⟨125027, by rfl⟩ : syracuseStep 166703 = 250055) B250055
theorem B1182599 : Blo 163797 1182599 := bstep (se 1 (by rfl) ⟨886949, by rfl⟩ : syracuseStep 1182599 = 1773899) B1773899
theorem B166811 : Blo 163797 166811 := bstep (se 1 (by rfl) ⟨125108, by rfl⟩ : syracuseStep 166811 = 250217) B250217
theorem B166863 : Blo 163797 166863 := bstep (se 1 (by rfl) ⟨125147, by rfl⟩ : syracuseStep 166863 = 250295) B250295
theorem B166887 : Blo 163797 166887 := bstep (se 1 (by rfl) ⟨125165, by rfl⟩ : syracuseStep 166887 = 250331) B250331
theorem B167199 : Blo 163797 167199 := bstep (se 1 (by rfl) ⟨125399, by rfl⟩ : syracuseStep 167199 = 250799) B250799
theorem B167259 : Blo 163797 167259 := bstep (se 1 (by rfl) ⟨125444, by rfl⟩ : syracuseStep 167259 = 250889) B250889
theorem B167279 : Blo 163797 167279 := bstep (se 1 (by rfl) ⟨125459, by rfl⟩ : syracuseStep 167279 = 250919) B250919
theorem B4787585 : Blo 163797 4787585 := bstep (se 2 (by rfl) ⟨1795344, by rfl⟩ : syracuseStep 4787585 = 3590689) B3590689
theorem B167335 : Blo 163797 167335 := bstep (se 1 (by rfl) ⟨125501, by rfl⟩ : syracuseStep 167335 = 251003) B251003
theorem B167419 : Blo 163797 167419 := bstep (se 1 (by rfl) ⟨125564, by rfl⟩ : syracuseStep 167419 = 251129) B251129
theorem B167487 : Blo 163797 167487 := bstep (se 1 (by rfl) ⟨125615, by rfl⟩ : syracuseStep 167487 = 251231) B251231
theorem B167495 : Blo 163797 167495 := bstep (se 1 (by rfl) ⟨125621, by rfl⟩ : syracuseStep 167495 = 251243) B251243
theorem B560735 : Blo 163797 560735 := bstep (se 1 (by rfl) ⟨420551, by rfl⟩ : syracuseStep 560735 = 841103) B841103
theorem B167647 : Blo 163797 167647 := bstep (se 1 (by rfl) ⟨125735, by rfl⟩ : syracuseStep 167647 = 251471) B251471
theorem B167727 : Blo 163797 167727 := bstep (se 1 (by rfl) ⟨125795, by rfl⟩ : syracuseStep 167727 = 251591) B251591
theorem B626561 : Blo 163797 626561 := bstep (se 2 (by rfl) ⟨234960, by rfl⟩ : syracuseStep 626561 = 469921) B469921
theorem B561053 : Blo 163797 561053 := bstep (se 3 (by rfl) ⟨105197, by rfl⟩ : syracuseStep 561053 = 210395) B210395
theorem B1085699 : Blo 163797 1085699 := bstep (se 1 (by rfl) ⟨814274, by rfl⟩ : syracuseStep 1085699 = 1628549) B1628549
theorem B954899 : Blo 163797 954899 := bstep (se 1 (by rfl) ⟨716174, by rfl⟩ : syracuseStep 954899 = 1432349) B1432349
theorem B1249991 : Blo 163797 1249991 := bstep (se 1 (by rfl) ⟨937493, by rfl⟩ : syracuseStep 1249991 = 1874987) B1874987
theorem B299743 : Blo 163797 299743 := bstep (se 1 (by rfl) ⟨224807, by rfl⟩ : syracuseStep 299743 = 449615) B449615
theorem B562139 : Blo 163797 562139 := bstep (se 1 (by rfl) ⟨421604, by rfl⟩ : syracuseStep 562139 = 843209) B843209
theorem B2364389 : Blo 163797 2364389 := bstep (se 4 (by rfl) ⟨221661, by rfl⟩ : syracuseStep 2364389 = 443323) B443323
theorem B562301 : Blo 163797 562301 := bstep (se 3 (by rfl) ⟨105431, by rfl⟩ : syracuseStep 562301 = 210863) B210863
theorem B759017 : Blo 163797 759017 := bstep (se 2 (by rfl) ⟨284631, by rfl⟩ : syracuseStep 759017 = 569263) B569263
theorem B562409 : Blo 163797 562409 := bstep (se 2 (by rfl) ⟨210903, by rfl⟩ : syracuseStep 562409 = 421807) B421807
theorem B562571 : Blo 163797 562571 := bstep (se 1 (by rfl) ⟨421928, by rfl⟩ : syracuseStep 562571 = 843857) B843857
theorem B11474369 : Blo 163797 11474369 := bstep (se 2 (by rfl) ⟨4302888, by rfl⟩ : syracuseStep 11474369 = 8605777) B8605777
theorem B3216941 : Blo 163797 3216941 := bstep (se 3 (by rfl) ⟨603176, by rfl⟩ : syracuseStep 3216941 = 1206353) B1206353
theorem B431929 : Blo 163797 431929 := bstep (se 2 (by rfl) ⟨161973, by rfl⟩ : syracuseStep 431929 = 323947) B323947
theorem B268553 : Blo 163797 268553 := bstep (se 2 (by rfl) ⟨100707, by rfl⟩ : syracuseStep 268553 = 201415) B201415
theorem B3545369 : Blo 163797 3545369 := bstep (se 2 (by rfl) ⟨1329513, by rfl⟩ : syracuseStep 3545369 = 2659027) B2659027
theorem B891773 : Blo 163797 891773 := bstep (se 3 (by rfl) ⟨167207, by rfl⟩ : syracuseStep 891773 = 334415) B334415
theorem B3840953 : Blo 163797 3840953 := bstep (se 2 (by rfl) ⟨1440357, by rfl⟩ : syracuseStep 3840953 = 2880715) B2880715
theorem B1908521 : Blo 163797 1908521 := bstep (se 2 (by rfl) ⟨715695, by rfl⟩ : syracuseStep 1908521 = 1431391) B1431391
theorem B1581065 : Blo 163797 1581065 := bstep (se 2 (by rfl) ⟨592899, by rfl⟩ : syracuseStep 1581065 = 1185799) B1185799
theorem B565595 : Blo 163797 565595 := bstep (se 1 (by rfl) ⟨424196, by rfl⟩ : syracuseStep 565595 = 848393) B848393
theorem B401831 : Blo 163797 401831 := bstep (se 1 (by rfl) ⟨301373, by rfl⟩ : syracuseStep 401831 = 602747) B602747
theorem B369071 : Blo 163797 369071 := bstep (se 1 (by rfl) ⟨276803, by rfl⟩ : syracuseStep 369071 = 553607) B553607
theorem B369107 : Blo 163797 369107 := bstep (se 1 (by rfl) ⟨276830, by rfl⟩ : syracuseStep 369107 = 553661) B553661
theorem B369215 : Blo 163797 369215 := bstep (se 1 (by rfl) ⟨276911, by rfl⟩ : syracuseStep 369215 = 553823) B553823
theorem B336491 : Blo 163797 336491 := bstep (se 1 (by rfl) ⟨252368, by rfl⟩ : syracuseStep 336491 = 504737) B504737
theorem B402041 : Blo 163797 402041 := bstep (se 2 (by rfl) ⟨150765, by rfl⟩ : syracuseStep 402041 = 301531) B301531
theorem B369323 : Blo 163797 369323 := bstep (se 1 (by rfl) ⟨276992, by rfl⟩ : syracuseStep 369323 = 553985) B553985
theorem B3089335 : Blo 163797 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B893915 : Blo 163797 893915 := bstep (se 1 (by rfl) ⟨670436, by rfl⟩ : syracuseStep 893915 = 1340873) B1340873
theorem B4007029 : Blo 163797 4007029 := bstep (se 5 (by rfl) ⟨187829, by rfl⟩ : syracuseStep 4007029 = 375659) B375659
theorem B369863 : Blo 163797 369863 := bstep (se 1 (by rfl) ⟨277397, by rfl⟩ : syracuseStep 369863 = 554795) B554795
theorem B238879 : Blo 163797 238879 := bstep (se 1 (by rfl) ⟨179159, by rfl⟩ : syracuseStep 238879 = 358319) B358319
theorem B370043 : Blo 163797 370043 := bstep (se 1 (by rfl) ⟨277532, by rfl⟩ : syracuseStep 370043 = 555065) B555065
theorem B632225 : Blo 163797 632225 := bstep (se 2 (by rfl) ⟨237084, by rfl⟩ : syracuseStep 632225 = 474169) B474169
theorem B370169 : Blo 163797 370169 := bstep (se 2 (by rfl) ⟨138813, by rfl⟩ : syracuseStep 370169 = 277627) B277627
theorem B370259 : Blo 163797 370259 := bstep (se 1 (by rfl) ⟨277694, by rfl⟩ : syracuseStep 370259 = 555389) B555389
theorem B370439 : Blo 163797 370439 := bstep (se 1 (by rfl) ⟨277829, by rfl⟩ : syracuseStep 370439 = 555659) B555659
theorem B632681 : Blo 163797 632681 := bstep (se 2 (by rfl) ⟨237255, by rfl⟩ : syracuseStep 632681 = 474511) B474511
theorem B403465 : Blo 163797 403465 := bstep (se 2 (by rfl) ⟨151299, by rfl⟩ : syracuseStep 403465 = 302599) B302599
theorem B1616057 : Blo 163797 1616057 := bstep (se 2 (by rfl) ⟨606021, by rfl⟩ : syracuseStep 1616057 = 1212043) B1212043
theorem B371051 : Blo 163797 371051 := bstep (se 1 (by rfl) ⟨278288, by rfl⟩ : syracuseStep 371051 = 556577) B556577
theorem B1255823 : Blo 163797 1255823 := bstep (se 1 (by rfl) ⟨941867, by rfl⟩ : syracuseStep 1255823 = 1883735) B1883735
theorem B207355 : Blo 163797 207355 := bstep (se 1 (by rfl) ⟨155516, by rfl⟩ : syracuseStep 207355 = 311033) B311033
theorem B371195 : Blo 163797 371195 := bstep (se 1 (by rfl) ⟨278396, by rfl⟩ : syracuseStep 371195 = 556793) B556793
theorem B469567 : Blo 163797 469567 := bstep (se 1 (by rfl) ⟨352175, by rfl⟩ : syracuseStep 469567 = 704351) B704351
theorem B371321 : Blo 163797 371321 := bstep (se 2 (by rfl) ⟨139245, by rfl⟩ : syracuseStep 371321 = 278491) B278491
theorem B371375 : Blo 163797 371375 := bstep (se 1 (by rfl) ⟨278531, by rfl⟩ : syracuseStep 371375 = 557063) B557063
theorem B371447 : Blo 163797 371447 := bstep (se 1 (by rfl) ⟨278585, by rfl⟩ : syracuseStep 371447 = 557171) B557171
theorem B371627 : Blo 163797 371627 := bstep (se 1 (by rfl) ⟨278720, by rfl⟩ : syracuseStep 371627 = 557441) B557441
theorem B1420253 : Blo 163797 1420253 := bstep (se 3 (by rfl) ⟨266297, by rfl⟩ : syracuseStep 1420253 = 532595) B532595
theorem B797777 : Blo 163797 797777 := bstep (se 2 (by rfl) ⟨299166, by rfl⟩ : syracuseStep 797777 = 598333) B598333
theorem B1191131 : Blo 163797 1191131 := bstep (se 1 (by rfl) ⟨893348, by rfl⟩ : syracuseStep 1191131 = 1786697) B1786697
theorem B208327 : Blo 163797 208327 := bstep (se 1 (by rfl) ⟨156245, by rfl⟩ : syracuseStep 208327 = 312491) B312491
theorem B372167 : Blo 163797 372167 := bstep (se 1 (by rfl) ⟨279125, by rfl⟩ : syracuseStep 372167 = 558251) B558251
theorem B831059 : Blo 163797 831059 := bstep (se 1 (by rfl) ⟨623294, by rfl⟩ : syracuseStep 831059 = 1246589) B1246589
theorem B2141963 : Blo 163797 2141963 := bstep (se 1 (by rfl) ⟨1606472, by rfl⟩ : syracuseStep 2141963 = 3212945) B3212945
theorem B372527 : Blo 163797 372527 := bstep (se 1 (by rfl) ⟨279395, by rfl⟩ : syracuseStep 372527 = 558791) B558791
theorem B175951 : Blo 163797 175951 := bstep (se 1 (by rfl) ⟨131963, by rfl⟩ : syracuseStep 175951 = 263927) B263927
theorem B209243 : Blo 163797 209243 := bstep (se 1 (by rfl) ⟨156932, by rfl⟩ : syracuseStep 209243 = 313865) B313865
theorem B373103 : Blo 163797 373103 := bstep (se 1 (by rfl) ⟨279827, by rfl⟩ : syracuseStep 373103 = 559655) B559655
theorem B373175 : Blo 163797 373175 := bstep (se 1 (by rfl) ⟨279881, by rfl⟩ : syracuseStep 373175 = 559763) B559763
theorem B373319 : Blo 163797 373319 := bstep (se 1 (by rfl) ⟨279989, by rfl⟩ : syracuseStep 373319 = 559979) B559979
theorem B373355 : Blo 163797 373355 := bstep (se 1 (by rfl) ⟨280016, by rfl⟩ : syracuseStep 373355 = 560033) B560033
theorem B209719 : Blo 163797 209719 := bstep (se 1 (by rfl) ⟨157289, by rfl⟩ : syracuseStep 209719 = 314579) B314579
theorem B4043627 : Blo 163797 4043627 := bstep (se 1 (by rfl) ⟨3032720, by rfl⟩ : syracuseStep 4043627 = 6065441) B6065441
theorem B373751 : Blo 163797 373751 := bstep (se 1 (by rfl) ⟨280313, by rfl⟩ : syracuseStep 373751 = 560627) B560627
theorem B570359 : Blo 163797 570359 := bstep (se 1 (by rfl) ⟨427769, by rfl⟩ : syracuseStep 570359 = 855539) B855539
theorem B210215 : Blo 163797 210215 := bstep (se 1 (by rfl) ⟨157661, by rfl⟩ : syracuseStep 210215 = 315323) B315323
theorem B374111 : Blo 163797 374111 := bstep (se 1 (by rfl) ⟨280583, by rfl⟩ : syracuseStep 374111 = 561167) B561167
theorem B6337925 : Blo 163797 6337925 := bstep (se 4 (by rfl) ⟨594180, by rfl⟩ : syracuseStep 6337925 = 1188361) B1188361
theorem B800237 : Blo 163797 800237 := bstep (se 3 (by rfl) ⟨150044, by rfl⟩ : syracuseStep 800237 = 300089) B300089
theorem B701959 : Blo 163797 701959 := bstep (se 1 (by rfl) ⟨526469, by rfl⟩ : syracuseStep 701959 = 1052939) B1052939
theorem B210539 : Blo 163797 210539 := bstep (se 1 (by rfl) ⟨157904, by rfl⟩ : syracuseStep 210539 = 315809) B315809
theorem B374507 : Blo 163797 374507 := bstep (se 1 (by rfl) ⟨280880, by rfl⟩ : syracuseStep 374507 = 561761) B561761
theorem B374633 : Blo 163797 374633 := bstep (se 2 (by rfl) ⟨140487, by rfl⟩ : syracuseStep 374633 = 280975) B280975
theorem B3389303 : Blo 163797 3389303 := bstep (se 1 (by rfl) ⟨2541977, by rfl⟩ : syracuseStep 3389303 = 5083955) B5083955
theorem B210919 : Blo 163797 210919 := bstep (se 1 (by rfl) ⟨158189, by rfl⟩ : syracuseStep 210919 = 316379) B316379
theorem B571673 : Blo 163797 571673 := bstep (se 2 (by rfl) ⟨214377, by rfl⟩ : syracuseStep 571673 = 428755) B428755
theorem B178463 : Blo 163797 178463 := bstep (se 1 (by rfl) ⟨133847, by rfl⟩ : syracuseStep 178463 = 267695) B267695
theorem B5880113 : Blo 163797 5880113 := bstep (se 2 (by rfl) ⟨2205042, by rfl⟩ : syracuseStep 5880113 = 4410085) B4410085
theorem B833975 : Blo 163797 833975 := bstep (se 1 (by rfl) ⟨625481, by rfl⟩ : syracuseStep 833975 = 1250963) B1250963
theorem B801353 : Blo 163797 801353 := bstep (se 2 (by rfl) ⟨300507, by rfl⟩ : syracuseStep 801353 = 601015) B601015
theorem B1423979 : Blo 163797 1423979 := bstep (se 1 (by rfl) ⟨1067984, by rfl⟩ : syracuseStep 1423979 = 2135969) B2135969
theorem B277175 : Blo 163797 277175 := bstep (se 1 (by rfl) ⟨207881, by rfl⟩ : syracuseStep 277175 = 415763) B415763
theorem B375479 : Blo 163797 375479 := bstep (se 1 (by rfl) ⟨281609, by rfl⟩ : syracuseStep 375479 = 563219) B563219
theorem B375695 : Blo 163797 375695 := bstep (se 1 (by rfl) ⟨281771, by rfl⟩ : syracuseStep 375695 = 563543) B563543
theorem B933029 : Blo 163797 933029 := bstep (se 4 (by rfl) ⟨87471, by rfl⟩ : syracuseStep 933029 = 174943) B174943
theorem B277897 : Blo 163797 277897 := bstep (se 2 (by rfl) ⟨104211, by rfl⟩ : syracuseStep 277897 = 208423) B208423
theorem B376415 : Blo 163797 376415 := bstep (se 1 (by rfl) ⟨282311, by rfl⟩ : syracuseStep 376415 = 564623) B564623
theorem B474785 : Blo 163797 474785 := bstep (se 2 (by rfl) ⟨178044, by rfl⟩ : syracuseStep 474785 = 356089) B356089
theorem B2866877 : Blo 163797 2866877 := bstep (se 3 (by rfl) ⟨537539, by rfl⟩ : syracuseStep 2866877 = 1075079) B1075079
theorem B507655 : Blo 163797 507655 := bstep (se 1 (by rfl) ⟨380741, by rfl⟩ : syracuseStep 507655 = 761483) B761483
theorem B376631 : Blo 163797 376631 := bstep (se 1 (by rfl) ⟨282473, by rfl⟩ : syracuseStep 376631 = 564947) B564947
theorem B278329 : Blo 163797 278329 := bstep (se 2 (by rfl) ⟨104373, by rfl⟩ : syracuseStep 278329 = 208747) B208747
theorem B245711 : Blo 163797 245711 := bstep (se 1 (by rfl) ⟨184283, by rfl⟩ : syracuseStep 245711 = 368567) B368567
theorem B1523731 : Blo 163797 1523731 := bstep (se 1 (by rfl) ⟨1142798, by rfl⟩ : syracuseStep 1523731 = 2285597) B2285597
theorem B802835 : Blo 163797 802835 := bstep (se 1 (by rfl) ⟨602126, by rfl⟩ : syracuseStep 802835 = 1204253) B1204253
theorem B278633 : Blo 163797 278633 := bstep (se 2 (by rfl) ⟨104487, by rfl⟩ : syracuseStep 278633 = 208975) B208975
theorem B376937 : Blo 163797 376937 := bstep (se 2 (by rfl) ⟨141351, by rfl⟩ : syracuseStep 376937 = 282703) B282703
theorem B246107 : Blo 163797 246107 := bstep (se 1 (by rfl) ⟨184580, by rfl⟩ : syracuseStep 246107 = 369161) B369161
theorem B311663 : Blo 163797 311663 := bstep (se 1 (by rfl) ⟨233747, by rfl⟩ : syracuseStep 311663 = 467495) B467495
theorem B803297 : Blo 163797 803297 := bstep (se 2 (by rfl) ⟨301236, by rfl⟩ : syracuseStep 803297 = 602473) B602473
theorem B246335 : Blo 163797 246335 := bstep (se 1 (by rfl) ⟨184751, by rfl⟩ : syracuseStep 246335 = 369503) B369503
theorem B377423 : Blo 163797 377423 := bstep (se 1 (by rfl) ⟨283067, by rfl⟩ : syracuseStep 377423 = 566135) B566135
theorem B377465 : Blo 163797 377465 := bstep (se 2 (by rfl) ⟨141549, by rfl⟩ : syracuseStep 377465 = 283099) B283099
theorem B803449 : Blo 163797 803449 := bstep (se 2 (by rfl) ⟨301293, by rfl⟩ : syracuseStep 803449 = 602587) B602587
theorem B836243 : Blo 163797 836243 := bstep (se 1 (by rfl) ⟨627182, by rfl⟩ : syracuseStep 836243 = 1254365) B1254365
theorem B246455 : Blo 163797 246455 := bstep (se 1 (by rfl) ⟨184841, by rfl⟩ : syracuseStep 246455 = 369683) B369683
theorem B246683 : Blo 163797 246683 := bstep (se 1 (by rfl) ⟨185012, by rfl⟩ : syracuseStep 246683 = 370025) B370025
theorem B1065959 : Blo 163797 1065959 := bstep (se 1 (by rfl) ⟨799469, by rfl⟩ : syracuseStep 1065959 = 1598939) B1598939
theorem B247079 : Blo 163797 247079 := bstep (se 1 (by rfl) ⟨185309, by rfl⟩ : syracuseStep 247079 = 370619) B370619
theorem B312673 : Blo 163797 312673 := bstep (se 2 (by rfl) ⟨117252, by rfl⟩ : syracuseStep 312673 = 234505) B234505
theorem B247163 : Blo 163797 247163 := bstep (se 1 (by rfl) ⟨185372, by rfl⟩ : syracuseStep 247163 = 370745) B370745
theorem B3556781 : Blo 163797 3556781 := bstep (se 3 (by rfl) ⟨666896, by rfl⟩ : syracuseStep 3556781 = 1333793) B1333793
theorem B2377133 : Blo 163797 2377133 := bstep (se 3 (by rfl) ⟨445712, by rfl⟩ : syracuseStep 2377133 = 891425) B891425
theorem B837053 : Blo 163797 837053 := bstep (se 3 (by rfl) ⟨156947, by rfl⟩ : syracuseStep 837053 = 313895) B313895
theorem B247289 : Blo 163797 247289 := bstep (se 2 (by rfl) ⟨92733, by rfl⟩ : syracuseStep 247289 = 185467) B185467
theorem B280057 : Blo 163797 280057 := bstep (se 2 (by rfl) ⟨105021, by rfl⟩ : syracuseStep 280057 = 210043) B210043
theorem B247391 : Blo 163797 247391 := bstep (se 1 (by rfl) ⟨185543, by rfl⟩ : syracuseStep 247391 = 371087) B371087
theorem B1590941 : Blo 163797 1590941 := bstep (se 3 (by rfl) ⟨298301, by rfl⟩ : syracuseStep 1590941 = 596603) B596603
theorem B444167 : Blo 163797 444167 := bstep (se 1 (by rfl) ⟨333125, by rfl⟩ : syracuseStep 444167 = 666251) B666251
theorem B280327 : Blo 163797 280327 := bstep (se 1 (by rfl) ⟨210245, by rfl⟩ : syracuseStep 280327 = 420491) B420491
theorem B706333 : Blo 163797 706333 := bstep (se 3 (by rfl) ⟨132437, by rfl⟩ : syracuseStep 706333 = 264875) B264875
theorem B280361 : Blo 163797 280361 := bstep (se 2 (by rfl) ⟨105135, by rfl⟩ : syracuseStep 280361 = 210271) B210271
theorem B247607 : Blo 163797 247607 := bstep (se 1 (by rfl) ⟨185705, by rfl⟩ : syracuseStep 247607 = 371411) B371411
theorem B1001297 : Blo 163797 1001297 := bstep (se 2 (by rfl) ⟨375486, by rfl⟩ : syracuseStep 1001297 = 750973) B750973
theorem B1099727 : Blo 163797 1099727 := bstep (se 1 (by rfl) ⟨824795, by rfl⟩ : syracuseStep 1099727 = 1649591) B1649591
theorem B247913 : Blo 163797 247913 := bstep (se 2 (by rfl) ⟨92967, by rfl⟩ : syracuseStep 247913 = 185935) B185935
theorem B248231 : Blo 163797 248231 := bstep (se 1 (by rfl) ⟨186173, by rfl⟩ : syracuseStep 248231 = 372347) B372347
theorem B248315 : Blo 163797 248315 := bstep (se 1 (by rfl) ⟨186236, by rfl⟩ : syracuseStep 248315 = 372473) B372473
theorem B281083 : Blo 163797 281083 := bstep (se 1 (by rfl) ⟨210812, by rfl⟩ : syracuseStep 281083 = 421625) B421625
theorem B248441 : Blo 163797 248441 := bstep (se 2 (by rfl) ⟨93165, by rfl⟩ : syracuseStep 248441 = 186331) B186331
theorem B248495 : Blo 163797 248495 := bstep (se 1 (by rfl) ⟨186371, by rfl⟩ : syracuseStep 248495 = 372743) B372743
theorem B248543 : Blo 163797 248543 := bstep (se 1 (by rfl) ⟨186407, by rfl⟩ : syracuseStep 248543 = 372815) B372815
theorem B314131 : Blo 163797 314131 := bstep (se 1 (by rfl) ⟨235598, by rfl⟩ : syracuseStep 314131 = 471197) B471197
theorem B281515 : Blo 163797 281515 := bstep (se 1 (by rfl) ⟨211136, by rfl⟩ : syracuseStep 281515 = 422273) B422273
theorem B248807 : Blo 163797 248807 := bstep (se 1 (by rfl) ⟨186605, by rfl⟩ : syracuseStep 248807 = 373211) B373211
theorem B281819 : Blo 163797 281819 := bstep (se 1 (by rfl) ⟨211364, by rfl⟩ : syracuseStep 281819 = 422729) B422729
theorem B249065 : Blo 163797 249065 := bstep (se 2 (by rfl) ⟨93399, by rfl⟩ : syracuseStep 249065 = 186799) B186799
theorem B249119 : Blo 163797 249119 := bstep (se 1 (by rfl) ⟨186839, by rfl⟩ : syracuseStep 249119 = 373679) B373679
theorem B314761 : Blo 163797 314761 := bstep (se 2 (by rfl) ⟨118035, by rfl⟩ : syracuseStep 314761 = 236071) B236071
theorem B5787065 : Blo 163797 5787065 := bstep (se 2 (by rfl) ⟨2170149, by rfl⟩ : syracuseStep 5787065 = 4340299) B4340299
theorem B937403 : Blo 163797 937403 := bstep (se 1 (by rfl) ⟨703052, by rfl⟩ : syracuseStep 937403 = 1406105) B1406105
theorem B249287 : Blo 163797 249287 := bstep (se 1 (by rfl) ⟨186965, by rfl⟩ : syracuseStep 249287 = 373931) B373931
theorem B282055 : Blo 163797 282055 := bstep (se 1 (by rfl) ⟨211541, by rfl⟩ : syracuseStep 282055 = 423083) B423083
theorem B1429001 : Blo 163797 1429001 := bstep (se 2 (by rfl) ⟨535875, by rfl⟩ : syracuseStep 1429001 = 1071751) B1071751
theorem B16305953 : Blo 163797 16305953 := bstep (se 2 (by rfl) ⟨6114732, by rfl⟩ : syracuseStep 16305953 = 12229465) B12229465
theorem B249641 : Blo 163797 249641 := bstep (se 2 (by rfl) ⟨93615, by rfl⟩ : syracuseStep 249641 = 187231) B187231
theorem B282415 : Blo 163797 282415 := bstep (se 1 (by rfl) ⟨211811, by rfl⟩ : syracuseStep 282415 = 423623) B423623
theorem B249647 : Blo 163797 249647 := bstep (se 1 (by rfl) ⟨187235, by rfl⟩ : syracuseStep 249647 = 374471) B374471
theorem B6377291 : Blo 163797 6377291 := bstep (se 1 (by rfl) ⟨4782968, by rfl⟩ : syracuseStep 6377291 = 9565937) B9565937
theorem B1888109 : Blo 163797 1888109 := bstep (se 3 (by rfl) ⟨354020, by rfl⟩ : syracuseStep 1888109 = 708041) B708041
theorem B282575 : Blo 163797 282575 := bstep (se 1 (by rfl) ⟨211931, by rfl⟩ : syracuseStep 282575 = 423863) B423863
theorem B3592421 : Blo 163797 3592421 := bstep (se 4 (by rfl) ⟨336789, by rfl⟩ : syracuseStep 3592421 = 673579) B673579
theorem B250121 : Blo 163797 250121 := bstep (se 2 (by rfl) ⟨93795, by rfl⟩ : syracuseStep 250121 = 187591) B187591
theorem B250223 : Blo 163797 250223 := bstep (se 1 (by rfl) ⟨187667, by rfl⟩ : syracuseStep 250223 = 375335) B375335
theorem B250439 : Blo 163797 250439 := bstep (se 1 (by rfl) ⟨187829, by rfl⟩ : syracuseStep 250439 = 375659) B375659
theorem B184927 : Blo 163797 184927 := bstep (se 1 (by rfl) ⟨138695, by rfl⟩ : syracuseStep 184927 = 277391) B277391
theorem B250475 : Blo 163797 250475 := bstep (se 1 (by rfl) ⟨187856, by rfl⟩ : syracuseStep 250475 = 375713) B375713
theorem B250703 : Blo 163797 250703 := bstep (se 1 (by rfl) ⟨188027, by rfl⟩ : syracuseStep 250703 = 376055) B376055
theorem B938861 : Blo 163797 938861 := bstep (se 3 (by rfl) ⟨176036, by rfl⟩ : syracuseStep 938861 = 352073) B352073
theorem B251099 : Blo 163797 251099 := bstep (se 1 (by rfl) ⟨188324, by rfl⟩ : syracuseStep 251099 = 376649) B376649
theorem B414953 : Blo 163797 414953 := bstep (se 2 (by rfl) ⟨155607, by rfl⟩ : syracuseStep 414953 = 311215) B311215
theorem B382201 : Blo 163797 382201 := bstep (se 2 (by rfl) ⟨143325, by rfl⟩ : syracuseStep 382201 = 286651) B286651
theorem B251273 : Blo 163797 251273 := bstep (se 2 (by rfl) ⟨94227, by rfl⟩ : syracuseStep 251273 = 188455) B188455
theorem B415115 : Blo 163797 415115 := bstep (se 1 (by rfl) ⟨311336, by rfl⟩ : syracuseStep 415115 = 622673) B622673
theorem B415327 : Blo 163797 415327 := bstep (se 1 (by rfl) ⟨311495, by rfl⟩ : syracuseStep 415327 = 622991) B622991
theorem B186079 : Blo 163797 186079 := bstep (se 1 (by rfl) ⟨139559, by rfl⟩ : syracuseStep 186079 = 279119) B279119
theorem B251627 : Blo 163797 251627 := bstep (se 1 (by rfl) ⟨188720, by rfl⟩ : syracuseStep 251627 = 377441) B377441
theorem B317191 : Blo 163797 317191 := bstep (se 1 (by rfl) ⟨237893, by rfl⟩ : syracuseStep 317191 = 475787) B475787
theorem B939863 : Blo 163797 939863 := bstep (se 1 (by rfl) ⟨704897, by rfl⟩ : syracuseStep 939863 = 1409795) B1409795
theorem B350057 : Blo 163797 350057 := bstep (se 2 (by rfl) ⟨131271, by rfl⟩ : syracuseStep 350057 = 262543) B262543
theorem B1791973 : Blo 163797 1791973 := bstep (se 4 (by rfl) ⟨167997, by rfl⟩ : syracuseStep 1791973 = 335995) B335995
theorem B841913 : Blo 163797 841913 := bstep (se 2 (by rfl) ⟨315717, by rfl⟩ : syracuseStep 841913 = 631435) B631435
theorem B415955 : Blo 163797 415955 := bstep (se 1 (by rfl) ⟨311966, by rfl⟩ : syracuseStep 415955 = 623933) B623933
theorem B186655 : Blo 163797 186655 := bstep (se 1 (by rfl) ⟨139991, by rfl⟩ : syracuseStep 186655 = 279983) B279983
theorem B448859 : Blo 163797 448859 := bstep (se 1 (by rfl) ⟨336644, by rfl⟩ : syracuseStep 448859 = 673289) B673289
theorem B186943 : Blo 163797 186943 := bstep (se 1 (by rfl) ⟨140207, by rfl⟩ : syracuseStep 186943 = 280415) B280415
theorem B711443 : Blo 163797 711443 := bstep (se 1 (by rfl) ⟨533582, by rfl⟩ : syracuseStep 711443 = 1067165) B1067165
theorem B711595 : Blo 163797 711595 := bstep (se 1 (by rfl) ⟨533696, by rfl⟩ : syracuseStep 711595 = 1067393) B1067393
theorem B449725 : Blo 163797 449725 := bstep (se 3 (by rfl) ⟨84323, by rfl⟩ : syracuseStep 449725 = 168647) B168647
theorem B187771 : Blo 163797 187771 := bstep (se 1 (by rfl) ⟨140828, by rfl⟩ : syracuseStep 187771 = 281657) B281657
theorem B1007063 : Blo 163797 1007063 := bstep (se 1 (by rfl) ⟨755297, by rfl⟩ : syracuseStep 1007063 = 1510595) B1510595
theorem B187967 : Blo 163797 187967 := bstep (se 1 (by rfl) ⟨140975, by rfl⟩ : syracuseStep 187967 = 281951) B281951
theorem B1498769 : Blo 163797 1498769 := bstep (se 2 (by rfl) ⟨562038, by rfl⟩ : syracuseStep 1498769 = 1124077) B1124077
theorem B188239 : Blo 163797 188239 := bstep (se 1 (by rfl) ⟨141179, by rfl⟩ : syracuseStep 188239 = 282359) B282359
theorem B843695 : Blo 163797 843695 := bstep (se 1 (by rfl) ⟨632771, by rfl⟩ : syracuseStep 843695 = 1265543) B1265543
theorem B188635 : Blo 163797 188635 := bstep (se 1 (by rfl) ⟨141476, by rfl⟩ : syracuseStep 188635 = 282953) B282953
theorem B450841 : Blo 163797 450841 := bstep (se 2 (by rfl) ⟨169065, by rfl⟩ : syracuseStep 450841 = 338131) B338131
theorem B352603 : Blo 163797 352603 := bstep (se 1 (by rfl) ⟨264452, by rfl⟩ : syracuseStep 352603 = 528905) B528905
theorem B39739747 : Blo 163797 39739747 := bstep (se 1 (by rfl) ⟨29804810, by rfl⟩ : syracuseStep 39739747 = 59609621) B59609621
theorem B418223 : Blo 163797 418223 := bstep (se 1 (by rfl) ⟨313667, by rfl⟩ : syracuseStep 418223 = 627335) B627335
theorem B1499795 : Blo 163797 1499795 := bstep (se 1 (by rfl) ⟨1124846, by rfl⟩ : syracuseStep 1499795 = 2249693) B2249693
theorem B1794743 : Blo 163797 1794743 := bstep (se 1 (by rfl) ⟨1346057, by rfl⟩ : syracuseStep 1794743 = 2692115) B2692115
theorem B2384801 : Blo 163797 2384801 := bstep (se 2 (by rfl) ⟨894300, by rfl⟩ : syracuseStep 2384801 = 1788601) B1788601
theorem B353423 : Blo 163797 353423 := bstep (se 1 (by rfl) ⟨265067, by rfl⟩ : syracuseStep 353423 = 530135) B530135
theorem B419195 : Blo 163797 419195 := bstep (se 1 (by rfl) ⟨314396, by rfl⟩ : syracuseStep 419195 = 628793) B628793
theorem B419489 : Blo 163797 419489 := bstep (se 2 (by rfl) ⟨157308, by rfl⟩ : syracuseStep 419489 = 314617) B314617
theorem B321259 : Blo 163797 321259 := bstep (se 1 (by rfl) ⟨240944, by rfl⟩ : syracuseStep 321259 = 481889) B481889
theorem B354089 : Blo 163797 354089 := bstep (se 2 (by rfl) ⟨132783, by rfl⟩ : syracuseStep 354089 = 265567) B265567
theorem B1402757 : Blo 163797 1402757 := bstep (se 4 (by rfl) ⟨131508, by rfl⟩ : syracuseStep 1402757 = 263017) B263017
theorem B452861 : Blo 163797 452861 := bstep (se 3 (by rfl) ⟨84911, by rfl⟩ : syracuseStep 452861 = 169823) B169823
theorem B420187 : Blo 163797 420187 := bstep (se 1 (by rfl) ⟨315140, by rfl⟩ : syracuseStep 420187 = 630281) B630281
theorem B1206701 : Blo 163797 1206701 := bstep (se 3 (by rfl) ⟨226256, by rfl⟩ : syracuseStep 1206701 = 452513) B452513
theorem B846611 : Blo 163797 846611 := bstep (se 1 (by rfl) ⟨634958, by rfl⟩ : syracuseStep 846611 = 1269917) B1269917
theorem B421159 : Blo 163797 421159 := bstep (se 1 (by rfl) ⟨315869, by rfl⟩ : syracuseStep 421159 = 631739) B631739
theorem B224635 : Blo 163797 224635 := bstep (se 1 (by rfl) ⟨168476, by rfl⟩ : syracuseStep 224635 = 336953) B336953
theorem B421433 : Blo 163797 421433 := bstep (se 2 (by rfl) ⟨158037, by rfl⟩ : syracuseStep 421433 = 316075) B316075
theorem B847745 : Blo 163797 847745 := bstep (se 2 (by rfl) ⟨317904, by rfl⟩ : syracuseStep 847745 = 635809) B635809
theorem B553391 : Blo 163797 553391 := bstep (se 1 (by rfl) ⟨415043, by rfl⟩ : syracuseStep 553391 = 830087) B830087
theorem B1405421 : Blo 163797 1405421 := bstep (se 3 (by rfl) ⟨263516, by rfl⟩ : syracuseStep 1405421 = 527033) B527033
theorem B3469873 : Blo 163797 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B848555 : Blo 163797 848555 := bstep (se 1 (by rfl) ⟨636416, by rfl⟩ : syracuseStep 848555 = 1272833) B1272833
theorem B357139 : Blo 163797 357139 := bstep (se 1 (by rfl) ⟨267854, by rfl⟩ : syracuseStep 357139 = 535709) B535709
theorem B357473 : Blo 163797 357473 := bstep (se 2 (by rfl) ⟨134052, by rfl⟩ : syracuseStep 357473 = 268105) B268105
theorem B849041 : Blo 163797 849041 := bstep (se 2 (by rfl) ⟨318390, by rfl⟩ : syracuseStep 849041 = 636781) B636781
theorem B11728151 : Blo 163797 11728151 := bstep (se 1 (by rfl) ⟨8796113, by rfl⟩ : syracuseStep 11728151 = 17592227) B17592227
theorem B947495 : Blo 163797 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B423265 : Blo 163797 423265 := bstep (se 2 (by rfl) ⟨158724, by rfl⟩ : syracuseStep 423265 = 317449) B317449
theorem B554363 : Blo 163797 554363 := bstep (se 1 (by rfl) ⟨415772, by rfl⟩ : syracuseStep 554363 = 831545) B831545
theorem B423737 : Blo 163797 423737 := bstep (se 2 (by rfl) ⟨158901, by rfl⟩ : syracuseStep 423737 = 317803) B317803
theorem B424217 : Blo 163797 424217 := bstep (se 2 (by rfl) ⟨159081, by rfl⟩ : syracuseStep 424217 = 318163) B318163
theorem B4290893 : Blo 163797 4290893 := bstep (se 3 (by rfl) ⟨804542, by rfl⟩ : syracuseStep 4290893 = 1609085) B1609085
theorem B1440089 : Blo 163797 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B424511 : Blo 163797 424511 := bstep (se 1 (by rfl) ⟨318383, by rfl⟩ : syracuseStep 424511 = 636767) B636767
theorem B948809 : Blo 163797 948809 := bstep (se 2 (by rfl) ⟨355803, by rfl⟩ : syracuseStep 948809 = 711607) B711607
theorem B457289 : Blo 163797 457289 := bstep (se 2 (by rfl) ⟨171483, by rfl⟩ : syracuseStep 457289 = 342967) B342967
theorem B555767 : Blo 163797 555767 := bstep (se 1 (by rfl) ⟨416825, by rfl⟩ : syracuseStep 555767 = 833651) B833651
theorem B424723 : Blo 163797 424723 := bstep (se 1 (by rfl) ⟨318542, by rfl⟩ : syracuseStep 424723 = 637085) B637085
theorem B556847 : Blo 163797 556847 := bstep (se 1 (by rfl) ⟨417635, by rfl⟩ : syracuseStep 556847 = 835271) B835271
theorem B163815 : Blo 163797 163815 := bstep (se 1 (by rfl) ⟨122861, by rfl⟩ : syracuseStep 163815 = 245723) B245723
theorem B2031641 : Blo 163797 2031641 := bstep (se 2 (by rfl) ⟨761865, by rfl⟩ : syracuseStep 2031641 = 1523731) B1523731
theorem B164071 : Blo 163797 164071 := bstep (se 1 (by rfl) ⟨123053, by rfl⟩ : syracuseStep 164071 = 246107) B246107
theorem B164223 : Blo 163797 164223 := bstep (se 1 (by rfl) ⟨123167, by rfl⟩ : syracuseStep 164223 = 246335) B246335
theorem B557495 : Blo 163797 557495 := bstep (se 1 (by rfl) ⟨418121, by rfl⟩ : syracuseStep 557495 = 836243) B836243
theorem B262607 : Blo 163797 262607 := bstep (se 1 (by rfl) ⟨196955, by rfl⟩ : syracuseStep 262607 = 393911) B393911
theorem B164303 : Blo 163797 164303 := bstep (se 1 (by rfl) ⟨123227, by rfl⟩ : syracuseStep 164303 = 246455) B246455
theorem B52986329 : Blo 163797 52986329 := bstep (se 2 (by rfl) ⟨19869873, by rfl⟩ : syracuseStep 52986329 = 39739747) B39739747
theorem B164455 : Blo 163797 164455 := bstep (se 1 (by rfl) ⟨123341, by rfl⟩ : syracuseStep 164455 = 246683) B246683
theorem B1901231 : Blo 163797 1901231 := bstep (se 1 (by rfl) ⟨1425923, by rfl⟩ : syracuseStep 1901231 = 2851847) B2851847
theorem B525035 : Blo 163797 525035 := bstep (se 1 (by rfl) ⟨393776, by rfl⟩ : syracuseStep 525035 = 787553) B787553
theorem B525113 : Blo 163797 525113 := bstep (se 2 (by rfl) ⟨196917, by rfl⟩ : syracuseStep 525113 = 393835) B393835
theorem B164719 : Blo 163797 164719 := bstep (se 1 (by rfl) ⟨123539, by rfl⟩ : syracuseStep 164719 = 247079) B247079
theorem B557981 : Blo 163797 557981 := bstep (se 3 (by rfl) ⟨104621, by rfl⟩ : syracuseStep 557981 = 209243) B209243
theorem B164775 : Blo 163797 164775 := bstep (se 1 (by rfl) ⟨123581, by rfl⟩ : syracuseStep 164775 = 247163) B247163
theorem B558035 : Blo 163797 558035 := bstep (se 1 (by rfl) ⟨418526, by rfl⟩ : syracuseStep 558035 = 837053) B837053
theorem B164859 : Blo 163797 164859 := bstep (se 1 (by rfl) ⟨123644, by rfl⟩ : syracuseStep 164859 = 247289) B247289
theorem B164927 : Blo 163797 164927 := bstep (se 1 (by rfl) ⟨123695, by rfl⟩ : syracuseStep 164927 = 247391) B247391
theorem B296111 : Blo 163797 296111 := bstep (se 1 (by rfl) ⟨222083, by rfl⟩ : syracuseStep 296111 = 444167) B444167
theorem B165071 : Blo 163797 165071 := bstep (se 1 (by rfl) ⟨123803, by rfl⟩ : syracuseStep 165071 = 247607) B247607
theorem B165275 : Blo 163797 165275 := bstep (se 1 (by rfl) ⟨123956, by rfl⟩ : syracuseStep 165275 = 247913) B247913
theorem B5342705 : Blo 163797 5342705 := bstep (se 2 (by rfl) ⟨2003514, by rfl⟩ : syracuseStep 5342705 = 4007029) B4007029
theorem B165487 : Blo 163797 165487 := bstep (se 1 (by rfl) ⟨124115, by rfl⟩ : syracuseStep 165487 = 248231) B248231
theorem B165543 : Blo 163797 165543 := bstep (se 1 (by rfl) ⟨124157, by rfl⟩ : syracuseStep 165543 = 248315) B248315
theorem B165627 : Blo 163797 165627 := bstep (se 1 (by rfl) ⟨124220, by rfl⟩ : syracuseStep 165627 = 248441) B248441
theorem B165663 : Blo 163797 165663 := bstep (se 1 (by rfl) ⟨124247, by rfl⟩ : syracuseStep 165663 = 248495) B248495
theorem B165695 : Blo 163797 165695 := bstep (se 1 (by rfl) ⟨124271, by rfl⟩ : syracuseStep 165695 = 248543) B248543
theorem B788399 : Blo 163797 788399 := bstep (se 1 (by rfl) ⟨591299, by rfl⟩ : syracuseStep 788399 = 1182599) B1182599
theorem B165871 : Blo 163797 165871 := bstep (se 1 (by rfl) ⟨124403, by rfl⟩ : syracuseStep 165871 = 248807) B248807
theorem B166043 : Blo 163797 166043 := bstep (se 1 (by rfl) ⟨124532, by rfl⟩ : syracuseStep 166043 = 249065) B249065
theorem B166079 : Blo 163797 166079 := bstep (se 1 (by rfl) ⟨124559, by rfl⟩ : syracuseStep 166079 = 249119) B249119
theorem B624935 : Blo 163797 624935 := bstep (se 1 (by rfl) ⟨468701, by rfl⟩ : syracuseStep 624935 = 937403) B937403
theorem B166191 : Blo 163797 166191 := bstep (se 1 (by rfl) ⟨124643, by rfl⟩ : syracuseStep 166191 = 249287) B249287
theorem B428345 : Blo 163797 428345 := bstep (se 2 (by rfl) ⟨160629, by rfl⟩ : syracuseStep 428345 = 321259) B321259
theorem B952667 : Blo 163797 952667 := bstep (se 1 (by rfl) ⟨714500, by rfl⟩ : syracuseStep 952667 = 1429001) B1429001
theorem B526817 : Blo 163797 526817 := bstep (se 2 (by rfl) ⟨197556, by rfl⟩ : syracuseStep 526817 = 395113) B395113
theorem B166427 : Blo 163797 166427 := bstep (se 1 (by rfl) ⟨124820, by rfl⟩ : syracuseStep 166427 = 249641) B249641
theorem B166431 : Blo 163797 166431 := bstep (se 1 (by rfl) ⟨124823, by rfl⟩ : syracuseStep 166431 = 249647) B249647
theorem B1968745 : Blo 163797 1968745 := bstep (se 2 (by rfl) ⟨738279, by rfl⟩ : syracuseStep 1968745 = 1476559) B1476559
theorem B2394947 : Blo 163797 2394947 := bstep (se 1 (by rfl) ⟨1796210, by rfl⟩ : syracuseStep 2394947 = 3592421) B3592421
theorem B723799 : Blo 163797 723799 := bstep (se 1 (by rfl) ⟨542849, by rfl⟩ : syracuseStep 723799 = 1085699) B1085699
theorem B166747 : Blo 163797 166747 := bstep (se 1 (by rfl) ⟨125060, by rfl⟩ : syracuseStep 166747 = 250121) B250121
theorem B166815 : Blo 163797 166815 := bstep (se 1 (by rfl) ⟨125111, by rfl⟩ : syracuseStep 166815 = 250223) B250223
theorem B166959 : Blo 163797 166959 := bstep (se 1 (by rfl) ⟨125219, by rfl⟩ : syracuseStep 166959 = 250439) B250439
theorem B166983 : Blo 163797 166983 := bstep (se 1 (by rfl) ⟨125237, by rfl⟩ : syracuseStep 166983 = 250475) B250475
theorem B560249 : Blo 163797 560249 := bstep (se 2 (by rfl) ⟨210093, by rfl⟩ : syracuseStep 560249 = 420187) B420187
theorem B167135 : Blo 163797 167135 := bstep (se 1 (by rfl) ⟨125351, by rfl⟩ : syracuseStep 167135 = 250703) B250703
theorem B625907 : Blo 163797 625907 := bstep (se 1 (by rfl) ⟨469430, by rfl⟩ : syracuseStep 625907 = 938861) B938861
theorem B1576259 : Blo 163797 1576259 := bstep (se 1 (by rfl) ⟨1182194, by rfl⟩ : syracuseStep 1576259 = 2364389) B2364389
theorem B626089 : Blo 163797 626089 := bstep (se 2 (by rfl) ⟨234783, by rfl⟩ : syracuseStep 626089 = 469567) B469567
theorem B2526653 : Blo 163797 2526653 := bstep (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) B947495
theorem B560573 : Blo 163797 560573 := bstep (se 3 (by rfl) ⟨105107, by rfl⟩ : syracuseStep 560573 = 210215) B210215
theorem B167399 : Blo 163797 167399 := bstep (se 1 (by rfl) ⟨125549, by rfl⟩ : syracuseStep 167399 = 251099) B251099
theorem B167515 : Blo 163797 167515 := bstep (se 1 (by rfl) ⟨125636, by rfl⟩ : syracuseStep 167515 = 251273) B251273
theorem B167751 : Blo 163797 167751 := bstep (se 1 (by rfl) ⟨125813, by rfl⟩ : syracuseStep 167751 = 251627) B251627
theorem B626575 : Blo 163797 626575 := bstep (se 1 (by rfl) ⟨469931, by rfl⟩ : syracuseStep 626575 = 939863) B939863
theorem B233371 : Blo 163797 233371 := bstep (se 1 (by rfl) ⟨175028, by rfl⟩ : syracuseStep 233371 = 350057) B350057
theorem B2133965 : Blo 163797 2133965 := bstep (se 3 (by rfl) ⟨400118, by rfl⟩ : syracuseStep 2133965 = 800237) B800237
theorem B1904741 : Blo 163797 1904741 := bstep (se 4 (by rfl) ⟨178569, by rfl⟩ : syracuseStep 1904741 = 357139) B357139
theorem B561275 : Blo 163797 561275 := bstep (se 1 (by rfl) ⟨420956, by rfl⟩ : syracuseStep 561275 = 841913) B841913
theorem B2363579 : Blo 163797 2363579 := bstep (se 1 (by rfl) ⟨1772684, by rfl⟩ : syracuseStep 2363579 = 3545369) B3545369
theorem B561437 : Blo 163797 561437 := bstep (se 3 (by rfl) ⟨105269, by rfl⟩ : syracuseStep 561437 = 210539) B210539
theorem B561545 : Blo 163797 561545 := bstep (se 2 (by rfl) ⟨210579, by rfl⟩ : syracuseStep 561545 = 421159) B421159
theorem B299513 : Blo 163797 299513 := bstep (se 2 (by rfl) ⟨112317, by rfl⟩ : syracuseStep 299513 = 224635) B224635
theorem B594515 : Blo 163797 594515 := bstep (se 1 (by rfl) ⟨445886, by rfl⟩ : syracuseStep 594515 = 891773) B891773
theorem B529213 : Blo 163797 529213 := bstep (se 3 (by rfl) ⟨99227, by rfl⟩ : syracuseStep 529213 = 198455) B198455
theorem B562463 : Blo 163797 562463 := bstep (se 1 (by rfl) ⟨421847, by rfl⟩ : syracuseStep 562463 = 843695) B843695
theorem B1054043 : Blo 163797 1054043 := bstep (se 1 (by rfl) ⟨790532, by rfl⟩ : syracuseStep 1054043 = 1581065) B1581065
theorem B267887 : Blo 163797 267887 := bstep (se 1 (by rfl) ⟨200915, by rfl⟩ : syracuseStep 267887 = 401831) B401831
theorem B595943 : Blo 163797 595943 := bstep (se 1 (by rfl) ⟨446957, by rfl⟩ : syracuseStep 595943 = 893915) B893915
theorem B4626497 : Blo 163797 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B2038405 : Blo 163797 2038405 := bstep (se 4 (by rfl) ⟨191100, by rfl⟩ : syracuseStep 2038405 = 382201) B382201
theorem B301907 : Blo 163797 301907 := bstep (se 1 (by rfl) ⟨226430, by rfl⟩ : syracuseStep 301907 = 452861) B452861
theorem B2136941 : Blo 163797 2136941 := bstep (se 3 (by rfl) ⟨400676, by rfl⟩ : syracuseStep 2136941 = 801353) B801353
theorem B564353 : Blo 163797 564353 := bstep (se 2 (by rfl) ⟨211632, by rfl⟩ : syracuseStep 564353 = 423265) B423265
theorem B564407 : Blo 163797 564407 := bstep (se 1 (by rfl) ⟨423305, by rfl⟩ : syracuseStep 564407 = 846611) B846611
theorem B531851 : Blo 163797 531851 := bstep (se 1 (by rfl) ⟨398888, by rfl⟩ : syracuseStep 531851 = 797777) B797777
theorem B794087 : Blo 163797 794087 := bstep (se 1 (by rfl) ⟨595565, by rfl⟩ : syracuseStep 794087 = 1191131) B1191131
theorem B565163 : Blo 163797 565163 := bstep (se 1 (by rfl) ⟨423872, by rfl⟩ : syracuseStep 565163 = 847745) B847745
theorem B368927 : Blo 163797 368927 := bstep (se 1 (by rfl) ⟨276695, by rfl⟩ : syracuseStep 368927 = 553391) B553391
theorem B565703 : Blo 163797 565703 := bstep (se 1 (by rfl) ⟨424277, by rfl⟩ : syracuseStep 565703 = 848555) B848555
theorem B2695751 : Blo 163797 2695751 := bstep (se 1 (by rfl) ⟨2021813, by rfl⟩ : syracuseStep 2695751 = 4043627) B4043627
theorem B238315 : Blo 163797 238315 := bstep (se 1 (by rfl) ⟨178736, by rfl⟩ : syracuseStep 238315 = 357473) B357473
theorem B566027 : Blo 163797 566027 := bstep (se 1 (by rfl) ⟨424520, by rfl⟩ : syracuseStep 566027 = 849041) B849041
theorem B369575 : Blo 163797 369575 := bstep (se 1 (by rfl) ⟨277181, by rfl⟩ : syracuseStep 369575 = 554363) B554363
theorem B566297 : Blo 163797 566297 := bstep (se 2 (by rfl) ⟨212361, by rfl⟩ : syracuseStep 566297 = 424723) B424723
theorem B501245 : Blo 163797 501245 := bstep (se 3 (by rfl) ⟨93983, by rfl⟩ : syracuseStep 501245 = 187967) B187967
theorem B2860595 : Blo 163797 2860595 := bstep (se 1 (by rfl) ⟨2145446, by rfl⟩ : syracuseStep 2860595 = 4290893) B4290893
theorem B960059 : Blo 163797 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B599633 : Blo 163797 599633 := bstep (se 2 (by rfl) ⟨224862, by rfl⟩ : syracuseStep 599633 = 449725) B449725
theorem B632539 : Blo 163797 632539 := bstep (se 1 (by rfl) ⟨474404, by rfl⟩ : syracuseStep 632539 = 948809) B948809
theorem B304859 : Blo 163797 304859 := bstep (se 1 (by rfl) ⟨228644, by rfl⟩ : syracuseStep 304859 = 457289) B457289
theorem B370511 : Blo 163797 370511 := bstep (se 1 (by rfl) ⟨277883, by rfl⟩ : syracuseStep 370511 = 555767) B555767
theorem B370529 : Blo 163797 370529 := bstep (se 2 (by rfl) ⟨138948, by rfl⟩ : syracuseStep 370529 = 277897) B277897
theorem B371105 : Blo 163797 371105 := bstep (se 2 (by rfl) ⟨139164, by rfl⟩ : syracuseStep 371105 = 278329) B278329
theorem B1911251 : Blo 163797 1911251 := bstep (se 1 (by rfl) ⟨1433438, by rfl⟩ : syracuseStep 1911251 = 2866877) B2866877
theorem B371231 : Blo 163797 371231 := bstep (se 1 (by rfl) ⟨278423, by rfl⟩ : syracuseStep 371231 = 556847) B556847
theorem B535223 : Blo 163797 535223 := bstep (se 1 (by rfl) ⟨401417, by rfl⟩ : syracuseStep 535223 = 802835) B802835
theorem B207775 : Blo 163797 207775 := bstep (se 1 (by rfl) ⟨155831, by rfl⟩ : syracuseStep 207775 = 311663) B311663
theorem B535531 : Blo 163797 535531 := bstep (se 1 (by rfl) ⟨401648, by rfl⟩ : syracuseStep 535531 = 803297) B803297
theorem B601121 : Blo 163797 601121 := bstep (se 2 (by rfl) ⟨225420, by rfl⟩ : syracuseStep 601121 = 450841) B450841
theorem B470137 : Blo 163797 470137 := bstep (se 2 (by rfl) ⟨176301, by rfl⟩ : syracuseStep 470137 = 352603) B352603
theorem B699961 : Blo 163797 699961 := bstep (se 2 (by rfl) ⟨262485, by rfl⟩ : syracuseStep 699961 = 524971) B524971
theorem B699977 : Blo 163797 699977 := bstep (se 2 (by rfl) ⟨262491, by rfl⟩ : syracuseStep 699977 = 524983) B524983
theorem B2371187 : Blo 163797 2371187 := bstep (se 1 (by rfl) ⟨1778390, by rfl⟩ : syracuseStep 2371187 = 3556781) B3556781
theorem B1584755 : Blo 163797 1584755 := bstep (se 1 (by rfl) ⟨1188566, by rfl⟩ : syracuseStep 1584755 = 2377133) B2377133
theorem B1060627 : Blo 163797 1060627 := bstep (se 1 (by rfl) ⟨795470, by rfl⟩ : syracuseStep 1060627 = 1590941) B1590941
theorem B667531 : Blo 163797 667531 := bstep (se 1 (by rfl) ⟨500648, by rfl⟩ : syracuseStep 667531 = 1001297) B1001297
theorem B372635 : Blo 163797 372635 := bstep (se 1 (by rfl) ⟨279476, by rfl⟩ : syracuseStep 372635 = 558953) B558953
theorem B733151 : Blo 163797 733151 := bstep (se 1 (by rfl) ⟨549863, by rfl⟩ : syracuseStep 733151 = 1099727) B1099727
theorem B2404403 : Blo 163797 2404403 := bstep (se 1 (by rfl) ⟨1803302, by rfl⟩ : syracuseStep 2404403 = 3606605) B3606605
theorem B372923 : Blo 163797 372923 := bstep (se 1 (by rfl) ⟨279692, by rfl⟩ : syracuseStep 372923 = 559385) B559385
theorem B373409 : Blo 163797 373409 := bstep (se 2 (by rfl) ⟨140028, by rfl⟩ : syracuseStep 373409 = 280057) B280057
theorem B3191723 : Blo 163797 3191723 := bstep (se 1 (by rfl) ⟨2393792, by rfl⟩ : syracuseStep 3191723 = 4787585) B4787585
theorem B373769 : Blo 163797 373769 := bstep (se 2 (by rfl) ⟨140163, by rfl⟩ : syracuseStep 373769 = 280327) B280327
theorem B373823 : Blo 163797 373823 := bstep (se 1 (by rfl) ⟨280367, by rfl⟩ : syracuseStep 373823 = 560735) B560735
theorem B1258739 : Blo 163797 1258739 := bstep (se 1 (by rfl) ⟨944054, by rfl⟩ : syracuseStep 1258739 = 1888109) B1888109
theorem B1520957 : Blo 163797 1520957 := bstep (se 3 (by rfl) ⟨285179, by rfl⟩ : syracuseStep 1520957 = 570359) B570359
theorem B537953 : Blo 163797 537953 := bstep (se 2 (by rfl) ⟨201732, by rfl⟩ : syracuseStep 537953 = 403465) B403465
theorem B636599 : Blo 163797 636599 := bstep (se 1 (by rfl) ⟨477449, by rfl⟩ : syracuseStep 636599 = 954899) B954899
theorem B833327 : Blo 163797 833327 := bstep (se 1 (by rfl) ⟨624995, by rfl⟩ : syracuseStep 833327 = 1249991) B1249991
theorem B374759 : Blo 163797 374759 := bstep (se 1 (by rfl) ⟨281069, by rfl⟩ : syracuseStep 374759 = 562139) B562139
theorem B276473 : Blo 163797 276473 := bstep (se 2 (by rfl) ⟨103677, by rfl⟩ : syracuseStep 276473 = 207355) B207355
theorem B374777 : Blo 163797 374777 := bstep (se 2 (by rfl) ⟨140541, by rfl⟩ : syracuseStep 374777 = 281083) B281083
theorem B374867 : Blo 163797 374867 := bstep (se 1 (by rfl) ⟨281150, by rfl⟩ : syracuseStep 374867 = 562301) B562301
theorem B276635 : Blo 163797 276635 := bstep (se 1 (by rfl) ⟨207476, by rfl⟩ : syracuseStep 276635 = 414953) B414953
theorem B506011 : Blo 163797 506011 := bstep (se 1 (by rfl) ⟨379508, by rfl⟩ : syracuseStep 506011 = 759017) B759017
theorem B374939 : Blo 163797 374939 := bstep (se 1 (by rfl) ⟨281204, by rfl⟩ : syracuseStep 374939 = 562409) B562409
theorem B276743 : Blo 163797 276743 := bstep (se 1 (by rfl) ⟨207557, by rfl⟩ : syracuseStep 276743 = 415115) B415115
theorem B375047 : Blo 163797 375047 := bstep (se 1 (by rfl) ⟨281285, by rfl⟩ : syracuseStep 375047 = 562571) B562571
theorem B7649579 : Blo 163797 7649579 := bstep (se 1 (by rfl) ⟨5737184, by rfl⟩ : syracuseStep 7649579 = 11474369) B11474369
theorem B2144627 : Blo 163797 2144627 := bstep (se 1 (by rfl) ⟨1608470, by rfl⟩ : syracuseStep 2144627 = 3216941) B3216941
theorem B7256465 : Blo 163797 7256465 := bstep (se 2 (by rfl) ⟨2721174, by rfl⟩ : syracuseStep 7256465 = 5442349) B5442349
theorem B375353 : Blo 163797 375353 := bstep (se 2 (by rfl) ⟨140757, by rfl⟩ : syracuseStep 375353 = 281515) B281515
theorem B277303 : Blo 163797 277303 := bstep (se 1 (by rfl) ⟨207977, by rfl⟩ : syracuseStep 277303 = 415955) B415955
theorem B474295 : Blo 163797 474295 := bstep (se 1 (by rfl) ⟨355721, by rfl⟩ : syracuseStep 474295 = 711443) B711443
theorem B277769 : Blo 163797 277769 := bstep (se 2 (by rfl) ⟨104163, by rfl⟩ : syracuseStep 277769 = 208327) B208327
theorem B376073 : Blo 163797 376073 := bstep (se 2 (by rfl) ⟨141027, by rfl⟩ : syracuseStep 376073 = 282055) B282055
theorem B671375 : Blo 163797 671375 := bstep (se 1 (by rfl) ⟨503531, by rfl⟩ : syracuseStep 671375 = 1007063) B1007063
theorem B376553 : Blo 163797 376553 := bstep (se 2 (by rfl) ⟨141207, by rfl⟩ : syracuseStep 376553 = 282415) B282415
theorem B999179 : Blo 163797 999179 := bstep (se 1 (by rfl) ⟨749384, by rfl⟩ : syracuseStep 999179 = 1498769) B1498769
theorem B377063 : Blo 163797 377063 := bstep (se 1 (by rfl) ⟨282797, by rfl⟩ : syracuseStep 377063 = 565595) B565595
theorem B246047 : Blo 163797 246047 := bstep (se 1 (by rfl) ⟨184535, by rfl⟩ : syracuseStep 246047 = 369071) B369071
theorem B278815 : Blo 163797 278815 := bstep (se 1 (by rfl) ⟨209111, by rfl⟩ : syracuseStep 278815 = 418223) B418223
theorem B246071 : Blo 163797 246071 := bstep (se 1 (by rfl) ⟨184553, by rfl⟩ : syracuseStep 246071 = 369107) B369107
theorem B246143 : Blo 163797 246143 := bstep (se 1 (by rfl) ⟨184607, by rfl⟩ : syracuseStep 246143 = 369215) B369215
theorem B999863 : Blo 163797 999863 := bstep (se 1 (by rfl) ⟨749897, by rfl⟩ : syracuseStep 999863 = 1499795) B1499795
theorem B246215 : Blo 163797 246215 := bstep (se 1 (by rfl) ⟨184661, by rfl⟩ : syracuseStep 246215 = 369323) B369323
theorem B1196495 : Blo 163797 1196495 := bstep (se 1 (by rfl) ⟨897371, by rfl⟩ : syracuseStep 1196495 = 1794743) B1794743
theorem B1589867 : Blo 163797 1589867 := bstep (se 1 (by rfl) ⟨1192400, by rfl⟩ : syracuseStep 1589867 = 2384801) B2384801
theorem B475901 : Blo 163797 475901 := bstep (se 3 (by rfl) ⟨89231, by rfl⟩ : syracuseStep 475901 = 178463) B178463
theorem B246569 : Blo 163797 246569 := bstep (se 2 (by rfl) ⟨92463, by rfl⟩ : syracuseStep 246569 = 184927) B184927
theorem B246575 : Blo 163797 246575 := bstep (se 1 (by rfl) ⟨184931, by rfl⟩ : syracuseStep 246575 = 369863) B369863
theorem B1196957 : Blo 163797 1196957 := bstep (se 3 (by rfl) ⟨224429, by rfl⟩ : syracuseStep 1196957 = 448859) B448859
theorem B246695 : Blo 163797 246695 := bstep (se 1 (by rfl) ⟨185021, by rfl⟩ : syracuseStep 246695 = 370043) B370043
theorem B279463 : Blo 163797 279463 := bstep (se 1 (by rfl) ⟨209597, by rfl⟩ : syracuseStep 279463 = 419195) B419195
theorem B246779 : Blo 163797 246779 := bstep (se 1 (by rfl) ⟨185084, by rfl⟩ : syracuseStep 246779 = 370169) B370169
theorem B246839 : Blo 163797 246839 := bstep (se 1 (by rfl) ⟨185129, by rfl⟩ : syracuseStep 246839 = 370259) B370259
theorem B279625 : Blo 163797 279625 := bstep (se 2 (by rfl) ⟨104859, by rfl⟩ : syracuseStep 279625 = 209719) B209719
theorem B279659 : Blo 163797 279659 := bstep (se 1 (by rfl) ⟨209744, by rfl⟩ : syracuseStep 279659 = 419489) B419489
theorem B246959 : Blo 163797 246959 := bstep (se 1 (by rfl) ⟨185219, by rfl⟩ : syracuseStep 246959 = 370439) B370439
theorem B935171 : Blo 163797 935171 := bstep (se 1 (by rfl) ⟨701378, by rfl⟩ : syracuseStep 935171 = 1402757) B1402757
theorem B247367 : Blo 163797 247367 := bstep (se 1 (by rfl) ⟨185525, by rfl⟩ : syracuseStep 247367 = 371051) B371051
theorem B837215 : Blo 163797 837215 := bstep (se 1 (by rfl) ⟨627911, by rfl⟩ : syracuseStep 837215 = 1255823) B1255823
theorem B804467 : Blo 163797 804467 := bstep (se 1 (by rfl) ⟨603350, by rfl⟩ : syracuseStep 804467 = 1206701) B1206701
theorem B247463 : Blo 163797 247463 := bstep (se 1 (by rfl) ⟨185597, by rfl⟩ : syracuseStep 247463 = 371195) B371195
theorem B247547 : Blo 163797 247547 := bstep (se 1 (by rfl) ⟨185660, by rfl⟩ : syracuseStep 247547 = 371321) B371321
theorem B247583 : Blo 163797 247583 := bstep (se 1 (by rfl) ⟨185687, by rfl⟩ : syracuseStep 247583 = 371375) B371375
theorem B247631 : Blo 163797 247631 := bstep (se 1 (by rfl) ⟨185723, by rfl⟩ : syracuseStep 247631 = 371447) B371447
theorem B247751 : Blo 163797 247751 := bstep (se 1 (by rfl) ⟨185813, by rfl⟩ : syracuseStep 247751 = 371627) B371627
theorem B935945 : Blo 163797 935945 := bstep (se 2 (by rfl) ⟨350979, by rfl⟩ : syracuseStep 935945 = 701959) B701959
theorem B248105 : Blo 163797 248105 := bstep (se 2 (by rfl) ⟨93039, by rfl⟩ : syracuseStep 248105 = 186079) B186079
theorem B248111 : Blo 163797 248111 := bstep (se 1 (by rfl) ⟨186083, by rfl⟩ : syracuseStep 248111 = 372167) B372167
theorem B280955 : Blo 163797 280955 := bstep (se 1 (by rfl) ⟨210716, by rfl⟩ : syracuseStep 280955 = 421433) B421433
theorem B575905 : Blo 163797 575905 := bstep (se 2 (by rfl) ⟨215964, by rfl⟩ : syracuseStep 575905 = 431929) B431929
theorem B10242541 : Blo 163797 10242541 := bstep (se 3 (by rfl) ⟨1920476, by rfl⟩ : syracuseStep 10242541 = 3840953) B3840953
theorem B1427975 : Blo 163797 1427975 := bstep (se 1 (by rfl) ⟨1070981, by rfl⟩ : syracuseStep 1427975 = 2141963) B2141963
theorem B248351 : Blo 163797 248351 := bstep (se 1 (by rfl) ⟨186263, by rfl⟩ : syracuseStep 248351 = 372527) B372527
theorem B281225 : Blo 163797 281225 := bstep (se 2 (by rfl) ⟨105459, by rfl⟩ : syracuseStep 281225 = 210919) B210919
theorem B248735 : Blo 163797 248735 := bstep (se 1 (by rfl) ⟨186551, by rfl⟩ : syracuseStep 248735 = 373103) B373103
theorem B248783 : Blo 163797 248783 := bstep (se 1 (by rfl) ⟨186587, by rfl⟩ : syracuseStep 248783 = 373175) B373175
theorem B936947 : Blo 163797 936947 := bstep (se 1 (by rfl) ⟨702710, by rfl⟩ : syracuseStep 936947 = 1405421) B1405421
theorem B248873 : Blo 163797 248873 := bstep (se 2 (by rfl) ⟨93327, by rfl⟩ : syracuseStep 248873 = 186655) B186655
theorem B248879 : Blo 163797 248879 := bstep (se 1 (by rfl) ⟨186659, by rfl⟩ : syracuseStep 248879 = 373319) B373319
theorem B248903 : Blo 163797 248903 := bstep (se 1 (by rfl) ⟨186677, by rfl⟩ : syracuseStep 248903 = 373355) B373355
theorem B249167 : Blo 163797 249167 := bstep (se 1 (by rfl) ⟨186875, by rfl⟩ : syracuseStep 249167 = 373751) B373751
theorem B249257 : Blo 163797 249257 := bstep (se 2 (by rfl) ⟨93471, by rfl⟩ : syracuseStep 249257 = 186943) B186943
theorem B7818767 : Blo 163797 7818767 := bstep (se 1 (by rfl) ⟨5864075, by rfl⟩ : syracuseStep 7818767 = 11728151) B11728151
theorem B249407 : Blo 163797 249407 := bstep (se 1 (by rfl) ⟨187055, by rfl⟩ : syracuseStep 249407 = 374111) B374111
theorem B249671 : Blo 163797 249671 := bstep (se 1 (by rfl) ⟨187253, by rfl⟩ : syracuseStep 249671 = 374507) B374507
theorem B282491 : Blo 163797 282491 := bstep (se 1 (by rfl) ⟨211868, by rfl⟩ : syracuseStep 282491 = 423737) B423737
theorem B249755 : Blo 163797 249755 := bstep (se 1 (by rfl) ⟨187316, by rfl⟩ : syracuseStep 249755 = 374633) B374633
theorem B381115 : Blo 163797 381115 := bstep (se 1 (by rfl) ⟨285836, by rfl⟩ : syracuseStep 381115 = 571673) B571673
theorem B282811 : Blo 163797 282811 := bstep (se 1 (by rfl) ⟨212108, by rfl⟩ : syracuseStep 282811 = 424217) B424217
theorem B3920075 : Blo 163797 3920075 := bstep (se 1 (by rfl) ⟨2940056, by rfl⟩ : syracuseStep 3920075 = 5880113) B5880113
theorem B283007 : Blo 163797 283007 := bstep (se 1 (by rfl) ⟨212255, by rfl⟩ : syracuseStep 283007 = 424511) B424511
theorem B938405 : Blo 163797 938405 := bstep (se 4 (by rfl) ⟨87975, by rfl⟩ : syracuseStep 938405 = 175951) B175951
theorem B184783 : Blo 163797 184783 := bstep (se 1 (by rfl) ⟨138587, by rfl⟩ : syracuseStep 184783 = 277175) B277175
theorem B250319 : Blo 163797 250319 := bstep (se 1 (by rfl) ⟨187739, by rfl⟩ : syracuseStep 250319 = 375479) B375479
theorem B250361 : Blo 163797 250361 := bstep (se 2 (by rfl) ⟨93885, by rfl⟩ : syracuseStep 250361 = 187771) B187771
theorem B250463 : Blo 163797 250463 := bstep (se 1 (by rfl) ⟨187847, by rfl⟩ : syracuseStep 250463 = 375695) B375695
theorem B676873 : Blo 163797 676873 := bstep (se 2 (by rfl) ⟨253827, by rfl⟩ : syracuseStep 676873 = 507655) B507655
theorem B250943 : Blo 163797 250943 := bstep (se 1 (by rfl) ⟨188207, by rfl⟩ : syracuseStep 250943 = 376415) B376415
theorem B1496141 : Blo 163797 1496141 := bstep (se 3 (by rfl) ⟨280526, by rfl⟩ : syracuseStep 1496141 = 561053) B561053
theorem B316523 : Blo 163797 316523 := bstep (se 1 (by rfl) ⟨237392, by rfl⟩ : syracuseStep 316523 = 474785) B474785
theorem B250985 : Blo 163797 250985 := bstep (se 2 (by rfl) ⟨94119, by rfl⟩ : syracuseStep 250985 = 188239) B188239
theorem B251087 : Blo 163797 251087 := bstep (se 1 (by rfl) ⟨188315, by rfl⟩ : syracuseStep 251087 = 376631) B376631
theorem B185755 : Blo 163797 185755 := bstep (se 1 (by rfl) ⟨139316, by rfl⟩ : syracuseStep 185755 = 278633) B278633
theorem B251291 : Blo 163797 251291 := bstep (se 1 (by rfl) ⟨188468, by rfl⟩ : syracuseStep 251291 = 376937) B376937
theorem B251513 : Blo 163797 251513 := bstep (se 2 (by rfl) ⟨94317, by rfl⟩ : syracuseStep 251513 = 188635) B188635
theorem B251615 : Blo 163797 251615 := bstep (se 1 (by rfl) ⟨188711, by rfl⟩ : syracuseStep 251615 = 377423) B377423
theorem B710639 : Blo 163797 710639 := bstep (se 1 (by rfl) ⟨532979, by rfl⟩ : syracuseStep 710639 = 1065959) B1065959
theorem B1071265 : Blo 163797 1071265 := bstep (se 2 (by rfl) ⟨401724, by rfl⟩ : syracuseStep 1071265 = 803449) B803449
theorem B481609 : Blo 163797 481609 := bstep (se 2 (by rfl) ⟨180603, by rfl⟩ : syracuseStep 481609 = 361207) B361207
theorem B186907 : Blo 163797 186907 := bstep (se 1 (by rfl) ⟨140180, by rfl⟩ : syracuseStep 186907 = 280361) B280361
theorem B4119113 : Blo 163797 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B416603 : Blo 163797 416603 := bstep (se 1 (by rfl) ⟨312452, by rfl⟩ : syracuseStep 416603 = 624905) B624905
theorem B1006573 : Blo 163797 1006573 := bstep (se 3 (by rfl) ⟨188732, by rfl⟩ : syracuseStep 1006573 = 377465) B377465
theorem B1072109 : Blo 163797 1072109 := bstep (se 3 (by rfl) ⟨201020, by rfl⟩ : syracuseStep 1072109 = 402041) B402041
theorem B318505 : Blo 163797 318505 := bstep (se 2 (by rfl) ⟨119439, by rfl⟩ : syracuseStep 318505 = 238879) B238879
theorem B416897 : Blo 163797 416897 := bstep (se 2 (by rfl) ⟨156336, by rfl⟩ : syracuseStep 416897 = 312673) B312673
theorem B187879 : Blo 163797 187879 := bstep (se 1 (by rfl) ⟨140909, by rfl⟩ : syracuseStep 187879 = 281819) B281819
theorem B3858043 : Blo 163797 3858043 := bstep (se 1 (by rfl) ⟨2893532, by rfl⟩ : syracuseStep 3858043 = 5787065) B5787065
theorem B941777 : Blo 163797 941777 := bstep (se 2 (by rfl) ⟨353166, by rfl⟩ : syracuseStep 941777 = 706333) B706333
theorem B4251527 : Blo 163797 4251527 := bstep (se 1 (by rfl) ⟨3188645, by rfl⟩ : syracuseStep 4251527 = 6377291) B6377291
theorem B417707 : Blo 163797 417707 := bstep (se 1 (by rfl) ⟨313280, by rfl⟩ : syracuseStep 417707 = 626561) B626561
theorem B188383 : Blo 163797 188383 := bstep (se 1 (by rfl) ⟨141287, by rfl⟩ : syracuseStep 188383 = 282575) B282575
theorem B942461 : Blo 163797 942461 := bstep (se 3 (by rfl) ⟨176711, by rfl⟩ : syracuseStep 942461 = 353423) B353423
theorem B418841 : Blo 163797 418841 := bstep (se 2 (by rfl) ⟨157065, by rfl⟩ : syracuseStep 418841 = 314131) B314131
theorem B1598629 : Blo 163797 1598629 := bstep (se 4 (by rfl) ⟨149871, by rfl⟩ : syracuseStep 1598629 = 299743) B299743
theorem B419681 : Blo 163797 419681 := bstep (se 2 (by rfl) ⟨157380, by rfl⟩ : syracuseStep 419681 = 314761) B314761
theorem B944237 : Blo 163797 944237 := bstep (se 3 (by rfl) ⟨177044, by rfl⟩ : syracuseStep 944237 = 354089) B354089
theorem B9038141 : Blo 163797 9038141 := bstep (se 3 (by rfl) ⟨1694651, by rfl⟩ : syracuseStep 9038141 = 3389303) B3389303
theorem B1272347 : Blo 163797 1272347 := bstep (se 1 (by rfl) ⟨954260, by rfl⟩ : syracuseStep 1272347 = 1908521) B1908521
theorem B224327 : Blo 163797 224327 := bstep (se 1 (by rfl) ⟨168245, by rfl⟩ : syracuseStep 224327 = 336491) B336491
theorem B716141 : Blo 163797 716141 := bstep (se 3 (by rfl) ⟨134276, by rfl⟩ : syracuseStep 716141 = 268553) B268553
theorem B421483 : Blo 163797 421483 := bstep (se 1 (by rfl) ⟨316112, by rfl⟩ : syracuseStep 421483 = 632225) B632225
theorem B421787 : Blo 163797 421787 := bstep (se 1 (by rfl) ⟨316340, by rfl⟩ : syracuseStep 421787 = 632681) B632681
theorem B1077371 : Blo 163797 1077371 := bstep (se 1 (by rfl) ⟨808028, by rfl⟩ : syracuseStep 1077371 = 1616057) B1616057
theorem B946835 : Blo 163797 946835 := bstep (se 1 (by rfl) ⟨710126, by rfl⟩ : syracuseStep 946835 = 1420253) B1420253
theorem B553769 : Blo 163797 553769 := bstep (se 2 (by rfl) ⟨207663, by rfl⟩ : syracuseStep 553769 = 415327) B415327
theorem B422921 : Blo 163797 422921 := bstep (se 2 (by rfl) ⟨158595, by rfl⟩ : syracuseStep 422921 = 317191) B317191
theorem B554039 : Blo 163797 554039 := bstep (se 1 (by rfl) ⟨415529, by rfl⟩ : syracuseStep 554039 = 831059) B831059
theorem B2389297 : Blo 163797 2389297 := bstep (se 2 (by rfl) ⟨895986, by rfl⟩ : syracuseStep 2389297 = 1791973) B1791973
theorem B173930165 : Blo 163797 173930165 := bstep (se 5 (by rfl) ⟨8152976, by rfl⟩ : syracuseStep 173930165 = 16305953) B16305953
theorem B4225283 : Blo 163797 4225283 := bstep (se 1 (by rfl) ⟨3168962, by rfl⟩ : syracuseStep 4225283 = 6337925) B6337925
theorem B948793 : Blo 163797 948793 := bstep (se 2 (by rfl) ⟨355797, by rfl⟩ : syracuseStep 948793 = 711595) B711595
theorem B555983 : Blo 163797 555983 := bstep (se 1 (by rfl) ⟨416987, by rfl⟩ : syracuseStep 555983 = 833975) B833975
theorem B949319 : Blo 163797 949319 := bstep (se 1 (by rfl) ⟨711989, by rfl⟩ : syracuseStep 949319 = 1423979) B1423979
theorem B622019 : Blo 163797 622019 := bstep (se 1 (by rfl) ⟨466514, by rfl⟩ : syracuseStep 622019 = 933029) B933029
theorem B163807 : Blo 163797 163807 := bstep (se 1 (by rfl) ⟨122855, by rfl⟩ : syracuseStep 163807 = 245711) B245711
theorem B164031 : Blo 163797 164031 := bstep (se 1 (by rfl) ⟨123023, by rfl⟩ : syracuseStep 164031 = 246047) B246047
theorem B164047 : Blo 163797 164047 := bstep (se 1 (by rfl) ⟨123035, by rfl⟩ : syracuseStep 164047 = 246071) B246071
theorem B164095 : Blo 163797 164095 := bstep (se 1 (by rfl) ⟨123071, by rfl⟩ : syracuseStep 164095 = 246143) B246143
theorem B164143 : Blo 163797 164143 := bstep (se 1 (by rfl) ⟨123107, by rfl⟩ : syracuseStep 164143 = 246215) B246215
theorem B35324219 : Blo 163797 35324219 := bstep (se 1 (by rfl) ⟨26493164, by rfl⟩ : syracuseStep 35324219 = 52986329) B52986329
theorem B164379 : Blo 163797 164379 := bstep (se 1 (by rfl) ⟨123284, by rfl⟩ : syracuseStep 164379 = 246569) B246569
theorem B164383 : Blo 163797 164383 := bstep (se 1 (by rfl) ⟨123287, by rfl⟩ : syracuseStep 164383 = 246575) B246575
theorem B164463 : Blo 163797 164463 := bstep (se 1 (by rfl) ⟨123347, by rfl⟩ : syracuseStep 164463 = 246695) B246695
theorem B164519 : Blo 163797 164519 := bstep (se 1 (by rfl) ⟨123389, by rfl⟩ : syracuseStep 164519 = 246779) B246779
theorem B164559 : Blo 163797 164559 := bstep (se 1 (by rfl) ⟨123419, by rfl⟩ : syracuseStep 164559 = 246839) B246839
theorem B197407 : Blo 163797 197407 := bstep (se 1 (by rfl) ⟨148055, by rfl⟩ : syracuseStep 197407 = 296111) B296111
theorem B164639 : Blo 163797 164639 := bstep (se 1 (by rfl) ⟨123479, by rfl⟩ : syracuseStep 164639 = 246959) B246959
theorem B623447 : Blo 163797 623447 := bstep (se 1 (by rfl) ⟨467585, by rfl⟩ : syracuseStep 623447 = 935171) B935171
theorem B2032613 : Blo 163797 2032613 := bstep (se 4 (by rfl) ⟨190557, by rfl⟩ : syracuseStep 2032613 = 381115) B381115
theorem B164911 : Blo 163797 164911 := bstep (se 1 (by rfl) ⟨123683, by rfl⟩ : syracuseStep 164911 = 247367) B247367
theorem B558143 : Blo 163797 558143 := bstep (se 1 (by rfl) ⟨418607, by rfl⟩ : syracuseStep 558143 = 837215) B837215
theorem B164975 : Blo 163797 164975 := bstep (se 1 (by rfl) ⟨123731, by rfl⟩ : syracuseStep 164975 = 247463) B247463
theorem B165031 : Blo 163797 165031 := bstep (se 1 (by rfl) ⟨123773, by rfl⟩ : syracuseStep 165031 = 247547) B247547
theorem B165055 : Blo 163797 165055 := bstep (se 1 (by rfl) ⟨123791, by rfl⟩ : syracuseStep 165055 = 247583) B247583
theorem B165087 : Blo 163797 165087 := bstep (se 1 (by rfl) ⟨123815, by rfl⟩ : syracuseStep 165087 = 247631) B247631
theorem B525599 : Blo 163797 525599 := bstep (se 1 (by rfl) ⟨394199, by rfl⟩ : syracuseStep 525599 = 788399) B788399
theorem B165167 : Blo 163797 165167 := bstep (se 1 (by rfl) ⟨123875, by rfl⟩ : syracuseStep 165167 = 247751) B247751
theorem B623963 : Blo 163797 623963 := bstep (se 1 (by rfl) ⟨467972, by rfl⟩ : syracuseStep 623963 = 935945) B935945
theorem B165403 : Blo 163797 165403 := bstep (se 1 (by rfl) ⟨124052, by rfl⟩ : syracuseStep 165403 = 248105) B248105
theorem B165407 : Blo 163797 165407 := bstep (se 1 (by rfl) ⟨124055, by rfl⟩ : syracuseStep 165407 = 248111) B248111
theorem B2131505 : Blo 163797 2131505 := bstep (se 2 (by rfl) ⟨799314, by rfl⟩ : syracuseStep 2131505 = 1598629) B1598629
theorem B951983 : Blo 163797 951983 := bstep (se 1 (by rfl) ⟨713987, by rfl⟩ : syracuseStep 951983 = 1427975) B1427975
theorem B165567 : Blo 163797 165567 := bstep (se 1 (by rfl) ⟨124175, by rfl⟩ : syracuseStep 165567 = 248351) B248351
theorem B165823 : Blo 163797 165823 := bstep (se 1 (by rfl) ⟨124367, by rfl⟩ : syracuseStep 165823 = 248735) B248735
theorem B165855 : Blo 163797 165855 := bstep (se 1 (by rfl) ⟨124391, by rfl⟩ : syracuseStep 165855 = 248783) B248783
theorem B624631 : Blo 163797 624631 := bstep (se 1 (by rfl) ⟨468473, by rfl⟩ : syracuseStep 624631 = 936947) B936947
theorem B165915 : Blo 163797 165915 := bstep (se 1 (by rfl) ⟨124436, by rfl⟩ : syracuseStep 165915 = 248873) B248873
theorem B165919 : Blo 163797 165919 := bstep (se 1 (by rfl) ⟨124439, by rfl⟩ : syracuseStep 165919 = 248879) B248879
theorem B165935 : Blo 163797 165935 := bstep (se 1 (by rfl) ⟨124451, by rfl⟩ : syracuseStep 165935 = 248903) B248903
theorem B1050839 : Blo 163797 1050839 := bstep (se 1 (by rfl) ⟨788129, by rfl⟩ : syracuseStep 1050839 = 1576259) B1576259
theorem B166111 : Blo 163797 166111 := bstep (se 1 (by rfl) ⟨124583, by rfl⟩ : syracuseStep 166111 = 249167) B249167
theorem B166171 : Blo 163797 166171 := bstep (se 1 (by rfl) ⟨124628, by rfl⟩ : syracuseStep 166171 = 249257) B249257
theorem B5212511 : Blo 163797 5212511 := bstep (se 1 (by rfl) ⟨3909383, by rfl⟩ : syracuseStep 5212511 = 7818767) B7818767
theorem B166271 : Blo 163797 166271 := bstep (se 1 (by rfl) ⟨124703, by rfl⟩ : syracuseStep 166271 = 249407) B249407
theorem B166447 : Blo 163797 166447 := bstep (se 1 (by rfl) ⟨124835, by rfl⟩ : syracuseStep 166447 = 249671) B249671
theorem B166503 : Blo 163797 166503 := bstep (se 1 (by rfl) ⟨124877, by rfl⟩ : syracuseStep 166503 = 249755) B249755
theorem B1575719 : Blo 163797 1575719 := bstep (se 1 (by rfl) ⟨1181789, by rfl⟩ : syracuseStep 1575719 = 2363579) B2363579
theorem B625603 : Blo 163797 625603 := bstep (se 1 (by rfl) ⟨469202, by rfl⟩ : syracuseStep 625603 = 938405) B938405
theorem B166879 : Blo 163797 166879 := bstep (se 1 (by rfl) ⟨125159, by rfl⟩ : syracuseStep 166879 = 250319) B250319
theorem B199675 : Blo 163797 199675 := bstep (se 1 (by rfl) ⟨149756, by rfl⟩ : syracuseStep 199675 = 299513) B299513
theorem B166907 : Blo 163797 166907 := bstep (se 1 (by rfl) ⟨125180, by rfl⟩ : syracuseStep 166907 = 250361) B250361
theorem B396343 : Blo 163797 396343 := bstep (se 1 (by rfl) ⟨297257, by rfl⟩ : syracuseStep 396343 = 594515) B594515
theorem B166975 : Blo 163797 166975 := bstep (se 1 (by rfl) ⟨125231, by rfl⟩ : syracuseStep 166975 = 250463) B250463
theorem B167295 : Blo 163797 167295 := bstep (se 1 (by rfl) ⟨125471, by rfl⟩ : syracuseStep 167295 = 250943) B250943
theorem B167323 : Blo 163797 167323 := bstep (se 1 (by rfl) ⟨125492, by rfl⟩ : syracuseStep 167323 = 250985) B250985
theorem B167391 : Blo 163797 167391 := bstep (se 1 (by rfl) ⟨125543, by rfl⟩ : syracuseStep 167391 = 251087) B251087
theorem B2624993 : Blo 163797 2624993 := bstep (se 2 (by rfl) ⟨984372, by rfl⟩ : syracuseStep 2624993 = 1968745) B1968745
theorem B167527 : Blo 163797 167527 := bstep (se 1 (by rfl) ⟨125645, by rfl⟩ : syracuseStep 167527 = 251291) B251291
theorem B5738165 : Blo 163797 5738165 := bstep (se 5 (by rfl) ⟨268976, by rfl⟩ : syracuseStep 5738165 = 537953) B537953
theorem B167675 : Blo 163797 167675 := bstep (se 1 (by rfl) ⟨125756, by rfl⟩ : syracuseStep 167675 = 251513) B251513
theorem B167743 : Blo 163797 167743 := bstep (se 1 (by rfl) ⟨125807, by rfl⟩ : syracuseStep 167743 = 251615) B251615
theorem B397295 : Blo 163797 397295 := bstep (se 1 (by rfl) ⟨297971, by rfl⟩ : syracuseStep 397295 = 595943) B595943
theorem B3084331 : Blo 163797 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B2560157 : Blo 163797 2560157 := bstep (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) B960059
theorem B626849 : Blo 163797 626849 := bstep (se 2 (by rfl) ⟨235068, by rfl⟩ : syracuseStep 626849 = 470137) B470137
theorem B201271 : Blo 163797 201271 := bstep (se 1 (by rfl) ⟨150953, by rfl⟩ : syracuseStep 201271 = 301907) B301907
theorem B561977 : Blo 163797 561977 := bstep (se 2 (by rfl) ⟨210741, by rfl⟩ : syracuseStep 561977 = 421483) B421483
theorem B529391 : Blo 163797 529391 := bstep (se 1 (by rfl) ⟨397043, by rfl⟩ : syracuseStep 529391 = 794087) B794087
theorem B1414169 : Blo 163797 1414169 := bstep (se 2 (by rfl) ⟨530313, by rfl⟩ : syracuseStep 1414169 = 1060627) B1060627
theorem B627851 : Blo 163797 627851 := bstep (se 1 (by rfl) ⟨470888, by rfl⟩ : syracuseStep 627851 = 941777) B941777
theorem B890041 : Blo 163797 890041 := bstep (se 2 (by rfl) ⟨333765, by rfl⟩ : syracuseStep 890041 = 667531) B667531
theorem B628307 : Blo 163797 628307 := bstep (se 1 (by rfl) ⟨471230, by rfl⟩ : syracuseStep 628307 = 942461) B942461
theorem B334163 : Blo 163797 334163 := bstep (se 1 (by rfl) ⟨250622, by rfl⟩ : syracuseStep 334163 = 501245) B501245
theorem B1907063 : Blo 163797 1907063 := bstep (se 1 (by rfl) ⟨1430297, by rfl⟩ : syracuseStep 1907063 = 2860595) B2860595
theorem B399755 : Blo 163797 399755 := bstep (se 1 (by rfl) ⟨299816, by rfl⟩ : syracuseStep 399755 = 599633) B599633
theorem B203239 : Blo 163797 203239 := bstep (se 1 (by rfl) ⟨152429, by rfl⟩ : syracuseStep 203239 = 304859) B304859
theorem B629491 : Blo 163797 629491 := bstep (se 1 (by rfl) ⟨472118, by rfl⟩ : syracuseStep 629491 = 944237) B944237
theorem B3185729 : Blo 163797 3185729 := bstep (se 2 (by rfl) ⟨1194648, by rfl⟩ : syracuseStep 3185729 = 2389297) B2389297
theorem B466651 : Blo 163797 466651 := bstep (se 1 (by rfl) ⟨349988, by rfl⟩ : syracuseStep 466651 = 699977) B699977
theorem B1580791 : Blo 163797 1580791 := bstep (se 1 (by rfl) ⟨1185593, by rfl⟩ : syracuseStep 1580791 = 2371187) B2371187
theorem B1056503 : Blo 163797 1056503 := bstep (se 1 (by rfl) ⟨792377, by rfl⟩ : syracuseStep 1056503 = 1584755) B1584755
theorem B598205 : Blo 163797 598205 := bstep (se 3 (by rfl) ⟨112163, by rfl⟩ : syracuseStep 598205 = 224327) B224327
theorem B631223 : Blo 163797 631223 := bstep (se 1 (by rfl) ⟨473417, by rfl⟩ : syracuseStep 631223 = 946835) B946835
theorem B369179 : Blo 163797 369179 := bstep (se 1 (by rfl) ⟨276884, by rfl⟩ : syracuseStep 369179 = 553769) B553769
theorem B369359 : Blo 163797 369359 := bstep (se 1 (by rfl) ⟨277019, by rfl⟩ : syracuseStep 369359 = 554039) B554039
theorem B1418269 : Blo 163797 1418269 := bstep (se 3 (by rfl) ⟨265925, by rfl⟩ : syracuseStep 1418269 = 531851) B531851
theorem B369737 : Blo 163797 369737 := bstep (se 2 (by rfl) ⟨138651, by rfl⟩ : syracuseStep 369737 = 277303) B277303
theorem B632393 : Blo 163797 632393 := bstep (se 2 (by rfl) ⟨237147, by rfl⟩ : syracuseStep 632393 = 474295) B474295
theorem B370655 : Blo 163797 370655 := bstep (se 1 (by rfl) ⟨277991, by rfl⟩ : syracuseStep 370655 = 555983) B555983
theorem B632879 : Blo 163797 632879 := bstep (se 1 (by rfl) ⟨474659, by rfl⟩ : syracuseStep 632879 = 949319) B949319
theorem B666119 : Blo 163797 666119 := bstep (se 1 (by rfl) ⟨499589, by rfl⟩ : syracuseStep 666119 = 999179) B999179
theorem B1354427 : Blo 163797 1354427 := bstep (se 1 (by rfl) ⟨1015820, by rfl⟩ : syracuseStep 1354427 = 2031641) B2031641
theorem B666575 : Blo 163797 666575 := bstep (se 1 (by rfl) ⟨499931, by rfl⟩ : syracuseStep 666575 = 999863) B999863
theorem B371663 : Blo 163797 371663 := bstep (se 1 (by rfl) ⟨278747, by rfl⟩ : syracuseStep 371663 = 557495) B557495
theorem B797663 : Blo 163797 797663 := bstep (se 1 (by rfl) ⟨598247, by rfl⟩ : syracuseStep 797663 = 1196495) B1196495
theorem B371753 : Blo 163797 371753 := bstep (se 2 (by rfl) ⟨139407, by rfl⟩ : syracuseStep 371753 = 278815) B278815
theorem B1059911 : Blo 163797 1059911 := bstep (se 1 (by rfl) ⟨794933, by rfl⟩ : syracuseStep 1059911 = 1589867) B1589867
theorem B371987 : Blo 163797 371987 := bstep (se 1 (by rfl) ⟨278990, by rfl⟩ : syracuseStep 371987 = 557981) B557981
theorem B797971 : Blo 163797 797971 := bstep (se 1 (by rfl) ⟨598478, by rfl⟩ : syracuseStep 797971 = 1196957) B1196957
theorem B372023 : Blo 163797 372023 := bstep (se 1 (by rfl) ⟨279017, by rfl⟩ : syracuseStep 372023 = 558035) B558035
theorem B536311 : Blo 163797 536311 := bstep (se 1 (by rfl) ⟨402233, by rfl⟩ : syracuseStep 536311 = 804467) B804467
theorem B700285 : Blo 163797 700285 := bstep (se 3 (by rfl) ⟨131303, by rfl⟩ : syracuseStep 700285 = 262607) B262607
theorem B372617 : Blo 163797 372617 := bstep (se 2 (by rfl) ⟨139731, by rfl⟩ : syracuseStep 372617 = 279463) B279463
theorem B372833 : Blo 163797 372833 := bstep (se 2 (by rfl) ⟨139812, by rfl⟩ : syracuseStep 372833 = 279625) B279625
theorem B635111 : Blo 163797 635111 := bstep (se 1 (by rfl) ⟨476333, by rfl⟩ : syracuseStep 635111 = 952667) B952667
theorem B2568581 : Blo 163797 2568581 := bstep (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) B481609
theorem B373499 : Blo 163797 373499 := bstep (se 1 (by rfl) ⟨280124, by rfl⟩ : syracuseStep 373499 = 560249) B560249
theorem B1684435 : Blo 163797 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B373715 : Blo 163797 373715 := bstep (se 1 (by rfl) ⟨280286, by rfl⟩ : syracuseStep 373715 = 560573) B560573
theorem B1422643 : Blo 163797 1422643 := bstep (se 1 (by rfl) ⟨1066982, by rfl⟩ : syracuseStep 1422643 = 2133965) B2133965
theorem B374183 : Blo 163797 374183 := bstep (se 1 (by rfl) ⟨280637, by rfl⟩ : syracuseStep 374183 = 561275) B561275
theorem B374291 : Blo 163797 374291 := bstep (se 1 (by rfl) ⟨280718, by rfl⟩ : syracuseStep 374291 = 561437) B561437
theorem B374363 : Blo 163797 374363 := bstep (se 1 (by rfl) ⟨280772, by rfl⟩ : syracuseStep 374363 = 561545) B561545
theorem B767873 : Blo 163797 767873 := bstep (se 2 (by rfl) ⟨287952, by rfl⟩ : syracuseStep 767873 = 575905) B575905
theorem B997427 : Blo 163797 997427 := bstep (se 1 (by rfl) ⟨748070, by rfl⟩ : syracuseStep 997427 = 1496141) B1496141
theorem B211015 : Blo 163797 211015 := bstep (se 1 (by rfl) ⟨158261, by rfl⟩ : syracuseStep 211015 = 316523) B316523
theorem B374975 : Blo 163797 374975 := bstep (se 1 (by rfl) ⟨281231, by rfl⟩ : syracuseStep 374975 = 562463) B562463
theorem B702695 : Blo 163797 702695 := bstep (se 1 (by rfl) ⟨527021, by rfl⟩ : syracuseStep 702695 = 1054043) B1054043
theorem B277033 : Blo 163797 277033 := bstep (se 2 (by rfl) ⟨103887, by rfl⟩ : syracuseStep 277033 = 207775) B207775
theorem B473759 : Blo 163797 473759 := bstep (se 1 (by rfl) ⟨355319, by rfl⟩ : syracuseStep 473759 = 710639) B710639
theorem B834785 : Blo 163797 834785 := bstep (se 2 (by rfl) ⟨313044, by rfl⟩ : syracuseStep 834785 = 626089) B626089
theorem B277735 : Blo 163797 277735 := bstep (se 1 (by rfl) ⟨208301, by rfl⟩ : syracuseStep 277735 = 416603) B416603
theorem B1424627 : Blo 163797 1424627 := bstep (se 1 (by rfl) ⟨1068470, by rfl⟩ : syracuseStep 1424627 = 2136941) B2136941
theorem B933281 : Blo 163797 933281 := bstep (se 2 (by rfl) ⟨349980, by rfl⟩ : syracuseStep 933281 = 699961) B699961
theorem B277931 : Blo 163797 277931 := bstep (se 1 (by rfl) ⟨208448, by rfl⟩ : syracuseStep 277931 = 416897) B416897
theorem B376235 : Blo 163797 376235 := bstep (se 1 (by rfl) ⟨282176, by rfl⟩ : syracuseStep 376235 = 564353) B564353
theorem B376271 : Blo 163797 376271 := bstep (se 1 (by rfl) ⟨282203, by rfl⟩ : syracuseStep 376271 = 564407) B564407
theorem B835433 : Blo 163797 835433 := bstep (se 2 (by rfl) ⟨313287, by rfl⟩ : syracuseStep 835433 = 626575) B626575
theorem B2834351 : Blo 163797 2834351 := bstep (se 1 (by rfl) ⟨2125763, by rfl⟩ : syracuseStep 2834351 = 4251527) B4251527
theorem B278471 : Blo 163797 278471 := bstep (se 1 (by rfl) ⟨208853, by rfl⟩ : syracuseStep 278471 = 417707) B417707
theorem B376775 : Blo 163797 376775 := bstep (se 1 (by rfl) ⟨282581, by rfl⟩ : syracuseStep 376775 = 565163) B565163
theorem B245951 : Blo 163797 245951 := bstep (se 1 (by rfl) ⟨184463, by rfl⟩ : syracuseStep 245951 = 368927) B368927
theorem B377081 : Blo 163797 377081 := bstep (se 2 (by rfl) ⟨141405, by rfl⟩ : syracuseStep 377081 = 282811) B282811
theorem B377135 : Blo 163797 377135 := bstep (se 1 (by rfl) ⟨282851, by rfl⟩ : syracuseStep 377135 = 565703) B565703
theorem B377351 : Blo 163797 377351 := bstep (se 1 (by rfl) ⟨283013, by rfl⟩ : syracuseStep 377351 = 566027) B566027
theorem B246377 : Blo 163797 246377 := bstep (se 2 (by rfl) ⟨92391, by rfl⟩ : syracuseStep 246377 = 184783) B184783
theorem B246383 : Blo 163797 246383 := bstep (se 1 (by rfl) ⟨184787, by rfl⟩ : syracuseStep 246383 = 369575) B369575
theorem B279227 : Blo 163797 279227 := bstep (se 1 (by rfl) ⟨209420, by rfl⟩ : syracuseStep 279227 = 418841) B418841
theorem B377531 : Blo 163797 377531 := bstep (se 1 (by rfl) ⟨283148, by rfl⟩ : syracuseStep 377531 = 566297) B566297
theorem B705617 : Blo 163797 705617 := bstep (se 2 (by rfl) ⟨264606, by rfl⟩ : syracuseStep 705617 = 529213) B529213
theorem B247007 : Blo 163797 247007 := bstep (se 1 (by rfl) ⟨185255, by rfl⟩ : syracuseStep 247007 = 370511) B370511
theorem B247019 : Blo 163797 247019 := bstep (se 1 (by rfl) ⟨185264, by rfl⟩ : syracuseStep 247019 = 370529) B370529
theorem B279787 : Blo 163797 279787 := bstep (se 1 (by rfl) ⟨209840, by rfl⟩ : syracuseStep 279787 = 419681) B419681
theorem B902497 : Blo 163797 902497 := bstep (se 2 (by rfl) ⟨338436, by rfl⟩ : syracuseStep 902497 = 676873) B676873
theorem B247403 : Blo 163797 247403 := bstep (se 1 (by rfl) ⟨185552, by rfl⟩ : syracuseStep 247403 = 371105) B371105
theorem B247487 : Blo 163797 247487 := bstep (se 1 (by rfl) ⟨185615, by rfl⟩ : syracuseStep 247487 = 371231) B371231
theorem B247673 : Blo 163797 247673 := bstep (se 2 (by rfl) ⟨92877, by rfl⟩ : syracuseStep 247673 = 185755) B185755
theorem B477427 : Blo 163797 477427 := bstep (se 1 (by rfl) ⟨358070, by rfl⟩ : syracuseStep 477427 = 716141) B716141
theorem B248423 : Blo 163797 248423 := bstep (se 1 (by rfl) ⟨186317, by rfl⟩ : syracuseStep 248423 = 372635) B372635
theorem B281191 : Blo 163797 281191 := bstep (se 1 (by rfl) ⟨210893, by rfl⟩ : syracuseStep 281191 = 421787) B421787
theorem B248615 : Blo 163797 248615 := bstep (se 1 (by rfl) ⟨186461, by rfl⟩ : syracuseStep 248615 = 372923) B372923
theorem B674681 : Blo 163797 674681 := bstep (se 2 (by rfl) ⟨253005, by rfl⟩ : syracuseStep 674681 = 506011) B506011
theorem B1428353 : Blo 163797 1428353 := bstep (se 2 (by rfl) ⟨535632, by rfl⟩ : syracuseStep 1428353 = 1071265) B1071265
theorem B248939 : Blo 163797 248939 := bstep (se 1 (by rfl) ⟨186704, by rfl⟩ : syracuseStep 248939 = 373409) B373409
theorem B249179 : Blo 163797 249179 := bstep (se 1 (by rfl) ⟨186884, by rfl⟩ : syracuseStep 249179 = 373769) B373769
theorem B281947 : Blo 163797 281947 := bstep (se 1 (by rfl) ⟨211460, by rfl⟩ : syracuseStep 281947 = 422921) B422921
theorem B249209 : Blo 163797 249209 := bstep (se 2 (by rfl) ⟨93453, by rfl⟩ : syracuseStep 249209 = 186907) B186907
theorem B249215 : Blo 163797 249215 := bstep (se 1 (by rfl) ⟨186911, by rfl⟩ : syracuseStep 249215 = 373823) B373823
theorem B1265057 : Blo 163797 1265057 := bstep (se 2 (by rfl) ⟨474396, by rfl⟩ : syracuseStep 1265057 = 948793) B948793
theorem B839159 : Blo 163797 839159 := bstep (se 1 (by rfl) ⟨629369, by rfl⟩ : syracuseStep 839159 = 1258739) B1258739
theorem B115953443 : Blo 163797 115953443 := bstep (se 1 (by rfl) ⟨86965082, by rfl⟩ : syracuseStep 115953443 = 173930165) B173930165
theorem B249839 : Blo 163797 249839 := bstep (se 1 (by rfl) ⟨187379, by rfl⟩ : syracuseStep 249839 = 374759) B374759
theorem B184315 : Blo 163797 184315 := bstep (se 1 (by rfl) ⟨138236, by rfl⟩ : syracuseStep 184315 = 276473) B276473
theorem B249851 : Blo 163797 249851 := bstep (se 1 (by rfl) ⟨187388, by rfl⟩ : syracuseStep 249851 = 374777) B374777
theorem B249911 : Blo 163797 249911 := bstep (se 1 (by rfl) ⟨187433, by rfl⟩ : syracuseStep 249911 = 374867) B374867
theorem B184423 : Blo 163797 184423 := bstep (se 1 (by rfl) ⟨138317, by rfl⟩ : syracuseStep 184423 = 276635) B276635
theorem B249959 : Blo 163797 249959 := bstep (se 1 (by rfl) ⟨187469, by rfl⟩ : syracuseStep 249959 = 374939) B374939
theorem B184495 : Blo 163797 184495 := bstep (se 1 (by rfl) ⟨138371, by rfl⟩ : syracuseStep 184495 = 276743) B276743
theorem B250031 : Blo 163797 250031 := bstep (se 1 (by rfl) ⟨187523, by rfl⟩ : syracuseStep 250031 = 375047) B375047
theorem B5099719 : Blo 163797 5099719 := bstep (se 1 (by rfl) ⟨3824789, by rfl⟩ : syracuseStep 5099719 = 7649579) B7649579
theorem B1429751 : Blo 163797 1429751 := bstep (se 1 (by rfl) ⟨1072313, by rfl⟩ : syracuseStep 1429751 = 2144627) B2144627
theorem B4837643 : Blo 163797 4837643 := bstep (se 1 (by rfl) ⟨3628232, by rfl⟩ : syracuseStep 4837643 = 7256465) B7256465
theorem B250235 : Blo 163797 250235 := bstep (se 1 (by rfl) ⟨187676, by rfl⟩ : syracuseStep 250235 = 375353) B375353
theorem B1790333 : Blo 163797 1790333 := bstep (se 3 (by rfl) ⟨335687, by rfl⟩ : syracuseStep 1790333 = 671375) B671375
theorem B1004141 : Blo 163797 1004141 := bstep (se 3 (by rfl) ⟨188276, by rfl⟩ : syracuseStep 1004141 = 376553) B376553
theorem B250505 : Blo 163797 250505 := bstep (se 2 (by rfl) ⟨93939, by rfl⟩ : syracuseStep 250505 = 187879) B187879
theorem B185179 : Blo 163797 185179 := bstep (se 1 (by rfl) ⟨138884, by rfl⟩ : syracuseStep 185179 = 277769) B277769
theorem B250715 : Blo 163797 250715 := bstep (se 1 (by rfl) ⟨188036, by rfl⟩ : syracuseStep 250715 = 376073) B376073
theorem B414679 : Blo 163797 414679 := bstep (se 1 (by rfl) ⟨311009, by rfl⟩ : syracuseStep 414679 = 622019) B622019
theorem B251177 : Blo 163797 251177 := bstep (se 2 (by rfl) ⟨94191, by rfl⟩ : syracuseStep 251177 = 188383) B188383
theorem B251375 : Blo 163797 251375 := bstep (se 1 (by rfl) ⟨188531, by rfl⟩ : syracuseStep 251375 = 377063) B377063
theorem B1267487 : Blo 163797 1267487 := bstep (se 1 (by rfl) ⟨950615, by rfl⟩ : syracuseStep 1267487 = 1901231) B1901231
theorem B350023 : Blo 163797 350023 := bstep (se 1 (by rfl) ⟨262517, by rfl⟩ : syracuseStep 350023 = 525035) B525035
theorem B317267 : Blo 163797 317267 := bstep (se 1 (by rfl) ⟨237950, by rfl⟩ : syracuseStep 317267 = 475901) B475901
theorem B350075 : Blo 163797 350075 := bstep (se 1 (by rfl) ⟨262556, by rfl⟩ : syracuseStep 350075 = 525113) B525113
theorem B186439 : Blo 163797 186439 := bstep (se 1 (by rfl) ⟨139829, by rfl⟩ : syracuseStep 186439 = 279659) B279659
theorem B317753 : Blo 163797 317753 := bstep (se 2 (by rfl) ⟨119157, by rfl⟩ : syracuseStep 317753 = 238315) B238315
theorem B3561803 : Blo 163797 3561803 := bstep (se 1 (by rfl) ⟨2671352, by rfl⟩ : syracuseStep 3561803 = 5342705) B5342705
theorem B416623 : Blo 163797 416623 := bstep (se 1 (by rfl) ⟨312467, by rfl⟩ : syracuseStep 416623 = 624935) B624935
theorem B285563 : Blo 163797 285563 := bstep (se 1 (by rfl) ⟨214172, by rfl⟩ : syracuseStep 285563 = 428345) B428345
theorem B187303 : Blo 163797 187303 := bstep (se 1 (by rfl) ⟨140477, by rfl⟩ : syracuseStep 187303 = 280955) B280955
theorem B351211 : Blo 163797 351211 := bstep (se 1 (by rfl) ⟨263408, by rfl⟩ : syracuseStep 351211 = 526817) B526817
theorem B187483 : Blo 163797 187483 := bstep (se 1 (by rfl) ⟨140612, by rfl⟩ : syracuseStep 187483 = 281225) B281225
theorem B1596631 : Blo 163797 1596631 := bstep (se 1 (by rfl) ⟨1197473, by rfl⟩ : syracuseStep 1596631 = 2394947) B2394947
theorem B417271 : Blo 163797 417271 := bstep (se 1 (by rfl) ⟨312953, by rfl⟩ : syracuseStep 417271 = 625907) B625907
theorem B843385 : Blo 163797 843385 := bstep (se 2 (by rfl) ⟨316269, by rfl⟩ : syracuseStep 843385 = 632539) B632539
theorem B188327 : Blo 163797 188327 := bstep (se 1 (by rfl) ⟨141245, by rfl⟩ : syracuseStep 188327 = 282491) B282491
theorem B1269827 : Blo 163797 1269827 := bstep (se 1 (by rfl) ⟨952370, by rfl⟩ : syracuseStep 1269827 = 1904741) B1904741
theorem B2613383 : Blo 163797 2613383 := bstep (se 1 (by rfl) ⟨1960037, by rfl⟩ : syracuseStep 2613383 = 3920075) B3920075
theorem B188671 : Blo 163797 188671 := bstep (se 1 (by rfl) ⟨141503, by rfl⟩ : syracuseStep 188671 = 283007) B283007
theorem B745757 : Blo 163797 745757 := bstep (se 3 (by rfl) ⟨139829, by rfl⟩ : syracuseStep 745757 = 279659) B279659
theorem B13656721 : Blo 163797 13656721 := bstep (se 2 (by rfl) ⟨5121270, by rfl⟩ : syracuseStep 13656721 = 10242541) B10242541
theorem B714041 : Blo 163797 714041 := bstep (se 2 (by rfl) ⟨267765, by rfl⟩ : syracuseStep 714041 = 535531) B535531
theorem B714365 : Blo 163797 714365 := bstep (se 3 (by rfl) ⟨133943, by rfl⟩ : syracuseStep 714365 = 267887) B267887
theorem B2746075 : Blo 163797 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B3860261 : Blo 163797 3860261 := bstep (se 4 (by rfl) ⟨361899, by rfl⟩ : syracuseStep 3860261 = 723799) B723799
theorem B714739 : Blo 163797 714739 := bstep (se 1 (by rfl) ⟨536054, by rfl⟩ : syracuseStep 714739 = 1072109) B1072109
theorem B1797167 : Blo 163797 1797167 := bstep (se 1 (by rfl) ⟨1347875, by rfl⟩ : syracuseStep 1797167 = 2695751) B2695751
theorem B6025427 : Blo 163797 6025427 := bstep (se 1 (by rfl) ⟨4519070, by rfl⟩ : syracuseStep 6025427 = 9038141) B9038141
theorem B1274167 : Blo 163797 1274167 := bstep (se 1 (by rfl) ⟨955625, by rfl⟩ : syracuseStep 1274167 = 1911251) B1911251
theorem B848231 : Blo 163797 848231 := bstep (se 1 (by rfl) ⟨636173, by rfl⟩ : syracuseStep 848231 = 1272347) B1272347
theorem B356815 : Blo 163797 356815 := bstep (se 1 (by rfl) ⟨267611, by rfl⟩ : syracuseStep 356815 = 535223) B535223
theorem B488767 : Blo 163797 488767 := bstep (se 1 (by rfl) ⟨366575, by rfl⟩ : syracuseStep 488767 = 733151) B733151
theorem B1602935 : Blo 163797 1602935 := bstep (se 1 (by rfl) ⟨1202201, by rfl⟩ : syracuseStep 1602935 = 2404403) B2404403
theorem B718247 : Blo 163797 718247 := bstep (se 1 (by rfl) ⟨538685, by rfl⟩ : syracuseStep 718247 = 1077371) B1077371
theorem B1602989 : Blo 163797 1602989 := bstep (se 3 (by rfl) ⟨300560, by rfl⟩ : syracuseStep 1602989 = 601121) B601121
theorem B2127815 : Blo 163797 2127815 := bstep (se 1 (by rfl) ⟨1595861, by rfl⟩ : syracuseStep 2127815 = 3191723) B3191723
theorem B2717873 : Blo 163797 2717873 := bstep (se 2 (by rfl) ⟨1019202, by rfl⟩ : syracuseStep 2717873 = 2038405) B2038405
theorem B1013971 : Blo 163797 1013971 := bstep (se 1 (by rfl) ⟨760478, by rfl⟩ : syracuseStep 1013971 = 1520957) B1520957
theorem B424399 : Blo 163797 424399 := bstep (se 1 (by rfl) ⟨318299, by rfl⟩ : syracuseStep 424399 = 636599) B636599
theorem B555551 : Blo 163797 555551 := bstep (se 1 (by rfl) ⟨416663, by rfl⟩ : syracuseStep 555551 = 833327) B833327
theorem B1342097 : Blo 163797 1342097 := bstep (se 2 (by rfl) ⟨503286, by rfl⟩ : syracuseStep 1342097 = 1006573) B1006573
theorem B424673 : Blo 163797 424673 := bstep (se 2 (by rfl) ⟨159252, by rfl⟩ : syracuseStep 424673 = 318505) B318505
theorem B2816855 : Blo 163797 2816855 := bstep (se 1 (by rfl) ⟨2112641, by rfl⟩ : syracuseStep 2816855 = 4225283) B4225283
theorem B1244645 : Blo 163797 1244645 := bstep (se 4 (by rfl) ⟨116685, by rfl⟩ : syracuseStep 1244645 = 233371) B233371
theorem B5144057 : Blo 163797 5144057 := bstep (se 2 (by rfl) ⟨1929021, by rfl⟩ : syracuseStep 5144057 = 3858043) B3858043
theorem B163967 : Blo 163797 163967 := bstep (se 1 (by rfl) ⟨122975, by rfl⟩ : syracuseStep 163967 = 245951) B245951
theorem B164251 : Blo 163797 164251 := bstep (se 1 (by rfl) ⟨123188, by rfl⟩ : syracuseStep 164251 = 246377) B246377
theorem B164255 : Blo 163797 164255 := bstep (se 1 (by rfl) ⟨123191, by rfl⟩ : syracuseStep 164255 = 246383) B246383
theorem B164671 : Blo 163797 164671 := bstep (se 1 (by rfl) ⟨123503, by rfl⟩ : syracuseStep 164671 = 247007) B247007
theorem B164679 : Blo 163797 164679 := bstep (se 1 (by rfl) ⟨123509, by rfl⟩ : syracuseStep 164679 = 247019) B247019
theorem B164935 : Blo 163797 164935 := bstep (se 1 (by rfl) ⟨123701, by rfl⟩ : syracuseStep 164935 = 247403) B247403
theorem B164991 : Blo 163797 164991 := bstep (se 1 (by rfl) ⟨123743, by rfl⟩ : syracuseStep 164991 = 247487) B247487
theorem B165115 : Blo 163797 165115 := bstep (se 1 (by rfl) ⟨123836, by rfl⟩ : syracuseStep 165115 = 247673) B247673
theorem B3475007 : Blo 163797 3475007 := bstep (se 1 (by rfl) ⟨2606255, by rfl⟩ : syracuseStep 3475007 = 5212511) B5212511
theorem B165615 : Blo 163797 165615 := bstep (se 1 (by rfl) ⟨124211, by rfl⟩ : syracuseStep 165615 = 248423) B248423
theorem B1050479 : Blo 163797 1050479 := bstep (se 1 (by rfl) ⟨787859, by rfl⟩ : syracuseStep 1050479 = 1575719) B1575719
theorem B165743 : Blo 163797 165743 := bstep (se 1 (by rfl) ⟨124307, by rfl⟩ : syracuseStep 165743 = 248615) B248615
theorem B952235 : Blo 163797 952235 := bstep (se 1 (by rfl) ⟨714176, by rfl⟩ : syracuseStep 952235 = 1428353) B1428353
theorem B165959 : Blo 163797 165959 := bstep (se 1 (by rfl) ⟨124469, by rfl⟩ : syracuseStep 165959 = 248939) B248939
theorem B166119 : Blo 163797 166119 := bstep (se 1 (by rfl) ⟨124589, by rfl⟩ : syracuseStep 166119 = 249179) B249179
theorem B166139 : Blo 163797 166139 := bstep (se 1 (by rfl) ⟨124604, by rfl⟩ : syracuseStep 166139 = 249209) B249209
theorem B166143 : Blo 163797 166143 := bstep (se 1 (by rfl) ⟨124607, by rfl⟩ : syracuseStep 166143 = 249215) B249215
theorem B559439 : Blo 163797 559439 := bstep (se 1 (by rfl) ⟨419579, by rfl⟩ : syracuseStep 559439 = 839159) B839159
theorem B77302295 : Blo 163797 77302295 := bstep (se 1 (by rfl) ⟨57976721, by rfl⟩ : syracuseStep 77302295 = 115953443) B115953443
theorem B1083941 : Blo 163797 1083941 := bstep (se 4 (by rfl) ⟨101619, by rfl⟩ : syracuseStep 1083941 = 203239) B203239
theorem B952985 : Blo 163797 952985 := bstep (se 2 (by rfl) ⟨357369, by rfl⟩ : syracuseStep 952985 = 714739) B714739
theorem B264863 : Blo 163797 264863 := bstep (se 1 (by rfl) ⟨198647, by rfl⟩ : syracuseStep 264863 = 397295) B397295
theorem B166559 : Blo 163797 166559 := bstep (se 1 (by rfl) ⟨124919, by rfl⟩ : syracuseStep 166559 = 249839) B249839
theorem B166567 : Blo 163797 166567 := bstep (se 1 (by rfl) ⟨124925, by rfl⟩ : syracuseStep 166567 = 249851) B249851
theorem B166607 : Blo 163797 166607 := bstep (se 1 (by rfl) ⟨124955, by rfl⟩ : syracuseStep 166607 = 249911) B249911
theorem B166639 : Blo 163797 166639 := bstep (se 1 (by rfl) ⟨124979, by rfl⟩ : syracuseStep 166639 = 249959) B249959
theorem B1706771 : Blo 163797 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B166687 : Blo 163797 166687 := bstep (se 1 (by rfl) ⟨125015, by rfl⟩ : syracuseStep 166687 = 250031) B250031
theorem B953167 : Blo 163797 953167 := bstep (se 1 (by rfl) ⟨714875, by rfl⟩ : syracuseStep 953167 = 1429751) B1429751
theorem B166823 : Blo 163797 166823 := bstep (se 1 (by rfl) ⟨125117, by rfl⟩ : syracuseStep 166823 = 250235) B250235
theorem B167003 : Blo 163797 167003 := bstep (se 1 (by rfl) ⟨125252, by rfl⟩ : syracuseStep 167003 = 250505) B250505
theorem B167143 : Blo 163797 167143 := bstep (se 1 (by rfl) ⟨125357, by rfl⟩ : syracuseStep 167143 = 250715) B250715
theorem B167451 : Blo 163797 167451 := bstep (se 1 (by rfl) ⟨125588, by rfl⟩ : syracuseStep 167451 = 251177) B251177
theorem B167583 : Blo 163797 167583 := bstep (se 1 (by rfl) ⟨125687, by rfl⟩ : syracuseStep 167583 = 251375) B251375
theorem B233383 : Blo 163797 233383 := bstep (se 1 (by rfl) ⟨175037, by rfl⟩ : syracuseStep 233383 = 350075) B350075
theorem B528457 : Blo 163797 528457 := bstep (se 2 (by rfl) ⟨198171, by rfl⟩ : syracuseStep 528457 = 396343) B396343
theorem B1052837 : Blo 163797 1052837 := bstep (se 4 (by rfl) ⟨98703, by rfl⟩ : syracuseStep 1052837 = 197407) B197407
theorem B266503 : Blo 163797 266503 := bstep (se 1 (by rfl) ⟨199877, by rfl⟩ : syracuseStep 266503 = 399755) B399755
theorem B1742255 : Blo 163797 1742255 := bstep (se 1 (by rfl) ⟨1306691, by rfl⟩ : syracuseStep 1742255 = 2613383) B2613383
theorem B497171 : Blo 163797 497171 := bstep (se 1 (by rfl) ⟨372878, by rfl⟩ : syracuseStep 497171 = 745757) B745757
theorem B268361 : Blo 163797 268361 := bstep (se 2 (by rfl) ⟨100635, by rfl⟩ : syracuseStep 268361 = 201271) B201271
theorem B891101 : Blo 163797 891101 := bstep (se 3 (by rfl) ⟨167081, by rfl⟩ : syracuseStep 891101 = 334163) B334163
theorem B1186721 : Blo 163797 1186721 := bstep (se 2 (by rfl) ⟨445020, by rfl⟩ : syracuseStep 1186721 = 890041) B890041
theorem B531775 : Blo 163797 531775 := bstep (se 1 (by rfl) ⟨398831, by rfl⟩ : syracuseStep 531775 = 797663) B797663
theorem B761501 : Blo 163797 761501 := bstep (se 3 (by rfl) ⟨142781, by rfl⟩ : syracuseStep 761501 = 285563) B285563
theorem B466697 : Blo 163797 466697 := bstep (se 2 (by rfl) ⟨175011, by rfl⟩ : syracuseStep 466697 = 350023) B350023
theorem B565487 : Blo 163797 565487 := bstep (se 1 (by rfl) ⟨424115, by rfl⟩ : syracuseStep 565487 = 848231) B848231
theorem B1712387 : Blo 163797 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B1351961 : Blo 163797 1351961 := bstep (se 2 (by rfl) ⟨506985, by rfl⟩ : syracuseStep 1351961 = 1013971) B1013971
theorem B565865 : Blo 163797 565865 := bstep (se 2 (by rfl) ⟨212199, by rfl⟩ : syracuseStep 565865 = 424399) B424399
theorem B369377 : Blo 163797 369377 := bstep (se 2 (by rfl) ⟨138516, by rfl⟩ : syracuseStep 369377 = 277033) B277033
theorem B1418543 : Blo 163797 1418543 := bstep (se 1 (by rfl) ⟨1063907, by rfl⟩ : syracuseStep 1418543 = 2127815) B2127815
theorem B468281 : Blo 163797 468281 := bstep (se 2 (by rfl) ⟨175605, by rfl⟩ : syracuseStep 468281 = 351211) B351211
theorem B664951 : Blo 163797 664951 := bstep (se 1 (by rfl) ⟨498713, by rfl⟩ : syracuseStep 664951 = 997427) B997427
theorem B1811915 : Blo 163797 1811915 := bstep (se 1 (by rfl) ⟨1358936, by rfl⟩ : syracuseStep 1811915 = 2717873) B2717873
theorem B468463 : Blo 163797 468463 := bstep (se 1 (by rfl) ⟨351347, by rfl⟩ : syracuseStep 468463 = 702695) B702695
theorem B370313 : Blo 163797 370313 := bstep (se 2 (by rfl) ⟨138867, by rfl⟩ : syracuseStep 370313 = 277735) B277735
theorem B370367 : Blo 163797 370367 := bstep (se 1 (by rfl) ⟨277775, by rfl⟩ : syracuseStep 370367 = 555551) B555551
theorem B894731 : Blo 163797 894731 := bstep (se 1 (by rfl) ⟨671048, by rfl⟩ : syracuseStep 894731 = 1342097) B1342097
theorem B1877903 : Blo 163797 1877903 := bstep (se 1 (by rfl) ⟨1408427, by rfl⟩ : syracuseStep 1877903 = 2816855) B2816855
theorem B1124513 : Blo 163797 1124513 := bstep (se 2 (by rfl) ⟨421692, by rfl⟩ : syracuseStep 1124513 = 843385) B843385
theorem B829763 : Blo 163797 829763 := bstep (se 1 (by rfl) ⟨622322, by rfl⟩ : syracuseStep 829763 = 1244645) B1244645
theorem B2107721 : Blo 163797 2107721 := bstep (se 2 (by rfl) ⟨790395, by rfl⟩ : syracuseStep 2107721 = 1580791) B1580791
theorem B502205 : Blo 163797 502205 := bstep (se 3 (by rfl) ⟨94163, by rfl⟩ : syracuseStep 502205 = 188327) B188327
theorem B1355075 : Blo 163797 1355075 := bstep (se 1 (by rfl) ⟨1016306, by rfl⟩ : syracuseStep 1355075 = 2032613) B2032613
theorem B372095 : Blo 163797 372095 := bstep (se 1 (by rfl) ⟨279071, by rfl⟩ : syracuseStep 372095 = 558143) B558143
theorem B470411 : Blo 163797 470411 := bstep (se 1 (by rfl) ⟨352808, by rfl⟩ : syracuseStep 470411 = 705617) B705617
theorem B1421003 : Blo 163797 1421003 := bstep (se 1 (by rfl) ⟨1065752, by rfl⟩ : syracuseStep 1421003 = 2131505) B2131505
theorem B634655 : Blo 163797 634655 := bstep (se 1 (by rfl) ⟨475991, by rfl⟩ : syracuseStep 634655 = 951983) B951983
theorem B700559 : Blo 163797 700559 := bstep (se 1 (by rfl) ⟨525419, by rfl⟩ : syracuseStep 700559 = 1050839) B1050839
theorem B373049 : Blo 163797 373049 := bstep (se 2 (by rfl) ⟨139893, by rfl⟩ : syracuseStep 373049 = 279787) B279787
theorem B1749995 : Blo 163797 1749995 := bstep (se 1 (by rfl) ⟨1312496, by rfl⟩ : syracuseStep 1749995 = 2624993) B2624993
theorem B832841 : Blo 163797 832841 := bstep (se 2 (by rfl) ⟨312315, by rfl⟩ : syracuseStep 832841 = 624631) B624631
theorem B3225095 : Blo 163797 3225095 := bstep (se 1 (by rfl) ⟨2418821, by rfl⟩ : syracuseStep 3225095 = 4837643) B4837643
theorem B1193555 : Blo 163797 1193555 := bstep (se 1 (by rfl) ⟨895166, by rfl⟩ : syracuseStep 1193555 = 1790333) B1790333
theorem B636569 : Blo 163797 636569 := bstep (se 2 (by rfl) ⟨238713, by rfl⟩ : syracuseStep 636569 = 477427) B477427
theorem B669427 : Blo 163797 669427 := bstep (se 1 (by rfl) ⟨502070, by rfl⟩ : syracuseStep 669427 = 1004141) B1004141
theorem B374651 : Blo 163797 374651 := bstep (se 1 (by rfl) ⟨280988, by rfl⟩ : syracuseStep 374651 = 561977) B561977
theorem B374921 : Blo 163797 374921 := bstep (se 2 (by rfl) ⟨140595, by rfl⟩ : syracuseStep 374921 = 281191) B281191
theorem B211511 : Blo 163797 211511 := bstep (se 1 (by rfl) ⟨158633, by rfl⟩ : syracuseStep 211511 = 317267) B317267
theorem B834137 : Blo 163797 834137 := bstep (se 2 (by rfl) ⟨312801, by rfl⟩ : syracuseStep 834137 = 625603) B625603
theorem B211835 : Blo 163797 211835 := bstep (se 1 (by rfl) ⟨158876, by rfl⟩ : syracuseStep 211835 = 317753) B317753
theorem B2374535 : Blo 163797 2374535 := bstep (se 1 (by rfl) ⟨1780901, by rfl⟩ : syracuseStep 2374535 = 3561803) B3561803
theorem B1063961 : Blo 163797 1063961 := bstep (se 2 (by rfl) ⟨398985, by rfl⟩ : syracuseStep 1063961 = 797971) B797971
theorem B375929 : Blo 163797 375929 := bstep (se 2 (by rfl) ⟨140973, by rfl⟩ : syracuseStep 375929 = 281947) B281947
theorem B704335 : Blo 163797 704335 := bstep (se 1 (by rfl) ⟨528251, by rfl⟩ : syracuseStep 704335 = 1056503) B1056503
theorem B933713 : Blo 163797 933713 := bstep (se 2 (by rfl) ⟨350142, by rfl⟩ : syracuseStep 933713 = 700285) B700285
theorem B1064933 : Blo 163797 1064933 := bstep (se 4 (by rfl) ⟨99837, by rfl⟩ : syracuseStep 1064933 = 199675) B199675
theorem B245753 : Blo 163797 245753 := bstep (se 2 (by rfl) ⟨92157, by rfl⟩ : syracuseStep 245753 = 184315) B184315
theorem B4112441 : Blo 163797 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B245897 : Blo 163797 245897 := bstep (se 2 (by rfl) ⟨92211, by rfl⟩ : syracuseStep 245897 = 184423) B184423
theorem B245993 : Blo 163797 245993 := bstep (se 2 (by rfl) ⟨92247, by rfl⟩ : syracuseStep 245993 = 184495) B184495
theorem B6799625 : Blo 163797 6799625 := bstep (se 2 (by rfl) ⟨2549859, by rfl⟩ : syracuseStep 6799625 = 5099719) B5099719
theorem B246119 : Blo 163797 246119 := bstep (se 1 (by rfl) ⟨184589, by rfl⟩ : syracuseStep 246119 = 369179) B369179
theorem B246239 : Blo 163797 246239 := bstep (se 1 (by rfl) ⟨184679, by rfl⟩ : syracuseStep 246239 = 369359) B369359
theorem B475753 : Blo 163797 475753 := bstep (se 2 (by rfl) ⟨178407, by rfl⟩ : syracuseStep 475753 = 356815) B356815
theorem B246491 : Blo 163797 246491 := bstep (se 1 (by rfl) ⟨184868, by rfl⟩ : syracuseStep 246491 = 369737) B369737
theorem B476027 : Blo 163797 476027 := bstep (se 1 (by rfl) ⟨357020, by rfl⟩ : syracuseStep 476027 = 714041) B714041
theorem B476243 : Blo 163797 476243 := bstep (se 1 (by rfl) ⟨357182, by rfl⟩ : syracuseStep 476243 = 714365) B714365
theorem B246905 : Blo 163797 246905 := bstep (se 2 (by rfl) ⟨92589, by rfl⟩ : syracuseStep 246905 = 185179) B185179
theorem B2573507 : Blo 163797 2573507 := bstep (se 1 (by rfl) ⟨1930130, by rfl⟩ : syracuseStep 2573507 = 3860261) B3860261
theorem B2245913 : Blo 163797 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B247103 : Blo 163797 247103 := bstep (se 1 (by rfl) ⟨185327, by rfl⟩ : syracuseStep 247103 = 370655) B370655
theorem B444079 : Blo 163797 444079 := bstep (se 1 (by rfl) ⟨333059, by rfl⟩ : syracuseStep 444079 = 666119) B666119
theorem B902951 : Blo 163797 902951 := bstep (se 1 (by rfl) ⟨677213, by rfl⟩ : syracuseStep 902951 = 1354427) B1354427
theorem B444383 : Blo 163797 444383 := bstep (se 1 (by rfl) ⟨333287, by rfl⟩ : syracuseStep 444383 = 666575) B666575
theorem B247775 : Blo 163797 247775 := bstep (se 1 (by rfl) ⟨185831, by rfl⟩ : syracuseStep 247775 = 371663) B371663
theorem B247835 : Blo 163797 247835 := bstep (se 1 (by rfl) ⟨185876, by rfl⟩ : syracuseStep 247835 = 371753) B371753
theorem B1198111 : Blo 163797 1198111 := bstep (se 1 (by rfl) ⟨898583, by rfl⟩ : syracuseStep 1198111 = 1797167) B1797167
theorem B706607 : Blo 163797 706607 := bstep (se 1 (by rfl) ⟨529955, by rfl⟩ : syracuseStep 706607 = 1059911) B1059911
theorem B247991 : Blo 163797 247991 := bstep (se 1 (by rfl) ⟨185993, by rfl⟩ : syracuseStep 247991 = 371987) B371987
theorem B248015 : Blo 163797 248015 := bstep (se 1 (by rfl) ⟨186011, by rfl⟩ : syracuseStep 248015 = 372023) B372023
theorem B248411 : Blo 163797 248411 := bstep (se 1 (by rfl) ⟨186308, by rfl⟩ : syracuseStep 248411 = 372617) B372617
theorem B248555 : Blo 163797 248555 := bstep (se 1 (by rfl) ⟨186416, by rfl⟩ : syracuseStep 248555 = 372833) B372833
theorem B248585 : Blo 163797 248585 := bstep (se 2 (by rfl) ⟨93219, by rfl⟩ : syracuseStep 248585 = 186439) B186439
theorem B281353 : Blo 163797 281353 := bstep (se 2 (by rfl) ⟨105507, by rfl⟩ : syracuseStep 281353 = 211015) B211015
theorem B4016951 : Blo 163797 4016951 := bstep (se 1 (by rfl) ⟨3012713, by rfl⟩ : syracuseStep 4016951 = 6025427) B6025427
theorem B248999 : Blo 163797 248999 := bstep (se 1 (by rfl) ⟨186749, by rfl⟩ : syracuseStep 248999 = 373499) B373499
theorem B249143 : Blo 163797 249143 := bstep (se 1 (by rfl) ⟨186857, by rfl⟩ : syracuseStep 249143 = 373715) B373715
theorem B1068623 : Blo 163797 1068623 := bstep (se 1 (by rfl) ⟨801467, by rfl⟩ : syracuseStep 1068623 = 1602935) B1602935
theorem B478831 : Blo 163797 478831 := bstep (se 1 (by rfl) ⟨359123, by rfl⟩ : syracuseStep 478831 = 718247) B718247
theorem B249455 : Blo 163797 249455 := bstep (se 1 (by rfl) ⟨187091, by rfl⟩ : syracuseStep 249455 = 374183) B374183
theorem B1068659 : Blo 163797 1068659 := bstep (se 1 (by rfl) ⟨801494, by rfl⟩ : syracuseStep 1068659 = 1602989) B1602989
theorem B839321 : Blo 163797 839321 := bstep (se 2 (by rfl) ⟨314745, by rfl⟩ : syracuseStep 839321 = 629491) B629491
theorem B249527 : Blo 163797 249527 := bstep (se 1 (by rfl) ⟨187145, by rfl⟩ : syracuseStep 249527 = 374291) B374291
theorem B249575 : Blo 163797 249575 := bstep (se 1 (by rfl) ⟨187181, by rfl⟩ : syracuseStep 249575 = 374363) B374363
theorem B249737 : Blo 163797 249737 := bstep (se 2 (by rfl) ⟨93651, by rfl⟩ : syracuseStep 249737 = 187303) B187303
theorem B511915 : Blo 163797 511915 := bstep (se 1 (by rfl) ⟨383936, by rfl⟩ : syracuseStep 511915 = 767873) B767873
theorem B7196597 : Blo 163797 7196597 := bstep (se 5 (by rfl) ⟨337340, by rfl⟩ : syracuseStep 7196597 = 674681) B674681
theorem B249977 : Blo 163797 249977 := bstep (se 2 (by rfl) ⟨93741, by rfl⟩ : syracuseStep 249977 = 187483) B187483
theorem B249983 : Blo 163797 249983 := bstep (se 1 (by rfl) ⟨187487, by rfl⟩ : syracuseStep 249983 = 374975) B374975
theorem B315839 : Blo 163797 315839 := bstep (se 1 (by rfl) ⟨236879, by rfl⟩ : syracuseStep 315839 = 473759) B473759
theorem B283115 : Blo 163797 283115 := bstep (se 1 (by rfl) ⟨212336, by rfl⟩ : syracuseStep 283115 = 424673) B424673
theorem B185287 : Blo 163797 185287 := bstep (se 1 (by rfl) ⟨138965, by rfl⟩ : syracuseStep 185287 = 277931) B277931
theorem B250823 : Blo 163797 250823 := bstep (se 1 (by rfl) ⟨188117, by rfl⟩ : syracuseStep 250823 = 376235) B376235
theorem B250847 : Blo 163797 250847 := bstep (se 1 (by rfl) ⟨188135, by rfl⟩ : syracuseStep 250847 = 376271) B376271
theorem B3429371 : Blo 163797 3429371 := bstep (se 1 (by rfl) ⟨2572028, by rfl⟩ : syracuseStep 3429371 = 5144057) B5144057
theorem B1889567 : Blo 163797 1889567 := bstep (se 1 (by rfl) ⟨1417175, by rfl⟩ : syracuseStep 1889567 = 2834351) B2834351
theorem B185647 : Blo 163797 185647 := bstep (se 1 (by rfl) ⟨139235, by rfl⟩ : syracuseStep 185647 = 278471) B278471
theorem B251183 : Blo 163797 251183 := bstep (se 1 (by rfl) ⟨188387, by rfl⟩ : syracuseStep 251183 = 376775) B376775
theorem B251387 : Blo 163797 251387 := bstep (se 1 (by rfl) ⟨188540, by rfl⟩ : syracuseStep 251387 = 377081) B377081
theorem B251423 : Blo 163797 251423 := bstep (se 1 (by rfl) ⟨188567, by rfl⟩ : syracuseStep 251423 = 377135) B377135
theorem B251561 : Blo 163797 251561 := bstep (se 2 (by rfl) ⟨94335, by rfl⟩ : syracuseStep 251561 = 188671) B188671
theorem B251567 : Blo 163797 251567 := bstep (se 1 (by rfl) ⟨188675, by rfl⟩ : syracuseStep 251567 = 377351) B377351
theorem B186151 : Blo 163797 186151 := bstep (se 1 (by rfl) ⟨139613, by rfl⟩ : syracuseStep 186151 = 279227) B279227
theorem B251687 : Blo 163797 251687 := bstep (se 1 (by rfl) ⟨188765, by rfl⟩ : syracuseStep 251687 = 377531) B377531
theorem B1595213 : Blo 163797 1595213 := bstep (se 3 (by rfl) ⟨299102, by rfl⟩ : syracuseStep 1595213 = 598205) B598205
theorem B415631 : Blo 163797 415631 := bstep (se 1 (by rfl) ⟨311723, by rfl⟩ : syracuseStep 415631 = 623447) B623447
theorem B94197917 : Blo 163797 94197917 := bstep (se 3 (by rfl) ⟨17662109, by rfl⟩ : syracuseStep 94197917 = 35324219) B35324219
theorem B350399 : Blo 163797 350399 := bstep (se 1 (by rfl) ⟨262799, by rfl⟩ : syracuseStep 350399 = 525599) B525599
theorem B18208961 : Blo 163797 18208961 := bstep (se 2 (by rfl) ⟨6828360, by rfl⟩ : syracuseStep 18208961 = 13656721) B13656721
theorem B415975 : Blo 163797 415975 := bstep (se 1 (by rfl) ⟨311981, by rfl⟩ : syracuseStep 415975 = 623963) B623963
theorem B1891025 : Blo 163797 1891025 := bstep (se 2 (by rfl) ⟨709134, by rfl⟩ : syracuseStep 1891025 = 1418269) B1418269
theorem B1203329 : Blo 163797 1203329 := bstep (se 2 (by rfl) ⟨451248, by rfl⟩ : syracuseStep 1203329 = 902497) B902497
theorem B843371 : Blo 163797 843371 := bstep (se 1 (by rfl) ⟨632528, by rfl⟩ : syracuseStep 843371 = 1265057) B1265057
theorem B3661433 : Blo 163797 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B3825443 : Blo 163797 3825443 := bstep (se 1 (by rfl) ⟨2869082, by rfl⟩ : syracuseStep 3825443 = 5738165) B5738165
theorem B417899 : Blo 163797 417899 := bstep (se 1 (by rfl) ⟨313424, by rfl⟩ : syracuseStep 417899 = 626849) B626849
theorem B352927 : Blo 163797 352927 := bstep (se 1 (by rfl) ⟨264695, by rfl⟩ : syracuseStep 352927 = 529391) B529391
theorem B942779 : Blo 163797 942779 := bstep (se 1 (by rfl) ⟨707084, by rfl⟩ : syracuseStep 942779 = 1414169) B1414169
theorem B418567 : Blo 163797 418567 := bstep (se 1 (by rfl) ⟨313925, by rfl⟩ : syracuseStep 418567 = 627851) B627851
theorem B418871 : Blo 163797 418871 := bstep (se 1 (by rfl) ⟨314153, by rfl⟩ : syracuseStep 418871 = 628307) B628307
theorem B844991 : Blo 163797 844991 := bstep (se 1 (by rfl) ⟨633743, by rfl⟩ : syracuseStep 844991 = 1267487) B1267487
theorem B1271375 : Blo 163797 1271375 := bstep (se 1 (by rfl) ⟨953531, by rfl⟩ : syracuseStep 1271375 = 1907063) B1907063
theorem B2123819 : Blo 163797 2123819 := bstep (se 1 (by rfl) ⟨1592864, by rfl⟩ : syracuseStep 2123819 = 3185729) B3185729
theorem B715081 : Blo 163797 715081 := bstep (se 2 (by rfl) ⟨268155, by rfl⟩ : syracuseStep 715081 = 536311) B536311
theorem B846551 : Blo 163797 846551 := bstep (se 1 (by rfl) ⟨634913, by rfl⟩ : syracuseStep 846551 = 1269827) B1269827
theorem B420815 : Blo 163797 420815 := bstep (se 1 (by rfl) ⟨315611, by rfl⟩ : syracuseStep 420815 = 631223) B631223
theorem B1698889 : Blo 163797 1698889 := bstep (se 2 (by rfl) ⟨637083, by rfl⟩ : syracuseStep 1698889 = 1274167) B1274167
theorem B421595 : Blo 163797 421595 := bstep (se 1 (by rfl) ⟨316196, by rfl⟩ : syracuseStep 421595 = 632393) B632393
theorem B552905 : Blo 163797 552905 := bstep (se 2 (by rfl) ⟨207339, by rfl⟩ : syracuseStep 552905 = 414679) B414679
theorem B421919 : Blo 163797 421919 := bstep (se 1 (by rfl) ⟨316439, by rfl⟩ : syracuseStep 421919 = 632879) B632879
theorem B1896857 : Blo 163797 1896857 := bstep (se 2 (by rfl) ⟨711321, by rfl⟩ : syracuseStep 1896857 = 1422643) B1422643
theorem B651689 : Blo 163797 651689 := bstep (se 2 (by rfl) ⟨244383, by rfl⟩ : syracuseStep 651689 = 488767) B488767
theorem B423407 : Blo 163797 423407 := bstep (se 1 (by rfl) ⟨317555, by rfl⟩ : syracuseStep 423407 = 635111) B635111
theorem B555497 : Blo 163797 555497 := bstep (se 2 (by rfl) ⟨208311, by rfl⟩ : syracuseStep 555497 = 416623) B416623
theorem B2128841 : Blo 163797 2128841 := bstep (se 2 (by rfl) ⟨798315, by rfl⟩ : syracuseStep 2128841 = 1596631) B1596631
theorem B556361 : Blo 163797 556361 := bstep (se 2 (by rfl) ⟨208635, by rfl⟩ : syracuseStep 556361 = 417271) B417271
theorem B556523 : Blo 163797 556523 := bstep (se 1 (by rfl) ⟨417392, by rfl⟩ : syracuseStep 556523 = 834785) B834785
theorem B949751 : Blo 163797 949751 := bstep (se 1 (by rfl) ⟨712313, by rfl⟩ : syracuseStep 949751 = 1424627) B1424627
theorem B622187 : Blo 163797 622187 := bstep (se 1 (by rfl) ⟨466640, by rfl⟩ : syracuseStep 622187 = 933281) B933281
theorem B622201 : Blo 163797 622201 := bstep (se 2 (by rfl) ⟨233325, by rfl⟩ : syracuseStep 622201 = 466651) B466651
theorem B556955 : Blo 163797 556955 := bstep (se 1 (by rfl) ⟨417716, by rfl⟩ : syracuseStep 556955 = 835433) B835433
theorem B163931 : Blo 163797 163931 := bstep (se 1 (by rfl) ⟨122948, by rfl⟩ : syracuseStep 163931 = 245897) B245897
theorem B163995 : Blo 163797 163995 := bstep (se 1 (by rfl) ⟨122996, by rfl⟩ : syracuseStep 163995 = 245993) B245993
theorem B164079 : Blo 163797 164079 := bstep (se 1 (by rfl) ⟨123059, by rfl⟩ : syracuseStep 164079 = 246119) B246119
theorem B164159 : Blo 163797 164159 := bstep (se 1 (by rfl) ⟨123119, by rfl⟩ : syracuseStep 164159 = 246239) B246239
theorem B164327 : Blo 163797 164327 := bstep (se 1 (by rfl) ⟨123245, by rfl⟩ : syracuseStep 164327 = 246491) B246491
theorem B164603 : Blo 163797 164603 := bstep (se 1 (by rfl) ⟨123452, by rfl⟩ : syracuseStep 164603 = 246905) B246905
theorem B164735 : Blo 163797 164735 := bstep (se 1 (by rfl) ⟨123551, by rfl⟩ : syracuseStep 164735 = 247103) B247103
theorem B558089 : Blo 163797 558089 := bstep (se 2 (by rfl) ⟨209283, by rfl⟩ : syracuseStep 558089 = 418567) B418567
theorem B296255 : Blo 163797 296255 := bstep (se 1 (by rfl) ⟨222191, by rfl⟩ : syracuseStep 296255 = 444383) B444383
theorem B165183 : Blo 163797 165183 := bstep (se 1 (by rfl) ⟨123887, by rfl⟩ : syracuseStep 165183 = 247775) B247775
theorem B165223 : Blo 163797 165223 := bstep (se 1 (by rfl) ⟨123917, by rfl⟩ : syracuseStep 165223 = 247835) B247835
theorem B165327 : Blo 163797 165327 := bstep (se 1 (by rfl) ⟨123995, by rfl⟩ : syracuseStep 165327 = 247991) B247991
theorem B165343 : Blo 163797 165343 := bstep (se 1 (by rfl) ⟨124007, by rfl⟩ : syracuseStep 165343 = 248015) B248015
theorem B722627 : Blo 163797 722627 := bstep (se 1 (by rfl) ⟨541970, by rfl⟩ : syracuseStep 722627 = 1083941) B1083941
theorem B165607 : Blo 163797 165607 := bstep (se 1 (by rfl) ⟨124205, by rfl⟩ : syracuseStep 165607 = 248411) B248411
theorem B165703 : Blo 163797 165703 := bstep (se 1 (by rfl) ⟨124277, by rfl⟩ : syracuseStep 165703 = 248555) B248555
theorem B886601 : Blo 163797 886601 := bstep (se 2 (by rfl) ⟨332475, by rfl⟩ : syracuseStep 886601 = 664951) B664951
theorem B165723 : Blo 163797 165723 := bstep (se 1 (by rfl) ⟨124292, by rfl⟩ : syracuseStep 165723 = 248585) B248585
theorem B624617 : Blo 163797 624617 := bstep (se 2 (by rfl) ⟨234231, by rfl⟩ : syracuseStep 624617 = 468463) B468463
theorem B165999 : Blo 163797 165999 := bstep (se 1 (by rfl) ⟨124499, by rfl⟩ : syracuseStep 165999 = 248999) B248999
theorem B166095 : Blo 163797 166095 := bstep (se 1 (by rfl) ⟨124571, by rfl⟩ : syracuseStep 166095 = 249143) B249143
theorem B592105 : Blo 163797 592105 := bstep (se 2 (by rfl) ⟨222039, by rfl⟩ : syracuseStep 592105 = 444079) B444079
theorem B166303 : Blo 163797 166303 := bstep (se 1 (by rfl) ⟨124727, by rfl⟩ : syracuseStep 166303 = 249455) B249455
theorem B559547 : Blo 163797 559547 := bstep (se 1 (by rfl) ⟨419660, by rfl⟩ : syracuseStep 559547 = 839321) B839321
theorem B166351 : Blo 163797 166351 := bstep (se 1 (by rfl) ⟨124763, by rfl⟩ : syracuseStep 166351 = 249527) B249527
theorem B166383 : Blo 163797 166383 := bstep (se 1 (by rfl) ⟨124787, by rfl⟩ : syracuseStep 166383 = 249575) B249575
theorem B166491 : Blo 163797 166491 := bstep (se 1 (by rfl) ⟨124868, by rfl⟩ : syracuseStep 166491 = 249737) B249737
theorem B166651 : Blo 163797 166651 := bstep (se 1 (by rfl) ⟨124988, by rfl⟩ : syracuseStep 166651 = 249977) B249977
theorem B166655 : Blo 163797 166655 := bstep (se 1 (by rfl) ⟨124991, by rfl⟩ : syracuseStep 166655 = 249983) B249983
theorem B953441 : Blo 163797 953441 := bstep (se 2 (by rfl) ⟨357540, by rfl⟩ : syracuseStep 953441 = 715081) B715081
theorem B167215 : Blo 163797 167215 := bstep (se 1 (by rfl) ⟨125411, by rfl⟩ : syracuseStep 167215 = 250823) B250823
theorem B167231 : Blo 163797 167231 := bstep (se 1 (by rfl) ⟨125423, by rfl⟩ : syracuseStep 167231 = 250847) B250847
theorem B167455 : Blo 163797 167455 := bstep (se 1 (by rfl) ⟨125591, by rfl⟩ : syracuseStep 167455 = 251183) B251183
theorem B167591 : Blo 163797 167591 := bstep (se 1 (by rfl) ⟨125693, by rfl⟩ : syracuseStep 167591 = 251387) B251387
theorem B331447 : Blo 163797 331447 := bstep (se 1 (by rfl) ⟨248585, by rfl⟩ : syracuseStep 331447 = 497171) B497171
theorem B167615 : Blo 163797 167615 := bstep (se 1 (by rfl) ⟨125711, by rfl⟩ : syracuseStep 167615 = 251423) B251423
theorem B167707 : Blo 163797 167707 := bstep (se 1 (by rfl) ⟨125780, by rfl⟩ : syracuseStep 167707 = 251561) B251561
theorem B167711 : Blo 163797 167711 := bstep (se 1 (by rfl) ⟨125783, by rfl⟩ : syracuseStep 167711 = 251567) B251567
theorem B167791 : Blo 163797 167791 := bstep (se 1 (by rfl) ⟨125843, by rfl⟩ : syracuseStep 167791 = 251687) B251687
theorem B2265185 : Blo 163797 2265185 := bstep (se 2 (by rfl) ⟨849444, by rfl⟩ : syracuseStep 2265185 = 1698889) B1698889
theorem B233599 : Blo 163797 233599 := bstep (se 1 (by rfl) ⟨175199, by rfl⟩ : syracuseStep 233599 = 350399) B350399
theorem B594067 : Blo 163797 594067 := bstep (se 1 (by rfl) ⟨445550, by rfl⟩ : syracuseStep 594067 = 891101) B891101
theorem B6951349 : Blo 163797 6951349 := bstep (se 5 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 6951349 = 651689) B651689
theorem B791147 : Blo 163797 791147 := bstep (se 1 (by rfl) ⟨593360, by rfl⟩ : syracuseStep 791147 = 1186721) B1186721
theorem B562247 : Blo 163797 562247 := bstep (se 1 (by rfl) ⟨421685, by rfl⟩ : syracuseStep 562247 = 843371) B843371
theorem B628519 : Blo 163797 628519 := bstep (se 1 (by rfl) ⟨471389, by rfl⟩ : syracuseStep 628519 = 942779) B942779
theorem B563327 : Blo 163797 563327 := bstep (se 1 (by rfl) ⟨422495, by rfl⟩ : syracuseStep 563327 = 844991) B844991
theorem B1251935 : Blo 163797 1251935 := bstep (se 1 (by rfl) ⟨938951, by rfl⟩ : syracuseStep 1251935 = 1877903) B1877903
theorem B1415879 : Blo 163797 1415879 := bstep (se 1 (by rfl) ⟨1061909, by rfl⟩ : syracuseStep 1415879 = 2123819) B2123819
theorem B564029 : Blo 163797 564029 := bstep (se 3 (by rfl) ⟨105755, by rfl⟩ : syracuseStep 564029 = 211511) B211511
theorem B564367 : Blo 163797 564367 := bstep (se 1 (by rfl) ⟨423275, by rfl⟩ : syracuseStep 564367 = 846551) B846551
theorem B564893 : Blo 163797 564893 := bstep (se 3 (by rfl) ⟨105917, by rfl⟩ : syracuseStep 564893 = 211835) B211835
theorem B368603 : Blo 163797 368603 := bstep (se 1 (by rfl) ⟨276452, by rfl⟩ : syracuseStep 368603 = 552905) B552905
theorem B467039 : Blo 163797 467039 := bstep (se 1 (by rfl) ⟨350279, by rfl⟩ : syracuseStep 467039 = 700559) B700559
theorem B795703 : Blo 163797 795703 := bstep (se 1 (by rfl) ⟨596777, by rfl⟩ : syracuseStep 795703 = 1193555) B1193555
theorem B370331 : Blo 163797 370331 := bstep (se 1 (by rfl) ⟨277748, by rfl⟩ : syracuseStep 370331 = 555497) B555497
theorem B1583023 : Blo 163797 1583023 := bstep (se 1 (by rfl) ⟨1187267, by rfl⟩ : syracuseStep 1583023 = 2374535) B2374535
theorem B1419227 : Blo 163797 1419227 := bstep (se 1 (by rfl) ⟨1064420, by rfl⟩ : syracuseStep 1419227 = 2128841) B2128841
theorem B829601 : Blo 163797 829601 := bstep (se 2 (by rfl) ⟨311100, by rfl⟩ : syracuseStep 829601 = 622201) B622201
theorem B370907 : Blo 163797 370907 := bstep (se 1 (by rfl) ⟨278180, by rfl⟩ : syracuseStep 370907 = 556361) B556361
theorem B371015 : Blo 163797 371015 := bstep (se 1 (by rfl) ⟨278261, by rfl⟩ : syracuseStep 371015 = 556523) B556523
theorem B633167 : Blo 163797 633167 := bstep (se 1 (by rfl) ⟨474875, by rfl⟩ : syracuseStep 633167 = 949751) B949751
theorem B371303 : Blo 163797 371303 := bstep (se 1 (by rfl) ⟨278477, by rfl⟩ : syracuseStep 371303 = 556955) B556955
theorem B4533083 : Blo 163797 4533083 := bstep (se 1 (by rfl) ⟨3399812, by rfl⟩ : syracuseStep 4533083 = 6799625) B6799625
theorem B4566365 : Blo 163797 4566365 := bstep (se 3 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 4566365 = 1712387) B1712387
theorem B1715671 : Blo 163797 1715671 := bstep (se 1 (by rfl) ⟨1286753, by rfl⟩ : syracuseStep 1715671 = 2573507) B2573507
theorem B634337 : Blo 163797 634337 := bstep (se 2 (by rfl) ⟨237876, by rfl⟩ : syracuseStep 634337 = 475753) B475753
theorem B601967 : Blo 163797 601967 := bstep (se 1 (by rfl) ⟨451475, by rfl⟩ : syracuseStep 601967 = 902951) B902951
theorem B700319 : Blo 163797 700319 := bstep (se 1 (by rfl) ⟨525239, by rfl⟩ : syracuseStep 700319 = 1050479) B1050479
theorem B634823 : Blo 163797 634823 := bstep (se 1 (by rfl) ⟨476117, by rfl⟩ : syracuseStep 634823 = 952235) B952235
theorem B471071 : Blo 163797 471071 := bstep (se 1 (by rfl) ⟨353303, by rfl⟩ : syracuseStep 471071 = 706607) B706607
theorem B372959 : Blo 163797 372959 := bstep (se 1 (by rfl) ⟨279719, by rfl⟩ : syracuseStep 372959 = 559439) B559439
theorem B635323 : Blo 163797 635323 := bstep (se 1 (by rfl) ⟨476492, by rfl⟩ : syracuseStep 635323 = 952985) B952985
theorem B176575 : Blo 163797 176575 := bstep (se 1 (by rfl) ⟨132431, by rfl⟩ : syracuseStep 176575 = 264863) B264863
theorem B4797731 : Blo 163797 4797731 := bstep (se 1 (by rfl) ⟨3598298, by rfl⟩ : syracuseStep 4797731 = 7196597) B7196597
theorem B701891 : Blo 163797 701891 := bstep (se 1 (by rfl) ⟨526418, by rfl⟩ : syracuseStep 701891 = 1052837) B1052837
theorem B1882277 : Blo 163797 1882277 := bstep (se 4 (by rfl) ⟨176463, by rfl⟩ : syracuseStep 1882277 = 352927) B352927
theorem B1259711 : Blo 163797 1259711 := bstep (se 1 (by rfl) ⟨944783, by rfl⟩ : syracuseStep 1259711 = 1889567) B1889567
theorem B1161503 : Blo 163797 1161503 := bstep (se 1 (by rfl) ⟨871127, by rfl⟩ : syracuseStep 1161503 = 1742255) B1742255
theorem B375137 : Blo 163797 375137 := bstep (se 2 (by rfl) ⟨140676, by rfl⟩ : syracuseStep 375137 = 281353) B281353
theorem B1063475 : Blo 163797 1063475 := bstep (se 1 (by rfl) ⟨797606, by rfl⟩ : syracuseStep 1063475 = 1595213) B1595213
theorem B277087 : Blo 163797 277087 := bstep (se 1 (by rfl) ⟨207815, by rfl⟩ : syracuseStep 277087 = 415631) B415631
theorem B178907 : Blo 163797 178907 := bstep (se 1 (by rfl) ⟨134180, by rfl⟩ : syracuseStep 178907 = 268361) B268361
theorem B62798611 : Blo 163797 62798611 := bstep (se 1 (by rfl) ⟨47098958, by rfl⟩ : syracuseStep 62798611 = 94197917) B94197917
theorem B12139307 : Blo 163797 12139307 := bstep (se 1 (by rfl) ⟨9104480, by rfl⟩ : syracuseStep 12139307 = 18208961) B18208961
theorem B1260683 : Blo 163797 1260683 := bstep (se 1 (by rfl) ⟨945512, by rfl⟩ : syracuseStep 1260683 = 1891025) B1891025
theorem B5356853 : Blo 163797 5356853 := bstep (se 5 (by rfl) ⟨251102, by rfl⟩ : syracuseStep 5356853 = 502205) B502205
theorem B802219 : Blo 163797 802219 := bstep (se 1 (by rfl) ⟨601664, by rfl⟩ : syracuseStep 802219 = 1203329) B1203329
theorem B638441 : Blo 163797 638441 := bstep (se 2 (by rfl) ⟨239415, by rfl⟩ : syracuseStep 638441 = 478831) B478831
theorem B2440955 : Blo 163797 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B507667 : Blo 163797 507667 := bstep (se 1 (by rfl) ⟨380750, by rfl⟩ : syracuseStep 507667 = 761501) B761501
theorem B311131 : Blo 163797 311131 := bstep (se 1 (by rfl) ⟨233348, by rfl⟩ : syracuseStep 311131 = 466697) B466697
theorem B311177 : Blo 163797 311177 := bstep (se 2 (by rfl) ⟨116691, by rfl⟩ : syracuseStep 311177 = 233383) B233383
theorem B278599 : Blo 163797 278599 := bstep (se 1 (by rfl) ⟨208949, by rfl⟩ : syracuseStep 278599 = 417899) B417899
theorem B704609 : Blo 163797 704609 := bstep (se 2 (by rfl) ⟨264228, by rfl⟩ : syracuseStep 704609 = 528457) B528457
theorem B376991 : Blo 163797 376991 := bstep (se 1 (by rfl) ⟨282743, by rfl⟩ : syracuseStep 376991 = 565487) B565487
theorem B901307 : Blo 163797 901307 := bstep (se 1 (by rfl) ⟨675980, by rfl⟩ : syracuseStep 901307 = 1351961) B1351961
theorem B377243 : Blo 163797 377243 := bstep (se 1 (by rfl) ⟨282932, by rfl⟩ : syracuseStep 377243 = 565865) B565865
theorem B246251 : Blo 163797 246251 := bstep (se 1 (by rfl) ⟨184688, by rfl⟩ : syracuseStep 246251 = 369377) B369377
theorem B279247 : Blo 163797 279247 := bstep (se 1 (by rfl) ⟨209435, by rfl⟩ : syracuseStep 279247 = 418871) B418871
theorem B312187 : Blo 163797 312187 := bstep (se 1 (by rfl) ⟨234140, by rfl⟩ : syracuseStep 312187 = 468281) B468281
theorem B246875 : Blo 163797 246875 := bstep (se 1 (by rfl) ⟨185156, by rfl⟩ : syracuseStep 246875 = 370313) B370313
theorem B246911 : Blo 163797 246911 := bstep (se 1 (by rfl) ⟨185183, by rfl⟩ : syracuseStep 246911 = 370367) B370367
theorem B247049 : Blo 163797 247049 := bstep (se 2 (by rfl) ⟨92643, by rfl⟩ : syracuseStep 247049 = 185287) B185287
theorem B247529 : Blo 163797 247529 := bstep (se 2 (by rfl) ⟨92823, by rfl⟩ : syracuseStep 247529 = 185647) B185647
theorem B280543 : Blo 163797 280543 := bstep (se 1 (by rfl) ⟨210407, by rfl⟩ : syracuseStep 280543 = 420815) B420815
theorem B903383 : Blo 163797 903383 := bstep (se 1 (by rfl) ⟨677537, by rfl⟩ : syracuseStep 903383 = 1355075) B1355075
theorem B248063 : Blo 163797 248063 := bstep (se 1 (by rfl) ⟨186047, by rfl⟩ : syracuseStep 248063 = 372095) B372095
theorem B313607 : Blo 163797 313607 := bstep (se 1 (by rfl) ⟨235205, by rfl⟩ : syracuseStep 313607 = 470411) B470411
theorem B248201 : Blo 163797 248201 := bstep (se 2 (by rfl) ⟨93075, by rfl⟩ : syracuseStep 248201 = 186151) B186151
theorem B281063 : Blo 163797 281063 := bstep (se 1 (by rfl) ⟨210797, by rfl⟩ : syracuseStep 281063 = 421595) B421595
theorem B281279 : Blo 163797 281279 := bstep (se 1 (by rfl) ⟨210959, by rfl⟩ : syracuseStep 281279 = 421919) B421919
theorem B248699 : Blo 163797 248699 := bstep (se 1 (by rfl) ⟨186524, by rfl⟩ : syracuseStep 248699 = 373049) B373049
theorem B1264571 : Blo 163797 1264571 := bstep (se 1 (by rfl) ⟨948428, by rfl⟩ : syracuseStep 1264571 = 1896857) B1896857
theorem B1166663 : Blo 163797 1166663 := bstep (se 1 (by rfl) ⟨874997, by rfl⟩ : syracuseStep 1166663 = 1749995) B1749995
theorem B282271 : Blo 163797 282271 := bstep (se 1 (by rfl) ⟨211703, by rfl⟩ : syracuseStep 282271 = 423407) B423407
theorem B2150063 : Blo 163797 2150063 := bstep (se 1 (by rfl) ⟨1612547, by rfl⟩ : syracuseStep 2150063 = 3225095) B3225095
theorem B249767 : Blo 163797 249767 := bstep (se 1 (by rfl) ⟨187325, by rfl⟩ : syracuseStep 249767 = 374651) B374651
theorem B249947 : Blo 163797 249947 := bstep (se 1 (by rfl) ⟨187460, by rfl⟩ : syracuseStep 249947 = 374921) B374921
theorem B709033 : Blo 163797 709033 := bstep (se 2 (by rfl) ⟨265887, by rfl⟩ : syracuseStep 709033 = 531775) B531775
theorem B709307 : Blo 163797 709307 := bstep (se 1 (by rfl) ⟨531980, by rfl⟩ : syracuseStep 709307 = 1063961) B1063961
theorem B250619 : Blo 163797 250619 := bstep (se 1 (by rfl) ⟨187964, by rfl⟩ : syracuseStep 250619 = 375929) B375929
theorem B414791 : Blo 163797 414791 := bstep (se 1 (by rfl) ⟨311093, by rfl⟩ : syracuseStep 414791 = 622187) B622187
theorem B939113 : Blo 163797 939113 := bstep (se 2 (by rfl) ⟨352167, by rfl⟩ : syracuseStep 939113 = 704335) B704335
theorem B709955 : Blo 163797 709955 := bstep (se 1 (by rfl) ⟨532466, by rfl⟩ : syracuseStep 709955 = 1064933) B1064933
theorem B2741627 : Blo 163797 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B317351 : Blo 163797 317351 := bstep (se 1 (by rfl) ⟨238013, by rfl⟩ : syracuseStep 317351 = 476027) B476027
theorem B317495 : Blo 163797 317495 := bstep (se 1 (by rfl) ⟨238121, by rfl⟩ : syracuseStep 317495 = 476243) B476243
theorem B1497275 : Blo 163797 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B2316671 : Blo 163797 2316671 := bstep (se 1 (by rfl) ⟨1737503, by rfl⟩ : syracuseStep 2316671 = 3475007) B3475007
theorem B842237 : Blo 163797 842237 := bstep (se 3 (by rfl) ⟨157919, by rfl⟩ : syracuseStep 842237 = 315839) B315839
theorem B51534863 : Blo 163797 51534863 := bstep (se 1 (by rfl) ⟨38651147, by rfl⟩ : syracuseStep 51534863 = 77302295) B77302295
theorem B2677967 : Blo 163797 2677967 := bstep (se 1 (by rfl) ⟨2008475, by rfl⟩ : syracuseStep 2677967 = 4016951) B4016951
theorem B712415 : Blo 163797 712415 := bstep (se 1 (by rfl) ⟨534311, by rfl⟩ : syracuseStep 712415 = 1068623) B1068623
theorem B712439 : Blo 163797 712439 := bstep (se 1 (by rfl) ⟨534329, by rfl⟩ : syracuseStep 712439 = 1068659) B1068659
theorem B1597481 : Blo 163797 1597481 := bstep (se 2 (by rfl) ⟨599055, by rfl⟩ : syracuseStep 1597481 = 1198111) B1198111
theorem B188743 : Blo 163797 188743 := bstep (se 1 (by rfl) ⟨141557, by rfl⟩ : syracuseStep 188743 = 283115) B283115
theorem B2286247 : Blo 163797 2286247 := bstep (se 1 (by rfl) ⟨1714685, by rfl⟩ : syracuseStep 2286247 = 3429371) B3429371
theorem B1270889 : Blo 163797 1270889 := bstep (se 2 (by rfl) ⟨476583, by rfl⟩ : syracuseStep 1270889 = 953167) B953167
theorem B2385949 : Blo 163797 2385949 := bstep (se 3 (by rfl) ⟨447365, by rfl⟩ : syracuseStep 2385949 = 894731) B894731
theorem B2550295 : Blo 163797 2550295 := bstep (se 1 (by rfl) ⟨1912721, by rfl⟩ : syracuseStep 2550295 = 3825443) B3825443
theorem B682553 : Blo 163797 682553 := bstep (se 2 (by rfl) ⟨255957, by rfl⟩ : syracuseStep 682553 = 511915) B511915
theorem B355337 : Blo 163797 355337 := bstep (se 2 (by rfl) ⟨133251, by rfl⟩ : syracuseStep 355337 = 266503) B266503
theorem B945695 : Blo 163797 945695 := bstep (se 1 (by rfl) ⟨709271, by rfl⟩ : syracuseStep 945695 = 1418543) B1418543
theorem B1207943 : Blo 163797 1207943 := bstep (se 1 (by rfl) ⟨905957, by rfl⟩ : syracuseStep 1207943 = 1811915) B1811915
theorem B847583 : Blo 163797 847583 := bstep (se 1 (by rfl) ⟨635687, by rfl⟩ : syracuseStep 847583 = 1271375) B1271375
theorem B749675 : Blo 163797 749675 := bstep (se 1 (by rfl) ⟨562256, by rfl⟩ : syracuseStep 749675 = 1124513) B1124513
theorem B553175 : Blo 163797 553175 := bstep (se 1 (by rfl) ⟨414881, by rfl⟩ : syracuseStep 553175 = 829763) B829763
theorem B1405147 : Blo 163797 1405147 := bstep (se 1 (by rfl) ⟨1053860, by rfl⟩ : syracuseStep 1405147 = 2107721) B2107721
theorem B4551389 : Blo 163797 4551389 := bstep (se 3 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 4551389 = 1706771) B1706771
theorem B947335 : Blo 163797 947335 := bstep (se 1 (by rfl) ⟨710501, by rfl⟩ : syracuseStep 947335 = 1421003) B1421003
theorem B423103 : Blo 163797 423103 := bstep (se 1 (by rfl) ⟨317327, by rfl⟩ : syracuseStep 423103 = 634655) B634655
theorem B554633 : Blo 163797 554633 := bstep (se 2 (by rfl) ⟨207987, by rfl⟩ : syracuseStep 554633 = 415975) B415975
theorem B555227 : Blo 163797 555227 := bstep (se 1 (by rfl) ⟨416420, by rfl⟩ : syracuseStep 555227 = 832841) B832841
theorem B424379 : Blo 163797 424379 := bstep (se 1 (by rfl) ⟨318284, by rfl⟩ : syracuseStep 424379 = 636569) B636569
theorem B3570277 : Blo 163797 3570277 := bstep (se 4 (by rfl) ⟨334713, by rfl⟩ : syracuseStep 3570277 = 669427) B669427
theorem B556091 : Blo 163797 556091 := bstep (se 1 (by rfl) ⟨417068, by rfl⟩ : syracuseStep 556091 = 834137) B834137
theorem B622475 : Blo 163797 622475 := bstep (se 1 (by rfl) ⟨466856, by rfl⟩ : syracuseStep 622475 = 933713) B933713
theorem B163835 : Blo 163797 163835 := bstep (se 1 (by rfl) ⟨122876, by rfl⟩ : syracuseStep 163835 = 245753) B245753
theorem B1999133 : Blo 163797 1999133 := bstep (se 3 (by rfl) ⟨374837, by rfl⟩ : syracuseStep 1999133 = 749675) B749675
theorem B164167 : Blo 163797 164167 := bstep (se 1 (by rfl) ⟨123125, by rfl⟩ : syracuseStep 164167 = 246251) B246251
theorem B164583 : Blo 163797 164583 := bstep (se 1 (by rfl) ⟨123437, by rfl⟩ : syracuseStep 164583 = 246875) B246875
theorem B164607 : Blo 163797 164607 := bstep (se 1 (by rfl) ⟨123455, by rfl⟩ : syracuseStep 164607 = 246911) B246911
theorem B164699 : Blo 163797 164699 := bstep (se 1 (by rfl) ⟨123524, by rfl⟩ : syracuseStep 164699 = 247049) B247049
theorem B3048329 : Blo 163797 3048329 := bstep (se 2 (by rfl) ⟨1143123, by rfl⟩ : syracuseStep 3048329 = 2286247) B2286247
theorem B165019 : Blo 163797 165019 := bstep (se 1 (by rfl) ⟨123764, by rfl⟩ : syracuseStep 165019 = 247529) B247529
theorem B591067 : Blo 163797 591067 := bstep (se 1 (by rfl) ⟨443300, by rfl⟩ : syracuseStep 591067 = 886601) B886601
theorem B165375 : Blo 163797 165375 := bstep (se 1 (by rfl) ⟨124031, by rfl⟩ : syracuseStep 165375 = 248063) B248063
theorem B165467 : Blo 163797 165467 := bstep (se 1 (by rfl) ⟨124100, by rfl⟩ : syracuseStep 165467 = 248201) B248201
theorem B165799 : Blo 163797 165799 := bstep (se 1 (by rfl) ⟨124349, by rfl⟩ : syracuseStep 165799 = 248699) B248699
theorem B166511 : Blo 163797 166511 := bstep (se 1 (by rfl) ⟨124883, by rfl⟩ : syracuseStep 166511 = 249767) B249767
theorem B3181265 : Blo 163797 3181265 := bstep (se 2 (by rfl) ⟨1192974, by rfl⟩ : syracuseStep 3181265 = 2385949) B2385949
theorem B166631 : Blo 163797 166631 := bstep (se 1 (by rfl) ⟨124973, by rfl⟩ : syracuseStep 166631 = 249947) B249947
theorem B1510123 : Blo 163797 1510123 := bstep (se 1 (by rfl) ⟨1132592, by rfl⟩ : syracuseStep 1510123 = 2265185) B2265185
theorem B789473 : Blo 163797 789473 := bstep (se 2 (by rfl) ⟨296052, by rfl⟩ : syracuseStep 789473 = 592105) B592105
theorem B167079 : Blo 163797 167079 := bstep (se 1 (by rfl) ⟨125309, by rfl⟩ : syracuseStep 167079 = 250619) B250619
theorem B626075 : Blo 163797 626075 := bstep (se 1 (by rfl) ⟨469556, by rfl⟩ : syracuseStep 626075 = 939113) B939113
theorem B790013 : Blo 163797 790013 := bstep (se 3 (by rfl) ⟨148127, by rfl⟩ : syracuseStep 790013 = 296255) B296255
theorem B7311005 : Blo 163797 7311005 := bstep (se 3 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 7311005 = 2741627) B2741627
theorem B1544447 : Blo 163797 1544447 := bstep (se 1 (by rfl) ⟨1158335, by rfl⟩ : syracuseStep 1544447 = 2316671) B2316671
theorem B561491 : Blo 163797 561491 := bstep (se 1 (by rfl) ⟨421118, by rfl⟩ : syracuseStep 561491 = 842237) B842237
theorem B792089 : Blo 163797 792089 := bstep (se 2 (by rfl) ⟨297033, by rfl⟩ : syracuseStep 792089 = 594067) B594067
theorem B1873529 : Blo 163797 1873529 := bstep (se 2 (by rfl) ⟨702573, by rfl⟩ : syracuseStep 1873529 = 1405147) B1405147
theorem B235433 : Blo 163797 235433 := bstep (se 2 (by rfl) ⟨88287, by rfl⟩ : syracuseStep 235433 = 176575) B176575
theorem B564137 : Blo 163797 564137 := bstep (se 2 (by rfl) ⟨211551, by rfl⟩ : syracuseStep 564137 = 423103) B423103
theorem B3022055 : Blo 163797 3022055 := bstep (se 1 (by rfl) ⟨2266541, by rfl⟩ : syracuseStep 3022055 = 4533083) B4533083
theorem B236891 : Blo 163797 236891 := bstep (se 1 (by rfl) ⟨177668, by rfl⟩ : syracuseStep 236891 = 355337) B355337
theorem B630463 : Blo 163797 630463 := bstep (se 1 (by rfl) ⟨472847, by rfl⟩ : syracuseStep 630463 = 945695) B945695
theorem B565055 : Blo 163797 565055 := bstep (se 1 (by rfl) ⟨423791, by rfl⟩ : syracuseStep 565055 = 847583) B847583
theorem B401311 : Blo 163797 401311 := bstep (se 1 (by rfl) ⟨300983, by rfl⟩ : syracuseStep 401311 = 601967) B601967
theorem B466879 : Blo 163797 466879 := bstep (se 1 (by rfl) ⟨350159, by rfl⟩ : syracuseStep 466879 = 700319) B700319
theorem B368783 : Blo 163797 368783 := bstep (se 1 (by rfl) ⟨276587, by rfl⟩ : syracuseStep 368783 = 553175) B553175
theorem B369449 : Blo 163797 369449 := bstep (se 2 (by rfl) ⟨138543, by rfl⟩ : syracuseStep 369449 = 277087) B277087
theorem B4760369 : Blo 163797 4760369 := bstep (se 2 (by rfl) ⟨1785138, by rfl⟩ : syracuseStep 4760369 = 3570277) B3570277
theorem B467927 : Blo 163797 467927 := bstep (se 1 (by rfl) ⟨350945, by rfl⟩ : syracuseStep 467927 = 701891) B701891
theorem B83731481 : Blo 163797 83731481 := bstep (se 2 (by rfl) ⟨31399305, by rfl⟩ : syracuseStep 83731481 = 62798611) B62798611
theorem B369755 : Blo 163797 369755 := bstep (se 1 (by rfl) ⟨277316, by rfl⟩ : syracuseStep 369755 = 554633) B554633
theorem B1254851 : Blo 163797 1254851 := bstep (se 1 (by rfl) ⟨941138, by rfl⟩ : syracuseStep 1254851 = 1882277) B1882277
theorem B370151 : Blo 163797 370151 := bstep (se 1 (by rfl) ⟨277613, by rfl⟩ : syracuseStep 370151 = 555227) B555227
theorem B370727 : Blo 163797 370727 := bstep (se 1 (by rfl) ⟨278045, by rfl⟩ : syracuseStep 370727 = 556091) B556091
theorem B207451 : Blo 163797 207451 := bstep (se 1 (by rfl) ⟨155588, by rfl⟩ : syracuseStep 207451 = 311177) B311177
theorem B469739 : Blo 163797 469739 := bstep (se 1 (by rfl) ⟨352304, by rfl⟩ : syracuseStep 469739 = 704609) B704609
theorem B371465 : Blo 163797 371465 := bstep (se 2 (by rfl) ⟨139299, by rfl⟩ : syracuseStep 371465 = 278599) B278599
theorem B600871 : Blo 163797 600871 := bstep (se 1 (by rfl) ⟨450653, by rfl⟩ : syracuseStep 600871 = 901307) B901307
theorem B372059 : Blo 163797 372059 := bstep (se 1 (by rfl) ⟨279044, by rfl⟩ : syracuseStep 372059 = 558089) B558089
theorem B372329 : Blo 163797 372329 := bstep (se 2 (by rfl) ⟨139623, by rfl⟩ : syracuseStep 372329 = 279247) B279247
theorem B1060937 : Blo 163797 1060937 := bstep (se 2 (by rfl) ⟨397851, by rfl⟩ : syracuseStep 1060937 = 795703) B795703
theorem B602255 : Blo 163797 602255 := bstep (se 1 (by rfl) ⟨451691, by rfl⟩ : syracuseStep 602255 = 903383) B903383
theorem B209071 : Blo 163797 209071 := bstep (se 1 (by rfl) ⟨156803, by rfl⟩ : syracuseStep 209071 = 313607) B313607
theorem B2109725 : Blo 163797 2109725 := bstep (se 3 (by rfl) ⟨395573, by rfl⟩ : syracuseStep 2109725 = 791147) B791147
theorem B373031 : Blo 163797 373031 := bstep (se 1 (by rfl) ⟨279773, by rfl⟩ : syracuseStep 373031 = 559547) B559547
theorem B635627 : Blo 163797 635627 := bstep (se 1 (by rfl) ⟨476720, by rfl⟩ : syracuseStep 635627 = 953441) B953441
theorem B2110697 : Blo 163797 2110697 := bstep (se 2 (by rfl) ⟨791511, by rfl⟩ : syracuseStep 2110697 = 1583023) B1583023
theorem B374057 : Blo 163797 374057 := bstep (se 2 (by rfl) ⟨140271, by rfl⟩ : syracuseStep 374057 = 280543) B280543
theorem B472871 : Blo 163797 472871 := bstep (se 1 (by rfl) ⟨354653, by rfl⟩ : syracuseStep 472871 = 709307) B709307
theorem B276527 : Blo 163797 276527 := bstep (se 1 (by rfl) ⟨207395, by rfl⟩ : syracuseStep 276527 = 414791) B414791
theorem B374831 : Blo 163797 374831 := bstep (se 1 (by rfl) ⟨281123, by rfl⟩ : syracuseStep 374831 = 562247) B562247
theorem B473303 : Blo 163797 473303 := bstep (se 1 (by rfl) ⟨354977, by rfl⟩ : syracuseStep 473303 = 709955) B709955
theorem B211567 : Blo 163797 211567 := bstep (se 1 (by rfl) ⟨158675, by rfl⟩ : syracuseStep 211567 = 317351) B317351
theorem B211663 : Blo 163797 211663 := bstep (se 1 (by rfl) ⟨158747, by rfl⟩ : syracuseStep 211663 = 317495) B317495
theorem B375551 : Blo 163797 375551 := bstep (se 1 (by rfl) ⟨281663, by rfl⟩ : syracuseStep 375551 = 563327) B563327
theorem B998183 : Blo 163797 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B834623 : Blo 163797 834623 := bstep (se 1 (by rfl) ⟨625967, by rfl⟩ : syracuseStep 834623 = 1251935) B1251935
theorem B376019 : Blo 163797 376019 := bstep (se 1 (by rfl) ⟨282014, by rfl⟩ : syracuseStep 376019 = 564029) B564029
theorem B34356575 : Blo 163797 34356575 := bstep (se 1 (by rfl) ⟨25767431, by rfl⟩ : syracuseStep 34356575 = 51534863) B51534863
theorem B1785311 : Blo 163797 1785311 := bstep (se 1 (by rfl) ⟨1338983, by rfl⟩ : syracuseStep 1785311 = 2677967) B2677967
theorem B376361 : Blo 163797 376361 := bstep (se 2 (by rfl) ⟨141135, by rfl⟩ : syracuseStep 376361 = 282271) B282271
theorem B441929 : Blo 163797 441929 := bstep (se 2 (by rfl) ⟨165723, by rfl⟩ : syracuseStep 441929 = 331447) B331447
theorem B376595 : Blo 163797 376595 := bstep (se 1 (by rfl) ⟨282446, by rfl⟩ : syracuseStep 376595 = 564893) B564893
theorem B474959 : Blo 163797 474959 := bstep (se 1 (by rfl) ⟨356219, by rfl⟩ : syracuseStep 474959 = 712439) B712439
theorem B245735 : Blo 163797 245735 := bstep (se 1 (by rfl) ⟨184301, by rfl⟩ : syracuseStep 245735 = 368603) B368603
theorem B1064987 : Blo 163797 1064987 := bstep (se 1 (by rfl) ⟨798740, by rfl⟩ : syracuseStep 1064987 = 1597481) B1597481
theorem B311359 : Blo 163797 311359 := bstep (se 1 (by rfl) ⟨233519, by rfl⟩ : syracuseStep 311359 = 467039) B467039
theorem B311465 : Blo 163797 311465 := bstep (se 2 (by rfl) ⟨116799, by rfl⟩ : syracuseStep 311465 = 233599) B233599
theorem B246887 : Blo 163797 246887 := bstep (se 1 (by rfl) ⟨185165, by rfl⟩ : syracuseStep 246887 = 370331) B370331
theorem B247271 : Blo 163797 247271 := bstep (se 1 (by rfl) ⟨185453, by rfl⟩ : syracuseStep 247271 = 370907) B370907
theorem B1820141 : Blo 163797 1820141 := bstep (se 3 (by rfl) ⟨341276, by rfl⟩ : syracuseStep 1820141 = 682553) B682553
theorem B1263113 : Blo 163797 1263113 := bstep (se 2 (by rfl) ⟨473667, by rfl⟩ : syracuseStep 1263113 = 947335) B947335
theorem B247343 : Blo 163797 247343 := bstep (se 1 (by rfl) ⟨185507, by rfl⟩ : syracuseStep 247343 = 371015) B371015
theorem B247535 : Blo 163797 247535 := bstep (se 1 (by rfl) ⟨185651, by rfl⟩ : syracuseStep 247535 = 371303) B371303
theorem B477085 : Blo 163797 477085 := bstep (se 3 (by rfl) ⟨89453, by rfl⟩ : syracuseStep 477085 = 178907) B178907
theorem B838025 : Blo 163797 838025 := bstep (se 2 (by rfl) ⟨314259, by rfl⟩ : syracuseStep 838025 = 628519) B628519
theorem B805295 : Blo 163797 805295 := bstep (se 1 (by rfl) ⟨603971, by rfl⟩ : syracuseStep 805295 = 1207943) B1207943
theorem B314047 : Blo 163797 314047 := bstep (se 1 (by rfl) ⟨235535, by rfl⟩ : syracuseStep 314047 = 471071) B471071
theorem B248639 : Blo 163797 248639 := bstep (se 1 (by rfl) ⟨186479, by rfl⟩ : syracuseStep 248639 = 372959) B372959
theorem B3034259 : Blo 163797 3034259 := bstep (se 1 (by rfl) ⟨2275694, by rfl⟩ : syracuseStep 3034259 = 4551389) B4551389
theorem B3198487 : Blo 163797 3198487 := bstep (se 1 (by rfl) ⟨2398865, by rfl⟩ : syracuseStep 3198487 = 4797731) B4797731
theorem B839807 : Blo 163797 839807 := bstep (se 1 (by rfl) ⟨629855, by rfl⟩ : syracuseStep 839807 = 1259711) B1259711
theorem B774335 : Blo 163797 774335 := bstep (se 1 (by rfl) ⟨580751, by rfl⟩ : syracuseStep 774335 = 1161503) B1161503
theorem B250091 : Blo 163797 250091 := bstep (se 1 (by rfl) ⟨187568, by rfl⟩ : syracuseStep 250091 = 375137) B375137
theorem B282919 : Blo 163797 282919 := bstep (se 1 (by rfl) ⟨212189, by rfl⟩ : syracuseStep 282919 = 424379) B424379
theorem B708983 : Blo 163797 708983 := bstep (se 1 (by rfl) ⟨531737, by rfl⟩ : syracuseStep 708983 = 1063475) B1063475
theorem B1069625 : Blo 163797 1069625 := bstep (se 2 (by rfl) ⟨401109, by rfl⟩ : syracuseStep 1069625 = 802219) B802219
theorem B840455 : Blo 163797 840455 := bstep (se 1 (by rfl) ⟨630341, by rfl⟩ : syracuseStep 840455 = 1260683) B1260683
theorem B676889 : Blo 163797 676889 := bstep (se 2 (by rfl) ⟨253833, by rfl⟩ : syracuseStep 676889 = 507667) B507667
theorem B414841 : Blo 163797 414841 := bstep (se 2 (by rfl) ⟨155565, by rfl⟩ : syracuseStep 414841 = 311131) B311131
theorem B1627303 : Blo 163797 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B414983 : Blo 163797 414983 := bstep (se 1 (by rfl) ⟨311237, by rfl⟩ : syracuseStep 414983 = 622475) B622475
theorem B251327 : Blo 163797 251327 := bstep (se 1 (by rfl) ⟨188495, by rfl⟩ : syracuseStep 251327 = 376991) B376991
theorem B251495 : Blo 163797 251495 := bstep (se 1 (by rfl) ⟨188621, by rfl⟩ : syracuseStep 251495 = 377243) B377243
theorem B251657 : Blo 163797 251657 := bstep (se 2 (by rfl) ⟨94371, by rfl⟩ : syracuseStep 251657 = 188743) B188743
theorem B481751 : Blo 163797 481751 := bstep (se 1 (by rfl) ⟨361313, by rfl⟩ : syracuseStep 481751 = 722627) B722627
theorem B416249 : Blo 163797 416249 := bstep (se 2 (by rfl) ⟨156093, by rfl⟩ : syracuseStep 416249 = 312187) B312187
theorem B416411 : Blo 163797 416411 := bstep (se 1 (by rfl) ⟨312308, by rfl⟩ : syracuseStep 416411 = 624617) B624617
theorem B187375 : Blo 163797 187375 := bstep (se 1 (by rfl) ⟨140531, by rfl⟩ : syracuseStep 187375 = 281063) B281063
theorem B187519 : Blo 163797 187519 := bstep (se 1 (by rfl) ⟨140639, by rfl⟩ : syracuseStep 187519 = 281279) B281279
theorem B843047 : Blo 163797 843047 := bstep (se 1 (by rfl) ⟨632285, by rfl⟩ : syracuseStep 843047 = 1264571) B1264571
theorem B777775 : Blo 163797 777775 := bstep (se 1 (by rfl) ⟨583331, by rfl⟩ : syracuseStep 777775 = 1166663) B1166663
theorem B1433375 : Blo 163797 1433375 := bstep (se 1 (by rfl) ⟨1075031, by rfl⟩ : syracuseStep 1433375 = 2150063) B2150063
theorem B3400393 : Blo 163797 3400393 := bstep (se 2 (by rfl) ⟨1275147, by rfl⟩ : syracuseStep 3400393 = 2550295) B2550295
theorem B943919 : Blo 163797 943919 := bstep (se 1 (by rfl) ⟨707939, by rfl⟩ : syracuseStep 943919 = 1415879) B1415879
theorem B2287561 : Blo 163797 2287561 := bstep (se 2 (by rfl) ⟨857835, by rfl⟩ : syracuseStep 2287561 = 1715671) B1715671
theorem B945377 : Blo 163797 945377 := bstep (se 2 (by rfl) ⟨354516, by rfl⟩ : syracuseStep 945377 = 709033) B709033
theorem B9268465 : Blo 163797 9268465 := bstep (se 2 (by rfl) ⟨3475674, by rfl⟩ : syracuseStep 9268465 = 6951349) B6951349
theorem B847097 : Blo 163797 847097 := bstep (se 2 (by rfl) ⟨317661, by rfl⟩ : syracuseStep 847097 = 635323) B635323
theorem B847259 : Blo 163797 847259 := bstep (se 1 (by rfl) ⟨635444, by rfl⟩ : syracuseStep 847259 = 1270889) B1270889
theorem B946151 : Blo 163797 946151 := bstep (se 1 (by rfl) ⟨709613, by rfl⟩ : syracuseStep 946151 = 1419227) B1419227
theorem B553067 : Blo 163797 553067 := bstep (se 1 (by rfl) ⟨414800, by rfl⟩ : syracuseStep 553067 = 829601) B829601
theorem B422111 : Blo 163797 422111 := bstep (se 1 (by rfl) ⟨316583, by rfl⟩ : syracuseStep 422111 = 633167) B633167
theorem B3044243 : Blo 163797 3044243 := bstep (se 1 (by rfl) ⟨2283182, by rfl⟩ : syracuseStep 3044243 = 4566365) B4566365
theorem B422891 : Blo 163797 422891 := bstep (se 1 (by rfl) ⟨317168, by rfl⟩ : syracuseStep 422891 = 634337) B634337
theorem B423215 : Blo 163797 423215 := bstep (se 1 (by rfl) ⟨317411, by rfl⟩ : syracuseStep 423215 = 634823) B634823
theorem B752489 : Blo 163797 752489 := bstep (se 2 (by rfl) ⟨282183, by rfl⟩ : syracuseStep 752489 = 564367) B564367
theorem B8092871 : Blo 163797 8092871 := bstep (se 1 (by rfl) ⟨6069653, by rfl⟩ : syracuseStep 8092871 = 12139307) B12139307
theorem B1899773 : Blo 163797 1899773 := bstep (se 3 (by rfl) ⟨356207, by rfl⟩ : syracuseStep 1899773 = 712415) B712415
theorem B3571235 : Blo 163797 3571235 := bstep (se 1 (by rfl) ⟨2678426, by rfl⟩ : syracuseStep 3571235 = 5356853) B5356853
theorem B425627 : Blo 163797 425627 := bstep (se 1 (by rfl) ⟨319220, by rfl⟩ : syracuseStep 425627 = 638441) B638441
theorem B2032219 : Blo 163797 2032219 := bstep (se 1 (by rfl) ⟨1524164, by rfl⟩ : syracuseStep 2032219 = 3048329) B3048329
theorem B164591 : Blo 163797 164591 := bstep (se 1 (by rfl) ⟨123443, by rfl⟩ : syracuseStep 164591 = 246887) B246887
theorem B164847 : Blo 163797 164847 := bstep (se 1 (by rfl) ⟨123635, by rfl⟩ : syracuseStep 164847 = 247271) B247271
theorem B1213427 : Blo 163797 1213427 := bstep (se 1 (by rfl) ⟨910070, by rfl⟩ : syracuseStep 1213427 = 1820141) B1820141
theorem B164895 : Blo 163797 164895 := bstep (se 1 (by rfl) ⟨123671, by rfl⟩ : syracuseStep 164895 = 247343) B247343
theorem B165023 : Blo 163797 165023 := bstep (se 1 (by rfl) ⟨123767, by rfl⟩ : syracuseStep 165023 = 247535) B247535
theorem B558683 : Blo 163797 558683 := bstep (se 1 (by rfl) ⟨419012, by rfl⟩ : syracuseStep 558683 = 838025) B838025
theorem B165759 : Blo 163797 165759 := bstep (se 1 (by rfl) ⟨124319, by rfl⟩ : syracuseStep 165759 = 248639) B248639
theorem B526675 : Blo 163797 526675 := bstep (se 1 (by rfl) ⟨395006, by rfl⟩ : syracuseStep 526675 = 790013) B790013
theorem B3050081 : Blo 163797 3050081 := bstep (se 2 (by rfl) ⟨1143780, by rfl⟩ : syracuseStep 3050081 = 2287561) B2287561
theorem B559871 : Blo 163797 559871 := bstep (se 1 (by rfl) ⟨419903, by rfl⟩ : syracuseStep 559871 = 839807) B839807
theorem B166727 : Blo 163797 166727 := bstep (se 1 (by rfl) ⟨125045, by rfl⟩ : syracuseStep 166727 = 250091) B250091
theorem B560303 : Blo 163797 560303 := bstep (se 1 (by rfl) ⟨420227, by rfl⟩ : syracuseStep 560303 = 840455) B840455
theorem B167551 : Blo 163797 167551 := bstep (se 1 (by rfl) ⟨125663, by rfl⟩ : syracuseStep 167551 = 251327) B251327
theorem B528059 : Blo 163797 528059 := bstep (se 1 (by rfl) ⟨396044, by rfl⟩ : syracuseStep 528059 = 792089) B792089
theorem B167663 : Blo 163797 167663 := bstep (se 1 (by rfl) ⟨125747, by rfl⟩ : syracuseStep 167663 = 251495) B251495
theorem B1249019 : Blo 163797 1249019 := bstep (se 1 (by rfl) ⟨936764, by rfl⟩ : syracuseStep 1249019 = 1873529) B1873529
theorem B167771 : Blo 163797 167771 := bstep (se 1 (by rfl) ⟨125828, by rfl⟩ : syracuseStep 167771 = 251657) B251657
theorem B12357953 : Blo 163797 12357953 := bstep (se 2 (by rfl) ⟨4634232, by rfl⟩ : syracuseStep 12357953 = 9268465) B9268465
theorem B4264649 : Blo 163797 4264649 := bstep (se 2 (by rfl) ⟨1599243, by rfl⟩ : syracuseStep 4264649 = 3198487) B3198487
theorem B562031 : Blo 163797 562031 := bstep (se 1 (by rfl) ⟨421523, by rfl⟩ : syracuseStep 562031 = 843047) B843047
theorem B627821 : Blo 163797 627821 := bstep (se 3 (by rfl) ⟨117716, by rfl⟩ : syracuseStep 627821 = 235433) B235433
theorem B955583 : Blo 163797 955583 := bstep (se 1 (by rfl) ⟨716687, by rfl⟩ : syracuseStep 955583 = 1433375) B1433375
theorem B3152357 : Blo 163797 3152357 := bstep (se 4 (by rfl) ⟨295533, by rfl⟩ : syracuseStep 3152357 = 591067) B591067
theorem B629279 : Blo 163797 629279 := bstep (se 1 (by rfl) ⟨471959, by rfl⟩ : syracuseStep 629279 = 943919) B943919
theorem B2169737 : Blo 163797 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B2661821 : Blo 163797 2661821 := bstep (se 3 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 2661821 = 998183) B998183
theorem B630251 : Blo 163797 630251 := bstep (se 1 (by rfl) ⟨472688, by rfl⟩ : syracuseStep 630251 = 945377) B945377
theorem B564731 : Blo 163797 564731 := bstep (se 1 (by rfl) ⟨423548, by rfl⟩ : syracuseStep 564731 = 847097) B847097
theorem B564839 : Blo 163797 564839 := bstep (se 1 (by rfl) ⟨423629, by rfl⟩ : syracuseStep 564839 = 847259) B847259
theorem B2105261 : Blo 163797 2105261 := bstep (se 3 (by rfl) ⟨394736, by rfl⟩ : syracuseStep 2105261 = 789473) B789473
theorem B630767 : Blo 163797 630767 := bstep (se 1 (by rfl) ⟨473075, by rfl⟩ : syracuseStep 630767 = 946151) B946151
theorem B368711 : Blo 163797 368711 := bstep (se 1 (by rfl) ⟨276533, by rfl⟩ : syracuseStep 368711 = 553067) B553067
theorem B401503 : Blo 163797 401503 := bstep (se 1 (by rfl) ⟨301127, by rfl⟩ : syracuseStep 401503 = 602255) B602255
theorem B631709 : Blo 163797 631709 := bstep (se 3 (by rfl) ⟨118445, by rfl⟩ : syracuseStep 631709 = 236891) B236891
theorem B501659 : Blo 163797 501659 := bstep (se 1 (by rfl) ⟨376244, by rfl⟩ : syracuseStep 501659 = 752489) B752489
theorem B1190207 : Blo 163797 1190207 := bstep (se 1 (by rfl) ⟨892655, by rfl⟩ : syracuseStep 1190207 = 1785311) B1785311
theorem B535081 : Blo 163797 535081 := bstep (se 2 (by rfl) ⟨200655, by rfl⟩ : syracuseStep 535081 = 401311) B401311
theorem B830573 : Blo 163797 830573 := bstep (se 3 (by rfl) ⟨155732, by rfl⟩ : syracuseStep 830573 = 311465) B311465
theorem B4533857 : Blo 163797 4533857 := bstep (se 2 (by rfl) ⟨1700196, by rfl⟩ : syracuseStep 4533857 = 3400393) B3400393
theorem B536863 : Blo 163797 536863 := bstep (se 1 (by rfl) ⟨402647, by rfl⟩ : syracuseStep 536863 = 805295) B805295
theorem B636113 : Blo 163797 636113 := bstep (se 2 (by rfl) ⟨238542, by rfl⟩ : syracuseStep 636113 = 477085) B477085
theorem B1029631 : Blo 163797 1029631 := bstep (se 1 (by rfl) ⟨772223, by rfl⟩ : syracuseStep 1029631 = 1544447) B1544447
theorem B374327 : Blo 163797 374327 := bstep (se 1 (by rfl) ⟨280745, by rfl⟩ : syracuseStep 374327 = 561491) B561491
theorem B472655 : Blo 163797 472655 := bstep (se 1 (by rfl) ⟨354491, by rfl⟩ : syracuseStep 472655 = 708983) B708983
theorem B276601 : Blo 163797 276601 := bstep (se 2 (by rfl) ⟨103725, by rfl⟩ : syracuseStep 276601 = 207451) B207451
theorem B276655 : Blo 163797 276655 := bstep (se 1 (by rfl) ⟨207491, by rfl⟩ : syracuseStep 276655 = 414983) B414983
theorem B2013497 : Blo 163797 2013497 := bstep (se 2 (by rfl) ⟨755061, by rfl⟩ : syracuseStep 2013497 = 1510123) B1510123
theorem B801161 : Blo 163797 801161 := bstep (se 2 (by rfl) ⟨300435, by rfl⟩ : syracuseStep 801161 = 600871) B600871
theorem B277499 : Blo 163797 277499 := bstep (se 1 (by rfl) ⟨208124, by rfl⟩ : syracuseStep 277499 = 416249) B416249
theorem B277607 : Blo 163797 277607 := bstep (se 1 (by rfl) ⟨208205, by rfl⟩ : syracuseStep 277607 = 416411) B416411
theorem B376091 : Blo 163797 376091 := bstep (se 1 (by rfl) ⟨282068, by rfl⟩ : syracuseStep 376091 = 564137) B564137
theorem B2014703 : Blo 163797 2014703 := bstep (se 1 (by rfl) ⟨1511027, by rfl⟩ : syracuseStep 2014703 = 3022055) B3022055
theorem B376703 : Blo 163797 376703 := bstep (se 1 (by rfl) ⟨282527, by rfl⟩ : syracuseStep 376703 = 565055) B565055
theorem B245855 : Blo 163797 245855 := bstep (se 1 (by rfl) ⟨184391, by rfl⟩ : syracuseStep 245855 = 368783) B368783
theorem B278761 : Blo 163797 278761 := bstep (se 2 (by rfl) ⟨104535, by rfl⟩ : syracuseStep 278761 = 209071) B209071
theorem B377225 : Blo 163797 377225 := bstep (se 2 (by rfl) ⟨141459, by rfl⟩ : syracuseStep 377225 = 282919) B282919
theorem B246299 : Blo 163797 246299 := bstep (se 1 (by rfl) ⟨184724, by rfl⟩ : syracuseStep 246299 = 369449) B369449
theorem B1262141 : Blo 163797 1262141 := bstep (se 3 (by rfl) ⟨236651, by rfl⟩ : syracuseStep 1262141 = 473303) B473303
theorem B311951 : Blo 163797 311951 := bstep (se 1 (by rfl) ⟨233963, by rfl⟩ : syracuseStep 311951 = 467927) B467927
theorem B55820987 : Blo 163797 55820987 := bstep (se 1 (by rfl) ⟨41865740, by rfl⟩ : syracuseStep 55820987 = 83731481) B83731481
theorem B246503 : Blo 163797 246503 := bstep (se 1 (by rfl) ⟨184877, by rfl⟩ : syracuseStep 246503 = 369755) B369755
theorem B836567 : Blo 163797 836567 := bstep (se 1 (by rfl) ⟨627425, by rfl⟩ : syracuseStep 836567 = 1254851) B1254851
theorem B246767 : Blo 163797 246767 := bstep (se 1 (by rfl) ⟨185075, by rfl⟩ : syracuseStep 246767 = 370151) B370151
theorem B247151 : Blo 163797 247151 := bstep (se 1 (by rfl) ⟨185363, by rfl⟩ : syracuseStep 247151 = 370727) B370727
theorem B313159 : Blo 163797 313159 := bstep (se 1 (by rfl) ⟨234869, by rfl⟩ : syracuseStep 313159 = 469739) B469739
theorem B247643 : Blo 163797 247643 := bstep (se 1 (by rfl) ⟨185732, by rfl⟩ : syracuseStep 247643 = 371465) B371465
theorem B248039 : Blo 163797 248039 := bstep (se 1 (by rfl) ⟨186029, by rfl⟩ : syracuseStep 248039 = 372059) B372059
theorem B248219 : Blo 163797 248219 := bstep (se 1 (by rfl) ⟨186164, by rfl⟩ : syracuseStep 248219 = 372329) B372329
theorem B707291 : Blo 163797 707291 := bstep (se 1 (by rfl) ⟨530468, by rfl⟩ : syracuseStep 707291 = 1060937) B1060937
theorem B281407 : Blo 163797 281407 := bstep (se 1 (by rfl) ⟨211055, by rfl⟩ : syracuseStep 281407 = 422111) B422111
theorem B248687 : Blo 163797 248687 := bstep (se 1 (by rfl) ⟨186515, by rfl⟩ : syracuseStep 248687 = 373031) B373031
theorem B281927 : Blo 163797 281927 := bstep (se 1 (by rfl) ⟨211445, by rfl⟩ : syracuseStep 281927 = 422891) B422891
theorem B282089 : Blo 163797 282089 := bstep (se 2 (by rfl) ⟨105783, by rfl⟩ : syracuseStep 282089 = 211567) B211567
theorem B249371 : Blo 163797 249371 := bstep (se 1 (by rfl) ⟨187028, by rfl⟩ : syracuseStep 249371 = 374057) B374057
theorem B282143 : Blo 163797 282143 := bstep (se 1 (by rfl) ⟨211607, by rfl⟩ : syracuseStep 282143 = 423215) B423215
theorem B282217 : Blo 163797 282217 := bstep (se 2 (by rfl) ⟨105831, by rfl⟩ : syracuseStep 282217 = 211663) B211663
theorem B315247 : Blo 163797 315247 := bstep (se 1 (by rfl) ⟨236435, by rfl⟩ : syracuseStep 315247 = 472871) B472871
theorem B249833 : Blo 163797 249833 := bstep (se 2 (by rfl) ⟨93687, by rfl⟩ : syracuseStep 249833 = 187375) B187375
theorem B184351 : Blo 163797 184351 := bstep (se 1 (by rfl) ⟨138263, by rfl⟩ : syracuseStep 184351 = 276527) B276527
theorem B249887 : Blo 163797 249887 := bstep (se 1 (by rfl) ⟨187415, by rfl⟩ : syracuseStep 249887 = 374831) B374831
theorem B250025 : Blo 163797 250025 := bstep (se 2 (by rfl) ⟨93759, by rfl⟩ : syracuseStep 250025 = 187519) B187519
theorem B250367 : Blo 163797 250367 := bstep (se 1 (by rfl) ⟨187775, by rfl⟩ : syracuseStep 250367 = 375551) B375551
theorem B1037033 : Blo 163797 1037033 := bstep (se 2 (by rfl) ⟨388887, by rfl⟩ : syracuseStep 1037033 = 777775) B777775
theorem B5395247 : Blo 163797 5395247 := bstep (se 1 (by rfl) ⟨4046435, by rfl⟩ : syracuseStep 5395247 = 8092871) B8092871
theorem B250679 : Blo 163797 250679 := bstep (se 1 (by rfl) ⟨188009, by rfl⟩ : syracuseStep 250679 = 376019) B376019
theorem B1266515 : Blo 163797 1266515 := bstep (se 1 (by rfl) ⟨949886, by rfl⟩ : syracuseStep 1266515 = 1899773) B1899773
theorem B840617 : Blo 163797 840617 := bstep (se 2 (by rfl) ⟨315231, by rfl⟩ : syracuseStep 840617 = 630463) B630463
theorem B2380823 : Blo 163797 2380823 := bstep (se 1 (by rfl) ⟨1785617, by rfl⟩ : syracuseStep 2380823 = 3571235) B3571235
theorem B250907 : Blo 163797 250907 := bstep (se 1 (by rfl) ⟨188180, by rfl⟩ : syracuseStep 250907 = 376361) B376361
theorem B283751 : Blo 163797 283751 := bstep (se 1 (by rfl) ⟨212813, by rfl⟩ : syracuseStep 283751 = 425627) B425627
theorem B251063 : Blo 163797 251063 := bstep (se 1 (by rfl) ⟨188297, by rfl⟩ : syracuseStep 251063 = 376595) B376595
theorem B316639 : Blo 163797 316639 := bstep (se 1 (by rfl) ⟨237479, by rfl⟩ : syracuseStep 316639 = 474959) B474959
theorem B709991 : Blo 163797 709991 := bstep (se 1 (by rfl) ⟨532493, by rfl⟩ : syracuseStep 709991 = 1064987) B1064987
theorem B415145 : Blo 163797 415145 := bstep (se 2 (by rfl) ⟨155679, by rfl⟩ : syracuseStep 415145 = 311359) B311359
theorem B1332755 : Blo 163797 1332755 := bstep (se 1 (by rfl) ⟨999566, by rfl⟩ : syracuseStep 1332755 = 1999133) B1999133
theorem B842075 : Blo 163797 842075 := bstep (se 1 (by rfl) ⟨631556, by rfl⟩ : syracuseStep 842075 = 1263113) B1263113
theorem B2120843 : Blo 163797 2120843 := bstep (se 1 (by rfl) ⟨1590632, by rfl⟩ : syracuseStep 2120843 = 3181265) B3181265
theorem B2022839 : Blo 163797 2022839 := bstep (se 1 (by rfl) ⟨1517129, by rfl⟩ : syracuseStep 2022839 = 3034259) B3034259
theorem B417383 : Blo 163797 417383 := bstep (se 1 (by rfl) ⟨313037, by rfl⟩ : syracuseStep 417383 = 626075) B626075
theorem B4874003 : Blo 163797 4874003 := bstep (se 1 (by rfl) ⟨3655502, by rfl⟩ : syracuseStep 4874003 = 7311005) B7311005
theorem B516223 : Blo 163797 516223 := bstep (se 1 (by rfl) ⟨387167, by rfl⟩ : syracuseStep 516223 = 774335) B774335
theorem B713083 : Blo 163797 713083 := bstep (se 1 (by rfl) ⟨534812, by rfl⟩ : syracuseStep 713083 = 1069625) B1069625
theorem B451259 : Blo 163797 451259 := bstep (se 1 (by rfl) ⟨338444, by rfl⟩ : syracuseStep 451259 = 676889) B676889
theorem B418729 : Blo 163797 418729 := bstep (se 2 (by rfl) ⟨157023, by rfl⟩ : syracuseStep 418729 = 314047) B314047
theorem B321167 : Blo 163797 321167 := bstep (se 1 (by rfl) ⟨240875, by rfl⟩ : syracuseStep 321167 = 481751) B481751
theorem B3173579 : Blo 163797 3173579 := bstep (se 1 (by rfl) ⟨2380184, by rfl⟩ : syracuseStep 3173579 = 4760369) B4760369
theorem B553121 : Blo 163797 553121 := bstep (se 2 (by rfl) ⟨207420, by rfl⟩ : syracuseStep 553121 = 414841) B414841
theorem B1406483 : Blo 163797 1406483 := bstep (se 1 (by rfl) ⟨1054862, by rfl⟩ : syracuseStep 1406483 = 2109725) B2109725
theorem B423751 : Blo 163797 423751 := bstep (se 1 (by rfl) ⟨317813, by rfl⟩ : syracuseStep 423751 = 635627) B635627
theorem B2029495 : Blo 163797 2029495 := bstep (se 1 (by rfl) ⟨1522121, by rfl⟩ : syracuseStep 2029495 = 3044243) B3044243
theorem B1407131 : Blo 163797 1407131 := bstep (se 1 (by rfl) ⟨1055348, by rfl⟩ : syracuseStep 1407131 = 2110697) B2110697
theorem B556415 : Blo 163797 556415 := bstep (se 1 (by rfl) ⟨417311, by rfl⟩ : syracuseStep 556415 = 834623) B834623
theorem B22904383 : Blo 163797 22904383 := bstep (se 1 (by rfl) ⟨17178287, by rfl⟩ : syracuseStep 22904383 = 34356575) B34356575
theorem B294619 : Blo 163797 294619 := bstep (se 1 (by rfl) ⟨220964, by rfl⟩ : syracuseStep 294619 = 441929) B441929
theorem B622505 : Blo 163797 622505 := bstep (se 2 (by rfl) ⟨233439, by rfl⟩ : syracuseStep 622505 = 466879) B466879
theorem B163823 : Blo 163797 163823 := bstep (se 1 (by rfl) ⟨122867, by rfl⟩ : syracuseStep 163823 = 245735) B245735
theorem B163903 : Blo 163797 163903 := bstep (se 1 (by rfl) ⟨122927, by rfl⟩ : syracuseStep 163903 = 245855) B245855
theorem B688297 : Blo 163797 688297 := bstep (se 2 (by rfl) ⟨258111, by rfl⟩ : syracuseStep 688297 = 516223) B516223
theorem B164199 : Blo 163797 164199 := bstep (se 1 (by rfl) ⟨123149, by rfl⟩ : syracuseStep 164199 = 246299) B246299
theorem B164335 : Blo 163797 164335 := bstep (se 1 (by rfl) ⟨123251, by rfl⟩ : syracuseStep 164335 = 246503) B246503
theorem B950777 : Blo 163797 950777 := bstep (se 2 (by rfl) ⟨356541, by rfl⟩ : syracuseStep 950777 = 713083) B713083
theorem B557711 : Blo 163797 557711 := bstep (se 1 (by rfl) ⟨418283, by rfl⟩ : syracuseStep 557711 = 836567) B836567
theorem B164511 : Blo 163797 164511 := bstep (se 1 (by rfl) ⟨123383, by rfl⟩ : syracuseStep 164511 = 246767) B246767
theorem B164767 : Blo 163797 164767 := bstep (se 1 (by rfl) ⟨123575, by rfl⟩ : syracuseStep 164767 = 247151) B247151
theorem B558305 : Blo 163797 558305 := bstep (se 2 (by rfl) ⟨209364, by rfl⟩ : syracuseStep 558305 = 418729) B418729
theorem B165095 : Blo 163797 165095 := bstep (se 1 (by rfl) ⟨123821, by rfl⟩ : syracuseStep 165095 = 247643) B247643
theorem B165359 : Blo 163797 165359 := bstep (se 1 (by rfl) ⟨124019, by rfl⟩ : syracuseStep 165359 = 248039) B248039
theorem B165479 : Blo 163797 165479 := bstep (se 1 (by rfl) ⟨124109, by rfl⟩ : syracuseStep 165479 = 248219) B248219
theorem B2033387 : Blo 163797 2033387 := bstep (se 1 (by rfl) ⟨1525040, by rfl⟩ : syracuseStep 2033387 = 3050081) B3050081
theorem B165791 : Blo 163797 165791 := bstep (se 1 (by rfl) ⟨124343, by rfl⟩ : syracuseStep 165791 = 248687) B248687
theorem B166247 : Blo 163797 166247 := bstep (se 1 (by rfl) ⟨124685, by rfl⟩ : syracuseStep 166247 = 249371) B249371
theorem B166555 : Blo 163797 166555 := bstep (se 1 (by rfl) ⟨124916, by rfl⟩ : syracuseStep 166555 = 249833) B249833
theorem B166591 : Blo 163797 166591 := bstep (se 1 (by rfl) ⟨124943, by rfl⟩ : syracuseStep 166591 = 249887) B249887
theorem B166683 : Blo 163797 166683 := bstep (se 1 (by rfl) ⟨125012, by rfl⟩ : syracuseStep 166683 = 250025) B250025
theorem B166911 : Blo 163797 166911 := bstep (se 1 (by rfl) ⟨125183, by rfl⟩ : syracuseStep 166911 = 250367) B250367
theorem B691355 : Blo 163797 691355 := bstep (se 1 (by rfl) ⟨518516, by rfl⟩ : syracuseStep 691355 = 1037033) B1037033
theorem B167119 : Blo 163797 167119 := bstep (se 1 (by rfl) ⟨125339, by rfl⟩ : syracuseStep 167119 = 250679) B250679
theorem B560411 : Blo 163797 560411 := bstep (se 1 (by rfl) ⟨420308, by rfl⟩ : syracuseStep 560411 = 840617) B840617
theorem B167271 : Blo 163797 167271 := bstep (se 1 (by rfl) ⟨125453, by rfl⟩ : syracuseStep 167271 = 250907) B250907
theorem B167375 : Blo 163797 167375 := bstep (se 1 (by rfl) ⟨125531, by rfl⟩ : syracuseStep 167375 = 251063) B251063
theorem B888503 : Blo 163797 888503 := bstep (se 1 (by rfl) ⟨666377, by rfl⟩ : syracuseStep 888503 = 1332755) B1332755
theorem B561383 : Blo 163797 561383 := bstep (se 1 (by rfl) ⟨421037, by rfl⟩ : syracuseStep 561383 = 842075) B842075
theorem B2101571 : Blo 163797 2101571 := bstep (se 1 (by rfl) ⟨1576178, by rfl⟩ : syracuseStep 2101571 = 3152357) B3152357
theorem B1446491 : Blo 163797 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B1413895 : Blo 163797 1413895 := bstep (se 1 (by rfl) ⟨1060421, by rfl⟩ : syracuseStep 1413895 = 2120843) B2120843
theorem B1348559 : Blo 163797 1348559 := bstep (se 1 (by rfl) ⟨1011419, by rfl⟩ : syracuseStep 1348559 = 2022839) B2022839
theorem B1774547 : Blo 163797 1774547 := bstep (se 1 (by rfl) ⟨1330910, by rfl⟩ : syracuseStep 1774547 = 2661821) B2661821
theorem B3249335 : Blo 163797 3249335 := bstep (se 1 (by rfl) ⟨2437001, by rfl⟩ : syracuseStep 3249335 = 4874003) B4874003
theorem B300839 : Blo 163797 300839 := bstep (se 1 (by rfl) ⟨225629, by rfl⟩ : syracuseStep 300839 = 451259) B451259
theorem B334439 : Blo 163797 334439 := bstep (se 1 (by rfl) ⟨250829, by rfl⟩ : syracuseStep 334439 = 501659) B501659
theorem B793471 : Blo 163797 793471 := bstep (se 1 (by rfl) ⟨595103, by rfl⟩ : syracuseStep 793471 = 1190207) B1190207
theorem B3022571 : Blo 163797 3022571 := bstep (se 1 (by rfl) ⟨2266928, by rfl⟩ : syracuseStep 3022571 = 4533857) B4533857
theorem B565001 : Blo 163797 565001 := bstep (se 2 (by rfl) ⟨211875, by rfl⟩ : syracuseStep 565001 = 423751) B423751
theorem B368747 : Blo 163797 368747 := bstep (se 1 (by rfl) ⟨276560, by rfl⟩ : syracuseStep 368747 = 553121) B553121
theorem B368801 : Blo 163797 368801 := bstep (se 2 (by rfl) ⟨138300, by rfl⟩ : syracuseStep 368801 = 276601) B276601
theorem B368873 : Blo 163797 368873 := bstep (se 2 (by rfl) ⟨138327, by rfl⟩ : syracuseStep 368873 = 276655) B276655
theorem B534107 : Blo 163797 534107 := bstep (se 1 (by rfl) ⟨400580, by rfl⟩ : syracuseStep 534107 = 801161) B801161
theorem B370943 : Blo 163797 370943 := bstep (se 1 (by rfl) ⟨278207, by rfl⟩ : syracuseStep 370943 = 556415) B556415
theorem B535337 : Blo 163797 535337 := bstep (se 2 (by rfl) ⟨200751, by rfl⟩ : syracuseStep 535337 = 401503) B401503
theorem B371681 : Blo 163797 371681 := bstep (se 2 (by rfl) ⟨139380, by rfl⟩ : syracuseStep 371681 = 278761) B278761
theorem B372455 : Blo 163797 372455 := bstep (se 1 (by rfl) ⟨279341, by rfl⟩ : syracuseStep 372455 = 558683) B558683
theorem B831869 : Blo 163797 831869 := bstep (se 3 (by rfl) ⟨155975, by rfl⟩ : syracuseStep 831869 = 311951) B311951
theorem B471527 : Blo 163797 471527 := bstep (se 1 (by rfl) ⟨353645, by rfl⟩ : syracuseStep 471527 = 707291) B707291
theorem B373247 : Blo 163797 373247 := bstep (se 1 (by rfl) ⟨279935, by rfl⟩ : syracuseStep 373247 = 559871) B559871
theorem B373535 : Blo 163797 373535 := bstep (se 1 (by rfl) ⟨280151, by rfl⟩ : syracuseStep 373535 = 560303) B560303
theorem B832679 : Blo 163797 832679 := bstep (se 1 (by rfl) ⟨624509, by rfl⟩ : syracuseStep 832679 = 1249019) B1249019
theorem B8238635 : Blo 163797 8238635 := bstep (se 1 (by rfl) ⟨6178976, by rfl⟩ : syracuseStep 8238635 = 12357953) B12357953
theorem B702233 : Blo 163797 702233 := bstep (se 2 (by rfl) ⟨263337, by rfl⟩ : syracuseStep 702233 = 526675) B526675
theorem B374687 : Blo 163797 374687 := bstep (se 1 (by rfl) ⟨281015, by rfl⟩ : syracuseStep 374687 = 562031) B562031
theorem B1587215 : Blo 163797 1587215 := bstep (se 1 (by rfl) ⟨1190411, by rfl⟩ : syracuseStep 1587215 = 2380823) B2380823
theorem B637055 : Blo 163797 637055 := bstep (se 1 (by rfl) ⟨477791, by rfl⟩ : syracuseStep 637055 = 955583) B955583
theorem B473327 : Blo 163797 473327 := bstep (se 1 (by rfl) ⟨354995, by rfl⟩ : syracuseStep 473327 = 709991) B709991
theorem B276763 : Blo 163797 276763 := bstep (se 1 (by rfl) ⟨207572, by rfl⟩ : syracuseStep 276763 = 415145) B415145
theorem B375209 : Blo 163797 375209 := bstep (se 2 (by rfl) ⟨140703, by rfl⟩ : syracuseStep 375209 = 281407) B281407
theorem B376289 : Blo 163797 376289 := bstep (se 2 (by rfl) ⟨141108, by rfl⟩ : syracuseStep 376289 = 282217) B282217
theorem B376487 : Blo 163797 376487 := bstep (se 1 (by rfl) ⟨282365, by rfl⟩ : syracuseStep 376487 = 564731) B564731
theorem B278255 : Blo 163797 278255 := bstep (se 1 (by rfl) ⟨208691, by rfl⟩ : syracuseStep 278255 = 417383) B417383
theorem B376559 : Blo 163797 376559 := bstep (se 1 (by rfl) ⟨282419, by rfl⟩ : syracuseStep 376559 = 564839) B564839
theorem B245801 : Blo 163797 245801 := bstep (se 2 (by rfl) ⟨92175, by rfl⟩ : syracuseStep 245801 = 184351) B184351
theorem B245807 : Blo 163797 245807 := bstep (se 1 (by rfl) ⟨184355, by rfl⟩ : syracuseStep 245807 = 368711) B368711
theorem B214111 : Blo 163797 214111 := bstep (se 1 (by rfl) ⟨160583, by rfl⟩ : syracuseStep 214111 = 321167) B321167
theorem B1688741 : Blo 163797 1688741 := bstep (se 4 (by rfl) ⟨158319, by rfl⟩ : syracuseStep 1688741 = 316639) B316639
theorem B2115719 : Blo 163797 2115719 := bstep (se 1 (by rfl) ⟨1586789, by rfl⟩ : syracuseStep 2115719 = 3173579) B3173579
theorem B2705993 : Blo 163797 2705993 := bstep (se 2 (by rfl) ⟨1014747, by rfl⟩ : syracuseStep 2705993 = 2029495) B2029495
theorem B937655 : Blo 163797 937655 := bstep (se 1 (by rfl) ⟨703241, by rfl⟩ : syracuseStep 937655 = 1406483) B1406483
theorem B249551 : Blo 163797 249551 := bstep (se 1 (by rfl) ⟨187163, by rfl⟩ : syracuseStep 249551 = 374327) B374327
theorem B315103 : Blo 163797 315103 := bstep (se 1 (by rfl) ⟨236327, by rfl⟩ : syracuseStep 315103 = 472655) B472655
theorem B938087 : Blo 163797 938087 := bstep (se 1 (by rfl) ⟨703565, by rfl⟩ : syracuseStep 938087 = 1407131) B1407131
theorem B184999 : Blo 163797 184999 := bstep (se 1 (by rfl) ⟨138749, by rfl⟩ : syracuseStep 184999 = 277499) B277499
theorem B185071 : Blo 163797 185071 := bstep (se 1 (by rfl) ⟨138803, by rfl⟩ : syracuseStep 185071 = 277607) B277607
theorem B250727 : Blo 163797 250727 := bstep (se 1 (by rfl) ⟨188045, by rfl⟩ : syracuseStep 250727 = 376091) B376091
theorem B251135 : Blo 163797 251135 := bstep (se 1 (by rfl) ⟨188351, by rfl⟩ : syracuseStep 251135 = 376703) B376703
theorem B415003 : Blo 163797 415003 := bstep (se 1 (by rfl) ⟨311252, by rfl⟩ : syracuseStep 415003 = 622505) B622505
theorem B251483 : Blo 163797 251483 := bstep (se 1 (by rfl) ⟨188612, by rfl⟩ : syracuseStep 251483 = 377225) B377225
theorem B841427 : Blo 163797 841427 := bstep (se 1 (by rfl) ⟨631070, by rfl⟩ : syracuseStep 841427 = 1262141) B1262141
theorem B37213991 : Blo 163797 37213991 := bstep (se 1 (by rfl) ⟨27910493, by rfl⟩ : syracuseStep 37213991 = 55820987) B55820987
theorem B808951 : Blo 163797 808951 := bstep (se 1 (by rfl) ⟨606713, by rfl⟩ : syracuseStep 808951 = 1213427) B1213427
theorem B2709625 : Blo 163797 2709625 := bstep (se 2 (by rfl) ⟨1016109, by rfl⟩ : syracuseStep 2709625 = 2032219) B2032219
theorem B187951 : Blo 163797 187951 := bstep (se 1 (by rfl) ⟨140963, by rfl⟩ : syracuseStep 187951 = 281927) B281927
theorem B188059 : Blo 163797 188059 := bstep (se 1 (by rfl) ⟨141044, by rfl⟩ : syracuseStep 188059 = 282089) B282089
theorem B188095 : Blo 163797 188095 := bstep (se 1 (by rfl) ⟨141071, by rfl⟩ : syracuseStep 188095 = 282143) B282143
theorem B417545 : Blo 163797 417545 := bstep (se 2 (by rfl) ⟨156579, by rfl⟩ : syracuseStep 417545 = 313159) B313159
theorem B352039 : Blo 163797 352039 := bstep (se 1 (by rfl) ⟨264029, by rfl⟩ : syracuseStep 352039 = 528059) B528059
theorem B2843099 : Blo 163797 2843099 := bstep (se 1 (by rfl) ⟨2132324, by rfl⟩ : syracuseStep 2843099 = 4264649) B4264649
theorem B3596831 : Blo 163797 3596831 := bstep (se 1 (by rfl) ⟨2697623, by rfl⟩ : syracuseStep 3596831 = 5395247) B5395247
theorem B844343 : Blo 163797 844343 := bstep (se 1 (by rfl) ⟨633257, by rfl⟩ : syracuseStep 844343 = 1266515) B1266515
theorem B713441 : Blo 163797 713441 := bstep (se 2 (by rfl) ⟨267540, by rfl⟩ : syracuseStep 713441 = 535081) B535081
theorem B189167 : Blo 163797 189167 := bstep (se 1 (by rfl) ⟨141875, by rfl⟩ : syracuseStep 189167 = 283751) B283751
theorem B418547 : Blo 163797 418547 := bstep (se 1 (by rfl) ⟨313910, by rfl⟩ : syracuseStep 418547 = 627821) B627821
theorem B419519 : Blo 163797 419519 := bstep (se 1 (by rfl) ⟨314639, by rfl⟩ : syracuseStep 419519 = 629279) B629279
theorem B420167 : Blo 163797 420167 := bstep (se 1 (by rfl) ⟨315125, by rfl⟩ : syracuseStep 420167 = 630251) B630251
theorem B420329 : Blo 163797 420329 := bstep (se 2 (by rfl) ⟨157623, by rfl⟩ : syracuseStep 420329 = 315247) B315247
theorem B1403507 : Blo 163797 1403507 := bstep (se 1 (by rfl) ⟨1052630, by rfl⟩ : syracuseStep 1403507 = 2105261) B2105261
theorem B420511 : Blo 163797 420511 := bstep (se 1 (by rfl) ⟨315383, by rfl⟩ : syracuseStep 420511 = 630767) B630767
theorem B715817 : Blo 163797 715817 := bstep (se 2 (by rfl) ⟨268431, by rfl⟩ : syracuseStep 715817 = 536863) B536863
theorem B421139 : Blo 163797 421139 := bstep (se 1 (by rfl) ⟨315854, by rfl⟩ : syracuseStep 421139 = 631709) B631709
theorem B1372841 : Blo 163797 1372841 := bstep (se 2 (by rfl) ⟨514815, by rfl⟩ : syracuseStep 1372841 = 1029631) B1029631
theorem B553715 : Blo 163797 553715 := bstep (se 1 (by rfl) ⟨415286, by rfl⟩ : syracuseStep 553715 = 830573) B830573
theorem B424075 : Blo 163797 424075 := bstep (se 1 (by rfl) ⟨318056, by rfl⟩ : syracuseStep 424075 = 636113) B636113
theorem B1342331 : Blo 163797 1342331 := bstep (se 1 (by rfl) ⟨1006748, by rfl⟩ : syracuseStep 1342331 = 2013497) B2013497
theorem B30539177 : Blo 163797 30539177 := bstep (se 2 (by rfl) ⟨11452191, by rfl⟩ : syracuseStep 30539177 = 22904383) B22904383
theorem B392825 : Blo 163797 392825 := bstep (se 2 (by rfl) ⟨147309, by rfl⟩ : syracuseStep 392825 = 294619) B294619
theorem B1343135 : Blo 163797 1343135 := bstep (se 1 (by rfl) ⟨1007351, by rfl⟩ : syracuseStep 1343135 = 2014703) B2014703
theorem B163867 : Blo 163797 163867 := bstep (se 1 (by rfl) ⟨122900, by rfl⟩ : syracuseStep 163867 = 245801) B245801
theorem B163871 : Blo 163797 163871 := bstep (se 1 (by rfl) ⟨122903, by rfl⟩ : syracuseStep 163871 = 245807) B245807
theorem B917729 : Blo 163797 917729 := bstep (se 2 (by rfl) ⟨344148, by rfl⟩ : syracuseStep 917729 = 688297) B688297
theorem B1410479 : Blo 163797 1410479 := bstep (se 1 (by rfl) ⟨1057859, by rfl⟩ : syracuseStep 1410479 = 2115719) B2115719
theorem B1803995 : Blo 163797 1803995 := bstep (se 1 (by rfl) ⟨1352996, by rfl⟩ : syracuseStep 1803995 = 2705993) B2705993
theorem B460903 : Blo 163797 460903 := bstep (se 1 (by rfl) ⟨345677, by rfl⟩ : syracuseStep 460903 = 691355) B691355
theorem B625103 : Blo 163797 625103 := bstep (se 1 (by rfl) ⟨468827, by rfl⟩ : syracuseStep 625103 = 937655) B937655
theorem B166367 : Blo 163797 166367 := bstep (se 1 (by rfl) ⟨124775, by rfl⟩ : syracuseStep 166367 = 249551) B249551
theorem B625391 : Blo 163797 625391 := bstep (se 1 (by rfl) ⟨469043, by rfl⟩ : syracuseStep 625391 = 938087) B938087
theorem B167151 : Blo 163797 167151 := bstep (se 1 (by rfl) ⟨125363, by rfl⟩ : syracuseStep 167151 = 250727) B250727
theorem B1183031 : Blo 163797 1183031 := bstep (se 1 (by rfl) ⟨887273, by rfl⟩ : syracuseStep 1183031 = 1774547) B1774547
theorem B2166223 : Blo 163797 2166223 := bstep (se 1 (by rfl) ⟨1624667, by rfl⟩ : syracuseStep 2166223 = 3249335) B3249335
theorem B167423 : Blo 163797 167423 := bstep (se 1 (by rfl) ⟨125567, by rfl⟩ : syracuseStep 167423 = 251135) B251135
theorem B560681 : Blo 163797 560681 := bstep (se 2 (by rfl) ⟨210255, by rfl⟩ : syracuseStep 560681 = 420511) B420511
theorem B167655 : Blo 163797 167655 := bstep (se 1 (by rfl) ⟨125741, by rfl⟩ : syracuseStep 167655 = 251483) B251483
theorem B560951 : Blo 163797 560951 := bstep (se 1 (by rfl) ⟨420713, by rfl⟩ : syracuseStep 560951 = 841427) B841427
theorem B24809327 : Blo 163797 24809327 := bstep (se 1 (by rfl) ⟨18606995, by rfl⟩ : syracuseStep 24809327 = 37213991) B37213991
theorem B2397887 : Blo 163797 2397887 := bstep (se 1 (by rfl) ⟨1798415, by rfl⟩ : syracuseStep 2397887 = 3596831) B3596831
theorem B562895 : Blo 163797 562895 := bstep (se 1 (by rfl) ⟨422171, by rfl⟩ : syracuseStep 562895 = 844343) B844343
theorem B3612833 : Blo 163797 3612833 := bstep (se 2 (by rfl) ⟨1354812, by rfl⟩ : syracuseStep 3612833 = 2709625) B2709625
theorem B565433 : Blo 163797 565433 := bstep (se 2 (by rfl) ⟨212037, by rfl⟩ : syracuseStep 565433 = 424075) B424075
theorem B369017 : Blo 163797 369017 := bstep (se 2 (by rfl) ⟨138381, by rfl⟩ : syracuseStep 369017 = 276763) B276763
theorem B369143 : Blo 163797 369143 := bstep (se 1 (by rfl) ⟨276857, by rfl⟩ : syracuseStep 369143 = 553715) B553715
theorem B1057961 : Blo 163797 1057961 := bstep (se 2 (by rfl) ⟨396735, by rfl⟩ : syracuseStep 1057961 = 793471) B793471
theorem B468155 : Blo 163797 468155 := bstep (se 1 (by rfl) ⟨351116, by rfl⟩ : syracuseStep 468155 = 702233) B702233
theorem B1058143 : Blo 163797 1058143 := bstep (se 1 (by rfl) ⟨793607, by rfl⟩ : syracuseStep 1058143 = 1587215) B1587215
theorem B2369341 : Blo 163797 2369341 := bstep (se 3 (by rfl) ⟨444251, by rfl⟩ : syracuseStep 2369341 = 888503) B888503
theorem B894887 : Blo 163797 894887 := bstep (se 1 (by rfl) ⟨671165, by rfl⟩ : syracuseStep 894887 = 1342331) B1342331
theorem B20359451 : Blo 163797 20359451 := bstep (se 1 (by rfl) ⟨15269588, by rfl⟩ : syracuseStep 20359451 = 30539177) B30539177
theorem B469385 : Blo 163797 469385 := bstep (se 2 (by rfl) ⟨176019, by rfl⟩ : syracuseStep 469385 = 352039) B352039
theorem B895423 : Blo 163797 895423 := bstep (se 1 (by rfl) ⟨671567, by rfl⟩ : syracuseStep 895423 = 1343135) B1343135
theorem B633851 : Blo 163797 633851 := bstep (se 1 (by rfl) ⟨475388, by rfl⟩ : syracuseStep 633851 = 950777) B950777
theorem B371807 : Blo 163797 371807 := bstep (se 1 (by rfl) ⟨278855, by rfl⟩ : syracuseStep 371807 = 557711) B557711
theorem B1125827 : Blo 163797 1125827 := bstep (se 1 (by rfl) ⟨844370, by rfl⟩ : syracuseStep 1125827 = 1688741) B1688741
theorem B372203 : Blo 163797 372203 := bstep (se 1 (by rfl) ⟨279152, by rfl⟩ : syracuseStep 372203 = 558305) B558305
theorem B1355591 : Blo 163797 1355591 := bstep (se 1 (by rfl) ⟨1016693, by rfl⟩ : syracuseStep 1355591 = 2033387) B2033387
theorem B373607 : Blo 163797 373607 := bstep (se 1 (by rfl) ⟨280205, by rfl⟩ : syracuseStep 373607 = 560411) B560411
theorem B374255 : Blo 163797 374255 := bstep (se 1 (by rfl) ⟨280691, by rfl⟩ : syracuseStep 374255 = 561383) B561383
theorem B964327 : Blo 163797 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B899039 : Blo 163797 899039 := bstep (se 1 (by rfl) ⟨674279, by rfl⟩ : syracuseStep 899039 = 1348559) B1348559
theorem B802237 : Blo 163797 802237 := bstep (se 3 (by rfl) ⟨150419, by rfl⟩ : syracuseStep 802237 = 300839) B300839
theorem B2015047 : Blo 163797 2015047 := bstep (se 1 (by rfl) ⟨1511285, by rfl⟩ : syracuseStep 2015047 = 3022571) B3022571
theorem B278363 : Blo 163797 278363 := bstep (se 1 (by rfl) ⟨208772, by rfl⟩ : syracuseStep 278363 = 417545) B417545
theorem B376667 : Blo 163797 376667 := bstep (se 1 (by rfl) ⟨282500, by rfl⟩ : syracuseStep 376667 = 565001) B565001
theorem B245831 : Blo 163797 245831 := bstep (se 1 (by rfl) ⟨184373, by rfl⟩ : syracuseStep 245831 = 368747) B368747
theorem B245867 : Blo 163797 245867 := bstep (se 1 (by rfl) ⟨184400, by rfl⟩ : syracuseStep 245867 = 368801) B368801
theorem B245915 : Blo 163797 245915 := bstep (se 1 (by rfl) ⟨184436, by rfl⟩ : syracuseStep 245915 = 368873) B368873
theorem B475627 : Blo 163797 475627 := bstep (se 1 (by rfl) ⟨356720, by rfl⟩ : syracuseStep 475627 = 713441) B713441
theorem B279031 : Blo 163797 279031 := bstep (se 1 (by rfl) ⟨209273, by rfl⟩ : syracuseStep 279031 = 418547) B418547
theorem B246665 : Blo 163797 246665 := bstep (se 2 (by rfl) ⟨92499, by rfl⟩ : syracuseStep 246665 = 184999) B184999
theorem B246761 : Blo 163797 246761 := bstep (se 2 (by rfl) ⟨92535, by rfl⟩ : syracuseStep 246761 = 185071) B185071
theorem B1885193 : Blo 163797 1885193 := bstep (se 2 (by rfl) ⟨706947, by rfl⟩ : syracuseStep 1885193 = 1413895) B1413895
theorem B279679 : Blo 163797 279679 := bstep (se 1 (by rfl) ⟨209759, by rfl⟩ : syracuseStep 279679 = 419519) B419519
theorem B247295 : Blo 163797 247295 := bstep (se 1 (by rfl) ⟨185471, by rfl⟩ : syracuseStep 247295 = 370943) B370943
theorem B280111 : Blo 163797 280111 := bstep (se 1 (by rfl) ⟨210083, by rfl⟩ : syracuseStep 280111 = 420167) B420167
theorem B280219 : Blo 163797 280219 := bstep (se 1 (by rfl) ⟨210164, by rfl⟩ : syracuseStep 280219 = 420329) B420329
theorem B935671 : Blo 163797 935671 := bstep (se 1 (by rfl) ⟨701753, by rfl⟩ : syracuseStep 935671 = 1403507) B1403507
theorem B247787 : Blo 163797 247787 := bstep (se 1 (by rfl) ⟨185840, by rfl⟩ : syracuseStep 247787 = 371681) B371681
theorem B477211 : Blo 163797 477211 := bstep (se 1 (by rfl) ⟨357908, by rfl⟩ : syracuseStep 477211 = 715817) B715817
theorem B280759 : Blo 163797 280759 := bstep (se 1 (by rfl) ⟨210569, by rfl⟩ : syracuseStep 280759 = 421139) B421139
theorem B248303 : Blo 163797 248303 := bstep (se 1 (by rfl) ⟨186227, by rfl⟩ : syracuseStep 248303 = 372455) B372455
theorem B2017781 : Blo 163797 2017781 := bstep (se 5 (by rfl) ⟨94583, by rfl⟩ : syracuseStep 2017781 = 189167) B189167
theorem B314351 : Blo 163797 314351 := bstep (se 1 (by rfl) ⟨235763, by rfl⟩ : syracuseStep 314351 = 471527) B471527
theorem B248831 : Blo 163797 248831 := bstep (se 1 (by rfl) ⟨186623, by rfl⟩ : syracuseStep 248831 = 373247) B373247
theorem B249023 : Blo 163797 249023 := bstep (se 1 (by rfl) ⟨186767, by rfl⟩ : syracuseStep 249023 = 373535) B373535
theorem B5492423 : Blo 163797 5492423 := bstep (se 1 (by rfl) ⟨4119317, by rfl⟩ : syracuseStep 5492423 = 8238635) B8238635
theorem B249791 : Blo 163797 249791 := bstep (se 1 (by rfl) ⟨187343, by rfl⟩ : syracuseStep 249791 = 374687) B374687
theorem B315551 : Blo 163797 315551 := bstep (se 1 (by rfl) ⟨236663, by rfl⟩ : syracuseStep 315551 = 473327) B473327
theorem B250139 : Blo 163797 250139 := bstep (se 1 (by rfl) ⟨187604, by rfl⟩ : syracuseStep 250139 = 375209) B375209
theorem B250601 : Blo 163797 250601 := bstep (se 2 (by rfl) ⟨93975, by rfl⟩ : syracuseStep 250601 = 187951) B187951
theorem B250745 : Blo 163797 250745 := bstep (se 2 (by rfl) ⟨94029, by rfl⟩ : syracuseStep 250745 = 188059) B188059
theorem B250793 : Blo 163797 250793 := bstep (se 2 (by rfl) ⟨94047, by rfl⟩ : syracuseStep 250793 = 188095) B188095
theorem B250859 : Blo 163797 250859 := bstep (se 1 (by rfl) ⟨188144, by rfl⟩ : syracuseStep 250859 = 376289) B376289
theorem B250991 : Blo 163797 250991 := bstep (se 1 (by rfl) ⟨188243, by rfl⟩ : syracuseStep 250991 = 376487) B376487
theorem B185503 : Blo 163797 185503 := bstep (se 1 (by rfl) ⟨139127, by rfl⟩ : syracuseStep 185503 = 278255) B278255
theorem B251039 : Blo 163797 251039 := bstep (se 1 (by rfl) ⟨188279, by rfl⟩ : syracuseStep 251039 = 376559) B376559
theorem B285481 : Blo 163797 285481 := bstep (se 2 (by rfl) ⟨107055, by rfl⟩ : syracuseStep 285481 = 214111) B214111
theorem B1401047 : Blo 163797 1401047 := bstep (se 1 (by rfl) ⟨1050785, by rfl⟩ : syracuseStep 1401047 = 2101571) B2101571
theorem B222959 : Blo 163797 222959 := bstep (se 1 (by rfl) ⟨167219, by rfl⟩ : syracuseStep 222959 = 334439) B334439
theorem B420137 : Blo 163797 420137 := bstep (se 2 (by rfl) ⟨157551, by rfl⟩ : syracuseStep 420137 = 315103) B315103
theorem B1895399 : Blo 163797 1895399 := bstep (se 1 (by rfl) ⟨1421549, by rfl⟩ : syracuseStep 1895399 = 2843099) B2843099
theorem B356071 : Blo 163797 356071 := bstep (se 1 (by rfl) ⟨267053, by rfl⟩ : syracuseStep 356071 = 534107) B534107
theorem B553337 : Blo 163797 553337 := bstep (se 2 (by rfl) ⟨207501, by rfl⟩ : syracuseStep 553337 = 415003) B415003
theorem B356891 : Blo 163797 356891 := bstep (se 1 (by rfl) ⟨267668, by rfl⟩ : syracuseStep 356891 = 535337) B535337
theorem B1078601 : Blo 163797 1078601 := bstep (se 2 (by rfl) ⟨404475, by rfl⟩ : syracuseStep 1078601 = 808951) B808951
theorem B554579 : Blo 163797 554579 := bstep (se 1 (by rfl) ⟨415934, by rfl⟩ : syracuseStep 554579 = 831869) B831869
theorem B915227 : Blo 163797 915227 := bstep (se 1 (by rfl) ⟨686420, by rfl⟩ : syracuseStep 915227 = 1372841) B1372841
theorem B555119 : Blo 163797 555119 := bstep (se 1 (by rfl) ⟨416339, by rfl⟩ : syracuseStep 555119 = 832679) B832679
theorem B424703 : Blo 163797 424703 := bstep (se 1 (by rfl) ⟨318527, by rfl⟩ : syracuseStep 424703 = 637055) B637055
theorem B261883 : Blo 163797 261883 := bstep (se 1 (by rfl) ⟨196412, by rfl⟩ : syracuseStep 261883 = 392825) B392825
theorem B163887 : Blo 163797 163887 := bstep (se 1 (by rfl) ⟨122915, by rfl⟩ : syracuseStep 163887 = 245831) B245831
theorem B163911 : Blo 163797 163911 := bstep (se 1 (by rfl) ⟨122933, by rfl⟩ : syracuseStep 163911 = 245867) B245867
theorem B163943 : Blo 163797 163943 := bstep (se 1 (by rfl) ⟨122957, by rfl⟩ : syracuseStep 163943 = 245915) B245915
theorem B164443 : Blo 163797 164443 := bstep (se 1 (by rfl) ⟨123332, by rfl⟩ : syracuseStep 164443 = 246665) B246665
theorem B164507 : Blo 163797 164507 := bstep (se 1 (by rfl) ⟨123380, by rfl⟩ : syracuseStep 164507 = 246761) B246761
theorem B164863 : Blo 163797 164863 := bstep (se 1 (by rfl) ⟨123647, by rfl⟩ : syracuseStep 164863 = 247295) B247295
theorem B165191 : Blo 163797 165191 := bstep (se 1 (by rfl) ⟨123893, by rfl⟩ : syracuseStep 165191 = 247787) B247787
theorem B951709 : Blo 163797 951709 := bstep (se 3 (by rfl) ⟨178445, by rfl⟩ : syracuseStep 951709 = 356891) B356891
theorem B165535 : Blo 163797 165535 := bstep (se 1 (by rfl) ⟨124151, by rfl⟩ : syracuseStep 165535 = 248303) B248303
theorem B1345187 : Blo 163797 1345187 := bstep (se 1 (by rfl) ⟨1008890, by rfl⟩ : syracuseStep 1345187 = 2017781) B2017781
theorem B1410857 : Blo 163797 1410857 := bstep (se 2 (by rfl) ⟨529071, by rfl⟩ : syracuseStep 1410857 = 1058143) B1058143
theorem B165887 : Blo 163797 165887 := bstep (se 1 (by rfl) ⟨124415, by rfl⟩ : syracuseStep 165887 = 248831) B248831
theorem B166015 : Blo 163797 166015 := bstep (se 1 (by rfl) ⟨124511, by rfl⟩ : syracuseStep 166015 = 249023) B249023
theorem B788687 : Blo 163797 788687 := bstep (se 1 (by rfl) ⟨591515, by rfl⟩ : syracuseStep 788687 = 1183031) B1183031
theorem B1247561 : Blo 163797 1247561 := bstep (se 2 (by rfl) ⟨467835, by rfl⟩ : syracuseStep 1247561 = 935671) B935671
theorem B166527 : Blo 163797 166527 := bstep (se 1 (by rfl) ⟨124895, by rfl⟩ : syracuseStep 166527 = 249791) B249791
theorem B166759 : Blo 163797 166759 := bstep (se 1 (by rfl) ⟨125069, by rfl⟩ : syracuseStep 166759 = 250139) B250139
theorem B2821229 : Blo 163797 2821229 := bstep (se 3 (by rfl) ⟨528980, by rfl⟩ : syracuseStep 2821229 = 1057961) B1057961
theorem B167067 : Blo 163797 167067 := bstep (se 1 (by rfl) ⟨125300, by rfl⟩ : syracuseStep 167067 = 250601) B250601
theorem B167163 : Blo 163797 167163 := bstep (se 1 (by rfl) ⟨125372, by rfl⟩ : syracuseStep 167163 = 250745) B250745
theorem B167195 : Blo 163797 167195 := bstep (se 1 (by rfl) ⟨125396, by rfl⟩ : syracuseStep 167195 = 250793) B250793
theorem B167239 : Blo 163797 167239 := bstep (se 1 (by rfl) ⟨125429, by rfl⟩ : syracuseStep 167239 = 250859) B250859
theorem B167327 : Blo 163797 167327 := bstep (se 1 (by rfl) ⟨125495, by rfl⟩ : syracuseStep 167327 = 250991) B250991
theorem B11505077 : Blo 163797 11505077 := bstep (se 5 (by rfl) ⟨539300, by rfl⟩ : syracuseStep 11505077 = 1078601) B1078601
theorem B167359 : Blo 163797 167359 := bstep (se 1 (by rfl) ⟨125519, by rfl⟩ : syracuseStep 167359 = 251039) B251039
theorem B2888297 : Blo 163797 2888297 := bstep (se 2 (by rfl) ⟨1083111, by rfl⟩ : syracuseStep 2888297 = 2166223) B2166223
theorem B594557 : Blo 163797 594557 := bstep (se 3 (by rfl) ⟨111479, by rfl⟩ : syracuseStep 594557 = 222959) B222959
theorem B596591 : Blo 163797 596591 := bstep (se 1 (by rfl) ⟨447443, by rfl⟩ : syracuseStep 596591 = 894887) B894887
theorem B13572967 : Blo 163797 13572967 := bstep (se 1 (by rfl) ⟨10179725, by rfl⟩ : syracuseStep 13572967 = 20359451) B20359451
theorem B1285769 : Blo 163797 1285769 := bstep (se 2 (by rfl) ⟨482163, by rfl⟩ : syracuseStep 1285769 = 964327) B964327
theorem B368891 : Blo 163797 368891 := bstep (se 1 (by rfl) ⟨276668, by rfl⟩ : syracuseStep 368891 = 553337) B553337
theorem B369719 : Blo 163797 369719 := bstep (se 1 (by rfl) ⟨277289, by rfl⟩ : syracuseStep 369719 = 554579) B554579
theorem B599359 : Blo 163797 599359 := bstep (se 1 (by rfl) ⟨449519, by rfl⟩ : syracuseStep 599359 = 899039) B899039
theorem B370079 : Blo 163797 370079 := bstep (se 1 (by rfl) ⟨277559, by rfl⟩ : syracuseStep 370079 = 555119) B555119
theorem B634169 : Blo 163797 634169 := bstep (se 2 (by rfl) ⟨237813, by rfl⟩ : syracuseStep 634169 = 475627) B475627
theorem B372041 : Blo 163797 372041 := bstep (se 2 (by rfl) ⟨139515, by rfl⟩ : syracuseStep 372041 = 279031) B279031
theorem B1256795 : Blo 163797 1256795 := bstep (se 1 (by rfl) ⟨942596, by rfl⟩ : syracuseStep 1256795 = 1885193) B1885193
theorem B372905 : Blo 163797 372905 := bstep (se 2 (by rfl) ⟨139839, by rfl⟩ : syracuseStep 372905 = 279679) B279679
theorem B209567 : Blo 163797 209567 := bstep (se 1 (by rfl) ⟨157175, by rfl⟩ : syracuseStep 209567 = 314351) B314351
theorem B373481 : Blo 163797 373481 := bstep (se 2 (by rfl) ⟨140055, by rfl⟩ : syracuseStep 373481 = 280111) B280111
theorem B373625 : Blo 163797 373625 := bstep (se 2 (by rfl) ⟨140109, by rfl⟩ : syracuseStep 373625 = 280219) B280219
theorem B373787 : Blo 163797 373787 := bstep (se 1 (by rfl) ⟨280340, by rfl⟩ : syracuseStep 373787 = 560681) B560681
theorem B3159121 : Blo 163797 3159121 := bstep (se 2 (by rfl) ⟨1184670, by rfl⟩ : syracuseStep 3159121 = 2369341) B2369341
theorem B373967 : Blo 163797 373967 := bstep (se 1 (by rfl) ⟨280475, by rfl⟩ : syracuseStep 373967 = 560951) B560951
theorem B636281 : Blo 163797 636281 := bstep (se 2 (by rfl) ⟨238605, by rfl⟩ : syracuseStep 636281 = 477211) B477211
theorem B210367 : Blo 163797 210367 := bstep (se 1 (by rfl) ⟨157775, by rfl⟩ : syracuseStep 210367 = 315551) B315551
theorem B374345 : Blo 163797 374345 := bstep (se 2 (by rfl) ⟨140379, by rfl⟩ : syracuseStep 374345 = 280759) B280759
theorem B1193897 : Blo 163797 1193897 := bstep (se 2 (by rfl) ⟨447711, by rfl⟩ : syracuseStep 1193897 = 895423) B895423
theorem B375263 : Blo 163797 375263 := bstep (se 1 (by rfl) ⟨281447, by rfl⟩ : syracuseStep 375263 = 562895) B562895
theorem B474761 : Blo 163797 474761 := bstep (se 2 (by rfl) ⟨178035, by rfl⟩ : syracuseStep 474761 = 356071) B356071
theorem B2408555 : Blo 163797 2408555 := bstep (se 1 (by rfl) ⟨1806416, by rfl⟩ : syracuseStep 2408555 = 3612833) B3612833
theorem B376955 : Blo 163797 376955 := bstep (se 1 (by rfl) ⟨282716, by rfl⟩ : syracuseStep 376955 = 565433) B565433
theorem B934031 : Blo 163797 934031 := bstep (se 1 (by rfl) ⟨700523, by rfl⟩ : syracuseStep 934031 = 1401047) B1401047
theorem B246011 : Blo 163797 246011 := bstep (se 1 (by rfl) ⟨184508, by rfl⟩ : syracuseStep 246011 = 369017) B369017
theorem B246095 : Blo 163797 246095 := bstep (se 1 (by rfl) ⟨184571, by rfl⟩ : syracuseStep 246095 = 369143) B369143
theorem B312103 : Blo 163797 312103 := bstep (se 1 (by rfl) ⟨234077, by rfl⟩ : syracuseStep 312103 = 468155) B468155
theorem B280091 : Blo 163797 280091 := bstep (se 1 (by rfl) ⟨210068, by rfl⟩ : syracuseStep 280091 = 420137) B420137
theorem B247337 : Blo 163797 247337 := bstep (se 2 (by rfl) ⟨92751, by rfl⟩ : syracuseStep 247337 = 185503) B185503
theorem B312923 : Blo 163797 312923 := bstep (se 1 (by rfl) ⟨234692, by rfl⟩ : syracuseStep 312923 = 469385) B469385
theorem B1263599 : Blo 163797 1263599 := bstep (se 1 (by rfl) ⟨947699, by rfl⟩ : syracuseStep 1263599 = 1895399) B1895399
theorem B247871 : Blo 163797 247871 := bstep (se 1 (by rfl) ⟨185903, by rfl⟩ : syracuseStep 247871 = 371807) B371807
theorem B248135 : Blo 163797 248135 := bstep (se 1 (by rfl) ⟨186101, by rfl⟩ : syracuseStep 248135 = 372203) B372203
theorem B903727 : Blo 163797 903727 := bstep (se 1 (by rfl) ⟨677795, by rfl⟩ : syracuseStep 903727 = 1355591) B1355591
theorem B249071 : Blo 163797 249071 := bstep (se 1 (by rfl) ⟨186803, by rfl⟩ : syracuseStep 249071 = 373607) B373607
theorem B249503 : Blo 163797 249503 := bstep (se 1 (by rfl) ⟨187127, by rfl⟩ : syracuseStep 249503 = 374255) B374255
theorem B380641 : Blo 163797 380641 := bstep (se 2 (by rfl) ⟨142740, by rfl⟩ : syracuseStep 380641 = 285481) B285481
theorem B610151 : Blo 163797 610151 := bstep (se 1 (by rfl) ⟨457613, by rfl⟩ : syracuseStep 610151 = 915227) B915227
theorem B283135 : Blo 163797 283135 := bstep (se 1 (by rfl) ⟨212351, by rfl⟩ : syracuseStep 283135 = 424703) B424703
theorem B1069649 : Blo 163797 1069649 := bstep (se 2 (by rfl) ⟨401118, by rfl⟩ : syracuseStep 1069649 = 802237) B802237
theorem B349177 : Blo 163797 349177 := bstep (se 2 (by rfl) ⟨130941, by rfl⟩ : syracuseStep 349177 = 261883) B261883
theorem B185575 : Blo 163797 185575 := bstep (se 1 (by rfl) ⟨139181, by rfl⟩ : syracuseStep 185575 = 278363) B278363
theorem B251111 : Blo 163797 251111 := bstep (se 1 (by rfl) ⟨188333, by rfl⟩ : syracuseStep 251111 = 376667) B376667
theorem B611819 : Blo 163797 611819 := bstep (se 1 (by rfl) ⟨458864, by rfl⟩ : syracuseStep 611819 = 917729) B917729
theorem B940319 : Blo 163797 940319 := bstep (se 1 (by rfl) ⟨705239, by rfl⟩ : syracuseStep 940319 = 1410479) B1410479
theorem B1202663 : Blo 163797 1202663 := bstep (se 1 (by rfl) ⟨901997, by rfl⟩ : syracuseStep 1202663 = 1803995) B1803995
theorem B416735 : Blo 163797 416735 := bstep (se 1 (by rfl) ⟨312551, by rfl⟩ : syracuseStep 416735 = 625103) B625103
theorem B416927 : Blo 163797 416927 := bstep (se 1 (by rfl) ⟨312695, by rfl⟩ : syracuseStep 416927 = 625391) B625391
theorem B3661615 : Blo 163797 3661615 := bstep (se 1 (by rfl) ⟨2746211, by rfl⟩ : syracuseStep 3661615 = 5492423) B5492423
theorem B16539551 : Blo 163797 16539551 := bstep (se 1 (by rfl) ⟨12404663, by rfl⟩ : syracuseStep 16539551 = 24809327) B24809327
theorem B614537 : Blo 163797 614537 := bstep (se 2 (by rfl) ⟨230451, by rfl⟩ : syracuseStep 614537 = 460903) B460903
theorem B1598591 : Blo 163797 1598591 := bstep (se 1 (by rfl) ⟨1198943, by rfl⟩ : syracuseStep 1598591 = 2397887) B2397887
theorem B422567 : Blo 163797 422567 := bstep (se 1 (by rfl) ⟨316925, by rfl⟩ : syracuseStep 422567 = 633851) B633851
theorem B750551 : Blo 163797 750551 := bstep (se 1 (by rfl) ⟨562913, by rfl⟩ : syracuseStep 750551 = 1125827) B1125827
theorem B10746917 : Blo 163797 10746917 := bstep (se 4 (by rfl) ⟨1007523, by rfl⟩ : syracuseStep 10746917 = 2015047) B2015047
theorem B1605703 : Blo 163797 1605703 := bstep (se 1 (by rfl) ⟨1204277, by rfl⟩ : syracuseStep 1605703 = 2408555) B2408555
theorem B622687 : Blo 163797 622687 := bstep (se 1 (by rfl) ⟨467015, by rfl⟩ : syracuseStep 622687 = 934031) B934031
theorem B164007 : Blo 163797 164007 := bstep (se 1 (by rfl) ⟨123005, by rfl⟩ : syracuseStep 164007 = 246011) B246011
theorem B164063 : Blo 163797 164063 := bstep (se 1 (by rfl) ⟨123047, by rfl⟩ : syracuseStep 164063 = 246095) B246095
theorem B164891 : Blo 163797 164891 := bstep (se 1 (by rfl) ⟨123668, by rfl⟩ : syracuseStep 164891 = 247337) B247337
theorem B165247 : Blo 163797 165247 := bstep (se 1 (by rfl) ⟨123935, by rfl⟩ : syracuseStep 165247 = 247871) B247871
theorem B525791 : Blo 163797 525791 := bstep (se 1 (by rfl) ⟨394343, by rfl⟩ : syracuseStep 525791 = 788687) B788687
theorem B165423 : Blo 163797 165423 := bstep (se 1 (by rfl) ⟨124067, by rfl⟩ : syracuseStep 165423 = 248135) B248135
theorem B558845 : Blo 163797 558845 := bstep (se 3 (by rfl) ⟨104783, by rfl⟩ : syracuseStep 558845 = 209567) B209567
theorem B166047 : Blo 163797 166047 := bstep (se 1 (by rfl) ⟨124535, by rfl⟩ : syracuseStep 166047 = 249071) B249071
theorem B7670051 : Blo 163797 7670051 := bstep (se 1 (by rfl) ⟨5752538, by rfl⟩ : syracuseStep 7670051 = 11505077) B11505077
theorem B166335 : Blo 163797 166335 := bstep (se 1 (by rfl) ⟨124751, by rfl⟩ : syracuseStep 166335 = 249503) B249503
theorem B396371 : Blo 163797 396371 := bstep (se 1 (by rfl) ⟨297278, by rfl⟩ : syracuseStep 396371 = 594557) B594557
theorem B167407 : Blo 163797 167407 := bstep (se 1 (by rfl) ⟨125555, by rfl⟩ : syracuseStep 167407 = 251111) B251111
theorem B626879 : Blo 163797 626879 := bstep (se 1 (by rfl) ⟨470159, by rfl⟩ : syracuseStep 626879 = 940319) B940319
theorem B397727 : Blo 163797 397727 := bstep (se 1 (by rfl) ⟨298295, by rfl⟩ : syracuseStep 397727 = 596591) B596591
theorem B857179 : Blo 163797 857179 := bstep (se 1 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 857179 = 1285769) B1285769
theorem B3183725 : Blo 163797 3183725 := bstep (se 3 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 3183725 = 1193897) B1193897
theorem B465569 : Blo 163797 465569 := bstep (se 2 (by rfl) ⟨174588, by rfl⟩ : syracuseStep 465569 = 349177) B349177
theorem B18097289 : Blo 163797 18097289 := bstep (se 2 (by rfl) ⟨6786483, by rfl⟩ : syracuseStep 18097289 = 13572967) B13572967
theorem B8005877 : Blo 163797 8005877 := bstep (se 5 (by rfl) ⟨375275, by rfl⟩ : syracuseStep 8005877 = 750551) B750551
theorem B896791 : Blo 163797 896791 := bstep (se 1 (by rfl) ⟨672593, by rfl⟩ : syracuseStep 896791 = 1345187) B1345187
theorem B831707 : Blo 163797 831707 := bstep (se 1 (by rfl) ⟨623780, by rfl⟩ : syracuseStep 831707 = 1247561) B1247561
theorem B799145 : Blo 163797 799145 := bstep (se 2 (by rfl) ⟨299679, by rfl⟩ : syracuseStep 799145 = 599359) B599359
theorem B1880819 : Blo 163797 1880819 := bstep (se 1 (by rfl) ⟨1410614, by rfl⟩ : syracuseStep 1880819 = 2821229) B2821229
theorem B407879 : Blo 163797 407879 := bstep (se 1 (by rfl) ⟨305909, by rfl⟩ : syracuseStep 407879 = 611819) B611819
theorem B834461 : Blo 163797 834461 := bstep (se 3 (by rfl) ⟨156461, by rfl⟩ : syracuseStep 834461 = 312923) B312923
theorem B801775 : Blo 163797 801775 := bstep (se 1 (by rfl) ⟨601331, by rfl⟩ : syracuseStep 801775 = 1202663) B1202663
theorem B277823 : Blo 163797 277823 := bstep (se 1 (by rfl) ⟨208367, by rfl⟩ : syracuseStep 277823 = 416735) B416735
theorem B277951 : Blo 163797 277951 := bstep (se 1 (by rfl) ⟨208463, by rfl⟩ : syracuseStep 277951 = 416927) B416927
theorem B507521 : Blo 163797 507521 := bstep (se 2 (by rfl) ⟨190320, by rfl⟩ : syracuseStep 507521 = 380641) B380641
theorem B11026367 : Blo 163797 11026367 := bstep (se 1 (by rfl) ⟨8269775, by rfl⟩ : syracuseStep 11026367 = 16539551) B16539551
theorem B409691 : Blo 163797 409691 := bstep (se 1 (by rfl) ⟨307268, by rfl⟩ : syracuseStep 409691 = 614537) B614537
theorem B245927 : Blo 163797 245927 := bstep (se 1 (by rfl) ⟨184445, by rfl⟩ : syracuseStep 245927 = 368891) B368891
theorem B377513 : Blo 163797 377513 := bstep (se 2 (by rfl) ⟨141567, by rfl⟩ : syracuseStep 377513 = 283135) B283135
theorem B246479 : Blo 163797 246479 := bstep (se 1 (by rfl) ⟨184859, by rfl⟩ : syracuseStep 246479 = 369719) B369719
theorem B1065727 : Blo 163797 1065727 := bstep (se 1 (by rfl) ⟨799295, by rfl⟩ : syracuseStep 1065727 = 1598591) B1598591
theorem B246719 : Blo 163797 246719 := bstep (se 1 (by rfl) ⟨185039, by rfl⟩ : syracuseStep 246719 = 370079) B370079
theorem B4212161 : Blo 163797 4212161 := bstep (se 2 (by rfl) ⟨1579560, by rfl⟩ : syracuseStep 4212161 = 3159121) B3159121
theorem B247433 : Blo 163797 247433 := bstep (se 2 (by rfl) ⟨92787, by rfl⟩ : syracuseStep 247433 = 185575) B185575
theorem B280489 : Blo 163797 280489 := bstep (se 2 (by rfl) ⟨105183, by rfl⟩ : syracuseStep 280489 = 210367) B210367
theorem B248027 : Blo 163797 248027 := bstep (se 1 (by rfl) ⟨186020, by rfl⟩ : syracuseStep 248027 = 372041) B372041
theorem B837863 : Blo 163797 837863 := bstep (se 1 (by rfl) ⟨628397, by rfl⟩ : syracuseStep 837863 = 1256795) B1256795
theorem B248603 : Blo 163797 248603 := bstep (se 1 (by rfl) ⟨186452, by rfl⟩ : syracuseStep 248603 = 372905) B372905
theorem B281711 : Blo 163797 281711 := bstep (se 1 (by rfl) ⟨211283, by rfl⟩ : syracuseStep 281711 = 422567) B422567
theorem B248987 : Blo 163797 248987 := bstep (se 1 (by rfl) ⟨186740, by rfl⟩ : syracuseStep 248987 = 373481) B373481
theorem B249083 : Blo 163797 249083 := bstep (se 1 (by rfl) ⟨186812, by rfl⟩ : syracuseStep 249083 = 373625) B373625
theorem B249191 : Blo 163797 249191 := bstep (se 1 (by rfl) ⟨186893, by rfl⟩ : syracuseStep 249191 = 373787) B373787
theorem B249311 : Blo 163797 249311 := bstep (se 1 (by rfl) ⟨186983, by rfl⟩ : syracuseStep 249311 = 373967) B373967
theorem B249563 : Blo 163797 249563 := bstep (se 1 (by rfl) ⟨187172, by rfl⟩ : syracuseStep 249563 = 374345) B374345
theorem B250175 : Blo 163797 250175 := bstep (se 1 (by rfl) ⟨187631, by rfl⟩ : syracuseStep 250175 = 375263) B375263
theorem B1266029 : Blo 163797 1266029 := bstep (se 3 (by rfl) ⟨237380, by rfl⟩ : syracuseStep 1266029 = 474761) B474761
theorem B7164611 : Blo 163797 7164611 := bstep (se 1 (by rfl) ⟨5373458, by rfl⟩ : syracuseStep 7164611 = 10746917) B10746917
theorem B1627069 : Blo 163797 1627069 := bstep (se 3 (by rfl) ⟨305075, by rfl⟩ : syracuseStep 1627069 = 610151) B610151
theorem B251303 : Blo 163797 251303 := bstep (se 1 (by rfl) ⟨188477, by rfl⟩ : syracuseStep 251303 = 376955) B376955
theorem B186727 : Blo 163797 186727 := bstep (se 1 (by rfl) ⟨140045, by rfl⟩ : syracuseStep 186727 = 280091) B280091
theorem B416137 : Blo 163797 416137 := bstep (se 2 (by rfl) ⟨156051, by rfl⟩ : syracuseStep 416137 = 312103) B312103
theorem B940571 : Blo 163797 940571 := bstep (se 1 (by rfl) ⟨705428, by rfl⟩ : syracuseStep 940571 = 1410857) B1410857
theorem B842399 : Blo 163797 842399 := bstep (se 1 (by rfl) ⟨631799, by rfl⟩ : syracuseStep 842399 = 1263599) B1263599
theorem B1268945 : Blo 163797 1268945 := bstep (se 2 (by rfl) ⟨475854, by rfl⟩ : syracuseStep 1268945 = 951709) B951709
theorem B713099 : Blo 163797 713099 := bstep (se 1 (by rfl) ⟨534824, by rfl⟩ : syracuseStep 713099 = 1069649) B1069649
theorem B1925531 : Blo 163797 1925531 := bstep (se 1 (by rfl) ⟨1444148, by rfl⟩ : syracuseStep 1925531 = 2888297) B2888297
theorem B1204969 : Blo 163797 1204969 := bstep (se 2 (by rfl) ⟨451863, by rfl⟩ : syracuseStep 1204969 = 903727) B903727
theorem B422779 : Blo 163797 422779 := bstep (se 1 (by rfl) ⟨317084, by rfl⟩ : syracuseStep 422779 = 634169) B634169
theorem B424187 : Blo 163797 424187 := bstep (se 1 (by rfl) ⟨318140, by rfl⟩ : syracuseStep 424187 = 636281) B636281
theorem B19528613 : Blo 163797 19528613 := bstep (se 4 (by rfl) ⟨1830807, by rfl⟩ : syracuseStep 19528613 = 3661615) B3661615
theorem B163951 : Blo 163797 163951 := bstep (se 1 (by rfl) ⟨122963, by rfl⟩ : syracuseStep 163951 = 245927) B245927
theorem B164319 : Blo 163797 164319 := bstep (se 1 (by rfl) ⟨123239, by rfl⟩ : syracuseStep 164319 = 246479) B246479
theorem B164479 : Blo 163797 164479 := bstep (se 1 (by rfl) ⟨123359, by rfl⟩ : syracuseStep 164479 = 246719) B246719
theorem B1606625 : Blo 163797 1606625 := bstep (se 2 (by rfl) ⟨602484, by rfl⟩ : syracuseStep 1606625 = 1204969) B1204969
theorem B164955 : Blo 163797 164955 := bstep (se 1 (by rfl) ⟨123716, by rfl⟩ : syracuseStep 164955 = 247433) B247433
theorem B165351 : Blo 163797 165351 := bstep (se 1 (by rfl) ⟨124013, by rfl⟩ : syracuseStep 165351 = 248027) B248027
theorem B558575 : Blo 163797 558575 := bstep (se 1 (by rfl) ⟨418931, by rfl⟩ : syracuseStep 558575 = 837863) B837863
theorem B5113367 : Blo 163797 5113367 := bstep (se 1 (by rfl) ⟨3835025, by rfl⟩ : syracuseStep 5113367 = 7670051) B7670051
theorem B165735 : Blo 163797 165735 := bstep (se 1 (by rfl) ⟨124301, by rfl⟩ : syracuseStep 165735 = 248603) B248603
theorem B165991 : Blo 163797 165991 := bstep (se 1 (by rfl) ⟨124493, by rfl⟩ : syracuseStep 165991 = 248987) B248987
theorem B166055 : Blo 163797 166055 := bstep (se 1 (by rfl) ⟨124541, by rfl⟩ : syracuseStep 166055 = 249083) B249083
theorem B166127 : Blo 163797 166127 := bstep (se 1 (by rfl) ⟨124595, by rfl⟩ : syracuseStep 166127 = 249191) B249191
theorem B166207 : Blo 163797 166207 := bstep (se 1 (by rfl) ⟨124655, by rfl⟩ : syracuseStep 166207 = 249311) B249311
theorem B166375 : Blo 163797 166375 := bstep (se 1 (by rfl) ⟨124781, by rfl⟩ : syracuseStep 166375 = 249563) B249563
theorem B166783 : Blo 163797 166783 := bstep (se 1 (by rfl) ⟨125087, by rfl⟩ : syracuseStep 166783 = 250175) B250175
theorem B265151 : Blo 163797 265151 := bstep (se 1 (by rfl) ⟨198863, by rfl⟩ : syracuseStep 265151 = 397727) B397727
theorem B167535 : Blo 163797 167535 := bstep (se 1 (by rfl) ⟨125651, by rfl⟩ : syracuseStep 167535 = 251303) B251303
theorem B627047 : Blo 163797 627047 := bstep (se 1 (by rfl) ⟨470285, by rfl⟩ : syracuseStep 627047 = 940571) B940571
theorem B561599 : Blo 163797 561599 := bstep (se 1 (by rfl) ⟨421199, by rfl⟩ : syracuseStep 561599 = 842399) B842399
theorem B1283687 : Blo 163797 1283687 := bstep (se 1 (by rfl) ⟨962765, by rfl⟩ : syracuseStep 1283687 = 1925531) B1925531
theorem B12064859 : Blo 163797 12064859 := bstep (se 1 (by rfl) ⟨9048644, by rfl⟩ : syracuseStep 12064859 = 18097289) B18097289
theorem B563705 : Blo 163797 563705 := bstep (se 2 (by rfl) ⟨211389, by rfl⟩ : syracuseStep 563705 = 422779) B422779
theorem B2169425 : Blo 163797 2169425 := bstep (se 2 (by rfl) ⟨813534, by rfl⟩ : syracuseStep 2169425 = 1627069) B1627069
theorem B1056989 : Blo 163797 1056989 := bstep (se 3 (by rfl) ⟨198185, by rfl⟩ : syracuseStep 1056989 = 396371) B396371
theorem B532763 : Blo 163797 532763 := bstep (se 1 (by rfl) ⟨399572, by rfl⟩ : syracuseStep 532763 = 799145) B799145
theorem B1253879 : Blo 163797 1253879 := bstep (se 1 (by rfl) ⟨940409, by rfl⟩ : syracuseStep 1253879 = 1880819) B1880819
theorem B271919 : Blo 163797 271919 := bstep (se 1 (by rfl) ⟨203939, by rfl⟩ : syracuseStep 271919 = 407879) B407879
theorem B370601 : Blo 163797 370601 := bstep (se 2 (by rfl) ⟨138975, by rfl⟩ : syracuseStep 370601 = 277951) B277951
theorem B13019075 : Blo 163797 13019075 := bstep (se 1 (by rfl) ⟨9764306, by rfl⟩ : syracuseStep 13019075 = 19528613) B19528613
theorem B338347 : Blo 163797 338347 := bstep (se 1 (by rfl) ⟨253760, by rfl⟩ : syracuseStep 338347 = 507521) B507521
theorem B7350911 : Blo 163797 7350911 := bstep (se 1 (by rfl) ⟨5513183, by rfl⟩ : syracuseStep 7350911 = 11026367) B11026367
theorem B2140937 : Blo 163797 2140937 := bstep (se 2 (by rfl) ⟨802851, by rfl⟩ : syracuseStep 2140937 = 1605703) B1605703
theorem B830249 : Blo 163797 830249 := bstep (se 2 (by rfl) ⟨311343, by rfl⟩ : syracuseStep 830249 = 622687) B622687
theorem B1092509 : Blo 163797 1092509 := bstep (se 3 (by rfl) ⟨204845, by rfl⟩ : syracuseStep 1092509 = 409691) B409691
theorem B372563 : Blo 163797 372563 := bstep (se 1 (by rfl) ⟨279422, by rfl⟩ : syracuseStep 372563 = 558845) B558845
theorem B373985 : Blo 163797 373985 := bstep (se 2 (by rfl) ⟨140244, by rfl⟩ : syracuseStep 373985 = 280489) B280489
theorem B670141 : Blo 163797 670141 := bstep (se 3 (by rfl) ⟨125651, by rfl⟩ : syracuseStep 670141 = 251303) B251303
theorem B5683877 : Blo 163797 5683877 := bstep (se 4 (by rfl) ⟨532863, by rfl⟩ : syracuseStep 5683877 = 1065727) B1065727
theorem B1195721 : Blo 163797 1195721 := bstep (se 2 (by rfl) ⟨448395, by rfl⟩ : syracuseStep 1195721 = 896791) B896791
theorem B475399 : Blo 163797 475399 := bstep (se 1 (by rfl) ⟨356549, by rfl⟩ : syracuseStep 475399 = 713099) B713099
theorem B4966069 : Blo 163797 4966069 := bstep (se 5 (by rfl) ⟨232784, by rfl⟩ : syracuseStep 4966069 = 465569) B465569
theorem B248969 : Blo 163797 248969 := bstep (se 2 (by rfl) ⟨93363, by rfl⟩ : syracuseStep 248969 = 186727) B186727
theorem B1069033 : Blo 163797 1069033 := bstep (se 2 (by rfl) ⟨400887, by rfl⟩ : syracuseStep 1069033 = 801775) B801775
theorem B282791 : Blo 163797 282791 := bstep (se 1 (by rfl) ⟨212093, by rfl⟩ : syracuseStep 282791 = 424187) B424187
theorem B185215 : Blo 163797 185215 := bstep (se 1 (by rfl) ⟨138911, by rfl⟩ : syracuseStep 185215 = 277823) B277823
theorem B251675 : Blo 163797 251675 := bstep (se 1 (by rfl) ⟨188756, by rfl⟩ : syracuseStep 251675 = 377513) B377513
theorem B2808107 : Blo 163797 2808107 := bstep (se 1 (by rfl) ⟨2106080, by rfl⟩ : syracuseStep 2808107 = 4212161) B4212161
theorem B187807 : Blo 163797 187807 := bstep (se 1 (by rfl) ⟨140855, by rfl⟩ : syracuseStep 187807 = 281711) B281711
theorem B417919 : Blo 163797 417919 := bstep (se 1 (by rfl) ⟨313439, by rfl⟩ : syracuseStep 417919 = 626879) B626879
theorem B844019 : Blo 163797 844019 := bstep (se 1 (by rfl) ⟨633014, by rfl⟩ : syracuseStep 844019 = 1266029) B1266029
theorem B4776407 : Blo 163797 4776407 := bstep (se 1 (by rfl) ⟨3582305, by rfl⟩ : syracuseStep 4776407 = 7164611) B7164611
theorem B2122483 : Blo 163797 2122483 := bstep (se 1 (by rfl) ⟨1591862, by rfl⟩ : syracuseStep 2122483 = 3183725) B3183725
theorem B1402109 : Blo 163797 1402109 := bstep (se 3 (by rfl) ⟨262895, by rfl⟩ : syracuseStep 1402109 = 525791) B525791
theorem B845963 : Blo 163797 845963 := bstep (se 1 (by rfl) ⟨634472, by rfl⟩ : syracuseStep 845963 = 1268945) B1268945
theorem B1142905 : Blo 163797 1142905 := bstep (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) B857179
theorem B5337251 : Blo 163797 5337251 := bstep (se 1 (by rfl) ⟨4002938, by rfl⟩ : syracuseStep 5337251 = 8005877) B8005877
theorem B554471 : Blo 163797 554471 := bstep (se 1 (by rfl) ⟨415853, by rfl⟩ : syracuseStep 554471 = 831707) B831707
theorem B554849 : Blo 163797 554849 := bstep (se 2 (by rfl) ⟨208068, by rfl⟩ : syracuseStep 554849 = 416137) B416137
theorem B556307 : Blo 163797 556307 := bstep (se 1 (by rfl) ⟨417230, by rfl⟩ : syracuseStep 556307 = 834461) B834461
theorem B557225 : Blo 163797 557225 := bstep (se 2 (by rfl) ⟨208959, by rfl⟩ : syracuseStep 557225 = 417919) B417919
theorem B3408911 : Blo 163797 3408911 := bstep (se 1 (by rfl) ⟨2556683, by rfl⟩ : syracuseStep 3408911 = 5113367) B5113367
theorem B165979 : Blo 163797 165979 := bstep (se 1 (by rfl) ⟨124484, by rfl⟩ : syracuseStep 165979 = 248969) B248969
theorem B1804517 : Blo 163797 1804517 := bstep (se 4 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 1804517 = 338347) B338347
theorem B6621425 : Blo 163797 6621425 := bstep (se 2 (by rfl) ⟨2483034, by rfl⟩ : syracuseStep 6621425 = 4966069) B4966069
theorem B855791 : Blo 163797 855791 := bstep (se 1 (by rfl) ⟨641843, by rfl⟩ : syracuseStep 855791 = 1283687) B1283687
theorem B167783 : Blo 163797 167783 := bstep (se 1 (by rfl) ⟨125837, by rfl⟩ : syracuseStep 167783 = 251675) B251675
theorem B725117 : Blo 163797 725117 := bstep (se 3 (by rfl) ⟨135959, by rfl⟩ : syracuseStep 725117 = 271919) B271919
theorem B1872071 : Blo 163797 1872071 := bstep (se 1 (by rfl) ⟨1404053, by rfl⟩ : syracuseStep 1872071 = 2808107) B2808107
theorem B1446283 : Blo 163797 1446283 := bstep (se 1 (by rfl) ⟨1084712, by rfl⟩ : syracuseStep 1446283 = 2169425) B2169425
theorem B562679 : Blo 163797 562679 := bstep (se 1 (by rfl) ⟨422009, by rfl⟩ : syracuseStep 562679 = 844019) B844019
theorem B3184271 : Blo 163797 3184271 := bstep (se 1 (by rfl) ⟨2388203, by rfl⟩ : syracuseStep 3184271 = 4776407) B4776407
theorem B563975 : Blo 163797 563975 := bstep (se 1 (by rfl) ⟨422981, by rfl⟩ : syracuseStep 563975 = 845963) B845963
theorem B893521 : Blo 163797 893521 := bstep (se 2 (by rfl) ⟨335070, by rfl⟩ : syracuseStep 893521 = 670141) B670141
theorem B369647 : Blo 163797 369647 := bstep (se 1 (by rfl) ⟨277235, by rfl⟩ : syracuseStep 369647 = 554471) B554471
theorem B369899 : Blo 163797 369899 := bstep (se 1 (by rfl) ⟨277424, by rfl⟩ : syracuseStep 369899 = 554849) B554849
theorem B370871 : Blo 163797 370871 := bstep (se 1 (by rfl) ⟨278153, by rfl⟩ : syracuseStep 370871 = 556307) B556307
theorem B797147 : Blo 163797 797147 := bstep (se 1 (by rfl) ⟨597860, by rfl⟩ : syracuseStep 797147 = 1195721) B1195721
theorem B633865 : Blo 163797 633865 := bstep (se 2 (by rfl) ⟨237699, by rfl⟩ : syracuseStep 633865 = 475399) B475399
theorem B2829977 : Blo 163797 2829977 := bstep (se 2 (by rfl) ⟨1061241, by rfl⟩ : syracuseStep 2829977 = 2122483) B2122483
theorem B372383 : Blo 163797 372383 := bstep (se 1 (by rfl) ⟨279287, by rfl⟩ : syracuseStep 372383 = 558575) B558575
theorem B374399 : Blo 163797 374399 := bstep (se 1 (by rfl) ⟨280799, by rfl⟩ : syracuseStep 374399 = 561599) B561599
theorem B8043239 : Blo 163797 8043239 := bstep (se 1 (by rfl) ⟨6032429, by rfl⟩ : syracuseStep 8043239 = 12064859) B12064859
theorem B375803 : Blo 163797 375803 := bstep (se 1 (by rfl) ⟨281852, by rfl⟩ : syracuseStep 375803 = 563705) B563705
theorem B1425377 : Blo 163797 1425377 := bstep (se 2 (by rfl) ⟨534516, by rfl⟩ : syracuseStep 1425377 = 1069033) B1069033
theorem B704659 : Blo 163797 704659 := bstep (se 1 (by rfl) ⟨528494, by rfl⟩ : syracuseStep 704659 = 1056989) B1056989
theorem B1523873 : Blo 163797 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B835919 : Blo 163797 835919 := bstep (se 1 (by rfl) ⟨626939, by rfl⟩ : syracuseStep 835919 = 1253879) B1253879
theorem B934739 : Blo 163797 934739 := bstep (se 1 (by rfl) ⟨701054, by rfl⟩ : syracuseStep 934739 = 1402109) B1402109
theorem B246953 : Blo 163797 246953 := bstep (se 2 (by rfl) ⟨92607, by rfl⟩ : syracuseStep 246953 = 185215) B185215
theorem B46613717 : Blo 163797 46613717 := bstep (se 7 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 46613717 = 1092509) B1092509
theorem B247067 : Blo 163797 247067 := bstep (se 1 (by rfl) ⟨185300, by rfl⟩ : syracuseStep 247067 = 370601) B370601
theorem B4900607 : Blo 163797 4900607 := bstep (se 1 (by rfl) ⟨3675455, by rfl⟩ : syracuseStep 4900607 = 7350911) B7350911
theorem B1427291 : Blo 163797 1427291 := bstep (se 1 (by rfl) ⟨1070468, by rfl⟩ : syracuseStep 1427291 = 2140937) B2140937
theorem B707069 : Blo 163797 707069 := bstep (se 3 (by rfl) ⟨132575, by rfl⟩ : syracuseStep 707069 = 265151) B265151
theorem B248375 : Blo 163797 248375 := bstep (se 1 (by rfl) ⟨186281, by rfl⟩ : syracuseStep 248375 = 372563) B372563
theorem B3558167 : Blo 163797 3558167 := bstep (se 1 (by rfl) ⟨2668625, by rfl⟩ : syracuseStep 3558167 = 5337251) B5337251
theorem B249323 : Blo 163797 249323 := bstep (se 1 (by rfl) ⟨186992, by rfl⟩ : syracuseStep 249323 = 373985) B373985
theorem B3789251 : Blo 163797 3789251 := bstep (se 1 (by rfl) ⟨2841938, by rfl⟩ : syracuseStep 3789251 = 5683877) B5683877
theorem B250409 : Blo 163797 250409 := bstep (se 2 (by rfl) ⟨93903, by rfl⟩ : syracuseStep 250409 = 187807) B187807
theorem B1071083 : Blo 163797 1071083 := bstep (se 1 (by rfl) ⟨803312, by rfl⟩ : syracuseStep 1071083 = 1606625) B1606625
theorem B188527 : Blo 163797 188527 := bstep (se 1 (by rfl) ⟨141395, by rfl⟩ : syracuseStep 188527 = 282791) B282791
theorem B418031 : Blo 163797 418031 := bstep (se 1 (by rfl) ⟨313523, by rfl⟩ : syracuseStep 418031 = 627047) B627047
theorem B355175 : Blo 163797 355175 := bstep (se 1 (by rfl) ⟨266381, by rfl⟩ : syracuseStep 355175 = 532763) B532763
theorem B8679383 : Blo 163797 8679383 := bstep (se 1 (by rfl) ⟨6509537, by rfl⟩ : syracuseStep 8679383 = 13019075) B13019075
theorem B553499 : Blo 163797 553499 := bstep (se 1 (by rfl) ⟨415124, by rfl⟩ : syracuseStep 553499 = 830249) B830249
theorem B1015915 : Blo 163797 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B557279 : Blo 163797 557279 := bstep (se 1 (by rfl) ⟨417959, by rfl⟩ : syracuseStep 557279 = 835919) B835919
theorem B1933645 : Blo 163797 1933645 := bstep (se 3 (by rfl) ⟨362558, by rfl⟩ : syracuseStep 1933645 = 725117) B725117
theorem B623159 : Blo 163797 623159 := bstep (se 1 (by rfl) ⟨467369, by rfl⟩ : syracuseStep 623159 = 934739) B934739
theorem B164635 : Blo 163797 164635 := bstep (se 1 (by rfl) ⟨123476, by rfl⟩ : syracuseStep 164635 = 246953) B246953
theorem B164711 : Blo 163797 164711 := bstep (se 1 (by rfl) ⟨123533, by rfl⟩ : syracuseStep 164711 = 247067) B247067
theorem B951527 : Blo 163797 951527 := bstep (se 1 (by rfl) ⟨713645, by rfl⟩ : syracuseStep 951527 = 1427291) B1427291
theorem B165583 : Blo 163797 165583 := bstep (se 1 (by rfl) ⟨124187, by rfl⟩ : syracuseStep 165583 = 248375) B248375
theorem B166215 : Blo 163797 166215 := bstep (se 1 (by rfl) ⟨124661, by rfl⟩ : syracuseStep 166215 = 249323) B249323
theorem B1248047 : Blo 163797 1248047 := bstep (se 1 (by rfl) ⟨936035, by rfl⟩ : syracuseStep 1248047 = 1872071) B1872071
theorem B2526167 : Blo 163797 2526167 := bstep (se 1 (by rfl) ⟨1894625, by rfl⟩ : syracuseStep 2526167 = 3789251) B3789251
theorem B166939 : Blo 163797 166939 := bstep (se 1 (by rfl) ⟨125204, by rfl⟩ : syracuseStep 166939 = 250409) B250409
theorem B2856221 : Blo 163797 2856221 := bstep (se 3 (by rfl) ⟨535541, by rfl⟩ : syracuseStep 2856221 = 1071083) B1071083
theorem B531431 : Blo 163797 531431 := bstep (se 1 (by rfl) ⟨398573, by rfl⟩ : syracuseStep 531431 = 797147) B797147
theorem B236783 : Blo 163797 236783 := bstep (se 1 (by rfl) ⟨177587, by rfl⟩ : syracuseStep 236783 = 355175) B355175
theorem B368999 : Blo 163797 368999 := bstep (se 1 (by rfl) ⟨276749, by rfl⟩ : syracuseStep 368999 = 553499) B553499
theorem B371483 : Blo 163797 371483 := bstep (se 1 (by rfl) ⟨278612, by rfl⟩ : syracuseStep 371483 = 557225) B557225
theorem B2272607 : Blo 163797 2272607 := bstep (se 1 (by rfl) ⟨1704455, by rfl⟩ : syracuseStep 2272607 = 3408911) B3408911
theorem B1191361 : Blo 163797 1191361 := bstep (se 2 (by rfl) ⟨446760, by rfl⟩ : syracuseStep 1191361 = 893521) B893521
theorem B31075811 : Blo 163797 31075811 := bstep (se 1 (by rfl) ⟨23306858, by rfl⟩ : syracuseStep 31075811 = 46613717) B46613717
theorem B471379 : Blo 163797 471379 := bstep (se 1 (by rfl) ⟨353534, by rfl⟩ : syracuseStep 471379 = 707069) B707069
theorem B2372111 : Blo 163797 2372111 := bstep (se 1 (by rfl) ⟨1779083, by rfl⟩ : syracuseStep 2372111 = 3558167) B3558167
theorem B570527 : Blo 163797 570527 := bstep (se 1 (by rfl) ⟨427895, by rfl⟩ : syracuseStep 570527 = 855791) B855791
theorem B375119 : Blo 163797 375119 := bstep (se 1 (by rfl) ⟨281339, by rfl⟩ : syracuseStep 375119 = 562679) B562679
theorem B375983 : Blo 163797 375983 := bstep (se 1 (by rfl) ⟨281987, by rfl⟩ : syracuseStep 375983 = 563975) B563975
theorem B278687 : Blo 163797 278687 := bstep (se 1 (by rfl) ⟨209015, by rfl⟩ : syracuseStep 278687 = 418031) B418031
theorem B246431 : Blo 163797 246431 := bstep (se 1 (by rfl) ⟨184823, by rfl⟩ : syracuseStep 246431 = 369647) B369647
theorem B246599 : Blo 163797 246599 := bstep (se 1 (by rfl) ⟨184949, by rfl⟩ : syracuseStep 246599 = 369899) B369899
theorem B247247 : Blo 163797 247247 := bstep (se 1 (by rfl) ⟨185435, by rfl⟩ : syracuseStep 247247 = 370871) B370871
theorem B1886651 : Blo 163797 1886651 := bstep (se 1 (by rfl) ⟨1414988, by rfl⟩ : syracuseStep 1886651 = 2829977) B2829977
theorem B248255 : Blo 163797 248255 := bstep (se 1 (by rfl) ⟨186191, by rfl⟩ : syracuseStep 248255 = 372383) B372383
theorem B5786255 : Blo 163797 5786255 := bstep (se 1 (by rfl) ⟨4339691, by rfl⟩ : syracuseStep 5786255 = 8679383) B8679383
theorem B249599 : Blo 163797 249599 := bstep (se 1 (by rfl) ⟨187199, by rfl⟩ : syracuseStep 249599 = 374399) B374399
theorem B5362159 : Blo 163797 5362159 := bstep (se 1 (by rfl) ⟨4021619, by rfl⟩ : syracuseStep 5362159 = 8043239) B8043239
theorem B250535 : Blo 163797 250535 := bstep (se 1 (by rfl) ⟨187901, by rfl⟩ : syracuseStep 250535 = 375803) B375803
theorem B251369 : Blo 163797 251369 := bstep (se 2 (by rfl) ⟨94263, by rfl⟩ : syracuseStep 251369 = 188527) B188527
theorem B939545 : Blo 163797 939545 := bstep (se 2 (by rfl) ⟨352329, by rfl⟩ : syracuseStep 939545 = 704659) B704659
theorem B3267071 : Blo 163797 3267071 := bstep (se 1 (by rfl) ⟨2450303, by rfl⟩ : syracuseStep 3267071 = 4900607) B4900607
theorem B1203011 : Blo 163797 1203011 := bstep (se 1 (by rfl) ⟨902258, by rfl⟩ : syracuseStep 1203011 = 1804517) B1804517
theorem B4414283 : Blo 163797 4414283 := bstep (se 1 (by rfl) ⟨3310712, by rfl⟩ : syracuseStep 4414283 = 6621425) B6621425
theorem B2122847 : Blo 163797 2122847 := bstep (se 1 (by rfl) ⟨1592135, by rfl⟩ : syracuseStep 2122847 = 3184271) B3184271
theorem B845153 : Blo 163797 845153 := bstep (se 2 (by rfl) ⟨316932, by rfl⟩ : syracuseStep 845153 = 633865) B633865
theorem B1928377 : Blo 163797 1928377 := bstep (se 2 (by rfl) ⟨723141, by rfl⟩ : syracuseStep 1928377 = 1446283) B1446283
theorem B950251 : Blo 163797 950251 := bstep (se 1 (by rfl) ⟨712688, by rfl⟩ : syracuseStep 950251 = 1425377) B1425377
theorem B164287 : Blo 163797 164287 := bstep (se 1 (by rfl) ⟨123215, by rfl⟩ : syracuseStep 164287 = 246431) B246431
theorem B164399 : Blo 163797 164399 := bstep (se 1 (by rfl) ⟨123299, by rfl⟩ : syracuseStep 164399 = 246599) B246599
theorem B164831 : Blo 163797 164831 := bstep (se 1 (by rfl) ⟨123623, by rfl⟩ : syracuseStep 164831 = 247247) B247247
theorem B165503 : Blo 163797 165503 := bstep (se 1 (by rfl) ⟨124127, by rfl⟩ : syracuseStep 165503 = 248255) B248255
theorem B166399 : Blo 163797 166399 := bstep (se 1 (by rfl) ⟨124799, by rfl⟩ : syracuseStep 166399 = 249599) B249599
theorem B167023 : Blo 163797 167023 := bstep (se 1 (by rfl) ⟨125267, by rfl⟩ : syracuseStep 167023 = 250535) B250535
theorem B1904147 : Blo 163797 1904147 := bstep (se 1 (by rfl) ⟨1428110, by rfl⟩ : syracuseStep 1904147 = 2856221) B2856221
theorem B167579 : Blo 163797 167579 := bstep (se 1 (by rfl) ⟨125684, by rfl⟩ : syracuseStep 167579 = 251369) B251369
theorem B626363 : Blo 163797 626363 := bstep (se 1 (by rfl) ⟨469772, by rfl⟩ : syracuseStep 626363 = 939545) B939545
theorem B628505 : Blo 163797 628505 := bstep (se 2 (by rfl) ⟨235689, by rfl⟩ : syracuseStep 628505 = 471379) B471379
theorem B7149545 : Blo 163797 7149545 := bstep (se 2 (by rfl) ⟨2681079, by rfl⟩ : syracuseStep 7149545 = 5362159) B5362159
theorem B1415231 : Blo 163797 1415231 := bstep (se 1 (by rfl) ⟨1061423, by rfl⟩ : syracuseStep 1415231 = 2122847) B2122847
theorem B563435 : Blo 163797 563435 := bstep (se 1 (by rfl) ⟨422576, by rfl⟩ : syracuseStep 563435 = 845153) B845153
theorem B1515071 : Blo 163797 1515071 := bstep (se 1 (by rfl) ⟨1136303, by rfl⟩ : syracuseStep 1515071 = 2272607) B2272607
theorem B20717207 : Blo 163797 20717207 := bstep (se 1 (by rfl) ⟨15537905, by rfl⟩ : syracuseStep 20717207 = 31075811) B31075811
theorem B1581407 : Blo 163797 1581407 := bstep (se 1 (by rfl) ⟨1186055, by rfl⟩ : syracuseStep 1581407 = 2372111) B2372111
theorem B631421 : Blo 163797 631421 := bstep (se 3 (by rfl) ⟨118391, by rfl⟩ : syracuseStep 631421 = 236783) B236783
theorem B1354553 : Blo 163797 1354553 := bstep (se 2 (by rfl) ⟨507957, by rfl⟩ : syracuseStep 1354553 = 1015915) B1015915
theorem B371519 : Blo 163797 371519 := bstep (se 1 (by rfl) ⟨278639, by rfl⟩ : syracuseStep 371519 = 557279) B557279
theorem B634351 : Blo 163797 634351 := bstep (se 1 (by rfl) ⟨475763, by rfl⟩ : syracuseStep 634351 = 951527) B951527
theorem B1257767 : Blo 163797 1257767 := bstep (se 1 (by rfl) ⟨943325, by rfl⟩ : syracuseStep 1257767 = 1886651) B1886651
theorem B832031 : Blo 163797 832031 := bstep (se 1 (by rfl) ⟨624023, by rfl⟩ : syracuseStep 832031 = 1248047) B1248047
theorem B1684111 : Blo 163797 1684111 := bstep (se 1 (by rfl) ⟨1263083, by rfl⟩ : syracuseStep 1684111 = 2526167) B2526167
theorem B2178047 : Blo 163797 2178047 := bstep (se 1 (by rfl) ⟨1633535, by rfl⟩ : syracuseStep 2178047 = 3267071) B3267071
theorem B802007 : Blo 163797 802007 := bstep (se 1 (by rfl) ⟨601505, by rfl⟩ : syracuseStep 802007 = 1203011) B1203011
theorem B1588481 : Blo 163797 1588481 := bstep (se 2 (by rfl) ⟨595680, by rfl⟩ : syracuseStep 1588481 = 1191361) B1191361
theorem B245999 : Blo 163797 245999 := bstep (se 1 (by rfl) ⟨184499, by rfl⟩ : syracuseStep 245999 = 368999) B368999
theorem B247655 : Blo 163797 247655 := bstep (se 1 (by rfl) ⟨185741, by rfl⟩ : syracuseStep 247655 = 371483) B371483
theorem B380351 : Blo 163797 380351 := bstep (se 1 (by rfl) ⟨285263, by rfl⟩ : syracuseStep 380351 = 570527) B570527
theorem B250079 : Blo 163797 250079 := bstep (se 1 (by rfl) ⟨187559, by rfl⟩ : syracuseStep 250079 = 375119) B375119
theorem B250655 : Blo 163797 250655 := bstep (se 1 (by rfl) ⟨187991, by rfl⟩ : syracuseStep 250655 = 375983) B375983
theorem B1267001 : Blo 163797 1267001 := bstep (se 2 (by rfl) ⟨475125, by rfl⟩ : syracuseStep 1267001 = 950251) B950251
theorem B185791 : Blo 163797 185791 := bstep (se 1 (by rfl) ⟨139343, by rfl⟩ : syracuseStep 185791 = 278687) B278687
theorem B415439 : Blo 163797 415439 := bstep (se 1 (by rfl) ⟨311579, by rfl⟩ : syracuseStep 415439 = 623159) B623159
theorem B2578193 : Blo 163797 2578193 := bstep (se 2 (by rfl) ⟨966822, by rfl⟩ : syracuseStep 2578193 = 1933645) B1933645
theorem B3857503 : Blo 163797 3857503 := bstep (se 1 (by rfl) ⟨2893127, by rfl⟩ : syracuseStep 3857503 = 5786255) B5786255
theorem B2942855 : Blo 163797 2942855 := bstep (se 1 (by rfl) ⟨2207141, by rfl⟩ : syracuseStep 2942855 = 4414283) B4414283
theorem B354287 : Blo 163797 354287 := bstep (se 1 (by rfl) ⟨265715, by rfl⟩ : syracuseStep 354287 = 531431) B531431
theorem B10284677 : Blo 163797 10284677 := bstep (se 4 (by rfl) ⟨964188, by rfl⟩ : syracuseStep 10284677 = 1928377) B1928377
theorem B163999 : Blo 163797 163999 := bstep (se 1 (by rfl) ⟨122999, by rfl⟩ : syracuseStep 163999 = 245999) B245999
theorem B165103 : Blo 163797 165103 := bstep (se 1 (by rfl) ⟨123827, by rfl⟩ : syracuseStep 165103 = 247655) B247655
theorem B166719 : Blo 163797 166719 := bstep (se 1 (by rfl) ⟨125039, by rfl⟩ : syracuseStep 166719 = 250079) B250079
theorem B167103 : Blo 163797 167103 := bstep (se 1 (by rfl) ⟨125327, by rfl⟩ : syracuseStep 167103 = 250655) B250655
theorem B1054271 : Blo 163797 1054271 := bstep (se 1 (by rfl) ⟨790703, by rfl⟩ : syracuseStep 1054271 = 1581407) B1581407
theorem B236191 : Blo 163797 236191 := bstep (se 1 (by rfl) ⟨177143, by rfl⟩ : syracuseStep 236191 = 354287) B354287
theorem B6856451 : Blo 163797 6856451 := bstep (se 1 (by rfl) ⟨5142338, by rfl⟩ : syracuseStep 6856451 = 10284677) B10284677
theorem B5808125 : Blo 163797 5808125 := bstep (se 3 (by rfl) ⟨1089023, by rfl⟩ : syracuseStep 5808125 = 2178047) B2178047
theorem B4040189 : Blo 163797 4040189 := bstep (se 3 (by rfl) ⟨757535, by rfl⟩ : syracuseStep 4040189 = 1515071) B1515071
theorem B534671 : Blo 163797 534671 := bstep (se 1 (by rfl) ⟨401003, by rfl⟩ : syracuseStep 534671 = 802007) B802007
theorem B1058987 : Blo 163797 1058987 := bstep (se 1 (by rfl) ⟨794240, by rfl⟩ : syracuseStep 1058987 = 1588481) B1588481
theorem B276959 : Blo 163797 276959 := bstep (se 1 (by rfl) ⟨207719, by rfl⟩ : syracuseStep 276959 = 415439) B415439
theorem B1718795 : Blo 163797 1718795 := bstep (se 1 (by rfl) ⟨1289096, by rfl⟩ : syracuseStep 1718795 = 2578193) B2578193
theorem B4766363 : Blo 163797 4766363 := bstep (se 1 (by rfl) ⟨3574772, by rfl⟩ : syracuseStep 4766363 = 7149545) B7149545
theorem B375623 : Blo 163797 375623 := bstep (se 1 (by rfl) ⟨281717, by rfl⟩ : syracuseStep 375623 = 563435) B563435
theorem B13811471 : Blo 163797 13811471 := bstep (se 1 (by rfl) ⟨10358603, by rfl⟩ : syracuseStep 13811471 = 20717207) B20717207
theorem B2245481 : Blo 163797 2245481 := bstep (se 2 (by rfl) ⟨842055, by rfl⟩ : syracuseStep 2245481 = 1684111) B1684111
theorem B903035 : Blo 163797 903035 := bstep (se 1 (by rfl) ⟨677276, by rfl⟩ : syracuseStep 903035 = 1354553) B1354553
theorem B247679 : Blo 163797 247679 := bstep (se 1 (by rfl) ⟨185759, by rfl⟩ : syracuseStep 247679 = 371519) B371519
theorem B247721 : Blo 163797 247721 := bstep (se 2 (by rfl) ⟨92895, by rfl⟩ : syracuseStep 247721 = 185791) B185791
theorem B838511 : Blo 163797 838511 := bstep (se 1 (by rfl) ⟨628883, by rfl⟩ : syracuseStep 838511 = 1257767) B1257767
theorem B253567 : Blo 163797 253567 := bstep (se 1 (by rfl) ⟨190175, by rfl⟩ : syracuseStep 253567 = 380351) B380351
theorem B1269431 : Blo 163797 1269431 := bstep (se 1 (by rfl) ⟨952073, by rfl⟩ : syracuseStep 1269431 = 1904147) B1904147
theorem B417575 : Blo 163797 417575 := bstep (se 1 (by rfl) ⟨313181, by rfl⟩ : syracuseStep 417575 = 626363) B626363
theorem B844667 : Blo 163797 844667 := bstep (se 1 (by rfl) ⟨633500, by rfl⟩ : syracuseStep 844667 = 1267001) B1267001
theorem B419003 : Blo 163797 419003 := bstep (se 1 (by rfl) ⟨314252, by rfl⟩ : syracuseStep 419003 = 628505) B628505
theorem B943487 : Blo 163797 943487 := bstep (se 1 (by rfl) ⟨707615, by rfl⟩ : syracuseStep 943487 = 1415231) B1415231
theorem B845801 : Blo 163797 845801 := bstep (se 2 (by rfl) ⟨317175, by rfl⟩ : syracuseStep 845801 = 634351) B634351
theorem B420947 : Blo 163797 420947 := bstep (se 1 (by rfl) ⟨315710, by rfl⟩ : syracuseStep 420947 = 631421) B631421
theorem B1961903 : Blo 163797 1961903 := bstep (se 1 (by rfl) ⟨1471427, by rfl⟩ : syracuseStep 1961903 = 2942855) B2942855
theorem B554687 : Blo 163797 554687 := bstep (se 1 (by rfl) ⟨416015, by rfl⟩ : syracuseStep 554687 = 832031) B832031
theorem B5143337 : Blo 163797 5143337 := bstep (se 2 (by rfl) ⟨1928751, by rfl⟩ : syracuseStep 5143337 = 3857503) B3857503
theorem B165119 : Blo 163797 165119 := bstep (se 1 (by rfl) ⟨123839, by rfl⟩ : syracuseStep 165119 = 247679) B247679
theorem B165147 : Blo 163797 165147 := bstep (se 1 (by rfl) ⟨123860, by rfl⟩ : syracuseStep 165147 = 247721) B247721
theorem B559007 : Blo 163797 559007 := bstep (se 1 (by rfl) ⟨419255, by rfl⟩ : syracuseStep 559007 = 838511) B838511
theorem B3872083 : Blo 163797 3872083 := bstep (se 1 (by rfl) ⟨2904062, by rfl⟩ : syracuseStep 3872083 = 5808125) B5808125
theorem B563111 : Blo 163797 563111 := bstep (se 1 (by rfl) ⟨422333, by rfl⟩ : syracuseStep 563111 = 844667) B844667
theorem B628991 : Blo 163797 628991 := bstep (se 1 (by rfl) ⟨471743, by rfl⟩ : syracuseStep 628991 = 943487) B943487
theorem B2693459 : Blo 163797 2693459 := bstep (se 1 (by rfl) ⟨2020094, by rfl⟩ : syracuseStep 2693459 = 4040189) B4040189
theorem B563867 : Blo 163797 563867 := bstep (se 1 (by rfl) ⟨422900, by rfl⟩ : syracuseStep 563867 = 845801) B845801
theorem B369791 : Blo 163797 369791 := bstep (se 1 (by rfl) ⟨277343, by rfl⟩ : syracuseStep 369791 = 554687) B554687
theorem B338089 : Blo 163797 338089 := bstep (se 2 (by rfl) ⟨126783, by rfl⟩ : syracuseStep 338089 = 253567) B253567
theorem B702847 : Blo 163797 702847 := bstep (se 1 (by rfl) ⟨527135, by rfl⟩ : syracuseStep 702847 = 1054271) B1054271
theorem B2408093 : Blo 163797 2408093 := bstep (se 3 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 2408093 = 903035) B903035
theorem B4570967 : Blo 163797 4570967 := bstep (se 1 (by rfl) ⟨3428225, by rfl⟩ : syracuseStep 4570967 = 6856451) B6856451
theorem B278383 : Blo 163797 278383 := bstep (se 1 (by rfl) ⟨208787, by rfl⟩ : syracuseStep 278383 = 417575) B417575
theorem B279335 : Blo 163797 279335 := bstep (se 1 (by rfl) ⟨209501, by rfl⟩ : syracuseStep 279335 = 419003) B419003
theorem B705991 : Blo 163797 705991 := bstep (se 1 (by rfl) ⟨529493, by rfl⟩ : syracuseStep 705991 = 1058987) B1058987
theorem B280631 : Blo 163797 280631 := bstep (se 1 (by rfl) ⟨210473, by rfl⟩ : syracuseStep 280631 = 420947) B420947
theorem B314921 : Blo 163797 314921 := bstep (se 2 (by rfl) ⟨118095, by rfl⟩ : syracuseStep 314921 = 236191) B236191
theorem B184639 : Blo 163797 184639 := bstep (se 1 (by rfl) ⟨138479, by rfl⟩ : syracuseStep 184639 = 276959) B276959
theorem B3428891 : Blo 163797 3428891 := bstep (se 1 (by rfl) ⟨2571668, by rfl⟩ : syracuseStep 3428891 = 5143337) B5143337
theorem B250415 : Blo 163797 250415 := bstep (se 1 (by rfl) ⟨187811, by rfl⟩ : syracuseStep 250415 = 375623) B375623
theorem B1496987 : Blo 163797 1496987 := bstep (se 1 (by rfl) ⟨1122740, by rfl⟩ : syracuseStep 1496987 = 2245481) B2245481
theorem B846287 : Blo 163797 846287 := bstep (se 1 (by rfl) ⟨634715, by rfl⟩ : syracuseStep 846287 = 1269431) B1269431
theorem B356447 : Blo 163797 356447 := bstep (se 1 (by rfl) ⟨267335, by rfl⟩ : syracuseStep 356447 = 534671) B534671
theorem B1307935 : Blo 163797 1307935 := bstep (se 1 (by rfl) ⟨980951, by rfl⟩ : syracuseStep 1307935 = 1961903) B1961903
theorem B1145863 : Blo 163797 1145863 := bstep (se 1 (by rfl) ⟨859397, by rfl⟩ : syracuseStep 1145863 = 1718795) B1718795
theorem B3177575 : Blo 163797 3177575 := bstep (se 1 (by rfl) ⟨2383181, by rfl⟩ : syracuseStep 3177575 = 4766363) B4766363
theorem B9207647 : Blo 163797 9207647 := bstep (se 1 (by rfl) ⟨6905735, by rfl⟩ : syracuseStep 9207647 = 13811471) B13811471
theorem B950525 : Blo 163797 950525 := bstep (se 3 (by rfl) ⟨178223, by rfl⟩ : syracuseStep 950525 = 356447) B356447
theorem B166943 : Blo 163797 166943 := bstep (se 1 (by rfl) ⟨125207, by rfl⟩ : syracuseStep 166943 = 250415) B250415
theorem B7182557 : Blo 163797 7182557 := bstep (se 3 (by rfl) ⟨1346729, by rfl⟩ : syracuseStep 7182557 = 2693459) B2693459
theorem B564191 : Blo 163797 564191 := bstep (se 1 (by rfl) ⟨423143, by rfl⟩ : syracuseStep 564191 = 846287) B846287
theorem B1743913 : Blo 163797 1743913 := bstep (se 2 (by rfl) ⟨653967, by rfl⟩ : syracuseStep 1743913 = 1307935) B1307935
theorem B371177 : Blo 163797 371177 := bstep (se 2 (by rfl) ⟨139191, by rfl⟩ : syracuseStep 371177 = 278383) B278383
theorem B6138431 : Blo 163797 6138431 := bstep (se 1 (by rfl) ⟨4603823, by rfl⟩ : syracuseStep 6138431 = 9207647) B9207647
theorem B372671 : Blo 163797 372671 := bstep (se 1 (by rfl) ⟨279503, by rfl⟩ : syracuseStep 372671 = 559007) B559007
theorem B209947 : Blo 163797 209947 := bstep (se 1 (by rfl) ⟨157460, by rfl⟩ : syracuseStep 209947 = 314921) B314921
theorem B997991 : Blo 163797 997991 := bstep (se 1 (by rfl) ⟨748493, by rfl⟩ : syracuseStep 997991 = 1496987) B1496987
theorem B375407 : Blo 163797 375407 := bstep (se 1 (by rfl) ⟨281555, by rfl⟩ : syracuseStep 375407 = 563111) B563111
theorem B375911 : Blo 163797 375911 := bstep (se 1 (by rfl) ⟨281933, by rfl⟩ : syracuseStep 375911 = 563867) B563867
theorem B246185 : Blo 163797 246185 := bstep (se 2 (by rfl) ⟨92319, by rfl⟩ : syracuseStep 246185 = 184639) B184639
theorem B246527 : Blo 163797 246527 := bstep (se 1 (by rfl) ⟨184895, by rfl⟩ : syracuseStep 246527 = 369791) B369791
theorem B5162777 : Blo 163797 5162777 := bstep (se 2 (by rfl) ⟨1936041, by rfl⟩ : syracuseStep 5162777 = 3872083) B3872083
theorem B937129 : Blo 163797 937129 := bstep (se 2 (by rfl) ⟨351423, by rfl⟩ : syracuseStep 937129 = 702847) B702847
theorem B1527817 : Blo 163797 1527817 := bstep (se 2 (by rfl) ⟨572931, by rfl⟩ : syracuseStep 1527817 = 1145863) B1145863
theorem B2118383 : Blo 163797 2118383 := bstep (se 1 (by rfl) ⟨1588787, by rfl⟩ : syracuseStep 2118383 = 3177575) B3177575
theorem B186223 : Blo 163797 186223 := bstep (se 1 (by rfl) ⟨139667, by rfl⟩ : syracuseStep 186223 = 279335) B279335
theorem B187087 : Blo 163797 187087 := bstep (se 1 (by rfl) ⟨140315, by rfl⟩ : syracuseStep 187087 = 280631) B280631
theorem B941321 : Blo 163797 941321 := bstep (se 2 (by rfl) ⟨352995, by rfl⟩ : syracuseStep 941321 = 705991) B705991
theorem B450785 : Blo 163797 450785 := bstep (se 2 (by rfl) ⟨169044, by rfl⟩ : syracuseStep 450785 = 338089) B338089
theorem B2285927 : Blo 163797 2285927 := bstep (se 1 (by rfl) ⟨1714445, by rfl⟩ : syracuseStep 2285927 = 3428891) B3428891
theorem B419327 : Blo 163797 419327 := bstep (se 1 (by rfl) ⟨314495, by rfl⟩ : syracuseStep 419327 = 628991) B628991
theorem B1605395 : Blo 163797 1605395 := bstep (se 1 (by rfl) ⟨1204046, by rfl⟩ : syracuseStep 1605395 = 2408093) B2408093
theorem B3047311 : Blo 163797 3047311 := bstep (se 1 (by rfl) ⟨2285483, by rfl⟩ : syracuseStep 3047311 = 4570967) B4570967
theorem B164123 : Blo 163797 164123 := bstep (se 1 (by rfl) ⟨123092, by rfl⟩ : syracuseStep 164123 = 246185) B246185
theorem B164351 : Blo 163797 164351 := bstep (se 1 (by rfl) ⟨123263, by rfl⟩ : syracuseStep 164351 = 246527) B246527
theorem B3441851 : Blo 163797 3441851 := bstep (se 1 (by rfl) ⟨2581388, by rfl⟩ : syracuseStep 3441851 = 5162777) B5162777
theorem B1412255 : Blo 163797 1412255 := bstep (se 1 (by rfl) ⟨1059191, by rfl⟩ : syracuseStep 1412255 = 2118383) B2118383
theorem B4788371 : Blo 163797 4788371 := bstep (se 1 (by rfl) ⟨3591278, by rfl⟩ : syracuseStep 4788371 = 7182557) B7182557
theorem B1249505 : Blo 163797 1249505 := bstep (se 2 (by rfl) ⟨468564, by rfl⟩ : syracuseStep 1249505 = 937129) B937129
theorem B627547 : Blo 163797 627547 := bstep (se 1 (by rfl) ⟨470660, by rfl⟩ : syracuseStep 627547 = 941321) B941321
theorem B2037089 : Blo 163797 2037089 := bstep (se 2 (by rfl) ⟨763908, by rfl⟩ : syracuseStep 2037089 = 1527817) B1527817
theorem B300523 : Blo 163797 300523 := bstep (se 1 (by rfl) ⟨225392, by rfl⟩ : syracuseStep 300523 = 450785) B450785
theorem B665327 : Blo 163797 665327 := bstep (se 1 (by rfl) ⟨498995, by rfl⟩ : syracuseStep 665327 = 997991) B997991
theorem B633683 : Blo 163797 633683 := bstep (se 1 (by rfl) ⟨475262, by rfl⟩ : syracuseStep 633683 = 950525) B950525
theorem B376127 : Blo 163797 376127 := bstep (se 1 (by rfl) ⟨282095, by rfl⟩ : syracuseStep 376127 = 564191) B564191
theorem B1523951 : Blo 163797 1523951 := bstep (se 1 (by rfl) ⟨1142963, by rfl⟩ : syracuseStep 1523951 = 2285927) B2285927
theorem B279551 : Blo 163797 279551 := bstep (se 1 (by rfl) ⟨209663, by rfl⟩ : syracuseStep 279551 = 419327) B419327
theorem B279929 : Blo 163797 279929 := bstep (se 2 (by rfl) ⟨104973, by rfl⟩ : syracuseStep 279929 = 209947) B209947
theorem B247451 : Blo 163797 247451 := bstep (se 1 (by rfl) ⟨185588, by rfl⟩ : syracuseStep 247451 = 371177) B371177
theorem B248297 : Blo 163797 248297 := bstep (se 2 (by rfl) ⟨93111, by rfl⟩ : syracuseStep 248297 = 186223) B186223
theorem B248447 : Blo 163797 248447 := bstep (se 1 (by rfl) ⟨186335, by rfl⟩ : syracuseStep 248447 = 372671) B372671
theorem B249449 : Blo 163797 249449 := bstep (se 2 (by rfl) ⟨93543, by rfl⟩ : syracuseStep 249449 = 187087) B187087
theorem B250271 : Blo 163797 250271 := bstep (se 1 (by rfl) ⟨187703, by rfl⟩ : syracuseStep 250271 = 375407) B375407
theorem B250607 : Blo 163797 250607 := bstep (se 1 (by rfl) ⟨187955, by rfl⟩ : syracuseStep 250607 = 375911) B375911
theorem B1070263 : Blo 163797 1070263 := bstep (se 1 (by rfl) ⟨802697, by rfl⟩ : syracuseStep 1070263 = 1605395) B1605395
theorem B4092287 : Blo 163797 4092287 := bstep (se 1 (by rfl) ⟨3069215, by rfl⟩ : syracuseStep 4092287 = 6138431) B6138431
theorem B2325217 : Blo 163797 2325217 := bstep (se 2 (by rfl) ⟨871956, by rfl⟩ : syracuseStep 2325217 = 1743913) B1743913
theorem B4063081 : Blo 163797 4063081 := bstep (se 2 (by rfl) ⟨1523655, by rfl⟩ : syracuseStep 4063081 = 3047311) B3047311
theorem B1015967 : Blo 163797 1015967 := bstep (se 1 (by rfl) ⟨761975, by rfl⟩ : syracuseStep 1015967 = 1523951) B1523951
theorem B2294567 : Blo 163797 2294567 := bstep (se 1 (by rfl) ⟨1720925, by rfl⟩ : syracuseStep 2294567 = 3441851) B3441851
theorem B10912765 : Blo 163797 10912765 := bstep (se 3 (by rfl) ⟨2046143, by rfl⟩ : syracuseStep 10912765 = 4092287) B4092287
theorem B164967 : Blo 163797 164967 := bstep (se 1 (by rfl) ⟨123725, by rfl⟩ : syracuseStep 164967 = 247451) B247451
theorem B165531 : Blo 163797 165531 := bstep (se 1 (by rfl) ⟨124148, by rfl⟩ : syracuseStep 165531 = 248297) B248297
theorem B165631 : Blo 163797 165631 := bstep (se 1 (by rfl) ⟨124223, by rfl⟩ : syracuseStep 165631 = 248447) B248447
theorem B166299 : Blo 163797 166299 := bstep (se 1 (by rfl) ⟨124724, by rfl⟩ : syracuseStep 166299 = 249449) B249449
theorem B166847 : Blo 163797 166847 := bstep (se 1 (by rfl) ⟨125135, by rfl⟩ : syracuseStep 166847 = 250271) B250271
theorem B167071 : Blo 163797 167071 := bstep (se 1 (by rfl) ⟨125303, by rfl⟩ : syracuseStep 167071 = 250607) B250607
theorem B400697 : Blo 163797 400697 := bstep (se 2 (by rfl) ⟨150261, by rfl⟩ : syracuseStep 400697 = 300523) B300523
theorem B5417441 : Blo 163797 5417441 := bstep (se 2 (by rfl) ⟨2031540, by rfl⟩ : syracuseStep 5417441 = 4063081) B4063081
theorem B3192247 : Blo 163797 3192247 := bstep (se 1 (by rfl) ⟨2394185, by rfl⟩ : syracuseStep 3192247 = 4788371) B4788371
theorem B833003 : Blo 163797 833003 := bstep (se 1 (by rfl) ⟨624752, by rfl⟩ : syracuseStep 833003 = 1249505) B1249505
theorem B1358059 : Blo 163797 1358059 := bstep (se 1 (by rfl) ⟨1018544, by rfl⟩ : syracuseStep 1358059 = 2037089) B2037089
theorem B836729 : Blo 163797 836729 := bstep (se 2 (by rfl) ⟨313773, by rfl⟩ : syracuseStep 836729 = 627547) B627547
theorem B443551 : Blo 163797 443551 := bstep (se 1 (by rfl) ⟨332663, by rfl⟩ : syracuseStep 443551 = 665327) B665327
theorem B1427017 : Blo 163797 1427017 := bstep (se 2 (by rfl) ⟨535131, by rfl⟩ : syracuseStep 1427017 = 1070263) B1070263
theorem B3100289 : Blo 163797 3100289 := bstep (se 2 (by rfl) ⟨1162608, by rfl⟩ : syracuseStep 3100289 = 2325217) B2325217
theorem B250751 : Blo 163797 250751 := bstep (se 1 (by rfl) ⟨188063, by rfl⟩ : syracuseStep 250751 = 376127) B376127
theorem B186367 : Blo 163797 186367 := bstep (se 1 (by rfl) ⟨139775, by rfl⟩ : syracuseStep 186367 = 279551) B279551
theorem B186619 : Blo 163797 186619 := bstep (se 1 (by rfl) ⟨139964, by rfl⟩ : syracuseStep 186619 = 279929) B279929
theorem B941503 : Blo 163797 941503 := bstep (se 1 (by rfl) ⟨706127, by rfl⟩ : syracuseStep 941503 = 1412255) B1412255
theorem B422455 : Blo 163797 422455 := bstep (se 1 (by rfl) ⟨316841, by rfl⟩ : syracuseStep 422455 = 633683) B633683
theorem B557819 : Blo 163797 557819 := bstep (se 1 (by rfl) ⟨418364, by rfl⟩ : syracuseStep 557819 = 836729) B836729
theorem B14550353 : Blo 163797 14550353 := bstep (se 2 (by rfl) ⟨5456382, by rfl⟩ : syracuseStep 14550353 = 10912765) B10912765
theorem B591401 : Blo 163797 591401 := bstep (se 2 (by rfl) ⟨221775, by rfl⟩ : syracuseStep 591401 = 443551) B443551
theorem B1902689 : Blo 163797 1902689 := bstep (se 2 (by rfl) ⟨713508, by rfl⟩ : syracuseStep 1902689 = 1427017) B1427017
theorem B167167 : Blo 163797 167167 := bstep (se 1 (by rfl) ⟨125375, by rfl⟩ : syracuseStep 167167 = 250751) B250751
theorem B267131 : Blo 163797 267131 := bstep (se 1 (by rfl) ⟨200348, by rfl⟩ : syracuseStep 267131 = 400697) B400697
theorem B563273 : Blo 163797 563273 := bstep (se 2 (by rfl) ⟨211227, by rfl⟩ : syracuseStep 563273 = 422455) B422455
theorem B3611627 : Blo 163797 3611627 := bstep (se 1 (by rfl) ⟨2708720, by rfl⟩ : syracuseStep 3611627 = 5417441) B5417441
theorem B1810745 : Blo 163797 1810745 := bstep (se 2 (by rfl) ⟨679029, by rfl⟩ : syracuseStep 1810745 = 1358059) B1358059
theorem B8267437 : Blo 163797 8267437 := bstep (se 3 (by rfl) ⟨1550144, by rfl⟩ : syracuseStep 8267437 = 3100289) B3100289
theorem B1255337 : Blo 163797 1255337 := bstep (se 2 (by rfl) ⟨470751, by rfl⟩ : syracuseStep 1255337 = 941503) B941503
theorem B248489 : Blo 163797 248489 := bstep (se 2 (by rfl) ⟨93183, by rfl⟩ : syracuseStep 248489 = 186367) B186367
theorem B248825 : Blo 163797 248825 := bstep (se 2 (by rfl) ⟨93309, by rfl⟩ : syracuseStep 248825 = 186619) B186619
theorem B2709245 : Blo 163797 2709245 := bstep (se 3 (by rfl) ⟨507983, by rfl⟩ : syracuseStep 2709245 = 1015967) B1015967
theorem B1529711 : Blo 163797 1529711 := bstep (se 1 (by rfl) ⟨1147283, by rfl⟩ : syracuseStep 1529711 = 2294567) B2294567
theorem B4256329 : Blo 163797 4256329 := bstep (se 2 (by rfl) ⟨1596123, by rfl⟩ : syracuseStep 4256329 = 3192247) B3192247
theorem B555335 : Blo 163797 555335 := bstep (se 1 (by rfl) ⟨416501, by rfl⟩ : syracuseStep 555335 = 833003) B833003
theorem B9700235 : Blo 163797 9700235 := bstep (se 1 (by rfl) ⟨7275176, by rfl⟩ : syracuseStep 9700235 = 14550353) B14550353
theorem B165659 : Blo 163797 165659 := bstep (se 1 (by rfl) ⟨124244, by rfl⟩ : syracuseStep 165659 = 248489) B248489
theorem B165883 : Blo 163797 165883 := bstep (se 1 (by rfl) ⟨124412, by rfl⟩ : syracuseStep 165883 = 248825) B248825
theorem B1019807 : Blo 163797 1019807 := bstep (se 1 (by rfl) ⟨764855, by rfl⟩ : syracuseStep 1019807 = 1529711) B1529711
theorem B1577069 : Blo 163797 1577069 := bstep (se 3 (by rfl) ⟨295700, by rfl⟩ : syracuseStep 1577069 = 591401) B591401
theorem B5675105 : Blo 163797 5675105 := bstep (se 2 (by rfl) ⟨2128164, by rfl⟩ : syracuseStep 5675105 = 4256329) B4256329
theorem B370223 : Blo 163797 370223 := bstep (se 1 (by rfl) ⟨277667, by rfl⟩ : syracuseStep 370223 = 555335) B555335
theorem B371879 : Blo 163797 371879 := bstep (se 1 (by rfl) ⟨278909, by rfl⟩ : syracuseStep 371879 = 557819) B557819
theorem B178087 : Blo 163797 178087 := bstep (se 1 (by rfl) ⟨133565, by rfl⟩ : syracuseStep 178087 = 267131) B267131
theorem B375515 : Blo 163797 375515 := bstep (se 1 (by rfl) ⟨281636, by rfl⟩ : syracuseStep 375515 = 563273) B563273
theorem B2407751 : Blo 163797 2407751 := bstep (se 1 (by rfl) ⟨1805813, by rfl⟩ : syracuseStep 2407751 = 3611627) B3611627
theorem B7224653 : Blo 163797 7224653 := bstep (se 3 (by rfl) ⟨1354622, by rfl⟩ : syracuseStep 7224653 = 2709245) B2709245
theorem B836891 : Blo 163797 836891 := bstep (se 1 (by rfl) ⟨627668, by rfl⟩ : syracuseStep 836891 = 1255337) B1255337
theorem B44092997 : Blo 163797 44092997 := bstep (se 4 (by rfl) ⟨4133718, by rfl⟩ : syracuseStep 44092997 = 8267437) B8267437
theorem B1268459 : Blo 163797 1268459 := bstep (se 1 (by rfl) ⟨951344, by rfl⟩ : syracuseStep 1268459 = 1902689) B1902689
theorem B1207163 : Blo 163797 1207163 := bstep (se 1 (by rfl) ⟨905372, by rfl⟩ : syracuseStep 1207163 = 1810745) B1810745
theorem B557927 : Blo 163797 557927 := bstep (se 1 (by rfl) ⟨418445, by rfl⟩ : syracuseStep 557927 = 836891) B836891
theorem B29395331 : Blo 163797 29395331 := bstep (se 1 (by rfl) ⟨22046498, by rfl⟩ : syracuseStep 29395331 = 44092997) B44092997
theorem B1051379 : Blo 163797 1051379 := bstep (se 1 (by rfl) ⟨788534, by rfl⟩ : syracuseStep 1051379 = 1577069) B1577069
theorem B237449 : Blo 163797 237449 := bstep (se 2 (by rfl) ⟨89043, by rfl⟩ : syracuseStep 237449 = 178087) B178087
theorem B6466823 : Blo 163797 6466823 := bstep (se 1 (by rfl) ⟨4850117, by rfl⟩ : syracuseStep 6466823 = 9700235) B9700235
theorem B246815 : Blo 163797 246815 := bstep (se 1 (by rfl) ⟨185111, by rfl⟩ : syracuseStep 246815 = 370223) B370223
theorem B804775 : Blo 163797 804775 := bstep (se 1 (by rfl) ⟨603581, by rfl⟩ : syracuseStep 804775 = 1207163) B1207163
theorem B247919 : Blo 163797 247919 := bstep (se 1 (by rfl) ⟨185939, by rfl⟩ : syracuseStep 247919 = 371879) B371879
theorem B250343 : Blo 163797 250343 := bstep (se 1 (by rfl) ⟨187757, by rfl⟩ : syracuseStep 250343 = 375515) B375515
theorem B679871 : Blo 163797 679871 := bstep (se 1 (by rfl) ⟨509903, by rfl⟩ : syracuseStep 679871 = 1019807) B1019807
theorem B845639 : Blo 163797 845639 := bstep (se 1 (by rfl) ⟨634229, by rfl⟩ : syracuseStep 845639 = 1268459) B1268459
theorem B15133613 : Blo 163797 15133613 := bstep (se 3 (by rfl) ⟨2837552, by rfl⟩ : syracuseStep 15133613 = 5675105) B5675105
theorem B1605167 : Blo 163797 1605167 := bstep (se 1 (by rfl) ⟨1203875, by rfl⟩ : syracuseStep 1605167 = 2407751) B2407751
theorem B4816435 : Blo 163797 4816435 := bstep (se 1 (by rfl) ⟨3612326, by rfl⟩ : syracuseStep 4816435 = 7224653) B7224653
theorem B164543 : Blo 163797 164543 := bstep (se 1 (by rfl) ⟨123407, by rfl⟩ : syracuseStep 164543 = 246815) B246815
theorem B165279 : Blo 163797 165279 := bstep (se 1 (by rfl) ⟨123959, by rfl⟩ : syracuseStep 165279 = 247919) B247919
theorem B19596887 : Blo 163797 19596887 := bstep (se 1 (by rfl) ⟨14697665, by rfl⟩ : syracuseStep 19596887 = 29395331) B29395331
theorem B166895 : Blo 163797 166895 := bstep (se 1 (by rfl) ⟨125171, by rfl⟩ : syracuseStep 166895 = 250343) B250343
theorem B563759 : Blo 163797 563759 := bstep (se 1 (by rfl) ⟨422819, by rfl⟩ : syracuseStep 563759 = 845639) B845639
theorem B633197 : Blo 163797 633197 := bstep (se 3 (by rfl) ⟨118724, by rfl⟩ : syracuseStep 633197 = 237449) B237449
theorem B1812989 : Blo 163797 1812989 := bstep (se 3 (by rfl) ⟨339935, by rfl⟩ : syracuseStep 1812989 = 679871) B679871
theorem B371951 : Blo 163797 371951 := bstep (se 1 (by rfl) ⟨278963, by rfl⟩ : syracuseStep 371951 = 557927) B557927
theorem B700919 : Blo 163797 700919 := bstep (se 1 (by rfl) ⟨525689, by rfl⟩ : syracuseStep 700919 = 1051379) B1051379
theorem B4311215 : Blo 163797 4311215 := bstep (se 1 (by rfl) ⟨3233411, by rfl⟩ : syracuseStep 4311215 = 6466823) B6466823
theorem B40356301 : Blo 163797 40356301 := bstep (se 3 (by rfl) ⟨7566806, by rfl⟩ : syracuseStep 40356301 = 15133613) B15133613
theorem B1070111 : Blo 163797 1070111 := bstep (se 1 (by rfl) ⟨802583, by rfl⟩ : syracuseStep 1070111 = 1605167) B1605167
theorem B1073033 : Blo 163797 1073033 := bstep (se 2 (by rfl) ⟨402387, by rfl⟩ : syracuseStep 1073033 = 804775) B804775
theorem B6421913 : Blo 163797 6421913 := bstep (se 2 (by rfl) ⟨2408217, by rfl⟩ : syracuseStep 6421913 = 4816435) B4816435
theorem B53808401 : Blo 163797 53808401 := bstep (se 2 (by rfl) ⟨20178150, by rfl⟩ : syracuseStep 53808401 = 40356301) B40356301
theorem B467279 : Blo 163797 467279 := bstep (se 1 (by rfl) ⟨350459, by rfl⟩ : syracuseStep 467279 = 700919) B700919
theorem B375839 : Blo 163797 375839 := bstep (se 1 (by rfl) ⟨281879, by rfl⟩ : syracuseStep 375839 = 563759) B563759
theorem B4834637 : Blo 163797 4834637 := bstep (se 3 (by rfl) ⟨906494, by rfl⟩ : syracuseStep 4834637 = 1812989) B1812989
theorem B247967 : Blo 163797 247967 := bstep (se 1 (by rfl) ⟨185975, by rfl⟩ : syracuseStep 247967 = 371951) B371951
theorem B4281275 : Blo 163797 4281275 := bstep (se 1 (by rfl) ⟨3210956, by rfl⟩ : syracuseStep 4281275 = 6421913) B6421913
theorem B13064591 : Blo 163797 13064591 := bstep (se 1 (by rfl) ⟨9798443, by rfl⟩ : syracuseStep 13064591 = 19596887) B19596887
theorem B2874143 : Blo 163797 2874143 := bstep (se 1 (by rfl) ⟨2155607, by rfl⟩ : syracuseStep 2874143 = 4311215) B4311215
theorem B713407 : Blo 163797 713407 := bstep (se 1 (by rfl) ⟨535055, by rfl⟩ : syracuseStep 713407 = 1070111) B1070111
theorem B715355 : Blo 163797 715355 := bstep (se 1 (by rfl) ⟨536516, by rfl⟩ : syracuseStep 715355 = 1073033) B1073033
theorem B422131 : Blo 163797 422131 := bstep (se 1 (by rfl) ⟨316598, by rfl⟩ : syracuseStep 422131 = 633197) B633197
theorem B951209 : Blo 163797 951209 := bstep (se 2 (by rfl) ⟨356703, by rfl⟩ : syracuseStep 951209 = 713407) B713407
theorem B165311 : Blo 163797 165311 := bstep (se 1 (by rfl) ⟨123983, by rfl⟩ : syracuseStep 165311 = 247967) B247967
theorem B562841 : Blo 163797 562841 := bstep (se 2 (by rfl) ⟨211065, by rfl⟩ : syracuseStep 562841 = 422131) B422131
theorem B3223091 : Blo 163797 3223091 := bstep (se 1 (by rfl) ⟨2417318, by rfl⟩ : syracuseStep 3223091 = 4834637) B4834637
theorem B11416733 : Blo 163797 11416733 := bstep (se 3 (by rfl) ⟨2140637, by rfl⟩ : syracuseStep 11416733 = 4281275) B4281275
theorem B1916095 : Blo 163797 1916095 := bstep (se 1 (by rfl) ⟨1437071, by rfl⟩ : syracuseStep 1916095 = 2874143) B2874143
theorem B311519 : Blo 163797 311519 := bstep (se 1 (by rfl) ⟨233639, by rfl⟩ : syracuseStep 311519 = 467279) B467279
theorem B476903 : Blo 163797 476903 := bstep (se 1 (by rfl) ⟨357677, by rfl⟩ : syracuseStep 476903 = 715355) B715355
theorem B250559 : Blo 163797 250559 := bstep (se 1 (by rfl) ⟨187919, by rfl⟩ : syracuseStep 250559 = 375839) B375839
theorem B35872267 : Blo 163797 35872267 := bstep (se 1 (by rfl) ⟨26904200, by rfl⟩ : syracuseStep 35872267 = 53808401) B53808401
theorem B8709727 : Blo 163797 8709727 := bstep (se 1 (by rfl) ⟨6532295, by rfl⟩ : syracuseStep 8709727 = 13064591) B13064591
theorem B167039 : Blo 163797 167039 := bstep (se 1 (by rfl) ⟨125279, by rfl⟩ : syracuseStep 167039 = 250559) B250559
theorem B7611155 : Blo 163797 7611155 := bstep (se 1 (by rfl) ⟨5708366, by rfl⟩ : syracuseStep 7611155 = 11416733) B11416733
theorem B207679 : Blo 163797 207679 := bstep (se 1 (by rfl) ⟨155759, by rfl⟩ : syracuseStep 207679 = 311519) B311519
theorem B634139 : Blo 163797 634139 := bstep (se 1 (by rfl) ⟨475604, by rfl⟩ : syracuseStep 634139 = 951209) B951209
theorem B11612969 : Blo 163797 11612969 := bstep (se 2 (by rfl) ⟨4354863, by rfl⟩ : syracuseStep 11612969 = 8709727) B8709727
theorem B375227 : Blo 163797 375227 := bstep (se 1 (by rfl) ⟨281420, by rfl⟩ : syracuseStep 375227 = 562841) B562841
theorem B2148727 : Blo 163797 2148727 := bstep (se 1 (by rfl) ⟨1611545, by rfl⟩ : syracuseStep 2148727 = 3223091) B3223091
theorem B47829689 : Blo 163797 47829689 := bstep (se 2 (by rfl) ⟨17936133, by rfl⟩ : syracuseStep 47829689 = 35872267) B35872267
theorem B317935 : Blo 163797 317935 := bstep (se 1 (by rfl) ⟨238451, by rfl⟩ : syracuseStep 317935 = 476903) B476903
theorem B2554793 : Blo 163797 2554793 := bstep (se 2 (by rfl) ⟨958047, by rfl⟩ : syracuseStep 2554793 = 1916095) B1916095
theorem B31886459 : Blo 163797 31886459 := bstep (se 1 (by rfl) ⟨23914844, by rfl⟩ : syracuseStep 31886459 = 47829689) B47829689
theorem B7741979 : Blo 163797 7741979 := bstep (se 1 (by rfl) ⟨5806484, by rfl⟩ : syracuseStep 7741979 = 11612969) B11612969
theorem B2864969 : Blo 163797 2864969 := bstep (se 2 (by rfl) ⟨1074363, by rfl⟩ : syracuseStep 2864969 = 2148727) B2148727
theorem B276905 : Blo 163797 276905 := bstep (se 2 (by rfl) ⟨103839, by rfl⟩ : syracuseStep 276905 = 207679) B207679
theorem B250151 : Blo 163797 250151 := bstep (se 1 (by rfl) ⟨187613, by rfl⟩ : syracuseStep 250151 = 375227) B375227
theorem B5074103 : Blo 163797 5074103 := bstep (se 1 (by rfl) ⟨3805577, by rfl⟩ : syracuseStep 5074103 = 7611155) B7611155
theorem B422759 : Blo 163797 422759 := bstep (se 1 (by rfl) ⟨317069, by rfl⟩ : syracuseStep 422759 = 634139) B634139
theorem B423913 : Blo 163797 423913 := bstep (se 2 (by rfl) ⟨158967, by rfl⟩ : syracuseStep 423913 = 317935) B317935
theorem B1703195 : Blo 163797 1703195 := bstep (se 1 (by rfl) ⟨1277396, by rfl⟩ : syracuseStep 1703195 = 2554793) B2554793
theorem B166767 : Blo 163797 166767 := bstep (se 1 (by rfl) ⟨125075, by rfl⟩ : syracuseStep 166767 = 250151) B250151
theorem B3382735 : Blo 163797 3382735 := bstep (se 1 (by rfl) ⟨2537051, by rfl⟩ : syracuseStep 3382735 = 5074103) B5074103
theorem B565217 : Blo 163797 565217 := bstep (se 2 (by rfl) ⟨211956, by rfl⟩ : syracuseStep 565217 = 423913) B423913
theorem B1909979 : Blo 163797 1909979 := bstep (se 1 (by rfl) ⟨1432484, by rfl⟩ : syracuseStep 1909979 = 2864969) B2864969
theorem B5161319 : Blo 163797 5161319 := bstep (se 1 (by rfl) ⟨3870989, by rfl⟩ : syracuseStep 5161319 = 7741979) B7741979
theorem B281839 : Blo 163797 281839 := bstep (se 1 (by rfl) ⟨211379, by rfl⟩ : syracuseStep 281839 = 422759) B422759
theorem B184603 : Blo 163797 184603 := bstep (se 1 (by rfl) ⟨138452, by rfl⟩ : syracuseStep 184603 = 276905) B276905
theorem B1135463 : Blo 163797 1135463 := bstep (se 1 (by rfl) ⟨851597, by rfl⟩ : syracuseStep 1135463 = 1703195) B1703195
theorem B21257639 : Blo 163797 21257639 := bstep (se 1 (by rfl) ⟨15943229, by rfl⟩ : syracuseStep 21257639 = 31886459) B31886459
theorem B3440879 : Blo 163797 3440879 := bstep (se 1 (by rfl) ⟨2580659, by rfl⟩ : syracuseStep 3440879 = 5161319) B5161319
theorem B3027901 : Blo 163797 3027901 := bstep (se 3 (by rfl) ⟨567731, by rfl⟩ : syracuseStep 3027901 = 1135463) B1135463
theorem B375785 : Blo 163797 375785 := bstep (se 2 (by rfl) ⟨140919, by rfl⟩ : syracuseStep 375785 = 281839) B281839
theorem B14171759 : Blo 163797 14171759 := bstep (se 1 (by rfl) ⟨10628819, by rfl⟩ : syracuseStep 14171759 = 21257639) B21257639
theorem B376811 : Blo 163797 376811 := bstep (se 1 (by rfl) ⟨282608, by rfl⟩ : syracuseStep 376811 = 565217) B565217
theorem B246137 : Blo 163797 246137 := bstep (se 2 (by rfl) ⟨92301, by rfl⟩ : syracuseStep 246137 = 184603) B184603
theorem B4510313 : Blo 163797 4510313 := bstep (se 2 (by rfl) ⟨1691367, by rfl⟩ : syracuseStep 4510313 = 3382735) B3382735
theorem B1273319 : Blo 163797 1273319 := bstep (se 1 (by rfl) ⟨954989, by rfl⟩ : syracuseStep 1273319 = 1909979) B1909979
theorem B2293919 : Blo 163797 2293919 := bstep (se 1 (by rfl) ⟨1720439, by rfl⟩ : syracuseStep 2293919 = 3440879) B3440879
theorem B164091 : Blo 163797 164091 := bstep (se 1 (by rfl) ⟨123068, by rfl⟩ : syracuseStep 164091 = 246137) B246137
theorem B4037201 : Blo 163797 4037201 := bstep (se 2 (by rfl) ⟨1513950, by rfl⟩ : syracuseStep 4037201 = 3027901) B3027901
theorem B9447839 : Blo 163797 9447839 := bstep (se 1 (by rfl) ⟨7085879, by rfl⟩ : syracuseStep 9447839 = 14171759) B14171759
theorem B250523 : Blo 163797 250523 := bstep (se 1 (by rfl) ⟨187892, by rfl⟩ : syracuseStep 250523 = 375785) B375785
theorem B251207 : Blo 163797 251207 := bstep (se 1 (by rfl) ⟨188405, by rfl⟩ : syracuseStep 251207 = 376811) B376811
theorem B3006875 : Blo 163797 3006875 := bstep (se 1 (by rfl) ⟨2255156, by rfl⟩ : syracuseStep 3006875 = 4510313) B4510313
theorem B848879 : Blo 163797 848879 := bstep (se 1 (by rfl) ⟨636659, by rfl⟩ : syracuseStep 848879 = 1273319) B1273319
theorem B167015 : Blo 163797 167015 := bstep (se 1 (by rfl) ⟨125261, by rfl⟩ : syracuseStep 167015 = 250523) B250523
theorem B167471 : Blo 163797 167471 := bstep (se 1 (by rfl) ⟨125603, by rfl⟩ : syracuseStep 167471 = 251207) B251207
theorem B2691467 : Blo 163797 2691467 := bstep (se 1 (by rfl) ⟨2018600, by rfl⟩ : syracuseStep 2691467 = 4037201) B4037201
theorem B2004583 : Blo 163797 2004583 := bstep (se 1 (by rfl) ⟨1503437, by rfl⟩ : syracuseStep 2004583 = 3006875) B3006875
theorem B6298559 : Blo 163797 6298559 := bstep (se 1 (by rfl) ⟨4723919, by rfl⟩ : syracuseStep 6298559 = 9447839) B9447839
theorem B565919 : Blo 163797 565919 := bstep (se 1 (by rfl) ⟨424439, by rfl⟩ : syracuseStep 565919 = 848879) B848879
theorem B1529279 : Blo 163797 1529279 := bstep (se 1 (by rfl) ⟨1146959, by rfl⟩ : syracuseStep 1529279 = 2293919) B2293919
theorem B1019519 : Blo 163797 1019519 := bstep (se 1 (by rfl) ⟨764639, by rfl⟩ : syracuseStep 1019519 = 1529279) B1529279
theorem B4199039 : Blo 163797 4199039 := bstep (se 1 (by rfl) ⟨3149279, by rfl⟩ : syracuseStep 4199039 = 6298559) B6298559
theorem B377279 : Blo 163797 377279 := bstep (se 1 (by rfl) ⟨282959, by rfl⟩ : syracuseStep 377279 = 565919) B565919
theorem B2672777 : Blo 163797 2672777 := bstep (se 2 (by rfl) ⟨1002291, by rfl⟩ : syracuseStep 2672777 = 2004583) B2004583
theorem B1794311 : Blo 163797 1794311 := bstep (se 1 (by rfl) ⟨1345733, by rfl⟩ : syracuseStep 1794311 = 2691467) B2691467
theorem B1781851 : Blo 163797 1781851 := bstep (se 1 (by rfl) ⟨1336388, by rfl⟩ : syracuseStep 1781851 = 2672777) B2672777
theorem B2799359 : Blo 163797 2799359 := bstep (se 1 (by rfl) ⟨2099519, by rfl⟩ : syracuseStep 2799359 = 4199039) B4199039
theorem B1196207 : Blo 163797 1196207 := bstep (se 1 (by rfl) ⟨897155, by rfl⟩ : syracuseStep 1196207 = 1794311) B1794311
theorem B251519 : Blo 163797 251519 := bstep (se 1 (by rfl) ⟨188639, by rfl⟩ : syracuseStep 251519 = 377279) B377279
theorem B679679 : Blo 163797 679679 := bstep (se 1 (by rfl) ⟨509759, by rfl⟩ : syracuseStep 679679 = 1019519) B1019519
theorem B167679 : Blo 163797 167679 := bstep (se 1 (by rfl) ⟨125759, by rfl⟩ : syracuseStep 167679 = 251519) B251519
theorem B797471 : Blo 163797 797471 := bstep (se 1 (by rfl) ⟨598103, by rfl⟩ : syracuseStep 797471 = 1196207) B1196207
theorem B2375801 : Blo 163797 2375801 := bstep (se 2 (by rfl) ⟨890925, by rfl⟩ : syracuseStep 2375801 = 1781851) B1781851
theorem B453119 : Blo 163797 453119 := bstep (se 1 (by rfl) ⟨339839, by rfl⟩ : syracuseStep 453119 = 679679) B679679
theorem B1866239 : Blo 163797 1866239 := bstep (se 1 (by rfl) ⟨1399679, by rfl⟩ : syracuseStep 1866239 = 2799359) B2799359
theorem B531647 : Blo 163797 531647 := bstep (se 1 (by rfl) ⟨398735, by rfl⟩ : syracuseStep 531647 = 797471) B797471
theorem B1583867 : Blo 163797 1583867 := bstep (se 1 (by rfl) ⟨1187900, by rfl⟩ : syracuseStep 1583867 = 2375801) B2375801
theorem B1208317 : Blo 163797 1208317 := bstep (se 3 (by rfl) ⟨226559, by rfl⟩ : syracuseStep 1208317 = 453119) B453119
theorem B1244159 : Blo 163797 1244159 := bstep (se 1 (by rfl) ⟨933119, by rfl⟩ : syracuseStep 1244159 = 1866239) B1866239
theorem B1611089 : Blo 163797 1611089 := bstep (se 2 (by rfl) ⟨604158, by rfl⟩ : syracuseStep 1611089 = 1208317) B1208317
theorem B1055911 : Blo 163797 1055911 := bstep (se 1 (by rfl) ⟨791933, by rfl⟩ : syracuseStep 1055911 = 1583867) B1583867
theorem B829439 : Blo 163797 829439 := bstep (se 1 (by rfl) ⟨622079, by rfl⟩ : syracuseStep 829439 = 1244159) B1244159
theorem B354431 : Blo 163797 354431 := bstep (se 1 (by rfl) ⟨265823, by rfl⟩ : syracuseStep 354431 = 531647) B531647
theorem B236287 : Blo 163797 236287 := bstep (se 1 (by rfl) ⟨177215, by rfl⟩ : syracuseStep 236287 = 354431) B354431
theorem B1074059 : Blo 163797 1074059 := bstep (se 1 (by rfl) ⟨805544, by rfl⟩ : syracuseStep 1074059 = 1611089) B1611089
theorem B552959 : Blo 163797 552959 := bstep (se 1 (by rfl) ⟨414719, by rfl⟩ : syracuseStep 552959 = 829439) B829439
theorem B1407881 : Blo 163797 1407881 := bstep (se 2 (by rfl) ⟨527955, by rfl⟩ : syracuseStep 1407881 = 1055911) B1055911
theorem B368639 : Blo 163797 368639 := bstep (se 1 (by rfl) ⟨276479, by rfl⟩ : syracuseStep 368639 = 552959) B552959
theorem B1260197 : Blo 163797 1260197 := bstep (se 4 (by rfl) ⟨118143, by rfl⟩ : syracuseStep 1260197 = 236287) B236287
theorem B938587 : Blo 163797 938587 := bstep (se 1 (by rfl) ⟨703940, by rfl⟩ : syracuseStep 938587 = 1407881) B1407881
theorem B716039 : Blo 163797 716039 := bstep (se 1 (by rfl) ⟨537029, by rfl⟩ : syracuseStep 716039 = 1074059) B1074059
theorem B1251449 : Blo 163797 1251449 := bstep (se 2 (by rfl) ⟨469293, by rfl⟩ : syracuseStep 1251449 = 938587) B938587
theorem B245759 : Blo 163797 245759 := bstep (se 1 (by rfl) ⟨184319, by rfl⟩ : syracuseStep 245759 = 368639) B368639
theorem B477359 : Blo 163797 477359 := bstep (se 1 (by rfl) ⟨358019, by rfl⟩ : syracuseStep 477359 = 716039) B716039
theorem B840131 : Blo 163797 840131 := bstep (se 1 (by rfl) ⟨630098, by rfl⟩ : syracuseStep 840131 = 1260197) B1260197
theorem B560087 : Blo 163797 560087 := bstep (se 1 (by rfl) ⟨420065, by rfl⟩ : syracuseStep 560087 = 840131) B840131
theorem B834299 : Blo 163797 834299 := bstep (se 1 (by rfl) ⟨625724, by rfl⟩ : syracuseStep 834299 = 1251449) B1251449
theorem B318239 : Blo 163797 318239 := bstep (se 1 (by rfl) ⟨238679, by rfl⟩ : syracuseStep 318239 = 477359) B477359
theorem B163839 : Blo 163797 163839 := bstep (se 1 (by rfl) ⟨122879, by rfl⟩ : syracuseStep 163839 = 245759) B245759
theorem B373391 : Blo 163797 373391 := bstep (se 1 (by rfl) ⟨280043, by rfl⟩ : syracuseStep 373391 = 560087) B560087
theorem B212159 : Blo 163797 212159 := bstep (se 1 (by rfl) ⟨159119, by rfl⟩ : syracuseStep 212159 = 318239) B318239
theorem B556199 : Blo 163797 556199 := bstep (se 1 (by rfl) ⟨417149, by rfl⟩ : syracuseStep 556199 = 834299) B834299
theorem B565757 : Blo 163797 565757 := bstep (se 3 (by rfl) ⟨106079, by rfl⟩ : syracuseStep 565757 = 212159) B212159
theorem B370799 : Blo 163797 370799 := bstep (se 1 (by rfl) ⟨278099, by rfl⟩ : syracuseStep 370799 = 556199) B556199
theorem B248927 : Blo 163797 248927 := bstep (se 1 (by rfl) ⟨186695, by rfl⟩ : syracuseStep 248927 = 373391) B373391
theorem B165951 : Blo 163797 165951 := bstep (se 1 (by rfl) ⟨124463, by rfl⟩ : syracuseStep 165951 = 248927) B248927
theorem B377171 : Blo 163797 377171 := bstep (se 1 (by rfl) ⟨282878, by rfl⟩ : syracuseStep 377171 = 565757) B565757
theorem B247199 : Blo 163797 247199 := bstep (se 1 (by rfl) ⟨185399, by rfl⟩ : syracuseStep 247199 = 370799) B370799
theorem B164799 : Blo 163797 164799 := bstep (se 1 (by rfl) ⟨123599, by rfl⟩ : syracuseStep 164799 = 247199) B247199
theorem B251447 : Blo 163797 251447 := bstep (se 1 (by rfl) ⟨188585, by rfl⟩ : syracuseStep 251447 = 377171) B377171
theorem B167631 : Blo 163797 167631 := bstep (se 1 (by rfl) ⟨125723, by rfl⟩ : syracuseStep 167631 = 251447) B251447

theorem C0 (j : ℕ) (h1 : 40949 ≤ j) (h2 : j ≤ 41648) : Blo 163797 (4 * j + 3) := by
  interval_cases j
  · exact B163799
  · exact B163803
  · exact B163807
  · exact B163811
  · exact B163815
  · exact B163819
  · exact B163823
  · exact B163827
  · exact B163831
  · exact B163835
  · exact B163839
  · exact B163843
  · exact B163847
  · exact B163851
  · exact B163855
  · exact B163859
  · exact B163863
  · exact B163867
  · exact B163871
  · exact B163875
  · exact B163879
  · exact B163883
  · exact B163887
  · exact B163891
  · exact B163895
  · exact B163899
  · exact B163903
  · exact B163907
  · exact B163911
  · exact B163915
  · exact B163919
  · exact B163923
  · exact B163927
  · exact B163931
  · exact B163935
  · exact B163939
  · exact B163943
  · exact B163947
  · exact B163951
  · exact B163955
  · exact B163959
  · exact B163963
  · exact B163967
  · exact B163971
  · exact B163975
  · exact B163979
  · exact B163983
  · exact B163987
  · exact B163991
  · exact B163995
  · exact B163999
  · exact B164003
  · exact B164007
  · exact B164011
  · exact B164015
  · exact B164019
  · exact B164023
  · exact B164027
  · exact B164031
  · exact B164035
  · exact B164039
  · exact B164043
  · exact B164047
  · exact B164051
  · exact B164055
  · exact B164059
  · exact B164063
  · exact B164067
  · exact B164071
  · exact B164075
  · exact B164079
  · exact B164083
  · exact B164087
  · exact B164091
  · exact B164095
  · exact B164099
  · exact B164103
  · exact B164107
  · exact B164111
  · exact B164115
  · exact B164119
  · exact B164123
  · exact B164127
  · exact B164131
  · exact B164135
  · exact B164139
  · exact B164143
  · exact B164147
  · exact B164151
  · exact B164155
  · exact B164159
  · exact B164163
  · exact B164167
  · exact B164171
  · exact B164175
  · exact B164179
  · exact B164183
  · exact B164187
  · exact B164191
  · exact B164195
  · exact B164199
  · exact B164203
  · exact B164207
  · exact B164211
  · exact B164215
  · exact B164219
  · exact B164223
  · exact B164227
  · exact B164231
  · exact B164235
  · exact B164239
  · exact B164243
  · exact B164247
  · exact B164251
  · exact B164255
  · exact B164259
  · exact B164263
  · exact B164267
  · exact B164271
  · exact B164275
  · exact B164279
  · exact B164283
  · exact B164287
  · exact B164291
  · exact B164295
  · exact B164299
  · exact B164303
  · exact B164307
  · exact B164311
  · exact B164315
  · exact B164319
  · exact B164323
  · exact B164327
  · exact B164331
  · exact B164335
  · exact B164339
  · exact B164343
  · exact B164347
  · exact B164351
  · exact B164355
  · exact B164359
  · exact B164363
  · exact B164367
  · exact B164371
  · exact B164375
  · exact B164379
  · exact B164383
  · exact B164387
  · exact B164391
  · exact B164395
  · exact B164399
  · exact B164403
  · exact B164407
  · exact B164411
  · exact B164415
  · exact B164419
  · exact B164423
  · exact B164427
  · exact B164431
  · exact B164435
  · exact B164439
  · exact B164443
  · exact B164447
  · exact B164451
  · exact B164455
  · exact B164459
  · exact B164463
  · exact B164467
  · exact B164471
  · exact B164475
  · exact B164479
  · exact B164483
  · exact B164487
  · exact B164491
  · exact B164495
  · exact B164499
  · exact B164503
  · exact B164507
  · exact B164511
  · exact B164515
  · exact B164519
  · exact B164523
  · exact B164527
  · exact B164531
  · exact B164535
  · exact B164539
  · exact B164543
  · exact B164547
  · exact B164551
  · exact B164555
  · exact B164559
  · exact B164563
  · exact B164567
  · exact B164571
  · exact B164575
  · exact B164579
  · exact B164583
  · exact B164587
  · exact B164591
  · exact B164595
  · exact B164599
  · exact B164603
  · exact B164607
  · exact B164611
  · exact B164615
  · exact B164619
  · exact B164623
  · exact B164627
  · exact B164631
  · exact B164635
  · exact B164639
  · exact B164643
  · exact B164647
  · exact B164651
  · exact B164655
  · exact B164659
  · exact B164663
  · exact B164667
  · exact B164671
  · exact B164675
  · exact B164679
  · exact B164683
  · exact B164687
  · exact B164691
  · exact B164695
  · exact B164699
  · exact B164703
  · exact B164707
  · exact B164711
  · exact B164715
  · exact B164719
  · exact B164723
  · exact B164727
  · exact B164731
  · exact B164735
  · exact B164739
  · exact B164743
  · exact B164747
  · exact B164751
  · exact B164755
  · exact B164759
  · exact B164763
  · exact B164767
  · exact B164771
  · exact B164775
  · exact B164779
  · exact B164783
  · exact B164787
  · exact B164791
  · exact B164795
  · exact B164799
  · exact B164803
  · exact B164807
  · exact B164811
  · exact B164815
  · exact B164819
  · exact B164823
  · exact B164827
  · exact B164831
  · exact B164835
  · exact B164839
  · exact B164843
  · exact B164847
  · exact B164851
  · exact B164855
  · exact B164859
  · exact B164863
  · exact B164867
  · exact B164871
  · exact B164875
  · exact B164879
  · exact B164883
  · exact B164887
  · exact B164891
  · exact B164895
  · exact B164899
  · exact B164903
  · exact B164907
  · exact B164911
  · exact B164915
  · exact B164919
  · exact B164923
  · exact B164927
  · exact B164931
  · exact B164935
  · exact B164939
  · exact B164943
  · exact B164947
  · exact B164951
  · exact B164955
  · exact B164959
  · exact B164963
  · exact B164967
  · exact B164971
  · exact B164975
  · exact B164979
  · exact B164983
  · exact B164987
  · exact B164991
  · exact B164995
  · exact B164999
  · exact B165003
  · exact B165007
  · exact B165011
  · exact B165015
  · exact B165019
  · exact B165023
  · exact B165027
  · exact B165031
  · exact B165035
  · exact B165039
  · exact B165043
  · exact B165047
  · exact B165051
  · exact B165055
  · exact B165059
  · exact B165063
  · exact B165067
  · exact B165071
  · exact B165075
  · exact B165079
  · exact B165083
  · exact B165087
  · exact B165091
  · exact B165095
  · exact B165099
  · exact B165103
  · exact B165107
  · exact B165111
  · exact B165115
  · exact B165119
  · exact B165123
  · exact B165127
  · exact B165131
  · exact B165135
  · exact B165139
  · exact B165143
  · exact B165147
  · exact B165151
  · exact B165155
  · exact B165159
  · exact B165163
  · exact B165167
  · exact B165171
  · exact B165175
  · exact B165179
  · exact B165183
  · exact B165187
  · exact B165191
  · exact B165195
  · exact B165199
  · exact B165203
  · exact B165207
  · exact B165211
  · exact B165215
  · exact B165219
  · exact B165223
  · exact B165227
  · exact B165231
  · exact B165235
  · exact B165239
  · exact B165243
  · exact B165247
  · exact B165251
  · exact B165255
  · exact B165259
  · exact B165263
  · exact B165267
  · exact B165271
  · exact B165275
  · exact B165279
  · exact B165283
  · exact B165287
  · exact B165291
  · exact B165295
  · exact B165299
  · exact B165303
  · exact B165307
  · exact B165311
  · exact B165315
  · exact B165319
  · exact B165323
  · exact B165327
  · exact B165331
  · exact B165335
  · exact B165339
  · exact B165343
  · exact B165347
  · exact B165351
  · exact B165355
  · exact B165359
  · exact B165363
  · exact B165367
  · exact B165371
  · exact B165375
  · exact B165379
  · exact B165383
  · exact B165387
  · exact B165391
  · exact B165395
  · exact B165399
  · exact B165403
  · exact B165407
  · exact B165411
  · exact B165415
  · exact B165419
  · exact B165423
  · exact B165427
  · exact B165431
  · exact B165435
  · exact B165439
  · exact B165443
  · exact B165447
  · exact B165451
  · exact B165455
  · exact B165459
  · exact B165463
  · exact B165467
  · exact B165471
  · exact B165475
  · exact B165479
  · exact B165483
  · exact B165487
  · exact B165491
  · exact B165495
  · exact B165499
  · exact B165503
  · exact B165507
  · exact B165511
  · exact B165515
  · exact B165519
  · exact B165523
  · exact B165527
  · exact B165531
  · exact B165535
  · exact B165539
  · exact B165543
  · exact B165547
  · exact B165551
  · exact B165555
  · exact B165559
  · exact B165563
  · exact B165567
  · exact B165571
  · exact B165575
  · exact B165579
  · exact B165583
  · exact B165587
  · exact B165591
  · exact B165595
  · exact B165599
  · exact B165603
  · exact B165607
  · exact B165611
  · exact B165615
  · exact B165619
  · exact B165623
  · exact B165627
  · exact B165631
  · exact B165635
  · exact B165639
  · exact B165643
  · exact B165647
  · exact B165651
  · exact B165655
  · exact B165659
  · exact B165663
  · exact B165667
  · exact B165671
  · exact B165675
  · exact B165679
  · exact B165683
  · exact B165687
  · exact B165691
  · exact B165695
  · exact B165699
  · exact B165703
  · exact B165707
  · exact B165711
  · exact B165715
  · exact B165719
  · exact B165723
  · exact B165727
  · exact B165731
  · exact B165735
  · exact B165739
  · exact B165743
  · exact B165747
  · exact B165751
  · exact B165755
  · exact B165759
  · exact B165763
  · exact B165767
  · exact B165771
  · exact B165775
  · exact B165779
  · exact B165783
  · exact B165787
  · exact B165791
  · exact B165795
  · exact B165799
  · exact B165803
  · exact B165807
  · exact B165811
  · exact B165815
  · exact B165819
  · exact B165823
  · exact B165827
  · exact B165831
  · exact B165835
  · exact B165839
  · exact B165843
  · exact B165847
  · exact B165851
  · exact B165855
  · exact B165859
  · exact B165863
  · exact B165867
  · exact B165871
  · exact B165875
  · exact B165879
  · exact B165883
  · exact B165887
  · exact B165891
  · exact B165895
  · exact B165899
  · exact B165903
  · exact B165907
  · exact B165911
  · exact B165915
  · exact B165919
  · exact B165923
  · exact B165927
  · exact B165931
  · exact B165935
  · exact B165939
  · exact B165943
  · exact B165947
  · exact B165951
  · exact B165955
  · exact B165959
  · exact B165963
  · exact B165967
  · exact B165971
  · exact B165975
  · exact B165979
  · exact B165983
  · exact B165987
  · exact B165991
  · exact B165995
  · exact B165999
  · exact B166003
  · exact B166007
  · exact B166011
  · exact B166015
  · exact B166019
  · exact B166023
  · exact B166027
  · exact B166031
  · exact B166035
  · exact B166039
  · exact B166043
  · exact B166047
  · exact B166051
  · exact B166055
  · exact B166059
  · exact B166063
  · exact B166067
  · exact B166071
  · exact B166075
  · exact B166079
  · exact B166083
  · exact B166087
  · exact B166091
  · exact B166095
  · exact B166099
  · exact B166103
  · exact B166107
  · exact B166111
  · exact B166115
  · exact B166119
  · exact B166123
  · exact B166127
  · exact B166131
  · exact B166135
  · exact B166139
  · exact B166143
  · exact B166147
  · exact B166151
  · exact B166155
  · exact B166159
  · exact B166163
  · exact B166167
  · exact B166171
  · exact B166175
  · exact B166179
  · exact B166183
  · exact B166187
  · exact B166191
  · exact B166195
  · exact B166199
  · exact B166203
  · exact B166207
  · exact B166211
  · exact B166215
  · exact B166219
  · exact B166223
  · exact B166227
  · exact B166231
  · exact B166235
  · exact B166239
  · exact B166243
  · exact B166247
  · exact B166251
  · exact B166255
  · exact B166259
  · exact B166263
  · exact B166267
  · exact B166271
  · exact B166275
  · exact B166279
  · exact B166283
  · exact B166287
  · exact B166291
  · exact B166295
  · exact B166299
  · exact B166303
  · exact B166307
  · exact B166311
  · exact B166315
  · exact B166319
  · exact B166323
  · exact B166327
  · exact B166331
  · exact B166335
  · exact B166339
  · exact B166343
  · exact B166347
  · exact B166351
  · exact B166355
  · exact B166359
  · exact B166363
  · exact B166367
  · exact B166371
  · exact B166375
  · exact B166379
  · exact B166383
  · exact B166387
  · exact B166391
  · exact B166395
  · exact B166399
  · exact B166403
  · exact B166407
  · exact B166411
  · exact B166415
  · exact B166419
  · exact B166423
  · exact B166427
  · exact B166431
  · exact B166435
  · exact B166439
  · exact B166443
  · exact B166447
  · exact B166451
  · exact B166455
  · exact B166459
  · exact B166463
  · exact B166467
  · exact B166471
  · exact B166475
  · exact B166479
  · exact B166483
  · exact B166487
  · exact B166491
  · exact B166495
  · exact B166499
  · exact B166503
  · exact B166507
  · exact B166511
  · exact B166515
  · exact B166519
  · exact B166523
  · exact B166527
  · exact B166531
  · exact B166535
  · exact B166539
  · exact B166543
  · exact B166547
  · exact B166551
  · exact B166555
  · exact B166559
  · exact B166563
  · exact B166567
  · exact B166571
  · exact B166575
  · exact B166579
  · exact B166583
  · exact B166587
  · exact B166591
  · exact B166595

theorem C1 (j : ℕ) (h1 : 41649 ≤ j) (h2 : j ≤ 41948) : Blo 163797 (4 * j + 3) := by
  interval_cases j
  · exact B166599
  · exact B166603
  · exact B166607
  · exact B166611
  · exact B166615
  · exact B166619
  · exact B166623
  · exact B166627
  · exact B166631
  · exact B166635
  · exact B166639
  · exact B166643
  · exact B166647
  · exact B166651
  · exact B166655
  · exact B166659
  · exact B166663
  · exact B166667
  · exact B166671
  · exact B166675
  · exact B166679
  · exact B166683
  · exact B166687
  · exact B166691
  · exact B166695
  · exact B166699
  · exact B166703
  · exact B166707
  · exact B166711
  · exact B166715
  · exact B166719
  · exact B166723
  · exact B166727
  · exact B166731
  · exact B166735
  · exact B166739
  · exact B166743
  · exact B166747
  · exact B166751
  · exact B166755
  · exact B166759
  · exact B166763
  · exact B166767
  · exact B166771
  · exact B166775
  · exact B166779
  · exact B166783
  · exact B166787
  · exact B166791
  · exact B166795
  · exact B166799
  · exact B166803
  · exact B166807
  · exact B166811
  · exact B166815
  · exact B166819
  · exact B166823
  · exact B166827
  · exact B166831
  · exact B166835
  · exact B166839
  · exact B166843
  · exact B166847
  · exact B166851
  · exact B166855
  · exact B166859
  · exact B166863
  · exact B166867
  · exact B166871
  · exact B166875
  · exact B166879
  · exact B166883
  · exact B166887
  · exact B166891
  · exact B166895
  · exact B166899
  · exact B166903
  · exact B166907
  · exact B166911
  · exact B166915
  · exact B166919
  · exact B166923
  · exact B166927
  · exact B166931
  · exact B166935
  · exact B166939
  · exact B166943
  · exact B166947
  · exact B166951
  · exact B166955
  · exact B166959
  · exact B166963
  · exact B166967
  · exact B166971
  · exact B166975
  · exact B166979
  · exact B166983
  · exact B166987
  · exact B166991
  · exact B166995
  · exact B166999
  · exact B167003
  · exact B167007
  · exact B167011
  · exact B167015
  · exact B167019
  · exact B167023
  · exact B167027
  · exact B167031
  · exact B167035
  · exact B167039
  · exact B167043
  · exact B167047
  · exact B167051
  · exact B167055
  · exact B167059
  · exact B167063
  · exact B167067
  · exact B167071
  · exact B167075
  · exact B167079
  · exact B167083
  · exact B167087
  · exact B167091
  · exact B167095
  · exact B167099
  · exact B167103
  · exact B167107
  · exact B167111
  · exact B167115
  · exact B167119
  · exact B167123
  · exact B167127
  · exact B167131
  · exact B167135
  · exact B167139
  · exact B167143
  · exact B167147
  · exact B167151
  · exact B167155
  · exact B167159
  · exact B167163
  · exact B167167
  · exact B167171
  · exact B167175
  · exact B167179
  · exact B167183
  · exact B167187
  · exact B167191
  · exact B167195
  · exact B167199
  · exact B167203
  · exact B167207
  · exact B167211
  · exact B167215
  · exact B167219
  · exact B167223
  · exact B167227
  · exact B167231
  · exact B167235
  · exact B167239
  · exact B167243
  · exact B167247
  · exact B167251
  · exact B167255
  · exact B167259
  · exact B167263
  · exact B167267
  · exact B167271
  · exact B167275
  · exact B167279
  · exact B167283
  · exact B167287
  · exact B167291
  · exact B167295
  · exact B167299
  · exact B167303
  · exact B167307
  · exact B167311
  · exact B167315
  · exact B167319
  · exact B167323
  · exact B167327
  · exact B167331
  · exact B167335
  · exact B167339
  · exact B167343
  · exact B167347
  · exact B167351
  · exact B167355
  · exact B167359
  · exact B167363
  · exact B167367
  · exact B167371
  · exact B167375
  · exact B167379
  · exact B167383
  · exact B167387
  · exact B167391
  · exact B167395
  · exact B167399
  · exact B167403
  · exact B167407
  · exact B167411
  · exact B167415
  · exact B167419
  · exact B167423
  · exact B167427
  · exact B167431
  · exact B167435
  · exact B167439
  · exact B167443
  · exact B167447
  · exact B167451
  · exact B167455
  · exact B167459
  · exact B167463
  · exact B167467
  · exact B167471
  · exact B167475
  · exact B167479
  · exact B167483
  · exact B167487
  · exact B167491
  · exact B167495
  · exact B167499
  · exact B167503
  · exact B167507
  · exact B167511
  · exact B167515
  · exact B167519
  · exact B167523
  · exact B167527
  · exact B167531
  · exact B167535
  · exact B167539
  · exact B167543
  · exact B167547
  · exact B167551
  · exact B167555
  · exact B167559
  · exact B167563
  · exact B167567
  · exact B167571
  · exact B167575
  · exact B167579
  · exact B167583
  · exact B167587
  · exact B167591
  · exact B167595
  · exact B167599
  · exact B167603
  · exact B167607
  · exact B167611
  · exact B167615
  · exact B167619
  · exact B167623
  · exact B167627
  · exact B167631
  · exact B167635
  · exact B167639
  · exact B167643
  · exact B167647
  · exact B167651
  · exact B167655
  · exact B167659
  · exact B167663
  · exact B167667
  · exact B167671
  · exact B167675
  · exact B167679
  · exact B167683
  · exact B167687
  · exact B167691
  · exact B167695
  · exact B167699
  · exact B167703
  · exact B167707
  · exact B167711
  · exact B167715
  · exact B167719
  · exact B167723
  · exact B167727
  · exact B167731
  · exact B167735
  · exact B167739
  · exact B167743
  · exact B167747
  · exact B167751
  · exact B167755
  · exact B167759
  · exact B167763
  · exact B167767
  · exact B167771
  · exact B167775
  · exact B167779
  · exact B167783
  · exact B167787
  · exact B167791
  · exact B167795

theorem solution (m : ℕ) (hlo : 163797 ≤ m) (hhi : m ≤ 167797) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 40949 ≤ j := by omega
    have hj2 : j ≤ 41948 := by omega
    have hb : Blo 163797 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 41649 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
