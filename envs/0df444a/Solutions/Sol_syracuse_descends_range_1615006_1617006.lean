-- Prove2me | solution 1 for syracuse_descends_range_1615006_1617006
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:12:31.183792+00:00
-- url     : https://prove2.me/submissions/6f19da67-d7f2-4d34-9a50-cd8dce313c28

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


theorem B1818625 : Blo 1615006 1818625 := bbase (se 2 (by rfl) ⟨681984, by rfl⟩ : syracuseStep 1818625 = 1363969) (by norm_num)
theorem B2424845 : Blo 1615006 2424845 := bbase (se 3 (by rfl) ⟨454658, by rfl⟩ : syracuseStep 2424845 = 909317) (by norm_num)
theorem B3637277 : Blo 1615006 3637277 := bbase (se 3 (by rfl) ⟨681989, by rfl⟩ : syracuseStep 3637277 = 1363979) (by norm_num)
theorem B2727965 : Blo 1615006 2727965 := bbase (se 3 (by rfl) ⟨511493, by rfl⟩ : syracuseStep 2727965 = 1022987) (by norm_num)
theorem B2424869 : Blo 1615006 2424869 := bbase (se 4 (by rfl) ⟨227331, by rfl⟩ : syracuseStep 2424869 = 454663) (by norm_num)
theorem B1818661 : Blo 1615006 1818661 := bbase (se 4 (by rfl) ⟨170499, by rfl⟩ : syracuseStep 1818661 = 340999) (by norm_num)
theorem B2424893 : Blo 1615006 2424893 := bbase (se 3 (by rfl) ⟨454667, by rfl⟩ : syracuseStep 2424893 = 909335) (by norm_num)
theorem B1818697 : Blo 1615006 1818697 := bbase (se 2 (by rfl) ⟨682011, by rfl⟩ : syracuseStep 1818697 = 1364023) (by norm_num)
theorem B34938965 : Blo 1615006 34938965 := bbase (se 8 (by rfl) ⟨204720, by rfl⟩ : syracuseStep 34938965 = 409441) (by norm_num)
theorem B29491285 : Blo 1615006 29491285 := bbase (se 8 (by rfl) ⟨172800, by rfl⟩ : syracuseStep 29491285 = 345601) (by norm_num)
theorem B2424917 : Blo 1615006 2424917 := bbase (se 8 (by rfl) ⟨14208, by rfl⟩ : syracuseStep 2424917 = 28417) (by norm_num)
theorem B3637349 : Blo 1615006 3637349 := bbase (se 4 (by rfl) ⟨341001, by rfl⟩ : syracuseStep 3637349 = 682003) (by norm_num)
theorem B2424941 : Blo 1615006 2424941 := bbase (se 3 (by rfl) ⟨454676, by rfl⟩ : syracuseStep 2424941 = 909353) (by norm_num)
theorem B1818733 : Blo 1615006 1818733 := bbase (se 3 (by rfl) ⟨341012, by rfl⟩ : syracuseStep 1818733 = 682025) (by norm_num)
theorem B2424965 : Blo 1615006 2424965 := bbase (se 4 (by rfl) ⟨227340, by rfl⟩ : syracuseStep 2424965 = 454681) (by norm_num)
theorem B1818769 : Blo 1615006 1818769 := bbase (se 2 (by rfl) ⟨682038, by rfl⟩ : syracuseStep 1818769 = 1364077) (by norm_num)
theorem B2728093 : Blo 1615006 2728093 := bbase (se 3 (by rfl) ⟨511517, by rfl⟩ : syracuseStep 2728093 = 1023035) (by norm_num)
theorem B2424989 : Blo 1615006 2424989 := bbase (se 3 (by rfl) ⟨454685, by rfl⟩ : syracuseStep 2424989 = 909371) (by norm_num)
theorem B3637421 : Blo 1615006 3637421 := bbase (se 3 (by rfl) ⟨682016, by rfl⟩ : syracuseStep 3637421 = 1364033) (by norm_num)
theorem B2425013 : Blo 1615006 2425013 := bbase (se 5 (by rfl) ⟨113672, by rfl⟩ : syracuseStep 2425013 = 227345) (by norm_num)
theorem B1818805 : Blo 1615006 1818805 := bbase (se 5 (by rfl) ⟨85256, by rfl⟩ : syracuseStep 1818805 = 170513) (by norm_num)
theorem B2425037 : Blo 1615006 2425037 := bbase (se 3 (by rfl) ⟨454694, by rfl⟩ : syracuseStep 2425037 = 909389) (by norm_num)
theorem B1818841 : Blo 1615006 1818841 := bbase (se 2 (by rfl) ⟨682065, by rfl⟩ : syracuseStep 1818841 = 1364131) (by norm_num)
theorem B4088029 : Blo 1615006 4088029 := bbase (se 3 (by rfl) ⟨766505, by rfl⟩ : syracuseStep 4088029 = 1533011) (by norm_num)
theorem B2425061 : Blo 1615006 2425061 := bbase (se 4 (by rfl) ⟨227349, by rfl⟩ : syracuseStep 2425061 = 454699) (by norm_num)
theorem B3637493 : Blo 1615006 3637493 := bbase (se 5 (by rfl) ⟨170507, by rfl⟩ : syracuseStep 3637493 = 341015) (by norm_num)
theorem B2728181 : Blo 1615006 2728181 := bbase (se 5 (by rfl) ⟨127883, by rfl⟩ : syracuseStep 2728181 = 255767) (by norm_num)
theorem B2425085 : Blo 1615006 2425085 := bbase (se 3 (by rfl) ⟨454703, by rfl⟩ : syracuseStep 2425085 = 909407) (by norm_num)
theorem B1818877 : Blo 1615006 1818877 := bbase (se 3 (by rfl) ⟨341039, by rfl⟩ : syracuseStep 1818877 = 682079) (by norm_num)
theorem B13803797 : Blo 1615006 13803797 := bbase (se 6 (by rfl) ⟨323526, by rfl⟩ : syracuseStep 13803797 = 647053) (by norm_num)
theorem B2425109 : Blo 1615006 2425109 := bbase (se 6 (by rfl) ⟨56838, by rfl⟩ : syracuseStep 2425109 = 113677) (by norm_num)
theorem B1818913 : Blo 1615006 1818913 := bbase (se 2 (by rfl) ⟨682092, by rfl⟩ : syracuseStep 1818913 = 1364185) (by norm_num)
theorem B2425133 : Blo 1615006 2425133 := bbase (se 3 (by rfl) ⟨454712, by rfl⟩ : syracuseStep 2425133 = 909425) (by norm_num)
theorem B2588981 : Blo 1615006 2588981 := bbase (se 5 (by rfl) ⟨121358, by rfl⟩ : syracuseStep 2588981 = 242717) (by norm_num)
theorem B3637565 : Blo 1615006 3637565 := bbase (se 3 (by rfl) ⟨682043, by rfl⟩ : syracuseStep 3637565 = 1364087) (by norm_num)
theorem B2425157 : Blo 1615006 2425157 := bbase (se 4 (by rfl) ⟨227358, by rfl⟩ : syracuseStep 2425157 = 454717) (by norm_num)
theorem B1818949 : Blo 1615006 1818949 := bbase (se 4 (by rfl) ⟨170526, by rfl⟩ : syracuseStep 1818949 = 341053) (by norm_num)
theorem B4088141 : Blo 1615006 4088141 := bbase (se 3 (by rfl) ⟨766526, by rfl⟩ : syracuseStep 4088141 = 1533053) (by norm_num)
theorem B2302285 : Blo 1615006 2302285 := bbase (se 3 (by rfl) ⟨431678, by rfl⟩ : syracuseStep 2302285 = 863357) (by norm_num)
theorem B5456213 : Blo 1615006 5456213 := bbase (se 10 (by rfl) ⟨7992, by rfl⟩ : syracuseStep 5456213 = 15985) (by norm_num)
theorem B2425181 : Blo 1615006 2425181 := bbase (se 3 (by rfl) ⟨454721, by rfl⟩ : syracuseStep 2425181 = 909443) (by norm_num)
theorem B1818985 : Blo 1615006 1818985 := bbase (se 2 (by rfl) ⟨682119, by rfl⟩ : syracuseStep 1818985 = 1364239) (by norm_num)
theorem B16589173 : Blo 1615006 16589173 := bbase (se 5 (by rfl) ⟨777617, by rfl⟩ : syracuseStep 16589173 = 1555235) (by norm_num)
theorem B2457973 : Blo 1615006 2457973 := bbase (se 5 (by rfl) ⟨115217, by rfl⟩ : syracuseStep 2457973 = 230435) (by norm_num)
theorem B2728309 : Blo 1615006 2728309 := bbase (se 5 (by rfl) ⟨127889, by rfl⟩ : syracuseStep 2728309 = 255779) (by norm_num)
theorem B9208181 : Blo 1615006 9208181 := bbase (se 5 (by rfl) ⟨431633, by rfl⟩ : syracuseStep 9208181 = 863267) (by norm_num)
theorem B2425205 : Blo 1615006 2425205 := bbase (se 5 (by rfl) ⟨113681, by rfl⟩ : syracuseStep 2425205 = 227363) (by norm_num)
theorem B3637637 : Blo 1615006 3637637 := bbase (se 4 (by rfl) ⟨341028, by rfl⟩ : syracuseStep 3637637 = 682057) (by norm_num)
theorem B2425229 : Blo 1615006 2425229 := bbase (se 3 (by rfl) ⟨454730, by rfl⟩ : syracuseStep 2425229 = 909461) (by norm_num)
theorem B1819021 : Blo 1615006 1819021 := bbase (se 3 (by rfl) ⟨341066, by rfl⟩ : syracuseStep 1819021 = 682133) (by norm_num)
theorem B2458021 : Blo 1615006 2458021 := bbase (se 4 (by rfl) ⟨230439, by rfl⟩ : syracuseStep 2458021 = 460879) (by norm_num)
theorem B2425253 : Blo 1615006 2425253 := bbase (se 4 (by rfl) ⟨227367, by rfl⟩ : syracuseStep 2425253 = 454735) (by norm_num)
theorem B1819057 : Blo 1615006 1819057 := bbase (se 2 (by rfl) ⟨682146, by rfl⟩ : syracuseStep 1819057 = 1364293) (by norm_num)
theorem B2425277 : Blo 1615006 2425277 := bbase (se 3 (by rfl) ⟨454739, by rfl⟩ : syracuseStep 2425277 = 909479) (by norm_num)
theorem B3637709 : Blo 1615006 3637709 := bbase (se 3 (by rfl) ⟨682070, by rfl⟩ : syracuseStep 3637709 = 1364141) (by norm_num)
theorem B2728397 : Blo 1615006 2728397 := bbase (se 3 (by rfl) ⟨511574, by rfl⟩ : syracuseStep 2728397 = 1023149) (by norm_num)
theorem B2425301 : Blo 1615006 2425301 := bbase (se 7 (by rfl) ⟨28421, by rfl⟩ : syracuseStep 2425301 = 56843) (by norm_num)
theorem B1819093 : Blo 1615006 1819093 := bbase (se 7 (by rfl) ⟨21317, by rfl⟩ : syracuseStep 1819093 = 42635) (by norm_num)
theorem B3449309 : Blo 1615006 3449309 := bbase (se 3 (by rfl) ⟨646745, by rfl⟩ : syracuseStep 3449309 = 1293491) (by norm_num)
theorem B2425325 : Blo 1615006 2425325 := bbase (se 3 (by rfl) ⟨454748, by rfl⟩ : syracuseStep 2425325 = 909497) (by norm_num)
theorem B1819129 : Blo 1615006 1819129 := bbase (se 2 (by rfl) ⟨682173, by rfl⟩ : syracuseStep 1819129 = 1364347) (by norm_num)
theorem B2425349 : Blo 1615006 2425349 := bbase (se 4 (by rfl) ⟨227376, by rfl⟩ : syracuseStep 2425349 = 454753) (by norm_num)
theorem B4088333 : Blo 1615006 4088333 := bbase (se 3 (by rfl) ⟨766562, by rfl⟩ : syracuseStep 4088333 = 1533125) (by norm_num)
theorem B3637781 : Blo 1615006 3637781 := bbase (se 6 (by rfl) ⟨85260, by rfl⟩ : syracuseStep 3637781 = 170521) (by norm_num)
theorem B2425373 : Blo 1615006 2425373 := bbase (se 3 (by rfl) ⟨454757, by rfl⟩ : syracuseStep 2425373 = 909515) (by norm_num)
theorem B6136357 : Blo 1615006 6136357 := bbase (se 4 (by rfl) ⟨575283, by rfl⟩ : syracuseStep 6136357 = 1150567) (by norm_num)
theorem B2425397 : Blo 1615006 2425397 := bbase (se 5 (by rfl) ⟨113690, by rfl⟩ : syracuseStep 2425397 = 227381) (by norm_num)
theorem B3883589 : Blo 1615006 3883589 := bbase (se 4 (by rfl) ⟨364086, by rfl⟩ : syracuseStep 3883589 = 728173) (by norm_num)
theorem B1638985 : Blo 1615006 1638985 := bbase (se 2 (by rfl) ⟨614619, by rfl⟩ : syracuseStep 1638985 = 1229239) (by norm_num)
theorem B2728525 : Blo 1615006 2728525 := bbase (se 3 (by rfl) ⟨511598, by rfl⟩ : syracuseStep 2728525 = 1023197) (by norm_num)
theorem B2425421 : Blo 1615006 2425421 := bbase (se 3 (by rfl) ⟨454766, by rfl⟩ : syracuseStep 2425421 = 909533) (by norm_num)
theorem B4604501 : Blo 1615006 4604501 := bbase (se 8 (by rfl) ⟨26979, by rfl⟩ : syracuseStep 4604501 = 53959) (by norm_num)
theorem B3637853 : Blo 1615006 3637853 := bbase (se 3 (by rfl) ⟨682097, by rfl⟩ : syracuseStep 3637853 = 1364195) (by norm_num)
theorem B2425445 : Blo 1615006 2425445 := bbase (se 4 (by rfl) ⟨227385, by rfl⟩ : syracuseStep 2425445 = 454771) (by norm_num)
theorem B2425469 : Blo 1615006 2425469 := bbase (se 3 (by rfl) ⟨454775, by rfl⟩ : syracuseStep 2425469 = 909551) (by norm_num)
theorem B2425493 : Blo 1615006 2425493 := bbase (se 6 (by rfl) ⟨56847, by rfl⟩ : syracuseStep 2425493 = 113695) (by norm_num)
theorem B3637925 : Blo 1615006 3637925 := bbase (se 4 (by rfl) ⟨341055, by rfl⟩ : syracuseStep 3637925 = 682111) (by norm_num)
theorem B2728613 : Blo 1615006 2728613 := bbase (se 4 (by rfl) ⟨255807, by rfl⟩ : syracuseStep 2728613 = 511615) (by norm_num)
theorem B3449549 : Blo 1615006 3449549 := bbase (se 3 (by rfl) ⟨646790, by rfl⟩ : syracuseStep 3449549 = 1293581) (by norm_num)
theorem B3687133 : Blo 1615006 3687133 := bbase (se 3 (by rfl) ⟨691337, by rfl⟩ : syracuseStep 3687133 = 1382675) (by norm_num)
theorem B3637997 : Blo 1615006 3637997 := bbase (se 3 (by rfl) ⟨682124, by rfl⟩ : syracuseStep 3637997 = 1364249) (by norm_num)
theorem B5456645 : Blo 1615006 5456645 := bbase (se 4 (by rfl) ⟨511560, by rfl⟩ : syracuseStep 5456645 = 1023121) (by norm_num)
theorem B3638069 : Blo 1615006 3638069 := bbase (se 5 (by rfl) ⟨170534, by rfl⟩ : syracuseStep 3638069 = 341069) (by norm_num)
theorem B6898517 : Blo 1615006 6898517 := bbase (se 9 (by rfl) ⟨20210, by rfl⟩ : syracuseStep 6898517 = 40421) (by norm_num)
theorem B19653461 : Blo 1615006 19653461 := bbase (se 9 (by rfl) ⟨57578, by rfl⟩ : syracuseStep 19653461 = 115157) (by norm_num)
theorem B6136661 : Blo 1615006 6136661 := bbase (se 9 (by rfl) ⟨17978, by rfl⟩ : syracuseStep 6136661 = 35957) (by norm_num)
theorem B4088677 : Blo 1615006 4088677 := bbase (se 4 (by rfl) ⟨383313, by rfl⟩ : syracuseStep 4088677 = 766627) (by norm_num)
theorem B3638141 : Blo 1615006 3638141 := bbase (se 3 (by rfl) ⟨682151, by rfl⟩ : syracuseStep 3638141 = 1364303) (by norm_num)
theorem B3883925 : Blo 1615006 3883925 := bbase (se 6 (by rfl) ⟨91029, by rfl⟩ : syracuseStep 3883925 = 182059) (by norm_num)
theorem B8184725 : Blo 1615006 8184725 := bbase (se 6 (by rfl) ⟨191829, by rfl⟩ : syracuseStep 8184725 = 383659) (by norm_num)
theorem B3638213 : Blo 1615006 3638213 := bbase (se 4 (by rfl) ⟨341082, by rfl⟩ : syracuseStep 3638213 = 682165) (by norm_num)
theorem B4088789 : Blo 1615006 4088789 := bbase (se 7 (by rfl) ⟨47915, by rfl⟩ : syracuseStep 4088789 = 95831) (by norm_num)
theorem B2589661 : Blo 1615006 2589661 := bbase (se 3 (by rfl) ⟨485561, by rfl⟩ : syracuseStep 2589661 = 971123) (by norm_num)
theorem B15533045 : Blo 1615006 15533045 := bbase (se 5 (by rfl) ⟨728111, by rfl⟩ : syracuseStep 15533045 = 1456223) (by norm_num)
theorem B2589725 : Blo 1615006 2589725 := bbase (se 3 (by rfl) ⟨485573, by rfl⟩ : syracuseStep 2589725 = 971147) (by norm_num)
theorem B4088981 : Blo 1615006 4088981 := bbase (se 6 (by rfl) ⟨95835, by rfl⟩ : syracuseStep 4088981 = 191671) (by norm_num)
theorem B6554773 : Blo 1615006 6554773 := bbase (se 6 (by rfl) ⟨153627, by rfl⟩ : syracuseStep 6554773 = 307255) (by norm_num)
theorem B5457077 : Blo 1615006 5457077 := bbase (se 5 (by rfl) ⟨255800, by rfl⟩ : syracuseStep 5457077 = 511601) (by norm_num)
theorem B3450053 : Blo 1615006 3450053 := bbase (se 4 (by rfl) ⟨323442, by rfl⟩ : syracuseStep 3450053 = 646885) (by norm_num)
theorem B3450061 : Blo 1615006 3450061 := bbase (se 3 (by rfl) ⟨646886, by rfl⟩ : syracuseStep 3450061 = 1293773) (by norm_num)
theorem B2073853 : Blo 1615006 2073853 := bbase (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) (by norm_num)
theorem B5178629 : Blo 1615006 5178629 := bbase (se 4 (by rfl) ⟨485496, by rfl⟩ : syracuseStep 5178629 = 970993) (by norm_num)
theorem B3884317 : Blo 1615006 3884317 := bbase (se 3 (by rfl) ⟨728309, by rfl⟩ : syracuseStep 3884317 = 1456619) (by norm_num)
theorem B8176949 : Blo 1615006 8176949 := bbase (se 5 (by rfl) ⟨383294, by rfl⟩ : syracuseStep 8176949 = 766589) (by norm_num)
theorem B4089325 : Blo 1615006 4089325 := bbase (se 3 (by rfl) ⟨766748, by rfl⟩ : syracuseStep 4089325 = 1533497) (by norm_num)
theorem B2074109 : Blo 1615006 2074109 := bbase (se 3 (by rfl) ⟨388895, by rfl⟩ : syracuseStep 2074109 = 777791) (by norm_num)
theorem B11650645 : Blo 1615006 11650645 := bbase (se 8 (by rfl) ⟨68265, by rfl⟩ : syracuseStep 11650645 = 136531) (by norm_num)
theorem B30721621 : Blo 1615006 30721621 := bbase (se 8 (by rfl) ⟨180009, by rfl⟩ : syracuseStep 30721621 = 360019) (by norm_num)
theorem B4916821 : Blo 1615006 4916821 := bbase (se 8 (by rfl) ⟨28809, by rfl⟩ : syracuseStep 4916821 = 57619) (by norm_num)
theorem B4089437 : Blo 1615006 4089437 := bbase (se 3 (by rfl) ⟨766769, by rfl⟩ : syracuseStep 4089437 = 1533539) (by norm_num)
theorem B10356437 : Blo 1615006 10356437 := bbase (se 7 (by rfl) ⟨121364, by rfl⟩ : syracuseStep 10356437 = 242729) (by norm_num)
theorem B4089629 : Blo 1615006 4089629 := bbase (se 3 (by rfl) ⟨766805, by rfl⟩ : syracuseStep 4089629 = 1533611) (by norm_num)
theorem B1967917 : Blo 1615006 1967917 := bbase (se 3 (by rfl) ⟨368984, by rfl⟩ : syracuseStep 1967917 = 737969) (by norm_num)
theorem B2762669 : Blo 1615006 2762669 := bbase (se 3 (by rfl) ⟨518000, by rfl⟩ : syracuseStep 2762669 = 1036001) (by norm_num)
theorem B4089973 : Blo 1615006 4089973 := bbase (se 5 (by rfl) ⟨191717, by rfl⟩ : syracuseStep 4089973 = 383435) (by norm_num)
theorem B8186021 : Blo 1615006 8186021 := bbase (se 4 (by rfl) ⟨767439, by rfl⟩ : syracuseStep 8186021 = 1534879) (by norm_num)
theorem B4090085 : Blo 1615006 4090085 := bbase (se 4 (by rfl) ⟨383445, by rfl⟩ : syracuseStep 4090085 = 766891) (by norm_num)
theorem B3451189 : Blo 1615006 3451189 := bbase (se 5 (by rfl) ⟨161774, by rfl⟩ : syracuseStep 3451189 = 323549) (by norm_num)
theorem B31476053 : Blo 1615006 31476053 := bbase (se 10 (by rfl) ⟨46107, by rfl⟩ : syracuseStep 31476053 = 92215) (by norm_num)
theorem B20695445 : Blo 1615006 20695445 := bbase (se 6 (by rfl) ⟨485049, by rfl⟩ : syracuseStep 20695445 = 970099) (by norm_num)
theorem B12954005 : Blo 1615006 12954005 := bbase (se 6 (by rfl) ⟨303609, by rfl⟩ : syracuseStep 12954005 = 607219) (by norm_num)
theorem B4090277 : Blo 1615006 4090277 := bbase (se 4 (by rfl) ⟨383463, by rfl⟩ : syracuseStep 4090277 = 766927) (by norm_num)
theorem B3066349 : Blo 1615006 3066349 := bbase (se 3 (by rfl) ⟨574940, by rfl⟩ : syracuseStep 3066349 = 1149881) (by norm_num)
theorem B2910701 : Blo 1615006 2910701 := bbase (se 3 (by rfl) ⟨545756, by rfl⟩ : syracuseStep 2910701 = 1091513) (by norm_num)
theorem B6392357 : Blo 1615006 6392357 := bbase (se 4 (by rfl) ⟨599283, by rfl⟩ : syracuseStep 6392357 = 1198567) (by norm_num)
theorem B8178245 : Blo 1615006 8178245 := bbase (se 4 (by rfl) ⟨766710, by rfl⟩ : syracuseStep 8178245 = 1533421) (by norm_num)
theorem B3066493 : Blo 1615006 3066493 := bbase (se 3 (by rfl) ⟨574967, by rfl⟩ : syracuseStep 3066493 = 1149935) (by norm_num)
theorem B3451565 : Blo 1615006 3451565 := bbase (se 3 (by rfl) ⟨647168, by rfl⟩ : syracuseStep 3451565 = 1294337) (by norm_num)
theorem B4090621 : Blo 1615006 4090621 := bbase (se 3 (by rfl) ⟨766991, by rfl⟩ : syracuseStep 4090621 = 1533983) (by norm_num)
theorem B4983557 : Blo 1615006 4983557 := bbase (se 4 (by rfl) ⟨467208, by rfl⟩ : syracuseStep 4983557 = 934417) (by norm_num)
theorem B3066653 : Blo 1615006 3066653 := bbase (se 3 (by rfl) ⟨574997, by rfl⟩ : syracuseStep 3066653 = 1149995) (by norm_num)
theorem B4090733 : Blo 1615006 4090733 := bbase (se 3 (by rfl) ⟨767012, by rfl⟩ : syracuseStep 4090733 = 1534025) (by norm_num)
theorem B1682317 : Blo 1615006 1682317 := bbase (se 3 (by rfl) ⟨315434, by rfl⟩ : syracuseStep 1682317 = 630869) (by norm_num)
theorem B6138773 : Blo 1615006 6138773 := bbase (se 6 (by rfl) ⟨143877, by rfl⟩ : syracuseStep 6138773 = 287755) (by norm_num)
theorem B3066797 : Blo 1615006 3066797 := bbase (se 3 (by rfl) ⟨575024, by rfl⟩ : syracuseStep 3066797 = 1150049) (by norm_num)
theorem B3787709 : Blo 1615006 3787709 := bbase (se 3 (by rfl) ⟨710195, by rfl⟩ : syracuseStep 3787709 = 1420391) (by norm_num)
theorem B4090925 : Blo 1615006 4090925 := bbase (se 3 (by rfl) ⟨767048, by rfl⟩ : syracuseStep 4090925 = 1534097) (by norm_num)
theorem B6900805 : Blo 1615006 6900805 := bbase (se 4 (by rfl) ⟨646950, by rfl⟩ : syracuseStep 6900805 = 1293901) (by norm_num)
theorem B9202805 : Blo 1615006 9202805 := bbase (se 5 (by rfl) ⟨431381, by rfl⟩ : syracuseStep 9202805 = 862763) (by norm_num)
theorem B5827733 : Blo 1615006 5827733 := bbase (se 6 (by rfl) ⟨136587, by rfl⟩ : syracuseStep 5827733 = 273175) (by norm_num)
theorem B13806773 : Blo 1615006 13806773 := bbase (se 5 (by rfl) ⟨647192, by rfl⟩ : syracuseStep 13806773 = 1294385) (by norm_num)
theorem B4369589 : Blo 1615006 4369589 := bbase (se 5 (by rfl) ⟨204824, by rfl⟩ : syracuseStep 4369589 = 409649) (by norm_num)
theorem B6139061 : Blo 1615006 6139061 := bbase (se 5 (by rfl) ⟨287768, by rfl⟩ : syracuseStep 6139061 = 575537) (by norm_num)
theorem B3067085 : Blo 1615006 3067085 := bbase (se 3 (by rfl) ⟨575078, by rfl⟩ : syracuseStep 3067085 = 1150157) (by norm_num)
theorem B8735957 : Blo 1615006 8735957 := bbase (se 7 (by rfl) ⟨102374, by rfl⟩ : syracuseStep 8735957 = 204749) (by norm_num)
theorem B12274901 : Blo 1615006 12274901 := bbase (se 7 (by rfl) ⟨143846, by rfl⟩ : syracuseStep 12274901 = 287693) (by norm_num)
theorem B4369621 : Blo 1615006 4369621 := bbase (se 7 (by rfl) ⟨51206, by rfl⟩ : syracuseStep 4369621 = 102413) (by norm_num)
theorem B5451029 : Blo 1615006 5451029 := bbase (se 6 (by rfl) ⟨127758, by rfl⟩ : syracuseStep 5451029 = 255517) (by norm_num)
theorem B3108149 : Blo 1615006 3108149 := bbase (se 5 (by rfl) ⟨145694, by rfl⟩ : syracuseStep 3108149 = 291389) (by norm_num)
theorem B4599125 : Blo 1615006 4599125 := bbase (se 11 (by rfl) ⟨3368, by rfl⟩ : syracuseStep 4599125 = 6737) (by norm_num)
theorem B7761253 : Blo 1615006 7761253 := bbase (se 4 (by rfl) ⟨727617, by rfl⟩ : syracuseStep 7761253 = 1455235) (by norm_num)
theorem B3067237 : Blo 1615006 3067237 := bbase (se 4 (by rfl) ⟨287553, by rfl⟩ : syracuseStep 3067237 = 575107) (by norm_num)
theorem B4091269 : Blo 1615006 4091269 := bbase (se 4 (by rfl) ⟨383556, by rfl⟩ : syracuseStep 4091269 = 767113) (by norm_num)
theorem B7769557 : Blo 1615006 7769557 := bbase (se 7 (by rfl) ⟨91049, by rfl⟩ : syracuseStep 7769557 = 182099) (by norm_num)
theorem B4091381 : Blo 1615006 4091381 := bbase (se 5 (by rfl) ⟨191783, by rfl⟩ : syracuseStep 4091381 = 383567) (by norm_num)
theorem B12267125 : Blo 1615006 12267125 := bbase (se 5 (by rfl) ⟨575021, by rfl⟩ : syracuseStep 12267125 = 1150043) (by norm_num)
theorem B3067541 : Blo 1615006 3067541 := bbase (se 6 (by rfl) ⟨71895, by rfl⟩ : syracuseStep 3067541 = 143791) (by norm_num)
theorem B1748633 : Blo 1615006 1748633 := bbase (se 2 (by rfl) ⟨655737, by rfl⟩ : syracuseStep 1748633 = 1311475) (by norm_num)
theorem B4091573 : Blo 1615006 4091573 := bbase (se 5 (by rfl) ⟨191792, by rfl⟩ : syracuseStep 4091573 = 383585) (by norm_num)
theorem B5451461 : Blo 1615006 5451461 := bbase (se 4 (by rfl) ⟨511074, by rfl⟩ : syracuseStep 5451461 = 1022149) (by norm_num)
theorem B8179541 : Blo 1615006 8179541 := bbase (se 9 (by rfl) ⟨23963, by rfl⟩ : syracuseStep 8179541 = 47927) (by norm_num)
theorem B3108701 : Blo 1615006 3108701 := bbase (se 3 (by rfl) ⟨582881, by rfl⟩ : syracuseStep 3108701 = 1165763) (by norm_num)
theorem B2764693 : Blo 1615006 2764693 := bbase (se 6 (by rfl) ⟨64797, by rfl⟩ : syracuseStep 2764693 = 129595) (by norm_num)
theorem B2183069 : Blo 1615006 2183069 := bbase (se 3 (by rfl) ⟨409325, by rfl⟩ : syracuseStep 2183069 = 818651) (by norm_num)
theorem B2625461 : Blo 1615006 2625461 := bbase (se 5 (by rfl) ⟨123068, by rfl⟩ : syracuseStep 2625461 = 246137) (by norm_num)
theorem B4091917 : Blo 1615006 4091917 := bbase (se 3 (by rfl) ⟨767234, by rfl⟩ : syracuseStep 4091917 = 1534469) (by norm_num)
theorem B8736821 : Blo 1615006 8736821 := bbase (se 5 (by rfl) ⟨409538, by rfl⟩ : syracuseStep 8736821 = 819077) (by norm_num)
theorem B5451893 : Blo 1615006 5451893 := bbase (se 5 (by rfl) ⟨255557, by rfl⟩ : syracuseStep 5451893 = 511115) (by norm_num)
theorem B4092029 : Blo 1615006 4092029 := bbase (se 3 (by rfl) ⟨767255, by rfl⟩ : syracuseStep 4092029 = 1534511) (by norm_num)
theorem B2044045 : Blo 1615006 2044045 := bbase (se 3 (by rfl) ⟨383258, by rfl⟩ : syracuseStep 2044045 = 766517) (by norm_num)
theorem B1724689 : Blo 1615006 1724689 := bbase (se 2 (by rfl) ⟨646758, by rfl⟩ : syracuseStep 1724689 = 1293517) (by norm_num)
theorem B9203989 : Blo 1615006 9203989 := bbase (se 6 (by rfl) ⟨215718, by rfl⟩ : syracuseStep 9203989 = 431437) (by norm_num)
theorem B3453205 : Blo 1615006 3453205 := bbase (se 6 (by rfl) ⟨80934, by rfl⟩ : syracuseStep 3453205 = 161869) (by norm_num)
theorem B2044217 : Blo 1615006 2044217 := bbase (se 2 (by rfl) ⟨766581, by rfl⟩ : syracuseStep 2044217 = 1533163) (by norm_num)
theorem B4092221 : Blo 1615006 4092221 := bbase (se 3 (by rfl) ⟨767291, by rfl⟩ : syracuseStep 4092221 = 1534583) (by norm_num)
theorem B2044273 : Blo 1615006 2044273 := bbase (se 2 (by rfl) ⟨766602, by rfl⟩ : syracuseStep 2044273 = 1533205) (by norm_num)
theorem B3068293 : Blo 1615006 3068293 := bbase (se 4 (by rfl) ⟨287652, by rfl⟩ : syracuseStep 3068293 = 575305) (by norm_num)
theorem B1749433 : Blo 1615006 1749433 := bbase (se 2 (by rfl) ⟨656037, by rfl⟩ : syracuseStep 1749433 = 1312075) (by norm_num)
theorem B2765261 : Blo 1615006 2765261 := bbase (se 3 (by rfl) ⟨518486, by rfl⟩ : syracuseStep 2765261 = 1036973) (by norm_num)
theorem B2044369 : Blo 1615006 2044369 := bbase (se 2 (by rfl) ⟨766638, by rfl⟩ : syracuseStep 2044369 = 1533277) (by norm_num)
theorem B7188965 : Blo 1615006 7188965 := bbase (se 4 (by rfl) ⟨673965, by rfl⟩ : syracuseStep 7188965 = 1347931) (by norm_num)
theorem B4600309 : Blo 1615006 4600309 := bbase (se 5 (by rfl) ⟨215639, by rfl⟩ : syracuseStep 4600309 = 431279) (by norm_num)
theorem B6902293 : Blo 1615006 6902293 := bbase (se 6 (by rfl) ⟨161772, by rfl⟩ : syracuseStep 6902293 = 323545) (by norm_num)
theorem B3068437 : Blo 1615006 3068437 := bbase (se 6 (by rfl) ⟨71916, by rfl⟩ : syracuseStep 3068437 = 143833) (by norm_num)
theorem B5452325 : Blo 1615006 5452325 := bbase (se 4 (by rfl) ⟨511155, by rfl⟩ : syracuseStep 5452325 = 1022311) (by norm_num)
theorem B6902309 : Blo 1615006 6902309 := bbase (se 4 (by rfl) ⟨647091, by rfl⟩ : syracuseStep 6902309 = 1294183) (by norm_num)
theorem B2765357 : Blo 1615006 2765357 := bbase (se 3 (by rfl) ⟨518504, by rfl⟩ : syracuseStep 2765357 = 1037009) (by norm_num)
theorem B2183773 : Blo 1615006 2183773 := bbase (se 3 (by rfl) ⟨409457, by rfl⟩ : syracuseStep 2183773 = 818915) (by norm_num)
theorem B2044541 : Blo 1615006 2044541 := bbase (se 3 (by rfl) ⟨383351, by rfl⟩ : syracuseStep 2044541 = 766703) (by norm_num)
theorem B4600469 : Blo 1615006 4600469 := bbase (se 6 (by rfl) ⟨107823, by rfl⟩ : syracuseStep 4600469 = 215647) (by norm_num)
theorem B4092565 : Blo 1615006 4092565 := bbase (se 6 (by rfl) ⟨95919, by rfl⟩ : syracuseStep 4092565 = 191839) (by norm_num)
theorem B3633821 : Blo 1615006 3633821 := bbase (se 3 (by rfl) ⟨681341, by rfl⟩ : syracuseStep 3633821 = 1362683) (by norm_num)
theorem B2044597 : Blo 1615006 2044597 := bbase (se 5 (by rfl) ⟨95840, by rfl⟩ : syracuseStep 2044597 = 191681) (by norm_num)
theorem B3068597 : Blo 1615006 3068597 := bbase (se 5 (by rfl) ⟨143840, by rfl⟩ : syracuseStep 3068597 = 287681) (by norm_num)
theorem B3633893 : Blo 1615006 3633893 := bbase (se 4 (by rfl) ⟨340677, by rfl⟩ : syracuseStep 3633893 = 681355) (by norm_num)
theorem B6132469 : Blo 1615006 6132469 := bbase (se 5 (by rfl) ⟨287459, by rfl⟩ : syracuseStep 6132469 = 574919) (by norm_num)
theorem B4092677 : Blo 1615006 4092677 := bbase (se 4 (by rfl) ⟨383688, by rfl⟩ : syracuseStep 4092677 = 767377) (by norm_num)
theorem B2044693 : Blo 1615006 2044693 := bbase (se 6 (by rfl) ⟨47922, by rfl⟩ : syracuseStep 2044693 = 95845) (by norm_num)
theorem B3633965 : Blo 1615006 3633965 := bbase (se 3 (by rfl) ⟨681368, by rfl⟩ : syracuseStep 3633965 = 1362737) (by norm_num)
theorem B3068741 : Blo 1615006 3068741 := bbase (se 4 (by rfl) ⟨287694, by rfl⟩ : syracuseStep 3068741 = 575389) (by norm_num)
theorem B3634037 : Blo 1615006 3634037 := bbase (se 5 (by rfl) ⟨170345, by rfl⟩ : syracuseStep 3634037 = 340691) (by norm_num)
theorem B4600709 : Blo 1615006 4600709 := bbase (se 4 (by rfl) ⟨431316, by rfl⟩ : syracuseStep 4600709 = 862633) (by norm_num)
theorem B4666261 : Blo 1615006 4666261 := bbase (se 6 (by rfl) ⟨109365, by rfl⟩ : syracuseStep 4666261 = 218731) (by norm_num)
theorem B3634109 : Blo 1615006 3634109 := bbase (se 3 (by rfl) ⟨681395, by rfl⟩ : syracuseStep 3634109 = 1362791) (by norm_num)
theorem B2044865 : Blo 1615006 2044865 := bbase (se 2 (by rfl) ⟨766824, by rfl⟩ : syracuseStep 2044865 = 1533649) (by norm_num)
theorem B4092869 : Blo 1615006 4092869 := bbase (se 4 (by rfl) ⟨383706, by rfl⟩ : syracuseStep 4092869 = 767413) (by norm_num)
theorem B5452757 : Blo 1615006 5452757 := bbase (se 7 (by rfl) ⟨63899, by rfl⟩ : syracuseStep 5452757 = 127799) (by norm_num)
theorem B2044921 : Blo 1615006 2044921 := bbase (se 2 (by rfl) ⟨766845, by rfl⟩ : syracuseStep 2044921 = 1533691) (by norm_num)
theorem B3634181 : Blo 1615006 3634181 := bbase (se 4 (by rfl) ⟨340704, by rfl⟩ : syracuseStep 3634181 = 681409) (by norm_num)
theorem B6132773 : Blo 1615006 6132773 := bbase (se 4 (by rfl) ⟨574947, by rfl⟩ : syracuseStep 6132773 = 1149895) (by norm_num)
theorem B4600901 : Blo 1615006 4600901 := bbase (se 4 (by rfl) ⟨431334, by rfl⟩ : syracuseStep 4600901 = 862669) (by norm_num)
theorem B1725509 : Blo 1615006 1725509 := bbase (se 4 (by rfl) ⟨161766, by rfl⟩ : syracuseStep 1725509 = 323533) (by norm_num)
theorem B3634253 : Blo 1615006 3634253 := bbase (se 3 (by rfl) ⟨681422, by rfl⟩ : syracuseStep 3634253 = 1362845) (by norm_num)
theorem B49755221 : Blo 1615006 49755221 := bbase (se 8 (by rfl) ⟨291534, by rfl⟩ : syracuseStep 49755221 = 583069) (by norm_num)
theorem B2045017 : Blo 1615006 2045017 := bbase (se 2 (by rfl) ⟨766881, by rfl⟩ : syracuseStep 2045017 = 1533763) (by norm_num)
theorem B8180837 : Blo 1615006 8180837 := bbase (se 4 (by rfl) ⟨766953, by rfl⟩ : syracuseStep 8180837 = 1533907) (by norm_num)
theorem B3069029 : Blo 1615006 3069029 := bbase (se 4 (by rfl) ⟨287721, by rfl⟩ : syracuseStep 3069029 = 575443) (by norm_num)
theorem B3634325 : Blo 1615006 3634325 := bbase (se 6 (by rfl) ⟨85179, by rfl⟩ : syracuseStep 3634325 = 170359) (by norm_num)
theorem B3634397 : Blo 1615006 3634397 := bbase (se 3 (by rfl) ⟨681449, by rfl⟩ : syracuseStep 3634397 = 1362899) (by norm_num)
theorem B3069181 : Blo 1615006 3069181 := bbase (se 3 (by rfl) ⟨575471, by rfl⟩ : syracuseStep 3069181 = 1150943) (by norm_num)
theorem B2045189 : Blo 1615006 2045189 := bbase (se 4 (by rfl) ⟨191736, by rfl⟩ : syracuseStep 2045189 = 383473) (by norm_num)
theorem B3634469 : Blo 1615006 3634469 := bbase (se 4 (by rfl) ⟨340731, by rfl⟩ : syracuseStep 3634469 = 681463) (by norm_num)
theorem B2045245 : Blo 1615006 2045245 := bbase (se 3 (by rfl) ⟨383483, by rfl⟩ : syracuseStep 2045245 = 766967) (by norm_num)
theorem B3634541 : Blo 1615006 3634541 := bbase (se 3 (by rfl) ⟨681476, by rfl⟩ : syracuseStep 3634541 = 1362953) (by norm_num)
theorem B5453189 : Blo 1615006 5453189 := bbase (se 4 (by rfl) ⟨511236, by rfl⟩ : syracuseStep 5453189 = 1022473) (by norm_num)
theorem B2045341 : Blo 1615006 2045341 := bbase (se 3 (by rfl) ⟨383501, by rfl⟩ : syracuseStep 2045341 = 767003) (by norm_num)
theorem B3634613 : Blo 1615006 3634613 := bbase (se 5 (by rfl) ⟨170372, by rfl⟩ : syracuseStep 3634613 = 340745) (by norm_num)
theorem B2725373 : Blo 1615006 2725373 := bbase (se 3 (by rfl) ⟨511007, by rfl⟩ : syracuseStep 2725373 = 1022015) (by norm_num)
theorem B3634685 : Blo 1615006 3634685 := bbase (se 3 (by rfl) ⟨681503, by rfl⟩ : syracuseStep 3634685 = 1363007) (by norm_num)
theorem B1725953 : Blo 1615006 1725953 := bbase (se 2 (by rfl) ⟨647232, by rfl⟩ : syracuseStep 1725953 = 1294465) (by norm_num)
theorem B5527045 : Blo 1615006 5527045 := bbase (se 4 (by rfl) ⟨518160, by rfl⟩ : syracuseStep 5527045 = 1036321) (by norm_num)
theorem B3069485 : Blo 1615006 3069485 := bbase (se 3 (by rfl) ⟨575528, by rfl⟩ : syracuseStep 3069485 = 1151057) (by norm_num)
theorem B5174837 : Blo 1615006 5174837 := bbase (se 5 (by rfl) ⟨242570, by rfl⟩ : syracuseStep 5174837 = 485141) (by norm_num)
theorem B3634757 : Blo 1615006 3634757 := bbase (se 4 (by rfl) ⟨340758, by rfl⟩ : syracuseStep 3634757 = 681517) (by norm_num)
theorem B2045513 : Blo 1615006 2045513 := bbase (se 2 (by rfl) ⟨767067, by rfl⟩ : syracuseStep 2045513 = 1534135) (by norm_num)
theorem B2725501 : Blo 1615006 2725501 := bbase (se 3 (by rfl) ⟨511031, by rfl⟩ : syracuseStep 2725501 = 1022063) (by norm_num)
theorem B2045569 : Blo 1615006 2045569 := bbase (se 2 (by rfl) ⟨767088, by rfl⟩ : syracuseStep 2045569 = 1534177) (by norm_num)
theorem B3634829 : Blo 1615006 3634829 := bbase (se 3 (by rfl) ⟨681530, by rfl⟩ : syracuseStep 3634829 = 1363061) (by norm_num)
theorem B2725589 : Blo 1615006 2725589 := bbase (se 7 (by rfl) ⟨31940, by rfl⟩ : syracuseStep 2725589 = 63881) (by norm_num)
theorem B3634901 : Blo 1615006 3634901 := bbase (se 7 (by rfl) ⟨42596, by rfl⟩ : syracuseStep 3634901 = 85193) (by norm_num)
theorem B2045665 : Blo 1615006 2045665 := bbase (se 2 (by rfl) ⟨767124, by rfl⟩ : syracuseStep 2045665 = 1534249) (by norm_num)
theorem B2422517 : Blo 1615006 2422517 := bbase (se 5 (by rfl) ⟨113555, by rfl⟩ : syracuseStep 2422517 = 227111) (by norm_num)
theorem B1726201 : Blo 1615006 1726201 := bbase (se 2 (by rfl) ⟨647325, by rfl⟩ : syracuseStep 1726201 = 1294651) (by norm_num)
theorem B2422541 : Blo 1615006 2422541 := bbase (se 3 (by rfl) ⟨454226, by rfl⟩ : syracuseStep 2422541 = 908453) (by norm_num)
theorem B3634973 : Blo 1615006 3634973 := bbase (se 3 (by rfl) ⟨681557, by rfl⟩ : syracuseStep 3634973 = 1363115) (by norm_num)
theorem B2422565 : Blo 1615006 2422565 := bbase (se 4 (by rfl) ⟨227115, by rfl⟩ : syracuseStep 2422565 = 454231) (by norm_num)
theorem B3684149 : Blo 1615006 3684149 := bbase (se 5 (by rfl) ⟨172694, by rfl⟩ : syracuseStep 3684149 = 345389) (by norm_num)
theorem B5453621 : Blo 1615006 5453621 := bbase (se 5 (by rfl) ⟨255638, by rfl⟩ : syracuseStep 5453621 = 511277) (by norm_num)
theorem B2422589 : Blo 1615006 2422589 := bbase (se 3 (by rfl) ⟨454235, by rfl⟩ : syracuseStep 2422589 = 908471) (by norm_num)
theorem B3880781 : Blo 1615006 3880781 := bbase (se 3 (by rfl) ⟨727646, by rfl⟩ : syracuseStep 3880781 = 1455293) (by norm_num)
theorem B2422613 : Blo 1615006 2422613 := bbase (se 9 (by rfl) ⟨7097, by rfl⟩ : syracuseStep 2422613 = 14195) (by norm_num)
theorem B2725717 : Blo 1615006 2725717 := bbase (se 9 (by rfl) ⟨7985, by rfl⟩ : syracuseStep 2725717 = 15971) (by norm_num)
theorem B3635045 : Blo 1615006 3635045 := bbase (se 4 (by rfl) ⟨340785, by rfl⟩ : syracuseStep 3635045 = 681571) (by norm_num)
theorem B2422637 : Blo 1615006 2422637 := bbase (se 3 (by rfl) ⟨454244, by rfl⟩ : syracuseStep 2422637 = 908489) (by norm_num)
theorem B11655029 : Blo 1615006 11655029 := bbase (se 5 (by rfl) ⟨546329, by rfl⟩ : syracuseStep 11655029 = 1092659) (by norm_num)
theorem B2422661 : Blo 1615006 2422661 := bbase (se 4 (by rfl) ⟨227124, by rfl⟩ : syracuseStep 2422661 = 454249) (by norm_num)
theorem B2045837 : Blo 1615006 2045837 := bbase (se 3 (by rfl) ⟨383594, by rfl⟩ : syracuseStep 2045837 = 767189) (by norm_num)
theorem B2422685 : Blo 1615006 2422685 := bbase (se 3 (by rfl) ⟨454253, by rfl⟩ : syracuseStep 2422685 = 908507) (by norm_num)
theorem B8288165 : Blo 1615006 8288165 := bbase (se 4 (by rfl) ⟨777015, by rfl⟩ : syracuseStep 8288165 = 1554031) (by norm_num)
theorem B3880877 : Blo 1615006 3880877 := bbase (se 3 (by rfl) ⟨727664, by rfl⟩ : syracuseStep 3880877 = 1455329) (by norm_num)
theorem B2725805 : Blo 1615006 2725805 := bbase (se 3 (by rfl) ⟨511088, by rfl⟩ : syracuseStep 2725805 = 1022177) (by norm_num)
theorem B3635117 : Blo 1615006 3635117 := bbase (se 3 (by rfl) ⟨681584, by rfl⟩ : syracuseStep 3635117 = 1363169) (by norm_num)
theorem B2422709 : Blo 1615006 2422709 := bbase (se 5 (by rfl) ⟨113564, by rfl⟩ : syracuseStep 2422709 = 227129) (by norm_num)
theorem B2045893 : Blo 1615006 2045893 := bbase (se 4 (by rfl) ⟨191802, by rfl⟩ : syracuseStep 2045893 = 383605) (by norm_num)
theorem B2185157 : Blo 1615006 2185157 := bbase (se 4 (by rfl) ⟨204858, by rfl⟩ : syracuseStep 2185157 = 409717) (by norm_num)
theorem B2422733 : Blo 1615006 2422733 := bbase (se 3 (by rfl) ⟨454262, by rfl⟩ : syracuseStep 2422733 = 908525) (by norm_num)
theorem B2299853 : Blo 1615006 2299853 := bbase (se 3 (by rfl) ⟨431222, by rfl⟩ : syracuseStep 2299853 = 862445) (by norm_num)
theorem B2422757 : Blo 1615006 2422757 := bbase (se 4 (by rfl) ⟨227133, by rfl⟩ : syracuseStep 2422757 = 454267) (by norm_num)
theorem B3635189 : Blo 1615006 3635189 := bbase (se 5 (by rfl) ⟨170399, by rfl⟩ : syracuseStep 3635189 = 340799) (by norm_num)
theorem B2422781 : Blo 1615006 2422781 := bbase (se 3 (by rfl) ⟨454271, by rfl⟩ : syracuseStep 2422781 = 908543) (by norm_num)
theorem B2422805 : Blo 1615006 2422805 := bbase (se 6 (by rfl) ⟨56784, by rfl⟩ : syracuseStep 2422805 = 113569) (by norm_num)
theorem B4601893 : Blo 1615006 4601893 := bbase (se 4 (by rfl) ⟨431427, by rfl⟩ : syracuseStep 4601893 = 862855) (by norm_num)
theorem B2045989 : Blo 1615006 2045989 := bbase (se 4 (by rfl) ⟨191811, by rfl⟩ : syracuseStep 2045989 = 383623) (by norm_num)
theorem B2422829 : Blo 1615006 2422829 := bbase (se 3 (by rfl) ⟨454280, by rfl⟩ : syracuseStep 2422829 = 908561) (by norm_num)
theorem B2725933 : Blo 1615006 2725933 := bbase (se 3 (by rfl) ⟨511112, by rfl⟩ : syracuseStep 2725933 = 1022225) (by norm_num)
theorem B3635261 : Blo 1615006 3635261 := bbase (se 3 (by rfl) ⟨681611, by rfl⟩ : syracuseStep 3635261 = 1363223) (by norm_num)
theorem B2422853 : Blo 1615006 2422853 := bbase (se 4 (by rfl) ⟨227142, by rfl⟩ : syracuseStep 2422853 = 454285) (by norm_num)
theorem B6993989 : Blo 1615006 6993989 := bbase (se 4 (by rfl) ⟨655686, by rfl⟩ : syracuseStep 6993989 = 1311373) (by norm_num)
theorem B2422877 : Blo 1615006 2422877 := bbase (se 3 (by rfl) ⟨454289, by rfl⟩ : syracuseStep 2422877 = 908579) (by norm_num)
theorem B2422901 : Blo 1615006 2422901 := bbase (se 5 (by rfl) ⟨113573, by rfl⟩ : syracuseStep 2422901 = 227147) (by norm_num)
theorem B2726021 : Blo 1615006 2726021 := bbase (se 4 (by rfl) ⟨255564, by rfl⟩ : syracuseStep 2726021 = 511129) (by norm_num)
theorem B3635333 : Blo 1615006 3635333 := bbase (se 4 (by rfl) ⟨340812, by rfl⟩ : syracuseStep 3635333 = 681625) (by norm_num)
theorem B2422925 : Blo 1615006 2422925 := bbase (se 3 (by rfl) ⟨454298, by rfl⟩ : syracuseStep 2422925 = 908597) (by norm_num)
theorem B2422949 : Blo 1615006 2422949 := bbase (se 4 (by rfl) ⟨227151, by rfl⟩ : syracuseStep 2422949 = 454303) (by norm_num)
theorem B1726633 : Blo 1615006 1726633 := bbase (se 2 (by rfl) ⟨647487, by rfl⟩ : syracuseStep 1726633 = 1294975) (by norm_num)
theorem B9828533 : Blo 1615006 9828533 := bbase (se 5 (by rfl) ⟨460712, by rfl⟩ : syracuseStep 9828533 = 921425) (by norm_num)
theorem B2422973 : Blo 1615006 2422973 := bbase (se 3 (by rfl) ⟨454307, by rfl⟩ : syracuseStep 2422973 = 908615) (by norm_num)
theorem B3635405 : Blo 1615006 3635405 := bbase (se 3 (by rfl) ⟨681638, by rfl⟩ : syracuseStep 3635405 = 1363277) (by norm_num)
theorem B2046161 : Blo 1615006 2046161 := bbase (se 2 (by rfl) ⟨767310, by rfl⟩ : syracuseStep 2046161 = 1534621) (by norm_num)
theorem B2422997 : Blo 1615006 2422997 := bbase (se 7 (by rfl) ⟨28394, by rfl⟩ : syracuseStep 2422997 = 56789) (by norm_num)
theorem B9205973 : Blo 1615006 9205973 := bbase (se 7 (by rfl) ⟨107882, by rfl⟩ : syracuseStep 9205973 = 215765) (by norm_num)
theorem B5454053 : Blo 1615006 5454053 := bbase (se 4 (by rfl) ⟨511317, by rfl⟩ : syracuseStep 5454053 = 1022635) (by norm_num)
theorem B2423021 : Blo 1615006 2423021 := bbase (se 3 (by rfl) ⟨454316, by rfl⟩ : syracuseStep 2423021 = 908633) (by norm_num)
theorem B1726705 : Blo 1615006 1726705 := bbase (se 2 (by rfl) ⟨647514, by rfl⟩ : syracuseStep 1726705 = 1295029) (by norm_num)
theorem B2423045 : Blo 1615006 2423045 := bbase (se 4 (by rfl) ⟨227160, by rfl⟩ : syracuseStep 2423045 = 454321) (by norm_num)
theorem B2726149 : Blo 1615006 2726149 := bbase (se 4 (by rfl) ⟨255576, by rfl⟩ : syracuseStep 2726149 = 511153) (by norm_num)
theorem B2046217 : Blo 1615006 2046217 := bbase (se 2 (by rfl) ⟨767331, by rfl⟩ : syracuseStep 2046217 = 1534663) (by norm_num)
theorem B3635477 : Blo 1615006 3635477 := bbase (se 6 (by rfl) ⟨85206, by rfl⟩ : syracuseStep 3635477 = 170413) (by norm_num)
theorem B2423069 : Blo 1615006 2423069 := bbase (se 3 (by rfl) ⟨454325, by rfl⟩ : syracuseStep 2423069 = 908651) (by norm_num)
theorem B2423093 : Blo 1615006 2423093 := bbase (se 5 (by rfl) ⟨113582, by rfl⟩ : syracuseStep 2423093 = 227165) (by norm_num)
theorem B1816897 : Blo 1615006 1816897 := bbase (se 2 (by rfl) ⟨681336, by rfl⟩ : syracuseStep 1816897 = 1362673) (by norm_num)
theorem B2423117 : Blo 1615006 2423117 := bbase (se 3 (by rfl) ⟨454334, by rfl⟩ : syracuseStep 2423117 = 908669) (by norm_num)
theorem B2726237 : Blo 1615006 2726237 := bbase (se 3 (by rfl) ⟨511169, by rfl⟩ : syracuseStep 2726237 = 1022339) (by norm_num)
theorem B3635549 : Blo 1615006 3635549 := bbase (se 3 (by rfl) ⟨681665, by rfl⟩ : syracuseStep 3635549 = 1363331) (by norm_num)
theorem B1816933 : Blo 1615006 1816933 := bbase (se 4 (by rfl) ⟨170337, by rfl⟩ : syracuseStep 1816933 = 340675) (by norm_num)
theorem B2423141 : Blo 1615006 2423141 := bbase (se 4 (by rfl) ⟨227169, by rfl⟩ : syracuseStep 2423141 = 454339) (by norm_num)
theorem B2046313 : Blo 1615006 2046313 := bbase (se 2 (by rfl) ⟨767367, by rfl⟩ : syracuseStep 2046313 = 1534735) (by norm_num)
theorem B8182133 : Blo 1615006 8182133 := bbase (se 5 (by rfl) ⟨383537, by rfl⟩ : syracuseStep 8182133 = 767075) (by norm_num)
theorem B2423165 : Blo 1615006 2423165 := bbase (se 3 (by rfl) ⟨454343, by rfl⟩ : syracuseStep 2423165 = 908687) (by norm_num)
theorem B1661317 : Blo 1615006 1661317 := bbase (se 4 (by rfl) ⟨155748, by rfl⟩ : syracuseStep 1661317 = 311497) (by norm_num)
theorem B1816969 : Blo 1615006 1816969 := bbase (se 2 (by rfl) ⟨681363, by rfl⟩ : syracuseStep 1816969 = 1362727) (by norm_num)
theorem B2423189 : Blo 1615006 2423189 := bbase (se 6 (by rfl) ⟨56793, by rfl⟩ : syracuseStep 2423189 = 113587) (by norm_num)
theorem B3635621 : Blo 1615006 3635621 := bbase (se 4 (by rfl) ⟨340839, by rfl⟩ : syracuseStep 3635621 = 681679) (by norm_num)
theorem B5527973 : Blo 1615006 5527973 := bbase (se 4 (by rfl) ⟨518247, by rfl⟩ : syracuseStep 5527973 = 1036495) (by norm_num)
theorem B1817005 : Blo 1615006 1817005 := bbase (se 3 (by rfl) ⟨340688, by rfl⟩ : syracuseStep 1817005 = 681377) (by norm_num)
theorem B2423213 : Blo 1615006 2423213 := bbase (se 3 (by rfl) ⟨454352, by rfl⟩ : syracuseStep 2423213 = 908705) (by norm_num)
theorem B5175733 : Blo 1615006 5175733 := bbase (se 5 (by rfl) ⟨242612, by rfl⟩ : syracuseStep 5175733 = 485225) (by norm_num)
theorem B6642101 : Blo 1615006 6642101 := bbase (se 5 (by rfl) ⟨311348, by rfl⟩ : syracuseStep 6642101 = 622697) (by norm_num)
theorem B2423237 : Blo 1615006 2423237 := bbase (se 4 (by rfl) ⟨227178, by rfl⟩ : syracuseStep 2423237 = 454357) (by norm_num)
theorem B1817041 : Blo 1615006 1817041 := bbase (se 2 (by rfl) ⟨681390, by rfl⟩ : syracuseStep 1817041 = 1362781) (by norm_num)
theorem B3275221 : Blo 1615006 3275221 := bbase (se 7 (by rfl) ⟨38381, by rfl⟩ : syracuseStep 3275221 = 76763) (by norm_num)
theorem B2423261 : Blo 1615006 2423261 := bbase (se 3 (by rfl) ⟨454361, by rfl⟩ : syracuseStep 2423261 = 908723) (by norm_num)
theorem B2726365 : Blo 1615006 2726365 := bbase (se 3 (by rfl) ⟨511193, by rfl⟩ : syracuseStep 2726365 = 1022387) (by norm_num)
theorem B3635693 : Blo 1615006 3635693 := bbase (se 3 (by rfl) ⟨681692, by rfl⟩ : syracuseStep 3635693 = 1363385) (by norm_num)
theorem B1817077 : Blo 1615006 1817077 := bbase (se 5 (by rfl) ⟨85175, by rfl⟩ : syracuseStep 1817077 = 170351) (by norm_num)
theorem B2423285 : Blo 1615006 2423285 := bbase (se 5 (by rfl) ⟨113591, by rfl⟩ : syracuseStep 2423285 = 227183) (by norm_num)
theorem B2300405 : Blo 1615006 2300405 := bbase (se 5 (by rfl) ⟨107831, by rfl⟩ : syracuseStep 2300405 = 215663) (by norm_num)
theorem B2423309 : Blo 1615006 2423309 := bbase (se 3 (by rfl) ⟨454370, by rfl⟩ : syracuseStep 2423309 = 908741) (by norm_num)
theorem B2046485 : Blo 1615006 2046485 := bbase (se 6 (by rfl) ⟨47964, by rfl⟩ : syracuseStep 2046485 = 95929) (by norm_num)
theorem B1817113 : Blo 1615006 1817113 := bbase (se 2 (by rfl) ⟨681417, by rfl⟩ : syracuseStep 1817113 = 1362835) (by norm_num)
theorem B2423333 : Blo 1615006 2423333 := bbase (se 4 (by rfl) ⟨227187, by rfl⟩ : syracuseStep 2423333 = 454375) (by norm_num)
theorem B3275317 : Blo 1615006 3275317 := bbase (se 5 (by rfl) ⟨153530, by rfl⟩ : syracuseStep 3275317 = 307061) (by norm_num)
theorem B2726453 : Blo 1615006 2726453 := bbase (se 5 (by rfl) ⟨127802, by rfl⟩ : syracuseStep 2726453 = 255605) (by norm_num)
theorem B3635765 : Blo 1615006 3635765 := bbase (se 5 (by rfl) ⟨170426, by rfl⟩ : syracuseStep 3635765 = 340853) (by norm_num)
theorem B1817149 : Blo 1615006 1817149 := bbase (se 3 (by rfl) ⟨340715, by rfl⟩ : syracuseStep 1817149 = 681431) (by norm_num)
theorem B2423357 : Blo 1615006 2423357 := bbase (se 3 (by rfl) ⟨454379, by rfl⟩ : syracuseStep 2423357 = 908759) (by norm_num)
theorem B2423381 : Blo 1615006 2423381 := bbase (se 8 (by rfl) ⟨14199, by rfl⟩ : syracuseStep 2423381 = 28399) (by norm_num)
theorem B78608981 : Blo 1615006 78608981 := bbase (se 8 (by rfl) ⟨460599, by rfl⟩ : syracuseStep 78608981 = 921199) (by norm_num)
theorem B1817185 : Blo 1615006 1817185 := bbase (se 2 (by rfl) ⟨681444, by rfl⟩ : syracuseStep 1817185 = 1362889) (by norm_num)
theorem B2423405 : Blo 1615006 2423405 := bbase (se 3 (by rfl) ⟨454388, by rfl⟩ : syracuseStep 2423405 = 908777) (by norm_num)
theorem B3684989 : Blo 1615006 3684989 := bbase (se 3 (by rfl) ⟨690935, by rfl⟩ : syracuseStep 3684989 = 1381871) (by norm_num)
theorem B3635837 : Blo 1615006 3635837 := bbase (se 3 (by rfl) ⟨681719, by rfl⟩ : syracuseStep 3635837 = 1363439) (by norm_num)
theorem B1817221 : Blo 1615006 1817221 := bbase (se 4 (by rfl) ⟨170364, by rfl⟩ : syracuseStep 1817221 = 340729) (by norm_num)
theorem B2423429 : Blo 1615006 2423429 := bbase (se 4 (by rfl) ⟨227196, by rfl⟩ : syracuseStep 2423429 = 454393) (by norm_num)
theorem B5454485 : Blo 1615006 5454485 := bbase (se 6 (by rfl) ⟨127839, by rfl⟩ : syracuseStep 5454485 = 255679) (by norm_num)
theorem B2423453 : Blo 1615006 2423453 := bbase (se 3 (by rfl) ⟨454397, by rfl⟩ : syracuseStep 2423453 = 908795) (by norm_num)
theorem B1817257 : Blo 1615006 1817257 := bbase (se 2 (by rfl) ⟨681471, by rfl⟩ : syracuseStep 1817257 = 1362943) (by norm_num)
theorem B2423477 : Blo 1615006 2423477 := bbase (se 5 (by rfl) ⟨113600, by rfl⟩ : syracuseStep 2423477 = 227201) (by norm_num)
theorem B2726581 : Blo 1615006 2726581 := bbase (se 5 (by rfl) ⟨127808, by rfl⟩ : syracuseStep 2726581 = 255617) (by norm_num)
theorem B3635909 : Blo 1615006 3635909 := bbase (se 4 (by rfl) ⟨340866, by rfl⟩ : syracuseStep 3635909 = 681733) (by norm_num)
theorem B1817293 : Blo 1615006 1817293 := bbase (se 3 (by rfl) ⟨340742, by rfl⟩ : syracuseStep 1817293 = 681485) (by norm_num)
theorem B2423501 : Blo 1615006 2423501 := bbase (se 3 (by rfl) ⟨454406, by rfl⟩ : syracuseStep 2423501 = 908813) (by norm_num)
theorem B2423525 : Blo 1615006 2423525 := bbase (se 4 (by rfl) ⟨227205, by rfl⟩ : syracuseStep 2423525 = 454411) (by norm_num)
theorem B1817329 : Blo 1615006 1817329 := bbase (se 2 (by rfl) ⟨681498, by rfl⟩ : syracuseStep 1817329 = 1362997) (by norm_num)
theorem B6904565 : Blo 1615006 6904565 := bbase (se 5 (by rfl) ⟨323651, by rfl⟩ : syracuseStep 6904565 = 647303) (by norm_num)
theorem B2423549 : Blo 1615006 2423549 := bbase (se 3 (by rfl) ⟨454415, by rfl⟩ : syracuseStep 2423549 = 908831) (by norm_num)
theorem B2726669 : Blo 1615006 2726669 := bbase (se 3 (by rfl) ⟨511250, by rfl⟩ : syracuseStep 2726669 = 1022501) (by norm_num)
theorem B3635981 : Blo 1615006 3635981 := bbase (se 3 (by rfl) ⟨681746, by rfl⟩ : syracuseStep 3635981 = 1363493) (by norm_num)
theorem B1817365 : Blo 1615006 1817365 := bbase (se 6 (by rfl) ⟨42594, by rfl⟩ : syracuseStep 1817365 = 85189) (by norm_num)
theorem B2423573 : Blo 1615006 2423573 := bbase (se 6 (by rfl) ⟨56802, by rfl⟩ : syracuseStep 2423573 = 113605) (by norm_num)
theorem B2423597 : Blo 1615006 2423597 := bbase (se 3 (by rfl) ⟨454424, by rfl⟩ : syracuseStep 2423597 = 908849) (by norm_num)
theorem B1817401 : Blo 1615006 1817401 := bbase (se 2 (by rfl) ⟨681525, by rfl⟩ : syracuseStep 1817401 = 1363051) (by norm_num)
theorem B1940285 : Blo 1615006 1940285 := bbase (se 3 (by rfl) ⟨363803, by rfl⟩ : syracuseStep 1940285 = 727607) (by norm_num)
theorem B2423621 : Blo 1615006 2423621 := bbase (se 4 (by rfl) ⟨227214, by rfl⟩ : syracuseStep 2423621 = 454429) (by norm_num)
theorem B2587469 : Blo 1615006 2587469 := bbase (se 3 (by rfl) ⟨485150, by rfl⟩ : syracuseStep 2587469 = 970301) (by norm_num)
theorem B3636053 : Blo 1615006 3636053 := bbase (se 9 (by rfl) ⟨10652, by rfl⟩ : syracuseStep 3636053 = 21305) (by norm_num)
theorem B1817437 : Blo 1615006 1817437 := bbase (se 3 (by rfl) ⟨340769, by rfl⟩ : syracuseStep 1817437 = 681539) (by norm_num)
theorem B2423645 : Blo 1615006 2423645 := bbase (se 3 (by rfl) ⟨454433, by rfl⟩ : syracuseStep 2423645 = 908867) (by norm_num)
theorem B2423669 : Blo 1615006 2423669 := bbase (se 5 (by rfl) ⟨113609, by rfl⟩ : syracuseStep 2423669 = 227219) (by norm_num)
theorem B1817473 : Blo 1615006 1817473 := bbase (se 2 (by rfl) ⟨681552, by rfl⟩ : syracuseStep 1817473 = 1363105) (by norm_num)
theorem B2423693 : Blo 1615006 2423693 := bbase (se 3 (by rfl) ⟨454442, by rfl⟩ : syracuseStep 2423693 = 908885) (by norm_num)
theorem B2726797 : Blo 1615006 2726797 := bbase (se 3 (by rfl) ⟨511274, by rfl⟩ : syracuseStep 2726797 = 1022549) (by norm_num)
theorem B3636125 : Blo 1615006 3636125 := bbase (se 3 (by rfl) ⟨681773, by rfl⟩ : syracuseStep 3636125 = 1363547) (by norm_num)
theorem B1817509 : Blo 1615006 1817509 := bbase (se 4 (by rfl) ⟨170391, by rfl⟩ : syracuseStep 1817509 = 340783) (by norm_num)
theorem B2423717 : Blo 1615006 2423717 := bbase (se 4 (by rfl) ⟨227223, by rfl⟩ : syracuseStep 2423717 = 454447) (by norm_num)
theorem B2423741 : Blo 1615006 2423741 := bbase (se 3 (by rfl) ⟨454451, by rfl⟩ : syracuseStep 2423741 = 908903) (by norm_num)
theorem B1817545 : Blo 1615006 1817545 := bbase (se 2 (by rfl) ⟨681579, by rfl⟩ : syracuseStep 1817545 = 1363159) (by norm_num)
theorem B2423765 : Blo 1615006 2423765 := bbase (se 7 (by rfl) ⟨28403, by rfl⟩ : syracuseStep 2423765 = 56807) (by norm_num)
theorem B2726885 : Blo 1615006 2726885 := bbase (se 4 (by rfl) ⟨255645, by rfl⟩ : syracuseStep 2726885 = 511291) (by norm_num)
theorem B3636197 : Blo 1615006 3636197 := bbase (se 4 (by rfl) ⟨340893, by rfl⟩ : syracuseStep 3636197 = 681787) (by norm_num)
theorem B1817581 : Blo 1615006 1817581 := bbase (se 3 (by rfl) ⟨340796, by rfl⟩ : syracuseStep 1817581 = 681593) (by norm_num)
theorem B2423789 : Blo 1615006 2423789 := bbase (se 3 (by rfl) ⟨454460, by rfl⟩ : syracuseStep 2423789 = 908921) (by norm_num)
theorem B3734525 : Blo 1615006 3734525 := bbase (se 3 (by rfl) ⟨700223, by rfl⟩ : syracuseStep 3734525 = 1400447) (by norm_num)
theorem B2423813 : Blo 1615006 2423813 := bbase (se 4 (by rfl) ⟨227232, by rfl⟩ : syracuseStep 2423813 = 454465) (by norm_num)
theorem B1817617 : Blo 1615006 1817617 := bbase (se 2 (by rfl) ⟨681606, by rfl⟩ : syracuseStep 1817617 = 1363213) (by norm_num)
theorem B2423837 : Blo 1615006 2423837 := bbase (se 3 (by rfl) ⟨454469, by rfl⟩ : syracuseStep 2423837 = 908939) (by norm_num)
theorem B3636269 : Blo 1615006 3636269 := bbase (se 3 (by rfl) ⟨681800, by rfl⟩ : syracuseStep 3636269 = 1363601) (by norm_num)
theorem B1817653 : Blo 1615006 1817653 := bbase (se 5 (by rfl) ⟨85202, by rfl⟩ : syracuseStep 1817653 = 170405) (by norm_num)
theorem B2423861 : Blo 1615006 2423861 := bbase (se 5 (by rfl) ⟨113618, by rfl⟩ : syracuseStep 2423861 = 227237) (by norm_num)
theorem B5454917 : Blo 1615006 5454917 := bbase (se 4 (by rfl) ⟨511398, by rfl⟩ : syracuseStep 5454917 = 1022797) (by norm_num)
theorem B2423885 : Blo 1615006 2423885 := bbase (se 3 (by rfl) ⟨454478, by rfl⟩ : syracuseStep 2423885 = 908957) (by norm_num)
theorem B1817689 : Blo 1615006 1817689 := bbase (se 2 (by rfl) ⟨681633, by rfl⟩ : syracuseStep 1817689 = 1363267) (by norm_num)
theorem B6134885 : Blo 1615006 6134885 := bbase (se 4 (by rfl) ⟨575145, by rfl⟩ : syracuseStep 6134885 = 1150291) (by norm_num)
theorem B2423909 : Blo 1615006 2423909 := bbase (se 4 (by rfl) ⟨227241, by rfl⟩ : syracuseStep 2423909 = 454483) (by norm_num)
theorem B2727013 : Blo 1615006 2727013 := bbase (se 4 (by rfl) ⟨255657, by rfl⟩ : syracuseStep 2727013 = 511315) (by norm_num)
theorem B1940593 : Blo 1615006 1940593 := bbase (se 2 (by rfl) ⟨727722, by rfl⟩ : syracuseStep 1940593 = 1455445) (by norm_num)
theorem B3636341 : Blo 1615006 3636341 := bbase (se 5 (by rfl) ⟨170453, by rfl⟩ : syracuseStep 3636341 = 340907) (by norm_num)
theorem B4602997 : Blo 1615006 4602997 := bbase (se 5 (by rfl) ⟨215765, by rfl⟩ : syracuseStep 4602997 = 431531) (by norm_num)
theorem B1817725 : Blo 1615006 1817725 := bbase (se 3 (by rfl) ⟨340823, by rfl⟩ : syracuseStep 1817725 = 681647) (by norm_num)
theorem B2423933 : Blo 1615006 2423933 := bbase (se 3 (by rfl) ⟨454487, by rfl⟩ : syracuseStep 2423933 = 908975) (by norm_num)
theorem B2423957 : Blo 1615006 2423957 := bbase (se 6 (by rfl) ⟨56811, by rfl⟩ : syracuseStep 2423957 = 113623) (by norm_num)
theorem B1817761 : Blo 1615006 1817761 := bbase (se 2 (by rfl) ⟨681660, by rfl⟩ : syracuseStep 1817761 = 1363321) (by norm_num)
theorem B2423981 : Blo 1615006 2423981 := bbase (se 3 (by rfl) ⟨454496, by rfl⟩ : syracuseStep 2423981 = 908993) (by norm_num)
theorem B2727101 : Blo 1615006 2727101 := bbase (se 3 (by rfl) ⟨511331, by rfl⟩ : syracuseStep 2727101 = 1022663) (by norm_num)
theorem B3636413 : Blo 1615006 3636413 := bbase (se 3 (by rfl) ⟨681827, by rfl⟩ : syracuseStep 3636413 = 1363655) (by norm_num)
theorem B1817797 : Blo 1615006 1817797 := bbase (se 4 (by rfl) ⟨170418, by rfl⟩ : syracuseStep 1817797 = 340837) (by norm_num)
theorem B2424005 : Blo 1615006 2424005 := bbase (se 4 (by rfl) ⟨227250, by rfl⟩ : syracuseStep 2424005 = 454501) (by norm_num)
theorem B3366101 : Blo 1615006 3366101 := bbase (se 7 (by rfl) ⟨39446, by rfl⟩ : syracuseStep 3366101 = 78893) (by norm_num)
theorem B2424029 : Blo 1615006 2424029 := bbase (se 3 (by rfl) ⟨454505, by rfl⟩ : syracuseStep 2424029 = 909011) (by norm_num)
theorem B2301157 : Blo 1615006 2301157 := bbase (se 4 (by rfl) ⟨215733, by rfl⟩ : syracuseStep 2301157 = 431467) (by norm_num)
theorem B1817833 : Blo 1615006 1817833 := bbase (se 2 (by rfl) ⟨681687, by rfl⟩ : syracuseStep 1817833 = 1363375) (by norm_num)
theorem B2424053 : Blo 1615006 2424053 := bbase (se 5 (by rfl) ⟨113627, by rfl⟩ : syracuseStep 2424053 = 227255) (by norm_num)
theorem B7765253 : Blo 1615006 7765253 := bbase (se 4 (by rfl) ⟨727992, by rfl⟩ : syracuseStep 7765253 = 1455985) (by norm_num)
theorem B3636485 : Blo 1615006 3636485 := bbase (se 4 (by rfl) ⟨340920, by rfl⟩ : syracuseStep 3636485 = 681841) (by norm_num)
theorem B1817869 : Blo 1615006 1817869 := bbase (se 3 (by rfl) ⟨340850, by rfl⟩ : syracuseStep 1817869 = 681701) (by norm_num)
theorem B2424077 : Blo 1615006 2424077 := bbase (se 3 (by rfl) ⟨454514, by rfl⟩ : syracuseStep 2424077 = 909029) (by norm_num)
theorem B2424101 : Blo 1615006 2424101 := bbase (se 4 (by rfl) ⟨227259, by rfl⟩ : syracuseStep 2424101 = 454519) (by norm_num)
theorem B1817905 : Blo 1615006 1817905 := bbase (se 2 (by rfl) ⟨681714, by rfl⟩ : syracuseStep 1817905 = 1363429) (by norm_num)
theorem B4914485 : Blo 1615006 4914485 := bbase (se 5 (by rfl) ⟨230366, by rfl⟩ : syracuseStep 4914485 = 460733) (by norm_num)
theorem B2424125 : Blo 1615006 2424125 := bbase (se 3 (by rfl) ⟨454523, by rfl⟩ : syracuseStep 2424125 = 909047) (by norm_num)
theorem B2727229 : Blo 1615006 2727229 := bbase (se 3 (by rfl) ⟨511355, by rfl⟩ : syracuseStep 2727229 = 1022711) (by norm_num)
theorem B1940809 : Blo 1615006 1940809 := bbase (se 2 (by rfl) ⟨727803, by rfl⟩ : syracuseStep 1940809 = 1455607) (by norm_num)
theorem B3636557 : Blo 1615006 3636557 := bbase (se 3 (by rfl) ⟨681854, by rfl⟩ : syracuseStep 3636557 = 1363709) (by norm_num)
theorem B1817941 : Blo 1615006 1817941 := bbase (se 11 (by rfl) ⟨1331, by rfl⟩ : syracuseStep 1817941 = 2663) (by norm_num)
theorem B2424149 : Blo 1615006 2424149 := bbase (se 11 (by rfl) ⟨1775, by rfl⟩ : syracuseStep 2424149 = 3551) (by norm_num)
theorem B4914533 : Blo 1615006 4914533 := bbase (se 4 (by rfl) ⟨460737, by rfl⟩ : syracuseStep 4914533 = 921475) (by norm_num)
theorem B2424173 : Blo 1615006 2424173 := bbase (se 3 (by rfl) ⟨454532, by rfl⟩ : syracuseStep 2424173 = 909065) (by norm_num)
theorem B2588021 : Blo 1615006 2588021 := bbase (se 5 (by rfl) ⟨121313, by rfl⟩ : syracuseStep 2588021 = 242627) (by norm_num)
theorem B1817977 : Blo 1615006 1817977 := bbase (se 2 (by rfl) ⟨681741, by rfl⟩ : syracuseStep 1817977 = 1363483) (by norm_num)
theorem B6135173 : Blo 1615006 6135173 := bbase (se 4 (by rfl) ⟨575172, by rfl⟩ : syracuseStep 6135173 = 1150345) (by norm_num)
theorem B2424197 : Blo 1615006 2424197 := bbase (se 4 (by rfl) ⟨227268, by rfl⟩ : syracuseStep 2424197 = 454537) (by norm_num)
theorem B2588053 : Blo 1615006 2588053 := bbase (se 6 (by rfl) ⟨60657, by rfl⟩ : syracuseStep 2588053 = 121315) (by norm_num)
theorem B2727317 : Blo 1615006 2727317 := bbase (se 6 (by rfl) ⟨63921, by rfl⟩ : syracuseStep 2727317 = 127843) (by norm_num)
theorem B3636629 : Blo 1615006 3636629 := bbase (se 6 (by rfl) ⟨85233, by rfl⟩ : syracuseStep 3636629 = 170467) (by norm_num)
theorem B1818013 : Blo 1615006 1818013 := bbase (se 3 (by rfl) ⟨340877, by rfl⟩ : syracuseStep 1818013 = 681755) (by norm_num)
theorem B2424221 : Blo 1615006 2424221 := bbase (se 3 (by rfl) ⟨454541, by rfl⟩ : syracuseStep 2424221 = 909083) (by norm_num)
theorem B2071985 : Blo 1615006 2071985 := bbase (se 2 (by rfl) ⟨776994, by rfl⟩ : syracuseStep 2071985 = 1553989) (by norm_num)
theorem B2424245 : Blo 1615006 2424245 := bbase (se 5 (by rfl) ⟨113636, by rfl⟩ : syracuseStep 2424245 = 227273) (by norm_num)
theorem B1818049 : Blo 1615006 1818049 := bbase (se 2 (by rfl) ⟨681768, by rfl⟩ : syracuseStep 1818049 = 1363537) (by norm_num)
theorem B7765445 : Blo 1615006 7765445 := bbase (se 4 (by rfl) ⟨728010, by rfl⟩ : syracuseStep 7765445 = 1456021) (by norm_num)
theorem B2424269 : Blo 1615006 2424269 := bbase (se 3 (by rfl) ⟨454550, by rfl⟩ : syracuseStep 2424269 = 909101) (by norm_num)
theorem B3636701 : Blo 1615006 3636701 := bbase (se 3 (by rfl) ⟨681881, by rfl⟩ : syracuseStep 3636701 = 1363763) (by norm_num)
theorem B1818085 : Blo 1615006 1818085 := bbase (se 4 (by rfl) ⟨170445, by rfl⟩ : syracuseStep 1818085 = 340891) (by norm_num)
theorem B2424293 : Blo 1615006 2424293 := bbase (se 4 (by rfl) ⟨227277, by rfl⟩ : syracuseStep 2424293 = 454555) (by norm_num)
theorem B5455349 : Blo 1615006 5455349 := bbase (se 5 (by rfl) ⟨255719, by rfl⟩ : syracuseStep 5455349 = 511439) (by norm_num)
theorem B2424317 : Blo 1615006 2424317 := bbase (se 3 (by rfl) ⟨454559, by rfl⟩ : syracuseStep 2424317 = 909119) (by norm_num)
theorem B1818121 : Blo 1615006 1818121 := bbase (se 2 (by rfl) ⟨681795, by rfl⟩ : syracuseStep 1818121 = 1363591) (by norm_num)
theorem B2424341 : Blo 1615006 2424341 := bbase (se 6 (by rfl) ⟨56820, by rfl⟩ : syracuseStep 2424341 = 113641) (by norm_num)
theorem B2727445 : Blo 1615006 2727445 := bbase (se 6 (by rfl) ⟨63924, by rfl⟩ : syracuseStep 2727445 = 127849) (by norm_num)
theorem B3636773 : Blo 1615006 3636773 := bbase (se 4 (by rfl) ⟨340947, by rfl⟩ : syracuseStep 3636773 = 681895) (by norm_num)
theorem B1818157 : Blo 1615006 1818157 := bbase (se 3 (by rfl) ⟨340904, by rfl⟩ : syracuseStep 1818157 = 681809) (by norm_num)
theorem B2424365 : Blo 1615006 2424365 := bbase (se 3 (by rfl) ⟨454568, by rfl⟩ : syracuseStep 2424365 = 909137) (by norm_num)
theorem B2424389 : Blo 1615006 2424389 := bbase (se 4 (by rfl) ⟨227286, by rfl⟩ : syracuseStep 2424389 = 454573) (by norm_num)
theorem B1818193 : Blo 1615006 1818193 := bbase (se 2 (by rfl) ⟨681822, by rfl⟩ : syracuseStep 1818193 = 1363645) (by norm_num)
theorem B2424413 : Blo 1615006 2424413 := bbase (se 3 (by rfl) ⟨454577, by rfl⟩ : syracuseStep 2424413 = 909155) (by norm_num)
theorem B2727533 : Blo 1615006 2727533 := bbase (se 3 (by rfl) ⟨511412, by rfl⟩ : syracuseStep 2727533 = 1022825) (by norm_num)
theorem B3636845 : Blo 1615006 3636845 := bbase (se 3 (by rfl) ⟨681908, by rfl⟩ : syracuseStep 3636845 = 1363817) (by norm_num)
theorem B1818229 : Blo 1615006 1818229 := bbase (se 5 (by rfl) ⟨85229, by rfl⟩ : syracuseStep 1818229 = 170459) (by norm_num)
theorem B2424437 : Blo 1615006 2424437 := bbase (se 5 (by rfl) ⟨113645, by rfl⟩ : syracuseStep 2424437 = 227291) (by norm_num)
theorem B1941121 : Blo 1615006 1941121 := bbase (se 2 (by rfl) ⟨727920, by rfl⟩ : syracuseStep 1941121 = 1455841) (by norm_num)
theorem B8183429 : Blo 1615006 8183429 := bbase (se 4 (by rfl) ⟨767196, by rfl⟩ : syracuseStep 8183429 = 1534393) (by norm_num)
theorem B2424461 : Blo 1615006 2424461 := bbase (se 3 (by rfl) ⟨454586, by rfl⟩ : syracuseStep 2424461 = 909173) (by norm_num)
theorem B1818265 : Blo 1615006 1818265 := bbase (se 2 (by rfl) ⟨681849, by rfl⟩ : syracuseStep 1818265 = 1363699) (by norm_num)
theorem B2424485 : Blo 1615006 2424485 := bbase (se 4 (by rfl) ⟨227295, by rfl⟩ : syracuseStep 2424485 = 454591) (by norm_num)
theorem B3636917 : Blo 1615006 3636917 := bbase (se 5 (by rfl) ⟨170480, by rfl⟩ : syracuseStep 3636917 = 340961) (by norm_num)
theorem B1818301 : Blo 1615006 1818301 := bbase (se 3 (by rfl) ⟨340931, by rfl⟩ : syracuseStep 1818301 = 681863) (by norm_num)
theorem B2424509 : Blo 1615006 2424509 := bbase (se 3 (by rfl) ⟨454595, by rfl⟩ : syracuseStep 2424509 = 909191) (by norm_num)
theorem B2424533 : Blo 1615006 2424533 := bbase (se 7 (by rfl) ⟨28412, by rfl⟩ : syracuseStep 2424533 = 56825) (by norm_num)
theorem B1818337 : Blo 1615006 1818337 := bbase (se 2 (by rfl) ⟨681876, by rfl⟩ : syracuseStep 1818337 = 1363753) (by norm_num)
theorem B2424557 : Blo 1615006 2424557 := bbase (se 3 (by rfl) ⟨454604, by rfl⟩ : syracuseStep 2424557 = 909209) (by norm_num)
theorem B2727661 : Blo 1615006 2727661 := bbase (se 3 (by rfl) ⟨511436, by rfl⟩ : syracuseStep 2727661 = 1022873) (by norm_num)
theorem B3636989 : Blo 1615006 3636989 := bbase (se 3 (by rfl) ⟨681935, by rfl⟩ : syracuseStep 3636989 = 1363871) (by norm_num)
theorem B1818373 : Blo 1615006 1818373 := bbase (se 4 (by rfl) ⟨170472, by rfl⟩ : syracuseStep 1818373 = 340945) (by norm_num)
theorem B2424581 : Blo 1615006 2424581 := bbase (se 4 (by rfl) ⟨227304, by rfl⟩ : syracuseStep 2424581 = 454609) (by norm_num)
theorem B2424605 : Blo 1615006 2424605 := bbase (se 3 (by rfl) ⟨454613, by rfl⟩ : syracuseStep 2424605 = 909227) (by norm_num)
theorem B1818409 : Blo 1615006 1818409 := bbase (se 2 (by rfl) ⟨681903, by rfl⟩ : syracuseStep 1818409 = 1363807) (by norm_num)
theorem B2424629 : Blo 1615006 2424629 := bbase (se 5 (by rfl) ⟨113654, by rfl⟩ : syracuseStep 2424629 = 227309) (by norm_num)
theorem B2727749 : Blo 1615006 2727749 := bbase (se 4 (by rfl) ⟨255726, by rfl⟩ : syracuseStep 2727749 = 511453) (by norm_num)
theorem B3637061 : Blo 1615006 3637061 := bbase (se 4 (by rfl) ⟨340974, by rfl⟩ : syracuseStep 3637061 = 681949) (by norm_num)
theorem B1818445 : Blo 1615006 1818445 := bbase (se 3 (by rfl) ⟨340958, by rfl⟩ : syracuseStep 1818445 = 681917) (by norm_num)
theorem B2424653 : Blo 1615006 2424653 := bbase (se 3 (by rfl) ⟨454622, by rfl⟩ : syracuseStep 2424653 = 909245) (by norm_num)
theorem B2424677 : Blo 1615006 2424677 := bbase (se 4 (by rfl) ⟨227313, by rfl⟩ : syracuseStep 2424677 = 454627) (by norm_num)
theorem B1818481 : Blo 1615006 1818481 := bbase (se 2 (by rfl) ⟨681930, by rfl⟩ : syracuseStep 1818481 = 1363861) (by norm_num)
theorem B1843069 : Blo 1615006 1843069 := bbase (se 3 (by rfl) ⟨345575, by rfl⟩ : syracuseStep 1843069 = 691151) (by norm_num)
theorem B2424701 : Blo 1615006 2424701 := bbase (se 3 (by rfl) ⟨454631, by rfl⟩ : syracuseStep 2424701 = 909263) (by norm_num)
theorem B3637133 : Blo 1615006 3637133 := bbase (se 3 (by rfl) ⟨681962, by rfl⟩ : syracuseStep 3637133 = 1363925) (by norm_num)
theorem B1818517 : Blo 1615006 1818517 := bbase (se 6 (by rfl) ⟨42621, by rfl⟩ : syracuseStep 1818517 = 85243) (by norm_num)
theorem B2424725 : Blo 1615006 2424725 := bbase (se 6 (by rfl) ⟨56829, by rfl⟩ : syracuseStep 2424725 = 113659) (by norm_num)
theorem B5455781 : Blo 1615006 5455781 := bbase (se 4 (by rfl) ⟨511479, by rfl⟩ : syracuseStep 5455781 = 1022959) (by norm_num)
theorem B2424749 : Blo 1615006 2424749 := bbase (se 3 (by rfl) ⟨454640, by rfl⟩ : syracuseStep 2424749 = 909281) (by norm_num)
theorem B4145077 : Blo 1615006 4145077 := bbase (se 5 (by rfl) ⟨194300, by rfl⟩ : syracuseStep 4145077 = 388601) (by norm_num)
theorem B1818553 : Blo 1615006 1818553 := bbase (se 2 (by rfl) ⟨681957, by rfl⟩ : syracuseStep 1818553 = 1363915) (by norm_num)
theorem B2424773 : Blo 1615006 2424773 := bbase (se 4 (by rfl) ⟨227322, by rfl⟩ : syracuseStep 2424773 = 454645) (by norm_num)
theorem B2727877 : Blo 1615006 2727877 := bbase (se 4 (by rfl) ⟨255738, by rfl⟩ : syracuseStep 2727877 = 511477) (by norm_num)
theorem B3637205 : Blo 1615006 3637205 := bbase (se 7 (by rfl) ⟨42623, by rfl⟩ : syracuseStep 3637205 = 85247) (by norm_num)
theorem B3882973 : Blo 1615006 3882973 := bbase (se 3 (by rfl) ⟨728057, by rfl⟩ : syracuseStep 3882973 = 1456115) (by norm_num)
theorem B1818589 : Blo 1615006 1818589 := bbase (se 3 (by rfl) ⟨340985, by rfl⟩ : syracuseStep 1818589 = 681971) (by norm_num)
theorem B2424797 : Blo 1615006 2424797 := bbase (se 3 (by rfl) ⟨454649, by rfl⟩ : syracuseStep 2424797 = 909299) (by norm_num)
theorem B2424821 : Blo 1615006 2424821 := bbase (se 5 (by rfl) ⟨113663, by rfl⟩ : syracuseStep 2424821 = 227327) (by norm_num)
theorem B2301949 : Blo 1615006 2301949 := bbase (se 3 (by rfl) ⟨431615, by rfl⟩ : syracuseStep 2301949 = 863231) (by norm_num)
theorem B2424833 : Blo 1615006 2424833 := bstep (se 2 (by rfl) ⟨909312, by rfl⟩ : syracuseStep 2424833 = 1818625) B1818625
theorem B5455889 : Blo 1615006 5455889 := bstep (se 2 (by rfl) ⟨2045958, by rfl⟩ : syracuseStep 5455889 = 4091917) B4091917
theorem B2424851 : Blo 1615006 2424851 := bstep (se 1 (by rfl) ⟨1818638, by rfl⟩ : syracuseStep 2424851 = 3637277) B3637277
theorem B1818643 : Blo 1615006 1818643 := bstep (se 1 (by rfl) ⟨1363982, by rfl⟩ : syracuseStep 1818643 = 2727965) B2727965
theorem B5824547 : Blo 1615006 5824547 := bstep (se 1 (by rfl) ⟨4368410, by rfl⟩ : syracuseStep 5824547 = 8736821) B8736821
theorem B6135857 : Blo 1615006 6135857 := bstep (se 2 (by rfl) ⟨2300946, by rfl⟩ : syracuseStep 6135857 = 4601893) B4601893
theorem B2727985 : Blo 1615006 2727985 := bstep (se 2 (by rfl) ⟨1022994, by rfl⟩ : syracuseStep 2727985 = 2045989) B2045989
theorem B2424881 : Blo 1615006 2424881 := bstep (se 2 (by rfl) ⟨909330, by rfl⟩ : syracuseStep 2424881 = 1818661) B1818661
theorem B53157941 : Blo 1615006 53157941 := bstep (se 5 (by rfl) ⟨2491778, by rfl⟩ : syracuseStep 53157941 = 4983557) B4983557
theorem B2424899 : Blo 1615006 2424899 := bstep (se 1 (by rfl) ⟨1818674, by rfl⟩ : syracuseStep 2424899 = 3637349) B3637349
theorem B2728019 : Blo 1615006 2728019 := bstep (se 1 (by rfl) ⟨2046014, by rfl⟩ : syracuseStep 2728019 = 4092029) B4092029
theorem B2424929 : Blo 1615006 2424929 := bstep (se 2 (by rfl) ⟨909348, by rfl⟩ : syracuseStep 2424929 = 1818697) B1818697
theorem B39321713 : Blo 1615006 39321713 := bstep (se 2 (by rfl) ⟨14745642, by rfl⟩ : syracuseStep 39321713 = 29491285) B29491285
theorem B2424947 : Blo 1615006 2424947 := bstep (se 1 (by rfl) ⟨1818710, by rfl⟩ : syracuseStep 2424947 = 3637421) B3637421
theorem B2424977 : Blo 1615006 2424977 := bstep (se 2 (by rfl) ⟨909366, by rfl⟩ : syracuseStep 2424977 = 1818733) B1818733
theorem B2424995 : Blo 1615006 2424995 := bstep (se 1 (by rfl) ⟨1818746, by rfl⟩ : syracuseStep 2424995 = 3637493) B3637493
theorem B1818787 : Blo 1615006 1818787 := bstep (se 1 (by rfl) ⟨1364090, by rfl⟩ : syracuseStep 1818787 = 2728181) B2728181
theorem B2425025 : Blo 1615006 2425025 := bstep (se 2 (by rfl) ⟨909384, by rfl⟩ : syracuseStep 2425025 = 1818769) B1818769
theorem B3637457 : Blo 1615006 3637457 := bstep (se 2 (by rfl) ⟨1364046, by rfl⟩ : syracuseStep 3637457 = 2728093) B2728093
theorem B2728147 : Blo 1615006 2728147 := bstep (se 1 (by rfl) ⟨2046110, by rfl⟩ : syracuseStep 2728147 = 4092221) B4092221
theorem B2425043 : Blo 1615006 2425043 := bstep (se 1 (by rfl) ⟨1818782, by rfl⟩ : syracuseStep 2425043 = 3637565) B3637565
theorem B2302177 : Blo 1615006 2302177 := bstep (se 2 (by rfl) ⟨863316, by rfl⟩ : syracuseStep 2302177 = 1726633) B1726633
theorem B3637475 : Blo 1615006 3637475 := bstep (se 1 (by rfl) ⟨2728106, by rfl⟩ : syracuseStep 3637475 = 5456213) B5456213
theorem B2425073 : Blo 1615006 2425073 := bstep (se 2 (by rfl) ⟨909402, by rfl⟩ : syracuseStep 2425073 = 1818805) B1818805
theorem B2425091 : Blo 1615006 2425091 := bstep (se 1 (by rfl) ⟨1818818, by rfl⟩ : syracuseStep 2425091 = 3637637) B3637637
theorem B8184077 : Blo 1615006 8184077 := bstep (se 3 (by rfl) ⟨1534514, by rfl⟩ : syracuseStep 8184077 = 3069029) B3069029
theorem B2425121 : Blo 1615006 2425121 := bstep (se 2 (by rfl) ⟨909420, by rfl⟩ : syracuseStep 2425121 = 1818841) B1818841
theorem B1843507 : Blo 1615006 1843507 := bstep (se 1 (by rfl) ⟨1382630, by rfl⟩ : syracuseStep 1843507 = 2765261) B2765261
theorem B2425139 : Blo 1615006 2425139 := bstep (se 1 (by rfl) ⟨1818854, by rfl⟩ : syracuseStep 2425139 = 3637709) B3637709
theorem B1818931 : Blo 1615006 1818931 := bstep (se 1 (by rfl) ⟨1364198, by rfl⟩ : syracuseStep 1818931 = 2728397) B2728397
theorem B2302273 : Blo 1615006 2302273 := bstep (se 2 (by rfl) ⟨863352, by rfl⟩ : syracuseStep 2302273 = 1726705) B1726705
theorem B4792643 : Blo 1615006 4792643 := bstep (se 1 (by rfl) ⟨3594482, by rfl⟩ : syracuseStep 4792643 = 7188965) B7188965
theorem B2425169 : Blo 1615006 2425169 := bstep (se 2 (by rfl) ⟨909438, by rfl⟩ : syracuseStep 2425169 = 1818877) B1818877
theorem B2728289 : Blo 1615006 2728289 := bstep (se 2 (by rfl) ⟨1023108, by rfl⟩ : syracuseStep 2728289 = 2046217) B2046217
theorem B2425187 : Blo 1615006 2425187 := bstep (se 1 (by rfl) ⟨1818890, by rfl⟩ : syracuseStep 2425187 = 3637781) B3637781
theorem B12271985 : Blo 1615006 12271985 := bstep (se 2 (by rfl) ⟨4601994, by rfl⟩ : syracuseStep 12271985 = 9203989) B9203989
theorem B4604273 : Blo 1615006 4604273 := bstep (se 2 (by rfl) ⟨1726602, by rfl⟩ : syracuseStep 4604273 = 3453205) B3453205
theorem B1843571 : Blo 1615006 1843571 := bstep (se 1 (by rfl) ⟨1382678, by rfl⟩ : syracuseStep 1843571 = 2765357) B2765357
theorem B2425217 : Blo 1615006 2425217 := bstep (se 2 (by rfl) ⟨909456, by rfl⟩ : syracuseStep 2425217 = 1818913) B1818913
theorem B2589059 : Blo 1615006 2589059 := bstep (se 1 (by rfl) ⟨1941794, by rfl⟩ : syracuseStep 2589059 = 3883589) B3883589
theorem B2425235 : Blo 1615006 2425235 := bstep (se 1 (by rfl) ⟨1818926, by rfl⟩ : syracuseStep 2425235 = 3637853) B3637853
theorem B2425265 : Blo 1615006 2425265 := bstep (se 2 (by rfl) ⟨909474, by rfl⟩ : syracuseStep 2425265 = 1818949) B1818949
theorem B2425283 : Blo 1615006 2425283 := bstep (se 1 (by rfl) ⟨1818962, by rfl⟩ : syracuseStep 2425283 = 3637925) B3637925
theorem B1819075 : Blo 1615006 1819075 := bstep (se 1 (by rfl) ⟨1364306, by rfl⟩ : syracuseStep 1819075 = 2728613) B2728613
theorem B2728417 : Blo 1615006 2728417 := bstep (se 2 (by rfl) ⟨1023156, by rfl⟩ : syracuseStep 2728417 = 2046313) B2046313
theorem B2425313 : Blo 1615006 2425313 := bstep (se 2 (by rfl) ⟨909492, by rfl⟩ : syracuseStep 2425313 = 1818985) B1818985
theorem B22118897 : Blo 1615006 22118897 := bstep (se 2 (by rfl) ⟨8294586, by rfl⟩ : syracuseStep 22118897 = 16589173) B16589173
theorem B3277297 : Blo 1615006 3277297 := bstep (se 2 (by rfl) ⟨1228986, by rfl⟩ : syracuseStep 3277297 = 2457973) B2457973
theorem B3637745 : Blo 1615006 3637745 := bstep (se 2 (by rfl) ⟨1364154, by rfl⟩ : syracuseStep 3637745 = 2728309) B2728309
theorem B2425331 : Blo 1615006 2425331 := bstep (se 1 (by rfl) ⟨1818998, by rfl⟩ : syracuseStep 2425331 = 3637997) B3637997
theorem B3637763 : Blo 1615006 3637763 := bstep (se 1 (by rfl) ⟨2728322, by rfl⟩ : syracuseStep 3637763 = 5456645) B5456645
theorem B2728451 : Blo 1615006 2728451 := bstep (se 1 (by rfl) ⟨2046338, by rfl⟩ : syracuseStep 2728451 = 4092677) B4092677
theorem B9200141 : Blo 1615006 9200141 := bstep (se 3 (by rfl) ⟨1725026, by rfl⟩ : syracuseStep 9200141 = 3450053) B3450053
theorem B2425361 : Blo 1615006 2425361 := bstep (se 2 (by rfl) ⟨909510, by rfl⟩ : syracuseStep 2425361 = 1819021) B1819021
theorem B2425379 : Blo 1615006 2425379 := bstep (se 1 (by rfl) ⟨1819034, by rfl⟩ : syracuseStep 2425379 = 3638069) B3638069
theorem B5456429 : Blo 1615006 5456429 := bstep (se 3 (by rfl) ⟨1023080, by rfl⟩ : syracuseStep 5456429 = 2046161) B2046161
theorem B3277361 : Blo 1615006 3277361 := bstep (se 2 (by rfl) ⟨1229010, by rfl⟩ : syracuseStep 3277361 = 2458021) B2458021
theorem B2425409 : Blo 1615006 2425409 := bstep (se 2 (by rfl) ⟨909528, by rfl⟩ : syracuseStep 2425409 = 1819057) B1819057
theorem B2425427 : Blo 1615006 2425427 := bstep (se 1 (by rfl) ⟨1819070, by rfl⟩ : syracuseStep 2425427 = 3638141) B3638141
theorem B2589283 : Blo 1615006 2589283 := bstep (se 1 (by rfl) ⟨1941962, by rfl⟩ : syracuseStep 2589283 = 3883925) B3883925
theorem B5456483 : Blo 1615006 5456483 := bstep (se 1 (by rfl) ⟨4092362, by rfl⟩ : syracuseStep 5456483 = 8184725) B8184725
theorem B4366961 : Blo 1615006 4366961 := bstep (se 2 (by rfl) ⟨1637610, by rfl⟩ : syracuseStep 4366961 = 3275221) B3275221
theorem B2425457 : Blo 1615006 2425457 := bstep (se 2 (by rfl) ⟨909546, by rfl⟩ : syracuseStep 2425457 = 1819093) B1819093
theorem B2728579 : Blo 1615006 2728579 := bstep (se 1 (by rfl) ⟨2046434, by rfl⟩ : syracuseStep 2728579 = 4092869) B4092869
theorem B2425475 : Blo 1615006 2425475 := bstep (se 1 (by rfl) ⟨1819106, by rfl⟩ : syracuseStep 2425475 = 3638213) B3638213
theorem B4088465 : Blo 1615006 4088465 := bstep (se 2 (by rfl) ⟨1533174, by rfl⟩ : syracuseStep 4088465 = 3066349) B3066349
theorem B2425505 : Blo 1615006 2425505 := bstep (se 2 (by rfl) ⟨909564, by rfl⟩ : syracuseStep 2425505 = 1819129) B1819129
theorem B10355363 : Blo 1615006 10355363 := bstep (se 1 (by rfl) ⟨7766522, by rfl⟩ : syracuseStep 10355363 = 15533045) B15533045
theorem B4088515 : Blo 1615006 4088515 := bstep (se 1 (by rfl) ⟨3066386, by rfl⟩ : syracuseStep 4088515 = 6132773) B6132773
theorem B33170147 : Blo 1615006 33170147 := bstep (se 1 (by rfl) ⟨24877610, by rfl⟩ : syracuseStep 33170147 = 49755221) B49755221
theorem B4367089 : Blo 1615006 4367089 := bstep (se 2 (by rfl) ⟨1637658, by rfl⟩ : syracuseStep 4367089 = 3275317) B3275317
theorem B3638033 : Blo 1615006 3638033 := bstep (se 2 (by rfl) ⟨1364262, by rfl⟩ : syracuseStep 3638033 = 2728525) B2728525
theorem B3638051 : Blo 1615006 3638051 := bstep (se 1 (by rfl) ⟨2728538, by rfl⟩ : syracuseStep 3638051 = 5457077) B5457077
theorem B4088657 : Blo 1615006 4088657 := bstep (se 2 (by rfl) ⟨1533246, by rfl⟩ : syracuseStep 4088657 = 3066493) B3066493
theorem B5456753 : Blo 1615006 5456753 := bstep (se 2 (by rfl) ⟨2046282, by rfl⟩ : syracuseStep 5456753 = 4092565) B4092565
theorem B4916177 : Blo 1615006 4916177 := bstep (se 2 (by rfl) ⟨1843566, by rfl⟩ : syracuseStep 4916177 = 3687133) B3687133
theorem B8176625 : Blo 1615006 8176625 := bstep (se 2 (by rfl) ⟨3066234, by rfl⟩ : syracuseStep 8176625 = 6132469) B6132469
theorem B3449891 : Blo 1615006 3449891 := bstep (se 1 (by rfl) ⟨2587418, by rfl⟩ : syracuseStep 3449891 = 5174837) B5174837
theorem B17712269 : Blo 1615006 17712269 := bstep (se 3 (by rfl) ⟨3321050, by rfl⟩ : syracuseStep 17712269 = 6642101) B6642101
theorem B1615011 : Blo 1615006 1615011 := bstep (se 1 (by rfl) ⟨1211258, by rfl⟩ : syracuseStep 1615011 = 2422517) B2422517
theorem B1615027 : Blo 1615006 1615027 := bstep (se 1 (by rfl) ⟨1211270, by rfl⟩ : syracuseStep 1615027 = 2422541) B2422541
theorem B1615043 : Blo 1615006 1615043 := bstep (se 1 (by rfl) ⟨1211282, by rfl⟩ : syracuseStep 1615043 = 2422565) B2422565
theorem B1615059 : Blo 1615006 1615059 := bstep (se 1 (by rfl) ⟨1211294, by rfl⟩ : syracuseStep 1615059 = 2422589) B2422589
theorem B1615075 : Blo 1615006 1615075 := bstep (se 1 (by rfl) ⟨1211306, by rfl⟩ : syracuseStep 1615075 = 2422613) B2422613
theorem B1615091 : Blo 1615006 1615091 := bstep (se 1 (by rfl) ⟨1211318, by rfl⟩ : syracuseStep 1615091 = 2422637) B2422637
theorem B1615107 : Blo 1615006 1615107 := bstep (se 1 (by rfl) ⟨1211330, by rfl⟩ : syracuseStep 1615107 = 2422661) B2422661
theorem B1615123 : Blo 1615006 1615123 := bstep (se 1 (by rfl) ⟨1211342, by rfl⟩ : syracuseStep 1615123 = 2422685) B2422685
theorem B1615139 : Blo 1615006 1615139 := bstep (se 1 (by rfl) ⟨1211354, by rfl⟩ : syracuseStep 1615139 = 2422709) B2422709
theorem B1615155 : Blo 1615006 1615155 := bstep (se 1 (by rfl) ⟨1211366, by rfl⟩ : syracuseStep 1615155 = 2422733) B2422733
theorem B1615171 : Blo 1615006 1615171 := bstep (se 1 (by rfl) ⟨1211378, by rfl⟩ : syracuseStep 1615171 = 2422757) B2422757
theorem B11060549 : Blo 1615006 11060549 := bstep (se 4 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 11060549 = 2073853) B2073853
theorem B1615187 : Blo 1615006 1615187 := bstep (se 1 (by rfl) ⟨1211390, by rfl⟩ : syracuseStep 1615187 = 2422781) B2422781
theorem B1615203 : Blo 1615006 1615203 := bstep (se 1 (by rfl) ⟨1211402, by rfl⟩ : syracuseStep 1615203 = 2422805) B2422805
theorem B1615219 : Blo 1615006 1615219 := bstep (se 1 (by rfl) ⟨1211414, by rfl⟩ : syracuseStep 1615219 = 2422829) B2422829
theorem B1615235 : Blo 1615006 1615235 := bstep (se 1 (by rfl) ⟨1211426, by rfl⟩ : syracuseStep 1615235 = 2422853) B2422853
theorem B4662659 : Blo 1615006 4662659 := bstep (se 1 (by rfl) ⟨3496994, by rfl⟩ : syracuseStep 4662659 = 6993989) B6993989
theorem B5457293 : Blo 1615006 5457293 := bstep (se 3 (by rfl) ⟨1023242, by rfl⟩ : syracuseStep 5457293 = 2046485) B2046485
theorem B1615251 : Blo 1615006 1615251 := bstep (se 1 (by rfl) ⟨1211438, by rfl⟩ : syracuseStep 1615251 = 2422877) B2422877
theorem B1615267 : Blo 1615006 1615267 := bstep (se 1 (by rfl) ⟨1211450, by rfl⟩ : syracuseStep 1615267 = 2422901) B2422901
theorem B9201073 : Blo 1615006 9201073 := bstep (se 2 (by rfl) ⟨3450402, by rfl⟩ : syracuseStep 9201073 = 6900805) B6900805
theorem B1615283 : Blo 1615006 1615283 := bstep (se 1 (by rfl) ⟨1211462, by rfl⟩ : syracuseStep 1615283 = 2422925) B2422925
theorem B1615299 : Blo 1615006 1615299 := bstep (se 1 (by rfl) ⟨1211474, by rfl⟩ : syracuseStep 1615299 = 2422949) B2422949
theorem B5457347 : Blo 1615006 5457347 := bstep (se 1 (by rfl) ⟨4093010, by rfl⟩ : syracuseStep 5457347 = 8186021) B8186021
theorem B1615315 : Blo 1615006 1615315 := bstep (se 1 (by rfl) ⟨1211486, by rfl⟩ : syracuseStep 1615315 = 2422973) B2422973
theorem B1615331 : Blo 1615006 1615331 := bstep (se 1 (by rfl) ⟨1211498, by rfl⟩ : syracuseStep 1615331 = 2422997) B2422997
theorem B6137315 : Blo 1615006 6137315 := bstep (se 1 (by rfl) ⟨4602986, by rfl⟩ : syracuseStep 6137315 = 9205973) B9205973
theorem B6137329 : Blo 1615006 6137329 := bstep (se 2 (by rfl) ⟨2301498, by rfl⟩ : syracuseStep 6137329 = 4602997) B4602997
theorem B1615347 : Blo 1615006 1615347 := bstep (se 1 (by rfl) ⟨1211510, by rfl⟩ : syracuseStep 1615347 = 2423021) B2423021
theorem B1615363 : Blo 1615006 1615363 := bstep (se 1 (by rfl) ⟨1211522, by rfl⟩ : syracuseStep 1615363 = 2423045) B2423045
theorem B1615379 : Blo 1615006 1615379 := bstep (se 1 (by rfl) ⟨1211534, by rfl⟩ : syracuseStep 1615379 = 2423069) B2423069
theorem B1615395 : Blo 1615006 1615395 := bstep (se 1 (by rfl) ⟨1211546, by rfl⟩ : syracuseStep 1615395 = 2423093) B2423093
theorem B1615411 : Blo 1615006 1615411 := bstep (se 1 (by rfl) ⟨1211558, by rfl⟩ : syracuseStep 1615411 = 2423117) B2423117
theorem B1615427 : Blo 1615006 1615427 := bstep (se 1 (by rfl) ⟨1211570, by rfl⟩ : syracuseStep 1615427 = 2423141) B2423141
theorem B1615443 : Blo 1615006 1615443 := bstep (se 1 (by rfl) ⟨1211582, by rfl⟩ : syracuseStep 1615443 = 2423165) B2423165
theorem B13796963 : Blo 1615006 13796963 := bstep (se 1 (by rfl) ⟨10347722, by rfl⟩ : syracuseStep 13796963 = 20695445) B20695445
theorem B1615459 : Blo 1615006 1615459 := bstep (se 1 (by rfl) ⟨1211594, by rfl⟩ : syracuseStep 1615459 = 2423189) B2423189
theorem B8636003 : Blo 1615006 8636003 := bstep (se 1 (by rfl) ⟨6477002, by rfl⟩ : syracuseStep 8636003 = 12954005) B12954005
theorem B5826161 : Blo 1615006 5826161 := bstep (se 2 (by rfl) ⟨2184810, by rfl⟩ : syracuseStep 5826161 = 4369621) B4369621
theorem B1615475 : Blo 1615006 1615475 := bstep (se 1 (by rfl) ⟨1211606, by rfl⟩ : syracuseStep 1615475 = 2423213) B2423213
theorem B1615491 : Blo 1615006 1615491 := bstep (se 1 (by rfl) ⟨1211618, by rfl⟩ : syracuseStep 1615491 = 2423237) B2423237
theorem B1615507 : Blo 1615006 1615507 := bstep (se 1 (by rfl) ⟨1211630, by rfl⟩ : syracuseStep 1615507 = 2423261) B2423261
theorem B1615523 : Blo 1615006 1615523 := bstep (se 1 (by rfl) ⟨1211642, by rfl⟩ : syracuseStep 1615523 = 2423285) B2423285
theorem B1615539 : Blo 1615006 1615539 := bstep (se 1 (by rfl) ⟨1211654, by rfl⟩ : syracuseStep 1615539 = 2423309) B2423309
theorem B1615555 : Blo 1615006 1615555 := bstep (se 1 (by rfl) ⟨1211666, by rfl⟩ : syracuseStep 1615555 = 2423333) B2423333
theorem B4261571 : Blo 1615006 4261571 := bstep (se 1 (by rfl) ⟨3196178, by rfl⟩ : syracuseStep 4261571 = 6392357) B6392357
theorem B1615571 : Blo 1615006 1615571 := bstep (se 1 (by rfl) ⟨1211678, by rfl⟩ : syracuseStep 1615571 = 2423357) B2423357
theorem B1615587 : Blo 1615006 1615587 := bstep (se 1 (by rfl) ⟨1211690, by rfl⟩ : syracuseStep 1615587 = 2423381) B2423381
theorem B52405987 : Blo 1615006 52405987 := bstep (se 1 (by rfl) ⟨39304490, by rfl⟩ : syracuseStep 52405987 = 78608981) B78608981
theorem B4663021 : Blo 1615006 4663021 := bstep (se 3 (by rfl) ⟨874316, by rfl⟩ : syracuseStep 4663021 = 1748633) B1748633
theorem B1615603 : Blo 1615006 1615603 := bstep (se 1 (by rfl) ⟨1211702, by rfl⟩ : syracuseStep 1615603 = 2423405) B2423405
theorem B1615619 : Blo 1615006 1615619 := bstep (se 1 (by rfl) ⟨1211714, by rfl⟩ : syracuseStep 1615619 = 2423429) B2423429
theorem B1615635 : Blo 1615006 1615635 := bstep (se 1 (by rfl) ⟨1211726, by rfl⟩ : syracuseStep 1615635 = 2423453) B2423453
theorem B1615651 : Blo 1615006 1615651 := bstep (se 1 (by rfl) ⟨1211738, by rfl⟩ : syracuseStep 1615651 = 2423477) B2423477
theorem B10348337 : Blo 1615006 10348337 := bstep (se 2 (by rfl) ⟨3880626, by rfl⟩ : syracuseStep 10348337 = 7761253) B7761253
theorem B4089649 : Blo 1615006 4089649 := bstep (se 2 (by rfl) ⟨1533618, by rfl⟩ : syracuseStep 4089649 = 3067237) B3067237
theorem B1615667 : Blo 1615006 1615667 := bstep (se 1 (by rfl) ⟨1211750, by rfl⟩ : syracuseStep 1615667 = 2423501) B2423501
theorem B1615683 : Blo 1615006 1615683 := bstep (se 1 (by rfl) ⟨1211762, by rfl⟩ : syracuseStep 1615683 = 2423525) B2423525
theorem B1615699 : Blo 1615006 1615699 := bstep (se 1 (by rfl) ⟨1211774, by rfl⟩ : syracuseStep 1615699 = 2423549) B2423549
theorem B1615715 : Blo 1615006 1615715 := bstep (se 1 (by rfl) ⟨1211786, by rfl⟩ : syracuseStep 1615715 = 2423573) B2423573
theorem B3450737 : Blo 1615006 3450737 := bstep (se 2 (by rfl) ⟨1294026, by rfl⟩ : syracuseStep 3450737 = 2588053) B2588053
theorem B1615731 : Blo 1615006 1615731 := bstep (se 1 (by rfl) ⟨1211798, by rfl⟩ : syracuseStep 1615731 = 2423597) B2423597
theorem B1615747 : Blo 1615006 1615747 := bstep (se 1 (by rfl) ⟨1211810, by rfl⟩ : syracuseStep 1615747 = 2423621) B2423621
theorem B1615763 : Blo 1615006 1615763 := bstep (se 1 (by rfl) ⟨1211822, by rfl⟩ : syracuseStep 1615763 = 2423645) B2423645
theorem B1615779 : Blo 1615006 1615779 := bstep (se 1 (by rfl) ⟨1211834, by rfl⟩ : syracuseStep 1615779 = 2423669) B2423669
theorem B1615795 : Blo 1615006 1615795 := bstep (se 1 (by rfl) ⟨1211846, by rfl⟩ : syracuseStep 1615795 = 2423693) B2423693
theorem B1615811 : Blo 1615006 1615811 := bstep (se 1 (by rfl) ⟨1211858, by rfl⟩ : syracuseStep 1615811 = 2423717) B2423717
theorem B1615827 : Blo 1615006 1615827 := bstep (se 1 (by rfl) ⟨1211870, by rfl⟩ : syracuseStep 1615827 = 2423741) B2423741
theorem B1615843 : Blo 1615006 1615843 := bstep (se 1 (by rfl) ⟨1211882, by rfl⟩ : syracuseStep 1615843 = 2423765) B2423765
theorem B1615859 : Blo 1615006 1615859 := bstep (se 1 (by rfl) ⟨1211894, by rfl⟩ : syracuseStep 1615859 = 2423789) B2423789
theorem B1615875 : Blo 1615006 1615875 := bstep (se 1 (by rfl) ⟨1211906, by rfl⟩ : syracuseStep 1615875 = 2423813) B2423813
theorem B1615891 : Blo 1615006 1615891 := bstep (se 1 (by rfl) ⟨1211918, by rfl⟩ : syracuseStep 1615891 = 2423837) B2423837
theorem B1615907 : Blo 1615006 1615907 := bstep (se 1 (by rfl) ⟨1211930, by rfl⟩ : syracuseStep 1615907 = 2423861) B2423861
theorem B1615923 : Blo 1615006 1615923 := bstep (se 1 (by rfl) ⟨1211942, by rfl⟩ : syracuseStep 1615923 = 2423885) B2423885
theorem B4089923 : Blo 1615006 4089923 := bstep (se 1 (by rfl) ⟨3067442, by rfl⟩ : syracuseStep 4089923 = 6134885) B6134885
theorem B1615939 : Blo 1615006 1615939 := bstep (se 1 (by rfl) ⟨1211954, by rfl⟩ : syracuseStep 1615939 = 2423909) B2423909
theorem B1615955 : Blo 1615006 1615955 := bstep (se 1 (by rfl) ⟨1211966, by rfl⟩ : syracuseStep 1615955 = 2423933) B2423933
theorem B1615971 : Blo 1615006 1615971 := bstep (se 1 (by rfl) ⟨1211978, by rfl⟩ : syracuseStep 1615971 = 2423957) B2423957
theorem B3885155 : Blo 1615006 3885155 := bstep (se 1 (by rfl) ⟨2913866, by rfl⟩ : syracuseStep 3885155 = 5827733) B5827733
theorem B15534193 : Blo 1615006 15534193 := bstep (se 2 (by rfl) ⟨5825322, by rfl⟩ : syracuseStep 15534193 = 11650645) B11650645
theorem B40962161 : Blo 1615006 40962161 := bstep (se 2 (by rfl) ⟨15360810, by rfl⟩ : syracuseStep 40962161 = 30721621) B30721621
theorem B1615987 : Blo 1615006 1615987 := bstep (se 1 (by rfl) ⟨1211990, by rfl⟩ : syracuseStep 1615987 = 2423981) B2423981
theorem B6555761 : Blo 1615006 6555761 := bstep (se 2 (by rfl) ⟨2458410, by rfl⟩ : syracuseStep 6555761 = 4916821) B4916821
theorem B1616003 : Blo 1615006 1616003 := bstep (se 1 (by rfl) ⟨1212002, by rfl⟩ : syracuseStep 1616003 = 2424005) B2424005
theorem B1616019 : Blo 1615006 1616019 := bstep (se 1 (by rfl) ⟨1212014, by rfl⟩ : syracuseStep 1616019 = 2424029) B2424029
theorem B1616035 : Blo 1615006 1616035 := bstep (se 1 (by rfl) ⟨1212026, by rfl⟩ : syracuseStep 1616035 = 2424053) B2424053
theorem B1616051 : Blo 1615006 1616051 := bstep (se 1 (by rfl) ⟨1212038, by rfl⟩ : syracuseStep 1616051 = 2424077) B2424077
theorem B1616067 : Blo 1615006 1616067 := bstep (se 1 (by rfl) ⟨1212050, by rfl⟩ : syracuseStep 1616067 = 2424101) B2424101
theorem B6899917 : Blo 1615006 6899917 := bstep (se 3 (by rfl) ⟨1293734, by rfl⟩ : syracuseStep 6899917 = 2587469) B2587469
theorem B1616083 : Blo 1615006 1616083 := bstep (se 1 (by rfl) ⟨1212062, by rfl⟩ : syracuseStep 1616083 = 2424125) B2424125
theorem B3066083 : Blo 1615006 3066083 := bstep (se 1 (by rfl) ⟨2299562, by rfl⟩ : syracuseStep 3066083 = 4599125) B4599125
theorem B1616099 : Blo 1615006 1616099 := bstep (se 1 (by rfl) ⟨1212074, by rfl⟩ : syracuseStep 1616099 = 2424149) B2424149
theorem B1616115 : Blo 1615006 1616115 := bstep (se 1 (by rfl) ⟨1212086, by rfl⟩ : syracuseStep 1616115 = 2424173) B2424173
theorem B4090115 : Blo 1615006 4090115 := bstep (se 1 (by rfl) ⟨3067586, by rfl⟩ : syracuseStep 4090115 = 6135173) B6135173
theorem B1616131 : Blo 1615006 1616131 := bstep (se 1 (by rfl) ⟨1212098, by rfl⟩ : syracuseStep 1616131 = 2424197) B2424197
theorem B1616147 : Blo 1615006 1616147 := bstep (se 1 (by rfl) ⟨1212110, by rfl⟩ : syracuseStep 1616147 = 2424221) B2424221
theorem B1616163 : Blo 1615006 1616163 := bstep (se 1 (by rfl) ⟨1212122, by rfl⟩ : syracuseStep 1616163 = 2424245) B2424245
theorem B1616179 : Blo 1615006 1616179 := bstep (se 1 (by rfl) ⟨1212134, by rfl⟩ : syracuseStep 1616179 = 2424269) B2424269
theorem B1616195 : Blo 1615006 1616195 := bstep (se 1 (by rfl) ⟨1212146, by rfl⟩ : syracuseStep 1616195 = 2424293) B2424293
theorem B1616211 : Blo 1615006 1616211 := bstep (se 1 (by rfl) ⟨1212158, by rfl⟩ : syracuseStep 1616211 = 2424317) B2424317
theorem B1616227 : Blo 1615006 1616227 := bstep (se 1 (by rfl) ⟨1212170, by rfl⟩ : syracuseStep 1616227 = 2424341) B2424341
theorem B1616243 : Blo 1615006 1616243 := bstep (se 1 (by rfl) ⟨1212182, by rfl⟩ : syracuseStep 1616243 = 2424365) B2424365
theorem B1616259 : Blo 1615006 1616259 := bstep (se 1 (by rfl) ⟨1212194, by rfl⟩ : syracuseStep 1616259 = 2424389) B2424389
theorem B2623889 : Blo 1615006 2623889 := bstep (se 2 (by rfl) ⟨983958, by rfl⟩ : syracuseStep 2623889 = 1967917) B1967917
theorem B1616275 : Blo 1615006 1616275 := bstep (se 1 (by rfl) ⟨1212206, by rfl⟩ : syracuseStep 1616275 = 2424413) B2424413
theorem B8178083 : Blo 1615006 8178083 := bstep (se 1 (by rfl) ⟨6133562, by rfl⟩ : syracuseStep 8178083 = 12267125) B12267125
theorem B1616291 : Blo 1615006 1616291 := bstep (se 1 (by rfl) ⟨1212218, by rfl⟩ : syracuseStep 1616291 = 2424437) B2424437
theorem B1616307 : Blo 1615006 1616307 := bstep (se 1 (by rfl) ⟨1212230, by rfl⟩ : syracuseStep 1616307 = 2424461) B2424461
theorem B1616323 : Blo 1615006 1616323 := bstep (se 1 (by rfl) ⟨1212242, by rfl⟩ : syracuseStep 1616323 = 2424485) B2424485
theorem B10349005 : Blo 1615006 10349005 := bstep (se 3 (by rfl) ⟨1940438, by rfl⟩ : syracuseStep 10349005 = 3880877) B3880877
theorem B1616339 : Blo 1615006 1616339 := bstep (se 1 (by rfl) ⟨1212254, by rfl⟩ : syracuseStep 1616339 = 2424509) B2424509
theorem B1616355 : Blo 1615006 1616355 := bstep (se 1 (by rfl) ⟨1212266, by rfl⟩ : syracuseStep 1616355 = 2424533) B2424533
theorem B1616371 : Blo 1615006 1616371 := bstep (se 1 (by rfl) ⟨1212278, by rfl⟩ : syracuseStep 1616371 = 2424557) B2424557
theorem B1616387 : Blo 1615006 1616387 := bstep (se 1 (by rfl) ⟨1212290, by rfl⟩ : syracuseStep 1616387 = 2424581) B2424581
theorem B5827085 : Blo 1615006 5827085 := bstep (se 3 (by rfl) ⟨1092578, by rfl⟩ : syracuseStep 5827085 = 2185157) B2185157
theorem B1616403 : Blo 1615006 1616403 := bstep (se 1 (by rfl) ⟨1212302, by rfl⟩ : syracuseStep 1616403 = 2424605) B2424605
theorem B1616419 : Blo 1615006 1616419 := bstep (se 1 (by rfl) ⟨1212314, by rfl⟩ : syracuseStep 1616419 = 2424629) B2424629
theorem B1616435 : Blo 1615006 1616435 := bstep (se 1 (by rfl) ⟨1212326, by rfl⟩ : syracuseStep 1616435 = 2424653) B2424653
theorem B1616451 : Blo 1615006 1616451 := bstep (se 1 (by rfl) ⟨1212338, by rfl⟩ : syracuseStep 1616451 = 2424677) B2424677
theorem B1616467 : Blo 1615006 1616467 := bstep (se 1 (by rfl) ⟨1212350, by rfl⟩ : syracuseStep 1616467 = 2424701) B2424701
theorem B1616483 : Blo 1615006 1616483 := bstep (se 1 (by rfl) ⟨1212362, by rfl⟩ : syracuseStep 1616483 = 2424725) B2424725
theorem B1616499 : Blo 1615006 1616499 := bstep (se 1 (by rfl) ⟨1212374, by rfl⟩ : syracuseStep 1616499 = 2424749) B2424749
theorem B1616515 : Blo 1615006 1616515 := bstep (se 1 (by rfl) ⟨1212386, by rfl⟩ : syracuseStep 1616515 = 2424773) B2424773
theorem B1616531 : Blo 1615006 1616531 := bstep (se 1 (by rfl) ⟨1212398, by rfl⟩ : syracuseStep 1616531 = 2424797) B2424797
theorem B1616547 : Blo 1615006 1616547 := bstep (se 1 (by rfl) ⟨1212410, by rfl⟩ : syracuseStep 1616547 = 2424821) B2424821
theorem B1616563 : Blo 1615006 1616563 := bstep (se 1 (by rfl) ⟨1212422, by rfl⟩ : syracuseStep 1616563 = 2424845) B2424845
theorem B18410165 : Blo 1615006 18410165 := bstep (se 5 (by rfl) ⟨862976, by rfl⟩ : syracuseStep 18410165 = 1725953) B1725953
theorem B1616579 : Blo 1615006 1616579 := bstep (se 1 (by rfl) ⟨1212434, by rfl⟩ : syracuseStep 1616579 = 2424869) B2424869
theorem B1616595 : Blo 1615006 1616595 := bstep (se 1 (by rfl) ⟨1212446, by rfl⟩ : syracuseStep 1616595 = 2424893) B2424893
theorem B23292643 : Blo 1615006 23292643 := bstep (se 1 (by rfl) ⟨17469482, by rfl⟩ : syracuseStep 23292643 = 34938965) B34938965
theorem B1616611 : Blo 1615006 1616611 := bstep (se 1 (by rfl) ⟨1212458, by rfl⟩ : syracuseStep 1616611 = 2424917) B2424917
theorem B1616627 : Blo 1615006 1616627 := bstep (se 1 (by rfl) ⟨1212470, by rfl⟩ : syracuseStep 1616627 = 2424941) B2424941
theorem B1616643 : Blo 1615006 1616643 := bstep (se 1 (by rfl) ⟨1212482, by rfl⟩ : syracuseStep 1616643 = 2424965) B2424965
theorem B1616659 : Blo 1615006 1616659 := bstep (se 1 (by rfl) ⟨1212494, by rfl⟩ : syracuseStep 1616659 = 2424989) B2424989
theorem B1616675 : Blo 1615006 1616675 := bstep (se 1 (by rfl) ⟨1212506, by rfl⟩ : syracuseStep 1616675 = 2425013) B2425013
theorem B1616691 : Blo 1615006 1616691 := bstep (se 1 (by rfl) ⟨1212518, by rfl⟩ : syracuseStep 1616691 = 2425037) B2425037
theorem B1616707 : Blo 1615006 1616707 := bstep (se 1 (by rfl) ⟨1212530, by rfl⟩ : syracuseStep 1616707 = 2425061) B2425061
theorem B1616723 : Blo 1615006 1616723 := bstep (se 1 (by rfl) ⟨1212542, by rfl⟩ : syracuseStep 1616723 = 2425085) B2425085
theorem B9202531 : Blo 1615006 9202531 := bstep (se 1 (by rfl) ⟨6901898, by rfl⟩ : syracuseStep 9202531 = 13803797) B13803797
theorem B1616739 : Blo 1615006 1616739 := bstep (se 1 (by rfl) ⟨1212554, by rfl⟩ : syracuseStep 1616739 = 2425109) B2425109
theorem B1616755 : Blo 1615006 1616755 := bstep (se 1 (by rfl) ⟨1212566, by rfl⟩ : syracuseStep 1616755 = 2425133) B2425133
theorem B1616771 : Blo 1615006 1616771 := bstep (se 1 (by rfl) ⟨1212578, by rfl⟩ : syracuseStep 1616771 = 2425157) B2425157
theorem B1616787 : Blo 1615006 1616787 := bstep (se 1 (by rfl) ⟨1212590, by rfl⟩ : syracuseStep 1616787 = 2425181) B2425181
theorem B6138787 : Blo 1615006 6138787 := bstep (se 1 (by rfl) ⟨4604090, by rfl⟩ : syracuseStep 6138787 = 9208181) B9208181
theorem B1616803 : Blo 1615006 1616803 := bstep (se 1 (by rfl) ⟨1212602, by rfl⟩ : syracuseStep 1616803 = 2425205) B2425205
theorem B1616819 : Blo 1615006 1616819 := bstep (se 1 (by rfl) ⟨1212614, by rfl⟩ : syracuseStep 1616819 = 2425229) B2425229
theorem B1616835 : Blo 1615006 1616835 := bstep (se 1 (by rfl) ⟨1212626, by rfl⟩ : syracuseStep 1616835 = 2425253) B2425253
theorem B5450705 : Blo 1615006 5450705 := bstep (se 2 (by rfl) ⟨2044014, by rfl⟩ : syracuseStep 5450705 = 4088029) B4088029
theorem B1616851 : Blo 1615006 1616851 := bstep (se 1 (by rfl) ⟨1212638, by rfl⟩ : syracuseStep 1616851 = 2425277) B2425277
theorem B1616867 : Blo 1615006 1616867 := bstep (se 1 (by rfl) ⟨1212650, by rfl⟩ : syracuseStep 1616867 = 2425301) B2425301
theorem B1616883 : Blo 1615006 1616883 := bstep (se 1 (by rfl) ⟨1212662, by rfl⟩ : syracuseStep 1616883 = 2425325) B2425325
theorem B1616899 : Blo 1615006 1616899 := bstep (se 1 (by rfl) ⟨1212674, by rfl⟩ : syracuseStep 1616899 = 2425349) B2425349
theorem B1616915 : Blo 1615006 1616915 := bstep (se 1 (by rfl) ⟨1212686, by rfl⟩ : syracuseStep 1616915 = 2425373) B2425373
theorem B1616931 : Blo 1615006 1616931 := bstep (se 1 (by rfl) ⟨1212698, by rfl⟩ : syracuseStep 1616931 = 2425397) B2425397
theorem B1616947 : Blo 1615006 1616947 := bstep (se 1 (by rfl) ⟨1212710, by rfl⟩ : syracuseStep 1616947 = 2425421) B2425421
theorem B1616963 : Blo 1615006 1616963 := bstep (se 1 (by rfl) ⟨1212722, by rfl⟩ : syracuseStep 1616963 = 2425445) B2425445
theorem B1616979 : Blo 1615006 1616979 := bstep (se 1 (by rfl) ⟨1212734, by rfl⟩ : syracuseStep 1616979 = 2425469) B2425469
theorem B3066979 : Blo 1615006 3066979 := bstep (se 1 (by rfl) ⟨2300234, by rfl⟩ : syracuseStep 3066979 = 4600469) B4600469
theorem B1616995 : Blo 1615006 1616995 := bstep (se 1 (by rfl) ⟨1212746, by rfl⟩ : syracuseStep 1616995 = 2425493) B2425493
theorem B4091057 : Blo 1615006 4091057 := bstep (se 2 (by rfl) ⟨1534146, by rfl⟩ : syracuseStep 4091057 = 3068293) B3068293
theorem B8178893 : Blo 1615006 8178893 := bstep (se 3 (by rfl) ⟨1533542, by rfl⟩ : syracuseStep 8178893 = 3067085) B3067085
theorem B4599011 : Blo 1615006 4599011 := bstep (se 1 (by rfl) ⟨3449258, by rfl⟩ : syracuseStep 4599011 = 6898517) B6898517
theorem B13102307 : Blo 1615006 13102307 := bstep (se 1 (by rfl) ⟨9826730, by rfl⟩ : syracuseStep 13102307 = 19653461) B19653461
theorem B4091107 : Blo 1615006 4091107 := bstep (se 1 (by rfl) ⟨3068330, by rfl⟩ : syracuseStep 4091107 = 6136661) B6136661
theorem B6900977 : Blo 1615006 6900977 := bstep (se 2 (by rfl) ⟨2587866, by rfl⟩ : syracuseStep 6900977 = 5175733) B5175733
theorem B3067139 : Blo 1615006 3067139 := bstep (se 1 (by rfl) ⟨2300354, by rfl⟩ : syracuseStep 3067139 = 4600709) B4600709
theorem B9203057 : Blo 1615006 9203057 := bstep (se 2 (by rfl) ⟨3451146, by rfl⟩ : syracuseStep 9203057 = 6902293) B6902293
theorem B4091249 : Blo 1615006 4091249 := bstep (se 2 (by rfl) ⟨1534218, by rfl⟩ : syracuseStep 4091249 = 3068437) B3068437
theorem B2911697 : Blo 1615006 2911697 := bstep (se 2 (by rfl) ⟨1091886, by rfl⟩ : syracuseStep 2911697 = 2183773) B2183773
theorem B5451245 : Blo 1615006 5451245 := bstep (se 3 (by rfl) ⟨1022108, by rfl⟩ : syracuseStep 5451245 = 2044217) B2044217
theorem B3452419 : Blo 1615006 3452419 := bstep (se 1 (by rfl) ⟨2589314, by rfl⟩ : syracuseStep 3452419 = 5178629) B5178629
theorem B5451299 : Blo 1615006 5451299 := bstep (se 1 (by rfl) ⟨4088474, by rfl⟩ : syracuseStep 5451299 = 8176949) B8176949
theorem B5525293 : Blo 1615006 5525293 := bstep (se 3 (by rfl) ⟨1035992, by rfl⟩ : syracuseStep 5525293 = 2071985) B2071985
theorem B5451569 : Blo 1615006 5451569 := bstep (se 2 (by rfl) ⟨2044338, by rfl⟩ : syracuseStep 5451569 = 4088677) B4088677
theorem B6221681 : Blo 1615006 6221681 := bstep (se 2 (by rfl) ⟨2333130, by rfl⟩ : syracuseStep 6221681 = 4666261) B4666261
theorem B7770019 : Blo 1615006 7770019 := bstep (se 1 (by rfl) ⟨5827514, by rfl⟩ : syracuseStep 7770019 = 11655029) B11655029
theorem B5525443 : Blo 1615006 5525443 := bstep (se 1 (by rfl) ⟨4144082, by rfl⟩ : syracuseStep 5525443 = 8288165) B8288165
theorem B7761869 : Blo 1615006 7761869 := bstep (se 3 (by rfl) ⟨1455350, by rfl⟩ : syracuseStep 7761869 = 2910701) B2910701
theorem B3452881 : Blo 1615006 3452881 := bstep (se 2 (by rfl) ⟨1294830, by rfl⟩ : syracuseStep 3452881 = 2589661) B2589661
theorem B20984035 : Blo 1615006 20984035 := bstep (se 1 (by rfl) ⟨15738026, by rfl⟩ : syracuseStep 20984035 = 31476053) B31476053
theorem B4600081 : Blo 1615006 4600081 := bstep (se 2 (by rfl) ⟨1725030, by rfl⟩ : syracuseStep 4600081 = 3450061) B3450061
theorem B3068209 : Blo 1615006 3068209 := bstep (se 2 (by rfl) ⟨1150578, by rfl⟩ : syracuseStep 3068209 = 2301157) B2301157
theorem B5452109 : Blo 1615006 5452109 := bstep (se 3 (by rfl) ⟨1022270, by rfl⟩ : syracuseStep 5452109 = 2044541) B2044541
theorem B4092241 : Blo 1615006 4092241 := bstep (se 2 (by rfl) ⟨1534590, by rfl⟩ : syracuseStep 4092241 = 3069181) B3069181
theorem B5452163 : Blo 1615006 5452163 := bstep (se 1 (by rfl) ⟨4089122, by rfl⟩ : syracuseStep 5452163 = 8178245) B8178245
theorem B2044435 : Blo 1615006 2044435 := bstep (se 1 (by rfl) ⟨1533326, by rfl⟩ : syracuseStep 2044435 = 3066653) B3066653
theorem B4092515 : Blo 1615006 4092515 := bstep (se 1 (by rfl) ⟨3069386, by rfl⟩ : syracuseStep 4092515 = 6138773) B6138773
theorem B10359409 : Blo 1615006 10359409 := bstep (se 2 (by rfl) ⟨3884778, by rfl⟩ : syracuseStep 10359409 = 7769557) B7769557
theorem B2044531 : Blo 1615006 2044531 := bstep (se 1 (by rfl) ⟨1533398, by rfl⟩ : syracuseStep 2044531 = 3066797) B3066797
theorem B5452433 : Blo 1615006 5452433 := bstep (se 2 (by rfl) ⟨2044662, by rfl⟩ : syracuseStep 5452433 = 4089325) B4089325
theorem B7369393 : Blo 1615006 7369393 := bstep (se 2 (by rfl) ⟨2763522, by rfl⟩ : syracuseStep 7369393 = 5527045) B5527045
theorem B8860357 : Blo 1615006 8860357 := bstep (se 4 (by rfl) ⟨830658, by rfl⟩ : syracuseStep 8860357 = 1661317) B1661317
theorem B9204515 : Blo 1615006 9204515 := bstep (se 1 (by rfl) ⟨6903386, by rfl⟩ : syracuseStep 9204515 = 13806773) B13806773
theorem B2913059 : Blo 1615006 2913059 := bstep (se 1 (by rfl) ⟨2184794, by rfl⟩ : syracuseStep 2913059 = 4369589) B4369589
theorem B4092707 : Blo 1615006 4092707 := bstep (se 1 (by rfl) ⟨3069530, by rfl⟩ : syracuseStep 4092707 = 6139061) B6139061
theorem B5174093 : Blo 1615006 5174093 := bstep (se 3 (by rfl) ⟨970142, by rfl⟩ : syracuseStep 5174093 = 1940285) B1940285
theorem B3634001 : Blo 1615006 3634001 := bstep (se 2 (by rfl) ⟨1362750, by rfl⟩ : syracuseStep 3634001 = 2725501) B2725501
theorem B3634019 : Blo 1615006 3634019 := bstep (se 1 (by rfl) ⟨2725514, by rfl⟩ : syracuseStep 3634019 = 5451029) B5451029
theorem B1725347 : Blo 1615006 1725347 := bstep (se 1 (by rfl) ⟨1294010, by rfl⟩ : syracuseStep 1725347 = 2588021) B2588021
theorem B22107077 : Blo 1615006 22107077 := bstep (se 4 (by rfl) ⟨2072538, by rfl⟩ : syracuseStep 22107077 = 4145077) B4145077
theorem B5821517 : Blo 1615006 5821517 := bstep (se 3 (by rfl) ⟨1091534, by rfl⟩ : syracuseStep 5821517 = 2183069) B2183069
theorem B2045027 : Blo 1615006 2045027 := bstep (se 1 (by rfl) ⟨1533770, by rfl⟩ : syracuseStep 2045027 = 3067541) B3067541
theorem B3634289 : Blo 1615006 3634289 := bstep (se 2 (by rfl) ⟨1362858, by rfl⟩ : syracuseStep 3634289 = 2725717) B2725717
theorem B3634307 : Blo 1615006 3634307 := bstep (se 1 (by rfl) ⟨2725730, by rfl⟩ : syracuseStep 3634307 = 5451461) B5451461
theorem B5452973 : Blo 1615006 5452973 := bstep (se 3 (by rfl) ⟨1022432, by rfl⟩ : syracuseStep 5452973 = 2044865) B2044865
theorem B6132941 : Blo 1615006 6132941 := bstep (se 3 (by rfl) ⟨1149926, by rfl⟩ : syracuseStep 6132941 = 2299853) B2299853
theorem B5453027 : Blo 1615006 5453027 := bstep (se 1 (by rfl) ⟨4089770, by rfl⟩ : syracuseStep 5453027 = 8179541) B8179541
theorem B1750307 : Blo 1615006 1750307 := bstep (se 1 (by rfl) ⟨1312730, by rfl⟩ : syracuseStep 1750307 = 2625461) B2625461
theorem B22123829 : Blo 1615006 22123829 := bstep (se 5 (by rfl) ⟨1037054, by rfl⟩ : syracuseStep 22123829 = 2074109) B2074109
theorem B9958733 : Blo 1615006 9958733 := bstep (se 3 (by rfl) ⟨1867262, by rfl⟩ : syracuseStep 9958733 = 3734525) B3734525
theorem B3069265 : Blo 1615006 3069265 := bstep (se 2 (by rfl) ⟨1150974, by rfl⟩ : syracuseStep 3069265 = 2301949) B2301949
theorem B3634577 : Blo 1615006 3634577 := bstep (se 2 (by rfl) ⟨1362966, by rfl⟩ : syracuseStep 3634577 = 2725933) B2725933
theorem B3634595 : Blo 1615006 3634595 := bstep (se 1 (by rfl) ⟨2725946, by rfl⟩ : syracuseStep 3634595 = 5451893) B5451893
theorem B5453297 : Blo 1615006 5453297 := bstep (se 2 (by rfl) ⟨2044986, by rfl⟩ : syracuseStep 5453297 = 4089973) B4089973
theorem B12269069 : Blo 1615006 12269069 := bstep (se 3 (by rfl) ⟨2300450, by rfl⟩ : syracuseStep 12269069 = 4600901) B4600901
theorem B4601357 : Blo 1615006 4601357 := bstep (se 3 (by rfl) ⟨862754, by rfl⟩ : syracuseStep 4601357 = 1725509) B1725509
theorem B2725393 : Blo 1615006 2725393 := bstep (se 2 (by rfl) ⟨1022022, by rfl⟩ : syracuseStep 2725393 = 2044045) B2044045
theorem B2725427 : Blo 1615006 2725427 := bstep (se 1 (by rfl) ⟨2044070, by rfl⟩ : syracuseStep 2725427 = 4088141) B4088141
theorem B3634865 : Blo 1615006 3634865 := bstep (se 2 (by rfl) ⟨1363074, by rfl⟩ : syracuseStep 3634865 = 2726149) B2726149
theorem B2725555 : Blo 1615006 2725555 := bstep (se 1 (by rfl) ⟨2044166, by rfl⟩ : syracuseStep 2725555 = 4088333) B4088333
theorem B2299585 : Blo 1615006 2299585 := bstep (se 2 (by rfl) ⟨862344, by rfl⟩ : syracuseStep 2299585 = 1724689) B1724689
theorem B3634883 : Blo 1615006 3634883 := bstep (se 1 (by rfl) ⟨2726162, by rfl⟩ : syracuseStep 3634883 = 5452325) B5452325
theorem B4601539 : Blo 1615006 4601539 := bstep (se 1 (by rfl) ⟨3451154, by rfl⟩ : syracuseStep 4601539 = 6902309) B6902309
theorem B3069667 : Blo 1615006 3069667 := bstep (se 1 (by rfl) ⟨2302250, by rfl⟩ : syracuseStep 3069667 = 4604501) B4604501
theorem B4601585 : Blo 1615006 4601585 := bstep (se 2 (by rfl) ⟨1725594, by rfl⟩ : syracuseStep 4601585 = 3451189) B3451189
theorem B2422529 : Blo 1615006 2422529 := bstep (se 2 (by rfl) ⟨908448, by rfl⟩ : syracuseStep 2422529 = 1816897) B1816897
theorem B3069713 : Blo 1615006 3069713 := bstep (se 2 (by rfl) ⟨1151142, by rfl⟩ : syracuseStep 3069713 = 2302285) B2302285
theorem B2422547 : Blo 1615006 2422547 := bstep (se 1 (by rfl) ⟨1816910, by rfl⟩ : syracuseStep 2422547 = 3633821) B3633821
theorem B2045731 : Blo 1615006 2045731 := bstep (se 1 (by rfl) ⟨1534298, by rfl⟩ : syracuseStep 2045731 = 3068597) B3068597
theorem B2422577 : Blo 1615006 2422577 := bstep (se 2 (by rfl) ⟨908466, by rfl⟩ : syracuseStep 2422577 = 1816933) B1816933
theorem B2299699 : Blo 1615006 2299699 := bstep (se 1 (by rfl) ⟨1724774, by rfl⟩ : syracuseStep 2299699 = 3449549) B3449549
theorem B2725697 : Blo 1615006 2725697 := bstep (se 2 (by rfl) ⟨1022136, by rfl⟩ : syracuseStep 2725697 = 2044273) B2044273
theorem B2422595 : Blo 1615006 2422595 := bstep (se 1 (by rfl) ⟨1816946, by rfl⟩ : syracuseStep 2422595 = 3633893) B3633893
theorem B2422625 : Blo 1615006 2422625 := bstep (se 2 (by rfl) ⟨908484, by rfl⟩ : syracuseStep 2422625 = 1816969) B1816969
theorem B2422643 : Blo 1615006 2422643 := bstep (se 1 (by rfl) ⟨1816982, by rfl⟩ : syracuseStep 2422643 = 3633965) B3633965
theorem B2045827 : Blo 1615006 2045827 := bstep (se 1 (by rfl) ⟨1534370, by rfl⟩ : syracuseStep 2045827 = 3068741) B3068741
theorem B2422673 : Blo 1615006 2422673 := bstep (se 2 (by rfl) ⟨908502, by rfl⟩ : syracuseStep 2422673 = 1817005) B1817005
theorem B2332577 : Blo 1615006 2332577 := bstep (se 2 (by rfl) ⟨874716, by rfl⟩ : syracuseStep 2332577 = 1749433) B1749433
theorem B2422691 : Blo 1615006 2422691 := bstep (se 1 (by rfl) ⟨1817018, by rfl⟩ : syracuseStep 2422691 = 3634037) B3634037
theorem B2422721 : Blo 1615006 2422721 := bstep (se 2 (by rfl) ⟨908520, by rfl⟩ : syracuseStep 2422721 = 1817041) B1817041
theorem B2725825 : Blo 1615006 2725825 := bstep (se 2 (by rfl) ⟨1022184, by rfl⟩ : syracuseStep 2725825 = 2044369) B2044369
theorem B3635153 : Blo 1615006 3635153 := bstep (se 2 (by rfl) ⟨1363182, by rfl⟩ : syracuseStep 3635153 = 2726365) B2726365
theorem B2422739 : Blo 1615006 2422739 := bstep (se 1 (by rfl) ⟨1817054, by rfl⟩ : syracuseStep 2422739 = 3634109) B3634109
theorem B2725859 : Blo 1615006 2725859 := bstep (se 1 (by rfl) ⟨2044394, by rfl⟩ : syracuseStep 2725859 = 4088789) B4088789
theorem B3635171 : Blo 1615006 3635171 := bstep (se 1 (by rfl) ⟨2726378, by rfl⟩ : syracuseStep 3635171 = 5452757) B5452757
theorem B2422769 : Blo 1615006 2422769 := bstep (se 2 (by rfl) ⟨908538, by rfl⟩ : syracuseStep 2422769 = 1817077) B1817077
theorem B6133745 : Blo 1615006 6133745 := bstep (se 2 (by rfl) ⟨2300154, by rfl⟩ : syracuseStep 6133745 = 4600309) B4600309
theorem B2422787 : Blo 1615006 2422787 := bstep (se 1 (by rfl) ⟨1817090, by rfl⟩ : syracuseStep 2422787 = 3634181) B3634181
theorem B5453837 : Blo 1615006 5453837 := bstep (se 3 (by rfl) ⟨1022594, by rfl⟩ : syracuseStep 5453837 = 2045189) B2045189
theorem B1726483 : Blo 1615006 1726483 := bstep (se 1 (by rfl) ⟨1294862, by rfl⟩ : syracuseStep 1726483 = 2589725) B2589725
theorem B2422817 : Blo 1615006 2422817 := bstep (se 2 (by rfl) ⟨908556, by rfl⟩ : syracuseStep 2422817 = 1817113) B1817113
theorem B8181809 : Blo 1615006 8181809 := bstep (se 2 (by rfl) ⟨3068178, by rfl⟩ : syracuseStep 8181809 = 6136357) B6136357
theorem B2422835 : Blo 1615006 2422835 := bstep (se 1 (by rfl) ⟨1817126, by rfl⟩ : syracuseStep 2422835 = 3634253) B3634253
theorem B5453891 : Blo 1615006 5453891 := bstep (se 1 (by rfl) ⟨4090418, by rfl⟩ : syracuseStep 5453891 = 8180837) B8180837
theorem B2422865 : Blo 1615006 2422865 := bstep (se 2 (by rfl) ⟨908574, by rfl⟩ : syracuseStep 2422865 = 1817149) B1817149
theorem B2185313 : Blo 1615006 2185313 := bstep (se 2 (by rfl) ⟨819492, by rfl⟩ : syracuseStep 2185313 = 1638985) B1638985
theorem B2422883 : Blo 1615006 2422883 := bstep (se 1 (by rfl) ⟨1817162, by rfl⟩ : syracuseStep 2422883 = 3634325) B3634325
theorem B2725987 : Blo 1615006 2725987 := bstep (se 1 (by rfl) ⟨2044490, by rfl⟩ : syracuseStep 2725987 = 4088981) B4088981
theorem B2422913 : Blo 1615006 2422913 := bstep (se 2 (by rfl) ⟨908592, by rfl⟩ : syracuseStep 2422913 = 1817185) B1817185
theorem B6903949 : Blo 1615006 6903949 := bstep (se 3 (by rfl) ⟨1294490, by rfl⟩ : syracuseStep 6903949 = 2588981) B2588981
theorem B2422931 : Blo 1615006 2422931 := bstep (se 1 (by rfl) ⟨1817198, by rfl⟩ : syracuseStep 2422931 = 3634397) B3634397
theorem B2422961 : Blo 1615006 2422961 := bstep (se 2 (by rfl) ⟨908610, by rfl⟩ : syracuseStep 2422961 = 1817221) B1817221
theorem B2422979 : Blo 1615006 2422979 := bstep (se 1 (by rfl) ⟨1817234, by rfl⟩ : syracuseStep 2422979 = 3634469) B3634469
theorem B2423009 : Blo 1615006 2423009 := bstep (se 2 (by rfl) ⟨908628, by rfl⟩ : syracuseStep 2423009 = 1817257) B1817257
theorem B2726129 : Blo 1615006 2726129 := bstep (se 2 (by rfl) ⟨1022298, by rfl⟩ : syracuseStep 2726129 = 2044597) B2044597
theorem B3635441 : Blo 1615006 3635441 := bstep (se 2 (by rfl) ⟨1363290, by rfl⟩ : syracuseStep 3635441 = 2726581) B2726581
theorem B2423027 : Blo 1615006 2423027 := bstep (se 1 (by rfl) ⟨1817270, by rfl⟩ : syracuseStep 2423027 = 3634541) B3634541
theorem B3635459 : Blo 1615006 3635459 := bstep (se 1 (by rfl) ⟨2726594, by rfl⟩ : syracuseStep 3635459 = 5453189) B5453189
theorem B13105421 : Blo 1615006 13105421 := bstep (se 3 (by rfl) ⟨2457266, by rfl⟩ : syracuseStep 13105421 = 4914533) B4914533
theorem B2423057 : Blo 1615006 2423057 := bstep (se 2 (by rfl) ⟨908646, by rfl⟩ : syracuseStep 2423057 = 1817293) B1817293
theorem B2423075 : Blo 1615006 2423075 := bstep (se 1 (by rfl) ⟨1817306, by rfl⟩ : syracuseStep 2423075 = 3634613) B3634613
theorem B2423105 : Blo 1615006 2423105 := bstep (se 2 (by rfl) ⟨908664, by rfl⟩ : syracuseStep 2423105 = 1817329) B1817329
theorem B5454161 : Blo 1615006 5454161 := bstep (se 2 (by rfl) ⟨2045310, by rfl⟩ : syracuseStep 5454161 = 4090621) B4090621
theorem B1816915 : Blo 1615006 1816915 := bstep (se 1 (by rfl) ⟨1362686, by rfl⟩ : syracuseStep 1816915 = 2725373) B2725373
theorem B2423123 : Blo 1615006 2423123 := bstep (se 1 (by rfl) ⟨1817342, by rfl⟩ : syracuseStep 2423123 = 3634685) B3634685
theorem B2423153 : Blo 1615006 2423153 := bstep (se 2 (by rfl) ⟨908682, by rfl⟩ : syracuseStep 2423153 = 1817365) B1817365
theorem B2726257 : Blo 1615006 2726257 := bstep (se 2 (by rfl) ⟨1022346, by rfl⟩ : syracuseStep 2726257 = 2044693) B2044693
theorem B2046323 : Blo 1615006 2046323 := bstep (se 1 (by rfl) ⟨1534742, by rfl⟩ : syracuseStep 2046323 = 3069485) B3069485
theorem B2423171 : Blo 1615006 2423171 := bstep (se 1 (by rfl) ⟨1817378, by rfl⟩ : syracuseStep 2423171 = 3634757) B3634757
theorem B2726291 : Blo 1615006 2726291 := bstep (se 1 (by rfl) ⟨2044718, by rfl⟩ : syracuseStep 2726291 = 4089437) B4089437
theorem B2423201 : Blo 1615006 2423201 := bstep (se 2 (by rfl) ⟨908700, by rfl⟩ : syracuseStep 2423201 = 1817401) B1817401
theorem B2423219 : Blo 1615006 2423219 := bstep (se 1 (by rfl) ⟨1817414, by rfl⟩ : syracuseStep 2423219 = 3634829) B3634829
theorem B2423249 : Blo 1615006 2423249 := bstep (se 2 (by rfl) ⟨908718, by rfl⟩ : syracuseStep 2423249 = 1817437) B1817437
theorem B1817059 : Blo 1615006 1817059 := bstep (se 1 (by rfl) ⟨1362794, by rfl⟩ : syracuseStep 1817059 = 2725589) B2725589
theorem B2423267 : Blo 1615006 2423267 := bstep (se 1 (by rfl) ⟨1817450, by rfl⟩ : syracuseStep 2423267 = 3634901) B3634901
theorem B6904291 : Blo 1615006 6904291 := bstep (se 1 (by rfl) ⟨5178218, by rfl⟩ : syracuseStep 6904291 = 10356437) B10356437
theorem B2423297 : Blo 1615006 2423297 := bstep (se 2 (by rfl) ⟨908736, by rfl⟩ : syracuseStep 2423297 = 1817473) B1817473
theorem B2243089 : Blo 1615006 2243089 := bstep (se 2 (by rfl) ⟨841158, by rfl⟩ : syracuseStep 2243089 = 1682317) B1682317
theorem B3635729 : Blo 1615006 3635729 := bstep (se 2 (by rfl) ⟨1363398, by rfl⟩ : syracuseStep 3635729 = 2726797) B2726797
theorem B2423315 : Blo 1615006 2423315 := bstep (se 1 (by rfl) ⟨1817486, by rfl⟩ : syracuseStep 2423315 = 3634973) B3634973
theorem B2726419 : Blo 1615006 2726419 := bstep (se 1 (by rfl) ⟨2044814, by rfl⟩ : syracuseStep 2726419 = 4089629) B4089629
theorem B2456099 : Blo 1615006 2456099 := bstep (se 1 (by rfl) ⟨1842074, by rfl⟩ : syracuseStep 2456099 = 3684149) B3684149
theorem B3635747 : Blo 1615006 3635747 := bstep (se 1 (by rfl) ⟨2726810, by rfl⟩ : syracuseStep 3635747 = 5453621) B5453621
theorem B2423345 : Blo 1615006 2423345 := bstep (se 2 (by rfl) ⟨908754, by rfl⟩ : syracuseStep 2423345 = 1817509) B1817509
theorem B2587187 : Blo 1615006 2587187 := bstep (se 1 (by rfl) ⟨1940390, by rfl⟩ : syracuseStep 2587187 = 3880781) B3880781
theorem B2423363 : Blo 1615006 2423363 := bstep (se 1 (by rfl) ⟨1817522, by rfl⟩ : syracuseStep 2423363 = 3635045) B3635045
theorem B9198157 : Blo 1615006 9198157 := bstep (se 3 (by rfl) ⟨1724654, by rfl⟩ : syracuseStep 9198157 = 3449309) B3449309
theorem B2423393 : Blo 1615006 2423393 := bstep (se 2 (by rfl) ⟨908772, by rfl⟩ : syracuseStep 2423393 = 1817545) B1817545
theorem B1841779 : Blo 1615006 1841779 := bstep (se 1 (by rfl) ⟨1381334, by rfl⟩ : syracuseStep 1841779 = 2762669) B2762669
theorem B1817203 : Blo 1615006 1817203 := bstep (se 1 (by rfl) ⟨1362902, by rfl⟩ : syracuseStep 1817203 = 2725805) B2725805
theorem B2423411 : Blo 1615006 2423411 := bstep (se 1 (by rfl) ⟨1817558, by rfl⟩ : syracuseStep 2423411 = 3635117) B3635117
theorem B9206405 : Blo 1615006 9206405 := bstep (se 4 (by rfl) ⟨863100, by rfl⟩ : syracuseStep 9206405 = 1726201) B1726201
theorem B6134413 : Blo 1615006 6134413 := bstep (se 3 (by rfl) ⟨1150202, by rfl⟩ : syracuseStep 6134413 = 2300405) B2300405
theorem B2423441 : Blo 1615006 2423441 := bstep (se 2 (by rfl) ⟨908790, by rfl⟩ : syracuseStep 2423441 = 1817581) B1817581
theorem B2726561 : Blo 1615006 2726561 := bstep (se 2 (by rfl) ⟨1022460, by rfl⟩ : syracuseStep 2726561 = 2044921) B2044921
theorem B2423459 : Blo 1615006 2423459 := bstep (se 1 (by rfl) ⟨1817594, by rfl⟩ : syracuseStep 2423459 = 3635189) B3635189
theorem B2423489 : Blo 1615006 2423489 := bstep (se 2 (by rfl) ⟨908808, by rfl⟩ : syracuseStep 2423489 = 1817617) B1817617
theorem B2423507 : Blo 1615006 2423507 := bstep (se 1 (by rfl) ⟨1817630, by rfl⟩ : syracuseStep 2423507 = 3635261) B3635261
theorem B2423537 : Blo 1615006 2423537 := bstep (se 2 (by rfl) ⟨908826, by rfl⟩ : syracuseStep 2423537 = 1817653) B1817653
theorem B1817347 : Blo 1615006 1817347 := bstep (se 1 (by rfl) ⟨1363010, by rfl⟩ : syracuseStep 1817347 = 2726021) B2726021
theorem B2423555 : Blo 1615006 2423555 := bstep (se 1 (by rfl) ⟨1817666, by rfl⟩ : syracuseStep 2423555 = 3635333) B3635333
theorem B2423585 : Blo 1615006 2423585 := bstep (se 2 (by rfl) ⟨908844, by rfl⟩ : syracuseStep 2423585 = 1817689) B1817689
theorem B2726689 : Blo 1615006 2726689 := bstep (se 2 (by rfl) ⟨1022508, by rfl⟩ : syracuseStep 2726689 = 2045017) B2045017
theorem B6552355 : Blo 1615006 6552355 := bstep (se 1 (by rfl) ⟨4914266, by rfl⟩ : syracuseStep 6552355 = 9828533) B9828533
theorem B3636017 : Blo 1615006 3636017 := bstep (se 2 (by rfl) ⟨1363506, by rfl⟩ : syracuseStep 3636017 = 2727013) B2727013
theorem B2423603 : Blo 1615006 2423603 := bstep (se 1 (by rfl) ⟨1817702, by rfl⟩ : syracuseStep 2423603 = 3635405) B3635405
theorem B2587457 : Blo 1615006 2587457 := bstep (se 2 (by rfl) ⟨970296, by rfl⟩ : syracuseStep 2587457 = 1940593) B1940593
theorem B2726723 : Blo 1615006 2726723 := bstep (se 1 (by rfl) ⟨2045042, by rfl⟩ : syracuseStep 2726723 = 4090085) B4090085
theorem B3636035 : Blo 1615006 3636035 := bstep (se 1 (by rfl) ⟨2727026, by rfl⟩ : syracuseStep 3636035 = 5454053) B5454053
theorem B20716357 : Blo 1615006 20716357 := bstep (se 4 (by rfl) ⟨1942158, by rfl⟩ : syracuseStep 20716357 = 3884317) B3884317
theorem B2423633 : Blo 1615006 2423633 := bstep (se 2 (by rfl) ⟨908862, by rfl⟩ : syracuseStep 2423633 = 1817725) B1817725
theorem B2423651 : Blo 1615006 2423651 := bstep (se 1 (by rfl) ⟨1817738, by rfl⟩ : syracuseStep 2423651 = 3635477) B3635477
theorem B5454701 : Blo 1615006 5454701 := bstep (se 3 (by rfl) ⟨1022756, by rfl⟩ : syracuseStep 5454701 = 2045513) B2045513
theorem B8739697 : Blo 1615006 8739697 := bstep (se 2 (by rfl) ⟨3277386, by rfl⟩ : syracuseStep 8739697 = 6554773) B6554773
theorem B2423681 : Blo 1615006 2423681 := bstep (se 2 (by rfl) ⟨908880, by rfl⟩ : syracuseStep 2423681 = 1817761) B1817761
theorem B1817491 : Blo 1615006 1817491 := bstep (se 1 (by rfl) ⟨1363118, by rfl⟩ : syracuseStep 1817491 = 2726237) B2726237
theorem B2423699 : Blo 1615006 2423699 := bstep (se 1 (by rfl) ⟨1817774, by rfl⟩ : syracuseStep 2423699 = 3635549) B3635549
theorem B5454755 : Blo 1615006 5454755 := bstep (se 1 (by rfl) ⟨4091066, by rfl⟩ : syracuseStep 5454755 = 8182133) B8182133
theorem B2423729 : Blo 1615006 2423729 := bstep (se 2 (by rfl) ⟨908898, by rfl⟩ : syracuseStep 2423729 = 1817797) B1817797
theorem B2423747 : Blo 1615006 2423747 := bstep (se 1 (by rfl) ⟨1817810, by rfl⟩ : syracuseStep 2423747 = 3635621) B3635621
theorem B3685315 : Blo 1615006 3685315 := bstep (se 1 (by rfl) ⟨2763986, by rfl⟩ : syracuseStep 3685315 = 5527973) B5527973
theorem B2726851 : Blo 1615006 2726851 := bstep (se 1 (by rfl) ⟨2045138, by rfl⟩ : syracuseStep 2726851 = 4090277) B4090277
theorem B2423777 : Blo 1615006 2423777 := bstep (se 2 (by rfl) ⟨908916, by rfl⟩ : syracuseStep 2423777 = 1817833) B1817833
theorem B2423795 : Blo 1615006 2423795 := bstep (se 1 (by rfl) ⟨1817846, by rfl⟩ : syracuseStep 2423795 = 3635693) B3635693
theorem B2423825 : Blo 1615006 2423825 := bstep (se 2 (by rfl) ⟨908934, by rfl⟩ : syracuseStep 2423825 = 1817869) B1817869
theorem B1817635 : Blo 1615006 1817635 := bstep (se 1 (by rfl) ⟨1363226, by rfl⟩ : syracuseStep 1817635 = 2726453) B2726453
theorem B2423843 : Blo 1615006 2423843 := bstep (se 1 (by rfl) ⟨1817882, by rfl⟩ : syracuseStep 2423843 = 3635765) B3635765
theorem B2423873 : Blo 1615006 2423873 := bstep (se 2 (by rfl) ⟨908952, by rfl⟩ : syracuseStep 2423873 = 1817905) B1817905
theorem B2726993 : Blo 1615006 2726993 := bstep (se 2 (by rfl) ⟨1022622, by rfl⟩ : syracuseStep 2726993 = 2045245) B2045245
theorem B3636305 : Blo 1615006 3636305 := bstep (se 2 (by rfl) ⟨1363614, by rfl⟩ : syracuseStep 3636305 = 2727229) B2727229
theorem B2456659 : Blo 1615006 2456659 := bstep (se 1 (by rfl) ⟨1842494, by rfl⟩ : syracuseStep 2456659 = 3684989) B3684989
theorem B2423891 : Blo 1615006 2423891 := bstep (se 1 (by rfl) ⟨1817918, by rfl⟩ : syracuseStep 2423891 = 3635837) B3635837
theorem B2587745 : Blo 1615006 2587745 := bstep (se 2 (by rfl) ⟨970404, by rfl⟩ : syracuseStep 2587745 = 1940809) B1940809
theorem B3636323 : Blo 1615006 3636323 := bstep (se 1 (by rfl) ⟨2727242, by rfl⟩ : syracuseStep 3636323 = 5454485) B5454485
theorem B2423921 : Blo 1615006 2423921 := bstep (se 2 (by rfl) ⟨908970, by rfl⟩ : syracuseStep 2423921 = 1817941) B1817941
theorem B2301043 : Blo 1615006 2301043 := bstep (se 1 (by rfl) ⟨1725782, by rfl⟩ : syracuseStep 2301043 = 3451565) B3451565
theorem B2423939 : Blo 1615006 2423939 := bstep (se 1 (by rfl) ⟨1817954, by rfl⟩ : syracuseStep 2423939 = 3635909) B3635909
theorem B2423969 : Blo 1615006 2423969 := bstep (se 2 (by rfl) ⟨908988, by rfl⟩ : syracuseStep 2423969 = 1817977) B1817977
theorem B4603043 : Blo 1615006 4603043 := bstep (se 1 (by rfl) ⟨3452282, by rfl⟩ : syracuseStep 4603043 = 6904565) B6904565
theorem B5455025 : Blo 1615006 5455025 := bstep (se 2 (by rfl) ⟨2045634, by rfl⟩ : syracuseStep 5455025 = 4091269) B4091269
theorem B1817779 : Blo 1615006 1817779 := bstep (se 1 (by rfl) ⟨1363334, by rfl⟩ : syracuseStep 1817779 = 2726669) B2726669
theorem B2423987 : Blo 1615006 2423987 := bstep (se 1 (by rfl) ⟨1817990, by rfl⟩ : syracuseStep 2423987 = 3635981) B3635981
theorem B2424017 : Blo 1615006 2424017 := bstep (se 2 (by rfl) ⟨909006, by rfl⟩ : syracuseStep 2424017 = 1818013) B1818013
theorem B2727121 : Blo 1615006 2727121 := bstep (se 2 (by rfl) ⟨1022670, by rfl⟩ : syracuseStep 2727121 = 2045341) B2045341
theorem B2424035 : Blo 1615006 2424035 := bstep (se 1 (by rfl) ⟨1818026, by rfl⟩ : syracuseStep 2424035 = 3636053) B3636053
theorem B2727155 : Blo 1615006 2727155 := bstep (se 1 (by rfl) ⟨2045366, by rfl⟩ : syracuseStep 2727155 = 4090733) B4090733
theorem B2424065 : Blo 1615006 2424065 := bstep (se 2 (by rfl) ⟨909024, by rfl⟩ : syracuseStep 2424065 = 1818049) B1818049
theorem B2424083 : Blo 1615006 2424083 := bstep (se 1 (by rfl) ⟨1818062, by rfl⟩ : syracuseStep 2424083 = 3636125) B3636125
theorem B2424113 : Blo 1615006 2424113 := bstep (se 2 (by rfl) ⟨909042, by rfl⟩ : syracuseStep 2424113 = 1818085) B1818085
theorem B1817923 : Blo 1615006 1817923 := bstep (se 1 (by rfl) ⟨1363442, by rfl⟩ : syracuseStep 1817923 = 2726885) B2726885
theorem B2424131 : Blo 1615006 2424131 := bstep (se 1 (by rfl) ⟨1818098, by rfl⟩ : syracuseStep 2424131 = 3636197) B3636197
theorem B2424161 : Blo 1615006 2424161 := bstep (se 2 (by rfl) ⟨909060, by rfl⟩ : syracuseStep 2424161 = 1818121) B1818121
theorem B3636593 : Blo 1615006 3636593 := bstep (se 2 (by rfl) ⟨1363722, by rfl⟩ : syracuseStep 3636593 = 2727445) B2727445
theorem B2424179 : Blo 1615006 2424179 := bstep (se 1 (by rfl) ⟨1818134, by rfl⟩ : syracuseStep 2424179 = 3636269) B3636269
theorem B2727283 : Blo 1615006 2727283 := bstep (se 1 (by rfl) ⟨2045462, by rfl⟩ : syracuseStep 2727283 = 4090925) B4090925
theorem B3636611 : Blo 1615006 3636611 := bstep (se 1 (by rfl) ⟨2727458, by rfl⟩ : syracuseStep 3636611 = 5454917) B5454917
theorem B2424209 : Blo 1615006 2424209 := bstep (se 2 (by rfl) ⟨909078, by rfl⟩ : syracuseStep 2424209 = 1818157) B1818157
theorem B6135203 : Blo 1615006 6135203 := bstep (se 1 (by rfl) ⟨4601402, by rfl⟩ : syracuseStep 6135203 = 9202805) B9202805
theorem B2424227 : Blo 1615006 2424227 := bstep (se 1 (by rfl) ⟨1818170, by rfl⟩ : syracuseStep 2424227 = 3636341) B3636341
theorem B2424257 : Blo 1615006 2424257 := bstep (se 2 (by rfl) ⟨909096, by rfl⟩ : syracuseStep 2424257 = 1818193) B1818193
theorem B1818067 : Blo 1615006 1818067 := bstep (se 1 (by rfl) ⟨1363550, by rfl⟩ : syracuseStep 1818067 = 2727101) B2727101
theorem B2424275 : Blo 1615006 2424275 := bstep (se 1 (by rfl) ⟨1818206, by rfl⟩ : syracuseStep 2424275 = 3636413) B3636413
theorem B5823971 : Blo 1615006 5823971 := bstep (se 1 (by rfl) ⟨4367978, by rfl⟩ : syracuseStep 5823971 = 8735957) B8735957
theorem B2244067 : Blo 1615006 2244067 := bstep (se 1 (by rfl) ⟨1683050, by rfl⟩ : syracuseStep 2244067 = 3366101) B3366101
theorem B8183267 : Blo 1615006 8183267 := bstep (se 1 (by rfl) ⟨6137450, by rfl⟩ : syracuseStep 8183267 = 12274901) B12274901
theorem B2424305 : Blo 1615006 2424305 := bstep (se 2 (by rfl) ⟨909114, by rfl⟩ : syracuseStep 2424305 = 1818229) B1818229
theorem B2588161 : Blo 1615006 2588161 := bstep (se 2 (by rfl) ⟨970560, by rfl⟩ : syracuseStep 2588161 = 1941121) B1941121
theorem B2727425 : Blo 1615006 2727425 := bstep (se 2 (by rfl) ⟨1022784, by rfl⟩ : syracuseStep 2727425 = 2045569) B2045569
theorem B5176835 : Blo 1615006 5176835 := bstep (se 1 (by rfl) ⟨3882626, by rfl⟩ : syracuseStep 5176835 = 7765253) B7765253
theorem B2424323 : Blo 1615006 2424323 := bstep (se 1 (by rfl) ⟨1818242, by rfl⟩ : syracuseStep 2424323 = 3636485) B3636485
theorem B2424353 : Blo 1615006 2424353 := bstep (se 2 (by rfl) ⟨909132, by rfl⟩ : syracuseStep 2424353 = 1818265) B1818265
theorem B2072099 : Blo 1615006 2072099 := bstep (se 1 (by rfl) ⟨1554074, by rfl⟩ : syracuseStep 2072099 = 3108149) B3108149
theorem B3276323 : Blo 1615006 3276323 := bstep (se 1 (by rfl) ⟨2457242, by rfl⟩ : syracuseStep 3276323 = 4914485) B4914485
theorem B2424371 : Blo 1615006 2424371 := bstep (se 1 (by rfl) ⟨1818278, by rfl⟩ : syracuseStep 2424371 = 3636557) B3636557
theorem B8289869 : Blo 1615006 8289869 := bstep (se 3 (by rfl) ⟨1554350, by rfl⟩ : syracuseStep 8289869 = 3108701) B3108701
theorem B2424401 : Blo 1615006 2424401 := bstep (se 2 (by rfl) ⟨909150, by rfl⟩ : syracuseStep 2424401 = 1818301) B1818301
theorem B1818211 : Blo 1615006 1818211 := bstep (se 1 (by rfl) ⟨1363658, by rfl⟩ : syracuseStep 1818211 = 2727317) B2727317
theorem B2424419 : Blo 1615006 2424419 := bstep (se 1 (by rfl) ⟨1818314, by rfl⟩ : syracuseStep 2424419 = 3636629) B3636629
theorem B2424449 : Blo 1615006 2424449 := bstep (se 2 (by rfl) ⟨909168, by rfl⟩ : syracuseStep 2424449 = 1818337) B1818337
theorem B5176963 : Blo 1615006 5176963 := bstep (se 1 (by rfl) ⟨3882722, by rfl⟩ : syracuseStep 5176963 = 7765445) B7765445
theorem B2727553 : Blo 1615006 2727553 := bstep (se 2 (by rfl) ⟨1022832, by rfl⟩ : syracuseStep 2727553 = 2045665) B2045665
theorem B3636881 : Blo 1615006 3636881 := bstep (se 2 (by rfl) ⟨1363830, by rfl⟩ : syracuseStep 3636881 = 2727661) B2727661
theorem B2424467 : Blo 1615006 2424467 := bstep (se 1 (by rfl) ⟨1818350, by rfl⟩ : syracuseStep 2424467 = 3636701) B3636701
theorem B2727587 : Blo 1615006 2727587 := bstep (se 1 (by rfl) ⟨2045690, by rfl⟩ : syracuseStep 2727587 = 4091381) B4091381
theorem B3636899 : Blo 1615006 3636899 := bstep (se 1 (by rfl) ⟨2727674, by rfl⟩ : syracuseStep 3636899 = 5455349) B5455349
theorem B2424497 : Blo 1615006 2424497 := bstep (se 2 (by rfl) ⟨909186, by rfl⟩ : syracuseStep 2424497 = 1818373) B1818373
theorem B2424515 : Blo 1615006 2424515 := bstep (se 1 (by rfl) ⟨1818386, by rfl⟩ : syracuseStep 2424515 = 3636773) B3636773
theorem B5455565 : Blo 1615006 5455565 := bstep (se 3 (by rfl) ⟨1022918, by rfl⟩ : syracuseStep 5455565 = 2045837) B2045837
theorem B2424545 : Blo 1615006 2424545 := bstep (se 2 (by rfl) ⟨909204, by rfl⟩ : syracuseStep 2424545 = 1818409) B1818409
theorem B1818355 : Blo 1615006 1818355 := bstep (se 1 (by rfl) ⟨1363766, by rfl⟩ : syracuseStep 1818355 = 2727533) B2727533
theorem B2424563 : Blo 1615006 2424563 := bstep (se 1 (by rfl) ⟨1818422, by rfl⟩ : syracuseStep 2424563 = 3636845) B3636845
theorem B5455619 : Blo 1615006 5455619 := bstep (se 1 (by rfl) ⟨4091714, by rfl⟩ : syracuseStep 5455619 = 8183429) B8183429
theorem B2424593 : Blo 1615006 2424593 := bstep (se 2 (by rfl) ⟨909222, by rfl⟩ : syracuseStep 2424593 = 1818445) B1818445
theorem B2424611 : Blo 1615006 2424611 := bstep (se 1 (by rfl) ⟨1818458, by rfl⟩ : syracuseStep 2424611 = 3636917) B3636917
theorem B2727715 : Blo 1615006 2727715 := bstep (se 1 (by rfl) ⟨2045786, by rfl⟩ : syracuseStep 2727715 = 4091573) B4091573
theorem B2424641 : Blo 1615006 2424641 := bstep (se 2 (by rfl) ⟨909240, by rfl⟩ : syracuseStep 2424641 = 1818481) B1818481
theorem B10100557 : Blo 1615006 10100557 := bstep (se 3 (by rfl) ⟨1893854, by rfl⟩ : syracuseStep 10100557 = 3787709) B3787709
theorem B2457425 : Blo 1615006 2457425 := bstep (se 2 (by rfl) ⟨921534, by rfl⟩ : syracuseStep 2457425 = 1843069) B1843069
theorem B2424659 : Blo 1615006 2424659 := bstep (se 1 (by rfl) ⟨1818494, by rfl⟩ : syracuseStep 2424659 = 3636989) B3636989
theorem B3686257 : Blo 1615006 3686257 := bstep (se 2 (by rfl) ⟨1382346, by rfl⟩ : syracuseStep 3686257 = 2764693) B2764693
theorem B2424689 : Blo 1615006 2424689 := bstep (se 2 (by rfl) ⟨909258, by rfl⟩ : syracuseStep 2424689 = 1818517) B1818517
theorem B1818499 : Blo 1615006 1818499 := bstep (se 1 (by rfl) ⟨1363874, by rfl⟩ : syracuseStep 1818499 = 2727749) B2727749
theorem B2424707 : Blo 1615006 2424707 := bstep (se 1 (by rfl) ⟨1818530, by rfl⟩ : syracuseStep 2424707 = 3637061) B3637061
theorem B2424737 : Blo 1615006 2424737 := bstep (se 2 (by rfl) ⟨909276, by rfl⟩ : syracuseStep 2424737 = 1818553) B1818553
theorem B2727857 : Blo 1615006 2727857 := bstep (se 2 (by rfl) ⟨1022946, by rfl⟩ : syracuseStep 2727857 = 2045893) B2045893
theorem B3637169 : Blo 1615006 3637169 := bstep (se 2 (by rfl) ⟨1363938, by rfl⟩ : syracuseStep 3637169 = 2727877) B2727877
theorem B2424755 : Blo 1615006 2424755 := bstep (se 1 (by rfl) ⟨1818566, by rfl⟩ : syracuseStep 2424755 = 3637133) B3637133
theorem B3637187 : Blo 1615006 3637187 := bstep (se 1 (by rfl) ⟨2727890, by rfl⟩ : syracuseStep 3637187 = 5455781) B5455781
theorem B5177297 : Blo 1615006 5177297 := bstep (se 2 (by rfl) ⟨1941486, by rfl⟩ : syracuseStep 5177297 = 3882973) B3882973
theorem B2424785 : Blo 1615006 2424785 := bstep (se 2 (by rfl) ⟨909294, by rfl⟩ : syracuseStep 2424785 = 1818589) B1818589
theorem B2424803 : Blo 1615006 2424803 := bstep (se 1 (by rfl) ⟨1818602, by rfl⟩ : syracuseStep 2424803 = 3637205) B3637205
theorem B3637259 : Blo 1615006 3637259 := bstep (se 1 (by rfl) ⟨2727944, by rfl⟩ : syracuseStep 3637259 = 5455889) B5455889
theorem B3883031 : Blo 1615006 3883031 := bstep (se 1 (by rfl) ⟨2912273, by rfl⟩ : syracuseStep 3883031 = 5824547) B5824547
theorem B2424857 : Blo 1615006 2424857 := bstep (se 2 (by rfl) ⟨909321, by rfl⟩ : syracuseStep 2424857 = 1818643) B1818643
theorem B2301977 : Blo 1615006 2301977 := bstep (se 2 (by rfl) ⟨863241, by rfl⟩ : syracuseStep 2301977 = 1726483) B1726483
theorem B35438627 : Blo 1615006 35438627 := bstep (se 1 (by rfl) ⟨26578970, by rfl⟩ : syracuseStep 35438627 = 53157941) B53157941
theorem B1818679 : Blo 1615006 1818679 := bstep (se 1 (by rfl) ⟨1364009, by rfl⟩ : syracuseStep 1818679 = 2728019) B2728019
theorem B3637313 : Blo 1615006 3637313 := bstep (se 2 (by rfl) ⟨1363992, by rfl⟩ : syracuseStep 3637313 = 2727985) B2727985
theorem B26214475 : Blo 1615006 26214475 := bstep (se 1 (by rfl) ⟨19660856, by rfl⟩ : syracuseStep 26214475 = 39321713) B39321713
theorem B2424971 : Blo 1615006 2424971 := bstep (se 1 (by rfl) ⟨1818728, by rfl⟩ : syracuseStep 2424971 = 3637457) B3637457
theorem B2424983 : Blo 1615006 2424983 := bstep (se 1 (by rfl) ⟨1818737, by rfl⟩ : syracuseStep 2424983 = 3637475) B3637475
theorem B5456051 : Blo 1615006 5456051 := bstep (se 1 (by rfl) ⟨4092038, by rfl⟩ : syracuseStep 5456051 = 8184077) B8184077
theorem B15524045 : Blo 1615006 15524045 := bstep (se 3 (by rfl) ⟨2910758, by rfl⟩ : syracuseStep 15524045 = 5821517) B5821517
theorem B3195095 : Blo 1615006 3195095 := bstep (se 1 (by rfl) ⟨2396321, by rfl⟩ : syracuseStep 3195095 = 4792643) B4792643
theorem B2425049 : Blo 1615006 2425049 := bstep (se 2 (by rfl) ⟨909393, by rfl⟩ : syracuseStep 2425049 = 1818787) B1818787
theorem B1818859 : Blo 1615006 1818859 := bstep (se 1 (by rfl) ⟨1364144, by rfl⟩ : syracuseStep 1818859 = 2728289) B2728289
theorem B9199889 : Blo 1615006 9199889 := bstep (se 2 (by rfl) ⟨3449958, by rfl⟩ : syracuseStep 9199889 = 6899917) B6899917
theorem B3637529 : Blo 1615006 3637529 := bstep (se 2 (by rfl) ⟨1364073, by rfl⟩ : syracuseStep 3637529 = 2728147) B2728147
theorem B14745931 : Blo 1615006 14745931 := bstep (se 1 (by rfl) ⟨11059448, by rfl⟩ : syracuseStep 14745931 = 22118897) B22118897
theorem B2425163 : Blo 1615006 2425163 := bstep (se 1 (by rfl) ⟨1818872, by rfl⟩ : syracuseStep 2425163 = 3637745) B3637745
theorem B2425175 : Blo 1615006 2425175 := bstep (se 1 (by rfl) ⟨1818881, by rfl⟩ : syracuseStep 2425175 = 3637763) B3637763
theorem B1818967 : Blo 1615006 1818967 := bstep (se 1 (by rfl) ⟨1364225, by rfl⟩ : syracuseStep 1818967 = 2728451) B2728451
theorem B3637619 : Blo 1615006 3637619 := bstep (se 1 (by rfl) ⟨2728214, by rfl⟩ : syracuseStep 3637619 = 5456429) B5456429
theorem B3637655 : Blo 1615006 3637655 := bstep (se 1 (by rfl) ⟨2728241, by rfl⟩ : syracuseStep 3637655 = 5456483) B5456483
theorem B2728343 : Blo 1615006 2728343 := bstep (se 1 (by rfl) ⟨2046257, by rfl⟩ : syracuseStep 2728343 = 4092515) B4092515
theorem B2458009 : Blo 1615006 2458009 := bstep (se 2 (by rfl) ⟨921753, by rfl⟩ : syracuseStep 2458009 = 1843507) B1843507
theorem B2425241 : Blo 1615006 2425241 := bstep (se 2 (by rfl) ⟨909465, by rfl⟩ : syracuseStep 2425241 = 1818931) B1818931
theorem B5456321 : Blo 1615006 5456321 := bstep (se 2 (by rfl) ⟨2046120, by rfl⟩ : syracuseStep 5456321 = 4092241) B4092241
theorem B2425355 : Blo 1615006 2425355 := bstep (se 1 (by rfl) ⟨1819016, by rfl⟩ : syracuseStep 2425355 = 3638033) B3638033
theorem B6136343 : Blo 1615006 6136343 := bstep (se 1 (by rfl) ⟨4602257, by rfl⟩ : syracuseStep 6136343 = 9204515) B9204515
theorem B1942039 : Blo 1615006 1942039 := bstep (se 1 (by rfl) ⟨1456529, by rfl⟩ : syracuseStep 1942039 = 2913059) B2913059
theorem B2728471 : Blo 1615006 2728471 := bstep (se 1 (by rfl) ⟨2046353, by rfl⟩ : syracuseStep 2728471 = 4092707) B4092707
theorem B2425367 : Blo 1615006 2425367 := bstep (se 1 (by rfl) ⟨1819025, by rfl⟩ : syracuseStep 2425367 = 3638051) B3638051
theorem B3449395 : Blo 1615006 3449395 := bstep (se 1 (by rfl) ⟨2587046, by rfl⟩ : syracuseStep 3449395 = 5174093) B5174093
theorem B3637835 : Blo 1615006 3637835 := bstep (se 1 (by rfl) ⟨2728376, by rfl⟩ : syracuseStep 3637835 = 5456753) B5456753
theorem B2425433 : Blo 1615006 2425433 := bstep (se 2 (by rfl) ⟨909537, by rfl⟩ : syracuseStep 2425433 = 1819075) B1819075
theorem B3637889 : Blo 1615006 3637889 := bstep (se 2 (by rfl) ⟨1364208, by rfl⟩ : syracuseStep 3637889 = 2728417) B2728417
theorem B14738051 : Blo 1615006 14738051 := bstep (se 1 (by rfl) ⟨11053538, by rfl⟩ : syracuseStep 14738051 = 22107077) B22107077
theorem B3277451 : Blo 1615006 3277451 := bstep (se 1 (by rfl) ⟨2458088, by rfl⟩ : syracuseStep 3277451 = 4916177) B4916177
theorem B2990785 : Blo 1615006 2990785 := bstep (se 2 (by rfl) ⟨1121544, by rfl⟩ : syracuseStep 2990785 = 2243089) B2243089
theorem B12264209 : Blo 1615006 12264209 := bstep (se 2 (by rfl) ⟨4599078, by rfl⟩ : syracuseStep 12264209 = 9198157) B9198157
theorem B4088627 : Blo 1615006 4088627 := bstep (se 1 (by rfl) ⟨3066470, by rfl⟩ : syracuseStep 4088627 = 6132941) B6132941
theorem B13812545 : Blo 1615006 13812545 := bstep (se 2 (by rfl) ⟨5179704, by rfl⟩ : syracuseStep 13812545 = 10359409) B10359409
theorem B3638105 : Blo 1615006 3638105 := bstep (se 2 (by rfl) ⟨1364289, by rfl⟩ : syracuseStep 3638105 = 2728579) B2728579
theorem B7373699 : Blo 1615006 7373699 := bstep (se 1 (by rfl) ⟨5530274, by rfl⟩ : syracuseStep 7373699 = 11060549) B11060549
theorem B3638195 : Blo 1615006 3638195 := bstep (se 1 (by rfl) ⟨2728646, by rfl⟩ : syracuseStep 3638195 = 5457293) B5457293
theorem B3638231 : Blo 1615006 3638231 := bstep (se 1 (by rfl) ⟨2728673, by rfl⟩ : syracuseStep 3638231 = 5457347) B5457347
theorem B31056857 : Blo 1615006 31056857 := bstep (se 2 (by rfl) ⟨11646321, by rfl⟩ : syracuseStep 31056857 = 23292643) B23292643
theorem B4916189 : Blo 1615006 4916189 := bstep (se 3 (by rfl) ⟨921785, by rfl⟩ : syracuseStep 4916189 = 1843571) B1843571
theorem B5456861 : Blo 1615006 5456861 := bstep (se 3 (by rfl) ⟨1023161, by rfl⟩ : syracuseStep 5456861 = 2046323) B2046323
theorem B3884107 : Blo 1615006 3884107 := bstep (se 1 (by rfl) ⟨2913080, by rfl⟩ : syracuseStep 3884107 = 5826161) B5826161
theorem B1615019 : Blo 1615006 1615019 := bstep (se 1 (by rfl) ⟨1211264, by rfl⟩ : syracuseStep 1615019 = 2422529) B2422529
theorem B1615031 : Blo 1615006 1615031 := bstep (se 1 (by rfl) ⟨1211273, by rfl⟩ : syracuseStep 1615031 = 2422547) B2422547
theorem B1615051 : Blo 1615006 1615051 := bstep (se 1 (by rfl) ⟨1211288, by rfl⟩ : syracuseStep 1615051 = 2422577) B2422577
theorem B1615063 : Blo 1615006 1615063 := bstep (se 1 (by rfl) ⟨1211297, by rfl⟩ : syracuseStep 1615063 = 2422595) B2422595
theorem B8185049 : Blo 1615006 8185049 := bstep (se 2 (by rfl) ⟨3069393, by rfl⟩ : syracuseStep 8185049 = 6138787) B6138787
theorem B1615083 : Blo 1615006 1615083 := bstep (se 1 (by rfl) ⟨1211312, by rfl⟩ : syracuseStep 1615083 = 2422625) B2422625
theorem B1615095 : Blo 1615006 1615095 := bstep (se 1 (by rfl) ⟨1211321, by rfl⟩ : syracuseStep 1615095 = 2422643) B2422643
theorem B1615115 : Blo 1615006 1615115 := bstep (se 1 (by rfl) ⟨1211336, by rfl⟩ : syracuseStep 1615115 = 2422673) B2422673
theorem B1615127 : Blo 1615006 1615127 := bstep (se 1 (by rfl) ⟨1211345, by rfl⟩ : syracuseStep 1615127 = 2422691) B2422691
theorem B1615147 : Blo 1615006 1615147 := bstep (se 1 (by rfl) ⟨1211360, by rfl⟩ : syracuseStep 1615147 = 2422721) B2422721
theorem B1615159 : Blo 1615006 1615159 := bstep (se 1 (by rfl) ⟨1211369, by rfl⟩ : syracuseStep 1615159 = 2422739) B2422739
theorem B1615179 : Blo 1615006 1615179 := bstep (se 1 (by rfl) ⟨1211384, by rfl⟩ : syracuseStep 1615179 = 2422769) B2422769
theorem B4089163 : Blo 1615006 4089163 := bstep (se 1 (by rfl) ⟨3066872, by rfl⟩ : syracuseStep 4089163 = 6133745) B6133745
theorem B1615191 : Blo 1615006 1615191 := bstep (se 1 (by rfl) ⟨1211393, by rfl⟩ : syracuseStep 1615191 = 2422787) B2422787
theorem B1615211 : Blo 1615006 1615211 := bstep (se 1 (by rfl) ⟨1211408, by rfl⟩ : syracuseStep 1615211 = 2422817) B2422817
theorem B1615223 : Blo 1615006 1615223 := bstep (se 1 (by rfl) ⟨1211417, by rfl⟩ : syracuseStep 1615223 = 2422835) B2422835
theorem B1615243 : Blo 1615006 1615243 := bstep (se 1 (by rfl) ⟨1211432, by rfl⟩ : syracuseStep 1615243 = 2422865) B2422865
theorem B78620053 : Blo 1615006 78620053 := bstep (se 6 (by rfl) ⟨1842657, by rfl⟩ : syracuseStep 78620053 = 3685315) B3685315
theorem B1615255 : Blo 1615006 1615255 := bstep (se 1 (by rfl) ⟨1211441, by rfl⟩ : syracuseStep 1615255 = 2422883) B2422883
theorem B2590103 : Blo 1615006 2590103 := bstep (se 1 (by rfl) ⟨1942577, by rfl⟩ : syracuseStep 2590103 = 3885155) B3885155
theorem B1615275 : Blo 1615006 1615275 := bstep (se 1 (by rfl) ⟨1211456, by rfl⟩ : syracuseStep 1615275 = 2422913) B2422913
theorem B1615287 : Blo 1615006 1615287 := bstep (se 1 (by rfl) ⟨1211465, by rfl⟩ : syracuseStep 1615287 = 2422931) B2422931
theorem B1615307 : Blo 1615006 1615307 := bstep (se 1 (by rfl) ⟨1211480, by rfl⟩ : syracuseStep 1615307 = 2422961) B2422961
theorem B1615319 : Blo 1615006 1615319 := bstep (se 1 (by rfl) ⟨1211489, by rfl⟩ : syracuseStep 1615319 = 2422979) B2422979
theorem B4089305 : Blo 1615006 4089305 := bstep (se 2 (by rfl) ⟨1533489, by rfl⟩ : syracuseStep 4089305 = 3066979) B3066979
theorem B6899165 : Blo 1615006 6899165 := bstep (se 3 (by rfl) ⟨1293593, by rfl⟩ : syracuseStep 6899165 = 2587187) B2587187
theorem B1615339 : Blo 1615006 1615339 := bstep (se 1 (by rfl) ⟨1211504, by rfl⟩ : syracuseStep 1615339 = 2423009) B2423009
theorem B1615351 : Blo 1615006 1615351 := bstep (se 1 (by rfl) ⟨1211513, by rfl⟩ : syracuseStep 1615351 = 2423027) B2423027
theorem B1615371 : Blo 1615006 1615371 := bstep (se 1 (by rfl) ⟨1211528, by rfl⟩ : syracuseStep 1615371 = 2423057) B2423057
theorem B1615383 : Blo 1615006 1615383 := bstep (se 1 (by rfl) ⟨1211537, by rfl⟩ : syracuseStep 1615383 = 2423075) B2423075
theorem B1615403 : Blo 1615006 1615403 := bstep (se 1 (by rfl) ⟨1211552, by rfl⟩ : syracuseStep 1615403 = 2423105) B2423105
theorem B1615415 : Blo 1615006 1615415 := bstep (se 1 (by rfl) ⟨1211561, by rfl⟩ : syracuseStep 1615415 = 2423123) B2423123
theorem B1615435 : Blo 1615006 1615435 := bstep (se 1 (by rfl) ⟨1211576, by rfl⟩ : syracuseStep 1615435 = 2423153) B2423153
theorem B1615447 : Blo 1615006 1615447 := bstep (se 1 (by rfl) ⟨1211585, by rfl⟩ : syracuseStep 1615447 = 2423171) B2423171
theorem B1615467 : Blo 1615006 1615467 := bstep (se 1 (by rfl) ⟨1211600, by rfl⟩ : syracuseStep 1615467 = 2423201) B2423201
theorem B1615479 : Blo 1615006 1615479 := bstep (se 1 (by rfl) ⟨1211609, by rfl⟩ : syracuseStep 1615479 = 2423219) B2423219
theorem B1615499 : Blo 1615006 1615499 := bstep (se 1 (by rfl) ⟨1211624, by rfl⟩ : syracuseStep 1615499 = 2423249) B2423249
theorem B1615511 : Blo 1615006 1615511 := bstep (se 1 (by rfl) ⟨1211633, by rfl⟩ : syracuseStep 1615511 = 2423267) B2423267
theorem B1615531 : Blo 1615006 1615531 := bstep (se 1 (by rfl) ⟨1211648, by rfl⟩ : syracuseStep 1615531 = 2423297) B2423297
theorem B3884723 : Blo 1615006 3884723 := bstep (se 1 (by rfl) ⟨2913542, by rfl⟩ : syracuseStep 3884723 = 5827085) B5827085
theorem B1615543 : Blo 1615006 1615543 := bstep (se 1 (by rfl) ⟨1211657, by rfl⟩ : syracuseStep 1615543 = 2423315) B2423315
theorem B1615563 : Blo 1615006 1615563 := bstep (se 1 (by rfl) ⟨1211672, by rfl⟩ : syracuseStep 1615563 = 2423345) B2423345
theorem B1615575 : Blo 1615006 1615575 := bstep (se 1 (by rfl) ⟨1211681, by rfl⟩ : syracuseStep 1615575 = 2423363) B2423363
theorem B1615595 : Blo 1615006 1615595 := bstep (se 1 (by rfl) ⟨1211696, by rfl⟩ : syracuseStep 1615595 = 2423393) B2423393
theorem B1615607 : Blo 1615006 1615607 := bstep (se 1 (by rfl) ⟨1211705, by rfl⟩ : syracuseStep 1615607 = 2423411) B2423411
theorem B6137603 : Blo 1615006 6137603 := bstep (se 1 (by rfl) ⟨4603202, by rfl⟩ : syracuseStep 6137603 = 9206405) B9206405
theorem B1615627 : Blo 1615006 1615627 := bstep (se 1 (by rfl) ⟨1211720, by rfl⟩ : syracuseStep 1615627 = 2423441) B2423441
theorem B1615639 : Blo 1615006 1615639 := bstep (se 1 (by rfl) ⟨1211729, by rfl⟩ : syracuseStep 1615639 = 2423459) B2423459
theorem B12273443 : Blo 1615006 12273443 := bstep (se 1 (by rfl) ⟨9205082, by rfl⟩ : syracuseStep 12273443 = 18410165) B18410165
theorem B1615659 : Blo 1615006 1615659 := bstep (se 1 (by rfl) ⟨1211744, by rfl⟩ : syracuseStep 1615659 = 2423489) B2423489
theorem B1615671 : Blo 1615006 1615671 := bstep (se 1 (by rfl) ⟨1211753, by rfl⟩ : syracuseStep 1615671 = 2423507) B2423507
theorem B1615691 : Blo 1615006 1615691 := bstep (se 1 (by rfl) ⟨1211768, by rfl⟩ : syracuseStep 1615691 = 2423537) B2423537
theorem B1615703 : Blo 1615006 1615703 := bstep (se 1 (by rfl) ⟨1211777, by rfl⟩ : syracuseStep 1615703 = 2423555) B2423555
theorem B1615723 : Blo 1615006 1615723 := bstep (se 1 (by rfl) ⟨1211792, by rfl⟩ : syracuseStep 1615723 = 2423585) B2423585
theorem B1615735 : Blo 1615006 1615735 := bstep (se 1 (by rfl) ⟨1211801, by rfl⟩ : syracuseStep 1615735 = 2423603) B2423603
theorem B1615755 : Blo 1615006 1615755 := bstep (se 1 (by rfl) ⟨1211816, by rfl⟩ : syracuseStep 1615755 = 2423633) B2423633
theorem B1615767 : Blo 1615006 1615767 := bstep (se 1 (by rfl) ⟨1211825, by rfl⟩ : syracuseStep 1615767 = 2423651) B2423651
theorem B1615787 : Blo 1615006 1615787 := bstep (se 1 (by rfl) ⟨1211840, by rfl⟩ : syracuseStep 1615787 = 2423681) B2423681
theorem B1615799 : Blo 1615006 1615799 := bstep (se 1 (by rfl) ⟨1211849, by rfl⟩ : syracuseStep 1615799 = 2423699) B2423699
theorem B1615819 : Blo 1615006 1615819 := bstep (se 1 (by rfl) ⟨1211864, by rfl⟩ : syracuseStep 1615819 = 2423729) B2423729
theorem B1615831 : Blo 1615006 1615831 := bstep (se 1 (by rfl) ⟨1211873, by rfl⟩ : syracuseStep 1615831 = 2423747) B2423747
theorem B1615851 : Blo 1615006 1615851 := bstep (se 1 (by rfl) ⟨1211888, by rfl⟩ : syracuseStep 1615851 = 2423777) B2423777
theorem B1615863 : Blo 1615006 1615863 := bstep (se 1 (by rfl) ⟨1211897, by rfl⟩ : syracuseStep 1615863 = 2423795) B2423795
theorem B3450881 : Blo 1615006 3450881 := bstep (se 2 (by rfl) ⟨1294080, by rfl⟩ : syracuseStep 3450881 = 2588161) B2588161
theorem B1615883 : Blo 1615006 1615883 := bstep (se 1 (by rfl) ⟨1211912, by rfl⟩ : syracuseStep 1615883 = 2423825) B2423825
theorem B1615895 : Blo 1615006 1615895 := bstep (se 1 (by rfl) ⟨1211921, by rfl⟩ : syracuseStep 1615895 = 2423843) B2423843
theorem B1615915 : Blo 1615006 1615915 := bstep (se 1 (by rfl) ⟨1211936, by rfl⟩ : syracuseStep 1615915 = 2423873) B2423873
theorem B1615927 : Blo 1615006 1615927 := bstep (se 1 (by rfl) ⟨1211945, by rfl⟩ : syracuseStep 1615927 = 2423891) B2423891
theorem B1615947 : Blo 1615006 1615947 := bstep (se 1 (by rfl) ⟨1211960, by rfl⟩ : syracuseStep 1615947 = 2423921) B2423921
theorem B1615959 : Blo 1615006 1615959 := bstep (se 1 (by rfl) ⟨1211969, by rfl⟩ : syracuseStep 1615959 = 2423939) B2423939
theorem B1615979 : Blo 1615006 1615979 := bstep (se 1 (by rfl) ⟨1211984, by rfl⟩ : syracuseStep 1615979 = 2423969) B2423969
theorem B1615991 : Blo 1615006 1615991 := bstep (se 1 (by rfl) ⟨1211993, by rfl⟩ : syracuseStep 1615991 = 2423987) B2423987
theorem B1616011 : Blo 1615006 1616011 := bstep (se 1 (by rfl) ⟨1212008, by rfl⟩ : syracuseStep 1616011 = 2424017) B2424017
theorem B3066007 : Blo 1615006 3066007 := bstep (se 1 (by rfl) ⟨2299505, by rfl⟩ : syracuseStep 3066007 = 4599011) B4599011
theorem B8734871 : Blo 1615006 8734871 := bstep (se 1 (by rfl) ⟨6551153, by rfl⟩ : syracuseStep 8734871 = 13102307) B13102307
theorem B1616023 : Blo 1615006 1616023 := bstep (se 1 (by rfl) ⟨1212017, by rfl⟩ : syracuseStep 1616023 = 2424035) B2424035
theorem B1616043 : Blo 1615006 1616043 := bstep (se 1 (by rfl) ⟨1212032, by rfl⟩ : syracuseStep 1616043 = 2424065) B2424065
theorem B1616055 : Blo 1615006 1616055 := bstep (se 1 (by rfl) ⟨1212041, by rfl⟩ : syracuseStep 1616055 = 2424083) B2424083
theorem B1616075 : Blo 1615006 1616075 := bstep (se 1 (by rfl) ⟨1212056, by rfl⟩ : syracuseStep 1616075 = 2424113) B2424113
theorem B1616087 : Blo 1615006 1616087 := bstep (se 1 (by rfl) ⟨1212065, by rfl⟩ : syracuseStep 1616087 = 2424131) B2424131
theorem B1616107 : Blo 1615006 1616107 := bstep (se 1 (by rfl) ⟨1212080, by rfl⟩ : syracuseStep 1616107 = 2424161) B2424161
theorem B1616119 : Blo 1615006 1616119 := bstep (se 1 (by rfl) ⟨1212089, by rfl⟩ : syracuseStep 1616119 = 2424179) B2424179
theorem B3066113 : Blo 1615006 3066113 := bstep (se 2 (by rfl) ⟨1149792, by rfl⟩ : syracuseStep 3066113 = 2299585) B2299585
theorem B1616139 : Blo 1615006 1616139 := bstep (se 1 (by rfl) ⟨1212104, by rfl⟩ : syracuseStep 1616139 = 2424209) B2424209
theorem B4090135 : Blo 1615006 4090135 := bstep (se 1 (by rfl) ⟨3067601, by rfl⟩ : syracuseStep 4090135 = 6135203) B6135203
theorem B1616151 : Blo 1615006 1616151 := bstep (se 1 (by rfl) ⟨1212113, by rfl⟩ : syracuseStep 1616151 = 2424227) B2424227
theorem B1616171 : Blo 1615006 1616171 := bstep (se 1 (by rfl) ⟨1212128, by rfl⟩ : syracuseStep 1616171 = 2424257) B2424257
theorem B1616183 : Blo 1615006 1616183 := bstep (se 1 (by rfl) ⟨1212137, by rfl⟩ : syracuseStep 1616183 = 2424275) B2424275
theorem B1616203 : Blo 1615006 1616203 := bstep (se 1 (by rfl) ⟨1212152, by rfl⟩ : syracuseStep 1616203 = 2424305) B2424305
theorem B3451223 : Blo 1615006 3451223 := bstep (se 1 (by rfl) ⟨2588417, by rfl⟩ : syracuseStep 3451223 = 5176835) B5176835
theorem B1616215 : Blo 1615006 1616215 := bstep (se 1 (by rfl) ⟨1212161, by rfl⟩ : syracuseStep 1616215 = 2424323) B2424323
theorem B1616235 : Blo 1615006 1616235 := bstep (se 1 (by rfl) ⟨1212176, by rfl⟩ : syracuseStep 1616235 = 2424353) B2424353
theorem B1616247 : Blo 1615006 1616247 := bstep (se 1 (by rfl) ⟨1212185, by rfl⟩ : syracuseStep 1616247 = 2424371) B2424371
theorem B1616267 : Blo 1615006 1616267 := bstep (se 1 (by rfl) ⟨1212200, by rfl⟩ : syracuseStep 1616267 = 2424401) B2424401
theorem B7367057 : Blo 1615006 7367057 := bstep (se 2 (by rfl) ⟨2762646, by rfl⟩ : syracuseStep 7367057 = 5525293) B5525293
theorem B1616279 : Blo 1615006 1616279 := bstep (se 1 (by rfl) ⟨1212209, by rfl⟩ : syracuseStep 1616279 = 2424419) B2424419
theorem B3066265 : Blo 1615006 3066265 := bstep (se 2 (by rfl) ⟨1149849, by rfl⟩ : syracuseStep 3066265 = 2299699) B2299699
theorem B1616299 : Blo 1615006 1616299 := bstep (se 1 (by rfl) ⟨1212224, by rfl⟩ : syracuseStep 1616299 = 2424449) B2424449
theorem B6220205 : Blo 1615006 6220205 := bstep (se 3 (by rfl) ⟨1166288, by rfl⟩ : syracuseStep 6220205 = 2332577) B2332577
theorem B1616311 : Blo 1615006 1616311 := bstep (se 1 (by rfl) ⟨1212233, by rfl⟩ : syracuseStep 1616311 = 2424467) B2424467
theorem B1616331 : Blo 1615006 1616331 := bstep (se 1 (by rfl) ⟨1212248, by rfl⟩ : syracuseStep 1616331 = 2424497) B2424497
theorem B1616343 : Blo 1615006 1616343 := bstep (se 1 (by rfl) ⟨1212257, by rfl⟩ : syracuseStep 1616343 = 2424515) B2424515
theorem B1616363 : Blo 1615006 1616363 := bstep (se 1 (by rfl) ⟨1212272, by rfl⟩ : syracuseStep 1616363 = 2424545) B2424545
theorem B1616375 : Blo 1615006 1616375 := bstep (se 1 (by rfl) ⟨1212281, by rfl⟩ : syracuseStep 1616375 = 2424563) B2424563
theorem B1616395 : Blo 1615006 1616395 := bstep (se 1 (by rfl) ⟨1212296, by rfl⟩ : syracuseStep 1616395 = 2424593) B2424593
theorem B1616407 : Blo 1615006 1616407 := bstep (se 1 (by rfl) ⟨1212305, by rfl⟩ : syracuseStep 1616407 = 2424611) B2424611
theorem B1616427 : Blo 1615006 1616427 := bstep (se 1 (by rfl) ⟨1212320, by rfl⟩ : syracuseStep 1616427 = 2424641) B2424641
theorem B1616439 : Blo 1615006 1616439 := bstep (se 1 (by rfl) ⟨1212329, by rfl⟩ : syracuseStep 1616439 = 2424659) B2424659
theorem B1616459 : Blo 1615006 1616459 := bstep (se 1 (by rfl) ⟨1212344, by rfl⟩ : syracuseStep 1616459 = 2424689) B2424689
theorem B4147787 : Blo 1615006 4147787 := bstep (se 1 (by rfl) ⟨3110840, by rfl⟩ : syracuseStep 4147787 = 6221681) B6221681
theorem B1616471 : Blo 1615006 1616471 := bstep (se 1 (by rfl) ⟨1212353, by rfl⟩ : syracuseStep 1616471 = 2424707) B2424707
theorem B7367257 : Blo 1615006 7367257 := bstep (se 2 (by rfl) ⟨2762721, by rfl⟩ : syracuseStep 7367257 = 5525443) B5525443
theorem B1616491 : Blo 1615006 1616491 := bstep (se 1 (by rfl) ⟨1212368, by rfl⟩ : syracuseStep 1616491 = 2424737) B2424737
theorem B1616503 : Blo 1615006 1616503 := bstep (se 1 (by rfl) ⟨1212377, by rfl⟩ : syracuseStep 1616503 = 2424755) B2424755
theorem B3451531 : Blo 1615006 3451531 := bstep (se 1 (by rfl) ⟨2588648, by rfl⟩ : syracuseStep 3451531 = 5177297) B5177297
theorem B1616523 : Blo 1615006 1616523 := bstep (se 1 (by rfl) ⟨1212392, by rfl⟩ : syracuseStep 1616523 = 2424785) B2424785
theorem B1616535 : Blo 1615006 1616535 := bstep (se 1 (by rfl) ⟨1212401, by rfl⟩ : syracuseStep 1616535 = 2424803) B2424803
theorem B1616555 : Blo 1615006 1616555 := bstep (se 1 (by rfl) ⟨1212416, by rfl⟩ : syracuseStep 1616555 = 2424833) B2424833
theorem B1616567 : Blo 1615006 1616567 := bstep (se 1 (by rfl) ⟨1212425, by rfl⟩ : syracuseStep 1616567 = 2424851) B2424851
theorem B4090571 : Blo 1615006 4090571 := bstep (se 1 (by rfl) ⟨3067928, by rfl⟩ : syracuseStep 4090571 = 6135857) B6135857
theorem B1616587 : Blo 1615006 1616587 := bstep (se 1 (by rfl) ⟨1212440, by rfl⟩ : syracuseStep 1616587 = 2424881) B2424881
theorem B1616599 : Blo 1615006 1616599 := bstep (se 1 (by rfl) ⟨1212449, by rfl⟩ : syracuseStep 1616599 = 2424899) B2424899
theorem B1616619 : Blo 1615006 1616619 := bstep (se 1 (by rfl) ⟨1212464, by rfl⟩ : syracuseStep 1616619 = 2424929) B2424929
theorem B1616631 : Blo 1615006 1616631 := bstep (se 1 (by rfl) ⟨1212473, by rfl⟩ : syracuseStep 1616631 = 2424947) B2424947
theorem B1616651 : Blo 1615006 1616651 := bstep (se 1 (by rfl) ⟨1212488, by rfl⟩ : syracuseStep 1616651 = 2424977) B2424977
theorem B1616663 : Blo 1615006 1616663 := bstep (se 1 (by rfl) ⟨1212497, by rfl⟩ : syracuseStep 1616663 = 2424995) B2424995
theorem B1616683 : Blo 1615006 1616683 := bstep (se 1 (by rfl) ⟨1212512, by rfl⟩ : syracuseStep 1616683 = 2425025) B2425025
theorem B1616695 : Blo 1615006 1616695 := bstep (se 1 (by rfl) ⟨1212521, by rfl⟩ : syracuseStep 1616695 = 2425043) B2425043
theorem B20712257 : Blo 1615006 20712257 := bstep (se 2 (by rfl) ⟨7767096, by rfl⟩ : syracuseStep 20712257 = 15534193) B15534193
theorem B1616715 : Blo 1615006 1616715 := bstep (se 1 (by rfl) ⟨1212536, by rfl⟩ : syracuseStep 1616715 = 2425073) B2425073
theorem B1616727 : Blo 1615006 1616727 := bstep (se 1 (by rfl) ⟨1212545, by rfl⟩ : syracuseStep 1616727 = 2425091) B2425091
theorem B1616747 : Blo 1615006 1616747 := bstep (se 1 (by rfl) ⟨1212560, by rfl⟩ : syracuseStep 1616747 = 2425121) B2425121
theorem B1616759 : Blo 1615006 1616759 := bstep (se 1 (by rfl) ⟨1212569, by rfl⟩ : syracuseStep 1616759 = 2425139) B2425139
theorem B1616779 : Blo 1615006 1616779 := bstep (se 1 (by rfl) ⟨1212584, by rfl⟩ : syracuseStep 1616779 = 2425169) B2425169
theorem B1616791 : Blo 1615006 1616791 := bstep (se 1 (by rfl) ⟨1212593, by rfl⟩ : syracuseStep 1616791 = 2425187) B2425187
theorem B1616811 : Blo 1615006 1616811 := bstep (se 1 (by rfl) ⟨1212608, by rfl⟩ : syracuseStep 1616811 = 2425217) B2425217
theorem B6900653 : Blo 1615006 6900653 := bstep (se 3 (by rfl) ⟨1293872, by rfl⟩ : syracuseStep 6900653 = 2587745) B2587745
theorem B5827501 : Blo 1615006 5827501 := bstep (se 3 (by rfl) ⟨1092656, by rfl⟩ : syracuseStep 5827501 = 2185313) B2185313
theorem B1616823 : Blo 1615006 1616823 := bstep (se 1 (by rfl) ⟨1212617, by rfl⟩ : syracuseStep 1616823 = 2425235) B2425235
theorem B1616843 : Blo 1615006 1616843 := bstep (se 1 (by rfl) ⟨1212632, by rfl⟩ : syracuseStep 1616843 = 2425265) B2425265
theorem B1616855 : Blo 1615006 1616855 := bstep (se 1 (by rfl) ⟨1212641, by rfl⟩ : syracuseStep 1616855 = 2425283) B2425283
theorem B27978713 : Blo 1615006 27978713 := bstep (se 2 (by rfl) ⟨10492017, by rfl⟩ : syracuseStep 27978713 = 20984035) B20984035
theorem B1616875 : Blo 1615006 1616875 := bstep (se 1 (by rfl) ⟨1212656, by rfl⟩ : syracuseStep 1616875 = 2425313) B2425313
theorem B1616887 : Blo 1615006 1616887 := bstep (se 1 (by rfl) ⟨1212665, by rfl⟩ : syracuseStep 1616887 = 2425331) B2425331
theorem B1616907 : Blo 1615006 1616907 := bstep (se 1 (by rfl) ⟨1212680, by rfl⟩ : syracuseStep 1616907 = 2425361) B2425361
theorem B1616919 : Blo 1615006 1616919 := bstep (se 1 (by rfl) ⟨1212689, by rfl⟩ : syracuseStep 1616919 = 2425379) B2425379
theorem B1616939 : Blo 1615006 1616939 := bstep (se 1 (by rfl) ⟨1212704, by rfl⟩ : syracuseStep 1616939 = 2425409) B2425409
theorem B1616951 : Blo 1615006 1616951 := bstep (se 1 (by rfl) ⟨1212713, by rfl⟩ : syracuseStep 1616951 = 2425427) B2425427
theorem B4090945 : Blo 1615006 4090945 := bstep (se 2 (by rfl) ⟨1534104, by rfl⟩ : syracuseStep 4090945 = 3068209) B3068209
theorem B2911307 : Blo 1615006 2911307 := bstep (se 1 (by rfl) ⟨2183480, by rfl⟩ : syracuseStep 2911307 = 4366961) B4366961
theorem B1616971 : Blo 1615006 1616971 := bstep (se 1 (by rfl) ⟨1212728, by rfl⟩ : syracuseStep 1616971 = 2425457) B2425457
theorem B1616983 : Blo 1615006 1616983 := bstep (se 1 (by rfl) ⟨1212737, by rfl⟩ : syracuseStep 1616983 = 2425475) B2425475
theorem B13102181 : Blo 1615006 13102181 := bstep (se 4 (by rfl) ⟨1228329, by rfl⟩ : syracuseStep 13102181 = 2456659) B2456659
theorem B1617003 : Blo 1615006 1617003 := bstep (se 1 (by rfl) ⟨1212752, by rfl⟩ : syracuseStep 1617003 = 2425505) B2425505
theorem B22113431 : Blo 1615006 22113431 := bstep (se 1 (by rfl) ⟨16585073, by rfl⟩ : syracuseStep 22113431 = 33170147) B33170147
theorem B13798673 : Blo 1615006 13798673 := bstep (se 2 (by rfl) ⟨5174502, by rfl⟩ : syracuseStep 13798673 = 10349005) B10349005
theorem B4369729 : Blo 1615006 4369729 := bstep (se 2 (by rfl) ⟨1638648, by rfl⟩ : syracuseStep 4369729 = 3277297) B3277297
theorem B5451083 : Blo 1615006 5451083 := bstep (se 1 (by rfl) ⟨4088312, by rfl⟩ : syracuseStep 5451083 = 8176625) B8176625
theorem B11808179 : Blo 1615006 11808179 := bstep (se 1 (by rfl) ⟨8856134, by rfl⟩ : syracuseStep 11808179 = 17712269) B17712269
theorem B3452377 : Blo 1615006 3452377 := bstep (se 2 (by rfl) ⟨1294641, by rfl⟩ : syracuseStep 3452377 = 2589283) B2589283
theorem B8179217 : Blo 1615006 8179217 := bstep (se 2 (by rfl) ⟨3067206, by rfl⟩ : syracuseStep 8179217 = 6134413) B6134413
theorem B14749219 : Blo 1615006 14749219 := bstep (se 1 (by rfl) ⟨11061914, by rfl⟩ : syracuseStep 14749219 = 22123829) B22123829
theorem B6639155 : Blo 1615006 6639155 := bstep (se 1 (by rfl) ⟨4979366, by rfl⟩ : syracuseStep 6639155 = 9958733) B9958733
theorem B9825857 : Blo 1615006 9825857 := bstep (se 2 (by rfl) ⟨3684696, by rfl⟩ : syracuseStep 9825857 = 7369393) B7369393
theorem B3108439 : Blo 1615006 3108439 := bstep (se 1 (by rfl) ⟨2331329, by rfl⟩ : syracuseStep 3108439 = 4662659) B4662659
theorem B5451353 : Blo 1615006 5451353 := bstep (se 2 (by rfl) ⟨2044257, by rfl⟩ : syracuseStep 5451353 = 4088515) B4088515
theorem B4091543 : Blo 1615006 4091543 := bstep (se 1 (by rfl) ⟨3068657, by rfl⟩ : syracuseStep 4091543 = 6137315) B6137315
theorem B8179379 : Blo 1615006 8179379 := bstep (se 1 (by rfl) ⟨6134534, by rfl⟩ : syracuseStep 8179379 = 12269069) B12269069
theorem B3067571 : Blo 1615006 3067571 := bstep (se 1 (by rfl) ⟨2300678, by rfl⟩ : syracuseStep 3067571 = 4601357) B4601357
theorem B47255237 : Blo 1615006 47255237 := bstep (se 4 (by rfl) ⟨4430178, by rfl⟩ : syracuseStep 47255237 = 8860357) B8860357
theorem B8736473 : Blo 1615006 8736473 := bstep (se 2 (by rfl) ⟨3276177, by rfl⟩ : syracuseStep 8736473 = 6552355) B6552355
theorem B11652929 : Blo 1615006 11652929 := bstep (se 2 (by rfl) ⟨4369848, by rfl⟩ : syracuseStep 11652929 = 8739697) B8739697
theorem B3067723 : Blo 1615006 3067723 := bstep (se 1 (by rfl) ⟨2300792, by rfl⟩ : syracuseStep 3067723 = 4601585) B4601585
theorem B27308107 : Blo 1615006 27308107 := bstep (se 1 (by rfl) ⟨20481080, by rfl⟩ : syracuseStep 27308107 = 40962161) B40962161
theorem B4370507 : Blo 1615006 4370507 := bstep (se 1 (by rfl) ⟨3277880, by rfl⟩ : syracuseStep 4370507 = 6555761) B6555761
theorem B5525597 : Blo 1615006 5525597 := bstep (se 3 (by rfl) ⟨1036049, by rfl⟩ : syracuseStep 5525597 = 2072099) B2072099
theorem B2044055 : Blo 1615006 2044055 := bstep (se 1 (by rfl) ⟨1533041, by rfl⟩ : syracuseStep 2044055 = 3066083) B3066083
theorem B3068057 : Blo 1615006 3068057 := bstep (se 2 (by rfl) ⟨1150521, by rfl⟩ : syracuseStep 3068057 = 2301043) B2301043
theorem B8736947 : Blo 1615006 8736947 := bstep (se 1 (by rfl) ⟨6552710, by rfl⟩ : syracuseStep 8736947 = 13105421) B13105421
theorem B22106317 : Blo 1615006 22106317 := bstep (se 3 (by rfl) ⟨4144934, by rfl⟩ : syracuseStep 22106317 = 8289869) B8289869
theorem B1749259 : Blo 1615006 1749259 := bstep (se 1 (by rfl) ⟨1311944, by rfl⟩ : syracuseStep 1749259 = 2623889) B2623889
theorem B5452055 : Blo 1615006 5452055 := bstep (se 1 (by rfl) ⟨4089041, by rfl⟩ : syracuseStep 5452055 = 8178083) B8178083
theorem B4092353 : Blo 1615006 4092353 := bstep (se 2 (by rfl) ⟨1534632, by rfl⟩ : syracuseStep 4092353 = 3069265) B3069265
theorem B1724971 : Blo 1615006 1724971 := bstep (se 1 (by rfl) ⟨1293728, by rfl⟩ : syracuseStep 1724971 = 2587457) B2587457
theorem B12268097 : Blo 1615006 12268097 := bstep (se 2 (by rfl) ⟨4600536, by rfl⟩ : syracuseStep 12268097 = 9201073) B9201073
theorem B3633803 : Blo 1615006 3633803 := bstep (se 1 (by rfl) ⟨2725352, by rfl⟩ : syracuseStep 3633803 = 5450705) B5450705
theorem B3633857 : Blo 1615006 3633857 := bstep (se 2 (by rfl) ⟨1362696, by rfl⟩ : syracuseStep 3633857 = 2725393) B2725393
theorem B3068695 : Blo 1615006 3068695 := bstep (se 1 (by rfl) ⟨2301521, by rfl⟩ : syracuseStep 3068695 = 4603043) B4603043
theorem B27595565 : Blo 1615006 27595565 := bstep (se 3 (by rfl) ⟨5174168, by rfl⟩ : syracuseStep 27595565 = 10348337) B10348337
theorem B5452595 : Blo 1615006 5452595 := bstep (se 1 (by rfl) ⟨4089446, by rfl⟩ : syracuseStep 5452595 = 8178893) B8178893
theorem B4600651 : Blo 1615006 4600651 := bstep (se 1 (by rfl) ⟨3450488, by rfl⟩ : syracuseStep 4600651 = 6900977) B6900977
theorem B2044759 : Blo 1615006 2044759 := bstep (se 1 (by rfl) ⟨1533569, by rfl⟩ : syracuseStep 2044759 = 3067139) B3067139
theorem B6902617 : Blo 1615006 6902617 := bstep (se 2 (by rfl) ⟨2588481, by rfl⟩ : syracuseStep 6902617 = 5176963) B5176963
theorem B3634073 : Blo 1615006 3634073 := bstep (se 2 (by rfl) ⟨1362777, by rfl⟩ : syracuseStep 3634073 = 2725555) B2725555
theorem B69874649 : Blo 1615006 69874649 := bstep (se 2 (by rfl) ⟨26202993, by rfl⟩ : syracuseStep 69874649 = 52405987) B52405987
theorem B4092889 : Blo 1615006 4092889 := bstep (se 2 (by rfl) ⟨1534833, by rfl⟩ : syracuseStep 4092889 = 3069667) B3069667
theorem B3634163 : Blo 1615006 3634163 := bstep (se 1 (by rfl) ⟨2725622, by rfl⟩ : syracuseStep 3634163 = 5451245) B5451245
theorem B3634199 : Blo 1615006 3634199 := bstep (se 1 (by rfl) ⟨2725649, by rfl⟩ : syracuseStep 3634199 = 5451299) B5451299
theorem B2184215 : Blo 1615006 2184215 := bstep (se 1 (by rfl) ⟨1638161, by rfl⟩ : syracuseStep 2184215 = 3276323) B3276323
theorem B5452865 : Blo 1615006 5452865 := bstep (se 2 (by rfl) ⟨2044824, by rfl⟩ : syracuseStep 5452865 = 4089649) B4089649
theorem B4600925 : Blo 1615006 4600925 := bstep (se 3 (by rfl) ⟨862673, by rfl⟩ : syracuseStep 4600925 = 1725347) B1725347
theorem B3634379 : Blo 1615006 3634379 := bstep (se 1 (by rfl) ⟨2725784, by rfl⟩ : syracuseStep 3634379 = 5451569) B5451569
theorem B10360025 : Blo 1615006 10360025 := bstep (se 2 (by rfl) ⟨3885009, by rfl⟩ : syracuseStep 10360025 = 7770019) B7770019
theorem B3634433 : Blo 1615006 3634433 := bstep (se 2 (by rfl) ⟨1362912, by rfl⟩ : syracuseStep 3634433 = 2725825) B2725825
theorem B5174579 : Blo 1615006 5174579 := bstep (se 1 (by rfl) ⟨3880934, by rfl⟩ : syracuseStep 5174579 = 7761869) B7761869
theorem B3634649 : Blo 1615006 3634649 := bstep (se 2 (by rfl) ⟨1362993, by rfl⟩ : syracuseStep 3634649 = 2725987) B2725987
theorem B9205265 : Blo 1615006 9205265 := bstep (se 2 (by rfl) ⟨3451974, by rfl⟩ : syracuseStep 9205265 = 6903949) B6903949
theorem B3634739 : Blo 1615006 3634739 := bstep (se 1 (by rfl) ⟨2726054, by rfl⟩ : syracuseStep 3634739 = 5452109) B5452109
theorem B8181323 : Blo 1615006 8181323 := bstep (se 1 (by rfl) ⟨6135992, by rfl⟩ : syracuseStep 8181323 = 12271985) B12271985
theorem B3069515 : Blo 1615006 3069515 := bstep (se 1 (by rfl) ⟨2302136, by rfl⟩ : syracuseStep 3069515 = 4604273) B4604273
theorem B3634775 : Blo 1615006 3634775 := bstep (se 1 (by rfl) ⟨2726081, by rfl⟩ : syracuseStep 3634775 = 5452163) B5452163
theorem B1726039 : Blo 1615006 1726039 := bstep (se 1 (by rfl) ⟨1294529, by rfl⟩ : syracuseStep 1726039 = 2589059) B2589059
theorem B5453405 : Blo 1615006 5453405 := bstep (se 3 (by rfl) ⟨1022513, by rfl⟩ : syracuseStep 5453405 = 2045027) B2045027
theorem B3069569 : Blo 1615006 3069569 := bstep (se 2 (by rfl) ⟨1151088, by rfl⟩ : syracuseStep 3069569 = 2302177) B2302177
theorem B6133427 : Blo 1615006 6133427 := bstep (se 1 (by rfl) ⟨4600070, by rfl⟩ : syracuseStep 6133427 = 9200141) B9200141
theorem B6133441 : Blo 1615006 6133441 := bstep (se 2 (by rfl) ⟨2300040, by rfl⟩ : syracuseStep 6133441 = 4600081) B4600081
theorem B2725643 : Blo 1615006 2725643 := bstep (se 1 (by rfl) ⟨2044232, by rfl⟩ : syracuseStep 2725643 = 4088465) B4088465
theorem B3634955 : Blo 1615006 3634955 := bstep (se 1 (by rfl) ⟨2726216, by rfl⟩ : syracuseStep 3634955 = 5452433) B5452433
theorem B6903575 : Blo 1615006 6903575 := bstep (se 1 (by rfl) ⟨5177681, by rfl⟩ : syracuseStep 6903575 = 10355363) B10355363
theorem B2422553 : Blo 1615006 2422553 := bstep (se 2 (by rfl) ⟨908457, by rfl⟩ : syracuseStep 2422553 = 1816915) B1816915
theorem B3635009 : Blo 1615006 3635009 := bstep (se 2 (by rfl) ⟨1363128, by rfl⟩ : syracuseStep 3635009 = 2726257) B2726257
theorem B2422667 : Blo 1615006 2422667 := bstep (se 1 (by rfl) ⟨1817000, by rfl⟩ : syracuseStep 2422667 = 3634001) B3634001
theorem B2725771 : Blo 1615006 2725771 := bstep (se 1 (by rfl) ⟨2044328, by rfl⟩ : syracuseStep 2725771 = 4088657) B4088657
theorem B2422679 : Blo 1615006 2422679 := bstep (se 1 (by rfl) ⟨1817009, by rfl⟩ : syracuseStep 2422679 = 3634019) B3634019
theorem B2422745 : Blo 1615006 2422745 := bstep (se 2 (by rfl) ⟨908529, by rfl⟩ : syracuseStep 2422745 = 1817059) B1817059
theorem B9205721 : Blo 1615006 9205721 := bstep (se 2 (by rfl) ⟨3452145, by rfl⟩ : syracuseStep 9205721 = 6904291) B6904291
theorem B2299927 : Blo 1615006 2299927 := bstep (se 1 (by rfl) ⟨1724945, by rfl⟩ : syracuseStep 2299927 = 3449891) B3449891
theorem B2725913 : Blo 1615006 2725913 := bstep (se 2 (by rfl) ⟨1022217, by rfl⟩ : syracuseStep 2725913 = 2044435) B2044435
theorem B3635225 : Blo 1615006 3635225 := bstep (se 2 (by rfl) ⟨1363209, by rfl⟩ : syracuseStep 3635225 = 2726419) B2726419
theorem B2422859 : Blo 1615006 2422859 := bstep (se 1 (by rfl) ⟨1817144, by rfl⟩ : syracuseStep 2422859 = 3634289) B3634289
theorem B2422871 : Blo 1615006 2422871 := bstep (se 1 (by rfl) ⟨1817153, by rfl⟩ : syracuseStep 2422871 = 3634307) B3634307
theorem B4667485 : Blo 1615006 4667485 := bstep (se 3 (by rfl) ⟨875153, by rfl⟩ : syracuseStep 4667485 = 1750307) B1750307
theorem B3635315 : Blo 1615006 3635315 := bstep (se 1 (by rfl) ⟨2726486, by rfl⟩ : syracuseStep 3635315 = 5452973) B5452973
theorem B3635351 : Blo 1615006 3635351 := bstep (se 1 (by rfl) ⟨2726513, by rfl⟩ : syracuseStep 3635351 = 5453027) B5453027
theorem B2455705 : Blo 1615006 2455705 := bstep (se 2 (by rfl) ⟨920889, by rfl⟩ : syracuseStep 2455705 = 1841779) B1841779
theorem B2422937 : Blo 1615006 2422937 := bstep (se 2 (by rfl) ⟨908601, by rfl⟩ : syracuseStep 2422937 = 1817203) B1817203
theorem B2726041 : Blo 1615006 2726041 := bstep (se 2 (by rfl) ⟨1022265, by rfl⟩ : syracuseStep 2726041 = 2044531) B2044531
theorem B2423051 : Blo 1615006 2423051 := bstep (se 1 (by rfl) ⟨1817288, by rfl⟩ : syracuseStep 2423051 = 3634577) B3634577
theorem B2423063 : Blo 1615006 2423063 := bstep (se 1 (by rfl) ⟨1817297, by rfl⟩ : syracuseStep 2423063 = 3634595) B3634595
theorem B5822785 : Blo 1615006 5822785 := bstep (se 2 (by rfl) ⟨2183544, by rfl⟩ : syracuseStep 5822785 = 4367089) B4367089
theorem B3635531 : Blo 1615006 3635531 := bstep (se 1 (by rfl) ⟨2726648, by rfl⟩ : syracuseStep 3635531 = 5453297) B5453297
theorem B2423129 : Blo 1615006 2423129 := bstep (se 2 (by rfl) ⟨908673, by rfl⟩ : syracuseStep 2423129 = 1817347) B1817347
theorem B1816951 : Blo 1615006 1816951 := bstep (se 1 (by rfl) ⟨1362713, by rfl⟩ : syracuseStep 1816951 = 2725427) B2725427
theorem B3635585 : Blo 1615006 3635585 := bstep (se 2 (by rfl) ⟨1363344, by rfl⟩ : syracuseStep 3635585 = 2726689) B2726689
theorem B9197975 : Blo 1615006 9197975 := bstep (se 1 (by rfl) ⟨6898481, by rfl⟩ : syracuseStep 9197975 = 13796963) B13796963
theorem B5757335 : Blo 1615006 5757335 := bstep (se 1 (by rfl) ⟨4318001, by rfl⟩ : syracuseStep 5757335 = 8636003) B8636003
theorem B27621809 : Blo 1615006 27621809 := bstep (se 2 (by rfl) ⟨10358178, by rfl⟩ : syracuseStep 27621809 = 20716357) B20716357
theorem B2423243 : Blo 1615006 2423243 := bstep (se 1 (by rfl) ⟨1817432, by rfl⟩ : syracuseStep 2423243 = 3634865) B3634865
theorem B2423255 : Blo 1615006 2423255 := bstep (se 1 (by rfl) ⟨1817441, by rfl⟩ : syracuseStep 2423255 = 3634883) B3634883
theorem B12270041 : Blo 1615006 12270041 := bstep (se 2 (by rfl) ⟨4601265, by rfl⟩ : syracuseStep 12270041 = 9202531) B9202531
theorem B2841047 : Blo 1615006 2841047 := bstep (se 1 (by rfl) ⟨2130785, by rfl⟩ : syracuseStep 2841047 = 4261571) B4261571
theorem B2046475 : Blo 1615006 2046475 := bstep (se 1 (by rfl) ⟨1534856, by rfl⟩ : syracuseStep 2046475 = 3069713) B3069713
theorem B2423321 : Blo 1615006 2423321 := bstep (se 2 (by rfl) ⟨908745, by rfl⟩ : syracuseStep 2423321 = 1817491) B1817491
theorem B1817131 : Blo 1615006 1817131 := bstep (se 1 (by rfl) ⟨1362848, by rfl⟩ : syracuseStep 1817131 = 2725697) B2725697
theorem B2300491 : Blo 1615006 2300491 := bstep (se 1 (by rfl) ⟨1725368, by rfl⟩ : syracuseStep 2300491 = 3450737) B3450737
theorem B3635801 : Blo 1615006 3635801 := bstep (se 2 (by rfl) ⟨1363425, by rfl⟩ : syracuseStep 3635801 = 2726851) B2726851
theorem B2423435 : Blo 1615006 2423435 := bstep (se 1 (by rfl) ⟨1817576, by rfl⟩ : syracuseStep 2423435 = 3635153) B3635153
theorem B1817239 : Blo 1615006 1817239 := bstep (se 1 (by rfl) ⟨1362929, by rfl⟩ : syracuseStep 1817239 = 2725859) B2725859
theorem B2423447 : Blo 1615006 2423447 := bstep (se 1 (by rfl) ⟨1817585, by rfl⟩ : syracuseStep 2423447 = 3635171) B3635171
theorem B3635891 : Blo 1615006 3635891 := bstep (se 1 (by rfl) ⟨2726918, by rfl⟩ : syracuseStep 3635891 = 5453837) B5453837
theorem B5454539 : Blo 1615006 5454539 := bstep (se 1 (by rfl) ⟨4090904, by rfl⟩ : syracuseStep 5454539 = 8181809) B8181809
theorem B2423513 : Blo 1615006 2423513 := bstep (se 2 (by rfl) ⟨908817, by rfl⟩ : syracuseStep 2423513 = 1817635) B1817635
theorem B2726615 : Blo 1615006 2726615 := bstep (se 1 (by rfl) ⟨2044961, by rfl⟩ : syracuseStep 2726615 = 4089923) B4089923
theorem B3635927 : Blo 1615006 3635927 := bstep (se 1 (by rfl) ⟨2726945, by rfl⟩ : syracuseStep 3635927 = 5453891) B5453891
theorem B8739629 : Blo 1615006 8739629 := bstep (se 3 (by rfl) ⟨1638680, by rfl⟩ : syracuseStep 8739629 = 3277361) B3277361
theorem B1817419 : Blo 1615006 1817419 := bstep (se 1 (by rfl) ⟨1363064, by rfl⟩ : syracuseStep 1817419 = 2726129) B2726129
theorem B2423627 : Blo 1615006 2423627 := bstep (se 1 (by rfl) ⟨1817720, by rfl⟩ : syracuseStep 2423627 = 3635441) B3635441
theorem B2423639 : Blo 1615006 2423639 := bstep (se 1 (by rfl) ⟨1817729, by rfl⟩ : syracuseStep 2423639 = 3635459) B3635459
theorem B2726743 : Blo 1615006 2726743 := bstep (se 1 (by rfl) ⟨2045057, by rfl⟩ : syracuseStep 2726743 = 4090115) B4090115
theorem B3636107 : Blo 1615006 3636107 := bstep (se 1 (by rfl) ⟨2727080, by rfl⟩ : syracuseStep 3636107 = 5454161) B5454161
theorem B2423705 : Blo 1615006 2423705 := bstep (se 2 (by rfl) ⟨908889, by rfl⟩ : syracuseStep 2423705 = 1817779) B1817779
theorem B1817527 : Blo 1615006 1817527 := bstep (se 1 (by rfl) ⟨1363145, by rfl⟩ : syracuseStep 1817527 = 2726291) B2726291
theorem B3636161 : Blo 1615006 3636161 := bstep (se 2 (by rfl) ⟨1363560, by rfl⟩ : syracuseStep 3636161 = 2727121) B2727121
theorem B5454809 : Blo 1615006 5454809 := bstep (se 2 (by rfl) ⟨2045553, by rfl⟩ : syracuseStep 5454809 = 4091107) B4091107
theorem B12278789 : Blo 1615006 12278789 := bstep (se 4 (by rfl) ⟨1151136, by rfl⟩ : syracuseStep 12278789 = 2302273) B2302273
theorem B2423819 : Blo 1615006 2423819 := bstep (se 1 (by rfl) ⟨1817864, by rfl⟩ : syracuseStep 2423819 = 3635729) B3635729
theorem B1637399 : Blo 1615006 1637399 := bstep (se 1 (by rfl) ⟨1228049, by rfl⟩ : syracuseStep 1637399 = 2456099) B2456099
theorem B2423831 : Blo 1615006 2423831 := bstep (se 1 (by rfl) ⟨1817873, by rfl⟩ : syracuseStep 2423831 = 3635747) B3635747
theorem B53869637 : Blo 1615006 53869637 := bstep (se 4 (by rfl) ⟨5050278, by rfl⟩ : syracuseStep 53869637 = 10100557) B10100557
theorem B2423897 : Blo 1615006 2423897 := bstep (se 2 (by rfl) ⟨908961, by rfl⟩ : syracuseStep 2423897 = 1817923) B1817923
theorem B1817707 : Blo 1615006 1817707 := bstep (se 1 (by rfl) ⟨1363280, by rfl⟩ : syracuseStep 1817707 = 2726561) B2726561
theorem B3636377 : Blo 1615006 3636377 := bstep (se 2 (by rfl) ⟨1363641, by rfl⟩ : syracuseStep 3636377 = 2727283) B2727283
theorem B2424011 : Blo 1615006 2424011 := bstep (se 1 (by rfl) ⟨1818008, by rfl⟩ : syracuseStep 2424011 = 3636017) B3636017
theorem B1817815 : Blo 1615006 1817815 := bstep (se 1 (by rfl) ⟨1363361, by rfl⟩ : syracuseStep 1817815 = 2726723) B2726723
theorem B2424023 : Blo 1615006 2424023 := bstep (se 1 (by rfl) ⟨1818017, by rfl⟩ : syracuseStep 2424023 = 3636035) B3636035
theorem B3636467 : Blo 1615006 3636467 := bstep (se 1 (by rfl) ⟨2727350, by rfl⟩ : syracuseStep 3636467 = 5454701) B5454701
theorem B3636503 : Blo 1615006 3636503 := bstep (se 1 (by rfl) ⟨2727377, by rfl⟩ : syracuseStep 3636503 = 5454755) B5454755
theorem B2424089 : Blo 1615006 2424089 := bstep (se 2 (by rfl) ⟨909033, by rfl⟩ : syracuseStep 2424089 = 1818067) B1818067
theorem B8183105 : Blo 1615006 8183105 := bstep (se 2 (by rfl) ⟨3068664, by rfl⟩ : syracuseStep 8183105 = 6137329) B6137329
theorem B4603225 : Blo 1615006 4603225 := bstep (se 2 (by rfl) ⟨1726209, by rfl⟩ : syracuseStep 4603225 = 3452419) B3452419
theorem B1817995 : Blo 1615006 1817995 := bstep (se 1 (by rfl) ⟨1363496, by rfl⟩ : syracuseStep 1817995 = 2726993) B2726993
theorem B2424203 : Blo 1615006 2424203 := bstep (se 1 (by rfl) ⟨1818152, by rfl⟩ : syracuseStep 2424203 = 3636305) B3636305
theorem B2424215 : Blo 1615006 2424215 := bstep (se 1 (by rfl) ⟨1818161, by rfl⟩ : syracuseStep 2424215 = 3636323) B3636323
theorem B2727371 : Blo 1615006 2727371 := bstep (se 1 (by rfl) ⟨2045528, by rfl⟩ : syracuseStep 2727371 = 4091057) B4091057
theorem B3636683 : Blo 1615006 3636683 := bstep (se 1 (by rfl) ⟨2727512, by rfl⟩ : syracuseStep 3636683 = 5455025) B5455025
theorem B2424281 : Blo 1615006 2424281 := bstep (se 2 (by rfl) ⟨909105, by rfl⟩ : syracuseStep 2424281 = 1818211) B1818211
theorem B1818103 : Blo 1615006 1818103 := bstep (se 1 (by rfl) ⟨1363577, by rfl⟩ : syracuseStep 1818103 = 2727155) B2727155
theorem B3636737 : Blo 1615006 3636737 := bstep (se 2 (by rfl) ⟨1363776, by rfl⟩ : syracuseStep 3636737 = 2727553) B2727553
theorem B6553133 : Blo 1615006 6553133 := bstep (se 3 (by rfl) ⟨1228712, by rfl⟩ : syracuseStep 6553133 = 2457425) B2457425
theorem B6135371 : Blo 1615006 6135371 := bstep (se 1 (by rfl) ⟨4601528, by rfl⟩ : syracuseStep 6135371 = 9203057) B9203057
theorem B2424395 : Blo 1615006 2424395 := bstep (se 1 (by rfl) ⟨1818296, by rfl⟩ : syracuseStep 2424395 = 3636593) B3636593
theorem B2727499 : Blo 1615006 2727499 := bstep (se 1 (by rfl) ⟨2045624, by rfl⟩ : syracuseStep 2727499 = 4091249) B4091249
theorem B2424407 : Blo 1615006 2424407 := bstep (se 1 (by rfl) ⟨1818305, by rfl⟩ : syracuseStep 2424407 = 3636611) B3636611
theorem B6135385 : Blo 1615006 6135385 := bstep (se 2 (by rfl) ⟨2300769, by rfl⟩ : syracuseStep 6135385 = 4601539) B4601539
theorem B1941131 : Blo 1615006 1941131 := bstep (se 1 (by rfl) ⟨1455848, by rfl⟩ : syracuseStep 1941131 = 2911697) B2911697
theorem B6217361 : Blo 1615006 6217361 := bstep (se 2 (by rfl) ⟨2331510, by rfl⟩ : syracuseStep 6217361 = 4663021) B4663021
theorem B3882647 : Blo 1615006 3882647 := bstep (se 1 (by rfl) ⟨2911985, by rfl⟩ : syracuseStep 3882647 = 5823971) B5823971
theorem B5455511 : Blo 1615006 5455511 := bstep (se 1 (by rfl) ⟨4091633, by rfl⟩ : syracuseStep 5455511 = 8183267) B8183267
theorem B2424473 : Blo 1615006 2424473 := bstep (se 2 (by rfl) ⟨909177, by rfl⟩ : syracuseStep 2424473 = 1818355) B1818355
theorem B1818283 : Blo 1615006 1818283 := bstep (se 1 (by rfl) ⟨1363712, by rfl⟩ : syracuseStep 1818283 = 2727425) B2727425
theorem B2727641 : Blo 1615006 2727641 := bstep (se 2 (by rfl) ⟨1022865, by rfl⟩ : syracuseStep 2727641 = 2045731) B2045731
theorem B3636953 : Blo 1615006 3636953 := bstep (se 2 (by rfl) ⟨1363857, by rfl⟩ : syracuseStep 3636953 = 2727715) B2727715
theorem B2424587 : Blo 1615006 2424587 := bstep (se 1 (by rfl) ⟨1818440, by rfl⟩ : syracuseStep 2424587 = 3636881) B3636881
theorem B1818391 : Blo 1615006 1818391 := bstep (se 1 (by rfl) ⟨1363793, by rfl⟩ : syracuseStep 1818391 = 2727587) B2727587
theorem B2424599 : Blo 1615006 2424599 := bstep (se 1 (by rfl) ⟨1818449, by rfl⟩ : syracuseStep 2424599 = 3636899) B3636899
theorem B3637043 : Blo 1615006 3637043 := bstep (se 1 (by rfl) ⟨2727782, by rfl⟩ : syracuseStep 3637043 = 5455565) B5455565
theorem B4915009 : Blo 1615006 4915009 := bstep (se 2 (by rfl) ⟨1843128, by rfl⟩ : syracuseStep 4915009 = 3686257) B3686257
theorem B3637079 : Blo 1615006 3637079 := bstep (se 1 (by rfl) ⟨2727809, by rfl⟩ : syracuseStep 3637079 = 5455619) B5455619
theorem B2424665 : Blo 1615006 2424665 := bstep (se 2 (by rfl) ⟨909249, by rfl⟩ : syracuseStep 2424665 = 1818499) B1818499
theorem B2727769 : Blo 1615006 2727769 := bstep (se 2 (by rfl) ⟨1022913, by rfl⟩ : syracuseStep 2727769 = 2045827) B2045827
theorem B11968357 : Blo 1615006 11968357 := bstep (se 4 (by rfl) ⟨1122033, by rfl⟩ : syracuseStep 11968357 = 2244067) B2244067
theorem B4603841 : Blo 1615006 4603841 := bstep (se 2 (by rfl) ⟨1726440, by rfl⟩ : syracuseStep 4603841 = 3452881) B3452881
theorem B1818571 : Blo 1615006 1818571 := bstep (se 1 (by rfl) ⟨1363928, by rfl⟩ : syracuseStep 1818571 = 2727857) B2727857
theorem B2424779 : Blo 1615006 2424779 := bstep (se 1 (by rfl) ⟨1818584, by rfl⟩ : syracuseStep 2424779 = 3637169) B3637169
theorem B2424791 : Blo 1615006 2424791 := bstep (se 1 (by rfl) ⟨1818593, by rfl⟩ : syracuseStep 2424791 = 3637187) B3637187
theorem B2424839 : Blo 1615006 2424839 := bstep (se 1 (by rfl) ⟨1818629, by rfl⟩ : syracuseStep 2424839 = 3637259) B3637259
theorem B2588687 : Blo 1615006 2588687 := bstep (se 1 (by rfl) ⟨1941515, by rfl⟩ : syracuseStep 2588687 = 3883031) B3883031
theorem B23625751 : Blo 1615006 23625751 := bstep (se 1 (by rfl) ⟨17719313, by rfl⟩ : syracuseStep 23625751 = 35438627) B35438627
theorem B2424875 : Blo 1615006 2424875 := bstep (se 1 (by rfl) ⟨1818656, by rfl⟩ : syracuseStep 2424875 = 3637313) B3637313
theorem B4366397 : Blo 1615006 4366397 := bstep (se 3 (by rfl) ⟨818699, by rfl⟩ : syracuseStep 4366397 = 1637399) B1637399
theorem B2424905 : Blo 1615006 2424905 := bstep (se 2 (by rfl) ⟨909339, by rfl⟩ : syracuseStep 2424905 = 1818679) B1818679
theorem B5824631 : Blo 1615006 5824631 := bstep (se 1 (by rfl) ⟨4368473, by rfl⟩ : syracuseStep 5824631 = 8736947) B8736947
theorem B3637367 : Blo 1615006 3637367 := bstep (se 1 (by rfl) ⟨2728025, by rfl⟩ : syracuseStep 3637367 = 5456051) B5456051
theorem B2425019 : Blo 1615006 2425019 := bstep (se 1 (by rfl) ⟨1818764, by rfl⟩ : syracuseStep 2425019 = 3637529) B3637529
theorem B4088009 : Blo 1615006 4088009 := bstep (se 2 (by rfl) ⟨1533003, by rfl⟩ : syracuseStep 4088009 = 3066007) B3066007
theorem B23298293 : Blo 1615006 23298293 := bstep (se 5 (by rfl) ⟨1092107, by rfl⟩ : syracuseStep 23298293 = 2184215) B2184215
theorem B2425079 : Blo 1615006 2425079 := bstep (se 1 (by rfl) ⟨1818809, by rfl⟩ : syracuseStep 2425079 = 3637619) B3637619
theorem B2425103 : Blo 1615006 2425103 := bstep (se 1 (by rfl) ⟨1818827, by rfl⟩ : syracuseStep 2425103 = 3637655) B3637655
theorem B1818895 : Blo 1615006 1818895 := bstep (se 1 (by rfl) ⟨1364171, by rfl⟩ : syracuseStep 1818895 = 2728343) B2728343
theorem B29475089 : Blo 1615006 29475089 := bstep (se 2 (by rfl) ⟨11053158, by rfl⟩ : syracuseStep 29475089 = 22106317) B22106317
theorem B3637547 : Blo 1615006 3637547 := bstep (se 1 (by rfl) ⟨2728160, by rfl⟩ : syracuseStep 3637547 = 5456321) B5456321
theorem B2728235 : Blo 1615006 2728235 := bstep (se 1 (by rfl) ⟨2046176, by rfl⟩ : syracuseStep 2728235 = 4092353) B4092353
theorem B2425145 : Blo 1615006 2425145 := bstep (se 2 (by rfl) ⟨909429, by rfl⟩ : syracuseStep 2425145 = 1818859) B1818859
theorem B2425223 : Blo 1615006 2425223 := bstep (se 1 (by rfl) ⟨1818917, by rfl⟩ : syracuseStep 2425223 = 3637835) B3637835
theorem B2425259 : Blo 1615006 2425259 := bstep (se 1 (by rfl) ⟨1818944, by rfl⟩ : syracuseStep 2425259 = 3637889) B3637889
theorem B2425289 : Blo 1615006 2425289 := bstep (se 2 (by rfl) ⟨909483, by rfl⟩ : syracuseStep 2425289 = 1818967) B1818967
theorem B8176139 : Blo 1615006 8176139 := bstep (se 1 (by rfl) ⟨6132104, by rfl⟩ : syracuseStep 8176139 = 12264209) B12264209
theorem B4088353 : Blo 1615006 4088353 := bstep (se 2 (by rfl) ⟨1533132, by rfl⟩ : syracuseStep 4088353 = 3066265) B3066265
theorem B3277345 : Blo 1615006 3277345 := bstep (se 2 (by rfl) ⟨1229004, by rfl⟩ : syracuseStep 3277345 = 2458009) B2458009
theorem B9208363 : Blo 1615006 9208363 := bstep (se 1 (by rfl) ⟨6906272, by rfl⟩ : syracuseStep 9208363 = 13812545) B13812545
theorem B2425403 : Blo 1615006 2425403 := bstep (se 1 (by rfl) ⟨1819052, by rfl⟩ : syracuseStep 2425403 = 3638105) B3638105
theorem B4915799 : Blo 1615006 4915799 := bstep (se 1 (by rfl) ⟨3686849, by rfl⟩ : syracuseStep 4915799 = 7373699) B7373699
theorem B2425463 : Blo 1615006 2425463 := bstep (se 1 (by rfl) ⟨1819097, by rfl⟩ : syracuseStep 2425463 = 3638195) B3638195
theorem B2425487 : Blo 1615006 2425487 := bstep (se 1 (by rfl) ⟨1819115, by rfl⟩ : syracuseStep 2425487 = 3638231) B3638231
theorem B3277459 : Blo 1615006 3277459 := bstep (se 1 (by rfl) ⟨2458094, by rfl⟩ : syracuseStep 3277459 = 4916189) B4916189
theorem B3637907 : Blo 1615006 3637907 := bstep (se 1 (by rfl) ⟨2728430, by rfl⟩ : syracuseStep 3637907 = 5456861) B5456861
theorem B8176301 : Blo 1615006 8176301 := bstep (se 3 (by rfl) ⟨1533056, by rfl⟩ : syracuseStep 8176301 = 3066113) B3066113
theorem B2728633 : Blo 1615006 2728633 := bstep (se 2 (by rfl) ⟨1023237, by rfl⟩ : syracuseStep 2728633 = 2046475) B2046475
theorem B3637961 : Blo 1615006 3637961 := bstep (se 2 (by rfl) ⟨1364235, by rfl⟩ : syracuseStep 3637961 = 2728471) B2728471
theorem B5456699 : Blo 1615006 5456699 := bstep (se 1 (by rfl) ⟨4092524, by rfl⟩ : syracuseStep 5456699 = 8185049) B8185049
theorem B6906683 : Blo 1615006 6906683 := bstep (se 1 (by rfl) ⟨5180012, by rfl⟩ : syracuseStep 6906683 = 10360025) B10360025
theorem B3449719 : Blo 1615006 3449719 := bstep (se 1 (by rfl) ⟨2587289, by rfl⟩ : syracuseStep 3449719 = 5174579) B5174579
theorem B6136843 : Blo 1615006 6136843 := bstep (se 1 (by rfl) ⟨4602632, by rfl⟩ : syracuseStep 6136843 = 9205265) B9205265
theorem B6906941 : Blo 1615006 6906941 := bstep (se 3 (by rfl) ⟨1295051, by rfl⟩ : syracuseStep 6906941 = 2590103) B2590103
theorem B4088951 : Blo 1615006 4088951 := bstep (se 1 (by rfl) ⟨3066713, by rfl⟩ : syracuseStep 4088951 = 6133427) B6133427
theorem B2589815 : Blo 1615006 2589815 := bstep (se 1 (by rfl) ⟨1942361, by rfl⟩ : syracuseStep 2589815 = 3884723) B3884723
theorem B1615035 : Blo 1615006 1615035 := bstep (se 1 (by rfl) ⟨1211276, by rfl⟩ : syracuseStep 1615035 = 2422553) B2422553
theorem B1615111 : Blo 1615006 1615111 := bstep (se 1 (by rfl) ⟨1211333, by rfl⟩ : syracuseStep 1615111 = 2422667) B2422667
theorem B1615119 : Blo 1615006 1615119 := bstep (se 1 (by rfl) ⟨1211339, by rfl⟩ : syracuseStep 1615119 = 2422679) B2422679
theorem B5457185 : Blo 1615006 5457185 := bstep (se 2 (by rfl) ⟨2046444, by rfl⟩ : syracuseStep 5457185 = 4092889) B4092889
theorem B1615163 : Blo 1615006 1615163 := bstep (se 1 (by rfl) ⟨1211372, by rfl⟩ : syracuseStep 1615163 = 2422745) B2422745
theorem B6137147 : Blo 1615006 6137147 := bstep (se 1 (by rfl) ⟨4602860, by rfl⟩ : syracuseStep 6137147 = 9205721) B9205721
theorem B1615239 : Blo 1615006 1615239 := bstep (se 1 (by rfl) ⟨1211429, by rfl⟩ : syracuseStep 1615239 = 2422859) B2422859
theorem B1615247 : Blo 1615006 1615247 := bstep (se 1 (by rfl) ⟨1211435, by rfl⟩ : syracuseStep 1615247 = 2422871) B2422871
theorem B5178809 : Blo 1615006 5178809 := bstep (se 2 (by rfl) ⟨1942053, by rfl⟩ : syracuseStep 5178809 = 3884107) B3884107
theorem B1615291 : Blo 1615006 1615291 := bstep (se 1 (by rfl) ⟨1211468, by rfl⟩ : syracuseStep 1615291 = 2422937) B2422937
theorem B1615367 : Blo 1615006 1615367 := bstep (se 1 (by rfl) ⟨1211525, by rfl⟩ : syracuseStep 1615367 = 2423051) B2423051
theorem B1615375 : Blo 1615006 1615375 := bstep (se 1 (by rfl) ⟨1211531, by rfl⟩ : syracuseStep 1615375 = 2423063) B2423063
theorem B11060765 : Blo 1615006 11060765 := bstep (se 3 (by rfl) ⟨2073893, by rfl⟩ : syracuseStep 11060765 = 4147787) B4147787
theorem B8185373 : Blo 1615006 8185373 := bstep (se 3 (by rfl) ⟨1534757, by rfl⟩ : syracuseStep 8185373 = 3069515) B3069515
theorem B1615419 : Blo 1615006 1615419 := bstep (se 1 (by rfl) ⟨1211564, by rfl⟩ : syracuseStep 1615419 = 2423129) B2423129
theorem B4146803 : Blo 1615006 4146803 := bstep (se 1 (by rfl) ⟨3110102, by rfl⟩ : syracuseStep 4146803 = 6220205) B6220205
theorem B1615495 : Blo 1615006 1615495 := bstep (se 1 (by rfl) ⟨1211621, by rfl⟩ : syracuseStep 1615495 = 2423243) B2423243
theorem B1615503 : Blo 1615006 1615503 := bstep (se 1 (by rfl) ⟨1211627, by rfl⟩ : syracuseStep 1615503 = 2423255) B2423255
theorem B1894031 : Blo 1615006 1894031 := bstep (se 1 (by rfl) ⟨1420523, by rfl⟩ : syracuseStep 1894031 = 2841047) B2841047
theorem B1615547 : Blo 1615006 1615547 := bstep (se 1 (by rfl) ⟨1211660, by rfl⟩ : syracuseStep 1615547 = 2423321) B2423321
theorem B78644965 : Blo 1615006 78644965 := bstep (se 4 (by rfl) ⟨7372965, by rfl⟩ : syracuseStep 78644965 = 14745931) B14745931
theorem B5826305 : Blo 1615006 5826305 := bstep (se 2 (by rfl) ⟨2184864, by rfl⟩ : syracuseStep 5826305 = 4369729) B4369729
theorem B1615623 : Blo 1615006 1615623 := bstep (se 1 (by rfl) ⟨1211717, by rfl⟩ : syracuseStep 1615623 = 2423435) B2423435
theorem B1615631 : Blo 1615006 1615631 := bstep (se 1 (by rfl) ⟨1211723, by rfl⟩ : syracuseStep 1615631 = 2423447) B2423447
theorem B6137633 : Blo 1615006 6137633 := bstep (se 2 (by rfl) ⟨2301612, by rfl⟩ : syracuseStep 6137633 = 4603225) B4603225
theorem B1615675 : Blo 1615006 1615675 := bstep (se 1 (by rfl) ⟨1211756, by rfl⟩ : syracuseStep 1615675 = 2423513) B2423513
theorem B104826737 : Blo 1615006 104826737 := bstep (se 2 (by rfl) ⟨39310026, by rfl⟩ : syracuseStep 104826737 = 78620053) B78620053
theorem B5826419 : Blo 1615006 5826419 := bstep (se 1 (by rfl) ⟨4369814, by rfl⟩ : syracuseStep 5826419 = 8739629) B8739629
theorem B1615751 : Blo 1615006 1615751 := bstep (se 1 (by rfl) ⟨1211813, by rfl⟩ : syracuseStep 1615751 = 2423627) B2423627
theorem B1615759 : Blo 1615006 1615759 := bstep (se 1 (by rfl) ⟨1211819, by rfl⟩ : syracuseStep 1615759 = 2423639) B2423639
theorem B1615803 : Blo 1615006 1615803 := bstep (se 1 (by rfl) ⟨1211852, by rfl⟩ : syracuseStep 1615803 = 2423705) B2423705
theorem B8185859 : Blo 1615006 8185859 := bstep (se 1 (by rfl) ⟨6139394, by rfl⟩ : syracuseStep 8185859 = 12278789) B12278789
theorem B1615879 : Blo 1615006 1615879 := bstep (se 1 (by rfl) ⟨1211909, by rfl⟩ : syracuseStep 1615879 = 2423819) B2423819
theorem B1615887 : Blo 1615006 1615887 := bstep (se 1 (by rfl) ⟨1211915, by rfl⟩ : syracuseStep 1615887 = 2423831) B2423831
theorem B1615931 : Blo 1615006 1615931 := bstep (se 1 (by rfl) ⟨1211948, by rfl⟩ : syracuseStep 1615931 = 2423897) B2423897
theorem B8734787 : Blo 1615006 8734787 := bstep (se 1 (by rfl) ⟨6551090, by rfl⟩ : syracuseStep 8734787 = 13102181) B13102181
theorem B1616007 : Blo 1615006 1616007 := bstep (se 1 (by rfl) ⟨1212005, by rfl⟩ : syracuseStep 1616007 = 2424011) B2424011
theorem B1616015 : Blo 1615006 1616015 := bstep (se 1 (by rfl) ⟨1212011, by rfl⟩ : syracuseStep 1616015 = 2424023) B2424023
theorem B1616059 : Blo 1615006 1616059 := bstep (se 1 (by rfl) ⟨1212044, by rfl⟩ : syracuseStep 1616059 = 2424089) B2424089
theorem B34081013 : Blo 1615006 34081013 := bstep (se 5 (by rfl) ⟨1597547, by rfl⟩ : syracuseStep 34081013 = 3195095) B3195095
theorem B8177921 : Blo 1615006 8177921 := bstep (se 2 (by rfl) ⟨3066720, by rfl⟩ : syracuseStep 8177921 = 6133441) B6133441
theorem B1616135 : Blo 1615006 1616135 := bstep (se 1 (by rfl) ⟨1212101, by rfl⟩ : syracuseStep 1616135 = 2424203) B2424203
theorem B1616143 : Blo 1615006 1616143 := bstep (se 1 (by rfl) ⟨1212107, by rfl⟩ : syracuseStep 1616143 = 2424215) B2424215
theorem B1616187 : Blo 1615006 1616187 := bstep (se 1 (by rfl) ⟨1212140, by rfl⟩ : syracuseStep 1616187 = 2424281) B2424281
theorem B4368755 : Blo 1615006 4368755 := bstep (se 1 (by rfl) ⟨3276566, by rfl⟩ : syracuseStep 4368755 = 6553133) B6553133
theorem B4426103 : Blo 1615006 4426103 := bstep (se 1 (by rfl) ⟨3319577, by rfl⟩ : syracuseStep 4426103 = 6639155) B6639155
theorem B4090247 : Blo 1615006 4090247 := bstep (se 1 (by rfl) ⟨3067685, by rfl⟩ : syracuseStep 4090247 = 6135371) B6135371
theorem B1616263 : Blo 1615006 1616263 := bstep (se 1 (by rfl) ⟨1212197, by rfl⟩ : syracuseStep 1616263 = 2424395) B2424395
theorem B1616271 : Blo 1615006 1616271 := bstep (se 1 (by rfl) ⟨1212203, by rfl⟩ : syracuseStep 1616271 = 2424407) B2424407
theorem B4090297 : Blo 1615006 4090297 := bstep (se 2 (by rfl) ⟨1533861, by rfl⟩ : syracuseStep 4090297 = 3067723) B3067723
theorem B1616315 : Blo 1615006 1616315 := bstep (se 1 (by rfl) ⟨1212236, by rfl⟩ : syracuseStep 1616315 = 2424473) B2424473
theorem B1616391 : Blo 1615006 1616391 := bstep (se 1 (by rfl) ⟨1212293, by rfl⟩ : syracuseStep 1616391 = 2424587) B2424587
theorem B1616399 : Blo 1615006 1616399 := bstep (se 1 (by rfl) ⟨1212299, by rfl⟩ : syracuseStep 1616399 = 2424599) B2424599
theorem B7768619 : Blo 1615006 7768619 := bstep (se 1 (by rfl) ⟨5826464, by rfl⟩ : syracuseStep 7768619 = 11652929) B11652929
theorem B1616443 : Blo 1615006 1616443 := bstep (se 1 (by rfl) ⟨1212332, by rfl⟩ : syracuseStep 1616443 = 2424665) B2424665
theorem B1616519 : Blo 1615006 1616519 := bstep (se 1 (by rfl) ⟨1212389, by rfl⟩ : syracuseStep 1616519 = 2424779) B2424779
theorem B1616527 : Blo 1615006 1616527 := bstep (se 1 (by rfl) ⟨1212395, by rfl⟩ : syracuseStep 1616527 = 2424791) B2424791
theorem B9202349 : Blo 1615006 9202349 := bstep (se 3 (by rfl) ⟨1725440, by rfl⟩ : syracuseStep 9202349 = 3450881) B3450881
theorem B1616571 : Blo 1615006 1616571 := bstep (se 1 (by rfl) ⟨1212428, by rfl⟩ : syracuseStep 1616571 = 2424857) B2424857
theorem B3066569 : Blo 1615006 3066569 := bstep (se 2 (by rfl) ⟨1149963, by rfl⟩ : syracuseStep 3066569 = 2299927) B2299927
theorem B6138605 : Blo 1615006 6138605 := bstep (se 3 (by rfl) ⟨1150988, by rfl⟩ : syracuseStep 6138605 = 2301977) B2301977
theorem B1616647 : Blo 1615006 1616647 := bstep (se 1 (by rfl) ⟨1212485, by rfl⟩ : syracuseStep 1616647 = 2424971) B2424971
theorem B1616655 : Blo 1615006 1616655 := bstep (se 1 (by rfl) ⟨1212491, by rfl⟩ : syracuseStep 1616655 = 2424983) B2424983
theorem B10357541 : Blo 1615006 10357541 := bstep (se 4 (by rfl) ⟨971019, by rfl⟩ : syracuseStep 10357541 = 1942039) B1942039
theorem B10349363 : Blo 1615006 10349363 := bstep (se 1 (by rfl) ⟨7762022, by rfl⟩ : syracuseStep 10349363 = 15524045) B15524045
theorem B1616699 : Blo 1615006 1616699 := bstep (se 1 (by rfl) ⟨1212524, by rfl⟩ : syracuseStep 1616699 = 2425049) B2425049
theorem B1616775 : Blo 1615006 1616775 := bstep (se 1 (by rfl) ⟨1212581, by rfl⟩ : syracuseStep 1616775 = 2425163) B2425163
theorem B1616783 : Blo 1615006 1616783 := bstep (se 1 (by rfl) ⟨1212587, by rfl⟩ : syracuseStep 1616783 = 2425175) B2425175
theorem B1616827 : Blo 1615006 1616827 := bstep (se 1 (by rfl) ⟨1212620, by rfl⟩ : syracuseStep 1616827 = 2425241) B2425241
theorem B1616903 : Blo 1615006 1616903 := bstep (se 1 (by rfl) ⟨1212677, by rfl⟩ : syracuseStep 1616903 = 2425355) B2425355
theorem B4090895 : Blo 1615006 4090895 := bstep (se 1 (by rfl) ⟨3068171, by rfl⟩ : syracuseStep 4090895 = 6136343) B6136343
theorem B1616911 : Blo 1615006 1616911 := bstep (se 1 (by rfl) ⟨1212683, by rfl⟩ : syracuseStep 1616911 = 2425367) B2425367
theorem B8178731 : Blo 1615006 8178731 := bstep (se 1 (by rfl) ⟨6134048, by rfl⟩ : syracuseStep 8178731 = 12268097) B12268097
theorem B1616955 : Blo 1615006 1616955 := bstep (se 1 (by rfl) ⟨1212716, by rfl⟩ : syracuseStep 1616955 = 2425433) B2425433
theorem B5450813 : Blo 1615006 5450813 := bstep (se 3 (by rfl) ⟨1022027, by rfl⟩ : syracuseStep 5450813 = 2044055) B2044055
theorem B39292037 : Blo 1615006 39292037 := bstep (se 4 (by rfl) ⟨3683628, by rfl⟩ : syracuseStep 39292037 = 7367257) B7367257
theorem B46583099 : Blo 1615006 46583099 := bstep (se 1 (by rfl) ⟨34937324, by rfl⟩ : syracuseStep 46583099 = 69874649) B69874649
theorem B20704571 : Blo 1615006 20704571 := bstep (se 1 (by rfl) ⟨15528428, by rfl⟩ : syracuseStep 20704571 = 31056857) B31056857
theorem B3067283 : Blo 1615006 3067283 := bstep (se 1 (by rfl) ⟨2300462, by rfl⟩ : syracuseStep 3067283 = 4600925) B4600925
theorem B4599193 : Blo 1615006 4599193 := bstep (se 2 (by rfl) ⟨1724697, by rfl⟩ : syracuseStep 4599193 = 3449395) B3449395
theorem B3067321 : Blo 1615006 3067321 := bstep (se 2 (by rfl) ⟨1150245, by rfl⟩ : syracuseStep 3067321 = 2300491) B2300491
theorem B4599443 : Blo 1615006 4599443 := bstep (se 1 (by rfl) ⟨3449582, by rfl⟩ : syracuseStep 4599443 = 6899165) B6899165
theorem B4091593 : Blo 1615006 4091593 := bstep (se 2 (by rfl) ⟨1534347, by rfl⟩ : syracuseStep 4091593 = 3068695) B3068695
theorem B9203489 : Blo 1615006 9203489 := bstep (se 2 (by rfl) ⟨3451308, by rfl⟩ : syracuseStep 9203489 = 6902617) B6902617
theorem B4091735 : Blo 1615006 4091735 := bstep (se 1 (by rfl) ⟨3068801, by rfl⟩ : syracuseStep 4091735 = 6137603) B6137603
theorem B7770001 : Blo 1615006 7770001 := bstep (se 2 (by rfl) ⟨2913750, by rfl⟩ : syracuseStep 7770001 = 5827501) B5827501
theorem B4911371 : Blo 1615006 4911371 := bstep (se 1 (by rfl) ⟨3683528, by rfl⟩ : syracuseStep 4911371 = 7367057) B7367057
theorem B6131983 : Blo 1615006 6131983 := bstep (se 1 (by rfl) ⟨4598987, by rfl⟩ : syracuseStep 6131983 = 9197975) B9197975
theorem B3838223 : Blo 1615006 3838223 := bstep (se 1 (by rfl) ⟨2878667, by rfl⟩ : syracuseStep 3838223 = 5757335) B5757335
theorem B8180027 : Blo 1615006 8180027 := bstep (se 1 (by rfl) ⟨6135020, by rfl⟩ : syracuseStep 8180027 = 12270041) B12270041
theorem B39301469 : Blo 1615006 39301469 := bstep (se 3 (by rfl) ⟨7369025, by rfl⟩ : syracuseStep 39301469 = 14738051) B14738051
theorem B5452217 : Blo 1615006 5452217 := bstep (se 2 (by rfl) ⟨2044581, by rfl⟩ : syracuseStep 5452217 = 4089163) B4089163
theorem B8180189 : Blo 1615006 8180189 := bstep (se 3 (by rfl) ⟨1533785, by rfl⟩ : syracuseStep 8180189 = 3067571) B3067571
theorem B13808171 : Blo 1615006 13808171 := bstep (se 1 (by rfl) ⟨10356128, by rfl⟩ : syracuseStep 13808171 = 20712257) B20712257
theorem B4600435 : Blo 1615006 4600435 := bstep (se 1 (by rfl) ⟨3450326, by rfl⟩ : syracuseStep 4600435 = 6900653) B6900653
theorem B19665625 : Blo 1615006 19665625 := bstep (se 2 (by rfl) ⟨7374609, by rfl⟩ : syracuseStep 19665625 = 14749219) B14749219
theorem B14742287 : Blo 1615006 14742287 := bstep (se 1 (by rfl) ⟨11056715, by rfl⟩ : syracuseStep 14742287 = 22113431) B22113431
theorem B8180513 : Blo 1615006 8180513 := bstep (se 2 (by rfl) ⟨3067692, by rfl⟩ : syracuseStep 8180513 = 6135385) B6135385
theorem B3634055 : Blo 1615006 3634055 := bstep (se 1 (by rfl) ⟨2725541, by rfl⟩ : syracuseStep 3634055 = 5451083) B5451083
theorem B5452811 : Blo 1615006 5452811 := bstep (se 1 (by rfl) ⟨4089608, by rfl⟩ : syracuseStep 5452811 = 8179217) B8179217
theorem B6550571 : Blo 1615006 6550571 := bstep (se 1 (by rfl) ⟨4912928, by rfl⟩ : syracuseStep 6550571 = 9825857) B9825857
theorem B3634235 : Blo 1615006 3634235 := bstep (se 1 (by rfl) ⟨2725676, by rfl⟩ : syracuseStep 3634235 = 5451353) B5451353
theorem B5452919 : Blo 1615006 5452919 := bstep (se 1 (by rfl) ⟨4089689, by rfl⟩ : syracuseStep 5452919 = 8179379) B8179379
theorem B31503491 : Blo 1615006 31503491 := bstep (se 1 (by rfl) ⟨23627618, by rfl⟩ : syracuseStep 31503491 = 47255237) B47255237
theorem B3634361 : Blo 1615006 3634361 := bstep (se 2 (by rfl) ⟨1362885, by rfl⟩ : syracuseStep 3634361 = 2725771) B2725771
theorem B3069227 : Blo 1615006 3069227 := bstep (se 1 (by rfl) ⟨2301920, by rfl⟩ : syracuseStep 3069227 = 4603841) B4603841
theorem B2913671 : Blo 1615006 2913671 := bstep (se 1 (by rfl) ⟨2185253, by rfl⟩ : syracuseStep 2913671 = 4370507) B4370507
theorem B3683731 : Blo 1615006 3683731 := bstep (se 1 (by rfl) ⟨2762798, by rfl⟩ : syracuseStep 3683731 = 5525597) B5525597
theorem B34952633 : Blo 1615006 34952633 := bstep (se 2 (by rfl) ⟨13107237, by rfl⟩ : syracuseStep 34952633 = 26214475) B26214475
theorem B36410809 : Blo 1615006 36410809 := bstep (se 2 (by rfl) ⟨13654053, by rfl⟩ : syracuseStep 36410809 = 27308107) B27308107
theorem B6223313 : Blo 1615006 6223313 := bstep (se 2 (by rfl) ⟨2333742, by rfl⟩ : syracuseStep 6223313 = 4667485) B4667485
theorem B6133259 : Blo 1615006 6133259 := bstep (se 1 (by rfl) ⟨4599944, by rfl⟩ : syracuseStep 6133259 = 9199889) B9199889
theorem B3634703 : Blo 1615006 3634703 := bstep (se 1 (by rfl) ⟨2726027, by rfl⟩ : syracuseStep 3634703 = 5452055) B5452055
theorem B143652365 : Blo 1615006 143652365 := bstep (se 3 (by rfl) ⟨26934818, by rfl⟩ : syracuseStep 143652365 = 53869637) B53869637
theorem B7763485 : Blo 1615006 7763485 := bstep (se 3 (by rfl) ⟨1455653, by rfl⟩ : syracuseStep 7763485 = 2911307) B2911307
theorem B3274273 : Blo 1615006 3274273 := bstep (se 2 (by rfl) ⟨1227852, by rfl⟩ : syracuseStep 3274273 = 2455705) B2455705
theorem B3634721 : Blo 1615006 3634721 := bstep (se 2 (by rfl) ⟨1363020, by rfl⟩ : syracuseStep 3634721 = 2726041) B2726041
theorem B5453513 : Blo 1615006 5453513 := bstep (se 2 (by rfl) ⟨2045067, by rfl⟩ : syracuseStep 5453513 = 4090135) B4090135
theorem B8181485 : Blo 1615006 8181485 := bstep (se 3 (by rfl) ⟨1534028, by rfl⟩ : syracuseStep 8181485 = 3068057) B3068057
theorem B2422535 : Blo 1615006 2422535 := bstep (se 1 (by rfl) ⟨1816901, by rfl⟩ : syracuseStep 2422535 = 3633803) B3633803
theorem B2184967 : Blo 1615006 2184967 := bstep (se 1 (by rfl) ⟨1638725, by rfl⟩ : syracuseStep 2184967 = 3277451) B3277451
theorem B16578341 : Blo 1615006 16578341 := bstep (se 4 (by rfl) ⟨1554219, by rfl⟩ : syracuseStep 16578341 = 3108439) B3108439
theorem B2422571 : Blo 1615006 2422571 := bstep (se 1 (by rfl) ⟨1816928, by rfl⟩ : syracuseStep 2422571 = 3633857) B3633857
theorem B2422601 : Blo 1615006 2422601 := bstep (se 2 (by rfl) ⟨908475, by rfl⟩ : syracuseStep 2422601 = 1816951) B1816951
theorem B18397043 : Blo 1615006 18397043 := bstep (se 1 (by rfl) ⟨13797782, by rfl⟩ : syracuseStep 18397043 = 27595565) B27595565
theorem B2725751 : Blo 1615006 2725751 := bstep (se 1 (by rfl) ⟨2044313, by rfl⟩ : syracuseStep 2725751 = 4088627) B4088627
theorem B3635063 : Blo 1615006 3635063 := bstep (se 1 (by rfl) ⟨2726297, by rfl⟩ : syracuseStep 3635063 = 5452595) B5452595
theorem B2422715 : Blo 1615006 2422715 := bstep (se 1 (by rfl) ⟨1817036, by rfl⟩ : syracuseStep 2422715 = 3634073) B3634073
theorem B2422775 : Blo 1615006 2422775 := bstep (se 1 (by rfl) ⟨1817081, by rfl⟩ : syracuseStep 2422775 = 3634163) B3634163
theorem B2422799 : Blo 1615006 2422799 := bstep (se 1 (by rfl) ⟨1817099, by rfl⟩ : syracuseStep 2422799 = 3634199) B3634199
theorem B3635243 : Blo 1615006 3635243 := bstep (se 1 (by rfl) ⟨2726432, by rfl⟩ : syracuseStep 3635243 = 5452865) B5452865
theorem B2422841 : Blo 1615006 2422841 := bstep (se 2 (by rfl) ⟨908565, by rfl⟩ : syracuseStep 2422841 = 1817131) B1817131
theorem B2299961 : Blo 1615006 2299961 := bstep (se 2 (by rfl) ⟨862485, by rfl⟩ : syracuseStep 2299961 = 1724971) B1724971
theorem B2422919 : Blo 1615006 2422919 := bstep (se 1 (by rfl) ⟨1817189, by rfl⟩ : syracuseStep 2422919 = 3634379) B3634379
theorem B2422955 : Blo 1615006 2422955 := bstep (se 1 (by rfl) ⟨1817216, by rfl⟩ : syracuseStep 2422955 = 3634433) B3634433
theorem B4602041 : Blo 1615006 4602041 := bstep (se 2 (by rfl) ⟨1725765, by rfl⟩ : syracuseStep 4602041 = 3451531) B3451531
theorem B2422985 : Blo 1615006 2422985 := bstep (se 2 (by rfl) ⟨908619, by rfl⟩ : syracuseStep 2422985 = 1817239) B1817239
theorem B3987713 : Blo 1615006 3987713 := bstep (se 2 (by rfl) ⟨1495392, by rfl⟩ : syracuseStep 3987713 = 2990785) B2990785
theorem B2423099 : Blo 1615006 2423099 := bstep (se 1 (by rfl) ⟨1817324, by rfl⟩ : syracuseStep 2423099 = 3634649) B3634649
theorem B2726203 : Blo 1615006 2726203 := bstep (se 1 (by rfl) ⟨2044652, by rfl⟩ : syracuseStep 2726203 = 4089305) B4089305
theorem B2423159 : Blo 1615006 2423159 := bstep (se 1 (by rfl) ⟨1817369, by rfl⟩ : syracuseStep 2423159 = 3634739) B3634739
theorem B5454215 : Blo 1615006 5454215 := bstep (se 1 (by rfl) ⟨4090661, by rfl⟩ : syracuseStep 5454215 = 8181323) B8181323
theorem B2423183 : Blo 1615006 2423183 := bstep (se 1 (by rfl) ⟨1817387, by rfl⟩ : syracuseStep 2423183 = 3634775) B3634775
theorem B3635603 : Blo 1615006 3635603 := bstep (se 1 (by rfl) ⟨2726702, by rfl⟩ : syracuseStep 3635603 = 5453405) B5453405
theorem B2046379 : Blo 1615006 2046379 := bstep (se 1 (by rfl) ⟨1534784, by rfl⟩ : syracuseStep 2046379 = 3069569) B3069569
theorem B2423225 : Blo 1615006 2423225 := bstep (se 2 (by rfl) ⟨908709, by rfl⟩ : syracuseStep 2423225 = 1817419) B1817419
theorem B6134201 : Blo 1615006 6134201 := bstep (se 2 (by rfl) ⟨2300325, by rfl⟩ : syracuseStep 6134201 = 4600651) B4600651
theorem B2726345 : Blo 1615006 2726345 := bstep (se 2 (by rfl) ⟨1022379, by rfl⟩ : syracuseStep 2726345 = 2044759) B2044759
theorem B3635657 : Blo 1615006 3635657 := bstep (se 2 (by rfl) ⟨1363371, by rfl⟩ : syracuseStep 3635657 = 2726743) B2726743
theorem B1817095 : Blo 1615006 1817095 := bstep (se 1 (by rfl) ⟨1362821, by rfl⟩ : syracuseStep 1817095 = 2725643) B2725643
theorem B2423303 : Blo 1615006 2423303 := bstep (se 1 (by rfl) ⟨1817477, by rfl⟩ : syracuseStep 2423303 = 3634955) B3634955
theorem B4602383 : Blo 1615006 4602383 := bstep (se 1 (by rfl) ⟨3451787, by rfl⟩ : syracuseStep 4602383 = 6903575) B6903575
theorem B8182295 : Blo 1615006 8182295 := bstep (se 1 (by rfl) ⟨6136721, by rfl⟩ : syracuseStep 8182295 = 12273443) B12273443
theorem B2423339 : Blo 1615006 2423339 := bstep (se 1 (by rfl) ⟨1817504, by rfl⟩ : syracuseStep 2423339 = 3635009) B3635009
theorem B2423369 : Blo 1615006 2423369 := bstep (se 2 (by rfl) ⟨908763, by rfl⟩ : syracuseStep 2423369 = 1817527) B1817527
theorem B1817275 : Blo 1615006 1817275 := bstep (se 1 (by rfl) ⟨1362956, by rfl⟩ : syracuseStep 1817275 = 2725913) B2725913
theorem B2423483 : Blo 1615006 2423483 := bstep (se 1 (by rfl) ⟨1817612, by rfl⟩ : syracuseStep 2423483 = 3635225) B3635225
theorem B9329381 : Blo 1615006 9329381 := bstep (se 4 (by rfl) ⟨874629, by rfl⟩ : syracuseStep 9329381 = 1749259) B1749259
theorem B2423543 : Blo 1615006 2423543 := bstep (se 1 (by rfl) ⟨1817657, by rfl⟩ : syracuseStep 2423543 = 3635315) B3635315
theorem B5454593 : Blo 1615006 5454593 := bstep (se 2 (by rfl) ⟨2045472, by rfl⟩ : syracuseStep 5454593 = 4090945) B4090945
theorem B2423567 : Blo 1615006 2423567 := bstep (se 1 (by rfl) ⟨1817675, by rfl⟩ : syracuseStep 2423567 = 3635351) B3635351
theorem B5823247 : Blo 1615006 5823247 := bstep (se 1 (by rfl) ⟨4367435, by rfl⟩ : syracuseStep 5823247 = 8734871) B8734871
theorem B2423609 : Blo 1615006 2423609 := bstep (se 2 (by rfl) ⟨908853, by rfl⟩ : syracuseStep 2423609 = 1817707) B1817707
theorem B2423687 : Blo 1615006 2423687 := bstep (se 1 (by rfl) ⟨1817765, by rfl⟩ : syracuseStep 2423687 = 3635531) B3635531
theorem B2300815 : Blo 1615006 2300815 := bstep (se 1 (by rfl) ⟨1725611, by rfl⟩ : syracuseStep 2300815 = 3451223) B3451223
theorem B2423723 : Blo 1615006 2423723 := bstep (se 1 (by rfl) ⟨1817792, by rfl⟩ : syracuseStep 2423723 = 3635585) B3635585
theorem B2423753 : Blo 1615006 2423753 := bstep (se 2 (by rfl) ⟨908907, by rfl⟩ : syracuseStep 2423753 = 1817815) B1817815
theorem B18414539 : Blo 1615006 18414539 := bstep (se 1 (by rfl) ⟨13810904, by rfl⟩ : syracuseStep 18414539 = 27621809) B27621809
theorem B31054853 : Blo 1615006 31054853 := bstep (se 4 (by rfl) ⟨2911392, by rfl⟩ : syracuseStep 31054853 = 5822785) B5822785
theorem B26213381 : Blo 1615006 26213381 := bstep (se 4 (by rfl) ⟨2457504, by rfl⟩ : syracuseStep 26213381 = 4915009) B4915009
theorem B5176349 : Blo 1615006 5176349 := bstep (se 3 (by rfl) ⟨970565, by rfl⟩ : syracuseStep 5176349 = 1941131) B1941131
theorem B2423867 : Blo 1615006 2423867 := bstep (se 1 (by rfl) ⟨1817900, by rfl⟩ : syracuseStep 2423867 = 3635801) B3635801
theorem B2423927 : Blo 1615006 2423927 := bstep (se 1 (by rfl) ⟨1817945, by rfl⟩ : syracuseStep 2423927 = 3635891) B3635891
theorem B2727047 : Blo 1615006 2727047 := bstep (se 1 (by rfl) ⟨2045285, by rfl⟩ : syracuseStep 2727047 = 4090571) B4090571
theorem B3636359 : Blo 1615006 3636359 := bstep (se 1 (by rfl) ⟨2727269, by rfl⟩ : syracuseStep 3636359 = 5454539) B5454539
theorem B1817743 : Blo 1615006 1817743 := bstep (se 1 (by rfl) ⟨1363307, by rfl⟩ : syracuseStep 1817743 = 2726615) B2726615
theorem B2423951 : Blo 1615006 2423951 := bstep (se 1 (by rfl) ⟨1817963, by rfl⟩ : syracuseStep 2423951 = 3635927) B3635927
theorem B2423993 : Blo 1615006 2423993 := bstep (se 2 (by rfl) ⟨908997, by rfl⟩ : syracuseStep 2423993 = 1817995) B1817995
theorem B2424071 : Blo 1615006 2424071 := bstep (se 1 (by rfl) ⟨1818053, by rfl⟩ : syracuseStep 2424071 = 3636107) B3636107
theorem B4603169 : Blo 1615006 4603169 := bstep (se 2 (by rfl) ⟨1726188, by rfl⟩ : syracuseStep 4603169 = 3452377) B3452377
theorem B2424107 : Blo 1615006 2424107 := bstep (se 1 (by rfl) ⟨1818080, by rfl⟩ : syracuseStep 2424107 = 3636161) B3636161
theorem B18652475 : Blo 1615006 18652475 := bstep (se 1 (by rfl) ⟨13989356, by rfl⟩ : syracuseStep 18652475 = 27978713) B27978713
theorem B3636539 : Blo 1615006 3636539 := bstep (se 1 (by rfl) ⟨2727404, by rfl⟩ : syracuseStep 3636539 = 5454809) B5454809
theorem B2424137 : Blo 1615006 2424137 := bstep (se 2 (by rfl) ⟨909051, by rfl⟩ : syracuseStep 2424137 = 1818103) B1818103
theorem B3636665 : Blo 1615006 3636665 := bstep (se 2 (by rfl) ⟨1363749, by rfl⟩ : syracuseStep 3636665 = 2727499) B2727499
theorem B2424251 : Blo 1615006 2424251 := bstep (se 1 (by rfl) ⟨1818188, by rfl⟩ : syracuseStep 2424251 = 3636377) B3636377
theorem B2301385 : Blo 1615006 2301385 := bstep (se 2 (by rfl) ⟨863019, by rfl⟩ : syracuseStep 2301385 = 1726039) B1726039
theorem B2424311 : Blo 1615006 2424311 := bstep (se 1 (by rfl) ⟨1818233, by rfl⟩ : syracuseStep 2424311 = 3636467) B3636467
theorem B9199115 : Blo 1615006 9199115 := bstep (se 1 (by rfl) ⟨6899336, by rfl⟩ : syracuseStep 9199115 = 13798673) B13798673
theorem B2424335 : Blo 1615006 2424335 := bstep (se 1 (by rfl) ⟨1818251, by rfl⟩ : syracuseStep 2424335 = 3636503) B3636503
theorem B5455403 : Blo 1615006 5455403 := bstep (se 1 (by rfl) ⟨4091552, by rfl⟩ : syracuseStep 5455403 = 8183105) B8183105
theorem B2424377 : Blo 1615006 2424377 := bstep (se 2 (by rfl) ⟨909141, by rfl⟩ : syracuseStep 2424377 = 1818283) B1818283
theorem B7872119 : Blo 1615006 7872119 := bstep (se 1 (by rfl) ⟨5904089, by rfl⟩ : syracuseStep 7872119 = 11808179) B11808179
theorem B1818247 : Blo 1615006 1818247 := bstep (se 1 (by rfl) ⟨1363685, by rfl⟩ : syracuseStep 1818247 = 2727371) B2727371
theorem B2424455 : Blo 1615006 2424455 := bstep (se 1 (by rfl) ⟨1818341, by rfl⟩ : syracuseStep 2424455 = 3636683) B3636683
theorem B2424491 : Blo 1615006 2424491 := bstep (se 1 (by rfl) ⟨1818368, by rfl⟩ : syracuseStep 2424491 = 3636737) B3636737
theorem B2424521 : Blo 1615006 2424521 := bstep (se 2 (by rfl) ⟨909195, by rfl⟩ : syracuseStep 2424521 = 1818391) B1818391
theorem B4144907 : Blo 1615006 4144907 := bstep (se 1 (by rfl) ⟨3108680, by rfl⟩ : syracuseStep 4144907 = 6217361) B6217361
theorem B2588431 : Blo 1615006 2588431 := bstep (se 1 (by rfl) ⟨1941323, by rfl⟩ : syracuseStep 2588431 = 3882647) B3882647
theorem B2727695 : Blo 1615006 2727695 := bstep (se 1 (by rfl) ⟨2045771, by rfl⟩ : syracuseStep 2727695 = 4091543) B4091543
theorem B3637007 : Blo 1615006 3637007 := bstep (se 1 (by rfl) ⟨2727755, by rfl⟩ : syracuseStep 3637007 = 5455511) B5455511
theorem B3637025 : Blo 1615006 3637025 := bstep (se 2 (by rfl) ⟨1363884, by rfl⟩ : syracuseStep 3637025 = 2727769) B2727769
theorem B15957809 : Blo 1615006 15957809 := bstep (se 2 (by rfl) ⟨5984178, by rfl⟩ : syracuseStep 15957809 = 11968357) B11968357
theorem B5824315 : Blo 1615006 5824315 := bstep (se 1 (by rfl) ⟨4368236, by rfl⟩ : syracuseStep 5824315 = 8736473) B8736473
theorem B1818427 : Blo 1615006 1818427 := bstep (se 1 (by rfl) ⟨1363820, by rfl⟩ : syracuseStep 1818427 = 2727641) B2727641
theorem B2424635 : Blo 1615006 2424635 := bstep (se 1 (by rfl) ⟨1818476, by rfl⟩ : syracuseStep 2424635 = 3636953) B3636953
theorem B2424695 : Blo 1615006 2424695 := bstep (se 1 (by rfl) ⟨1818521, by rfl⟩ : syracuseStep 2424695 = 3637043) B3637043
theorem B2424719 : Blo 1615006 2424719 := bstep (se 1 (by rfl) ⟨1818539, by rfl⟩ : syracuseStep 2424719 = 3637079) B3637079
theorem B2424761 : Blo 1615006 2424761 := bstep (se 2 (by rfl) ⟨909285, by rfl⟩ : syracuseStep 2424761 = 1818571) B1818571
theorem B3883087 : Blo 1615006 3883087 := bstep (se 1 (by rfl) ⟨2912315, by rfl⟩ : syracuseStep 3883087 = 5824631) B5824631
theorem B2424911 : Blo 1615006 2424911 := bstep (se 1 (by rfl) ⟨1818683, by rfl⟩ : syracuseStep 2424911 = 3637367) B3637367
theorem B15532195 : Blo 1615006 15532195 := bstep (se 1 (by rfl) ⟨11649146, by rfl⟩ : syracuseStep 15532195 = 23298293) B23298293
theorem B2425031 : Blo 1615006 2425031 := bstep (se 1 (by rfl) ⟨1818773, by rfl⟩ : syracuseStep 2425031 = 3637547) B3637547
theorem B1818823 : Blo 1615006 1818823 := bstep (se 1 (by rfl) ⟨1364117, by rfl⟩ : syracuseStep 1818823 = 2728235) B2728235
theorem B8175977 : Blo 1615006 8175977 := bstep (se 2 (by rfl) ⟨3065991, by rfl⟩ : syracuseStep 8175977 = 6131983) B6131983
theorem B2425193 : Blo 1615006 2425193 := bstep (se 2 (by rfl) ⟨909447, by rfl⟩ : syracuseStep 2425193 = 1818895) B1818895
theorem B3277199 : Blo 1615006 3277199 := bstep (se 1 (by rfl) ⟨2457899, by rfl⟩ : syracuseStep 3277199 = 4915799) B4915799
theorem B2425271 : Blo 1615006 2425271 := bstep (se 1 (by rfl) ⟨1818953, by rfl⟩ : syracuseStep 2425271 = 3637907) B3637907
theorem B2425307 : Blo 1615006 2425307 := bstep (se 1 (by rfl) ⟨1818980, by rfl⟩ : syracuseStep 2425307 = 3637961) B3637961
theorem B3637799 : Blo 1615006 3637799 := bstep (se 1 (by rfl) ⟨2728349, by rfl⟩ : syracuseStep 3637799 = 5456699) B5456699
theorem B4604455 : Blo 1615006 4604455 := bstep (se 1 (by rfl) ⟨3453341, by rfl⟩ : syracuseStep 4604455 = 6906683) B6906683
theorem B2728505 : Blo 1615006 2728505 := bstep (se 2 (by rfl) ⟨1023189, by rfl⟩ : syracuseStep 2728505 = 2046379) B2046379
theorem B4367047 : Blo 1615006 4367047 := bstep (se 1 (by rfl) ⟨3275285, by rfl⟩ : syracuseStep 4367047 = 6550571) B6550571
theorem B4604627 : Blo 1615006 4604627 := bstep (se 1 (by rfl) ⟨3453470, by rfl⟩ : syracuseStep 4604627 = 6906941) B6906941
theorem B3638123 : Blo 1615006 3638123 := bstep (se 1 (by rfl) ⟨2728592, by rfl⟩ : syracuseStep 3638123 = 5457185) B5457185
theorem B3638177 : Blo 1615006 3638177 := bstep (se 2 (by rfl) ⟨1364316, by rfl⟩ : syracuseStep 3638177 = 2728633) B2728633
theorem B11650013 : Blo 1615006 11650013 := bstep (se 3 (by rfl) ⟨2184377, by rfl⟩ : syracuseStep 11650013 = 4368755) B4368755
theorem B4088839 : Blo 1615006 4088839 := bstep (se 1 (by rfl) ⟨3066629, by rfl⟩ : syracuseStep 4088839 = 6133259) B6133259
theorem B7373843 : Blo 1615006 7373843 := bstep (se 1 (by rfl) ⟨5530382, by rfl⟩ : syracuseStep 7373843 = 11060765) B11060765
theorem B5456915 : Blo 1615006 5456915 := bstep (se 1 (by rfl) ⟨4092686, by rfl⟩ : syracuseStep 5456915 = 8185373) B8185373
theorem B3884203 : Blo 1615006 3884203 := bstep (se 1 (by rfl) ⟨2913152, by rfl⟩ : syracuseStep 3884203 = 5826305) B5826305
theorem B1615023 : Blo 1615006 1615023 := bstep (se 1 (by rfl) ⟨1211267, by rfl⟩ : syracuseStep 1615023 = 2422535) B2422535
theorem B11052227 : Blo 1615006 11052227 := bstep (se 1 (by rfl) ⟨8289170, by rfl⟩ : syracuseStep 11052227 = 16578341) B16578341
theorem B1615047 : Blo 1615006 1615047 := bstep (se 1 (by rfl) ⟨1211285, by rfl⟩ : syracuseStep 1615047 = 2422571) B2422571
theorem B1615067 : Blo 1615006 1615067 := bstep (se 1 (by rfl) ⟨1211300, by rfl⟩ : syracuseStep 1615067 = 2422601) B2422601
theorem B12264695 : Blo 1615006 12264695 := bstep (se 1 (by rfl) ⟨9198521, by rfl⟩ : syracuseStep 12264695 = 18397043) B18397043
theorem B3884279 : Blo 1615006 3884279 := bstep (se 1 (by rfl) ⟨2913209, by rfl⟩ : syracuseStep 3884279 = 5826419) B5826419
theorem B1615143 : Blo 1615006 1615143 := bstep (se 1 (by rfl) ⟨1211357, by rfl⟩ : syracuseStep 1615143 = 2422715) B2422715
theorem B1615183 : Blo 1615006 1615183 := bstep (se 1 (by rfl) ⟨1211387, by rfl⟩ : syracuseStep 1615183 = 2422775) B2422775
theorem B5457239 : Blo 1615006 5457239 := bstep (se 1 (by rfl) ⟨4092929, by rfl⟩ : syracuseStep 5457239 = 8185859) B8185859
theorem B1615199 : Blo 1615006 1615199 := bstep (se 1 (by rfl) ⟨1211399, by rfl⟩ : syracuseStep 1615199 = 2422799) B2422799
theorem B1615227 : Blo 1615006 1615227 := bstep (se 1 (by rfl) ⟨1211420, by rfl⟩ : syracuseStep 1615227 = 2422841) B2422841
theorem B1615279 : Blo 1615006 1615279 := bstep (se 1 (by rfl) ⟨1211459, by rfl⟩ : syracuseStep 1615279 = 2422919) B2422919
theorem B1615303 : Blo 1615006 1615303 := bstep (se 1 (by rfl) ⟨1211477, by rfl⟩ : syracuseStep 1615303 = 2422955) B2422955
theorem B1615323 : Blo 1615006 1615323 := bstep (se 1 (by rfl) ⟨1211492, by rfl⟩ : syracuseStep 1615323 = 2422985) B2422985
theorem B1615399 : Blo 1615006 1615399 := bstep (se 1 (by rfl) ⟨1211549, by rfl⟩ : syracuseStep 1615399 = 2423099) B2423099
theorem B1615439 : Blo 1615006 1615439 := bstep (se 1 (by rfl) ⟨1211579, by rfl⟩ : syracuseStep 1615439 = 2423159) B2423159
theorem B1615455 : Blo 1615006 1615455 := bstep (se 1 (by rfl) ⟨1211591, by rfl⟩ : syracuseStep 1615455 = 2423183) B2423183
theorem B1615483 : Blo 1615006 1615483 := bstep (se 1 (by rfl) ⟨1211612, by rfl⟩ : syracuseStep 1615483 = 2423225) B2423225
theorem B4089467 : Blo 1615006 4089467 := bstep (se 1 (by rfl) ⟨3067100, by rfl⟩ : syracuseStep 4089467 = 6134201) B6134201
theorem B1615535 : Blo 1615006 1615535 := bstep (se 1 (by rfl) ⟨1211651, by rfl⟩ : syracuseStep 1615535 = 2423303) B2423303
theorem B1615559 : Blo 1615006 1615559 := bstep (se 1 (by rfl) ⟨1211669, by rfl⟩ : syracuseStep 1615559 = 2423339) B2423339
theorem B5179079 : Blo 1615006 5179079 := bstep (se 1 (by rfl) ⟨3884309, by rfl⟩ : syracuseStep 5179079 = 7768619) B7768619
theorem B1615579 : Blo 1615006 1615579 := bstep (se 1 (by rfl) ⟨1211684, by rfl⟩ : syracuseStep 1615579 = 2423369) B2423369
theorem B12265181 : Blo 1615006 12265181 := bstep (se 3 (by rfl) ⟨2299721, by rfl⟩ : syracuseStep 12265181 = 4599443) B4599443
theorem B1615655 : Blo 1615006 1615655 := bstep (se 1 (by rfl) ⟨1211741, by rfl⟩ : syracuseStep 1615655 = 2423483) B2423483
theorem B6219587 : Blo 1615006 6219587 := bstep (se 1 (by rfl) ⟨4664690, by rfl⟩ : syracuseStep 6219587 = 9329381) B9329381
theorem B1615695 : Blo 1615006 1615695 := bstep (se 1 (by rfl) ⟨1211771, by rfl⟩ : syracuseStep 1615695 = 2423543) B2423543
theorem B1615711 : Blo 1615006 1615711 := bstep (se 1 (by rfl) ⟨1211783, by rfl⟩ : syracuseStep 1615711 = 2423567) B2423567
theorem B6899575 : Blo 1615006 6899575 := bstep (se 1 (by rfl) ⟨5174681, by rfl⟩ : syracuseStep 6899575 = 10349363) B10349363
theorem B1615739 : Blo 1615006 1615739 := bstep (se 1 (by rfl) ⟨1211804, by rfl⟩ : syracuseStep 1615739 = 2423609) B2423609
theorem B4089761 : Blo 1615006 4089761 := bstep (se 2 (by rfl) ⟨1533660, by rfl⟩ : syracuseStep 4089761 = 3067321) B3067321
theorem B48547745 : Blo 1615006 48547745 := bstep (se 2 (by rfl) ⟨18205404, by rfl⟩ : syracuseStep 48547745 = 36410809) B36410809
theorem B1615791 : Blo 1615006 1615791 := bstep (se 1 (by rfl) ⟨1211843, by rfl⟩ : syracuseStep 1615791 = 2423687) B2423687
theorem B1615815 : Blo 1615006 1615815 := bstep (se 1 (by rfl) ⟨1211861, by rfl⟩ : syracuseStep 1615815 = 2423723) B2423723
theorem B1615835 : Blo 1615006 1615835 := bstep (se 1 (by rfl) ⟨1211876, by rfl⟩ : syracuseStep 1615835 = 2423753) B2423753
theorem B20703235 : Blo 1615006 20703235 := bstep (se 1 (by rfl) ⟨15527426, by rfl⟩ : syracuseStep 20703235 = 31054853) B31054853
theorem B17475587 : Blo 1615006 17475587 := bstep (se 1 (by rfl) ⟨13106690, by rfl⟩ : syracuseStep 17475587 = 26213381) B26213381
theorem B3450899 : Blo 1615006 3450899 := bstep (se 1 (by rfl) ⟨2588174, by rfl⟩ : syracuseStep 3450899 = 5176349) B5176349
theorem B1615911 : Blo 1615006 1615911 := bstep (se 1 (by rfl) ⟨1211933, by rfl⟩ : syracuseStep 1615911 = 2423867) B2423867
theorem B1615951 : Blo 1615006 1615951 := bstep (se 1 (by rfl) ⟨1211963, by rfl⟩ : syracuseStep 1615951 = 2423927) B2423927
theorem B1615967 : Blo 1615006 1615967 := bstep (se 1 (by rfl) ⟨1211975, by rfl⟩ : syracuseStep 1615967 = 2423951) B2423951
theorem B1615995 : Blo 1615006 1615995 := bstep (se 1 (by rfl) ⟨1211996, by rfl⟩ : syracuseStep 1615995 = 2423993) B2423993
theorem B1616047 : Blo 1615006 1616047 := bstep (se 1 (by rfl) ⟨1212035, by rfl⟩ : syracuseStep 1616047 = 2424071) B2424071
theorem B1616071 : Blo 1615006 1616071 := bstep (se 1 (by rfl) ⟨1212053, by rfl⟩ : syracuseStep 1616071 = 2424107) B2424107
theorem B1616091 : Blo 1615006 1616091 := bstep (se 1 (by rfl) ⟨1212068, by rfl⟩ : syracuseStep 1616091 = 2424137) B2424137
theorem B1616167 : Blo 1615006 1616167 := bstep (se 1 (by rfl) ⟨1212125, by rfl⟩ : syracuseStep 1616167 = 2424251) B2424251
theorem B104859953 : Blo 1615006 104859953 := bstep (se 2 (by rfl) ⟨39322482, by rfl⟩ : syracuseStep 104859953 = 78644965) B78644965
theorem B1616207 : Blo 1615006 1616207 := bstep (se 1 (by rfl) ⟨1212155, by rfl⟩ : syracuseStep 1616207 = 2424311) B2424311
theorem B1616223 : Blo 1615006 1616223 := bstep (se 1 (by rfl) ⟨1212167, by rfl⟩ : syracuseStep 1616223 = 2424335) B2424335
theorem B3451241 : Blo 1615006 3451241 := bstep (se 2 (by rfl) ⟨1294215, by rfl⟩ : syracuseStep 3451241 = 2588431) B2588431
theorem B1616251 : Blo 1615006 1616251 := bstep (se 1 (by rfl) ⟨1212188, by rfl⟩ : syracuseStep 1616251 = 2424377) B2424377
theorem B1616303 : Blo 1615006 1616303 := bstep (se 1 (by rfl) ⟨1212227, by rfl⟩ : syracuseStep 1616303 = 2424455) B2424455
theorem B1616327 : Blo 1615006 1616327 := bstep (se 1 (by rfl) ⟨1212245, by rfl⟩ : syracuseStep 1616327 = 2424491) B2424491
theorem B1616347 : Blo 1615006 1616347 := bstep (se 1 (by rfl) ⟨1212260, by rfl⟩ : syracuseStep 1616347 = 2424521) B2424521
theorem B2763271 : Blo 1615006 2763271 := bstep (se 1 (by rfl) ⟨2072453, by rfl⟩ : syracuseStep 2763271 = 4144907) B4144907
theorem B1616423 : Blo 1615006 1616423 := bstep (se 1 (by rfl) ⟨1212317, by rfl⟩ : syracuseStep 1616423 = 2424635) B2424635
theorem B1616463 : Blo 1615006 1616463 := bstep (se 1 (by rfl) ⟨1212347, by rfl⟩ : syracuseStep 1616463 = 2424695) B2424695
theorem B1616479 : Blo 1615006 1616479 := bstep (se 1 (by rfl) ⟨1212359, by rfl⟩ : syracuseStep 1616479 = 2424719) B2424719
theorem B1616507 : Blo 1615006 1616507 := bstep (se 1 (by rfl) ⟨1212380, by rfl⟩ : syracuseStep 1616507 = 2424761) B2424761
theorem B1616559 : Blo 1615006 1616559 := bstep (se 1 (by rfl) ⟨1212419, by rfl⟩ : syracuseStep 1616559 = 2424839) B2424839
theorem B1616583 : Blo 1615006 1616583 := bstep (se 1 (by rfl) ⟨1212437, by rfl⟩ : syracuseStep 1616583 = 2424875) B2424875
theorem B31501001 : Blo 1615006 31501001 := bstep (se 2 (by rfl) ⟨11812875, by rfl⟩ : syracuseStep 31501001 = 23625751) B23625751
theorem B1616603 : Blo 1615006 1616603 := bstep (se 1 (by rfl) ⟨1212452, by rfl⟩ : syracuseStep 1616603 = 2424905) B2424905
theorem B1616679 : Blo 1615006 1616679 := bstep (se 1 (by rfl) ⟨1212509, by rfl⟩ : syracuseStep 1616679 = 2425019) B2425019
theorem B11643725 : Blo 1615006 11643725 := bstep (se 3 (by rfl) ⟨2183198, by rfl⟩ : syracuseStep 11643725 = 4366397) B4366397
theorem B1616719 : Blo 1615006 1616719 := bstep (se 1 (by rfl) ⟨1212539, by rfl⟩ : syracuseStep 1616719 = 2425079) B2425079
theorem B1616735 : Blo 1615006 1616735 := bstep (se 1 (by rfl) ⟨1212551, by rfl⟩ : syracuseStep 1616735 = 2425103) B2425103
theorem B1616763 : Blo 1615006 1616763 := bstep (se 1 (by rfl) ⟨1212572, by rfl⟩ : syracuseStep 1616763 = 2425145) B2425145
theorem B26200979 : Blo 1615006 26200979 := bstep (se 1 (by rfl) ⟨19650734, by rfl⟩ : syracuseStep 26200979 = 39301469) B39301469
theorem B1616815 : Blo 1615006 1616815 := bstep (se 1 (by rfl) ⟨1212611, by rfl⟩ : syracuseStep 1616815 = 2425223) B2425223
theorem B1616839 : Blo 1615006 1616839 := bstep (se 1 (by rfl) ⟨1212629, by rfl⟩ : syracuseStep 1616839 = 2425259) B2425259
theorem B1616859 : Blo 1615006 1616859 := bstep (se 1 (by rfl) ⟨1212644, by rfl⟩ : syracuseStep 1616859 = 2425289) B2425289
theorem B5450759 : Blo 1615006 5450759 := bstep (se 1 (by rfl) ⟨4088069, by rfl⟩ : syracuseStep 5450759 = 8176139) B8176139
theorem B1616935 : Blo 1615006 1616935 := bstep (se 1 (by rfl) ⟨1212701, by rfl⟩ : syracuseStep 1616935 = 2425403) B2425403
theorem B1616975 : Blo 1615006 1616975 := bstep (se 1 (by rfl) ⟨1212731, by rfl⟩ : syracuseStep 1616975 = 2425463) B2425463
theorem B1616991 : Blo 1615006 1616991 := bstep (se 1 (by rfl) ⟨1212743, by rfl⟩ : syracuseStep 1616991 = 2425487) B2425487
theorem B5450867 : Blo 1615006 5450867 := bstep (se 1 (by rfl) ⟨4088150, by rfl⟩ : syracuseStep 5450867 = 8176301) B8176301
theorem B10235261 : Blo 1615006 10235261 := bstep (se 3 (by rfl) ⟨1919111, by rfl⟩ : syracuseStep 10235261 = 3838223) B3838223
theorem B5451137 : Blo 1615006 5451137 := bstep (se 2 (by rfl) ⟨2044176, by rfl⟩ : syracuseStep 5451137 = 4088353) B4088353
theorem B4369793 : Blo 1615006 4369793 := bstep (se 2 (by rfl) ⟨1638672, by rfl⟩ : syracuseStep 4369793 = 3277345) B3277345
theorem B4369945 : Blo 1615006 4369945 := bstep (se 2 (by rfl) ⟨1638729, by rfl⟩ : syracuseStep 4369945 = 3277459) B3277459
theorem B4091431 : Blo 1615006 4091431 := bstep (se 1 (by rfl) ⟨3068573, by rfl⟩ : syracuseStep 4091431 = 6137147) B6137147
theorem B23301755 : Blo 1615006 23301755 := bstep (se 1 (by rfl) ⟨17476316, by rfl⟩ : syracuseStep 23301755 = 34952633) B34952633
theorem B3452539 : Blo 1615006 3452539 := bstep (se 1 (by rfl) ⟨2589404, by rfl⟩ : syracuseStep 3452539 = 5178809) B5178809
theorem B4148875 : Blo 1615006 4148875 := bstep (se 1 (by rfl) ⟨3111656, by rfl⟩ : syracuseStep 4148875 = 6223313) B6223313
theorem B95768243 : Blo 1615006 95768243 := bstep (se 1 (by rfl) ⟨71826182, by rfl⟩ : syracuseStep 95768243 = 143652365) B143652365
theorem B7769789 : Blo 1615006 7769789 := bstep (se 3 (by rfl) ⟨1456835, by rfl⟩ : syracuseStep 7769789 = 2913671) B2913671
theorem B2764535 : Blo 1615006 2764535 := bstep (se 1 (by rfl) ⟨2073401, by rfl⟩ : syracuseStep 2764535 = 4146803) B4146803
theorem B4091755 : Blo 1615006 4091755 := bstep (se 1 (by rfl) ⟨3068816, by rfl⟩ : syracuseStep 4091755 = 6137633) B6137633
theorem B3068027 : Blo 1615006 3068027 := bstep (se 1 (by rfl) ⟨2301020, by rfl⟩ : syracuseStep 3068027 = 4602041) B4602041
theorem B22720675 : Blo 1615006 22720675 := bstep (se 1 (by rfl) ⟨17040506, by rfl⟩ : syracuseStep 22720675 = 34081013) B34081013
theorem B2658475 : Blo 1615006 2658475 := bstep (se 1 (by rfl) ⟨1993856, by rfl⟩ : syracuseStep 2658475 = 3987713) B3987713
theorem B5451947 : Blo 1615006 5451947 := bstep (se 1 (by rfl) ⟨4088960, by rfl⟩ : syracuseStep 5451947 = 8177921) B8177921
theorem B3068255 : Blo 1615006 3068255 := bstep (se 1 (by rfl) ⟨2301191, by rfl⟩ : syracuseStep 3068255 = 4602383) B4602383
theorem B2044379 : Blo 1615006 2044379 := bstep (se 1 (by rfl) ⟨1533284, by rfl⟩ : syracuseStep 2044379 = 3066569) B3066569
theorem B4092403 : Blo 1615006 4092403 := bstep (se 1 (by rfl) ⟨3069302, by rfl⟩ : syracuseStep 4092403 = 6138605) B6138605
theorem B4911641 : Blo 1615006 4911641 := bstep (se 2 (by rfl) ⟨1841865, by rfl⟩ : syracuseStep 4911641 = 3683731) B3683731
theorem B6132257 : Blo 1615006 6132257 := bstep (se 2 (by rfl) ⟨2299596, by rfl⟩ : syracuseStep 6132257 = 4599193) B4599193
theorem B3068513 : Blo 1615006 3068513 := bstep (se 2 (by rfl) ⟨1150692, by rfl⟩ : syracuseStep 3068513 = 2301385) B2301385
theorem B12276359 : Blo 1615006 12276359 := bstep (se 1 (by rfl) ⟨9207269, by rfl⟩ : syracuseStep 12276359 = 18414539) B18414539
theorem B5452487 : Blo 1615006 5452487 := bstep (se 1 (by rfl) ⟨4089365, by rfl⟩ : syracuseStep 5452487 = 8178731) B8178731
theorem B10351313 : Blo 1615006 10351313 := bstep (se 2 (by rfl) ⟨3881742, by rfl⟩ : syracuseStep 10351313 = 7763485) B7763485
theorem B3633875 : Blo 1615006 3633875 := bstep (se 1 (by rfl) ⟨2725406, by rfl⟩ : syracuseStep 3633875 = 5450813) B5450813
theorem B26194691 : Blo 1615006 26194691 := bstep (se 1 (by rfl) ⟨19646018, by rfl⟩ : syracuseStep 26194691 = 39292037) B39292037
theorem B3068779 : Blo 1615006 3068779 := bstep (se 1 (by rfl) ⟨2301584, by rfl⟩ : syracuseStep 3068779 = 4603169) B4603169
theorem B2044855 : Blo 1615006 2044855 := bstep (se 1 (by rfl) ⟨1533641, by rfl⟩ : syracuseStep 2044855 = 3067283) B3067283
theorem B6132743 : Blo 1615006 6132743 := bstep (se 1 (by rfl) ⟨4599557, by rfl⟩ : syracuseStep 6132743 = 9199115) B9199115
theorem B2913289 : Blo 1615006 2913289 := bstep (se 2 (by rfl) ⟨1092483, by rfl⟩ : syracuseStep 2913289 = 2184967) B2184967
theorem B5248079 : Blo 1615006 5248079 := bstep (se 1 (by rfl) ⟨3936059, by rfl⟩ : syracuseStep 5248079 = 7872119) B7872119
theorem B10360001 : Blo 1615006 10360001 := bstep (se 2 (by rfl) ⟨3885000, by rfl⟩ : syracuseStep 10360001 = 7770001) B7770001
theorem B10638539 : Blo 1615006 10638539 := bstep (se 1 (by rfl) ⟨7978904, by rfl⟩ : syracuseStep 10638539 = 15957809) B15957809
theorem B1725791 : Blo 1615006 1725791 := bstep (se 1 (by rfl) ⟨1294343, by rfl⟩ : syracuseStep 1725791 = 2588687) B2588687
theorem B2725339 : Blo 1615006 2725339 := bstep (se 1 (by rfl) ⟨2044004, by rfl⟩ : syracuseStep 2725339 = 4088009) B4088009
theorem B6133229 : Blo 1615006 6133229 := bstep (se 3 (by rfl) ⟨1149980, by rfl⟩ : syracuseStep 6133229 = 2299961) B2299961
theorem B3274247 : Blo 1615006 3274247 := bstep (se 1 (by rfl) ⟨2455685, by rfl⟩ : syracuseStep 3274247 = 4911371) B4911371
theorem B19650059 : Blo 1615006 19650059 := bstep (se 1 (by rfl) ⟨14737544, by rfl⟩ : syracuseStep 19650059 = 29475089) B29475089
theorem B5453351 : Blo 1615006 5453351 := bstep (se 1 (by rfl) ⟨4090013, by rfl⟩ : syracuseStep 5453351 = 8180027) B8180027
theorem B3634811 : Blo 1615006 3634811 := bstep (se 1 (by rfl) ⟨2726108, by rfl⟩ : syracuseStep 3634811 = 5452217) B5452217
theorem B5453459 : Blo 1615006 5453459 := bstep (se 1 (by rfl) ⟨4090094, by rfl⟩ : syracuseStep 5453459 = 8180189) B8180189
theorem B9205447 : Blo 1615006 9205447 := bstep (se 1 (by rfl) ⟨6904085, by rfl⟩ : syracuseStep 9205447 = 13808171) B13808171
theorem B3634937 : Blo 1615006 3634937 := bstep (se 2 (by rfl) ⟨1363101, by rfl⟩ : syracuseStep 3634937 = 2726203) B2726203
theorem B9828191 : Blo 1615006 9828191 := bstep (se 1 (by rfl) ⟨7371143, by rfl⟩ : syracuseStep 9828191 = 14742287) B14742287
theorem B5453675 : Blo 1615006 5453675 := bstep (se 1 (by rfl) ⟨4090256, by rfl⟩ : syracuseStep 5453675 = 8180513) B8180513
theorem B5453729 : Blo 1615006 5453729 := bstep (se 2 (by rfl) ⟨2045148, by rfl⟩ : syracuseStep 5453729 = 4090297) B4090297
theorem B2422703 : Blo 1615006 2422703 := bstep (se 1 (by rfl) ⟨1817027, by rfl⟩ : syracuseStep 2422703 = 3634055) B3634055
theorem B80811989 : Blo 1615006 80811989 := bstep (se 7 (by rfl) ⟨947015, by rfl⟩ : syracuseStep 80811989 = 1894031) B1894031
theorem B3635207 : Blo 1615006 3635207 := bstep (se 1 (by rfl) ⟨2726405, by rfl⟩ : syracuseStep 3635207 = 5452811) B5452811
theorem B2422793 : Blo 1615006 2422793 := bstep (se 2 (by rfl) ⟨908547, by rfl⟩ : syracuseStep 2422793 = 1817095) B1817095
theorem B2422823 : Blo 1615006 2422823 := bstep (se 1 (by rfl) ⟨1817117, by rfl⟩ : syracuseStep 2422823 = 3634235) B3634235
theorem B12277817 : Blo 1615006 12277817 := bstep (se 2 (by rfl) ⟨4604181, by rfl⟩ : syracuseStep 12277817 = 9208363) B9208363
theorem B2725967 : Blo 1615006 2725967 := bstep (se 1 (by rfl) ⟨2044475, by rfl⟩ : syracuseStep 2725967 = 4088951) B4088951
theorem B3635279 : Blo 1615006 3635279 := bstep (se 1 (by rfl) ⟨2726459, by rfl⟩ : syracuseStep 3635279 = 5452919) B5452919
theorem B1726543 : Blo 1615006 1726543 := bstep (se 1 (by rfl) ⟨1294907, by rfl⟩ : syracuseStep 1726543 = 2589815) B2589815
theorem B21002327 : Blo 1615006 21002327 := bstep (se 1 (by rfl) ⟨15751745, by rfl⟩ : syracuseStep 21002327 = 31503491) B31503491
theorem B2422907 : Blo 1615006 2422907 := bstep (se 1 (by rfl) ⟨1817180, by rfl⟩ : syracuseStep 2422907 = 3634361) B3634361
theorem B6133913 : Blo 1615006 6133913 := bstep (se 2 (by rfl) ⟨2300217, by rfl⟩ : syracuseStep 6133913 = 4600435) B4600435
theorem B49739933 : Blo 1615006 49739933 := bstep (se 3 (by rfl) ⟨9326237, by rfl⟩ : syracuseStep 49739933 = 18652475) B18652475
theorem B2046151 : Blo 1615006 2046151 := bstep (se 1 (by rfl) ⟨1534613, by rfl⟩ : syracuseStep 2046151 = 3069227) B3069227
theorem B2423033 : Blo 1615006 2423033 := bstep (se 2 (by rfl) ⟨908637, by rfl⟩ : syracuseStep 2423033 = 1817275) B1817275
theorem B26220833 : Blo 1615006 26220833 := bstep (se 2 (by rfl) ⟨9832812, by rfl⟩ : syracuseStep 26220833 = 19665625) B19665625
theorem B11802941 : Blo 1615006 11802941 := bstep (se 3 (by rfl) ⟨2213051, by rfl⟩ : syracuseStep 11802941 = 4426103) B4426103
theorem B2423135 : Blo 1615006 2423135 := bstep (se 1 (by rfl) ⟨1817351, by rfl⟩ : syracuseStep 2423135 = 3634703) B3634703
theorem B7764329 : Blo 1615006 7764329 := bstep (se 2 (by rfl) ⟨2911623, by rfl⟩ : syracuseStep 7764329 = 5823247) B5823247
theorem B2423147 : Blo 1615006 2423147 := bstep (se 1 (by rfl) ⟨1817360, by rfl⟩ : syracuseStep 2423147 = 3634721) B3634721
theorem B3635675 : Blo 1615006 3635675 := bstep (se 1 (by rfl) ⟨2726756, by rfl⟩ : syracuseStep 3635675 = 5453513) B5453513
theorem B5454323 : Blo 1615006 5454323 := bstep (se 1 (by rfl) ⟨4090742, by rfl⟩ : syracuseStep 5454323 = 8181485) B8181485
theorem B69884491 : Blo 1615006 69884491 := bstep (se 1 (by rfl) ⟨52413368, by rfl⟩ : syracuseStep 69884491 = 104826737) B104826737
theorem B1817167 : Blo 1615006 1817167 := bstep (se 1 (by rfl) ⟨1362875, by rfl⟩ : syracuseStep 1817167 = 2725751) B2725751
theorem B2423375 : Blo 1615006 2423375 := bstep (se 1 (by rfl) ⟨1817531, by rfl⟩ : syracuseStep 2423375 = 3635063) B3635063
theorem B8182457 : Blo 1615006 8182457 := bstep (se 2 (by rfl) ⟨3068421, by rfl⟩ : syracuseStep 8182457 = 6136843) B6136843
theorem B2423495 : Blo 1615006 2423495 := bstep (se 1 (by rfl) ⟨1817621, by rfl⟩ : syracuseStep 2423495 = 3635243) B3635243
theorem B5823191 : Blo 1615006 5823191 := bstep (se 1 (by rfl) ⟨4367393, by rfl⟩ : syracuseStep 5823191 = 8734787) B8734787
theorem B2423657 : Blo 1615006 2423657 := bstep (se 2 (by rfl) ⟨908871, by rfl⟩ : syracuseStep 2423657 = 1817743) B1817743
theorem B2726831 : Blo 1615006 2726831 := bstep (se 1 (by rfl) ⟨2045123, by rfl⟩ : syracuseStep 2726831 = 4090247) B4090247
theorem B3636143 : Blo 1615006 3636143 := bstep (se 1 (by rfl) ⟨2727107, by rfl⟩ : syracuseStep 3636143 = 5454215) B5454215
theorem B2423735 : Blo 1615006 2423735 := bstep (se 1 (by rfl) ⟨1817801, by rfl⟩ : syracuseStep 2423735 = 3635603) B3635603
theorem B1817563 : Blo 1615006 1817563 := bstep (se 1 (by rfl) ⟨1363172, by rfl⟩ : syracuseStep 1817563 = 2726345) B2726345
theorem B2423771 : Blo 1615006 2423771 := bstep (se 1 (by rfl) ⟨1817828, by rfl⟩ : syracuseStep 2423771 = 3635657) B3635657
theorem B5454863 : Blo 1615006 5454863 := bstep (se 1 (by rfl) ⟨4091147, by rfl⟩ : syracuseStep 5454863 = 8182295) B8182295
theorem B6134899 : Blo 1615006 6134899 := bstep (se 1 (by rfl) ⟨4601174, by rfl⟩ : syracuseStep 6134899 = 9202349) B9202349
theorem B3636395 : Blo 1615006 3636395 := bstep (se 1 (by rfl) ⟨2727296, by rfl⟩ : syracuseStep 3636395 = 5454593) B5454593
theorem B6905027 : Blo 1615006 6905027 := bstep (se 1 (by rfl) ⟨5178770, by rfl⟩ : syracuseStep 6905027 = 10357541) B10357541
theorem B18398501 : Blo 1615006 18398501 := bstep (se 4 (by rfl) ⟨1724859, by rfl⟩ : syracuseStep 18398501 = 3449719) B3449719
theorem B2727263 : Blo 1615006 2727263 := bstep (se 1 (by rfl) ⟨2045447, by rfl⟩ : syracuseStep 2727263 = 4090895) B4090895
theorem B4365697 : Blo 1615006 4365697 := bstep (se 2 (by rfl) ⟨1637136, by rfl⟩ : syracuseStep 4365697 = 3274273) B3274273
theorem B12271013 : Blo 1615006 12271013 := bstep (se 4 (by rfl) ⟨1150407, by rfl⟩ : syracuseStep 12271013 = 2300815) B2300815
theorem B1818031 : Blo 1615006 1818031 := bstep (se 1 (by rfl) ⟨1363523, by rfl⟩ : syracuseStep 1818031 = 2727047) B2727047
theorem B2424239 : Blo 1615006 2424239 := bstep (se 1 (by rfl) ⟨1818179, by rfl⟩ : syracuseStep 2424239 = 3636359) B3636359
theorem B2424329 : Blo 1615006 2424329 := bstep (se 2 (by rfl) ⟨909123, by rfl⟩ : syracuseStep 2424329 = 1818247) B1818247
theorem B31055399 : Blo 1615006 31055399 := bstep (se 1 (by rfl) ⟨23291549, by rfl⟩ : syracuseStep 31055399 = 46583099) B46583099
theorem B13803047 : Blo 1615006 13803047 := bstep (se 1 (by rfl) ⟨10352285, by rfl⟩ : syracuseStep 13803047 = 20704571) B20704571
theorem B2424359 : Blo 1615006 2424359 := bstep (se 1 (by rfl) ⟨1818269, by rfl⟩ : syracuseStep 2424359 = 3636539) B3636539
theorem B5455457 : Blo 1615006 5455457 := bstep (se 2 (by rfl) ⟨2045796, by rfl⟩ : syracuseStep 5455457 = 4091593) B4091593
theorem B2424443 : Blo 1615006 2424443 := bstep (se 1 (by rfl) ⟨1818332, by rfl⟩ : syracuseStep 2424443 = 3636665) B3636665
theorem B3636935 : Blo 1615006 3636935 := bstep (se 1 (by rfl) ⟨2727701, by rfl⟩ : syracuseStep 3636935 = 5455403) B5455403
theorem B7765753 : Blo 1615006 7765753 := bstep (se 2 (by rfl) ⟨2912157, by rfl⟩ : syracuseStep 7765753 = 5824315) B5824315
theorem B2424569 : Blo 1615006 2424569 := bstep (se 2 (by rfl) ⟨909213, by rfl⟩ : syracuseStep 2424569 = 1818427) B1818427
theorem B1818463 : Blo 1615006 1818463 := bstep (se 1 (by rfl) ⟨1363847, by rfl⟩ : syracuseStep 1818463 = 2727695) B2727695
theorem B2424671 : Blo 1615006 2424671 := bstep (se 1 (by rfl) ⟨1818503, by rfl⟩ : syracuseStep 2424671 = 3637007) B3637007
theorem B6135659 : Blo 1615006 6135659 := bstep (se 1 (by rfl) ⟨4601744, by rfl⟩ : syracuseStep 6135659 = 9203489) B9203489
theorem B2424683 : Blo 1615006 2424683 := bstep (se 1 (by rfl) ⟨1818512, by rfl⟩ : syracuseStep 2424683 = 3637025) B3637025
theorem B2727823 : Blo 1615006 2727823 := bstep (se 1 (by rfl) ⟨2045867, by rfl⟩ : syracuseStep 2727823 = 4091735) B4091735
theorem B5177449 : Blo 1615006 5177449 := bstep (se 2 (by rfl) ⟨1941543, by rfl⟩ : syracuseStep 5177449 = 3883087) B3883087
theorem B2302057 : Blo 1615006 2302057 := bstep (se 2 (by rfl) ⟨863271, by rfl⟩ : syracuseStep 2302057 = 1726543) B1726543
theorem B30294233 : Blo 1615006 30294233 := bstep (se 2 (by rfl) ⟨11360337, by rfl⟩ : syracuseStep 30294233 = 22720675) B22720675
theorem B20709593 : Blo 1615006 20709593 := bstep (se 2 (by rfl) ⟨7766097, by rfl⟩ : syracuseStep 20709593 = 15532195) B15532195
theorem B2728201 : Blo 1615006 2728201 := bstep (se 2 (by rfl) ⟨1023075, by rfl⟩ : syracuseStep 2728201 = 2046151) B2046151
theorem B2425097 : Blo 1615006 2425097 := bstep (se 2 (by rfl) ⟨909411, by rfl⟩ : syracuseStep 2425097 = 1818823) B1818823
theorem B4088171 : Blo 1615006 4088171 := bstep (se 1 (by rfl) ⟨3066128, by rfl⟩ : syracuseStep 4088171 = 6132257) B6132257
theorem B2425199 : Blo 1615006 2425199 := bstep (se 1 (by rfl) ⟨1818899, by rfl⟩ : syracuseStep 2425199 = 3637799) B3637799
theorem B1819003 : Blo 1615006 1819003 := bstep (se 1 (by rfl) ⟨1364252, by rfl⟩ : syracuseStep 1819003 = 2728505) B2728505
theorem B8184239 : Blo 1615006 8184239 := bstep (se 1 (by rfl) ⟨6138179, by rfl⟩ : syracuseStep 8184239 = 12276359) B12276359
theorem B2425415 : Blo 1615006 2425415 := bstep (se 1 (by rfl) ⟨1819061, by rfl⟩ : syracuseStep 2425415 = 3638123) B3638123
theorem B2425451 : Blo 1615006 2425451 := bstep (se 1 (by rfl) ⟨1819088, by rfl⟩ : syracuseStep 2425451 = 3638177) B3638177
theorem B7766675 : Blo 1615006 7766675 := bstep (se 1 (by rfl) ⟨5825006, by rfl⟩ : syracuseStep 7766675 = 11650013) B11650013
theorem B5456537 : Blo 1615006 5456537 := bstep (se 2 (by rfl) ⟨2046201, by rfl⟩ : syracuseStep 5456537 = 4092403) B4092403
theorem B4088495 : Blo 1615006 4088495 := bstep (se 1 (by rfl) ⟨3066371, by rfl⟩ : syracuseStep 4088495 = 6132743) B6132743
theorem B4915895 : Blo 1615006 4915895 := bstep (se 1 (by rfl) ⟨3686921, by rfl⟩ : syracuseStep 4915895 = 7373843) B7373843
theorem B3637943 : Blo 1615006 3637943 := bstep (se 1 (by rfl) ⟨2728457, by rfl⟩ : syracuseStep 3637943 = 5456915) B5456915
theorem B3498719 : Blo 1615006 3498719 := bstep (se 1 (by rfl) ⟨2624039, by rfl⟩ : syracuseStep 3498719 = 5248079) B5248079
theorem B6906667 : Blo 1615006 6906667 := bstep (se 1 (by rfl) ⟨5180000, by rfl⟩ : syracuseStep 6906667 = 10360001) B10360001
theorem B8176463 : Blo 1615006 8176463 := bstep (se 1 (by rfl) ⟨6132347, by rfl⟩ : syracuseStep 8176463 = 12264695) B12264695
theorem B3638159 : Blo 1615006 3638159 := bstep (se 1 (by rfl) ⟨2728619, by rfl⟩ : syracuseStep 3638159 = 5457239) B5457239
theorem B4088819 : Blo 1615006 4088819 := bstep (se 1 (by rfl) ⟨3066614, by rfl⟩ : syracuseStep 4088819 = 6133229) B6133229
theorem B13100039 : Blo 1615006 13100039 := bstep (se 1 (by rfl) ⟨9825029, by rfl⟩ : syracuseStep 13100039 = 19650059) B19650059
theorem B8176787 : Blo 1615006 8176787 := bstep (se 1 (by rfl) ⟨6132590, by rfl⟩ : syracuseStep 8176787 = 12265181) B12265181
theorem B4146391 : Blo 1615006 4146391 := bstep (se 1 (by rfl) ⟨3109793, by rfl⟩ : syracuseStep 4146391 = 6219587) B6219587
theorem B1615135 : Blo 1615006 1615135 := bstep (se 1 (by rfl) ⟨1211351, by rfl⟩ : syracuseStep 1615135 = 2422703) B2422703
theorem B11650391 : Blo 1615006 11650391 := bstep (se 1 (by rfl) ⟨8737793, by rfl⟩ : syracuseStep 11650391 = 17475587) B17475587
theorem B1615195 : Blo 1615006 1615195 := bstep (se 1 (by rfl) ⟨1211396, by rfl⟩ : syracuseStep 1615195 = 2422793) B2422793
theorem B1615215 : Blo 1615006 1615215 := bstep (se 1 (by rfl) ⟨1211411, by rfl⟩ : syracuseStep 1615215 = 2422823) B2422823
theorem B8185211 : Blo 1615006 8185211 := bstep (se 1 (by rfl) ⟨6138908, by rfl⟩ : syracuseStep 8185211 = 12277817) B12277817
theorem B14001551 : Blo 1615006 14001551 := bstep (se 1 (by rfl) ⟨10501163, by rfl⟩ : syracuseStep 14001551 = 21002327) B21002327
theorem B1615271 : Blo 1615006 1615271 := bstep (se 1 (by rfl) ⟨1211453, by rfl⟩ : syracuseStep 1615271 = 2422907) B2422907
theorem B4089275 : Blo 1615006 4089275 := bstep (se 1 (by rfl) ⟨3066956, by rfl⟩ : syracuseStep 4089275 = 6133913) B6133913
theorem B1615355 : Blo 1615006 1615355 := bstep (se 1 (by rfl) ⟨1211516, by rfl⟩ : syracuseStep 1615355 = 2423033) B2423033
theorem B5178937 : Blo 1615006 5178937 := bstep (se 2 (by rfl) ⟨1942101, by rfl⟩ : syracuseStep 5178937 = 3884203) B3884203
theorem B1615423 : Blo 1615006 1615423 := bstep (se 1 (by rfl) ⟨1211567, by rfl⟩ : syracuseStep 1615423 = 2423135) B2423135
theorem B1615431 : Blo 1615006 1615431 := bstep (se 1 (by rfl) ⟨1211573, by rfl⟩ : syracuseStep 1615431 = 2423147) B2423147
theorem B1615583 : Blo 1615006 1615583 := bstep (se 1 (by rfl) ⟨1211687, by rfl⟩ : syracuseStep 1615583 = 2423375) B2423375
theorem B1615663 : Blo 1615006 1615663 := bstep (se 1 (by rfl) ⟨1211747, by rfl⟩ : syracuseStep 1615663 = 2423495) B2423495
theorem B84002669 : Blo 1615006 84002669 := bstep (se 3 (by rfl) ⟨15750500, by rfl⟩ : syracuseStep 84002669 = 31501001) B31501001
theorem B1615771 : Blo 1615006 1615771 := bstep (se 1 (by rfl) ⟨1211828, by rfl⟩ : syracuseStep 1615771 = 2423657) B2423657
theorem B17467319 : Blo 1615006 17467319 := bstep (se 1 (by rfl) ⟨13100489, by rfl⟩ : syracuseStep 17467319 = 26200979) B26200979
theorem B1615823 : Blo 1615006 1615823 := bstep (se 1 (by rfl) ⟨1211867, by rfl⟩ : syracuseStep 1615823 = 2423735) B2423735
theorem B1615847 : Blo 1615006 1615847 := bstep (se 1 (by rfl) ⟨1211885, by rfl⟩ : syracuseStep 1615847 = 2423771) B2423771
theorem B5826593 : Blo 1615006 5826593 := bstep (se 2 (by rfl) ⟨2184972, by rfl⟩ : syracuseStep 5826593 = 4369945) B4369945
theorem B5531833 : Blo 1615006 5531833 := bstep (se 2 (by rfl) ⟨2074437, by rfl⟩ : syracuseStep 5531833 = 4148875) B4148875
theorem B12265667 : Blo 1615006 12265667 := bstep (se 1 (by rfl) ⟨9199250, by rfl⟩ : syracuseStep 12265667 = 18398501) B18398501
theorem B12273929 : Blo 1615006 12273929 := bstep (se 2 (by rfl) ⟨4602723, by rfl⟩ : syracuseStep 12273929 = 9205447) B9205447
theorem B1616159 : Blo 1615006 1616159 := bstep (se 1 (by rfl) ⟨1212119, by rfl⟩ : syracuseStep 1616159 = 2424239) B2424239
theorem B1616219 : Blo 1615006 1616219 := bstep (se 1 (by rfl) ⟨1212164, by rfl⟩ : syracuseStep 1616219 = 2424329) B2424329
theorem B20703599 : Blo 1615006 20703599 := bstep (se 1 (by rfl) ⟨15527699, by rfl⟩ : syracuseStep 20703599 = 31055399) B31055399
theorem B9202031 : Blo 1615006 9202031 := bstep (se 1 (by rfl) ⟨6901523, by rfl⟩ : syracuseStep 9202031 = 13803047) B13803047
theorem B1616239 : Blo 1615006 1616239 := bstep (se 1 (by rfl) ⟨1212179, by rfl⟩ : syracuseStep 1616239 = 2424359) B2424359
theorem B1616295 : Blo 1615006 1616295 := bstep (se 1 (by rfl) ⟨1212221, by rfl⟩ : syracuseStep 1616295 = 2424443) B2424443
theorem B15534503 : Blo 1615006 15534503 := bstep (se 1 (by rfl) ⟨11650877, by rfl⟩ : syracuseStep 15534503 = 23301755) B23301755
theorem B5179859 : Blo 1615006 5179859 := bstep (se 1 (by rfl) ⟨3884894, by rfl⟩ : syracuseStep 5179859 = 7769789) B7769789
theorem B1616379 : Blo 1615006 1616379 := bstep (se 1 (by rfl) ⟨1212284, by rfl⟩ : syracuseStep 1616379 = 2424569) B2424569
theorem B1616447 : Blo 1615006 1616447 := bstep (se 1 (by rfl) ⟨1212335, by rfl⟩ : syracuseStep 1616447 = 2424671) B2424671
theorem B4090439 : Blo 1615006 4090439 := bstep (se 1 (by rfl) ⟨3067829, by rfl⟩ : syracuseStep 4090439 = 6135659) B6135659
theorem B1616455 : Blo 1615006 1616455 := bstep (se 1 (by rfl) ⟨1212341, by rfl⟩ : syracuseStep 1616455 = 2424683) B2424683
theorem B1616607 : Blo 1615006 1616607 := bstep (se 1 (by rfl) ⟨1212455, by rfl⟩ : syracuseStep 1616607 = 2424911) B2424911
theorem B1616687 : Blo 1615006 1616687 := bstep (se 1 (by rfl) ⟨1212515, by rfl⟩ : syracuseStep 1616687 = 2425031) B2425031
theorem B5450651 : Blo 1615006 5450651 := bstep (se 1 (by rfl) ⟨4087988, by rfl⟩ : syracuseStep 5450651 = 8175977) B8175977
theorem B1616795 : Blo 1615006 1616795 := bstep (se 1 (by rfl) ⟨1212596, by rfl⟩ : syracuseStep 1616795 = 2425193) B2425193
theorem B1616847 : Blo 1615006 1616847 := bstep (se 1 (by rfl) ⟨1212635, by rfl⟩ : syracuseStep 1616847 = 2425271) B2425271
theorem B1616871 : Blo 1615006 1616871 := bstep (se 1 (by rfl) ⟨1212653, by rfl⟩ : syracuseStep 1616871 = 2425307) B2425307
theorem B6900875 : Blo 1615006 6900875 := bstep (se 1 (by rfl) ⟨5175656, by rfl⟩ : syracuseStep 6900875 = 10351313) B10351313
theorem B10358077 : Blo 1615006 10358077 := bstep (se 3 (by rfl) ⟨1942139, by rfl⟩ : syracuseStep 10358077 = 3884279) B3884279
theorem B6139273 : Blo 1615006 6139273 := bstep (se 2 (by rfl) ⟨2302227, by rfl⟩ : syracuseStep 6139273 = 4604455) B4604455
theorem B93179321 : Blo 1615006 93179321 := bstep (se 2 (by rfl) ⟨34942245, by rfl⟩ : syracuseStep 93179321 = 69884491) B69884491
theorem B11652781 : Blo 1615006 11652781 := bstep (se 3 (by rfl) ⟨2184896, by rfl⟩ : syracuseStep 11652781 = 4369793) B4369793
theorem B2182831 : Blo 1615006 2182831 := bstep (se 1 (by rfl) ⟨1637123, by rfl⟩ : syracuseStep 2182831 = 3274247) B3274247
theorem B3452719 : Blo 1615006 3452719 := bstep (se 1 (by rfl) ⟨2589539, by rfl⟩ : syracuseStep 3452719 = 5179079) B5179079
theorem B4091705 : Blo 1615006 4091705 := bstep (se 2 (by rfl) ⟨1534389, by rfl⟩ : syracuseStep 4091705 = 3068779) B3068779
theorem B5451677 : Blo 1615006 5451677 := bstep (se 3 (by rfl) ⟨1022189, by rfl⟩ : syracuseStep 5451677 = 2044379) B2044379
theorem B53874659 : Blo 1615006 53874659 := bstep (se 1 (by rfl) ⟨40405994, by rfl⟩ : syracuseStep 53874659 = 80811989) B80811989
theorem B5451785 : Blo 1615006 5451785 := bstep (se 2 (by rfl) ⟨2044419, by rfl⟩ : syracuseStep 5451785 = 4088839) B4088839
theorem B8179865 : Blo 1615006 8179865 := bstep (se 2 (by rfl) ⟨3067449, by rfl⟩ : syracuseStep 8179865 = 6134899) B6134899
theorem B69906635 : Blo 1615006 69906635 := bstep (se 1 (by rfl) ⟨52429976, by rfl⟩ : syracuseStep 69906635 = 104859953) B104859953
theorem B7868627 : Blo 1615006 7868627 := bstep (se 1 (by rfl) ⟨5901470, by rfl⟩ : syracuseStep 7868627 = 11802941) B11802941
theorem B5820929 : Blo 1615006 5820929 := bstep (se 2 (by rfl) ⟨2182848, by rfl⟩ : syracuseStep 5820929 = 4365697) B4365697
theorem B7762483 : Blo 1615006 7762483 := bstep (se 1 (by rfl) ⟨5821862, by rfl⟩ : syracuseStep 7762483 = 11643725) B11643725
theorem B3633785 : Blo 1615006 3633785 := bstep (se 2 (by rfl) ⟨1362669, by rfl⟩ : syracuseStep 3633785 = 2725339) B2725339
theorem B3633839 : Blo 1615006 3633839 := bstep (se 1 (by rfl) ⟨2725379, by rfl⟩ : syracuseStep 3633839 = 5450759) B5450759
theorem B3633911 : Blo 1615006 3633911 := bstep (se 1 (by rfl) ⟨2725433, by rfl⟩ : syracuseStep 3633911 = 5450867) B5450867
theorem B3634091 : Blo 1615006 3634091 := bstep (se 1 (by rfl) ⟨2725568, by rfl⟩ : syracuseStep 3634091 = 5451137) B5451137
theorem B8180675 : Blo 1615006 8180675 := bstep (se 1 (by rfl) ⟨6135506, by rfl⟩ : syracuseStep 8180675 = 12271013) B12271013
theorem B63845495 : Blo 1615006 63845495 := bstep (se 1 (by rfl) ⟨47884121, by rfl⟩ : syracuseStep 63845495 = 95768243) B95768243
theorem B27604313 : Blo 1615006 27604313 := bstep (se 2 (by rfl) ⟨10351617, by rfl⟩ : syracuseStep 27604313 = 20703235) B20703235
theorem B15537541 : Blo 1615006 15537541 := bstep (se 4 (by rfl) ⟨1456644, by rfl⟩ : syracuseStep 15537541 = 2913289) B2913289
theorem B2045351 : Blo 1615006 2045351 := bstep (se 1 (by rfl) ⟨1534013, by rfl⟩ : syracuseStep 2045351 = 3068027) B3068027
theorem B3634631 : Blo 1615006 3634631 := bstep (se 1 (by rfl) ⟨2725973, by rfl⟩ : syracuseStep 3634631 = 5451947) B5451947
theorem B3544633 : Blo 1615006 3544633 := bstep (se 2 (by rfl) ⟨1329237, by rfl⟩ : syracuseStep 3544633 = 2658475) B2658475
theorem B2045503 : Blo 1615006 2045503 := bstep (se 1 (by rfl) ⟨1534127, by rfl⟩ : syracuseStep 2045503 = 3068255) B3068255
theorem B3274427 : Blo 1615006 3274427 := bstep (se 1 (by rfl) ⟨2455820, by rfl⟩ : syracuseStep 3274427 = 4911641) B4911641
theorem B2045675 : Blo 1615006 2045675 := bstep (se 1 (by rfl) ⟨1534256, by rfl⟩ : syracuseStep 2045675 = 3068513) B3068513
theorem B3634991 : Blo 1615006 3634991 := bstep (se 1 (by rfl) ⟨2726243, by rfl⟩ : syracuseStep 3634991 = 5452487) B5452487
theorem B2422583 : Blo 1615006 2422583 := bstep (se 1 (by rfl) ⟨1816937, by rfl⟩ : syracuseStep 2422583 = 3633875) B3633875
theorem B3069751 : Blo 1615006 3069751 := bstep (se 1 (by rfl) ⟨2302313, by rfl⟩ : syracuseStep 3069751 = 4604627) B4604627
theorem B17463127 : Blo 1615006 17463127 := bstep (se 1 (by rfl) ⟨13097345, by rfl⟩ : syracuseStep 17463127 = 26194691) B26194691
theorem B29472605 : Blo 1615006 29472605 := bstep (se 3 (by rfl) ⟨5526113, by rfl⟩ : syracuseStep 29472605 = 11052227) B11052227
theorem B3684361 : Blo 1615006 3684361 := bstep (se 2 (by rfl) ⟨1381635, by rfl⟩ : syracuseStep 3684361 = 2763271) B2763271
theorem B2422889 : Blo 1615006 2422889 := bstep (se 2 (by rfl) ⟨908583, by rfl⟩ : syracuseStep 2422889 = 1817167) B1817167
theorem B7092359 : Blo 1615006 7092359 := bstep (se 1 (by rfl) ⟨5319269, by rfl⟩ : syracuseStep 7092359 = 10638539) B10638539
theorem B4602109 : Blo 1615006 4602109 := bstep (se 3 (by rfl) ⟨862895, by rfl⟩ : syracuseStep 4602109 = 1725791) B1725791
theorem B5822729 : Blo 1615006 5822729 := bstep (se 2 (by rfl) ⟨2183523, by rfl⟩ : syracuseStep 5822729 = 4367047) B4367047
theorem B3635567 : Blo 1615006 3635567 := bstep (se 1 (by rfl) ⟨2726675, by rfl⟩ : syracuseStep 3635567 = 5453351) B5453351
theorem B8739197 : Blo 1615006 8739197 := bstep (se 3 (by rfl) ⟨1638599, by rfl⟩ : syracuseStep 8739197 = 3277199) B3277199
theorem B2423207 : Blo 1615006 2423207 := bstep (se 1 (by rfl) ⟨1817405, by rfl⟩ : syracuseStep 2423207 = 3634811) B3634811
theorem B2726311 : Blo 1615006 2726311 := bstep (se 1 (by rfl) ⟨2044733, by rfl⟩ : syracuseStep 2726311 = 4089467) B4089467
theorem B3635639 : Blo 1615006 3635639 := bstep (se 1 (by rfl) ⟨2726729, by rfl⟩ : syracuseStep 3635639 = 5453459) B5453459
theorem B2423291 : Blo 1615006 2423291 := bstep (se 1 (by rfl) ⟨1817468, by rfl⟩ : syracuseStep 2423291 = 3634937) B3634937
theorem B6552127 : Blo 1615006 6552127 := bstep (se 1 (by rfl) ⟨4914095, by rfl⟩ : syracuseStep 6552127 = 9828191) B9828191
theorem B3635783 : Blo 1615006 3635783 := bstep (se 1 (by rfl) ⟨2726837, by rfl⟩ : syracuseStep 3635783 = 5453675) B5453675
theorem B2726473 : Blo 1615006 2726473 := bstep (se 2 (by rfl) ⟨1022427, by rfl⟩ : syracuseStep 2726473 = 2044855) B2044855
theorem B2726507 : Blo 1615006 2726507 := bstep (se 1 (by rfl) ⟨2044880, by rfl⟩ : syracuseStep 2726507 = 4089761) B4089761
theorem B3635819 : Blo 1615006 3635819 := bstep (se 1 (by rfl) ⟨2726864, by rfl⟩ : syracuseStep 3635819 = 5453729) B5453729
theorem B32365163 : Blo 1615006 32365163 := bstep (se 1 (by rfl) ⟨24273872, by rfl⟩ : syracuseStep 32365163 = 48547745) B48547745
theorem B2423417 : Blo 1615006 2423417 := bstep (se 2 (by rfl) ⟨908781, by rfl⟩ : syracuseStep 2423417 = 1817563) B1817563
theorem B2423471 : Blo 1615006 2423471 := bstep (se 1 (by rfl) ⟨1817603, by rfl⟩ : syracuseStep 2423471 = 3635207) B3635207
theorem B2300599 : Blo 1615006 2300599 := bstep (se 1 (by rfl) ⟨1725449, by rfl⟩ : syracuseStep 2300599 = 3450899) B3450899
theorem B1817311 : Blo 1615006 1817311 := bstep (se 1 (by rfl) ⟨1362983, by rfl⟩ : syracuseStep 1817311 = 2725967) B2725967
theorem B2423519 : Blo 1615006 2423519 := bstep (se 1 (by rfl) ⟨1817639, by rfl⟩ : syracuseStep 2423519 = 3635279) B3635279
theorem B33159955 : Blo 1615006 33159955 := bstep (se 1 (by rfl) ⟨24869966, by rfl⟩ : syracuseStep 33159955 = 49739933) B49739933
theorem B17480555 : Blo 1615006 17480555 := bstep (se 1 (by rfl) ⟨13110416, by rfl⟩ : syracuseStep 17480555 = 26220833) B26220833
theorem B5176219 : Blo 1615006 5176219 := bstep (se 1 (by rfl) ⟨3882164, by rfl⟩ : syracuseStep 5176219 = 7764329) B7764329
theorem B2300827 : Blo 1615006 2300827 := bstep (se 1 (by rfl) ⟨1725620, by rfl⟩ : syracuseStep 2300827 = 3451241) B3451241
theorem B2423783 : Blo 1615006 2423783 := bstep (se 1 (by rfl) ⟨1817837, by rfl⟩ : syracuseStep 2423783 = 3635675) B3635675
theorem B3636215 : Blo 1615006 3636215 := bstep (se 1 (by rfl) ⟨2727161, by rfl⟩ : syracuseStep 3636215 = 5454323) B5454323
theorem B5454971 : Blo 1615006 5454971 := bstep (se 1 (by rfl) ⟨4091228, by rfl⟩ : syracuseStep 5454971 = 8182457) B8182457
theorem B3882127 : Blo 1615006 3882127 := bstep (se 1 (by rfl) ⟨2911595, by rfl⟩ : syracuseStep 3882127 = 5823191) B5823191
theorem B2424041 : Blo 1615006 2424041 := bstep (se 2 (by rfl) ⟨909015, by rfl⟩ : syracuseStep 2424041 = 1818031) B1818031
theorem B1817887 : Blo 1615006 1817887 := bstep (se 1 (by rfl) ⟨1363415, by rfl⟩ : syracuseStep 1817887 = 2726831) B2726831
theorem B2424095 : Blo 1615006 2424095 := bstep (se 1 (by rfl) ⟨1818071, by rfl⟩ : syracuseStep 2424095 = 3636143) B3636143
theorem B7372093 : Blo 1615006 7372093 := bstep (se 3 (by rfl) ⟨1382267, by rfl⟩ : syracuseStep 7372093 = 2764535) B2764535
theorem B3636575 : Blo 1615006 3636575 := bstep (se 1 (by rfl) ⟨2727431, by rfl⟩ : syracuseStep 3636575 = 5454863) B5454863
theorem B5455241 : Blo 1615006 5455241 := bstep (se 2 (by rfl) ⟨2045715, by rfl⟩ : syracuseStep 5455241 = 4091431) B4091431
theorem B2424263 : Blo 1615006 2424263 := bstep (se 1 (by rfl) ⟨1818197, by rfl⟩ : syracuseStep 2424263 = 3636395) B3636395
theorem B4603351 : Blo 1615006 4603351 := bstep (se 1 (by rfl) ⟨3452513, by rfl⟩ : syracuseStep 4603351 = 6905027) B6905027
theorem B4603385 : Blo 1615006 4603385 := bstep (se 2 (by rfl) ⟨1726269, by rfl⟩ : syracuseStep 4603385 = 3452539) B3452539
theorem B1818175 : Blo 1615006 1818175 := bstep (se 1 (by rfl) ⟨1363631, by rfl⟩ : syracuseStep 1818175 = 2727263) B2727263
theorem B6823507 : Blo 1615006 6823507 := bstep (se 1 (by rfl) ⟨5117630, by rfl⟩ : syracuseStep 6823507 = 10235261) B10235261
theorem B10354337 : Blo 1615006 10354337 := bstep (se 2 (by rfl) ⟨3882876, by rfl⟩ : syracuseStep 10354337 = 7765753) B7765753
theorem B3636971 : Blo 1615006 3636971 := bstep (se 1 (by rfl) ⟨2727728, by rfl⟩ : syracuseStep 3636971 = 5455457) B5455457
theorem B2424617 : Blo 1615006 2424617 := bstep (se 2 (by rfl) ⟨909231, by rfl⟩ : syracuseStep 2424617 = 1818463) B1818463
theorem B2424623 : Blo 1615006 2424623 := bstep (se 1 (by rfl) ⟨1818467, by rfl⟩ : syracuseStep 2424623 = 3636935) B3636935
theorem B5455673 : Blo 1615006 5455673 := bstep (se 2 (by rfl) ⟨2045877, by rfl⟩ : syracuseStep 5455673 = 4091755) B4091755
theorem B9199433 : Blo 1615006 9199433 := bstep (se 2 (by rfl) ⟨3449787, by rfl⟩ : syracuseStep 9199433 = 6899575) B6899575
theorem B3637097 : Blo 1615006 3637097 := bstep (se 2 (by rfl) ⟨1363911, by rfl⟩ : syracuseStep 3637097 = 2727823) B2727823
theorem B46604423 : Blo 1615006 46604423 := bstep (se 1 (by rfl) ⟨34953317, by rfl⟩ : syracuseStep 46604423 = 69906635) B69906635
theorem B5456159 : Blo 1615006 5456159 := bstep (se 1 (by rfl) ⟨4092119, by rfl⟩ : syracuseStep 5456159 = 8184239) B8184239
theorem B6136145 : Blo 1615006 6136145 := bstep (se 2 (by rfl) ⟨2301054, by rfl⟩ : syracuseStep 6136145 = 4602109) B4602109
theorem B3637601 : Blo 1615006 3637601 := bstep (se 2 (by rfl) ⟨1364100, by rfl⟩ : syracuseStep 3637601 = 2728201) B2728201
theorem B5177783 : Blo 1615006 5177783 := bstep (se 1 (by rfl) ⟨3883337, by rfl⟩ : syracuseStep 5177783 = 7766675) B7766675
theorem B3637691 : Blo 1615006 3637691 := bstep (se 1 (by rfl) ⟨2728268, by rfl⟩ : syracuseStep 3637691 = 5456537) B5456537
theorem B2425295 : Blo 1615006 2425295 := bstep (se 1 (by rfl) ⟨1818971, by rfl⟩ : syracuseStep 2425295 = 3637943) B3637943
theorem B2425337 : Blo 1615006 2425337 := bstep (se 2 (by rfl) ⟨909501, by rfl⟩ : syracuseStep 2425337 = 1819003) B1819003
theorem B2425439 : Blo 1615006 2425439 := bstep (se 1 (by rfl) ⟨1819079, by rfl⟩ : syracuseStep 2425439 = 3638159) B3638159
theorem B8733359 : Blo 1615006 8733359 := bstep (se 1 (by rfl) ⟨6550019, by rfl⟩ : syracuseStep 8733359 = 13100039) B13100039
theorem B7766927 : Blo 1615006 7766927 := bstep (se 1 (by rfl) ⟨5825195, by rfl⟩ : syracuseStep 7766927 = 11650391) B11650391
theorem B5456807 : Blo 1615006 5456807 := bstep (se 1 (by rfl) ⟨4092605, by rfl⟩ : syracuseStep 5456807 = 8185211) B8185211
theorem B44213273 : Blo 1615006 44213273 := bstep (se 2 (by rfl) ⟨16579977, by rfl⟩ : syracuseStep 44213273 = 33159955) B33159955
theorem B9208889 : Blo 1615006 9208889 := bstep (se 2 (by rfl) ⟨3453333, by rfl⟩ : syracuseStep 9208889 = 6906667) B6906667
theorem B1615055 : Blo 1615006 1615055 := bstep (se 1 (by rfl) ⟨1211291, by rfl⟩ : syracuseStep 1615055 = 2422583) B2422583
theorem B56001779 : Blo 1615006 56001779 := bstep (se 1 (by rfl) ⟨42001334, by rfl⟩ : syracuseStep 56001779 = 84002669) B84002669
theorem B3884395 : Blo 1615006 3884395 := bstep (se 1 (by rfl) ⟨2913296, by rfl⟩ : syracuseStep 3884395 = 5826593) B5826593
theorem B1615259 : Blo 1615006 1615259 := bstep (se 1 (by rfl) ⟨1211444, by rfl⟩ : syracuseStep 1615259 = 2422889) B2422889
theorem B4728239 : Blo 1615006 4728239 := bstep (se 1 (by rfl) ⟨3546179, by rfl⟩ : syracuseStep 4728239 = 7092359) B7092359
theorem B8177111 : Blo 1615006 8177111 := bstep (se 1 (by rfl) ⟨6132833, by rfl⟩ : syracuseStep 8177111 = 12265667) B12265667
theorem B5826131 : Blo 1615006 5826131 := bstep (se 1 (by rfl) ⟨4369598, by rfl⟩ : syracuseStep 5826131 = 8739197) B8739197
theorem B1615471 : Blo 1615006 1615471 := bstep (se 1 (by rfl) ⟨1211603, by rfl⟩ : syracuseStep 1615471 = 2423207) B2423207
theorem B10356335 : Blo 1615006 10356335 := bstep (se 1 (by rfl) ⟨7767251, by rfl⟩ : syracuseStep 10356335 = 15534503) B15534503
theorem B1615527 : Blo 1615006 1615527 := bstep (se 1 (by rfl) ⟨1211645, by rfl⟩ : syracuseStep 1615527 = 2423291) B2423291
theorem B1615611 : Blo 1615006 1615611 := bstep (se 1 (by rfl) ⟨1211708, by rfl⟩ : syracuseStep 1615611 = 2423417) B2423417
theorem B1615647 : Blo 1615006 1615647 := bstep (se 1 (by rfl) ⟨1211735, by rfl⟩ : syracuseStep 1615647 = 2423471) B2423471
theorem B13109053 : Blo 1615006 13109053 := bstep (se 3 (by rfl) ⟨2457947, by rfl⟩ : syracuseStep 13109053 = 4915895) B4915895
theorem B1615679 : Blo 1615006 1615679 := bstep (se 1 (by rfl) ⟨1211759, by rfl⟩ : syracuseStep 1615679 = 2423519) B2423519
theorem B8185697 : Blo 1615006 8185697 := bstep (se 2 (by rfl) ⟨3069636, by rfl⟩ : syracuseStep 8185697 = 6139273) B6139273
theorem B6137801 : Blo 1615006 6137801 := bstep (se 2 (by rfl) ⟨2301675, by rfl⟩ : syracuseStep 6137801 = 4603351) B4603351
theorem B1615855 : Blo 1615006 1615855 := bstep (se 1 (by rfl) ⟨1211891, by rfl⟩ : syracuseStep 1615855 = 2423783) B2423783
theorem B1616027 : Blo 1615006 1616027 := bstep (se 1 (by rfl) ⟨1212020, by rfl⟩ : syracuseStep 1616027 = 2424041) B2424041
theorem B1616063 : Blo 1615006 1616063 := bstep (se 1 (by rfl) ⟨1212047, by rfl⟩ : syracuseStep 1616063 = 2424095) B2424095
theorem B1616175 : Blo 1615006 1616175 := bstep (se 1 (by rfl) ⟨1212131, by rfl⟩ : syracuseStep 1616175 = 2424263) B2424263
theorem B23284169 : Blo 1615006 23284169 := bstep (se 2 (by rfl) ⟨8731563, by rfl⟩ : syracuseStep 23284169 = 17463127) B17463127
theorem B1616411 : Blo 1615006 1616411 := bstep (se 1 (by rfl) ⟨1212308, by rfl⟩ : syracuseStep 1616411 = 2424617) B2424617
theorem B1616415 : Blo 1615006 1616415 := bstep (se 1 (by rfl) ⟨1212311, by rfl⟩ : syracuseStep 1616415 = 2424623) B2424623
theorem B143665757 : Blo 1615006 143665757 := bstep (se 3 (by rfl) ⟨26937329, by rfl⟩ : syracuseStep 143665757 = 53874659) B53874659
theorem B5245751 : Blo 1615006 5245751 := bstep (se 1 (by rfl) ⟨3934313, by rfl⟩ : syracuseStep 5245751 = 7868627) B7868627
theorem B20196155 : Blo 1615006 20196155 := bstep (se 1 (by rfl) ⟨15147116, by rfl⟩ : syracuseStep 20196155 = 30294233) B30294233
theorem B13806395 : Blo 1615006 13806395 := bstep (se 1 (by rfl) ⟨10354796, by rfl⟩ : syracuseStep 13806395 = 20709593) B20709593
theorem B1616731 : Blo 1615006 1616731 := bstep (se 1 (by rfl) ⟨1212548, by rfl⟩ : syracuseStep 1616731 = 2425097) B2425097
theorem B1616799 : Blo 1615006 1616799 := bstep (se 1 (by rfl) ⟨1212599, by rfl⟩ : syracuseStep 1616799 = 2425199) B2425199
theorem B1616943 : Blo 1615006 1616943 := bstep (se 1 (by rfl) ⟨1212707, by rfl⟩ : syracuseStep 1616943 = 2425415) B2425415
theorem B1616967 : Blo 1615006 1616967 := bstep (se 1 (by rfl) ⟨1212725, by rfl⟩ : syracuseStep 1616967 = 2425451) B2425451
theorem B5450975 : Blo 1615006 5450975 := bstep (se 1 (by rfl) ⟨4088231, by rfl⟩ : syracuseStep 5450975 = 8176463) B8176463
theorem B8736169 : Blo 1615006 8736169 := bstep (se 2 (by rfl) ⟨3276063, by rfl⟩ : syracuseStep 8736169 = 6552127) B6552127
theorem B5451191 : Blo 1615006 5451191 := bstep (se 1 (by rfl) ⟨4088393, by rfl⟩ : syracuseStep 5451191 = 8176787) B8176787
theorem B18402875 : Blo 1615006 18402875 := bstep (se 1 (by rfl) ⟨13802156, by rfl⟩ : syracuseStep 18402875 = 27604313) B27604313
theorem B3067465 : Blo 1615006 3067465 := bstep (se 2 (by rfl) ⟨1150299, by rfl⟩ : syracuseStep 3067465 = 2300599) B2300599
theorem B9334367 : Blo 1615006 9334367 := bstep (se 1 (by rfl) ⟨7000775, by rfl⟩ : syracuseStep 9334367 = 14001551) B14001551
theorem B29503109 : Blo 1615006 29503109 := bstep (se 4 (by rfl) ⟨2765916, by rfl⟩ : syracuseStep 29503109 = 5531833) B5531833
theorem B46567061 : Blo 1615006 46567061 := bstep (se 6 (by rfl) ⟨1091415, by rfl⟩ : syracuseStep 46567061 = 2182831) B2182831
theorem B2182951 : Blo 1615006 2182951 := bstep (se 1 (by rfl) ⟨1637213, by rfl⟩ : syracuseStep 2182951 = 3274427) B3274427
theorem B6901625 : Blo 1615006 6901625 := bstep (se 2 (by rfl) ⟨2588109, by rfl⟩ : syracuseStep 6901625 = 5176219) B5176219
theorem B3067769 : Blo 1615006 3067769 := bstep (se 2 (by rfl) ⟨1150413, by rfl⟩ : syracuseStep 3067769 = 2300827) B2300827
theorem B19648403 : Blo 1615006 19648403 := bstep (se 1 (by rfl) ⟨14736302, by rfl⟩ : syracuseStep 19648403 = 29472605) B29472605
theorem B11644879 : Blo 1615006 11644879 := bstep (se 1 (by rfl) ⟨8733659, by rfl⟩ : syracuseStep 11644879 = 17467319) B17467319
theorem B3453239 : Blo 1615006 3453239 := bstep (se 1 (by rfl) ⟨2589929, by rfl⟩ : syracuseStep 3453239 = 5179859) B5179859
theorem B11653703 : Blo 1615006 11653703 := bstep (se 1 (by rfl) ⟨8740277, by rfl⟩ : syracuseStep 11653703 = 17480555) B17480555
theorem B3633767 : Blo 1615006 3633767 := bstep (se 1 (by rfl) ⟨2725325, by rfl⟩ : syracuseStep 3633767 = 5450651) B5450651
theorem B4600583 : Blo 1615006 4600583 := bstep (se 1 (by rfl) ⟨3450437, by rfl⟩ : syracuseStep 4600583 = 6900875) B6900875
theorem B9098009 : Blo 1615006 9098009 := bstep (se 2 (by rfl) ⟨3411753, by rfl⟩ : syracuseStep 9098009 = 6823507) B6823507
theorem B15537041 : Blo 1615006 15537041 := bstep (se 2 (by rfl) ⟨5826390, by rfl⟩ : syracuseStep 15537041 = 11652781) B11652781
theorem B3068923 : Blo 1615006 3068923 := bstep (se 1 (by rfl) ⟨2301692, by rfl⟩ : syracuseStep 3068923 = 4603385) B4603385
theorem B4093001 : Blo 1615006 4093001 := bstep (se 2 (by rfl) ⟨1534875, by rfl⟩ : syracuseStep 4093001 = 3069751) B3069751
theorem B6902891 : Blo 1615006 6902891 := bstep (se 1 (by rfl) ⟨5177168, by rfl⟩ : syracuseStep 6902891 = 10354337) B10354337
theorem B6132955 : Blo 1615006 6132955 := bstep (se 1 (by rfl) ⟨4599716, by rfl⟩ : syracuseStep 6132955 = 9199433) B9199433
theorem B3634451 : Blo 1615006 3634451 := bstep (se 1 (by rfl) ⟨2725838, by rfl⟩ : syracuseStep 3634451 = 5451677) B5451677
theorem B3634523 : Blo 1615006 3634523 := bstep (se 1 (by rfl) ⟨2725892, by rfl⟩ : syracuseStep 3634523 = 5451785) B5451785
theorem B4912481 : Blo 1615006 4912481 := bstep (se 2 (by rfl) ⟨1842180, by rfl⟩ : syracuseStep 4912481 = 3684361) B3684361
theorem B5453243 : Blo 1615006 5453243 := bstep (se 1 (by rfl) ⟨4089932, by rfl⟩ : syracuseStep 5453243 = 8179865) B8179865
theorem B3069409 : Blo 1615006 3069409 := bstep (se 2 (by rfl) ⟨1151028, by rfl⟩ : syracuseStep 3069409 = 2302057) B2302057
theorem B2725447 : Blo 1615006 2725447 := bstep (se 1 (by rfl) ⟨2044085, by rfl⟩ : syracuseStep 2725447 = 4088171) B4088171
theorem B41399909 : Blo 1615006 41399909 := bstep (se 4 (by rfl) ⟨3881241, by rfl⟩ : syracuseStep 41399909 = 7762483) B7762483
theorem B18904709 : Blo 1615006 18904709 := bstep (se 4 (by rfl) ⟨1772316, by rfl⟩ : syracuseStep 18904709 = 3544633) B3544633
theorem B3880619 : Blo 1615006 3880619 := bstep (se 1 (by rfl) ⟨2910464, by rfl⟩ : syracuseStep 3880619 = 5820929) B5820929
theorem B2422523 : Blo 1615006 2422523 := bstep (se 1 (by rfl) ⟨1816892, by rfl⟩ : syracuseStep 2422523 = 3633785) B3633785
theorem B2422559 : Blo 1615006 2422559 := bstep (se 1 (by rfl) ⟨1816919, by rfl⟩ : syracuseStep 2422559 = 3633839) B3633839
theorem B2725663 : Blo 1615006 2725663 := bstep (se 1 (by rfl) ⟨2044247, by rfl⟩ : syracuseStep 2725663 = 4088495) B4088495
theorem B2422607 : Blo 1615006 2422607 := bstep (se 1 (by rfl) ⟨1816955, by rfl⟩ : syracuseStep 2422607 = 3633911) B3633911
theorem B27613061 : Blo 1615006 27613061 := bstep (se 4 (by rfl) ⟨2588724, by rfl⟩ : syracuseStep 27613061 = 5177449) B5177449
theorem B3635081 : Blo 1615006 3635081 := bstep (se 2 (by rfl) ⟨1363155, by rfl⟩ : syracuseStep 3635081 = 2726311) B2726311
theorem B2422727 : Blo 1615006 2422727 := bstep (se 1 (by rfl) ⟨1817045, by rfl⟩ : syracuseStep 2422727 = 3634091) B3634091
theorem B5453783 : Blo 1615006 5453783 := bstep (se 1 (by rfl) ⟨4090337, by rfl⟩ : syracuseStep 5453783 = 8180675) B8180675
theorem B2725879 : Blo 1615006 2725879 := bstep (se 1 (by rfl) ⟨2044409, by rfl⟩ : syracuseStep 2725879 = 4088819) B4088819
theorem B42563663 : Blo 1615006 42563663 := bstep (se 1 (by rfl) ⟨31922747, by rfl⟩ : syracuseStep 42563663 = 63845495) B63845495
theorem B3635297 : Blo 1615006 3635297 := bstep (se 2 (by rfl) ⟨1363236, by rfl⟩ : syracuseStep 3635297 = 2726473) B2726473
theorem B2726183 : Blo 1615006 2726183 := bstep (se 1 (by rfl) ⟨2044637, by rfl⟩ : syracuseStep 2726183 = 4089275) B4089275
theorem B2423081 : Blo 1615006 2423081 := bstep (se 2 (by rfl) ⟨908655, by rfl⟩ : syracuseStep 2423081 = 1817311) B1817311
theorem B2423087 : Blo 1615006 2423087 := bstep (se 1 (by rfl) ⟨1817315, by rfl⟩ : syracuseStep 2423087 = 3634631) B3634631
theorem B5454269 : Blo 1615006 5454269 := bstep (se 3 (by rfl) ⟨1022675, by rfl⟩ : syracuseStep 5454269 = 2045351) B2045351
theorem B2423327 : Blo 1615006 2423327 := bstep (se 1 (by rfl) ⟨1817495, by rfl⟩ : syracuseStep 2423327 = 3634991) B3634991
theorem B3881819 : Blo 1615006 3881819 := bstep (se 1 (by rfl) ⟨2911364, by rfl⟩ : syracuseStep 3881819 = 5822729) B5822729
theorem B8182619 : Blo 1615006 8182619 := bstep (se 1 (by rfl) ⟨6136964, by rfl⟩ : syracuseStep 8182619 = 12273929) B12273929
theorem B5176169 : Blo 1615006 5176169 := bstep (se 2 (by rfl) ⟨1941063, by rfl⟩ : syracuseStep 5176169 = 3882127) B3882127
theorem B13802399 : Blo 1615006 13802399 := bstep (se 1 (by rfl) ⟨10351799, by rfl⟩ : syracuseStep 13802399 = 20703599) B20703599
theorem B6134687 : Blo 1615006 6134687 := bstep (se 1 (by rfl) ⟨4601015, by rfl⟩ : syracuseStep 6134687 = 9202031) B9202031
theorem B2423711 : Blo 1615006 2423711 := bstep (se 1 (by rfl) ⟨1817783, by rfl⟩ : syracuseStep 2423711 = 3635567) B3635567
theorem B5528521 : Blo 1615006 5528521 := bstep (se 2 (by rfl) ⟨2073195, by rfl⟩ : syracuseStep 5528521 = 4146391) B4146391
theorem B2423759 : Blo 1615006 2423759 := bstep (se 1 (by rfl) ⟨1817819, by rfl⟩ : syracuseStep 2423759 = 3635639) B3635639
theorem B2423849 : Blo 1615006 2423849 := bstep (se 2 (by rfl) ⟨908943, by rfl⟩ : syracuseStep 2423849 = 1817887) B1817887
theorem B2423855 : Blo 1615006 2423855 := bstep (se 1 (by rfl) ⟨1817891, by rfl⟩ : syracuseStep 2423855 = 3635783) B3635783
theorem B2726959 : Blo 1615006 2726959 := bstep (se 1 (by rfl) ⟨2045219, by rfl⟩ : syracuseStep 2726959 = 4090439) B4090439
theorem B1817671 : Blo 1615006 1817671 := bstep (se 1 (by rfl) ⟨1363253, by rfl⟩ : syracuseStep 1817671 = 2726507) B2726507
theorem B2423879 : Blo 1615006 2423879 := bstep (se 1 (by rfl) ⟨1817909, by rfl⟩ : syracuseStep 2423879 = 3635819) B3635819
theorem B21576775 : Blo 1615006 21576775 := bstep (se 1 (by rfl) ⟨16182581, by rfl⟩ : syracuseStep 21576775 = 32365163) B32365163
theorem B9829457 : Blo 1615006 9829457 := bstep (se 2 (by rfl) ⟨3686046, by rfl⟩ : syracuseStep 9829457 = 7372093) B7372093
theorem B13810769 : Blo 1615006 13810769 := bstep (se 2 (by rfl) ⟨5179038, by rfl⟩ : syracuseStep 13810769 = 10358077) B10358077
theorem B20716721 : Blo 1615006 20716721 := bstep (se 2 (by rfl) ⟨7768770, by rfl⟩ : syracuseStep 20716721 = 15537541) B15537541
theorem B9329917 : Blo 1615006 9329917 := bstep (se 3 (by rfl) ⟨1749359, by rfl⟩ : syracuseStep 9329917 = 3498719) B3498719
theorem B5455133 : Blo 1615006 5455133 := bstep (se 3 (by rfl) ⟨1022837, by rfl⟩ : syracuseStep 5455133 = 2045675) B2045675
theorem B2424143 : Blo 1615006 2424143 := bstep (se 1 (by rfl) ⟨1818107, by rfl⟩ : syracuseStep 2424143 = 3636215) B3636215
theorem B6905249 : Blo 1615006 6905249 := bstep (se 2 (by rfl) ⟨2589468, by rfl⟩ : syracuseStep 6905249 = 5178937) B5178937
theorem B3636647 : Blo 1615006 3636647 := bstep (se 1 (by rfl) ⟨2727485, by rfl⟩ : syracuseStep 3636647 = 5454971) B5454971
theorem B2424233 : Blo 1615006 2424233 := bstep (se 2 (by rfl) ⟨909087, by rfl⟩ : syracuseStep 2424233 = 1818175) B1818175
theorem B2727337 : Blo 1615006 2727337 := bstep (se 2 (by rfl) ⟨1022751, by rfl⟩ : syracuseStep 2727337 = 2045503) B2045503
theorem B2424383 : Blo 1615006 2424383 := bstep (se 1 (by rfl) ⟨1818287, by rfl⟩ : syracuseStep 2424383 = 3636575) B3636575
theorem B3636827 : Blo 1615006 3636827 := bstep (se 1 (by rfl) ⟨2727620, by rfl⟩ : syracuseStep 3636827 = 5455241) B5455241
theorem B62119547 : Blo 1615006 62119547 := bstep (se 1 (by rfl) ⟨46589660, by rfl⟩ : syracuseStep 62119547 = 93179321) B93179321
theorem B4603625 : Blo 1615006 4603625 := bstep (se 2 (by rfl) ⟨1726359, by rfl⟩ : syracuseStep 4603625 = 3452719) B3452719
theorem B2424647 : Blo 1615006 2424647 := bstep (se 1 (by rfl) ⟨1818485, by rfl⟩ : syracuseStep 2424647 = 3636971) B3636971
theorem B2727803 : Blo 1615006 2727803 := bstep (se 1 (by rfl) ⟨2045852, by rfl⟩ : syracuseStep 2727803 = 4091705) B4091705
theorem B3637115 : Blo 1615006 3637115 := bstep (se 1 (by rfl) ⟨2727836, by rfl⟩ : syracuseStep 3637115 = 5455673) B5455673
theorem B2424731 : Blo 1615006 2424731 := bstep (se 1 (by rfl) ⟨1818548, by rfl⟩ : syracuseStep 2424731 = 3637097) B3637097
theorem B3637439 : Blo 1615006 3637439 := bstep (se 1 (by rfl) ⟨2728079, by rfl⟩ : syracuseStep 3637439 = 5456159) B5456159
theorem B2425067 : Blo 1615006 2425067 := bstep (se 1 (by rfl) ⟨1818800, by rfl⟩ : syracuseStep 2425067 = 3637601) B3637601
theorem B2425127 : Blo 1615006 2425127 := bstep (se 1 (by rfl) ⟨1818845, by rfl⟩ : syracuseStep 2425127 = 3637691) B3637691
theorem B5177951 : Blo 1615006 5177951 := bstep (se 1 (by rfl) ⟨3883463, by rfl⟩ : syracuseStep 5177951 = 7766927) B7766927
theorem B3637871 : Blo 1615006 3637871 := bstep (se 1 (by rfl) ⟨2728403, by rfl⟩ : syracuseStep 3637871 = 5456807) B5456807
theorem B29475515 : Blo 1615006 29475515 := bstep (se 1 (by rfl) ⟨22106636, by rfl⟩ : syracuseStep 29475515 = 44213273) B44213273
theorem B2728667 : Blo 1615006 2728667 := bstep (se 1 (by rfl) ⟨2046500, by rfl⟩ : syracuseStep 2728667 = 4093001) B4093001
theorem B9208637 : Blo 1615006 9208637 := bstep (se 3 (by rfl) ⟨1726619, by rfl⟩ : syracuseStep 9208637 = 3453239) B3453239
theorem B3884087 : Blo 1615006 3884087 := bstep (se 1 (by rfl) ⟨2913065, by rfl⟩ : syracuseStep 3884087 = 5826131) B5826131
theorem B27599939 : Blo 1615006 27599939 := bstep (se 1 (by rfl) ⟨20699954, by rfl⟩ : syracuseStep 27599939 = 41399909) B41399909
theorem B1615015 : Blo 1615006 1615015 := bstep (se 1 (by rfl) ⟨1211261, by rfl⟩ : syracuseStep 1615015 = 2422523) B2422523
theorem B1615039 : Blo 1615006 1615039 := bstep (se 1 (by rfl) ⟨1211279, by rfl⟩ : syracuseStep 1615039 = 2422559) B2422559
theorem B1615071 : Blo 1615006 1615071 := bstep (se 1 (by rfl) ⟨1211303, by rfl⟩ : syracuseStep 1615071 = 2422607) B2422607
theorem B5457131 : Blo 1615006 5457131 := bstep (se 1 (by rfl) ⟨4092848, by rfl⟩ : syracuseStep 5457131 = 8185697) B8185697
theorem B18408707 : Blo 1615006 18408707 := bstep (se 1 (by rfl) ⟨13806530, by rfl⟩ : syracuseStep 18408707 = 27613061) B27613061
theorem B1615151 : Blo 1615006 1615151 := bstep (se 1 (by rfl) ⟨1211363, by rfl⟩ : syracuseStep 1615151 = 2422727) B2422727
theorem B1615387 : Blo 1615006 1615387 := bstep (se 1 (by rfl) ⟨1211540, by rfl⟩ : syracuseStep 1615387 = 2423081) B2423081
theorem B1615391 : Blo 1615006 1615391 := bstep (se 1 (by rfl) ⟨1211543, by rfl⟩ : syracuseStep 1615391 = 2423087) B2423087
theorem B8177273 : Blo 1615006 8177273 := bstep (se 2 (by rfl) ⟨3066477, by rfl⟩ : syracuseStep 8177273 = 6132955) B6132955
theorem B1615551 : Blo 1615006 1615551 := bstep (se 1 (by rfl) ⟨1211663, by rfl⟩ : syracuseStep 1615551 = 2423327) B2423327
theorem B5179193 : Blo 1615006 5179193 := bstep (se 2 (by rfl) ⟨1942197, by rfl⟩ : syracuseStep 5179193 = 3884395) B3884395
theorem B3450779 : Blo 1615006 3450779 := bstep (se 1 (by rfl) ⟨2588084, by rfl⟩ : syracuseStep 3450779 = 5176169) B5176169
theorem B9201599 : Blo 1615006 9201599 := bstep (se 1 (by rfl) ⟨6901199, by rfl⟩ : syracuseStep 9201599 = 13802399) B13802399
theorem B4089791 : Blo 1615006 4089791 := bstep (se 1 (by rfl) ⟨3067343, by rfl⟩ : syracuseStep 4089791 = 6134687) B6134687
theorem B1615807 : Blo 1615006 1615807 := bstep (se 1 (by rfl) ⟨1211855, by rfl⟩ : syracuseStep 1615807 = 2423711) B2423711
theorem B1615839 : Blo 1615006 1615839 := bstep (se 1 (by rfl) ⟨1211879, by rfl⟩ : syracuseStep 1615839 = 2423759) B2423759
theorem B1615899 : Blo 1615006 1615899 := bstep (se 1 (by rfl) ⟨1211924, by rfl⟩ : syracuseStep 1615899 = 2423849) B2423849
theorem B1615903 : Blo 1615006 1615903 := bstep (se 1 (by rfl) ⟨1211927, by rfl⟩ : syracuseStep 1615903 = 2423855) B2423855
theorem B1615919 : Blo 1615006 1615919 := bstep (se 1 (by rfl) ⟨1211939, by rfl⟩ : syracuseStep 1615919 = 2423879) B2423879
theorem B4089953 : Blo 1615006 4089953 := bstep (se 2 (by rfl) ⟨1533732, by rfl⟩ : syracuseStep 4089953 = 3067465) B3067465
theorem B1616095 : Blo 1615006 1616095 := bstep (se 1 (by rfl) ⟨1212071, by rfl⟩ : syracuseStep 1616095 = 2424143) B2424143
theorem B1616155 : Blo 1615006 1616155 := bstep (se 1 (by rfl) ⟨1212116, by rfl⟩ : syracuseStep 1616155 = 2424233) B2424233
theorem B1616255 : Blo 1615006 1616255 := bstep (se 1 (by rfl) ⟨1212191, by rfl⟩ : syracuseStep 1616255 = 2424383) B2424383
theorem B2910601 : Blo 1615006 2910601 := bstep (se 2 (by rfl) ⟨1091475, by rfl⟩ : syracuseStep 2910601 = 2182951) B2182951
theorem B41413031 : Blo 1615006 41413031 := bstep (se 1 (by rfl) ⟨31059773, by rfl⟩ : syracuseStep 41413031 = 62119547) B62119547
theorem B1616431 : Blo 1615006 1616431 := bstep (se 1 (by rfl) ⟨1212323, by rfl⟩ : syracuseStep 1616431 = 2424647) B2424647
theorem B1616487 : Blo 1615006 1616487 := bstep (se 1 (by rfl) ⟨1212365, by rfl⟩ : syracuseStep 1616487 = 2424731) B2424731
theorem B15526505 : Blo 1615006 15526505 := bstep (se 2 (by rfl) ⟨5822439, by rfl⟩ : syracuseStep 15526505 = 11644879) B11644879
theorem B4090763 : Blo 1615006 4090763 := bstep (se 1 (by rfl) ⟨3068072, by rfl⟩ : syracuseStep 4090763 = 6136145) B6136145
theorem B1616863 : Blo 1615006 1616863 := bstep (se 1 (by rfl) ⟨1212647, by rfl⟩ : syracuseStep 1616863 = 2425295) B2425295
theorem B1616891 : Blo 1615006 1616891 := bstep (se 1 (by rfl) ⟨1212668, by rfl⟩ : syracuseStep 1616891 = 2425337) B2425337
theorem B7769135 : Blo 1615006 7769135 := bstep (se 1 (by rfl) ⟨5826851, by rfl⟩ : syracuseStep 7769135 = 11653703) B11653703
theorem B1616959 : Blo 1615006 1616959 := bstep (se 1 (by rfl) ⟨1212719, by rfl⟩ : syracuseStep 1616959 = 2425439) B2425439
theorem B3067055 : Blo 1615006 3067055 := bstep (se 1 (by rfl) ⟨2300291, by rfl⟩ : syracuseStep 3067055 = 4600583) B4600583
theorem B6065339 : Blo 1615006 6065339 := bstep (se 1 (by rfl) ⟨4549004, by rfl⟩ : syracuseStep 6065339 = 9098009) B9098009
theorem B10358027 : Blo 1615006 10358027 := bstep (se 1 (by rfl) ⟨7768520, by rfl⟩ : syracuseStep 10358027 = 15537041) B15537041
theorem B6139259 : Blo 1615006 6139259 := bstep (se 1 (by rfl) ⟨4604444, by rfl⟩ : syracuseStep 6139259 = 9208889) B9208889
theorem B37334519 : Blo 1615006 37334519 := bstep (se 1 (by rfl) ⟨28000889, by rfl⟩ : syracuseStep 37334519 = 56001779) B56001779
theorem B5451407 : Blo 1615006 5451407 := bstep (se 1 (by rfl) ⟨4088555, by rfl⟩ : syracuseStep 5451407 = 8177111) B8177111
theorem B13807421 : Blo 1615006 13807421 := bstep (se 3 (by rfl) ⟨2588891, by rfl⟩ : syracuseStep 13807421 = 5177783) B5177783
theorem B4091867 : Blo 1615006 4091867 := bstep (se 1 (by rfl) ⟨3068900, by rfl⟩ : syracuseStep 4091867 = 6137801) B6137801
theorem B4091897 : Blo 1615006 4091897 := bstep (se 2 (by rfl) ⟨1534461, by rfl⟩ : syracuseStep 4091897 = 3068923) B3068923
theorem B12439889 : Blo 1615006 12439889 := bstep (se 2 (by rfl) ⟨4664958, by rfl⟩ : syracuseStep 12439889 = 9329917) B9329917
theorem B95777171 : Blo 1615006 95777171 := bstep (se 1 (by rfl) ⟨71832878, by rfl⟩ : syracuseStep 95777171 = 143665757) B143665757
theorem B13464103 : Blo 1615006 13464103 := bstep (se 1 (by rfl) ⟨10098077, by rfl⟩ : syracuseStep 13464103 = 20196155) B20196155
theorem B9204263 : Blo 1615006 9204263 := bstep (se 1 (by rfl) ⟨6903197, by rfl⟩ : syracuseStep 9204263 = 13806395) B13806395
theorem B4092545 : Blo 1615006 4092545 := bstep (se 2 (by rfl) ⟨1534704, by rfl⟩ : syracuseStep 4092545 = 3069409) B3069409
theorem B3633929 : Blo 1615006 3633929 := bstep (se 2 (by rfl) ⟨1362723, by rfl⟩ : syracuseStep 3633929 = 2725447) B2725447
theorem B3633983 : Blo 1615006 3633983 := bstep (se 1 (by rfl) ⟨2725487, by rfl⟩ : syracuseStep 3633983 = 5450975) B5450975
theorem B3634127 : Blo 1615006 3634127 := bstep (se 1 (by rfl) ⟨2725595, by rfl⟩ : syracuseStep 3634127 = 5451191) B5451191
theorem B18404333 : Blo 1615006 18404333 := bstep (se 3 (by rfl) ⟨3450812, by rfl⟩ : syracuseStep 18404333 = 6901625) B6901625
theorem B12268583 : Blo 1615006 12268583 := bstep (se 1 (by rfl) ⟨9201437, by rfl⟩ : syracuseStep 12268583 = 18402875) B18402875
theorem B3634217 : Blo 1615006 3634217 := bstep (se 2 (by rfl) ⟨1362831, by rfl⟩ : syracuseStep 3634217 = 2725663) B2725663
theorem B6222911 : Blo 1615006 6222911 := bstep (se 1 (by rfl) ⟨4667183, by rfl⟩ : syracuseStep 6222911 = 9334367) B9334367
theorem B17478737 : Blo 1615006 17478737 := bstep (se 2 (by rfl) ⟨6554526, by rfl⟩ : syracuseStep 17478737 = 13109053) B13109053
theorem B31044707 : Blo 1615006 31044707 := bstep (se 1 (by rfl) ⟨23283530, by rfl⟩ : syracuseStep 31044707 = 46567061) B46567061
theorem B3069083 : Blo 1615006 3069083 := bstep (se 1 (by rfl) ⟨2301812, by rfl⟩ : syracuseStep 3069083 = 4603625) B4603625
theorem B2045179 : Blo 1615006 2045179 := bstep (se 1 (by rfl) ⟨1533884, by rfl⟩ : syracuseStep 2045179 = 3067769) B3067769
theorem B3634505 : Blo 1615006 3634505 := bstep (se 2 (by rfl) ⟨1362939, by rfl⟩ : syracuseStep 3634505 = 2725879) B2725879
theorem B31069615 : Blo 1615006 31069615 := bstep (se 1 (by rfl) ⟨23302211, by rfl⟩ : syracuseStep 31069615 = 46604423) B46604423
theorem B2422511 : Blo 1615006 2422511 := bstep (se 1 (by rfl) ⟨1816883, by rfl⟩ : syracuseStep 2422511 = 3633767) B3633767
theorem B5822239 : Blo 1615006 5822239 := bstep (se 1 (by rfl) ⟨4366679, by rfl⟩ : syracuseStep 5822239 = 8733359) B8733359
theorem B4601927 : Blo 1615006 4601927 := bstep (se 1 (by rfl) ⟨3451445, by rfl⟩ : syracuseStep 4601927 = 6902891) B6902891
theorem B2422967 : Blo 1615006 2422967 := bstep (se 1 (by rfl) ⟨1817225, by rfl⟩ : syracuseStep 2422967 = 3634451) B3634451
theorem B2423015 : Blo 1615006 2423015 := bstep (se 1 (by rfl) ⟨1817261, by rfl⟩ : syracuseStep 2423015 = 3634523) B3634523
theorem B3274987 : Blo 1615006 3274987 := bstep (se 1 (by rfl) ⟨2456240, by rfl⟩ : syracuseStep 3274987 = 4912481) B4912481
theorem B3152159 : Blo 1615006 3152159 := bstep (se 1 (by rfl) ⟨2364119, by rfl⟩ : syracuseStep 3152159 = 4728239) B4728239
theorem B3635495 : Blo 1615006 3635495 := bstep (se 1 (by rfl) ⟨2726621, by rfl⟩ : syracuseStep 3635495 = 5453243) B5453243
theorem B6904223 : Blo 1615006 6904223 := bstep (se 1 (by rfl) ⟨5178167, by rfl⟩ : syracuseStep 6904223 = 10356335) B10356335
theorem B2587079 : Blo 1615006 2587079 := bstep (se 1 (by rfl) ⟨1940309, by rfl⟩ : syracuseStep 2587079 = 3880619) B3880619
theorem B2423387 : Blo 1615006 2423387 := bstep (se 1 (by rfl) ⟨1817540, by rfl⟩ : syracuseStep 2423387 = 3635081) B3635081
theorem B7371361 : Blo 1615006 7371361 := bstep (se 2 (by rfl) ⟨2764260, by rfl⟩ : syracuseStep 7371361 = 5528521) B5528521
theorem B3635855 : Blo 1615006 3635855 := bstep (se 1 (by rfl) ⟨2726891, by rfl⟩ : syracuseStep 3635855 = 5453783) B5453783
theorem B28375775 : Blo 1615006 28375775 := bstep (se 1 (by rfl) ⟨21281831, by rfl⟩ : syracuseStep 28375775 = 42563663) B42563663
theorem B3635945 : Blo 1615006 3635945 := bstep (se 2 (by rfl) ⟨1363479, by rfl⟩ : syracuseStep 3635945 = 2726959) B2726959
theorem B2423531 : Blo 1615006 2423531 := bstep (se 1 (by rfl) ⟨1817648, by rfl⟩ : syracuseStep 2423531 = 3635297) B3635297
theorem B2423561 : Blo 1615006 2423561 := bstep (se 2 (by rfl) ⟨908835, by rfl⟩ : syracuseStep 2423561 = 1817671) B1817671
theorem B28769033 : Blo 1615006 28769033 := bstep (se 2 (by rfl) ⟨10788387, by rfl⟩ : syracuseStep 28769033 = 21576775) B21576775
theorem B1817455 : Blo 1615006 1817455 := bstep (se 1 (by rfl) ⟨1363091, by rfl⟩ : syracuseStep 1817455 = 2726183) B2726183
theorem B3636179 : Blo 1615006 3636179 := bstep (se 1 (by rfl) ⟨2727134, by rfl⟩ : syracuseStep 3636179 = 5454269) B5454269
theorem B15522779 : Blo 1615006 15522779 := bstep (se 1 (by rfl) ⟨11642084, by rfl⟩ : syracuseStep 15522779 = 23284169) B23284169
theorem B50412557 : Blo 1615006 50412557 := bstep (se 3 (by rfl) ⟨9452354, by rfl⟩ : syracuseStep 50412557 = 18904709) B18904709
theorem B3497167 : Blo 1615006 3497167 := bstep (se 1 (by rfl) ⟨2622875, by rfl⟩ : syracuseStep 3497167 = 5245751) B5245751
theorem B11648225 : Blo 1615006 11648225 := bstep (se 2 (by rfl) ⟨4368084, by rfl⟩ : syracuseStep 11648225 = 8736169) B8736169
theorem B3636449 : Blo 1615006 3636449 := bstep (se 2 (by rfl) ⟨1363668, by rfl⟩ : syracuseStep 3636449 = 2727337) B2727337
theorem B2587879 : Blo 1615006 2587879 := bstep (se 1 (by rfl) ⟨1940909, by rfl⟩ : syracuseStep 2587879 = 3881819) B3881819
theorem B5455079 : Blo 1615006 5455079 := bstep (se 1 (by rfl) ⟨4091309, by rfl⟩ : syracuseStep 5455079 = 8182619) B8182619
theorem B6552971 : Blo 1615006 6552971 := bstep (se 1 (by rfl) ⟨4914728, by rfl⟩ : syracuseStep 6552971 = 9829457) B9829457
theorem B9207179 : Blo 1615006 9207179 := bstep (se 1 (by rfl) ⟨6905384, by rfl⟩ : syracuseStep 9207179 = 13810769) B13810769
theorem B13811147 : Blo 1615006 13811147 := bstep (se 1 (by rfl) ⟨10358360, by rfl⟩ : syracuseStep 13811147 = 20716721) B20716721
theorem B3636755 : Blo 1615006 3636755 := bstep (se 1 (by rfl) ⟨2727566, by rfl⟩ : syracuseStep 3636755 = 5455133) B5455133
theorem B4603499 : Blo 1615006 4603499 := bstep (se 1 (by rfl) ⟨3452624, by rfl⟩ : syracuseStep 4603499 = 6905249) B6905249
theorem B2424431 : Blo 1615006 2424431 := bstep (se 1 (by rfl) ⟨1818323, by rfl⟩ : syracuseStep 2424431 = 3636647) B3636647
theorem B2424551 : Blo 1615006 2424551 := bstep (se 1 (by rfl) ⟨1818413, by rfl⟩ : syracuseStep 2424551 = 3636827) B3636827
theorem B19668739 : Blo 1615006 19668739 := bstep (se 1 (by rfl) ⟨14751554, by rfl⟩ : syracuseStep 19668739 = 29503109) B29503109
theorem B1818535 : Blo 1615006 1818535 := bstep (se 1 (by rfl) ⟨1363901, by rfl⟩ : syracuseStep 1818535 = 2727803) B2727803
theorem B2424743 : Blo 1615006 2424743 := bstep (se 1 (by rfl) ⟨1818557, by rfl⟩ : syracuseStep 2424743 = 3637115) B3637115
theorem B13098935 : Blo 1615006 13098935 := bstep (se 1 (by rfl) ⟨9824201, by rfl⟩ : syracuseStep 13098935 = 19648403) B19648403
theorem B2424959 : Blo 1615006 2424959 := bstep (se 1 (by rfl) ⟨1818719, by rfl⟩ : syracuseStep 2424959 = 3637439) B3637439
theorem B20717693 : Blo 1615006 20717693 := bstep (se 3 (by rfl) ⟨3884567, by rfl⟩ : syracuseStep 20717693 = 7769135) B7769135
theorem B4366649 : Blo 1615006 4366649 := bstep (se 2 (by rfl) ⟨1637493, by rfl⟩ : syracuseStep 4366649 = 3274987) B3274987
theorem B6136175 : Blo 1615006 6136175 := bstep (se 1 (by rfl) ⟨4602131, by rfl⟩ : syracuseStep 6136175 = 9204263) B9204263
theorem B2425247 : Blo 1615006 2425247 := bstep (se 1 (by rfl) ⟨1818935, by rfl⟩ : syracuseStep 2425247 = 3637871) B3637871
theorem B2728363 : Blo 1615006 2728363 := bstep (se 1 (by rfl) ⟨2046272, by rfl⟩ : syracuseStep 2728363 = 4092545) B4092545
theorem B1819111 : Blo 1615006 1819111 := bstep (se 1 (by rfl) ⟨1364333, by rfl⟩ : syracuseStep 1819111 = 2728667) B2728667
theorem B2589391 : Blo 1615006 2589391 := bstep (se 1 (by rfl) ⟨1942043, by rfl⟩ : syracuseStep 2589391 = 3884087) B3884087
theorem B18399959 : Blo 1615006 18399959 := bstep (se 1 (by rfl) ⟨13799969, by rfl⟩ : syracuseStep 18399959 = 27599939) B27599939
theorem B3638087 : Blo 1615006 3638087 := bstep (se 1 (by rfl) ⟨2728565, by rfl⟩ : syracuseStep 3638087 = 5457131) B5457131
theorem B12272471 : Blo 1615006 12272471 := bstep (se 1 (by rfl) ⟨9204353, by rfl⟩ : syracuseStep 12272471 = 18408707) B18408707
theorem B1615007 : Blo 1615006 1615007 := bstep (se 1 (by rfl) ⟨1211255, by rfl⟩ : syracuseStep 1615007 = 2422511) B2422511
theorem B6898877 : Blo 1615006 6898877 := bstep (se 3 (by rfl) ⟨1293539, by rfl⟩ : syracuseStep 6898877 = 2587079) B2587079
theorem B1615311 : Blo 1615006 1615311 := bstep (se 1 (by rfl) ⟨1211483, by rfl⟩ : syracuseStep 1615311 = 2422967) B2422967
theorem B1615343 : Blo 1615006 1615343 := bstep (se 1 (by rfl) ⟨1211507, by rfl⟩ : syracuseStep 1615343 = 2423015) B2423015
theorem B4662889 : Blo 1615006 4662889 := bstep (se 2 (by rfl) ⟨1748583, by rfl⟩ : syracuseStep 4662889 = 3497167) B3497167
theorem B27608687 : Blo 1615006 27608687 := bstep (se 1 (by rfl) ⟨20706515, by rfl⟩ : syracuseStep 27608687 = 41413031) B41413031
theorem B1615591 : Blo 1615006 1615591 := bstep (se 1 (by rfl) ⟨1211693, by rfl⟩ : syracuseStep 1615591 = 2423387) B2423387
theorem B18917183 : Blo 1615006 18917183 := bstep (se 1 (by rfl) ⟨14187887, by rfl⟩ : syracuseStep 18917183 = 28375775) B28375775
theorem B1615687 : Blo 1615006 1615687 := bstep (se 1 (by rfl) ⟨1211765, by rfl⟩ : syracuseStep 1615687 = 2423531) B2423531
theorem B1615707 : Blo 1615006 1615707 := bstep (se 1 (by rfl) ⟨1211780, by rfl⟩ : syracuseStep 1615707 = 2423561) B2423561
theorem B19179355 : Blo 1615006 19179355 := bstep (se 1 (by rfl) ⟨14384516, by rfl⟩ : syracuseStep 19179355 = 28769033) B28769033
theorem B10348519 : Blo 1615006 10348519 := bstep (se 1 (by rfl) ⟨7761389, by rfl⟩ : syracuseStep 10348519 = 15522779) B15522779
theorem B4368647 : Blo 1615006 4368647 := bstep (se 1 (by rfl) ⟨3276485, by rfl⟩ : syracuseStep 4368647 = 6552971) B6552971
theorem B6138119 : Blo 1615006 6138119 := bstep (se 1 (by rfl) ⟨4603589, by rfl⟩ : syracuseStep 6138119 = 9207179) B9207179
theorem B24889679 : Blo 1615006 24889679 := bstep (se 1 (by rfl) ⟨18667259, by rfl⟩ : syracuseStep 24889679 = 37334519) B37334519
theorem B26224985 : Blo 1615006 26224985 := bstep (se 2 (by rfl) ⟨9834369, by rfl⟩ : syracuseStep 26224985 = 19668739) B19668739
theorem B1616287 : Blo 1615006 1616287 := bstep (se 1 (by rfl) ⟨1212215, by rfl⟩ : syracuseStep 1616287 = 2424431) B2424431
theorem B1616367 : Blo 1615006 1616367 := bstep (se 1 (by rfl) ⟨1212275, by rfl⟩ : syracuseStep 1616367 = 2424551) B2424551
theorem B1616495 : Blo 1615006 1616495 := bstep (se 1 (by rfl) ⟨1212371, by rfl⟩ : syracuseStep 1616495 = 2424743) B2424743
theorem B1616711 : Blo 1615006 1616711 := bstep (se 1 (by rfl) ⟨1212533, by rfl⟩ : syracuseStep 1616711 = 2425067) B2425067
theorem B1616751 : Blo 1615006 1616751 := bstep (se 1 (by rfl) ⟨1212563, by rfl⟩ : syracuseStep 1616751 = 2425127) B2425127
theorem B8293259 : Blo 1615006 8293259 := bstep (se 1 (by rfl) ⟨6219944, by rfl⟩ : syracuseStep 8293259 = 12439889) B12439889
theorem B63851447 : Blo 1615006 63851447 := bstep (se 1 (by rfl) ⟨47888585, by rfl⟩ : syracuseStep 63851447 = 95777171) B95777171
theorem B33623029 : Blo 1615006 33623029 := bstep (se 5 (by rfl) ⟨1576079, by rfl⟩ : syracuseStep 33623029 = 3152159) B3152159
theorem B3451967 : Blo 1615006 3451967 := bstep (se 1 (by rfl) ⟨2588975, by rfl⟩ : syracuseStep 3451967 = 5177951) B5177951
theorem B16174237 : Blo 1615006 16174237 := bstep (se 3 (by rfl) ⟨3032669, by rfl⟩ : syracuseStep 16174237 = 6065339) B6065339
theorem B6139091 : Blo 1615006 6139091 := bstep (se 1 (by rfl) ⟨4604318, by rfl⟩ : syracuseStep 6139091 = 9208637) B9208637
theorem B2727931 : Blo 1615006 2727931 := bstep (se 1 (by rfl) ⟨2045948, by rfl⟩ : syracuseStep 2727931 = 4091897) B4091897
theorem B8179055 : Blo 1615006 8179055 := bstep (se 1 (by rfl) ⟨6134291, by rfl⟩ : syracuseStep 8179055 = 12268583) B12268583
theorem B17952137 : Blo 1615006 17952137 := bstep (se 2 (by rfl) ⟨6732051, by rfl⟩ : syracuseStep 17952137 = 13464103) B13464103
theorem B11652491 : Blo 1615006 11652491 := bstep (se 1 (by rfl) ⟨8739368, by rfl⟩ : syracuseStep 11652491 = 17478737) B17478737
theorem B20696471 : Blo 1615006 20696471 := bstep (se 1 (by rfl) ⟨15522353, by rfl⟩ : syracuseStep 20696471 = 31044707) B31044707
theorem B5451515 : Blo 1615006 5451515 := bstep (se 1 (by rfl) ⟨4088636, by rfl⟩ : syracuseStep 5451515 = 8177273) B8177273
theorem B3452795 : Blo 1615006 3452795 := bstep (se 1 (by rfl) ⟨2589596, by rfl⟩ : syracuseStep 3452795 = 5179193) B5179193
theorem B3067951 : Blo 1615006 3067951 := bstep (se 1 (by rfl) ⟨2300963, by rfl⟩ : syracuseStep 3067951 = 4601927) B4601927
theorem B10351003 : Blo 1615006 10351003 := bstep (se 1 (by rfl) ⟨7763252, by rfl⟩ : syracuseStep 10351003 = 15526505) B15526505
theorem B33608371 : Blo 1615006 33608371 := bstep (se 1 (by rfl) ⟨25206278, by rfl⟩ : syracuseStep 33608371 = 50412557) B50412557
theorem B2044703 : Blo 1615006 2044703 := bstep (se 1 (by rfl) ⟨1533527, by rfl⟩ : syracuseStep 2044703 = 3067055) B3067055
theorem B4092839 : Blo 1615006 4092839 := bstep (se 1 (by rfl) ⟨3069629, by rfl⟩ : syracuseStep 4092839 = 6139259) B6139259
theorem B7762985 : Blo 1615006 7762985 := bstep (se 2 (by rfl) ⟨2911119, by rfl⟩ : syracuseStep 7762985 = 5822239) B5822239
theorem B3068999 : Blo 1615006 3068999 := bstep (se 1 (by rfl) ⟨2301749, by rfl⟩ : syracuseStep 3068999 = 4603499) B4603499
theorem B3634271 : Blo 1615006 3634271 := bstep (se 1 (by rfl) ⟨2725703, by rfl⟩ : syracuseStep 3634271 = 5451407) B5451407
theorem B9204947 : Blo 1615006 9204947 := bstep (se 1 (by rfl) ⟨6903710, by rfl⟩ : syracuseStep 9204947 = 13807421) B13807421
theorem B16594429 : Blo 1615006 16594429 := bstep (se 3 (by rfl) ⟨3111455, by rfl⟩ : syracuseStep 16594429 = 6222911) B6222911
theorem B2422619 : Blo 1615006 2422619 := bstep (se 1 (by rfl) ⟨1816964, by rfl⟩ : syracuseStep 2422619 = 3633929) B3633929
theorem B3880801 : Blo 1615006 3880801 := bstep (se 2 (by rfl) ⟨1455300, by rfl⟩ : syracuseStep 3880801 = 2910601) B2910601
theorem B2422655 : Blo 1615006 2422655 := bstep (se 1 (by rfl) ⟨1816991, by rfl⟩ : syracuseStep 2422655 = 3633983) B3633983
theorem B2422751 : Blo 1615006 2422751 := bstep (se 1 (by rfl) ⟨1817063, by rfl⟩ : syracuseStep 2422751 = 3634127) B3634127
theorem B12269555 : Blo 1615006 12269555 := bstep (se 1 (by rfl) ⟨9202166, by rfl⟩ : syracuseStep 12269555 = 18404333) B18404333
theorem B2422811 : Blo 1615006 2422811 := bstep (se 1 (by rfl) ⟨1817108, by rfl⟩ : syracuseStep 2422811 = 3634217) B3634217
theorem B2046055 : Blo 1615006 2046055 := bstep (se 1 (by rfl) ⟨1534541, by rfl⟩ : syracuseStep 2046055 = 3069083) B3069083
theorem B9828481 : Blo 1615006 9828481 := bstep (se 2 (by rfl) ⟨3685680, by rfl⟩ : syracuseStep 9828481 = 7371361) B7371361
theorem B2423003 : Blo 1615006 2423003 := bstep (se 1 (by rfl) ⟨1817252, by rfl⟩ : syracuseStep 2423003 = 3634505) B3634505
theorem B2423273 : Blo 1615006 2423273 := bstep (se 2 (by rfl) ⟨908727, by rfl⟩ : syracuseStep 2423273 = 1817455) B1817455
theorem B13802021 : Blo 1615006 13802021 := bstep (se 4 (by rfl) ⟨1293939, by rfl⟩ : syracuseStep 13802021 = 2587879) B2587879
theorem B2300519 : Blo 1615006 2300519 := bstep (se 1 (by rfl) ⟨1725389, by rfl⟩ : syracuseStep 2300519 = 3450779) B3450779
theorem B6134399 : Blo 1615006 6134399 := bstep (se 1 (by rfl) ⟨4600799, by rfl⟩ : syracuseStep 6134399 = 9201599) B9201599
theorem B2726527 : Blo 1615006 2726527 := bstep (se 1 (by rfl) ⟨2044895, by rfl⟩ : syracuseStep 2726527 = 4089791) B4089791
theorem B2726635 : Blo 1615006 2726635 := bstep (se 1 (by rfl) ⟨2044976, by rfl⟩ : syracuseStep 2726635 = 4089953) B4089953
theorem B2423663 : Blo 1615006 2423663 := bstep (se 1 (by rfl) ⟨1817747, by rfl⟩ : syracuseStep 2423663 = 3635495) B3635495
theorem B4602815 : Blo 1615006 4602815 := bstep (se 1 (by rfl) ⟨3452111, by rfl⟩ : syracuseStep 4602815 = 6904223) B6904223
theorem B2726905 : Blo 1615006 2726905 := bstep (se 2 (by rfl) ⟨1022589, by rfl⟩ : syracuseStep 2726905 = 2045179) B2045179
theorem B2423903 : Blo 1615006 2423903 := bstep (se 1 (by rfl) ⟨1817927, by rfl⟩ : syracuseStep 2423903 = 3635855) B3635855
theorem B2423963 : Blo 1615006 2423963 := bstep (se 1 (by rfl) ⟨1817972, by rfl⟩ : syracuseStep 2423963 = 3635945) B3635945
theorem B78601373 : Blo 1615006 78601373 := bstep (se 3 (by rfl) ⟨14737757, by rfl⟩ : syracuseStep 78601373 = 29475515) B29475515
theorem B41426153 : Blo 1615006 41426153 := bstep (se 2 (by rfl) ⟨15534807, by rfl⟩ : syracuseStep 41426153 = 31069615) B31069615
theorem B2727175 : Blo 1615006 2727175 := bstep (se 1 (by rfl) ⟨2045381, by rfl⟩ : syracuseStep 2727175 = 4090763) B4090763
theorem B2424119 : Blo 1615006 2424119 := bstep (se 1 (by rfl) ⟨1818089, by rfl⟩ : syracuseStep 2424119 = 3636179) B3636179
theorem B7765483 : Blo 1615006 7765483 := bstep (se 1 (by rfl) ⟨5824112, by rfl⟩ : syracuseStep 7765483 = 11648225) B11648225
theorem B2424299 : Blo 1615006 2424299 := bstep (se 1 (by rfl) ⟨1818224, by rfl⟩ : syracuseStep 2424299 = 3636449) B3636449
theorem B3636719 : Blo 1615006 3636719 := bstep (se 1 (by rfl) ⟨2727539, by rfl⟩ : syracuseStep 3636719 = 5455079) B5455079
theorem B6905351 : Blo 1615006 6905351 := bstep (se 1 (by rfl) ⟨5179013, by rfl⟩ : syracuseStep 6905351 = 10358027) B10358027
theorem B9207431 : Blo 1615006 9207431 := bstep (se 1 (by rfl) ⟨6905573, by rfl⟩ : syracuseStep 9207431 = 13811147) B13811147
theorem B2424503 : Blo 1615006 2424503 := bstep (se 1 (by rfl) ⟨1818377, by rfl⟩ : syracuseStep 2424503 = 3636755) B3636755
theorem B2424713 : Blo 1615006 2424713 := bstep (se 2 (by rfl) ⟨909267, by rfl⟩ : syracuseStep 2424713 = 1818535) B1818535
theorem B8732623 : Blo 1615006 8732623 := bstep (se 1 (by rfl) ⟨6549467, by rfl⟩ : syracuseStep 8732623 = 13098935) B13098935
theorem B2727911 : Blo 1615006 2727911 := bstep (se 1 (by rfl) ⟨2045933, by rfl⟩ : syracuseStep 2727911 = 4091867) B4091867
theorem B13811795 : Blo 1615006 13811795 := bstep (se 1 (by rfl) ⟨10358846, by rfl⟩ : syracuseStep 13811795 = 20717693) B20717693
theorem B2728073 : Blo 1615006 2728073 := bstep (se 2 (by rfl) ⟨1023027, by rfl⟩ : syracuseStep 2728073 = 2046055) B2046055
theorem B2425391 : Blo 1615006 2425391 := bstep (se 1 (by rfl) ⟨1819043, by rfl⟩ : syracuseStep 2425391 = 3638087) B3638087
theorem B3637817 : Blo 1615006 3637817 := bstep (se 2 (by rfl) ⟨1364181, by rfl⟩ : syracuseStep 3637817 = 2728363) B2728363
theorem B2728559 : Blo 1615006 2728559 := bstep (se 1 (by rfl) ⟨2046419, by rfl⟩ : syracuseStep 2728559 = 4092839) B4092839
theorem B2425481 : Blo 1615006 2425481 := bstep (se 2 (by rfl) ⟨909555, by rfl⟩ : syracuseStep 2425481 = 1819111) B1819111
theorem B6136631 : Blo 1615006 6136631 := bstep (se 1 (by rfl) ⟨4602473, by rfl⟩ : syracuseStep 6136631 = 9204947) B9204947
theorem B44811161 : Blo 1615006 44811161 := bstep (se 2 (by rfl) ⟨16804185, by rfl⟩ : syracuseStep 44811161 = 33608371) B33608371
theorem B1615079 : Blo 1615006 1615079 := bstep (se 1 (by rfl) ⟨1211309, by rfl⟩ : syracuseStep 1615079 = 2422619) B2422619
theorem B1615103 : Blo 1615006 1615103 := bstep (se 1 (by rfl) ⟨1211327, by rfl⟩ : syracuseStep 1615103 = 2422655) B2422655
theorem B1615167 : Blo 1615006 1615167 := bstep (se 1 (by rfl) ⟨1211375, by rfl⟩ : syracuseStep 1615167 = 2422751) B2422751
theorem B1615207 : Blo 1615006 1615207 := bstep (se 1 (by rfl) ⟨1211405, by rfl⟩ : syracuseStep 1615207 = 2422811) B2422811
theorem B1615335 : Blo 1615006 1615335 := bstep (se 1 (by rfl) ⟨1211501, by rfl⟩ : syracuseStep 1615335 = 2423003) B2423003
theorem B17483323 : Blo 1615006 17483323 := bstep (se 1 (by rfl) ⟨13112492, by rfl⟩ : syracuseStep 17483323 = 26224985) B26224985
theorem B1615515 : Blo 1615006 1615515 := bstep (se 1 (by rfl) ⟨1211636, by rfl⟩ : syracuseStep 1615515 = 2423273) B2423273
theorem B9201347 : Blo 1615006 9201347 := bstep (se 1 (by rfl) ⟨6901010, by rfl⟩ : syracuseStep 9201347 = 13802021) B13802021
theorem B4089599 : Blo 1615006 4089599 := bstep (se 1 (by rfl) ⟨3067199, by rfl⟩ : syracuseStep 4089599 = 6134399) B6134399
theorem B1615775 : Blo 1615006 1615775 := bstep (se 1 (by rfl) ⟨1211831, by rfl⟩ : syracuseStep 1615775 = 2423663) B2423663
theorem B1615935 : Blo 1615006 1615935 := bstep (se 1 (by rfl) ⟨1211951, by rfl⟩ : syracuseStep 1615935 = 2423903) B2423903
theorem B1615975 : Blo 1615006 1615975 := bstep (se 1 (by rfl) ⟨1211981, by rfl⟩ : syracuseStep 1615975 = 2423963) B2423963
theorem B27617435 : Blo 1615006 27617435 := bstep (se 1 (by rfl) ⟨20713076, by rfl⟩ : syracuseStep 27617435 = 41426153) B41426153
theorem B1616079 : Blo 1615006 1616079 := bstep (se 1 (by rfl) ⟨1212059, by rfl⟩ : syracuseStep 1616079 = 2424119) B2424119
theorem B7768327 : Blo 1615006 7768327 := bstep (se 1 (by rfl) ⟨5826245, by rfl⟩ : syracuseStep 7768327 = 11652491) B11652491
theorem B13797647 : Blo 1615006 13797647 := bstep (se 1 (by rfl) ⟨10348235, by rfl⟩ : syracuseStep 13797647 = 20696471) B20696471
theorem B1616199 : Blo 1615006 1616199 := bstep (se 1 (by rfl) ⟨1212149, by rfl⟩ : syracuseStep 1616199 = 2424299) B2424299
theorem B6138287 : Blo 1615006 6138287 := bstep (se 1 (by rfl) ⟨4603715, by rfl⟩ : syracuseStep 6138287 = 9207431) B9207431
theorem B1616335 : Blo 1615006 1616335 := bstep (se 1 (by rfl) ⟨1212251, by rfl⟩ : syracuseStep 1616335 = 2424503) B2424503
theorem B1616475 : Blo 1615006 1616475 := bstep (se 1 (by rfl) ⟨1212356, by rfl⟩ : syracuseStep 1616475 = 2424713) B2424713
theorem B11643497 : Blo 1615006 11643497 := bstep (se 2 (by rfl) ⟨4366311, by rfl⟩ : syracuseStep 11643497 = 8732623) B8732623
theorem B13798025 : Blo 1615006 13798025 := bstep (se 2 (by rfl) ⟨5174259, by rfl⟩ : syracuseStep 13798025 = 10348519) B10348519
theorem B4090601 : Blo 1615006 4090601 := bstep (se 2 (by rfl) ⟨1533975, by rfl⟩ : syracuseStep 4090601 = 3067951) B3067951
theorem B1616639 : Blo 1615006 1616639 := bstep (se 1 (by rfl) ⟨1212479, by rfl⟩ : syracuseStep 1616639 = 2424959) B2424959
theorem B2911099 : Blo 1615006 2911099 := bstep (se 1 (by rfl) ⟨2183324, by rfl⟩ : syracuseStep 2911099 = 4366649) B4366649
theorem B4090783 : Blo 1615006 4090783 := bstep (se 1 (by rfl) ⟨3068087, by rfl⟩ : syracuseStep 4090783 = 6136175) B6136175
theorem B1616831 : Blo 1615006 1616831 := bstep (se 1 (by rfl) ⟨1212623, by rfl⟩ : syracuseStep 1616831 = 2425247) B2425247
theorem B12266639 : Blo 1615006 12266639 := bstep (se 1 (by rfl) ⟨9199979, by rfl⟩ : syracuseStep 12266639 = 18399959) B18399959
theorem B4599251 : Blo 1615006 4599251 := bstep (se 1 (by rfl) ⟨3449438, by rfl⟩ : syracuseStep 4599251 = 6898877) B6898877
theorem B44830705 : Blo 1615006 44830705 := bstep (se 2 (by rfl) ⟨16811514, by rfl⟩ : syracuseStep 44830705 = 33623029) B33623029
theorem B8179703 : Blo 1615006 8179703 := bstep (se 1 (by rfl) ⟨6134777, by rfl⟩ : syracuseStep 8179703 = 12269555) B12269555
theorem B2912431 : Blo 1615006 2912431 := bstep (se 1 (by rfl) ⟨2184323, by rfl⟩ : syracuseStep 2912431 = 4368647) B4368647
theorem B4092079 : Blo 1615006 4092079 := bstep (se 1 (by rfl) ⟨3069059, by rfl⟩ : syracuseStep 4092079 = 6138119) B6138119
theorem B21565649 : Blo 1615006 21565649 := bstep (se 2 (by rfl) ⟨8087118, by rfl⟩ : syracuseStep 21565649 = 16174237) B16174237
theorem B16593119 : Blo 1615006 16593119 := bstep (se 1 (by rfl) ⟨12444839, by rfl⟩ : syracuseStep 16593119 = 24889679) B24889679
theorem B3068543 : Blo 1615006 3068543 := bstep (se 1 (by rfl) ⟨2301407, by rfl⟩ : syracuseStep 3068543 = 4602815) B4602815
theorem B5452541 : Blo 1615006 5452541 := bstep (se 3 (by rfl) ⟨1022351, by rfl⟩ : syracuseStep 5452541 = 2044703) B2044703
theorem B52400915 : Blo 1615006 52400915 := bstep (se 1 (by rfl) ⟨39300686, by rfl⟩ : syracuseStep 52400915 = 78601373) B78601373
theorem B4092727 : Blo 1615006 4092727 := bstep (se 1 (by rfl) ⟨3069545, by rfl⟩ : syracuseStep 4092727 = 6139091) B6139091
theorem B5452703 : Blo 1615006 5452703 := bstep (se 1 (by rfl) ⟨4089527, by rfl⟩ : syracuseStep 5452703 = 8179055) B8179055
theorem B25572473 : Blo 1615006 25572473 := bstep (se 2 (by rfl) ⟨9589677, by rfl⟩ : syracuseStep 25572473 = 19179355) B19179355
theorem B5174401 : Blo 1615006 5174401 := bstep (se 2 (by rfl) ⟨1940400, by rfl⟩ : syracuseStep 5174401 = 3880801) B3880801
theorem B3634343 : Blo 1615006 3634343 := bstep (se 1 (by rfl) ⟨2725757, by rfl⟩ : syracuseStep 3634343 = 5451515) B5451515
theorem B13104641 : Blo 1615006 13104641 := bstep (se 2 (by rfl) ⟨4914240, by rfl⟩ : syracuseStep 13104641 = 9828481) B9828481
theorem B13801337 : Blo 1615006 13801337 := bstep (se 2 (by rfl) ⟨5175501, by rfl⟩ : syracuseStep 13801337 = 10351003) B10351003
theorem B8181647 : Blo 1615006 8181647 := bstep (se 1 (by rfl) ⟨6136235, by rfl⟩ : syracuseStep 8181647 = 12272471) B12272471
theorem B5175323 : Blo 1615006 5175323 := bstep (se 1 (by rfl) ⟨3881492, by rfl⟩ : syracuseStep 5175323 = 7762985) B7762985
theorem B2045999 : Blo 1615006 2045999 := bstep (se 1 (by rfl) ⟨1534499, by rfl⟩ : syracuseStep 2045999 = 3068999) B3068999
theorem B2422847 : Blo 1615006 2422847 := bstep (se 1 (by rfl) ⟨1817135, by rfl⟩ : syracuseStep 2422847 = 3634271) B3634271
theorem B3635369 : Blo 1615006 3635369 := bstep (se 2 (by rfl) ⟨1363263, by rfl⟩ : syracuseStep 3635369 = 2726527) B2726527
theorem B3635513 : Blo 1615006 3635513 := bstep (se 2 (by rfl) ⟨1363317, by rfl⟩ : syracuseStep 3635513 = 2726635) B2726635
theorem B18405791 : Blo 1615006 18405791 := bstep (se 1 (by rfl) ⟨13804343, by rfl⟩ : syracuseStep 18405791 = 27608687) B27608687
theorem B13810085 : Blo 1615006 13810085 := bstep (se 4 (by rfl) ⟨1294695, by rfl⟩ : syracuseStep 13810085 = 2589391) B2589391
theorem B3635873 : Blo 1615006 3635873 := bstep (se 2 (by rfl) ⟨1363452, by rfl⟩ : syracuseStep 3635873 = 2726905) B2726905
theorem B6134717 : Blo 1615006 6134717 := bstep (se 3 (by rfl) ⟨1150259, by rfl⟩ : syracuseStep 6134717 = 2300519) B2300519
theorem B3636233 : Blo 1615006 3636233 := bstep (se 2 (by rfl) ⟨1363587, by rfl⟩ : syracuseStep 3636233 = 2727175) B2727175
theorem B5528839 : Blo 1615006 5528839 := bstep (se 1 (by rfl) ⟨4146629, by rfl⟩ : syracuseStep 5528839 = 8293259) B8293259
theorem B10353977 : Blo 1615006 10353977 := bstep (se 2 (by rfl) ⟨3882741, by rfl⟩ : syracuseStep 10353977 = 7765483) B7765483
theorem B22125905 : Blo 1615006 22125905 := bstep (se 2 (by rfl) ⟨8297214, by rfl⟩ : syracuseStep 22125905 = 16594429) B16594429
theorem B2301311 : Blo 1615006 2301311 := bstep (se 1 (by rfl) ⟨1725983, by rfl⟩ : syracuseStep 2301311 = 3451967) B3451967
theorem B50445821 : Blo 1615006 50445821 := bstep (se 3 (by rfl) ⟨9458591, by rfl⟩ : syracuseStep 50445821 = 18917183) B18917183
theorem B99474965 : Blo 1615006 99474965 := bstep (se 6 (by rfl) ⟨2331444, by rfl⟩ : syracuseStep 99474965 = 4662889) B4662889
theorem B11968091 : Blo 1615006 11968091 := bstep (se 1 (by rfl) ⟨8976068, by rfl⟩ : syracuseStep 11968091 = 17952137) B17952137
theorem B2424479 : Blo 1615006 2424479 := bstep (se 1 (by rfl) ⟨1818359, by rfl⟩ : syracuseStep 2424479 = 3636719) B3636719
theorem B4603567 : Blo 1615006 4603567 := bstep (se 1 (by rfl) ⟨3452675, by rfl⟩ : syracuseStep 4603567 = 6905351) B6905351
theorem B170270525 : Blo 1615006 170270525 := bstep (se 3 (by rfl) ⟨31925723, by rfl⟩ : syracuseStep 170270525 = 63851447) B63851447
theorem B2301863 : Blo 1615006 2301863 := bstep (se 1 (by rfl) ⟨1726397, by rfl⟩ : syracuseStep 2301863 = 3452795) B3452795
theorem B1818607 : Blo 1615006 1818607 := bstep (se 1 (by rfl) ⟨1363955, by rfl⟩ : syracuseStep 1818607 = 2727911) B2727911
theorem B3637241 : Blo 1615006 3637241 := bstep (se 2 (by rfl) ⟨1363965, by rfl⟩ : syracuseStep 3637241 = 2727931) B2727931
theorem B9207863 : Blo 1615006 9207863 := bstep (se 1 (by rfl) ⟨6905897, by rfl⟩ : syracuseStep 9207863 = 13811795) B13811795
theorem B1818715 : Blo 1615006 1818715 := bstep (se 1 (by rfl) ⟨1364036, by rfl⟩ : syracuseStep 1818715 = 2728073) B2728073
theorem B5455997 : Blo 1615006 5455997 := bstep (se 3 (by rfl) ⟨1022999, by rfl⟩ : syracuseStep 5455997 = 2045999) B2045999
theorem B14377099 : Blo 1615006 14377099 := bstep (se 1 (by rfl) ⟨10782824, by rfl⟩ : syracuseStep 14377099 = 21565649) B21565649
theorem B3883241 : Blo 1615006 3883241 := bstep (se 2 (by rfl) ⟨1456215, by rfl⟩ : syracuseStep 3883241 = 2912431) B2912431
theorem B5456105 : Blo 1615006 5456105 := bstep (se 2 (by rfl) ⟨2046039, by rfl⟩ : syracuseStep 5456105 = 4092079) B4092079
theorem B2425211 : Blo 1615006 2425211 := bstep (se 1 (by rfl) ⟨1818908, by rfl⟩ : syracuseStep 2425211 = 3637817) B3637817
theorem B1819039 : Blo 1615006 1819039 := bstep (se 1 (by rfl) ⟨1364279, by rfl⟩ : syracuseStep 1819039 = 2728559) B2728559
theorem B17048315 : Blo 1615006 17048315 := bstep (se 1 (by rfl) ⟨12786236, by rfl⟩ : syracuseStep 17048315 = 25572473) B25572473
theorem B6136829 : Blo 1615006 6136829 := bstep (se 3 (by rfl) ⟨1150655, by rfl⟩ : syracuseStep 6136829 = 2301311) B2301311
theorem B5456969 : Blo 1615006 5456969 := bstep (se 2 (by rfl) ⟨2046363, by rfl⟩ : syracuseStep 5456969 = 4092727) B4092727
theorem B9200891 : Blo 1615006 9200891 := bstep (se 1 (by rfl) ⟨6900668, by rfl⟩ : syracuseStep 9200891 = 13801337) B13801337
theorem B3450215 : Blo 1615006 3450215 := bstep (se 1 (by rfl) ⟨2587661, by rfl⟩ : syracuseStep 3450215 = 5175323) B5175323
theorem B1615231 : Blo 1615006 1615231 := bstep (se 1 (by rfl) ⟨1211423, by rfl⟩ : syracuseStep 1615231 = 2422847) B2422847
theorem B6899201 : Blo 1615006 6899201 := bstep (se 2 (by rfl) ⟨2587200, by rfl⟩ : syracuseStep 6899201 = 5174401) B5174401
theorem B4089811 : Blo 1615006 4089811 := bstep (se 1 (by rfl) ⟨3067358, by rfl⟩ : syracuseStep 4089811 = 6134717) B6134717
theorem B8177759 : Blo 1615006 8177759 := bstep (se 1 (by rfl) ⟨6133319, by rfl⟩ : syracuseStep 8177759 = 12266639) B12266639
theorem B6138089 : Blo 1615006 6138089 := bstep (se 2 (by rfl) ⟨2301783, by rfl⟩ : syracuseStep 6138089 = 4603567) B4603567
theorem B3066167 : Blo 1615006 3066167 := bstep (se 1 (by rfl) ⟨2299625, by rfl⟩ : syracuseStep 3066167 = 4599251) B4599251
theorem B33630547 : Blo 1615006 33630547 := bstep (se 1 (by rfl) ⟨25222910, by rfl⟩ : syracuseStep 33630547 = 50445821) B50445821
theorem B66316643 : Blo 1615006 66316643 := bstep (se 1 (by rfl) ⟨49737482, by rfl⟩ : syracuseStep 66316643 = 99474965) B99474965
theorem B6138301 : Blo 1615006 6138301 := bstep (se 3 (by rfl) ⟨1150931, by rfl⟩ : syracuseStep 6138301 = 2301863) B2301863
theorem B1616319 : Blo 1615006 1616319 := bstep (se 1 (by rfl) ⟨1212239, by rfl⟩ : syracuseStep 1616319 = 2424479) B2424479
theorem B11062079 : Blo 1615006 11062079 := bstep (se 1 (by rfl) ⟨8296559, by rfl⟩ : syracuseStep 11062079 = 16593119) B16593119
theorem B10357769 : Blo 1615006 10357769 := bstep (se 2 (by rfl) ⟨3884163, by rfl⟩ : syracuseStep 10357769 = 7768327) B7768327
theorem B1616927 : Blo 1615006 1616927 := bstep (se 1 (by rfl) ⟨1212695, by rfl⟩ : syracuseStep 1616927 = 2425391) B2425391
theorem B1616987 : Blo 1615006 1616987 := bstep (se 1 (by rfl) ⟨1212740, by rfl⟩ : syracuseStep 1616987 = 2425481) B2425481
theorem B34933943 : Blo 1615006 34933943 := bstep (se 1 (by rfl) ⟨26200457, by rfl⟩ : syracuseStep 34933943 = 52400915) B52400915
theorem B4091087 : Blo 1615006 4091087 := bstep (se 1 (by rfl) ⟨3068315, by rfl⟩ : syracuseStep 4091087 = 6136631) B6136631
theorem B8736427 : Blo 1615006 8736427 := bstep (se 1 (by rfl) ⟨6552320, by rfl⟩ : syracuseStep 8736427 = 13104641) B13104641
theorem B18411623 : Blo 1615006 18411623 := bstep (se 1 (by rfl) ⟨13808717, by rfl⟩ : syracuseStep 18411623 = 27617435) B27617435
theorem B4092191 : Blo 1615006 4092191 := bstep (se 1 (by rfl) ⟨3069143, by rfl⟩ : syracuseStep 4092191 = 6138287) B6138287
theorem B7762331 : Blo 1615006 7762331 := bstep (se 1 (by rfl) ⟨5821748, by rfl⟩ : syracuseStep 7762331 = 11643497) B11643497
theorem B23311097 : Blo 1615006 23311097 := bstep (se 2 (by rfl) ⟨8741661, by rfl⟩ : syracuseStep 23311097 = 17483323) B17483323
theorem B6902651 : Blo 1615006 6902651 := bstep (se 1 (by rfl) ⟨5176988, by rfl⟩ : syracuseStep 6902651 = 10353977) B10353977
theorem B14750603 : Blo 1615006 14750603 := bstep (se 1 (by rfl) ⟨11062952, by rfl⟩ : syracuseStep 14750603 = 22125905) B22125905
theorem B113513683 : Blo 1615006 113513683 := bstep (se 1 (by rfl) ⟨85135262, by rfl⟩ : syracuseStep 113513683 = 170270525) B170270525
theorem B59774273 : Blo 1615006 59774273 := bstep (se 2 (by rfl) ⟨22415352, by rfl⟩ : syracuseStep 59774273 = 44830705) B44830705
theorem B5453135 : Blo 1615006 5453135 := bstep (se 1 (by rfl) ⟨4089851, by rfl⟩ : syracuseStep 5453135 = 8179703) B8179703
theorem B3635027 : Blo 1615006 3635027 := bstep (se 1 (by rfl) ⟨2726270, by rfl⟩ : syracuseStep 3635027 = 5452541) B5452541
theorem B29874107 : Blo 1615006 29874107 := bstep (se 1 (by rfl) ⟨22405580, by rfl⟩ : syracuseStep 29874107 = 44811161) B44811161
theorem B3635135 : Blo 1615006 3635135 := bstep (se 1 (by rfl) ⟨2726351, by rfl⟩ : syracuseStep 3635135 = 5452703) B5452703
theorem B2422895 : Blo 1615006 2422895 := bstep (se 1 (by rfl) ⟨1817171, by rfl⟩ : syracuseStep 2422895 = 3634343) B3634343
theorem B6134231 : Blo 1615006 6134231 := bstep (se 1 (by rfl) ⟨4600673, by rfl⟩ : syracuseStep 6134231 = 9201347) B9201347
theorem B3881465 : Blo 1615006 3881465 := bstep (se 2 (by rfl) ⟨1455549, by rfl⟩ : syracuseStep 3881465 = 2911099) B2911099
theorem B2726399 : Blo 1615006 2726399 := bstep (se 1 (by rfl) ⟨2044799, by rfl⟩ : syracuseStep 2726399 = 4089599) B4089599
theorem B5454377 : Blo 1615006 5454377 := bstep (se 2 (by rfl) ⟨2045391, by rfl⟩ : syracuseStep 5454377 = 4090783) B4090783
theorem B5454431 : Blo 1615006 5454431 := bstep (se 1 (by rfl) ⟨4090823, by rfl⟩ : syracuseStep 5454431 = 8181647) B8181647
theorem B2423579 : Blo 1615006 2423579 := bstep (se 1 (by rfl) ⟨1817684, by rfl⟩ : syracuseStep 2423579 = 3635369) B3635369
theorem B9198431 : Blo 1615006 9198431 := bstep (se 1 (by rfl) ⟨6898823, by rfl⟩ : syracuseStep 9198431 = 13797647) B13797647
theorem B2423675 : Blo 1615006 2423675 := bstep (se 1 (by rfl) ⟨1817756, by rfl⟩ : syracuseStep 2423675 = 3635513) B3635513
theorem B12270527 : Blo 1615006 12270527 := bstep (se 1 (by rfl) ⟨9202895, by rfl⟩ : syracuseStep 12270527 = 18405791) B18405791
theorem B9206723 : Blo 1615006 9206723 := bstep (se 1 (by rfl) ⟨6905042, by rfl⟩ : syracuseStep 9206723 = 13810085) B13810085
theorem B8182781 : Blo 1615006 8182781 := bstep (se 3 (by rfl) ⟨1534271, by rfl⟩ : syracuseStep 8182781 = 3068543) B3068543
theorem B7371785 : Blo 1615006 7371785 := bstep (se 2 (by rfl) ⟨2764419, by rfl⟩ : syracuseStep 7371785 = 5528839) B5528839
theorem B9198683 : Blo 1615006 9198683 := bstep (se 1 (by rfl) ⟨6899012, by rfl⟩ : syracuseStep 9198683 = 13798025) B13798025
theorem B2423915 : Blo 1615006 2423915 := bstep (se 1 (by rfl) ⟨1817936, by rfl⟩ : syracuseStep 2423915 = 3635873) B3635873
theorem B2727067 : Blo 1615006 2727067 := bstep (se 1 (by rfl) ⟨2045300, by rfl⟩ : syracuseStep 2727067 = 4090601) B4090601
theorem B2424155 : Blo 1615006 2424155 := bstep (se 1 (by rfl) ⟨1818116, by rfl⟩ : syracuseStep 2424155 = 3636233) B3636233
theorem B7978727 : Blo 1615006 7978727 := bstep (se 1 (by rfl) ⟨5984045, by rfl⟩ : syracuseStep 7978727 = 11968091) B11968091
theorem B2424809 : Blo 1615006 2424809 := bstep (se 2 (by rfl) ⟨909303, by rfl⟩ : syracuseStep 2424809 = 1818607) B1818607
theorem B2424827 : Blo 1615006 2424827 := bstep (se 1 (by rfl) ⟨1818620, by rfl⟩ : syracuseStep 2424827 = 3637241) B3637241
theorem B3637331 : Blo 1615006 3637331 := bstep (se 1 (by rfl) ⟨2727998, by rfl⟩ : syracuseStep 3637331 = 5455997) B5455997
theorem B2424953 : Blo 1615006 2424953 := bstep (se 2 (by rfl) ⟨909357, by rfl⟩ : syracuseStep 2424953 = 1818715) B1818715
theorem B3637403 : Blo 1615006 3637403 := bstep (se 1 (by rfl) ⟨2728052, by rfl⟩ : syracuseStep 3637403 = 5456105) B5456105
theorem B19169465 : Blo 1615006 19169465 := bstep (se 2 (by rfl) ⟨7188549, by rfl⟩ : syracuseStep 19169465 = 14377099) B14377099
theorem B2728127 : Blo 1615006 2728127 := bstep (se 1 (by rfl) ⟨2046095, by rfl⟩ : syracuseStep 2728127 = 4092191) B4092191
theorem B15540731 : Blo 1615006 15540731 := bstep (se 1 (by rfl) ⟨11655548, by rfl⟩ : syracuseStep 15540731 = 23311097) B23311097
theorem B2425385 : Blo 1615006 2425385 := bstep (se 2 (by rfl) ⟨909519, by rfl⟩ : syracuseStep 2425385 = 1819039) B1819039
theorem B8184401 : Blo 1615006 8184401 := bstep (se 2 (by rfl) ⟨3069150, by rfl⟩ : syracuseStep 8184401 = 6138301) B6138301
theorem B10355309 : Blo 1615006 10355309 := bstep (se 3 (by rfl) ⟨1941620, by rfl⟩ : syracuseStep 10355309 = 3883241) B3883241
theorem B3637979 : Blo 1615006 3637979 := bstep (se 1 (by rfl) ⟨2728484, by rfl⟩ : syracuseStep 3637979 = 5456969) B5456969
theorem B9200573 : Blo 1615006 9200573 := bstep (se 3 (by rfl) ⟨1725107, by rfl⟩ : syracuseStep 9200573 = 3450215) B3450215
theorem B1615263 : Blo 1615006 1615263 := bstep (se 1 (by rfl) ⟨1211447, by rfl⟩ : syracuseStep 1615263 = 2422895) B2422895
theorem B4089487 : Blo 1615006 4089487 := bstep (se 1 (by rfl) ⟨3067115, by rfl⟩ : syracuseStep 4089487 = 6134231) B6134231
theorem B1615719 : Blo 1615006 1615719 := bstep (se 1 (by rfl) ⟨1211789, by rfl⟩ : syracuseStep 1615719 = 2423579) B2423579
theorem B7374719 : Blo 1615006 7374719 := bstep (se 1 (by rfl) ⟨5531039, by rfl⟩ : syracuseStep 7374719 = 11062079) B11062079
theorem B1615783 : Blo 1615006 1615783 := bstep (se 1 (by rfl) ⟨1211837, by rfl⟩ : syracuseStep 1615783 = 2423675) B2423675
theorem B21276605 : Blo 1615006 21276605 := bstep (se 3 (by rfl) ⟨3989363, by rfl⟩ : syracuseStep 21276605 = 7978727) B7978727
theorem B6137815 : Blo 1615006 6137815 := bstep (se 1 (by rfl) ⟨4603361, by rfl⟩ : syracuseStep 6137815 = 9206723) B9206723
theorem B1615943 : Blo 1615006 1615943 := bstep (se 1 (by rfl) ⟨1211957, by rfl⟩ : syracuseStep 1615943 = 2423915) B2423915
theorem B1616103 : Blo 1615006 1616103 := bstep (se 1 (by rfl) ⟨1212077, by rfl⟩ : syracuseStep 1616103 = 2424155) B2424155
theorem B1616539 : Blo 1615006 1616539 := bstep (se 1 (by rfl) ⟨1212404, by rfl⟩ : syracuseStep 1616539 = 2424809) B2424809
theorem B1616551 : Blo 1615006 1616551 := bstep (se 1 (by rfl) ⟨1212413, by rfl⟩ : syracuseStep 1616551 = 2424827) B2424827
theorem B6138575 : Blo 1615006 6138575 := bstep (se 1 (by rfl) ⟨4603931, by rfl⟩ : syracuseStep 6138575 = 9207863) B9207863
theorem B12274415 : Blo 1615006 12274415 := bstep (se 1 (by rfl) ⟨9205811, by rfl⟩ : syracuseStep 12274415 = 18411623) B18411623
theorem B1616807 : Blo 1615006 1616807 := bstep (se 1 (by rfl) ⟨1212605, by rfl⟩ : syracuseStep 1616807 = 2425211) B2425211
theorem B11365543 : Blo 1615006 11365543 := bstep (se 1 (by rfl) ⟨8524157, by rfl⟩ : syracuseStep 11365543 = 17048315) B17048315
theorem B9833735 : Blo 1615006 9833735 := bstep (se 1 (by rfl) ⟨7375301, by rfl⟩ : syracuseStep 9833735 = 14750603) B14750603
theorem B4091219 : Blo 1615006 4091219 := bstep (se 1 (by rfl) ⟨3068414, by rfl⟩ : syracuseStep 4091219 = 6136829) B6136829
theorem B39849515 : Blo 1615006 39849515 := bstep (se 1 (by rfl) ⟨29887136, by rfl⟩ : syracuseStep 39849515 = 59774273) B59774273
theorem B4599467 : Blo 1615006 4599467 := bstep (se 1 (by rfl) ⟨3449600, by rfl⟩ : syracuseStep 4599467 = 6899201) B6899201
theorem B5451839 : Blo 1615006 5451839 := bstep (se 1 (by rfl) ⟨4088879, by rfl⟩ : syracuseStep 5451839 = 8177759) B8177759
theorem B4092059 : Blo 1615006 4092059 := bstep (se 1 (by rfl) ⟨3069044, by rfl⟩ : syracuseStep 4092059 = 6138089) B6138089
theorem B2044111 : Blo 1615006 2044111 := bstep (se 1 (by rfl) ⟨1533083, by rfl⟩ : syracuseStep 2044111 = 3066167) B3066167
theorem B151351577 : Blo 1615006 151351577 := bstep (se 2 (by rfl) ⟨56756841, by rfl⟩ : syracuseStep 151351577 = 113513683) B113513683
theorem B6132287 : Blo 1615006 6132287 := bstep (se 1 (by rfl) ⟨4599215, by rfl⟩ : syracuseStep 6132287 = 9198431) B9198431
theorem B8180351 : Blo 1615006 8180351 := bstep (se 1 (by rfl) ⟨6135263, by rfl⟩ : syracuseStep 8180351 = 12270527) B12270527
theorem B6132455 : Blo 1615006 6132455 := bstep (se 1 (by rfl) ⟨4599341, by rfl⟩ : syracuseStep 6132455 = 9198683) B9198683
theorem B79664285 : Blo 1615006 79664285 := bstep (se 3 (by rfl) ⟨14937053, by rfl⟩ : syracuseStep 79664285 = 29874107) B29874107
theorem B5453081 : Blo 1615006 5453081 := bstep (se 2 (by rfl) ⟨2044905, by rfl⟩ : syracuseStep 5453081 = 4089811) B4089811
theorem B5174887 : Blo 1615006 5174887 := bstep (se 1 (by rfl) ⟨3881165, by rfl⟩ : syracuseStep 5174887 = 7762331) B7762331
theorem B44840729 : Blo 1615006 44840729 := bstep (se 2 (by rfl) ⟨16815273, by rfl⟩ : syracuseStep 44840729 = 33630547) B33630547
theorem B4601767 : Blo 1615006 4601767 := bstep (se 1 (by rfl) ⟨3451325, by rfl⟩ : syracuseStep 4601767 = 6902651) B6902651
theorem B6133927 : Blo 1615006 6133927 := bstep (se 1 (by rfl) ⟨4600445, by rfl⟩ : syracuseStep 6133927 = 9200891) B9200891
theorem B3635423 : Blo 1615006 3635423 := bstep (se 1 (by rfl) ⟨2726567, by rfl⟩ : syracuseStep 3635423 = 5453135) B5453135
theorem B46594277 : Blo 1615006 46594277 := bstep (se 4 (by rfl) ⟨4368213, by rfl⟩ : syracuseStep 46594277 = 8736427) B8736427
theorem B2423351 : Blo 1615006 2423351 := bstep (se 1 (by rfl) ⟨1817513, by rfl⟩ : syracuseStep 2423351 = 3635027) B3635027
theorem B2423423 : Blo 1615006 2423423 := bstep (se 1 (by rfl) ⟨1817567, by rfl⟩ : syracuseStep 2423423 = 3635135) B3635135
theorem B3636089 : Blo 1615006 3636089 := bstep (se 2 (by rfl) ⟨1363533, by rfl⟩ : syracuseStep 3636089 = 2727067) B2727067
theorem B44211095 : Blo 1615006 44211095 := bstep (se 1 (by rfl) ⟨33158321, by rfl⟩ : syracuseStep 44211095 = 66316643) B66316643
theorem B2587643 : Blo 1615006 2587643 := bstep (se 1 (by rfl) ⟨1940732, by rfl⟩ : syracuseStep 2587643 = 3881465) B3881465
theorem B1817599 : Blo 1615006 1817599 := bstep (se 1 (by rfl) ⟨1363199, by rfl⟩ : syracuseStep 1817599 = 2726399) B2726399
theorem B3636251 : Blo 1615006 3636251 := bstep (se 1 (by rfl) ⟨2727188, by rfl⟩ : syracuseStep 3636251 = 5454377) B5454377
theorem B3636287 : Blo 1615006 3636287 := bstep (se 1 (by rfl) ⟨2727215, by rfl⟩ : syracuseStep 3636287 = 5454431) B5454431
theorem B5455187 : Blo 1615006 5455187 := bstep (se 1 (by rfl) ⟨4091390, by rfl⟩ : syracuseStep 5455187 = 8182781) B8182781
theorem B4914523 : Blo 1615006 4914523 := bstep (se 1 (by rfl) ⟨3685892, by rfl⟩ : syracuseStep 4914523 = 7371785) B7371785
theorem B6905179 : Blo 1615006 6905179 := bstep (se 1 (by rfl) ⟨5178884, by rfl⟩ : syracuseStep 6905179 = 10357769) B10357769
theorem B23289295 : Blo 1615006 23289295 := bstep (se 1 (by rfl) ⟨17466971, by rfl⟩ : syracuseStep 23289295 = 34933943) B34933943
theorem B2727391 : Blo 1615006 2727391 := bstep (se 1 (by rfl) ⟨2045543, by rfl⟩ : syracuseStep 2727391 = 4091087) B4091087
theorem B2424887 : Blo 1615006 2424887 := bstep (se 1 (by rfl) ⟨1818665, by rfl⟩ : syracuseStep 2424887 = 3637331) B3637331
theorem B2728039 : Blo 1615006 2728039 := bstep (se 1 (by rfl) ⟨2046029, by rfl⟩ : syracuseStep 2728039 = 4092059) B4092059
theorem B2424935 : Blo 1615006 2424935 := bstep (se 1 (by rfl) ⟨1818701, by rfl⟩ : syracuseStep 2424935 = 3637403) B3637403
theorem B1818751 : Blo 1615006 1818751 := bstep (se 1 (by rfl) ⟨1364063, by rfl⟩ : syracuseStep 1818751 = 2728127) B2728127
theorem B100901051 : Blo 1615006 100901051 := bstep (se 1 (by rfl) ⟨75675788, by rfl⟩ : syracuseStep 100901051 = 151351577) B151351577
theorem B4088191 : Blo 1615006 4088191 := bstep (se 1 (by rfl) ⟨3066143, by rfl⟩ : syracuseStep 4088191 = 6132287) B6132287
theorem B5456267 : Blo 1615006 5456267 := bstep (se 1 (by rfl) ⟨4092200, by rfl⟩ : syracuseStep 5456267 = 8184401) B8184401
theorem B2425319 : Blo 1615006 2425319 := bstep (se 1 (by rfl) ⟨1818989, by rfl⟩ : syracuseStep 2425319 = 3637979) B3637979
theorem B51118573 : Blo 1615006 51118573 := bstep (se 3 (by rfl) ⟨9584732, by rfl⟩ : syracuseStep 51118573 = 19169465) B19169465
theorem B4088303 : Blo 1615006 4088303 := bstep (se 1 (by rfl) ⟨3066227, by rfl⟩ : syracuseStep 4088303 = 6132455) B6132455
theorem B53109523 : Blo 1615006 53109523 := bstep (se 1 (by rfl) ⟨39832142, by rfl⟩ : syracuseStep 53109523 = 79664285) B79664285
theorem B29893819 : Blo 1615006 29893819 := bstep (se 1 (by rfl) ⟨22420364, by rfl⟩ : syracuseStep 29893819 = 44840729) B44840729
theorem B4916479 : Blo 1615006 4916479 := bstep (se 1 (by rfl) ⟨3687359, by rfl⟩ : syracuseStep 4916479 = 7374719) B7374719
theorem B1615567 : Blo 1615006 1615567 := bstep (se 1 (by rfl) ⟨1211675, by rfl⟩ : syracuseStep 1615567 = 2423351) B2423351
theorem B1615615 : Blo 1615006 1615615 := bstep (se 1 (by rfl) ⟨1211711, by rfl⟩ : syracuseStep 1615615 = 2423423) B2423423
theorem B6899849 : Blo 1615006 6899849 := bstep (se 2 (by rfl) ⟨2587443, by rfl⟩ : syracuseStep 6899849 = 5174887) B5174887
theorem B6555823 : Blo 1615006 6555823 := bstep (se 1 (by rfl) ⟨4916867, by rfl⟩ : syracuseStep 6555823 = 9833735) B9833735
theorem B3066311 : Blo 1615006 3066311 := bstep (se 1 (by rfl) ⟨2299733, by rfl⟩ : syracuseStep 3066311 = 4599467) B4599467
theorem B1616635 : Blo 1615006 1616635 := bstep (se 1 (by rfl) ⟨1212476, by rfl⟩ : syracuseStep 1616635 = 2424953) B2424953
theorem B8178569 : Blo 1615006 8178569 := bstep (se 2 (by rfl) ⟨3066963, by rfl⟩ : syracuseStep 8178569 = 6133927) B6133927
theorem B1616923 : Blo 1615006 1616923 := bstep (se 1 (by rfl) ⟨1212692, by rfl⟩ : syracuseStep 1616923 = 2425385) B2425385
theorem B4092383 : Blo 1615006 4092383 := bstep (se 1 (by rfl) ⟨3069287, by rfl⟩ : syracuseStep 4092383 = 6138575) B6138575
theorem B31052393 : Blo 1615006 31052393 := bstep (se 2 (by rfl) ⟨11644647, by rfl⟩ : syracuseStep 31052393 = 23289295) B23289295
theorem B1725095 : Blo 1615006 1725095 := bstep (se 1 (by rfl) ⟨1293821, by rfl⟩ : syracuseStep 1725095 = 2587643) B2587643
theorem B5452649 : Blo 1615006 5452649 := bstep (se 2 (by rfl) ⟨2044743, by rfl⟩ : syracuseStep 5452649 = 4089487) B4089487
theorem B3634559 : Blo 1615006 3634559 := bstep (se 1 (by rfl) ⟨2725919, by rfl⟩ : syracuseStep 3634559 = 5451839) B5451839
theorem B2725481 : Blo 1615006 2725481 := bstep (se 2 (by rfl) ⟨1022055, by rfl⟩ : syracuseStep 2725481 = 2044111) B2044111
theorem B10360487 : Blo 1615006 10360487 := bstep (se 1 (by rfl) ⟨7770365, by rfl⟩ : syracuseStep 10360487 = 15540731) B15540731
theorem B6903539 : Blo 1615006 6903539 := bstep (se 1 (by rfl) ⟨5177654, by rfl⟩ : syracuseStep 6903539 = 10355309) B10355309
theorem B5453567 : Blo 1615006 5453567 := bstep (se 1 (by rfl) ⟨4090175, by rfl⟩ : syracuseStep 5453567 = 8180351) B8180351
theorem B6133715 : Blo 1615006 6133715 := bstep (se 1 (by rfl) ⟨4600286, by rfl⟩ : syracuseStep 6133715 = 9200573) B9200573
theorem B3635387 : Blo 1615006 3635387 := bstep (se 1 (by rfl) ⟨2726540, by rfl⟩ : syracuseStep 3635387 = 5453081) B5453081
theorem B2423465 : Blo 1615006 2423465 := bstep (se 2 (by rfl) ⟨908799, by rfl⟩ : syracuseStep 2423465 = 1817599) B1817599
theorem B2423615 : Blo 1615006 2423615 := bstep (se 1 (by rfl) ⟨1817711, by rfl⟩ : syracuseStep 2423615 = 3635423) B3635423
theorem B31062851 : Blo 1615006 31062851 := bstep (se 1 (by rfl) ⟨23297138, by rfl⟩ : syracuseStep 31062851 = 46594277) B46594277
theorem B15154057 : Blo 1615006 15154057 := bstep (se 2 (by rfl) ⟨5682771, by rfl⟩ : syracuseStep 15154057 = 11365543) B11365543
theorem B6552697 : Blo 1615006 6552697 := bstep (se 2 (by rfl) ⟨2457261, by rfl⟩ : syracuseStep 6552697 = 4914523) B4914523
theorem B9206905 : Blo 1615006 9206905 := bstep (se 2 (by rfl) ⟨3452589, by rfl⟩ : syracuseStep 9206905 = 6905179) B6905179
theorem B8182943 : Blo 1615006 8182943 := bstep (se 1 (by rfl) ⟨6137207, by rfl⟩ : syracuseStep 8182943 = 12274415) B12274415
theorem B2424059 : Blo 1615006 2424059 := bstep (se 1 (by rfl) ⟨1818044, by rfl⟩ : syracuseStep 2424059 = 3636089) B3636089
theorem B29474063 : Blo 1615006 29474063 := bstep (se 1 (by rfl) ⟨22105547, by rfl⟩ : syracuseStep 29474063 = 44211095) B44211095
theorem B3636521 : Blo 1615006 3636521 := bstep (se 2 (by rfl) ⟨1363695, by rfl⟩ : syracuseStep 3636521 = 2727391) B2727391
theorem B2424167 : Blo 1615006 2424167 := bstep (se 1 (by rfl) ⟨1818125, by rfl⟩ : syracuseStep 2424167 = 3636251) B3636251
theorem B2424191 : Blo 1615006 2424191 := bstep (se 1 (by rfl) ⟨1818143, by rfl⟩ : syracuseStep 2424191 = 3636287) B3636287
theorem B2727479 : Blo 1615006 2727479 := bstep (se 1 (by rfl) ⟨2045609, by rfl⟩ : syracuseStep 2727479 = 4091219) B4091219
theorem B3636791 : Blo 1615006 3636791 := bstep (se 1 (by rfl) ⟨2727593, by rfl⟩ : syracuseStep 3636791 = 5455187) B5455187
theorem B26566343 : Blo 1615006 26566343 := bstep (se 1 (by rfl) ⟨19924757, by rfl⟩ : syracuseStep 26566343 = 39849515) B39849515
theorem B56737613 : Blo 1615006 56737613 := bstep (se 3 (by rfl) ⟨10638302, by rfl⟩ : syracuseStep 56737613 = 21276605) B21276605
theorem B6135689 : Blo 1615006 6135689 := bstep (se 2 (by rfl) ⟨2300883, by rfl⟩ : syracuseStep 6135689 = 4601767) B4601767
theorem B8183753 : Blo 1615006 8183753 := bstep (se 2 (by rfl) ⟨3068907, by rfl⟩ : syracuseStep 8183753 = 6137815) B6137815
theorem B3637385 : Blo 1615006 3637385 := bstep (se 2 (by rfl) ⟨1364019, by rfl⟩ : syracuseStep 3637385 = 2728039) B2728039
theorem B2425001 : Blo 1615006 2425001 := bstep (se 2 (by rfl) ⟨909375, by rfl⟩ : syracuseStep 2425001 = 1818751) B1818751
theorem B3637511 : Blo 1615006 3637511 := bstep (se 1 (by rfl) ⟨2728133, by rfl⟩ : syracuseStep 3637511 = 5456267) B5456267
theorem B2728255 : Blo 1615006 2728255 := bstep (se 1 (by rfl) ⟨2046191, by rfl⟩ : syracuseStep 2728255 = 4092383) B4092383
theorem B20701595 : Blo 1615006 20701595 := bstep (se 1 (by rfl) ⟨15526196, by rfl⟩ : syracuseStep 20701595 = 31052393) B31052393
theorem B68158097 : Blo 1615006 68158097 := bstep (se 2 (by rfl) ⟨25559286, by rfl⟩ : syracuseStep 68158097 = 51118573) B51118573
theorem B34964389 : Blo 1615006 34964389 := bstep (se 4 (by rfl) ⟨3277911, by rfl⟩ : syracuseStep 34964389 = 6555823) B6555823
theorem B6906991 : Blo 1615006 6906991 := bstep (se 1 (by rfl) ⟨5180243, by rfl⟩ : syracuseStep 6906991 = 10360487) B10360487
theorem B4089143 : Blo 1615006 4089143 := bstep (se 1 (by rfl) ⟨3066857, by rfl⟩ : syracuseStep 4089143 = 6133715) B6133715
theorem B6555305 : Blo 1615006 6555305 := bstep (se 2 (by rfl) ⟨2458239, by rfl⟩ : syracuseStep 6555305 = 4916479) B4916479
theorem B1615643 : Blo 1615006 1615643 := bstep (se 1 (by rfl) ⟨1211732, by rfl⟩ : syracuseStep 1615643 = 2423465) B2423465
theorem B1615743 : Blo 1615006 1615743 := bstep (se 1 (by rfl) ⟨1211807, by rfl⟩ : syracuseStep 1615743 = 2423615) B2423615
theorem B1616039 : Blo 1615006 1616039 := bstep (se 1 (by rfl) ⟨1212029, by rfl⟩ : syracuseStep 1616039 = 2424059) B2424059
theorem B1616111 : Blo 1615006 1616111 := bstep (se 1 (by rfl) ⟨1212083, by rfl⟩ : syracuseStep 1616111 = 2424167) B2424167
theorem B1616127 : Blo 1615006 1616127 := bstep (se 1 (by rfl) ⟨1212095, by rfl⟩ : syracuseStep 1616127 = 2424191) B2424191
theorem B37825075 : Blo 1615006 37825075 := bstep (se 1 (by rfl) ⟨28368806, by rfl⟩ : syracuseStep 37825075 = 56737613) B56737613
theorem B4090459 : Blo 1615006 4090459 := bstep (se 1 (by rfl) ⟨3067844, by rfl⟩ : syracuseStep 4090459 = 6135689) B6135689
theorem B1616591 : Blo 1615006 1616591 := bstep (se 1 (by rfl) ⟨1212443, by rfl⟩ : syracuseStep 1616591 = 2424887) B2424887
theorem B1616623 : Blo 1615006 1616623 := bstep (se 1 (by rfl) ⟨1212467, by rfl⟩ : syracuseStep 1616623 = 2424935) B2424935
theorem B67267367 : Blo 1615006 67267367 := bstep (se 1 (by rfl) ⟨50450525, by rfl⟩ : syracuseStep 67267367 = 100901051) B100901051
theorem B1616879 : Blo 1615006 1616879 := bstep (se 1 (by rfl) ⟨1212659, by rfl⟩ : syracuseStep 1616879 = 2425319) B2425319
theorem B5450921 : Blo 1615006 5450921 := bstep (se 2 (by rfl) ⟨2044095, by rfl⟩ : syracuseStep 5450921 = 4088191) B4088191
theorem B20205409 : Blo 1615006 20205409 := bstep (se 2 (by rfl) ⟨7577028, by rfl⟩ : syracuseStep 20205409 = 15154057) B15154057
theorem B4599899 : Blo 1615006 4599899 := bstep (se 1 (by rfl) ⟨3449924, by rfl⟩ : syracuseStep 4599899 = 6899849) B6899849
theorem B283250789 : Blo 1615006 283250789 := bstep (se 4 (by rfl) ⟨26554761, by rfl⟩ : syracuseStep 283250789 = 53109523) B53109523
theorem B8736929 : Blo 1615006 8736929 := bstep (se 2 (by rfl) ⟨3276348, by rfl⟩ : syracuseStep 8736929 = 6552697) B6552697
theorem B12275873 : Blo 1615006 12275873 := bstep (se 2 (by rfl) ⟨4603452, by rfl⟩ : syracuseStep 12275873 = 9206905) B9206905
theorem B39858425 : Blo 1615006 39858425 := bstep (se 2 (by rfl) ⟨14946909, by rfl⟩ : syracuseStep 39858425 = 29893819) B29893819
theorem B2044207 : Blo 1615006 2044207 := bstep (se 1 (by rfl) ⟨1533155, by rfl⟩ : syracuseStep 2044207 = 3066311) B3066311
theorem B4600253 : Blo 1615006 4600253 := bstep (se 3 (by rfl) ⟨862547, by rfl⟩ : syracuseStep 4600253 = 1725095) B1725095
theorem B5452379 : Blo 1615006 5452379 := bstep (se 1 (by rfl) ⟨4089284, by rfl⟩ : syracuseStep 5452379 = 8178569) B8178569
theorem B19649375 : Blo 1615006 19649375 := bstep (se 1 (by rfl) ⟨14737031, by rfl⟩ : syracuseStep 19649375 = 29474063) B29474063
theorem B2725535 : Blo 1615006 2725535 := bstep (se 1 (by rfl) ⟨2044151, by rfl⟩ : syracuseStep 2725535 = 4088303) B4088303
theorem B3635099 : Blo 1615006 3635099 := bstep (se 1 (by rfl) ⟨2726324, by rfl⟩ : syracuseStep 3635099 = 5452649) B5452649
theorem B2423039 : Blo 1615006 2423039 := bstep (se 1 (by rfl) ⟨1817279, by rfl⟩ : syracuseStep 2423039 = 3634559) B3634559
theorem B1816987 : Blo 1615006 1816987 := bstep (se 1 (by rfl) ⟨1362740, by rfl⟩ : syracuseStep 1816987 = 2725481) B2725481
theorem B4602359 : Blo 1615006 4602359 := bstep (se 1 (by rfl) ⟨3451769, by rfl⟩ : syracuseStep 4602359 = 6903539) B6903539
theorem B3635711 : Blo 1615006 3635711 := bstep (se 1 (by rfl) ⟨2726783, by rfl⟩ : syracuseStep 3635711 = 5453567) B5453567
theorem B2423591 : Blo 1615006 2423591 := bstep (se 1 (by rfl) ⟨1817693, by rfl⟩ : syracuseStep 2423591 = 3635387) B3635387
theorem B20708567 : Blo 1615006 20708567 := bstep (se 1 (by rfl) ⟨15531425, by rfl⟩ : syracuseStep 20708567 = 31062851) B31062851
theorem B5455295 : Blo 1615006 5455295 := bstep (se 1 (by rfl) ⟨4091471, by rfl⟩ : syracuseStep 5455295 = 8182943) B8182943
theorem B2424347 : Blo 1615006 2424347 := bstep (se 1 (by rfl) ⟨1818260, by rfl⟩ : syracuseStep 2424347 = 3636521) B3636521
theorem B1818319 : Blo 1615006 1818319 := bstep (se 1 (by rfl) ⟨1363739, by rfl⟩ : syracuseStep 1818319 = 2727479) B2727479
theorem B2424527 : Blo 1615006 2424527 := bstep (se 1 (by rfl) ⟨1818395, by rfl⟩ : syracuseStep 2424527 = 3636791) B3636791
theorem B17710895 : Blo 1615006 17710895 := bstep (se 1 (by rfl) ⟨13283171, by rfl⟩ : syracuseStep 17710895 = 26566343) B26566343
theorem B5455835 : Blo 1615006 5455835 := bstep (se 1 (by rfl) ⟨4091876, by rfl⟩ : syracuseStep 5455835 = 8183753) B8183753
theorem B188833859 : Blo 1615006 188833859 := bstep (se 1 (by rfl) ⟨141625394, by rfl⟩ : syracuseStep 188833859 = 283250789) B283250789
theorem B2424923 : Blo 1615006 2424923 := bstep (se 1 (by rfl) ⟨1818692, by rfl⟩ : syracuseStep 2424923 = 3637385) B3637385
theorem B5824619 : Blo 1615006 5824619 := bstep (se 1 (by rfl) ⟨4368464, by rfl⟩ : syracuseStep 5824619 = 8736929) B8736929
theorem B8183915 : Blo 1615006 8183915 := bstep (se 1 (by rfl) ⟨6137936, by rfl⟩ : syracuseStep 8183915 = 12275873) B12275873
theorem B2425007 : Blo 1615006 2425007 := bstep (se 1 (by rfl) ⟨1818755, by rfl⟩ : syracuseStep 2425007 = 3637511) B3637511
theorem B3637673 : Blo 1615006 3637673 := bstep (se 2 (by rfl) ⟨1364127, by rfl⟩ : syracuseStep 3637673 = 2728255) B2728255
theorem B13099583 : Blo 1615006 13099583 := bstep (se 1 (by rfl) ⟨9824687, by rfl⟩ : syracuseStep 13099583 = 19649375) B19649375
theorem B12272957 : Blo 1615006 12272957 := bstep (se 3 (by rfl) ⟨2301179, by rfl⟩ : syracuseStep 12272957 = 4602359) B4602359
theorem B9209321 : Blo 1615006 9209321 := bstep (se 2 (by rfl) ⟨3453495, by rfl⟩ : syracuseStep 9209321 = 6906991) B6906991
theorem B1615359 : Blo 1615006 1615359 := bstep (se 1 (by rfl) ⟨1211519, by rfl⟩ : syracuseStep 1615359 = 2423039) B2423039
theorem B1615727 : Blo 1615006 1615727 := bstep (se 1 (by rfl) ⟨1211795, by rfl⟩ : syracuseStep 1615727 = 2423591) B2423591
theorem B44844911 : Blo 1615006 44844911 := bstep (se 1 (by rfl) ⟨33633683, by rfl⟩ : syracuseStep 44844911 = 67267367) B67267367
theorem B13805711 : Blo 1615006 13805711 := bstep (se 1 (by rfl) ⟨10354283, by rfl⟩ : syracuseStep 13805711 = 20708567) B20708567
theorem B1616231 : Blo 1615006 1616231 := bstep (se 1 (by rfl) ⟨1212173, by rfl⟩ : syracuseStep 1616231 = 2424347) B2424347
theorem B1616351 : Blo 1615006 1616351 := bstep (se 1 (by rfl) ⟨1212263, by rfl⟩ : syracuseStep 1616351 = 2424527) B2424527
theorem B11807263 : Blo 1615006 11807263 := bstep (se 1 (by rfl) ⟨8855447, by rfl⟩ : syracuseStep 11807263 = 17710895) B17710895
theorem B3066599 : Blo 1615006 3066599 := bstep (se 1 (by rfl) ⟨2299949, by rfl⟩ : syracuseStep 3066599 = 4599899) B4599899
theorem B1616667 : Blo 1615006 1616667 := bstep (se 1 (by rfl) ⟨1212500, by rfl⟩ : syracuseStep 1616667 = 2425001) B2425001
theorem B3066835 : Blo 1615006 3066835 := bstep (se 1 (by rfl) ⟨2300126, by rfl⟩ : syracuseStep 3066835 = 4600253) B4600253
theorem B4370203 : Blo 1615006 4370203 := bstep (se 1 (by rfl) ⟨3277652, by rfl⟩ : syracuseStep 4370203 = 6555305) B6555305
theorem B3633947 : Blo 1615006 3633947 := bstep (se 1 (by rfl) ⟨2725460, by rfl⟩ : syracuseStep 3633947 = 5450921) B5450921
theorem B26940545 : Blo 1615006 26940545 := bstep (se 2 (by rfl) ⟨10102704, by rfl⟩ : syracuseStep 26940545 = 20205409) B20205409
theorem B26572283 : Blo 1615006 26572283 := bstep (se 1 (by rfl) ⟨19929212, by rfl⟩ : syracuseStep 26572283 = 39858425) B39858425
theorem B201733733 : Blo 1615006 201733733 := bstep (se 4 (by rfl) ⟨18912537, by rfl⟩ : syracuseStep 201733733 = 37825075) B37825075
theorem B13801063 : Blo 1615006 13801063 := bstep (se 1 (by rfl) ⟨10350797, by rfl⟩ : syracuseStep 13801063 = 20701595) B20701595
theorem B3634919 : Blo 1615006 3634919 := bstep (se 1 (by rfl) ⟨2726189, by rfl⟩ : syracuseStep 3634919 = 5452379) B5452379
theorem B2725609 : Blo 1615006 2725609 := bstep (se 2 (by rfl) ⟨1022103, by rfl⟩ : syracuseStep 2725609 = 2044207) B2044207
theorem B45438731 : Blo 1615006 45438731 := bstep (se 1 (by rfl) ⟨34079048, by rfl⟩ : syracuseStep 45438731 = 68158097) B68158097
theorem B2422649 : Blo 1615006 2422649 := bstep (se 2 (by rfl) ⟨908493, by rfl⟩ : syracuseStep 2422649 = 1816987) B1816987
theorem B5453945 : Blo 1615006 5453945 := bstep (se 2 (by rfl) ⟨2045229, by rfl⟩ : syracuseStep 5453945 = 4090459) B4090459
theorem B2726095 : Blo 1615006 2726095 := bstep (se 1 (by rfl) ⟨2044571, by rfl⟩ : syracuseStep 2726095 = 4089143) B4089143
theorem B1817023 : Blo 1615006 1817023 := bstep (se 1 (by rfl) ⟨1362767, by rfl⟩ : syracuseStep 1817023 = 2725535) B2725535
theorem B46619185 : Blo 1615006 46619185 := bstep (se 2 (by rfl) ⟨17482194, by rfl⟩ : syracuseStep 46619185 = 34964389) B34964389
theorem B2423399 : Blo 1615006 2423399 := bstep (se 1 (by rfl) ⟨1817549, by rfl⟩ : syracuseStep 2423399 = 3635099) B3635099
theorem B2423807 : Blo 1615006 2423807 := bstep (se 1 (by rfl) ⟨1817855, by rfl⟩ : syracuseStep 2423807 = 3635711) B3635711
theorem B2424425 : Blo 1615006 2424425 := bstep (se 2 (by rfl) ⟨909159, by rfl⟩ : syracuseStep 2424425 = 1818319) B1818319
theorem B3636863 : Blo 1615006 3636863 := bstep (se 1 (by rfl) ⟨2727647, by rfl⟩ : syracuseStep 3636863 = 5455295) B5455295
theorem B3637223 : Blo 1615006 3637223 := bstep (se 1 (by rfl) ⟨2727917, by rfl⟩ : syracuseStep 3637223 = 5455835) B5455835
theorem B3883079 : Blo 1615006 3883079 := bstep (se 1 (by rfl) ⟨2912309, by rfl⟩ : syracuseStep 3883079 = 5824619) B5824619
theorem B5455943 : Blo 1615006 5455943 := bstep (se 1 (by rfl) ⟨4091957, by rfl⟩ : syracuseStep 5455943 = 8183915) B8183915
theorem B2425115 : Blo 1615006 2425115 := bstep (se 1 (by rfl) ⟨1818836, by rfl⟩ : syracuseStep 2425115 = 3637673) B3637673
theorem B134489155 : Blo 1615006 134489155 := bstep (se 1 (by rfl) ⟨100866866, by rfl⟩ : syracuseStep 134489155 = 201733733) B201733733
theorem B1615099 : Blo 1615006 1615099 := bstep (se 1 (by rfl) ⟨1211324, by rfl⟩ : syracuseStep 1615099 = 2422649) B2422649
theorem B4089113 : Blo 1615006 4089113 := bstep (se 2 (by rfl) ⟨1533417, by rfl⟩ : syracuseStep 4089113 = 3066835) B3066835
theorem B23307749 : Blo 1615006 23307749 := bstep (se 4 (by rfl) ⟨2185101, by rfl⟩ : syracuseStep 23307749 = 4370203) B4370203
theorem B34932221 : Blo 1615006 34932221 := bstep (se 3 (by rfl) ⟨6549791, by rfl⟩ : syracuseStep 34932221 = 13099583) B13099583
theorem B1615599 : Blo 1615006 1615599 := bstep (se 1 (by rfl) ⟨1211699, by rfl⟩ : syracuseStep 1615599 = 2423399) B2423399
theorem B8177597 : Blo 1615006 8177597 := bstep (se 3 (by rfl) ⟨1533299, by rfl⟩ : syracuseStep 8177597 = 3066599) B3066599
theorem B1615871 : Blo 1615006 1615871 := bstep (se 1 (by rfl) ⟨1211903, by rfl⟩ : syracuseStep 1615871 = 2423807) B2423807
theorem B18401417 : Blo 1615006 18401417 := bstep (se 2 (by rfl) ⟨6900531, by rfl⟩ : syracuseStep 18401417 = 13801063) B13801063
theorem B1616283 : Blo 1615006 1616283 := bstep (se 1 (by rfl) ⟨1212212, by rfl⟩ : syracuseStep 1616283 = 2424425) B2424425
theorem B125889239 : Blo 1615006 125889239 := bstep (se 1 (by rfl) ⟨94416929, by rfl⟩ : syracuseStep 125889239 = 188833859) B188833859
theorem B1616615 : Blo 1615006 1616615 := bstep (se 1 (by rfl) ⟨1212461, by rfl⟩ : syracuseStep 1616615 = 2424923) B2424923
theorem B1616671 : Blo 1615006 1616671 := bstep (se 1 (by rfl) ⟨1212503, by rfl⟩ : syracuseStep 1616671 = 2425007) B2425007
theorem B17960363 : Blo 1615006 17960363 := bstep (se 1 (by rfl) ⟨13470272, by rfl⟩ : syracuseStep 17960363 = 26940545) B26940545
theorem B6139547 : Blo 1615006 6139547 := bstep (se 1 (by rfl) ⟨4604660, by rfl⟩ : syracuseStep 6139547 = 9209321) B9209321
theorem B17714855 : Blo 1615006 17714855 := bstep (se 1 (by rfl) ⟨13286141, by rfl⟩ : syracuseStep 17714855 = 26572283) B26572283
theorem B29896607 : Blo 1615006 29896607 := bstep (se 1 (by rfl) ⟨22422455, by rfl⟩ : syracuseStep 29896607 = 44844911) B44844911
theorem B9203807 : Blo 1615006 9203807 := bstep (se 1 (by rfl) ⟨6902855, by rfl⟩ : syracuseStep 9203807 = 13805711) B13805711
theorem B3634145 : Blo 1615006 3634145 := bstep (se 2 (by rfl) ⟨1362804, by rfl⟩ : syracuseStep 3634145 = 2725609) B2725609
theorem B3634793 : Blo 1615006 3634793 := bstep (se 2 (by rfl) ⟨1363047, by rfl⟩ : syracuseStep 3634793 = 2726095) B2726095
theorem B2422631 : Blo 1615006 2422631 := bstep (se 1 (by rfl) ⟨1816973, by rfl⟩ : syracuseStep 2422631 = 3633947) B3633947
theorem B2422697 : Blo 1615006 2422697 := bstep (se 2 (by rfl) ⟨908511, by rfl⟩ : syracuseStep 2422697 = 1817023) B1817023
theorem B15743017 : Blo 1615006 15743017 := bstep (se 2 (by rfl) ⟨5903631, by rfl⟩ : syracuseStep 15743017 = 11807263) B11807263
theorem B62158913 : Blo 1615006 62158913 := bstep (se 2 (by rfl) ⟨23309592, by rfl⟩ : syracuseStep 62158913 = 46619185) B46619185
theorem B8181971 : Blo 1615006 8181971 := bstep (se 1 (by rfl) ⟨6136478, by rfl⟩ : syracuseStep 8181971 = 12272957) B12272957
theorem B2423279 : Blo 1615006 2423279 := bstep (se 1 (by rfl) ⟨1817459, by rfl⟩ : syracuseStep 2423279 = 3634919) B3634919
theorem B30292487 : Blo 1615006 30292487 := bstep (se 1 (by rfl) ⟨22719365, by rfl⟩ : syracuseStep 30292487 = 45438731) B45438731
theorem B3635963 : Blo 1615006 3635963 := bstep (se 1 (by rfl) ⟨2726972, by rfl⟩ : syracuseStep 3635963 = 5453945) B5453945
theorem B2424575 : Blo 1615006 2424575 := bstep (se 1 (by rfl) ⟨1818431, by rfl⟩ : syracuseStep 2424575 = 3636863) B3636863
theorem B2424815 : Blo 1615006 2424815 := bstep (se 1 (by rfl) ⟨1818611, by rfl⟩ : syracuseStep 2424815 = 3637223) B3637223
theorem B3637295 : Blo 1615006 3637295 := bstep (se 1 (by rfl) ⟨2727971, by rfl⟩ : syracuseStep 3637295 = 5455943) B5455943
theorem B6135871 : Blo 1615006 6135871 := bstep (se 1 (by rfl) ⟨4601903, by rfl⟩ : syracuseStep 6135871 = 9203807) B9203807
theorem B10354877 : Blo 1615006 10354877 := bstep (se 3 (by rfl) ⟨1941539, by rfl⟩ : syracuseStep 10354877 = 3883079) B3883079
theorem B1615087 : Blo 1615006 1615087 := bstep (se 1 (by rfl) ⟨1211315, by rfl⟩ : syracuseStep 1615087 = 2422631) B2422631
theorem B1615131 : Blo 1615006 1615131 := bstep (se 1 (by rfl) ⟨1211348, by rfl⟩ : syracuseStep 1615131 = 2422697) B2422697
theorem B1615519 : Blo 1615006 1615519 := bstep (se 1 (by rfl) ⟨1211639, by rfl⟩ : syracuseStep 1615519 = 2423279) B2423279
theorem B20194991 : Blo 1615006 20194991 := bstep (se 1 (by rfl) ⟨15146243, by rfl⟩ : syracuseStep 20194991 = 30292487) B30292487
theorem B1616383 : Blo 1615006 1616383 := bstep (se 1 (by rfl) ⟨1212287, by rfl⟩ : syracuseStep 1616383 = 2424575) B2424575
theorem B1616543 : Blo 1615006 1616543 := bstep (se 1 (by rfl) ⟨1212407, by rfl⟩ : syracuseStep 1616543 = 2424815) B2424815
theorem B1616743 : Blo 1615006 1616743 := bstep (se 1 (by rfl) ⟨1212557, by rfl⟩ : syracuseStep 1616743 = 2425115) B2425115
theorem B83962757 : Blo 1615006 83962757 := bstep (se 4 (by rfl) ⟨7871508, by rfl⟩ : syracuseStep 83962757 = 15743017) B15743017
theorem B5451731 : Blo 1615006 5451731 := bstep (se 1 (by rfl) ⟨4088798, by rfl⟩ : syracuseStep 5451731 = 8177597) B8177597
theorem B41439275 : Blo 1615006 41439275 := bstep (se 1 (by rfl) ⟨31079456, by rfl⟩ : syracuseStep 41439275 = 62158913) B62158913
theorem B179318873 : Blo 1615006 179318873 := bstep (se 2 (by rfl) ⟨67244577, by rfl⟩ : syracuseStep 179318873 = 134489155) B134489155
theorem B12267611 : Blo 1615006 12267611 := bstep (se 1 (by rfl) ⟨9200708, by rfl⟩ : syracuseStep 12267611 = 18401417) B18401417
theorem B335704637 : Blo 1615006 335704637 := bstep (se 3 (by rfl) ⟨62944619, by rfl⟩ : syracuseStep 335704637 = 125889239) B125889239
theorem B11973575 : Blo 1615006 11973575 := bstep (se 1 (by rfl) ⟨8980181, by rfl⟩ : syracuseStep 11973575 = 17960363) B17960363
theorem B4093031 : Blo 1615006 4093031 := bstep (se 1 (by rfl) ⟨3069773, by rfl⟩ : syracuseStep 4093031 = 6139547) B6139547
theorem B11809903 : Blo 1615006 11809903 := bstep (se 1 (by rfl) ⟨8857427, by rfl⟩ : syracuseStep 11809903 = 17714855) B17714855
theorem B2422763 : Blo 1615006 2422763 := bstep (se 1 (by rfl) ⟨1817072, by rfl⟩ : syracuseStep 2422763 = 3634145) B3634145
theorem B2726075 : Blo 1615006 2726075 := bstep (se 1 (by rfl) ⟨2044556, by rfl⟩ : syracuseStep 2726075 = 4089113) B4089113
theorem B15538499 : Blo 1615006 15538499 := bstep (se 1 (by rfl) ⟨11653874, by rfl⟩ : syracuseStep 15538499 = 23307749) B23307749
theorem B23288147 : Blo 1615006 23288147 := bstep (se 1 (by rfl) ⟨17466110, by rfl⟩ : syracuseStep 23288147 = 34932221) B34932221
theorem B2423195 : Blo 1615006 2423195 := bstep (se 1 (by rfl) ⟨1817396, by rfl⟩ : syracuseStep 2423195 = 3634793) B3634793
theorem B5454647 : Blo 1615006 5454647 := bstep (se 1 (by rfl) ⟨4090985, by rfl⟩ : syracuseStep 5454647 = 8181971) B8181971
theorem B2423975 : Blo 1615006 2423975 := bstep (se 1 (by rfl) ⟨1817981, by rfl⟩ : syracuseStep 2423975 = 3635963) B3635963
theorem B19931071 : Blo 1615006 19931071 := bstep (se 1 (by rfl) ⟨14948303, by rfl⟩ : syracuseStep 19931071 = 29896607) B29896607
theorem B2424863 : Blo 1615006 2424863 := bstep (se 1 (by rfl) ⟨1818647, by rfl⟩ : syracuseStep 2424863 = 3637295) B3637295
theorem B119545915 : Blo 1615006 119545915 := bstep (se 1 (by rfl) ⟨89659436, by rfl⟩ : syracuseStep 119545915 = 179318873) B179318873
theorem B2728687 : Blo 1615006 2728687 := bstep (se 1 (by rfl) ⟨2046515, by rfl⟩ : syracuseStep 2728687 = 4093031) B4093031
theorem B1615175 : Blo 1615006 1615175 := bstep (se 1 (by rfl) ⟨1211381, by rfl⟩ : syracuseStep 1615175 = 2422763) B2422763
theorem B15746537 : Blo 1615006 15746537 := bstep (se 2 (by rfl) ⟨5904951, by rfl⟩ : syracuseStep 15746537 = 11809903) B11809903
theorem B15525431 : Blo 1615006 15525431 := bstep (se 1 (by rfl) ⟨11644073, by rfl⟩ : syracuseStep 15525431 = 23288147) B23288147
theorem B1615463 : Blo 1615006 1615463 := bstep (se 1 (by rfl) ⟨1211597, by rfl⟩ : syracuseStep 1615463 = 2423195) B2423195
theorem B1615983 : Blo 1615006 1615983 := bstep (se 1 (by rfl) ⟨1211987, by rfl⟩ : syracuseStep 1615983 = 2423975) B2423975
theorem B27626183 : Blo 1615006 27626183 := bstep (se 1 (by rfl) ⟨20719637, by rfl⟩ : syracuseStep 27626183 = 41439275) B41439275
theorem B8178407 : Blo 1615006 8178407 := bstep (se 1 (by rfl) ⟨6133805, by rfl⟩ : syracuseStep 8178407 = 12267611) B12267611
theorem B7982383 : Blo 1615006 7982383 := bstep (se 1 (by rfl) ⟨5986787, by rfl⟩ : syracuseStep 7982383 = 11973575) B11973575
theorem B13463327 : Blo 1615006 13463327 := bstep (se 1 (by rfl) ⟨10097495, by rfl⟩ : syracuseStep 13463327 = 20194991) B20194991
theorem B10358999 : Blo 1615006 10358999 := bstep (se 1 (by rfl) ⟨7769249, by rfl⟩ : syracuseStep 10358999 = 15538499) B15538499
theorem B3634487 : Blo 1615006 3634487 := bstep (se 1 (by rfl) ⟨2725865, by rfl⟩ : syracuseStep 3634487 = 5451731) B5451731
theorem B8181161 : Blo 1615006 8181161 := bstep (se 2 (by rfl) ⟨3067935, by rfl⟩ : syracuseStep 8181161 = 6135871) B6135871
theorem B6903251 : Blo 1615006 6903251 := bstep (se 1 (by rfl) ⟨5177438, by rfl⟩ : syracuseStep 6903251 = 10354877) B10354877
theorem B223803091 : Blo 1615006 223803091 := bstep (se 1 (by rfl) ⟨167852318, by rfl⟩ : syracuseStep 223803091 = 335704637) B335704637
theorem B1817383 : Blo 1615006 1817383 := bstep (se 1 (by rfl) ⟨1363037, by rfl⟩ : syracuseStep 1817383 = 2726075) B2726075
theorem B3636431 : Blo 1615006 3636431 := bstep (se 1 (by rfl) ⟨2727323, by rfl⟩ : syracuseStep 3636431 = 5454647) B5454647
theorem B55975171 : Blo 1615006 55975171 := bstep (se 1 (by rfl) ⟨41981378, by rfl⟩ : syracuseStep 55975171 = 83962757) B83962757
theorem B26574761 : Blo 1615006 26574761 := bstep (se 2 (by rfl) ⟨9965535, by rfl⟩ : syracuseStep 26574761 = 19931071) B19931071
theorem B6905999 : Blo 1615006 6905999 := bstep (se 1 (by rfl) ⟨5179499, by rfl⟩ : syracuseStep 6905999 = 10358999) B10358999
theorem B3638249 : Blo 1615006 3638249 := bstep (se 2 (by rfl) ⟨1364343, by rfl⟩ : syracuseStep 3638249 = 2728687) B2728687
theorem B1193616485 : Blo 1615006 1193616485 := bstep (se 4 (by rfl) ⟨111901545, by rfl⟩ : syracuseStep 1193616485 = 223803091) B223803091
theorem B10643177 : Blo 1615006 10643177 := bstep (se 2 (by rfl) ⟨3991191, by rfl⟩ : syracuseStep 10643177 = 7982383) B7982383
theorem B18417455 : Blo 1615006 18417455 := bstep (se 1 (by rfl) ⟨13813091, by rfl⟩ : syracuseStep 18417455 = 27626183) B27626183
theorem B1616575 : Blo 1615006 1616575 := bstep (se 1 (by rfl) ⟨1212431, by rfl⟩ : syracuseStep 1616575 = 2424863) B2424863
theorem B159394553 : Blo 1615006 159394553 := bstep (se 2 (by rfl) ⟨59772957, by rfl⟩ : syracuseStep 159394553 = 119545915) B119545915
theorem B10497691 : Blo 1615006 10497691 := bstep (se 1 (by rfl) ⟨7873268, by rfl⟩ : syracuseStep 10497691 = 15746537) B15746537
theorem B10350287 : Blo 1615006 10350287 := bstep (se 1 (by rfl) ⟨7762715, by rfl⟩ : syracuseStep 10350287 = 15525431) B15525431
theorem B74633561 : Blo 1615006 74633561 := bstep (se 2 (by rfl) ⟨27987585, by rfl⟩ : syracuseStep 74633561 = 55975171) B55975171
theorem B5452271 : Blo 1615006 5452271 := bstep (se 1 (by rfl) ⟨4089203, by rfl⟩ : syracuseStep 5452271 = 8178407) B8178407
theorem B70866029 : Blo 1615006 70866029 := bstep (se 3 (by rfl) ⟨13287380, by rfl⟩ : syracuseStep 70866029 = 26574761) B26574761
theorem B8975551 : Blo 1615006 8975551 := bstep (se 1 (by rfl) ⟨6731663, by rfl⟩ : syracuseStep 8975551 = 13463327) B13463327
theorem B2422991 : Blo 1615006 2422991 := bstep (se 1 (by rfl) ⟨1817243, by rfl⟩ : syracuseStep 2422991 = 3634487) B3634487
theorem B5454107 : Blo 1615006 5454107 := bstep (se 1 (by rfl) ⟨4090580, by rfl⟩ : syracuseStep 5454107 = 8181161) B8181161
theorem B4602167 : Blo 1615006 4602167 := bstep (se 1 (by rfl) ⟨3451625, by rfl⟩ : syracuseStep 4602167 = 6903251) B6903251
theorem B2423177 : Blo 1615006 2423177 := bstep (se 2 (by rfl) ⟨908691, by rfl⟩ : syracuseStep 2423177 = 1817383) B1817383
theorem B2424287 : Blo 1615006 2424287 := bstep (se 1 (by rfl) ⟨1818215, by rfl⟩ : syracuseStep 2424287 = 3636431) B3636431
theorem B18415997 : Blo 1615006 18415997 := bstep (se 3 (by rfl) ⟨3452999, by rfl⟩ : syracuseStep 18415997 = 6905999) B6905999
theorem B2425499 : Blo 1615006 2425499 := bstep (se 1 (by rfl) ⟨1819124, by rfl⟩ : syracuseStep 2425499 = 3638249) B3638249
theorem B47244019 : Blo 1615006 47244019 := bstep (se 1 (by rfl) ⟨35433014, by rfl⟩ : syracuseStep 47244019 = 70866029) B70866029
theorem B7095451 : Blo 1615006 7095451 := bstep (se 1 (by rfl) ⟨5321588, by rfl⟩ : syracuseStep 7095451 = 10643177) B10643177
theorem B1615327 : Blo 1615006 1615327 := bstep (se 1 (by rfl) ⟨1211495, by rfl⟩ : syracuseStep 1615327 = 2422991) B2422991
theorem B1615451 : Blo 1615006 1615451 := bstep (se 1 (by rfl) ⟨1211588, by rfl⟩ : syracuseStep 1615451 = 2423177) B2423177
theorem B1616191 : Blo 1615006 1616191 := bstep (se 1 (by rfl) ⟨1212143, by rfl⟩ : syracuseStep 1616191 = 2424287) B2424287
theorem B6900191 : Blo 1615006 6900191 := bstep (se 1 (by rfl) ⟨5175143, by rfl⟩ : syracuseStep 6900191 = 10350287) B10350287
theorem B3068111 : Blo 1615006 3068111 := bstep (se 1 (by rfl) ⟨2301083, by rfl⟩ : syracuseStep 3068111 = 4602167) B4602167
theorem B106263035 : Blo 1615006 106263035 := bstep (se 1 (by rfl) ⟨79697276, by rfl⟩ : syracuseStep 106263035 = 159394553) B159394553
theorem B13996921 : Blo 1615006 13996921 := bstep (se 2 (by rfl) ⟨5248845, by rfl⟩ : syracuseStep 13996921 = 10497691) B10497691
theorem B49755707 : Blo 1615006 49755707 := bstep (se 1 (by rfl) ⟨37316780, by rfl⟩ : syracuseStep 49755707 = 74633561) B74633561
theorem B3634847 : Blo 1615006 3634847 := bstep (se 1 (by rfl) ⟨2726135, by rfl⟩ : syracuseStep 3634847 = 5452271) B5452271
theorem B795744323 : Blo 1615006 795744323 := bstep (se 1 (by rfl) ⟨596808242, by rfl⟩ : syracuseStep 795744323 = 1193616485) B1193616485
theorem B12278303 : Blo 1615006 12278303 := bstep (se 1 (by rfl) ⟨9208727, by rfl⟩ : syracuseStep 12278303 = 18417455) B18417455
theorem B3636071 : Blo 1615006 3636071 := bstep (se 1 (by rfl) ⟨2727053, by rfl⟩ : syracuseStep 3636071 = 5454107) B5454107
theorem B11967401 : Blo 1615006 11967401 := bstep (se 2 (by rfl) ⟨4487775, by rfl⟩ : syracuseStep 11967401 = 8975551) B8975551
theorem B33170471 : Blo 1615006 33170471 := bstep (se 1 (by rfl) ⟨24877853, by rfl⟩ : syracuseStep 33170471 = 49755707) B49755707
theorem B18662561 : Blo 1615006 18662561 := bstep (se 2 (by rfl) ⟨6998460, by rfl⟩ : syracuseStep 18662561 = 13996921) B13996921
theorem B8185535 : Blo 1615006 8185535 := bstep (se 1 (by rfl) ⟨6139151, by rfl⟩ : syracuseStep 8185535 = 12278303) B12278303
theorem B1616999 : Blo 1615006 1616999 := bstep (se 1 (by rfl) ⟨1212749, by rfl⟩ : syracuseStep 1616999 = 2425499) B2425499
theorem B62992025 : Blo 1615006 62992025 := bstep (se 2 (by rfl) ⟨23622009, by rfl⟩ : syracuseStep 62992025 = 47244019) B47244019
theorem B4600127 : Blo 1615006 4600127 := bstep (se 1 (by rfl) ⟨3450095, by rfl⟩ : syracuseStep 4600127 = 6900191) B6900191
theorem B2045407 : Blo 1615006 2045407 := bstep (se 1 (by rfl) ⟨1534055, by rfl⟩ : syracuseStep 2045407 = 3068111) B3068111
theorem B12277331 : Blo 1615006 12277331 := bstep (se 1 (by rfl) ⟨9207998, by rfl⟩ : syracuseStep 12277331 = 18415997) B18415997
theorem B70842023 : Blo 1615006 70842023 := bstep (se 1 (by rfl) ⟨53131517, by rfl⟩ : syracuseStep 70842023 = 106263035) B106263035
theorem B2423231 : Blo 1615006 2423231 := bstep (se 1 (by rfl) ⟨1817423, by rfl⟩ : syracuseStep 2423231 = 3634847) B3634847
theorem B530496215 : Blo 1615006 530496215 := bstep (se 1 (by rfl) ⟨397872161, by rfl⟩ : syracuseStep 530496215 = 795744323) B795744323
theorem B9460601 : Blo 1615006 9460601 := bstep (se 2 (by rfl) ⟨3547725, by rfl⟩ : syracuseStep 9460601 = 7095451) B7095451
theorem B2424047 : Blo 1615006 2424047 := bstep (se 1 (by rfl) ⟨1818035, by rfl⟩ : syracuseStep 2424047 = 3636071) B3636071
theorem B7978267 : Blo 1615006 7978267 := bstep (se 1 (by rfl) ⟨5983700, by rfl⟩ : syracuseStep 7978267 = 11967401) B11967401
theorem B8184887 : Blo 1615006 8184887 := bstep (se 1 (by rfl) ⟨6138665, by rfl⟩ : syracuseStep 8184887 = 12277331) B12277331
theorem B47228015 : Blo 1615006 47228015 := bstep (se 1 (by rfl) ⟨35421011, by rfl⟩ : syracuseStep 47228015 = 70842023) B70842023
theorem B5457023 : Blo 1615006 5457023 := bstep (se 1 (by rfl) ⟨4092767, by rfl⟩ : syracuseStep 5457023 = 8185535) B8185535
theorem B1615487 : Blo 1615006 1615487 := bstep (se 1 (by rfl) ⟨1211615, by rfl⟩ : syracuseStep 1615487 = 2423231) B2423231
theorem B1616031 : Blo 1615006 1616031 := bstep (se 1 (by rfl) ⟨1212023, by rfl⟩ : syracuseStep 1616031 = 2424047) B2424047
theorem B41994683 : Blo 1615006 41994683 := bstep (se 1 (by rfl) ⟨31496012, by rfl⟩ : syracuseStep 41994683 = 62992025) B62992025
theorem B3066751 : Blo 1615006 3066751 := bstep (se 1 (by rfl) ⟨2300063, by rfl⟩ : syracuseStep 3066751 = 4600127) B4600127
theorem B22113647 : Blo 1615006 22113647 := bstep (se 1 (by rfl) ⟨16585235, by rfl⟩ : syracuseStep 22113647 = 33170471) B33170471
theorem B10637689 : Blo 1615006 10637689 := bstep (se 2 (by rfl) ⟨3989133, by rfl⟩ : syracuseStep 10637689 = 7978267) B7978267
theorem B12441707 : Blo 1615006 12441707 := bstep (se 1 (by rfl) ⟨9331280, by rfl⟩ : syracuseStep 12441707 = 18662561) B18662561
theorem B353664143 : Blo 1615006 353664143 := bstep (se 1 (by rfl) ⟨265248107, by rfl⟩ : syracuseStep 353664143 = 530496215) B530496215
theorem B6307067 : Blo 1615006 6307067 := bstep (se 1 (by rfl) ⟨4730300, by rfl⟩ : syracuseStep 6307067 = 9460601) B9460601
theorem B2727209 : Blo 1615006 2727209 := bstep (se 2 (by rfl) ⟨1022703, by rfl⟩ : syracuseStep 2727209 = 2045407) B2045407
theorem B5456591 : Blo 1615006 5456591 := bstep (se 1 (by rfl) ⟨4092443, by rfl⟩ : syracuseStep 5456591 = 8184887) B8184887
theorem B3638015 : Blo 1615006 3638015 := bstep (se 1 (by rfl) ⟨2728511, by rfl⟩ : syracuseStep 3638015 = 5457023) B5457023
theorem B4089001 : Blo 1615006 4089001 := bstep (se 2 (by rfl) ⟨1533375, by rfl⟩ : syracuseStep 4089001 = 3066751) B3066751
theorem B235776095 : Blo 1615006 235776095 := bstep (se 1 (by rfl) ⟨176832071, by rfl⟩ : syracuseStep 235776095 = 353664143) B353664143
theorem B4204711 : Blo 1615006 4204711 := bstep (se 1 (by rfl) ⟨3153533, by rfl⟩ : syracuseStep 4204711 = 6307067) B6307067
theorem B14183585 : Blo 1615006 14183585 := bstep (se 2 (by rfl) ⟨5318844, by rfl⟩ : syracuseStep 14183585 = 10637689) B10637689
theorem B31485343 : Blo 1615006 31485343 := bstep (se 1 (by rfl) ⟨23614007, by rfl⟩ : syracuseStep 31485343 = 47228015) B47228015
theorem B8294471 : Blo 1615006 8294471 := bstep (se 1 (by rfl) ⟨6220853, by rfl⟩ : syracuseStep 8294471 = 12441707) B12441707
theorem B27996455 : Blo 1615006 27996455 := bstep (se 1 (by rfl) ⟨20997341, by rfl⟩ : syracuseStep 27996455 = 41994683) B41994683
theorem B14742431 : Blo 1615006 14742431 := bstep (se 1 (by rfl) ⟨11056823, by rfl⟩ : syracuseStep 14742431 = 22113647) B22113647
theorem B1818139 : Blo 1615006 1818139 := bstep (se 1 (by rfl) ⟨1363604, by rfl⟩ : syracuseStep 1818139 = 2727209) B2727209
theorem B5529647 : Blo 1615006 5529647 := bstep (se 1 (by rfl) ⟨4147235, by rfl⟩ : syracuseStep 5529647 = 8294471) B8294471
theorem B3637727 : Blo 1615006 3637727 := bstep (se 1 (by rfl) ⟨2728295, by rfl⟩ : syracuseStep 3637727 = 5456591) B5456591
theorem B2425343 : Blo 1615006 2425343 := bstep (se 1 (by rfl) ⟨1819007, by rfl⟩ : syracuseStep 2425343 = 3638015) B3638015
theorem B9455723 : Blo 1615006 9455723 := bstep (se 1 (by rfl) ⟨7091792, by rfl⟩ : syracuseStep 9455723 = 14183585) B14183585
theorem B18664303 : Blo 1615006 18664303 := bstep (se 1 (by rfl) ⟨13998227, by rfl⟩ : syracuseStep 18664303 = 27996455) B27996455
theorem B5606281 : Blo 1615006 5606281 := bstep (se 2 (by rfl) ⟨2102355, by rfl⟩ : syracuseStep 5606281 = 4204711) B4204711
theorem B157184063 : Blo 1615006 157184063 := bstep (se 1 (by rfl) ⟨117888047, by rfl⟩ : syracuseStep 157184063 = 235776095) B235776095
theorem B5452001 : Blo 1615006 5452001 := bstep (se 2 (by rfl) ⟨2044500, by rfl⟩ : syracuseStep 5452001 = 4089001) B4089001
theorem B41980457 : Blo 1615006 41980457 := bstep (se 2 (by rfl) ⟨15742671, by rfl⟩ : syracuseStep 41980457 = 31485343) B31485343
theorem B9828287 : Blo 1615006 9828287 := bstep (se 1 (by rfl) ⟨7371215, by rfl⟩ : syracuseStep 9828287 = 14742431) B14742431
theorem B2424185 : Blo 1615006 2424185 := bstep (se 2 (by rfl) ⟨909069, by rfl⟩ : syracuseStep 2424185 = 1818139) B1818139
theorem B14745725 : Blo 1615006 14745725 := bstep (se 3 (by rfl) ⟨2764823, by rfl⟩ : syracuseStep 14745725 = 5529647) B5529647
theorem B2425151 : Blo 1615006 2425151 := bstep (se 1 (by rfl) ⟨1818863, by rfl⟩ : syracuseStep 2425151 = 3637727) B3637727
theorem B1616123 : Blo 1615006 1616123 := bstep (se 1 (by rfl) ⟨1212092, by rfl⟩ : syracuseStep 1616123 = 2424185) B2424185
theorem B1616895 : Blo 1615006 1616895 := bstep (se 1 (by rfl) ⟨1212671, by rfl⟩ : syracuseStep 1616895 = 2425343) B2425343
theorem B27986971 : Blo 1615006 27986971 := bstep (se 1 (by rfl) ⟨20990228, by rfl⟩ : syracuseStep 27986971 = 41980457) B41980457
theorem B7475041 : Blo 1615006 7475041 := bstep (se 2 (by rfl) ⟨2803140, by rfl⟩ : syracuseStep 7475041 = 5606281) B5606281
theorem B6303815 : Blo 1615006 6303815 := bstep (se 1 (by rfl) ⟨4727861, by rfl⟩ : syracuseStep 6303815 = 9455723) B9455723
theorem B104789375 : Blo 1615006 104789375 := bstep (se 1 (by rfl) ⟨78592031, by rfl⟩ : syracuseStep 104789375 = 157184063) B157184063
theorem B3634667 : Blo 1615006 3634667 := bstep (se 1 (by rfl) ⟨2726000, by rfl⟩ : syracuseStep 3634667 = 5452001) B5452001
theorem B24885737 : Blo 1615006 24885737 := bstep (se 2 (by rfl) ⟨9332151, by rfl⟩ : syracuseStep 24885737 = 18664303) B18664303
theorem B6552191 : Blo 1615006 6552191 := bstep (se 1 (by rfl) ⟨4914143, by rfl⟩ : syracuseStep 6552191 = 9828287) B9828287
theorem B4202543 : Blo 1615006 4202543 := bstep (se 1 (by rfl) ⟨3151907, by rfl⟩ : syracuseStep 4202543 = 6303815) B6303815
theorem B9830483 : Blo 1615006 9830483 := bstep (se 1 (by rfl) ⟨7372862, by rfl⟩ : syracuseStep 9830483 = 14745725) B14745725
theorem B37315961 : Blo 1615006 37315961 := bstep (se 2 (by rfl) ⟨13993485, by rfl⟩ : syracuseStep 37315961 = 27986971) B27986971
theorem B16590491 : Blo 1615006 16590491 := bstep (se 1 (by rfl) ⟨12442868, by rfl⟩ : syracuseStep 16590491 = 24885737) B24885737
theorem B1616767 : Blo 1615006 1616767 := bstep (se 1 (by rfl) ⟨1212575, by rfl⟩ : syracuseStep 1616767 = 2425151) B2425151
theorem B9966721 : Blo 1615006 9966721 := bstep (se 2 (by rfl) ⟨3737520, by rfl⟩ : syracuseStep 9966721 = 7475041) B7475041
theorem B69859583 : Blo 1615006 69859583 := bstep (se 1 (by rfl) ⟨52394687, by rfl⟩ : syracuseStep 69859583 = 104789375) B104789375
theorem B2423111 : Blo 1615006 2423111 := bstep (se 1 (by rfl) ⟨1817333, by rfl⟩ : syracuseStep 2423111 = 3634667) B3634667
theorem B17472509 : Blo 1615006 17472509 := bstep (se 3 (by rfl) ⟨3276095, by rfl⟩ : syracuseStep 17472509 = 6552191) B6552191
theorem B6553655 : Blo 1615006 6553655 := bstep (se 1 (by rfl) ⟨4915241, by rfl⟩ : syracuseStep 6553655 = 9830483) B9830483
theorem B11206781 : Blo 1615006 11206781 := bstep (se 3 (by rfl) ⟨2101271, by rfl⟩ : syracuseStep 11206781 = 4202543) B4202543
theorem B11060327 : Blo 1615006 11060327 := bstep (se 1 (by rfl) ⟨8295245, by rfl⟩ : syracuseStep 11060327 = 16590491) B16590491
theorem B46573055 : Blo 1615006 46573055 := bstep (se 1 (by rfl) ⟨34929791, by rfl⟩ : syracuseStep 46573055 = 69859583) B69859583
theorem B13288961 : Blo 1615006 13288961 := bstep (se 2 (by rfl) ⟨4983360, by rfl⟩ : syracuseStep 13288961 = 9966721) B9966721
theorem B1615407 : Blo 1615006 1615407 := bstep (se 1 (by rfl) ⟨1211555, by rfl⟩ : syracuseStep 1615407 = 2423111) B2423111
theorem B24877307 : Blo 1615006 24877307 := bstep (se 1 (by rfl) ⟨18657980, by rfl⟩ : syracuseStep 24877307 = 37315961) B37315961
theorem B11648339 : Blo 1615006 11648339 := bstep (se 1 (by rfl) ⟨8736254, by rfl⟩ : syracuseStep 11648339 = 17472509) B17472509
theorem B7471187 : Blo 1615006 7471187 := bstep (se 1 (by rfl) ⟨5603390, by rfl⟩ : syracuseStep 7471187 = 11206781) B11206781
theorem B7373551 : Blo 1615006 7373551 := bstep (se 1 (by rfl) ⟨5530163, by rfl⟩ : syracuseStep 7373551 = 11060327) B11060327
theorem B31048703 : Blo 1615006 31048703 := bstep (se 1 (by rfl) ⟨23286527, by rfl⟩ : syracuseStep 31048703 = 46573055) B46573055
theorem B4369103 : Blo 1615006 4369103 := bstep (se 1 (by rfl) ⟨3276827, by rfl⟩ : syracuseStep 4369103 = 6553655) B6553655
theorem B8859307 : Blo 1615006 8859307 := bstep (se 1 (by rfl) ⟨6644480, by rfl⟩ : syracuseStep 8859307 = 13288961) B13288961
theorem B16584871 : Blo 1615006 16584871 := bstep (se 1 (by rfl) ⟨12438653, by rfl⟩ : syracuseStep 16584871 = 24877307) B24877307
theorem B7765559 : Blo 1615006 7765559 := bstep (se 1 (by rfl) ⟨5824169, by rfl⟩ : syracuseStep 7765559 = 11648339) B11648339
theorem B4980791 : Blo 1615006 4980791 := bstep (se 1 (by rfl) ⟨3735593, by rfl⟩ : syracuseStep 4980791 = 7471187) B7471187
theorem B9831401 : Blo 1615006 9831401 := bstep (se 2 (by rfl) ⟨3686775, by rfl⟩ : syracuseStep 9831401 = 7373551) B7373551
theorem B22113161 : Blo 1615006 22113161 := bstep (se 2 (by rfl) ⟨8292435, by rfl⟩ : syracuseStep 22113161 = 16584871) B16584871
theorem B2912735 : Blo 1615006 2912735 := bstep (se 1 (by rfl) ⟨2184551, by rfl⟩ : syracuseStep 2912735 = 4369103) B4369103
theorem B20699135 : Blo 1615006 20699135 := bstep (se 1 (by rfl) ⟨15524351, by rfl⟩ : syracuseStep 20699135 = 31048703) B31048703
theorem B11812409 : Blo 1615006 11812409 := bstep (se 2 (by rfl) ⟨4429653, by rfl⟩ : syracuseStep 11812409 = 8859307) B8859307
theorem B5177039 : Blo 1615006 5177039 := bstep (se 1 (by rfl) ⟨3882779, by rfl⟩ : syracuseStep 5177039 = 7765559) B7765559
theorem B1941823 : Blo 1615006 1941823 := bstep (se 1 (by rfl) ⟨1456367, by rfl⟩ : syracuseStep 1941823 = 2912735) B2912735
theorem B6554267 : Blo 1615006 6554267 := bstep (se 1 (by rfl) ⟨4915700, by rfl⟩ : syracuseStep 6554267 = 9831401) B9831401
theorem B13805437 : Blo 1615006 13805437 := bstep (se 3 (by rfl) ⟨2588519, by rfl⟩ : syracuseStep 13805437 = 5177039) B5177039
theorem B7874939 : Blo 1615006 7874939 := bstep (se 1 (by rfl) ⟨5906204, by rfl⟩ : syracuseStep 7874939 = 11812409) B11812409
theorem B3320527 : Blo 1615006 3320527 := bstep (se 1 (by rfl) ⟨2490395, by rfl⟩ : syracuseStep 3320527 = 4980791) B4980791
theorem B13799423 : Blo 1615006 13799423 := bstep (se 1 (by rfl) ⟨10349567, by rfl⟩ : syracuseStep 13799423 = 20699135) B20699135
theorem B14742107 : Blo 1615006 14742107 := bstep (se 1 (by rfl) ⟨11056580, by rfl⟩ : syracuseStep 14742107 = 22113161) B22113161
theorem B2589097 : Blo 1615006 2589097 := bstep (se 2 (by rfl) ⟨970911, by rfl⟩ : syracuseStep 2589097 = 1941823) B1941823
theorem B4369511 : Blo 1615006 4369511 := bstep (se 1 (by rfl) ⟨3277133, by rfl⟩ : syracuseStep 4369511 = 6554267) B6554267
theorem B4427369 : Blo 1615006 4427369 := bstep (se 2 (by rfl) ⟨1660263, by rfl⟩ : syracuseStep 4427369 = 3320527) B3320527
theorem B20999837 : Blo 1615006 20999837 := bstep (se 3 (by rfl) ⟨3937469, by rfl⟩ : syracuseStep 20999837 = 7874939) B7874939
theorem B9828071 : Blo 1615006 9828071 := bstep (se 1 (by rfl) ⟨7371053, by rfl⟩ : syracuseStep 9828071 = 14742107) B14742107
theorem B18407249 : Blo 1615006 18407249 := bstep (se 2 (by rfl) ⟨6902718, by rfl⟩ : syracuseStep 18407249 = 13805437) B13805437
theorem B9199615 : Blo 1615006 9199615 := bstep (se 1 (by rfl) ⟨6899711, by rfl⟩ : syracuseStep 9199615 = 13799423) B13799423
theorem B2951579 : Blo 1615006 2951579 := bstep (se 1 (by rfl) ⟨2213684, by rfl⟩ : syracuseStep 2951579 = 4427369) B4427369
theorem B12266153 : Blo 1615006 12266153 := bstep (se 2 (by rfl) ⟨4599807, by rfl⟩ : syracuseStep 12266153 = 9199615) B9199615
theorem B11652029 : Blo 1615006 11652029 := bstep (se 3 (by rfl) ⟨2184755, by rfl⟩ : syracuseStep 11652029 = 4369511) B4369511
theorem B3452129 : Blo 1615006 3452129 := bstep (se 2 (by rfl) ⟨1294548, by rfl⟩ : syracuseStep 3452129 = 2589097) B2589097
theorem B6552047 : Blo 1615006 6552047 := bstep (se 1 (by rfl) ⟨4914035, by rfl⟩ : syracuseStep 6552047 = 9828071) B9828071
theorem B13999891 : Blo 1615006 13999891 := bstep (se 1 (by rfl) ⟨10499918, by rfl⟩ : syracuseStep 13999891 = 20999837) B20999837
theorem B12271499 : Blo 1615006 12271499 := bstep (se 1 (by rfl) ⟨9203624, by rfl⟩ : syracuseStep 12271499 = 18407249) B18407249
theorem B8177435 : Blo 1615006 8177435 := bstep (se 1 (by rfl) ⟨6133076, by rfl⟩ : syracuseStep 8177435 = 12266153) B12266153
theorem B7768019 : Blo 1615006 7768019 := bstep (se 1 (by rfl) ⟨5826014, by rfl⟩ : syracuseStep 7768019 = 11652029) B11652029
theorem B18666521 : Blo 1615006 18666521 := bstep (se 2 (by rfl) ⟨6999945, by rfl⟩ : syracuseStep 18666521 = 13999891) B13999891
theorem B8180999 : Blo 1615006 8180999 := bstep (se 1 (by rfl) ⟨6135749, by rfl⟩ : syracuseStep 8180999 = 12271499) B12271499
theorem B7870877 : Blo 1615006 7870877 := bstep (se 3 (by rfl) ⟨1475789, by rfl⟩ : syracuseStep 7870877 = 2951579) B2951579
theorem B17472125 : Blo 1615006 17472125 := bstep (se 3 (by rfl) ⟨3276023, by rfl⟩ : syracuseStep 17472125 = 6552047) B6552047
theorem B2301419 : Blo 1615006 2301419 := bstep (se 1 (by rfl) ⟨1726064, by rfl⟩ : syracuseStep 2301419 = 3452129) B3452129
theorem B12444347 : Blo 1615006 12444347 := bstep (se 1 (by rfl) ⟨9333260, by rfl⟩ : syracuseStep 12444347 = 18666521) B18666521
theorem B6137117 : Blo 1615006 6137117 := bstep (se 3 (by rfl) ⟨1150709, by rfl⟩ : syracuseStep 6137117 = 2301419) B2301419
theorem B5451623 : Blo 1615006 5451623 := bstep (se 1 (by rfl) ⟨4088717, by rfl⟩ : syracuseStep 5451623 = 8177435) B8177435
theorem B5247251 : Blo 1615006 5247251 := bstep (se 1 (by rfl) ⟨3935438, by rfl⟩ : syracuseStep 5247251 = 7870877) B7870877
theorem B20714717 : Blo 1615006 20714717 := bstep (se 3 (by rfl) ⟨3884009, by rfl⟩ : syracuseStep 20714717 = 7768019) B7768019
theorem B5453999 : Blo 1615006 5453999 := bstep (se 1 (by rfl) ⟨4090499, by rfl⟩ : syracuseStep 5453999 = 8180999) B8180999
theorem B11648083 : Blo 1615006 11648083 := bstep (se 1 (by rfl) ⟨8736062, by rfl⟩ : syracuseStep 11648083 = 17472125) B17472125
theorem B3498167 : Blo 1615006 3498167 := bstep (se 1 (by rfl) ⟨2623625, by rfl⟩ : syracuseStep 3498167 = 5247251) B5247251
theorem B4091411 : Blo 1615006 4091411 := bstep (se 1 (by rfl) ⟨3068558, by rfl⟩ : syracuseStep 4091411 = 6137117) B6137117
theorem B3634415 : Blo 1615006 3634415 := bstep (se 1 (by rfl) ⟨2725811, by rfl⟩ : syracuseStep 3634415 = 5451623) B5451623
theorem B8296231 : Blo 1615006 8296231 := bstep (se 1 (by rfl) ⟨6222173, by rfl⟩ : syracuseStep 8296231 = 12444347) B12444347
theorem B13809811 : Blo 1615006 13809811 := bstep (se 1 (by rfl) ⟨10357358, by rfl⟩ : syracuseStep 13809811 = 20714717) B20714717
theorem B15530777 : Blo 1615006 15530777 := bstep (se 2 (by rfl) ⟨5824041, by rfl⟩ : syracuseStep 15530777 = 11648083) B11648083
theorem B3635999 : Blo 1615006 3635999 := bstep (se 1 (by rfl) ⟨2726999, by rfl⟩ : syracuseStep 3635999 = 5453999) B5453999
theorem B11061641 : Blo 1615006 11061641 := bstep (se 2 (by rfl) ⟨4148115, by rfl⟩ : syracuseStep 11061641 = 8296231) B8296231
theorem B18413081 : Blo 1615006 18413081 := bstep (se 2 (by rfl) ⟨6904905, by rfl⟩ : syracuseStep 18413081 = 13809811) B13809811
theorem B9328445 : Blo 1615006 9328445 := bstep (se 3 (by rfl) ⟨1749083, by rfl⟩ : syracuseStep 9328445 = 3498167) B3498167
theorem B2422943 : Blo 1615006 2422943 := bstep (se 1 (by rfl) ⟨1817207, by rfl⟩ : syracuseStep 2422943 = 3634415) B3634415
theorem B10353851 : Blo 1615006 10353851 := bstep (se 1 (by rfl) ⟨7765388, by rfl⟩ : syracuseStep 10353851 = 15530777) B15530777
theorem B2423999 : Blo 1615006 2423999 := bstep (se 1 (by rfl) ⟨1817999, by rfl⟩ : syracuseStep 2423999 = 3635999) B3635999
theorem B2727607 : Blo 1615006 2727607 := bstep (se 1 (by rfl) ⟨2045705, by rfl⟩ : syracuseStep 2727607 = 4091411) B4091411
theorem B6218963 : Blo 1615006 6218963 := bstep (se 1 (by rfl) ⟨4664222, by rfl⟩ : syracuseStep 6218963 = 9328445) B9328445
theorem B1615295 : Blo 1615006 1615295 := bstep (se 1 (by rfl) ⟨1211471, by rfl⟩ : syracuseStep 1615295 = 2422943) B2422943
theorem B1615999 : Blo 1615006 1615999 := bstep (se 1 (by rfl) ⟨1211999, by rfl⟩ : syracuseStep 1615999 = 2423999) B2423999
theorem B12275387 : Blo 1615006 12275387 := bstep (se 1 (by rfl) ⟨9206540, by rfl⟩ : syracuseStep 12275387 = 18413081) B18413081
theorem B6902567 : Blo 1615006 6902567 := bstep (se 1 (by rfl) ⟨5176925, by rfl⟩ : syracuseStep 6902567 = 10353851) B10353851
theorem B29497709 : Blo 1615006 29497709 := bstep (se 3 (by rfl) ⟨5530820, by rfl⟩ : syracuseStep 29497709 = 11061641) B11061641
theorem B3636809 : Blo 1615006 3636809 := bstep (se 2 (by rfl) ⟨1363803, by rfl⟩ : syracuseStep 3636809 = 2727607) B2727607
theorem B4145975 : Blo 1615006 4145975 := bstep (se 1 (by rfl) ⟨3109481, by rfl⟩ : syracuseStep 4145975 = 6218963) B6218963
theorem B19665139 : Blo 1615006 19665139 := bstep (se 1 (by rfl) ⟨14748854, by rfl⟩ : syracuseStep 19665139 = 29497709) B29497709
theorem B4601711 : Blo 1615006 4601711 := bstep (se 1 (by rfl) ⟨3451283, by rfl⟩ : syracuseStep 4601711 = 6902567) B6902567
theorem B2424539 : Blo 1615006 2424539 := bstep (se 1 (by rfl) ⟨1818404, by rfl⟩ : syracuseStep 2424539 = 3636809) B3636809
theorem B8183591 : Blo 1615006 8183591 := bstep (se 1 (by rfl) ⟨6137693, by rfl⟩ : syracuseStep 8183591 = 12275387) B12275387
theorem B1616359 : Blo 1615006 1616359 := bstep (se 1 (by rfl) ⟨1212269, by rfl⟩ : syracuseStep 1616359 = 2424539) B2424539
theorem B2763983 : Blo 1615006 2763983 := bstep (se 1 (by rfl) ⟨2072987, by rfl⟩ : syracuseStep 2763983 = 4145975) B4145975
theorem B3067807 : Blo 1615006 3067807 := bstep (se 1 (by rfl) ⟨2300855, by rfl⟩ : syracuseStep 3067807 = 4601711) B4601711
theorem B26220185 : Blo 1615006 26220185 := bstep (se 2 (by rfl) ⟨9832569, by rfl⟩ : syracuseStep 26220185 = 19665139) B19665139
theorem B5455727 : Blo 1615006 5455727 := bstep (se 1 (by rfl) ⟨4091795, by rfl⟩ : syracuseStep 5455727 = 8183591) B8183591
theorem B4090409 : Blo 1615006 4090409 := bstep (se 2 (by rfl) ⟨1533903, by rfl⟩ : syracuseStep 4090409 = 3067807) B3067807
theorem B17480123 : Blo 1615006 17480123 := bstep (se 1 (by rfl) ⟨13110092, by rfl⟩ : syracuseStep 17480123 = 26220185) B26220185
theorem B1842655 : Blo 1615006 1842655 := bstep (se 1 (by rfl) ⟨1381991, by rfl⟩ : syracuseStep 1842655 = 2763983) B2763983
theorem B3637151 : Blo 1615006 3637151 := bstep (se 1 (by rfl) ⟨2727863, by rfl⟩ : syracuseStep 3637151 = 5455727) B5455727
theorem B11653415 : Blo 1615006 11653415 := bstep (se 1 (by rfl) ⟨8740061, by rfl⟩ : syracuseStep 11653415 = 17480123) B17480123
theorem B2726939 : Blo 1615006 2726939 := bstep (se 1 (by rfl) ⟨2045204, by rfl⟩ : syracuseStep 2726939 = 4090409) B4090409
theorem B2456873 : Blo 1615006 2456873 := bstep (se 2 (by rfl) ⟨921327, by rfl⟩ : syracuseStep 2456873 = 1842655) B1842655
theorem B2424767 : Blo 1615006 2424767 := bstep (se 1 (by rfl) ⟨1818575, by rfl⟩ : syracuseStep 2424767 = 3637151) B3637151
theorem B1616511 : Blo 1615006 1616511 := bstep (se 1 (by rfl) ⟨1212383, by rfl⟩ : syracuseStep 1616511 = 2424767) B2424767
theorem B7768943 : Blo 1615006 7768943 := bstep (se 1 (by rfl) ⟨5826707, by rfl⟩ : syracuseStep 7768943 = 11653415) B11653415
theorem B1817959 : Blo 1615006 1817959 := bstep (se 1 (by rfl) ⟨1363469, by rfl⟩ : syracuseStep 1817959 = 2726939) B2726939
theorem B1637915 : Blo 1615006 1637915 := bstep (se 1 (by rfl) ⟨1228436, by rfl⟩ : syracuseStep 1637915 = 2456873) B2456873
theorem B4367773 : Blo 1615006 4367773 := bstep (se 3 (by rfl) ⟨818957, by rfl⟩ : syracuseStep 4367773 = 1637915) B1637915
theorem B5179295 : Blo 1615006 5179295 := bstep (se 1 (by rfl) ⟨3884471, by rfl⟩ : syracuseStep 5179295 = 7768943) B7768943
theorem B2423945 : Blo 1615006 2423945 := bstep (se 2 (by rfl) ⟨908979, by rfl⟩ : syracuseStep 2423945 = 1817959) B1817959
theorem B1615963 : Blo 1615006 1615963 := bstep (se 1 (by rfl) ⟨1211972, by rfl⟩ : syracuseStep 1615963 = 2423945) B2423945
theorem B3452863 : Blo 1615006 3452863 := bstep (se 1 (by rfl) ⟨2589647, by rfl⟩ : syracuseStep 3452863 = 5179295) B5179295
theorem B5823697 : Blo 1615006 5823697 := bstep (se 2 (by rfl) ⟨2183886, by rfl⟩ : syracuseStep 5823697 = 4367773) B4367773
theorem B7764929 : Blo 1615006 7764929 := bstep (se 2 (by rfl) ⟨2911848, by rfl⟩ : syracuseStep 7764929 = 5823697) B5823697
theorem B4603817 : Blo 1615006 4603817 := bstep (se 2 (by rfl) ⟨1726431, by rfl⟩ : syracuseStep 4603817 = 3452863) B3452863
theorem B12276845 : Blo 1615006 12276845 := bstep (se 3 (by rfl) ⟨2301908, by rfl⟩ : syracuseStep 12276845 = 4603817) B4603817
theorem B5176619 : Blo 1615006 5176619 := bstep (se 1 (by rfl) ⟨3882464, by rfl⟩ : syracuseStep 5176619 = 7764929) B7764929
theorem B8184563 : Blo 1615006 8184563 := bstep (se 1 (by rfl) ⟨6138422, by rfl⟩ : syracuseStep 8184563 = 12276845) B12276845
theorem B3451079 : Blo 1615006 3451079 := bstep (se 1 (by rfl) ⟨2588309, by rfl⟩ : syracuseStep 3451079 = 5176619) B5176619
theorem B5456375 : Blo 1615006 5456375 := bstep (se 1 (by rfl) ⟨4092281, by rfl⟩ : syracuseStep 5456375 = 8184563) B8184563
theorem B2300719 : Blo 1615006 2300719 := bstep (se 1 (by rfl) ⟨1725539, by rfl⟩ : syracuseStep 2300719 = 3451079) B3451079
theorem B3637583 : Blo 1615006 3637583 := bstep (se 1 (by rfl) ⟨2728187, by rfl⟩ : syracuseStep 3637583 = 5456375) B5456375
theorem B3067625 : Blo 1615006 3067625 := bstep (se 2 (by rfl) ⟨1150359, by rfl⟩ : syracuseStep 3067625 = 2300719) B2300719
theorem B2425055 : Blo 1615006 2425055 := bstep (se 1 (by rfl) ⟨1818791, by rfl⟩ : syracuseStep 2425055 = 3637583) B3637583
theorem B2045083 : Blo 1615006 2045083 := bstep (se 1 (by rfl) ⟨1533812, by rfl⟩ : syracuseStep 2045083 = 3067625) B3067625
theorem B1616703 : Blo 1615006 1616703 := bstep (se 1 (by rfl) ⟨1212527, by rfl⟩ : syracuseStep 1616703 = 2425055) B2425055
theorem B2726777 : Blo 1615006 2726777 := bstep (se 2 (by rfl) ⟨1022541, by rfl⟩ : syracuseStep 2726777 = 2045083) B2045083
theorem B1817851 : Blo 1615006 1817851 := bstep (se 1 (by rfl) ⟨1363388, by rfl⟩ : syracuseStep 1817851 = 2726777) B2726777
theorem B2423801 : Blo 1615006 2423801 := bstep (se 2 (by rfl) ⟨908925, by rfl⟩ : syracuseStep 2423801 = 1817851) B1817851
theorem B1615867 : Blo 1615006 1615867 := bstep (se 1 (by rfl) ⟨1211900, by rfl⟩ : syracuseStep 1615867 = 2423801) B2423801

theorem C0 (j : ℕ) (h1 : 403751 ≤ j) (h2 : j ≤ 404250) : Blo 1615006 (4 * j + 3) := by
  interval_cases j
  · exact B1615007
  · exact B1615011
  · exact B1615015
  · exact B1615019
  · exact B1615023
  · exact B1615027
  · exact B1615031
  · exact B1615035
  · exact B1615039
  · exact B1615043
  · exact B1615047
  · exact B1615051
  · exact B1615055
  · exact B1615059
  · exact B1615063
  · exact B1615067
  · exact B1615071
  · exact B1615075
  · exact B1615079
  · exact B1615083
  · exact B1615087
  · exact B1615091
  · exact B1615095
  · exact B1615099
  · exact B1615103
  · exact B1615107
  · exact B1615111
  · exact B1615115
  · exact B1615119
  · exact B1615123
  · exact B1615127
  · exact B1615131
  · exact B1615135
  · exact B1615139
  · exact B1615143
  · exact B1615147
  · exact B1615151
  · exact B1615155
  · exact B1615159
  · exact B1615163
  · exact B1615167
  · exact B1615171
  · exact B1615175
  · exact B1615179
  · exact B1615183
  · exact B1615187
  · exact B1615191
  · exact B1615195
  · exact B1615199
  · exact B1615203
  · exact B1615207
  · exact B1615211
  · exact B1615215
  · exact B1615219
  · exact B1615223
  · exact B1615227
  · exact B1615231
  · exact B1615235
  · exact B1615239
  · exact B1615243
  · exact B1615247
  · exact B1615251
  · exact B1615255
  · exact B1615259
  · exact B1615263
  · exact B1615267
  · exact B1615271
  · exact B1615275
  · exact B1615279
  · exact B1615283
  · exact B1615287
  · exact B1615291
  · exact B1615295
  · exact B1615299
  · exact B1615303
  · exact B1615307
  · exact B1615311
  · exact B1615315
  · exact B1615319
  · exact B1615323
  · exact B1615327
  · exact B1615331
  · exact B1615335
  · exact B1615339
  · exact B1615343
  · exact B1615347
  · exact B1615351
  · exact B1615355
  · exact B1615359
  · exact B1615363
  · exact B1615367
  · exact B1615371
  · exact B1615375
  · exact B1615379
  · exact B1615383
  · exact B1615387
  · exact B1615391
  · exact B1615395
  · exact B1615399
  · exact B1615403
  · exact B1615407
  · exact B1615411
  · exact B1615415
  · exact B1615419
  · exact B1615423
  · exact B1615427
  · exact B1615431
  · exact B1615435
  · exact B1615439
  · exact B1615443
  · exact B1615447
  · exact B1615451
  · exact B1615455
  · exact B1615459
  · exact B1615463
  · exact B1615467
  · exact B1615471
  · exact B1615475
  · exact B1615479
  · exact B1615483
  · exact B1615487
  · exact B1615491
  · exact B1615495
  · exact B1615499
  · exact B1615503
  · exact B1615507
  · exact B1615511
  · exact B1615515
  · exact B1615519
  · exact B1615523
  · exact B1615527
  · exact B1615531
  · exact B1615535
  · exact B1615539
  · exact B1615543
  · exact B1615547
  · exact B1615551
  · exact B1615555
  · exact B1615559
  · exact B1615563
  · exact B1615567
  · exact B1615571
  · exact B1615575
  · exact B1615579
  · exact B1615583
  · exact B1615587
  · exact B1615591
  · exact B1615595
  · exact B1615599
  · exact B1615603
  · exact B1615607
  · exact B1615611
  · exact B1615615
  · exact B1615619
  · exact B1615623
  · exact B1615627
  · exact B1615631
  · exact B1615635
  · exact B1615639
  · exact B1615643
  · exact B1615647
  · exact B1615651
  · exact B1615655
  · exact B1615659
  · exact B1615663
  · exact B1615667
  · exact B1615671
  · exact B1615675
  · exact B1615679
  · exact B1615683
  · exact B1615687
  · exact B1615691
  · exact B1615695
  · exact B1615699
  · exact B1615703
  · exact B1615707
  · exact B1615711
  · exact B1615715
  · exact B1615719
  · exact B1615723
  · exact B1615727
  · exact B1615731
  · exact B1615735
  · exact B1615739
  · exact B1615743
  · exact B1615747
  · exact B1615751
  · exact B1615755
  · exact B1615759
  · exact B1615763
  · exact B1615767
  · exact B1615771
  · exact B1615775
  · exact B1615779
  · exact B1615783
  · exact B1615787
  · exact B1615791
  · exact B1615795
  · exact B1615799
  · exact B1615803
  · exact B1615807
  · exact B1615811
  · exact B1615815
  · exact B1615819
  · exact B1615823
  · exact B1615827
  · exact B1615831
  · exact B1615835
  · exact B1615839
  · exact B1615843
  · exact B1615847
  · exact B1615851
  · exact B1615855
  · exact B1615859
  · exact B1615863
  · exact B1615867
  · exact B1615871
  · exact B1615875
  · exact B1615879
  · exact B1615883
  · exact B1615887
  · exact B1615891
  · exact B1615895
  · exact B1615899
  · exact B1615903
  · exact B1615907
  · exact B1615911
  · exact B1615915
  · exact B1615919
  · exact B1615923
  · exact B1615927
  · exact B1615931
  · exact B1615935
  · exact B1615939
  · exact B1615943
  · exact B1615947
  · exact B1615951
  · exact B1615955
  · exact B1615959
  · exact B1615963
  · exact B1615967
  · exact B1615971
  · exact B1615975
  · exact B1615979
  · exact B1615983
  · exact B1615987
  · exact B1615991
  · exact B1615995
  · exact B1615999
  · exact B1616003
  · exact B1616007
  · exact B1616011
  · exact B1616015
  · exact B1616019
  · exact B1616023
  · exact B1616027
  · exact B1616031
  · exact B1616035
  · exact B1616039
  · exact B1616043
  · exact B1616047
  · exact B1616051
  · exact B1616055
  · exact B1616059
  · exact B1616063
  · exact B1616067
  · exact B1616071
  · exact B1616075
  · exact B1616079
  · exact B1616083
  · exact B1616087
  · exact B1616091
  · exact B1616095
  · exact B1616099
  · exact B1616103
  · exact B1616107
  · exact B1616111
  · exact B1616115
  · exact B1616119
  · exact B1616123
  · exact B1616127
  · exact B1616131
  · exact B1616135
  · exact B1616139
  · exact B1616143
  · exact B1616147
  · exact B1616151
  · exact B1616155
  · exact B1616159
  · exact B1616163
  · exact B1616167
  · exact B1616171
  · exact B1616175
  · exact B1616179
  · exact B1616183
  · exact B1616187
  · exact B1616191
  · exact B1616195
  · exact B1616199
  · exact B1616203
  · exact B1616207
  · exact B1616211
  · exact B1616215
  · exact B1616219
  · exact B1616223
  · exact B1616227
  · exact B1616231
  · exact B1616235
  · exact B1616239
  · exact B1616243
  · exact B1616247
  · exact B1616251
  · exact B1616255
  · exact B1616259
  · exact B1616263
  · exact B1616267
  · exact B1616271
  · exact B1616275
  · exact B1616279
  · exact B1616283
  · exact B1616287
  · exact B1616291
  · exact B1616295
  · exact B1616299
  · exact B1616303
  · exact B1616307
  · exact B1616311
  · exact B1616315
  · exact B1616319
  · exact B1616323
  · exact B1616327
  · exact B1616331
  · exact B1616335
  · exact B1616339
  · exact B1616343
  · exact B1616347
  · exact B1616351
  · exact B1616355
  · exact B1616359
  · exact B1616363
  · exact B1616367
  · exact B1616371
  · exact B1616375
  · exact B1616379
  · exact B1616383
  · exact B1616387
  · exact B1616391
  · exact B1616395
  · exact B1616399
  · exact B1616403
  · exact B1616407
  · exact B1616411
  · exact B1616415
  · exact B1616419
  · exact B1616423
  · exact B1616427
  · exact B1616431
  · exact B1616435
  · exact B1616439
  · exact B1616443
  · exact B1616447
  · exact B1616451
  · exact B1616455
  · exact B1616459
  · exact B1616463
  · exact B1616467
  · exact B1616471
  · exact B1616475
  · exact B1616479
  · exact B1616483
  · exact B1616487
  · exact B1616491
  · exact B1616495
  · exact B1616499
  · exact B1616503
  · exact B1616507
  · exact B1616511
  · exact B1616515
  · exact B1616519
  · exact B1616523
  · exact B1616527
  · exact B1616531
  · exact B1616535
  · exact B1616539
  · exact B1616543
  · exact B1616547
  · exact B1616551
  · exact B1616555
  · exact B1616559
  · exact B1616563
  · exact B1616567
  · exact B1616571
  · exact B1616575
  · exact B1616579
  · exact B1616583
  · exact B1616587
  · exact B1616591
  · exact B1616595
  · exact B1616599
  · exact B1616603
  · exact B1616607
  · exact B1616611
  · exact B1616615
  · exact B1616619
  · exact B1616623
  · exact B1616627
  · exact B1616631
  · exact B1616635
  · exact B1616639
  · exact B1616643
  · exact B1616647
  · exact B1616651
  · exact B1616655
  · exact B1616659
  · exact B1616663
  · exact B1616667
  · exact B1616671
  · exact B1616675
  · exact B1616679
  · exact B1616683
  · exact B1616687
  · exact B1616691
  · exact B1616695
  · exact B1616699
  · exact B1616703
  · exact B1616707
  · exact B1616711
  · exact B1616715
  · exact B1616719
  · exact B1616723
  · exact B1616727
  · exact B1616731
  · exact B1616735
  · exact B1616739
  · exact B1616743
  · exact B1616747
  · exact B1616751
  · exact B1616755
  · exact B1616759
  · exact B1616763
  · exact B1616767
  · exact B1616771
  · exact B1616775
  · exact B1616779
  · exact B1616783
  · exact B1616787
  · exact B1616791
  · exact B1616795
  · exact B1616799
  · exact B1616803
  · exact B1616807
  · exact B1616811
  · exact B1616815
  · exact B1616819
  · exact B1616823
  · exact B1616827
  · exact B1616831
  · exact B1616835
  · exact B1616839
  · exact B1616843
  · exact B1616847
  · exact B1616851
  · exact B1616855
  · exact B1616859
  · exact B1616863
  · exact B1616867
  · exact B1616871
  · exact B1616875
  · exact B1616879
  · exact B1616883
  · exact B1616887
  · exact B1616891
  · exact B1616895
  · exact B1616899
  · exact B1616903
  · exact B1616907
  · exact B1616911
  · exact B1616915
  · exact B1616919
  · exact B1616923
  · exact B1616927
  · exact B1616931
  · exact B1616935
  · exact B1616939
  · exact B1616943
  · exact B1616947
  · exact B1616951
  · exact B1616955
  · exact B1616959
  · exact B1616963
  · exact B1616967
  · exact B1616971
  · exact B1616975
  · exact B1616979
  · exact B1616983
  · exact B1616987
  · exact B1616991
  · exact B1616995
  · exact B1616999
  · exact B1617003

theorem solution (m : ℕ) (hlo : 1615006 ≤ m) (hhi : m ≤ 1617006) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 403751 ≤ j := by omega
    have hj2 : j ≤ 404250 := by omega
    have hb : Blo 1615006 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
